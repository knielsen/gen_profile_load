/*
  Generate typical load on mysqld for GCC profile-guided optimisation.
  Copyright 2014 Kristian Nielsen.

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*/

#include <sys/types.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <poll.h>

#include <errno.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <mysql.h>


/*
  Some constants to define simple data distributions.
  M is the count of operations to do.
*/
const int M= 500;
const int A1= 37;                        /* Should be relative prime with M */
const int A2= 73;                        /* Should be relative prime with M */
const int B1= 50;                    /* Should not be relative prime with M */

#define MAX_PH 100

enum enum_placeholder_types
{
  PHT_INT,
  PHT_STR
};

struct query {
  char *q_str;
  int num_placeholders;
  int *placeholder_types;
  MYSQL_STMT *stmt;
};

static int do_binlog, do_binlog_format, do_nonblock, do_prepared;
static pid_t mysqld_pid;
MYSQL mysql;

static void
fatal(const char *errmsg)
{
  perror(errmsg);
  exit(1);
}


static void
fatal_mysql(const char *errmsg)
{
  fprintf(stderr, "%s: %s\n", errmsg, mysql_error(&mysql));
  exit(1);
}


static int
wait_for_mysql(MYSQL *mysql, int status)
{
  struct pollfd pfd;
  int timeout;
  int res;

  pfd.fd= mysql_get_socket(mysql);
  pfd.events=
    (status & MYSQL_WAIT_READ ? POLLIN : 0) |
    (status & MYSQL_WAIT_WRITE ? POLLOUT : 0) |
    (status & MYSQL_WAIT_EXCEPT ? POLLPRI : 0);
  if (status & MYSQL_WAIT_TIMEOUT)
    timeout= 1000*mysql_get_timeout_value(mysql);
  else
    timeout= -1;
  res= poll(&pfd, 1, timeout);
  if (res <= 0)
    return MYSQL_WAIT_TIMEOUT;
  else
  {
    int status= 0;
    if (pfd.revents & POLLIN)
      status|= MYSQL_WAIT_READ;
    if (pfd.revents & POLLOUT)
      status|= MYSQL_WAIT_WRITE;
    if (pfd.revents & POLLPRI)
      status|= MYSQL_WAIT_EXCEPT;
    return status;
  }
}


static struct query *
get_vqueryf(const char *q_str, va_list ap)
{
  char buf[1000];
  int ph_types[MAX_PH];
  int num_ph;
  int i;
  struct query *q;

  i= 0;
  num_ph= 0;
  while (*q_str && i < sizeof(buf) - 1 &&
         num_ph < MAX_PH)
  {
    if (q_str[0] == '%' && q_str[1] == 's')
    {
      const char *str= va_arg(ap, const char *);
      while (*str && i < sizeof(buf) - 1)
        buf[i++]= *str++;
      q_str+= 2;
    }
    else if (q_str[0] == '?' && q_str[1] == 'd')
    {
      ph_types[num_ph++]= PHT_INT;
      buf[i++]= '?';
      q_str+= 2;
    }
    else if (q_str[0] == '?' && q_str[1] == 's')
    {
      ph_types[num_ph++]= PHT_STR;
      buf[i++]= '?';
      q_str+= 2;
    }
    else
      buf[i++]= *q_str++;
  }
  buf[i]= 0;
  q= malloc(sizeof(*q));
  q->q_str= strdup(buf);
  q->num_placeholders= num_ph;
  q->placeholder_types= malloc(num_ph*sizeof(q->placeholder_types[0]));
  memcpy(q->placeholder_types, ph_types,
         num_ph*sizeof(q->placeholder_types[0]));

  if (do_prepared)
  {
    int err;
    q->stmt= mysql_stmt_init(&mysql);
    if (do_nonblock)
    {
      int status;

      status= mysql_stmt_prepare_start(&err, q->stmt, q->q_str, strlen(q->q_str));
      while (status)
      {
        status= wait_for_mysql(&mysql, status);
        status= mysql_stmt_prepare_cont(&err, q->stmt, status);
      }
    }
    else
      err= mysql_stmt_prepare(q->stmt, q->q_str, strlen(q->q_str));

    if (err)
        fatal_mysql("mysql_stmt_prepare() failed");
  }
  else
    q->stmt= NULL;

  return q;
}


static struct query *
get_queryf(const char *q_str, ...)
{
  va_list ap;
  struct query *q;

  va_start(ap, q_str);
  q= get_vqueryf(q_str, ap);
  va_end(ap);
  return q;
}


static void
free_query(struct query *q)
{
  free(q->q_str);
  free(q->placeholder_types);
  if (q->stmt)
    mysql_stmt_close(q->stmt);
  free(q);
}


static void
do_vqueryq(struct query *q, va_list ap, int fetch_results)
{
  int err, status;
  MYSQL_RES *res;
  MYSQL_ROW row;

  if (do_prepared)
  {
    int colcnt;
    int i;
    char buf[1000];
    unsigned long outlen;
    MYSQL_BIND bind[MAX_PH];
    union { int vi; struct { char *s; unsigned long l;} vs; } bindval[MAX_PH];
    unsigned long typ=
      (fetch_results ? CURSOR_TYPE_READ_ONLY : CURSOR_TYPE_NO_CURSOR);
    mysql_stmt_attr_set(q->stmt, STMT_ATTR_CURSOR_TYPE, (void *)&typ);

    /*
      ToDo: we could put the bind structure into struct query, and then we would
      only have to mysql_stmt_bind_param() once.
    */
    memset(bind, 0, q->num_placeholders*sizeof(bind[0]));
    for (i= 0; i < q->num_placeholders; ++i)
    {
      switch (q->placeholder_types[i])
      {
      case PHT_INT:
        bind[i].buffer_type= MYSQL_TYPE_LONG;
        bindval[i].vi= va_arg(ap, int);
        bind[i].buffer= (char *)&bindval[i].vi;
        bind[i].is_null= 0;
        bind[i].length= 0;
        break;
      case PHT_STR:
        bind[i].buffer_type= MYSQL_TYPE_STRING;
        bindval[i].vs.s= va_arg(ap, char *);
        bindval[i].vs.l= strlen(bindval[i].vs.s);
        bind[i].buffer= bindval[i].vs.s;
        bind[i].is_null= NULL;
        bind[i].length= &bindval[i].vs.l;
        break;
      }
    }
    err= mysql_stmt_bind_param(q->stmt, bind);
    if (err)
      fatal_mysql("mysql_stmt_bind_param() failed");

    if (do_nonblock)
    {
      status= mysql_stmt_execute_start(&err, q->stmt);
      while (status)
      {
        status= wait_for_mysql(&mysql, status);
        status= mysql_stmt_execute_cont(&err, q->stmt, status);
      }
    }
    else
      err= mysql_stmt_execute(q->stmt);

    if (err)
      fatal_mysql("mysql_stmt_execute() failed");

    if (!fetch_results)
      return;

    res= mysql_stmt_result_metadata(q->stmt);
    colcnt= mysql_num_fields(res);

    if (colcnt >= MAX_PH)
    {
      errno= 0;
      fatal("Too many result columns");
    }

    memset(bind, 0, colcnt*sizeof(bind[0]));
    for (i= 0; i < colcnt; ++i)
    {
      bind[i].buffer_type= MYSQL_TYPE_STRING;
      bind[i].buffer= buf;
      bind[i].buffer_length= sizeof(buf);
      bind[i].length= &outlen;
    }
    mysql_stmt_bind_result(q->stmt, bind);

    for (;;)
    {
      if (do_nonblock)
      {
        status= mysql_stmt_fetch_start(&err, q->stmt);
        while (status)
        {
          status= wait_for_mysql(&mysql, status);
          status= mysql_stmt_fetch_cont(&err, q->stmt, status);
        }
      }
      else
        err= mysql_stmt_fetch(q->stmt);

      if (err == MYSQL_NO_DATA)
        break;
      else if (err != 0)
        fatal_mysql("mysql_stmt_fetch() failed");
    }

    mysql_free_result(res);
  }
  else
  {
    char buf[3000];
    int i= 0;
    const char *p= q->q_str;
    int ph= 0;
    const char *str_arg;
    int str_len;

    /*
      Non-prepared statement.
      Insert the placeholder values into the query string, properly escaped.
    */
    while (*p && i < sizeof(buf)-1)
    {
      if (p[0] == '?' && ph < q->num_placeholders)
      {
        switch (q->placeholder_types[ph])
        {
        case PHT_INT:
          i+= snprintf(&buf[i], sizeof(buf) - i, "%d", va_arg(ap, int));
          break;
        case PHT_STR:
          str_arg= va_arg(ap, const char *);
          str_len= strlen(str_arg);
          if (str_len*2+1 <= sizeof(buf) - i - 2)
          {
            buf[i++]= '\'';
            i+= mysql_real_escape_string(&mysql, &buf[i], str_arg, str_len);
            buf[i++]= '\'';
          }
          break;
        }
        ++ph;
      }
      else
        buf[i++]= p[0];
      ++p;
    }
    buf[i]= '\0';

    if (do_nonblock)
    {
      status= mysql_real_query_start(&err, &mysql, buf, i);
      while (status)
      {
        status= wait_for_mysql(&mysql, status);
        status= mysql_real_query_cont(&err, &mysql, status);
      }
    }
    else
      err= mysql_real_query(&mysql, buf, i);

    if (err)
      fatal_mysql("mysql_real_query() returns error");

    if (!fetch_results)
      return;

    if (do_nonblock)
    {
      res= mysql_use_result(&mysql);
      if (!res)
        fatal_mysql("mysql_use_result() returns error");
      for (;;)
      {
        status= mysql_fetch_row_start(&row, res);
        while (status)
        {
          status= wait_for_mysql(&mysql, status);
          status= mysql_fetch_row_cont(&row, res, status);
        }
        if (!row)
          break;
      }
      if (mysql_errno(&mysql))
        fatal_mysql("Got error while retrieving rows");
    }
    else
    {
      res= mysql_store_result(&mysql);
      if (!res)
        fatal_mysql("mysql_store_result() returns error");
      while ((row= mysql_fetch_row(res)) != NULL)
        ;
    }
    mysql_free_result(res);
  }
}


static void
do_queryq(struct query *q, ...)
{
  va_list ap;

  va_start(ap, q);
  do_vqueryq(q, ap, 0);
  va_end(ap);
}


static void
do_queryq_result(struct query *q, ...)
{
  va_list ap;

  va_start(ap, q);
  do_vqueryq(q, ap, 1);
  va_end(ap);
}


static void
do_queryf(const char *q_str, ...)
{
  va_list ap;
  struct query *q;

  va_start(ap, q_str);
  q= get_vqueryf(q_str, ap);
  do_queryq(q);
  free_query(q);
  va_end(ap);
}


static int
try_to_connect(void)
{
  MYSQL *l_mysql;

  mysql_close(&mysql);
  mysql_init(&mysql);
  mysql_options(&mysql, MYSQL_OPT_NONBLOCK, 0);
  if (do_nonblock)
  {
    int status;

    status= mysql_real_connect_start(&l_mysql, &mysql, NULL, "root", NULL,
                                     "test", 0, "pgo_data/mysql.sock", 0);
    while (status)
    {
      status= wait_for_mysql(&mysql, status);
      status= mysql_real_connect_cont(&l_mysql, &mysql, status);
    }
  }
  else
  {
    l_mysql= mysql_real_connect(&mysql, NULL, "root", NULL,
                                "test", 0, "pgo_data/mysql.sock", 0);
  }

  return (l_mysql != NULL);
}


static void
reconnect(void)
{
  if (!try_to_connect())
    fatal_mysql("failed to connect to mysqld");
  if (do_binlog_format == 0)
    do_queryf("SET binlog_format=statement");
  else if (do_binlog_format == 1)
    do_queryf("SET binlog_format=mixed");
  else if (do_binlog_format == 1)
    do_queryf("SET binlog_format=row");
}


static void
install_server(void)
{
  int err;
  FILE *f;
  int c;

  /*
    Lets make the test data directory unreadable to other than the user.
    We do not want to allow others access to the socket to be able to
    access the server and run arbitrary query as SUPER.
  */
  err= mkdir("pgo_data", 0700);
  if (err)
    fatal("Failed to create mysqld data directory pgo_data/");

  symlink("../../scripts/fill_help_tables.sql",
          "scripts/fill_help_tables.sql");
  symlink("../../scripts/mysql_system_tables.sql",
          "scripts/mysql_system_tables.sql");
  symlink("../../scripts/mysql_system_tables_data.sql",
          "scripts/mysql_system_tables_data.sql");
  symlink("../../scripts/mysql_performance_tables.sql",
          "scripts/mysql_performance_tables.sql");

  f= popen("sh scripts/mysql_install_db --no-defaults --srcdir=\"$(pwd)\" "
           "--datadir=pgo_data", "r");
  while ((c= getc(f)) != EOF)
    putchar(c);
  err= pclose(f);
  if (err == -1)
    fatal("mysql_install_db failed");
}


static void
start_server(void)
{
  char cmdline[2000];

  mysqld_pid= fork();
  if (mysqld_pid == (pid_t)-1)
    fatal("Failed to fork()");
  if (mysqld_pid != 0)
  {
    /* Parent. */
    int i;

    for (i= 0; i < 200; ++i)
    {
      if (try_to_connect())
        return;
      usleep(100000);
    }
    fatal_mysql("mysqld failed to start within 20 seconds");
  }

  snprintf(cmdline, sizeof(cmdline),
           "sql/mysqld --no-defaults --language=\"$(pwd)/sql/share/english\" "
           "--basedir=\"$(pwd)\" --datadir=pgo_data "
           "--socket=\"$(pwd)/pgo_data/mysql.sock\" --skip-networking "
           "--secure-file-priv=\"$(pwd)/pgo_data\" "
           "--innodb-buffer-pool-size=128M%s",
           (do_binlog ? " --log-bin=master_bin --server-id=1" : ""));

  /* Now we are running in the child. */
  execl("/bin/sh", "/bin/sh", "-c", cmdline, NULL);
  /* We only come here if exec failed. */
  fatal("execl() failed");
}

static void
stop_server(void)
{
  int status;

  do_queryf("shutdown");

  if (mysqld_pid <= 0)
    return;
  waitpid(mysqld_pid, &status, 0);
  if (!WIFEXITED(status))
    fatal("mysqld did not exit normally (did it crash?)");
  if (WEXITSTATUS(status))
    fatal("mysqld exited with non-zero status");
  mysqld_pid= 0;
}


static void
setup_schema_eng(const char *engine)
{
  do_queryf("CREATE TABLE test.t1_%s (\n"
            "  a INT NOT NULL PRIMARY KEY,\n"
            "  v INT,\n"
            "  s VARCHAR(50) NOT NULL,\n"
            "  c CHAR(40),\n"
            "  KEY (v),\n"
            "  KEY (s)\n"
            ") ENGINE=%s\n" , engine, engine);
  do_queryf("CREATE TABLE test.t2_%s (\n"
            "  a INT NOT NULL PRIMARY KEY AUTO_INCREMENT,\n"
            "  v INT\n"
            ") ENGINE=%s\n" , engine, engine);
}


static void
mk_string(char *buf, int size, int a, int b)
{
  int i;
  static const char data[]=
    "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ*([]%.!@#<>";

  --size;
  for (i= 0; i < (a % size); ++i)
    buf[i]= data[(b+i)%(sizeof(data)-1)];
  buf[i]= 0;
}


static void
pl_insert(const char *engine)
{
  int i, j, k;
  struct query *q1, *q2;
  char s1[31], s2[21];

  q1 = get_queryf("INSERT INTO test.t1_%s VALUES (?d, ?d, ?s, ?s)", engine);
  q2 = get_queryf("INSERT INTO test.t2_%s (v) VALUES (?d)", engine);

  i = 0;
  j = 42;
  k = 11;
  do
  {
    mk_string(s1, sizeof(s1), j, k);
    mk_string(s2, sizeof(s2), k, j);
    do_queryq(q1, i, j, s1, s2);
    do_queryq(q2, k);
    j= (j + B1) % M;
    k= (k + A1) % M;
  } while ((i= (i+A2)%M) != 0);

  free_query(q2);
  free_query(q1);
}


static void
pl_pk_select(const char *engine)
{
  struct query *q;
  int i;

  q= get_queryf("SELECT v, s FROM test.t1_%s WHERE a=?d", engine);
  i= 0;
  do
  {
    do_queryq_result(q, i);
  } while ((i= (i + A1)%M) != 0);
  free_query(q);
}


static void
pl_range_select(const char *engine)
{
  struct query *q;
  int i;

  q= get_queryf("SELECT a, c FROM test.t1_%s WHERE a BETWEEN ?d AND ?d",
                engine);
  i= 0;
  do
  {
    do_queryq_result(q, i-8, i+8);
  } while ((i= (i + A1)%M) != 0);
  free_query(q);
}


static void
pl_join_select(const char *engine)
{
  struct query *q;
  int i;

  q= get_queryf("SELECT A.v, B.a"
                " FROM test.t2_%s B"
                " JOIN test.t1_%s A ON (B.v = A.v)"
                " WHERE B.a = ?d", engine, engine);

  i= 0;
  do
  {
    do_queryq_result(q, i);
  } while ((i= (i + A1)%M) != 0);

  free_query(q);
}


/* Do a simple non-indexed int update. */
static void
pl_update1(const char *engine)
{
  struct query *q;
  int i;

  q= get_queryf("UPDATE test.t2_%s SET v=v+1 WHERE a=?d", engine);

  i= 0;
  do
  {
    do_queryq(q, i);
  } while ((i= (i+A1)%M) != 0);

  free_query(q);
}


/* Do update on indexed int,varchar, and on unindexed char. */
static void
pl_update2(const char *engine)
{
  struct query *q;
  int i;
  char s[21];

  q= get_queryf("UPDATE test.t1_%s SET v=?d, s=?s, c=?s WHERE a=?d", engine);

  i= 0;
  do
  {
    mk_string(s, sizeof(s), i, i);
    do_queryq(q, i, s, s, i);
  } while ((i= (i+A1)%M) != 0);

  free_query(q);
}


static void
pl_delete(const char *engine)
{
  int i;
  struct query *q1, *q2;

  q1 = get_queryf("DELETE FROM test.t1_%s WHERE a=?d", engine);
  q2 = get_queryf("DELETE FROM test.t2_%s", engine);

  i = 0;
  do
  {
    do_queryq(q1, i);
  } while ((i= (i+A2)%M) != 0);
  do_queryq(q2);

  free_query(q2);
  free_query(q1);
}


int
main(int argc, char *argv[])
{
  int a1, a2, a3, a4, a5;
  const char *all_engines[]= {
    "innodb",
    "myisam"
  };

  mysql_init(&mysql);
  install_server();
  do_binlog= 0;
  start_server();
  setup_schema_eng("innodb");
  setup_schema_eng("myisam");

  /* Loop over binlog disabled, enabled. */
  for (a1= 0; a1 <= 1; ++a1)
  {
    if (a1 == 1)
    {
      stop_server();
      do_binlog= 1;
      start_server();
    }

    /* Loop over binlog formats, if enabled. */
    for (a2= (do_binlog ? 0 : -1); a2 <= (do_binlog ? 2 : -1); ++a2)
    {
      if (a2 >= 0)
        do_binlog_format= a2;

      /* Loop over plain or non-blocking client API. */
      for (a3= 0; a3 <= 1; ++a3)
      {
        do_nonblock= a3;
        reconnect();

        /* Loop over plain or prepared statements. */
        for (a4= 0; a4 <= 1; ++a4)
        {
          do_prepared= a4;

          /* Loop over engines. */
          for (a5= 0; a5 < sizeof(all_engines)/sizeof(all_engines[0]); ++a5)
          {
            const char *engine= all_engines[a5];

            pl_insert(engine);
            pl_pk_select(engine);
            pl_range_select(engine);
            pl_join_select(engine);
            pl_update1(engine);
            pl_update2(engine);
            pl_delete(engine);
          }
        }
      }
    }
  }
  stop_server();
  mysql_close(&mysql);
  mysql_server_end();

  return 0;
}
