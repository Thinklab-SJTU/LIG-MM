void *mallocN(int n);
void exit(int n);
int strlen(const char *str);
char *strcpy(char *dest, const char *src);
int strcmp(const char *str1, const char *str2);

unsigned hash(char *s) {
  unsigned n, i;
  int c;

  n = 0;
  i = 0;
  c = s[0];
  while (c) {
    n = n * 65599u + (unsigned)c;
    i = i + 1;
    c = s[i];
  }
  return n;
}

struct cell {
  char *key;
  unsigned value;
  struct cell *next;
};

enum {N = 109};

struct hashtable {
  struct cell *buckets[N];
};

char *copy_string(char *s) {
  int i, n;
  char *p;

  n = strlen(s) + 1;
  p = mallocN(n);
  if (!p) exit(1);
  strcpy(p, s);
  return p;
}

// struct hashtable *new_hash_table() {
//   int i;
//   struct hashtable *p;
//   p = (struct hashtable *)malloc(sizeof(*p));
//   if (!p) exit(1);
//   for (i=0; i<N; i++) p->buckets[i] = (void *)0;
//   return p;
// }

struct cell *new_cell(char *key, unsigned value, struct cell *next) {
  struct cell *p;
  p = mallocN(sizeof(*p));
  if (!p) exit(1);
  p->key = copy_string(key);
  p->value = value;
  p->next = next;
  return p;
}

unsigned hash_table_get(struct hashtable *table, char *s) {
  unsigned h, b;
  struct cell *p;

  h = hash(s) % N;
  p = table->buckets[h];
  while (p) {
    if (strcmp(p->key, s) == 0)
      return p->count;
    p = p->next;
  }
  return 0;
}

void set_list(struct cell **r0, char *s, unsigned v) {
  struct cell *p, **r;
  r = r0;
  while (1) {
    p = *r;
    if (!p) {
      *r = new_cell(s, v, (void *)0);
      return;
    }
    if (strcmp(p->key, s) == 0) {
      p->value = v;
      return;
    }
    r = &(p->next);
  }
}  

void hash_table_set(struct hashtable *table, char *s, unsigned v) {
  unsigned h;
  h = hash(s) % N;
  set_list(&(table->buckets[h]), s, v);
}
