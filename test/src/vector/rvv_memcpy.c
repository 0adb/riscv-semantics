#include <stdlib.h>
#include <riscv_vector.h>

int getchar();
int putchar(int c);

void fill_vec(int *a, int n) {
  for (int i = 0 ; i < n; i++) {
    a[i] = (i % 4) + 97;
  }
  a[n-2]=10;
  a[n-1]=0;
}

void* memcpy_vec(void *dst, void *src, size_t n) {
  void *save = dst;
  for (size_t vl; n > 0; n -= vl, src += vl, dst += vl) {
    vl = __riscv_vsetvl_e8m8(n);
    vuint8m8_t vec_src = __riscv_vle8_v_u8m8(src, vl);
    __riscv_vse8_v_u8m8(dst, vec_src, vl);
  }
  return save;
}

void print_vec(int *a, int n) {
  int* p;
  for (p = a; p < a + n; p++) putchar(*p);
}

int main() {
  char *s = "Hello, world!\n";
  char *p;
  for (p = s; p < s + 14; p++) putchar(*p);
  // PROLOGUE, to see where things are breaking ^^
  
  const int N = 256;
  int golden[N];
  fill_vec(golden, N);
  print_vec(golden, N);
  
  // UP TO HERE, no vector instructions used ^^
  int actual[N];
  memcpy_vec(actual, golden, sizeof(golden));
  print_vec(actual, N);
  
}
