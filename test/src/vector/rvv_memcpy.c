#include <stdlib.h>
#include <riscv_vector.h>

int getchar();
int putchar(int c);

void* memcpy_vec(void *dst, void *src, size_t n) {
  void *save = dst;
  for (size_t vl; n > 0; n -= vl, src += vl, dst += vl) { 
    vl = __riscv_vsetvl_e8m8(n);
    vuint8m8_t vec_src = __riscv_vle8_v_u8m8(src, vl);
    __riscv_vse8_v_u8m8(dst, vec_src, vl);
  }
  return save;
}

int main() {
  char *s = "begin c\n";
  char *p;
  for (p = s; p < s + 8; p++) putchar(*p);
    
  const int N = 256;
  int golden[N];
  for (int i = 0; i < N; i++) { golden[i] = s[i % 4]; }
  for (int i = 0; i < N; i++) { putchar(golden[i]); }

  putchar('\n');
  // UP TO HERE, no vector instructions used ^^
  int actual[N];
  memcpy_vec(actual, golden, sizeof(golden));
  for (int i = 0; i < N; i++) {
    putchar(actual[i]);
  }
  putchar('\n');
  
}
