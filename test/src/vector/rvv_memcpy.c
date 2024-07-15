#include <stdlib.h>
#include <riscv_vector.h>

int getchar();
int putchar(int c);

void* memcpy_vec(void *dst, void *src, size_t n) {
  void *save = dst;
  for (size_t vl; n > 0; n -= vl, src += vl, dst += vl) { 
    vl = __riscv_vsetvl_e8m1(n);   
    vuint8m1_t vec_src = __riscv_vle8_v_u8m1(src, vl);
    __riscv_vse8_v_u8m1(dst, vec_src, vl);
  }
  return save;
}

int main() {

  char* s = "0123";
  const int N = 7;
  int golden[N];
  for (int i = 0; i < N; i++) { golden[i] = s[i % 4]; }
  
  for (int i = 0; i < N; i++) { putchar(golden[i]); }
  
  putchar('\n');
  
  int actual[N];
  
  memcpy_vec(actual, golden, sizeof(golden));
  
  for (int i = 0; i < N; i++) {
    putchar(actual[i]);
  }
  
  putchar('\n');
  
}
