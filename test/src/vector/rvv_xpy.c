#include <stdlib.h>
#include <riscv_vector.h>

int getchar();
int putchar(int c);


void xpy_char_reference(size_t n, const char *x, char *y) {
  for (size_t i = 0; i < n; ++i) {
    y[i] = x[i] + y[i];
  }
}

void xpy_char_rvv(size_t n, const char *x, char *y) {
  size_t l;

  vint8m2_t vx, vy;

  for (; n > 0; n -= l) {
    l = __riscv_vsetvl_e8m2(n);
    vx =__riscv_vle8_v_i8m2(x, l);
    x += l;
    vy = __riscv_vle8_v_i8m2(y, l);
    vy = __riscv_vadd_vv_i8m2(vy, vx, l);
    __riscv_vse8_v_i8m2 (y, vy, l);
    y += l;
  }
}

void xpy_int_reference(size_t n, const int *x, int *y) {
  for (size_t i = 0; i < n; ++i) {
    y[i] = x[i] + y[i];
  }
}

void xpy_int_rvv(size_t n, const int *x, int *y) {
  size_t l;

  vint32m1_t vx, vy;

  for (; n > 0; n -= l) {
    l = __riscv_vsetvl_e32m1(n);
    vx =__riscv_vle32_v_i32m1(x, l);
    x += l;
    vy = __riscv_vle32_v_i32m1(y, l);
    vy = __riscv_vadd_vv_i32m1(vy, vx, l);
    __riscv_vse32_v_i32m1 (y, vy, l);
    y += l;
  }
}

int main() {
  {
    char *s = "test1\n";
    char *p;
    for (p = s; p < s + 6; p++) putchar(*p);
  }

  const int N = 17;
  char src[N];
  char golden[N];
  char actual[N];
  
  for (int i = 0; i < N; i++) {
    golden[i] = '0';
    actual[i] = '0';
    src[i] = (i % 10);
  }

  xpy_char_reference(N, src, golden);
  xpy_char_rvv(N, src, actual);
  

  for (int i = 0; i < N; i++) {
    
    int val = golden[i];
    while (val > 0) {
      putchar('0' + (val % 10));
      val = val / 10;
    }
    putchar(' ');
  }
  putchar('\n');

  for (int i = 0; i < N; i++) {
    
    int val = actual[i];
    while (val > 0) {
      putchar('0' + (val % 10));
      val = val / 10;
    }
    putchar(' ');
  }
  putchar('\n');

  
  {
    char *s = "test2\n";
    char *p;
    for (p = s; p < s + 6; p++) putchar(*p);
  }
  const int N1 = 3;
  int src1[N1];
  int golden1[N1];
  int actual1[N1];
  
  for (int i = 0; i < N1; i++) {
    golden1[i] = (i % 3);
    actual1[i] = (i % 3);
    src1[i] = 255;
  }

  
  xpy_int_reference(N1, src1, golden1);
  xpy_int_rvv(N1, src1, actual1);
  for (int i = 0; i < N1; i++) {
    int val = golden1[i];
    while (val > 0) {
      putchar('0' + (val % 10));
      val = val / 10;
    }
    putchar(' ');
  }
  putchar('\n');

  for (int i = 0; i < N1; i++) {
    int val = actual1[i];
    while (val > 0) {
      putchar('0' + (val % 10));
      val = val / 10;
    }
    putchar(' ');
  } 
  putchar('\n');
  
  
  
}
