#include <stdio.h>
#define fixnum_mask 3
#define fixnum_tag 0
#define fixnum_shift 2

#define char_shift 8
#define char_tag 15
#define char_mask 255

// #b01001111
#define empty_list 79

// #b10011111
#define scheme_t 63
// #b00011111
#define scheme_f 47

long long scheme_entry();

int main(int argc, char** argv){
  long long val = scheme_entry();
  if ((val & fixnum_mask) == fixnum_tag) {
    // printf("%lld\n", val >> fixnum_shift);
    printf("%lld", val >> fixnum_shift);
  } else if (val == empty_list) {
    // printf("()\n");
    printf("()");
  } else if ((val & char_mask) == char_tag) {
    // printf("#\\%c", val >> char_shift);
    printf("#\\%c", val >> char_shift);
  } else if (val == scheme_t) {
    // printf("#t");
    printf("#t");
  } else if (val == scheme_f) {
    // printf("#f\n");
    printf("#f");
  }
  return 0;
}
