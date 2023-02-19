#include <sys/mman.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <signal.h>

int main() {
  // Get our read/write/exec memory to work with
  void *p = mmap((void *)0x10000, 0x10000,
                 PROT_EXEC | PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
  if ((intptr_t)p == -1) {
    perror("mmap");
    return 1;
  }
  // A little visual output to reassure us...
  printf("%p\n", p);
  fflush(stdout);

  // breakpoint for the test to start at
  asm("int $3");
  return 0;
}
