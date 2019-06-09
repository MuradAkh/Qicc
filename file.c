#include <stdio.h>


int main(){
  int x = 1;
  while(x > 0){
        if(x < -1)break;
    x = -1;
  }

  int y = 1;
  int g = x * y;
  while(y > 0){
    if(g < -1)break;
    y = -1;
  }

   while(x > 0){
    x = -1;
  }

  return 0;
}