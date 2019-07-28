int hello(int i) { return i; }
#define MAEK(x) x;

int main(){
  int x  = 1;
  int z = -1;
  int *y = &z;
  while (x)
  {
    hello(*y);
    while (*y)
    {
      hello(*y);
      x = 2;
      *y = 2;

      while(x){
        if(*y){
          hello(*y);
        }
        hello(*y);
        *y = x;
      }
  
    }
    
  }

  while (x - z)
  {
    hello(1);
  }
  
  
  

  return 0;
}