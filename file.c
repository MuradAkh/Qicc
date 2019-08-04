int hello(int i) { return i; }
#define MAEK(x) x;

int main()
{
  int x = 1;
  int z = -1;
  int *y = &z;
  while (x)
  {
    x = z;
    hello(z);

    while (z)
    {
      *y = x;
      x = 1;

      while(x){
        hello(x);
      }

      while(x){
        while(z){
          hello(x);
        }
      }


      while (1)
      {
        hello(*y);

        if (*y)
          break;
        hello(x);
      }
    }
  }

  return 0;
}