int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

int main(){
    int n;
    for (int i = 0; i < 100; i++)
    {
        int x = 0;
        for (int j = 0; j < 10; j++)
        {
            __CPROVER_assert(x == 0, "postcondition");
        }
      
    }
}