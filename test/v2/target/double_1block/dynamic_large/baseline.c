int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

int main(){
    for (int i = 0;; i++)
    {
        int x = 0;
        for (int j = 0; j < 100; j++)
        {
            __CPROVER_assert(x == 0, "postcondition");
        }
      
    }
}