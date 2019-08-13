int __CPROVER_assert(int a, char *b) {}


int main()
{
    int n;
    client(n);
}

int client(int n)
{
    int i = 0;
    int sum = 0;
    while (i <= n)
    {
        if (lib(i) == 0)
        {
            sum += i;
        }
        i++;
    }

    int j = 0;
    while (j < 100)
    {
        int k = 100;
        //relevant context
        __CPROVER_assert((lib(k) >= 0), "postcondition");
        //relevant context
        j++;
    }
    //relevant context
    return sum;
}

int lib(int a)
{
    int i = 2;
    int count = 0;
    while (i < a)
    {
        if ((a % i) != 0)
        {
            count = 1;
        }
        i++;
    }
    return count;
}