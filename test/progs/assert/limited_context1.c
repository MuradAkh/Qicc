int __CPROVER_assert(int a, char *b) {}

void cond(int *i)
{
    int j = 0;
    //relevant context
    while (j < 30)
    {
        j++;
        __CPROVER_assert(j >= 0, "postcondition");
    }
    //relevant context
    *i++;
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

    int *z;
    *z = 2;
    while (*z < 10)
    {
        cond(z);
    }
    return sum;
}

int main()
{
    int n;
    client(n);
}
