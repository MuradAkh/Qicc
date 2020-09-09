int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

int main(){
    int x;
    int* a;
    two_sum_prev(a, x);
}

#define SIZE 320

int ind(int* arr, int i){
    return *(arr + i);
}

int two_sum_prev(int *arr, int s){	
   for (int i = 0; i < SIZE; i++){
       for (int j = 0; j < i; j++){
           if(ind(arr, j) + ind(arr, i) == s) printf("found!");
           __CPROVER_assert(j < SIZE, "postcondition");
       }
   }

}
