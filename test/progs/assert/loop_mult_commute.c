int main(){
    int x;
    client(x);
}

int client(int x) {
	if (x>=18 && x<22){
	int a = x;
	int b = 20;
	int c=0;
	int d=0;
	for (int i=1;i<=a;++i){
		c+=b;
	}
	for (int i=1;i<=b;++i){
		d+=a;
		assert (d <= c);
	}
    assert( c == d );
	return c;

	}
	else{
	    return 0;
	  }
}
