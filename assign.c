int b;
int main() {
    b=1;
    int a[20];
    a[0] = 28;
    a[1] = a[0] / 2;
    a[2] = a[1] * 10;
    a[3] = a[2] - b;
    return a[3];
}
