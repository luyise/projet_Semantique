
int x = 2;

void main() {
    int i;
    for (i = 0; i < 5; i++) {
        int y;
        if (i%2 == 0) {
            y = 1;
        } else {
            y = y + 1;
        }
        x = y;
    }
}
