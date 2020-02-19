#include <iostream>
#include <string>
#include <stdlib.h>
#include <cstring>

using namespace std;

bool get_file_name(int argc, char *argv[], char* file_name, int k, char* format){
    if (file_name == NULL){
        printf( "Allocation memory failed");
        file_name = NULL;
        return false;
    }
    for (int i = 0; i < strlen(argv[k]); i++){
        file_name[i] = argv[k][i];
    }
    file_name[strlen(argv[k])] = '\0';
    if (strlen(file_name) < 4){
        printf("Incorrect format of the input data");
        return false;
    }
    format[0] = file_name[strlen(argv[k]) - 3];
    format[1] = file_name[strlen(argv[k]) - 2];
    format[2] = file_name[strlen(argv[k]) - 1];
    return true;
}

bool read_file(int argc, char *argv[], int &type, int &w, int &h, int &dummy, unsigned char** _p, char* format){
    char *file_name;
    file_name = (char*)malloc(sizeof(char) * 100);
    if (!get_file_name(argc, argv, file_name, 1, format)){
        return false;
    }
    if (file_name == NULL){
        printf( "Allocation memory failed");
        return false;
    }
    FILE *f;
    if ((format[0] != 'p' || format[1] != 'g' || format[2] != 'm') && (format[0] != 'p' || format[1] != 'p' || format[2] != 'm')){
        printf("Incorrect format of the input data");
        return false;
    }
    f = fopen(file_name, "rb");
    free(file_name);
    if (f == NULL){
        printf("The file was not found");
        return false;
    }
    int x = fscanf(f, "P%i%i%i%i\n", &type, &w, &h, &dummy);
    if (x != 4){
        printf("The file is incorrect");
        return false;
    }
    if (type == 5) {
        *_p = (unsigned char *) malloc(sizeof(unsigned char) * h * w);
    }
    else if (type == 6){
        *_p = (unsigned char *) malloc(sizeof(unsigned char) * h * w * 3);
    }
    if (*_p == NULL){
        printf( "Allocation memory failed");
        return false;
    }
    if (type == 5) {
        fread(*_p, sizeof(unsigned char), w * h, f);
    }
    else if (type == 6){
        fread(*_p, sizeof(unsigned char), w * h * 3, f);
    }
    fclose(f);
    return true;
}

class P5_class{
private:
    int type, w, h, dummy;

public:
    unsigned char* p;
    P5_class(int _type, int _w, int _h, int _dummy, unsigned char* _p){
        type = _type;
        w = _w;
        h = _h;
        dummy = _dummy;
        p = _p;
    }
    void inversion(){
        for (int i = 0; i < h; ++i) {
            for (int j = 0; j < w; ++j) {
                p[i * w + j] = 255 - p[i * w + j];
            }
        }
    }
    void vert_refl(){
        for (int i = 0; i < h; ++i) {
            for (int j = 0; j < w / 2; ++j) {
                swap(p[i * w + j], p[(i + 1) * w - j - 1]);
            }
        }
    }
    void horizontal_refl(){
        for (int i = 0; i < h / 2; ++i) {
            for (int j = 0; j < w; ++j) {
                swap(p[i * w + j], p[(h - i - 1) * w + j]);
            }
        }
    }
    void clockwise(){
        unsigned char* temp_p;
        temp_p = (unsigned char*)malloc(sizeof(unsigned char) * h * w);
        for (int i = 0; i < h; i++){
            for (int j = 0; j < w; j++){
                temp_p[j * h + h - i - 1] = p[i * w + j];
            }
        }
        free(p);
        p = temp_p;
    }
    void counter_clockwise() {
        unsigned char *temp_p;
        temp_p = (unsigned char *) malloc(sizeof(unsigned char) * h * w);
        for (int i = 0; i < h; i++) {
            for (int j = 0; j < w; j++) {
                temp_p[(w - j - 1) * h + i] = p[i * w + j];
            }
        }
        free(p);
        p = temp_p;
    }
};

class P6_class{
private:
    int type, w, h, dummy;

public:
    unsigned char* p;
    P6_class(int _type, int _w, int _h, int _dummy, unsigned char* _p){
        type = _type;
        w = _w;
        h = _h;
        dummy = _dummy;
        p = _p;
    }
    void inversion(){
        for (int i = 0; i < h; ++i) {
            for (int j = 0; j < w; ++j) {
                p[i * w * 3 + j * 3] = 255 - p[i * w * 3 + j * 3];
                p[i * w * 3 + j * 3 + 1] = 255 - p[i * w * 3 + j * 3 + 1];
                p[i * w * 3 + j * 3 + 2] = 255 - p[i * w * 3 + j * 3 + 2];
            }
        }
    }
    void vert_refl(){
        for (int i = 0; i < h; ++i) {
            for (int j = 0; j < w / 2; ++j) {
                swap(p[i * w * 3 + j * 3], p[(i + 1) * w * 3 - (j - 1) * 3]);
                swap(p[i * w * 3 + j * 3 + 1], p[(i + 1) * w * 3 - (j - 1) * 3 + 1]);
                swap(p[i * w * 3 + j * 3 + 2], p[(i + 1) * w * 3 - (j - 1) * 3 + 2]);
            }
        }
    }
    void horizontal_refl(){
        for (int i = 0; i < h / 2; ++i) {
            for (int j = 0; j < w; ++j) {
                swap(p[i * w * 3 + j * 3], p[(h - i - 1) * w * 3 + j * 3]);
                swap(p[i * w * 3 + j * 3 + 1], p[(h - i - 1) * w * 3 + j * 3 + 1]);
                swap(p[i * w * 3 + j * 3 + 2], p[(h - i - 1) * w * 3 + j * 3 + 2]);
            }
        }
    }
    void clockwise(){
        unsigned char* temp_p;
        temp_p = (unsigned char*)malloc(sizeof(unsigned char) * h * w * 3);
        for (int i = 0; i < h; i++){
            for (int j = 0; j < w; j++){
                temp_p[j * h * 3 + (h - i - 1) * 3] = p[i * w * 3 + j * 3];
                temp_p[j * h * 3 + (h - i - 1) * 3 + 1] = p[i * w * 3 + j * 3 + 1];
                temp_p[j * h * 3 + (h - i - 1) * 3 + 2] = p[i * w * 3 + j * 3 + 2];
            }
        }
        free(p);
        p = temp_p;
    }
    void counter_clockwise() {
        unsigned char *temp_p;
        temp_p = (unsigned char *) malloc(sizeof(unsigned char) * h * w * 3);
        for (int i = 0; i < h; i++) {
            for (int j = 0; j < w; j++) {
                temp_p[(w - j - 1) * h * 3 + i * 3] = p[i * w * 3 + j * 3];
                temp_p[(w - j - 1) * h * 3 + i * 3 + 1] = p[i * w * 3 + j * 3 + 1];
                temp_p[(w - j - 1) * h * 3 + i * 3 + 2] = p[i * w * 3 + j * 3 + 2];
            }
        }
        free(p);
        p = temp_p;
    }
};

int main(int argc, char *argv[])
{
    int type, w, h, dummy;
    char number;
    unsigned char *_p;
    char format_in[3];
    char format_out[3];
    if (read_file(argc, argv,type, w, h, dummy, &_p, format_in)){
        char *outfile_name;
        outfile_name = (char*)malloc(sizeof(char) * 100);
        get_file_name(argc, argv, outfile_name, 2, format_out);
        if (outfile_name == NULL){
            printf( "Allocation memory failed");
            return 0;
        }
        if (format_in[0] != format_out[0] || format_in[1] != format_out[1] || format_in[2] != format_out[2]){
            printf("Invalid input data");
            return 0;
        }
        FILE* f_out;
        f_out = fopen(outfile_name, "wb");
        free(outfile_name);
        if (type == 5){
            P5_class new_p5(type, w, h, dummy, _p);
            number = argv[3][0];
            if (number == '0'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, w, h, dummy);
                new_p5.inversion();
            }
            else if (number == '1'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, w, h, dummy);
                new_p5.horizontal_refl();
            }
            else if (number == '2'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, w, h, dummy);
                new_p5.vert_refl();
            }
            else if (number == '3'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, h, w, dummy);
                new_p5.clockwise();
            }
            else if (number == '4'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, h, w, dummy);
                new_p5.counter_clockwise();
            }
            fwrite(new_p5.p, sizeof(unsigned char), w * h, f_out);
            free(new_p5.p);
        }
        else if (type == 6){
            P6_class new_p6(type, w, h, dummy, _p);
            number = argv[3][0];
            if (number == '0'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, w, h, dummy);
                new_p6.inversion();
            }
            else if (number == '1'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, w, h, dummy);
                new_p6.horizontal_refl();
            }
            else if (number == '2'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, w, h, dummy);
                new_p6.vert_refl();
            }
            else if (number == '3'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, h, w, dummy);
                new_p6.clockwise();
            }
            else if (number == '4'){
                fprintf(f_out, "P%i\n%i %i\n%i\n", type, h, w, dummy);
                new_p6.counter_clockwise();
            }
            fwrite(new_p6.p, sizeof(unsigned char), w * h * 3, f_out);
            free(new_p6.p);
        }
        printf("Success");
        fclose(f_out);
    }
    return 0;
}