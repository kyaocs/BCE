//
//  Utility.h
//  MSBC_GAP
//
//  Created by kai on 2022/1/21.
//

#ifndef utility_h
#define utility_h

#define miv(a,b) ((a)>(b)?(b):(a))
#define mav(a,b) ((a)<(b)?(b):(a))

#include <iostream>
#include <fstream>
#include <vector>
#include <string.h>
#include <cstdlib>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <queue>
#include <list>
#include <cmath>
#include <ctime>
#include <algorithm>
#define NDEBUG
#include <assert.h>

#include <cstdio>
#include <cstring>
#include <string>
#include <sstream>
#include <set>

using namespace std;

typedef unsigned int ui;
const int INF = 1000000000;

#define _STATISTIC_
#define _BITSET_ //use bit set to represent the adjacency matrix
#define _RECOLOR_

//#define _DEBUG_
//#define _COLORUB_
//#define _MtauPNORDER_
//#define _ER_

#define _egoN_vr_
#define _ET1_
#define _ET2_
#define _VRandOrder_
#define _Pivot_

#include <cassert>

#ifdef _BITSET_
#define set_bit(array, pos) (((array)[(pos)>>3]) |= (1<<((pos)&7)))
#define reverse_bit(array, pos) (((array)[(pos)>>3]) ^= (1<<((pos)&7)))
#define test_bit1(array, pos) (((array)[(pos)>>3])&(1<<((pos)&7)))
#define test_bit(array, pos) ((((array)[(pos)>>3])>>((pos)&7))&1)
#else
#define set_bit(array, pos) (((array)[pos]) = 1)
#define reverse_bit(array, pos) (((array)[pos]) = 1- ((array)[pos]))
#define test_bit(array, pos) ((array)[pos])
#endif

using ept = unsigned long;

#define pb push_back
#define mp make_pair

class Utility {
public:
    static FILE *open_file(const char *file_name, const char *mode) {
        FILE *f = fopen(file_name, mode);
        if(f == nullptr) {
            printf("Can not open file: %s\n", file_name);
            exit(1);
        }

        return f;
    }

    static std::string integer_to_string(long long number) {
        std::vector<ui> sequence;
        if(number == 0) sequence.pb(0);
        while(number > 0) {
            sequence.pb(number%1000);
            number /= 1000;
        }

        char buf[5];
        std::string res;
        for(ui i = sequence.size();i > 0;i --) {
            if(i == sequence.size()) sprintf(buf, "%u", sequence[i-1]);
            else sprintf(buf, ",%03u", sequence[i-1]);
            res += std::string(buf);
        }
        return res;
    }
};

/*  vector<string> v = split(s, "c")    */
vector<string> split(const string &s, const string &seperator){
    vector<string> result;
    typedef string::size_type string_size;
    string_size i = 0;
    
    while(i != s.size()){
        int flag = 0;
        while(i != s.size() && flag == 0){
            flag = 1;
            for(string_size x = 0; x < seperator.size(); ++x)
                if(s[i] == seperator[x]){
                    ++i;
                    flag = 0;
                    break;
                    }
        }
        flag = 0;
        string_size j = i;
        while(j != s.size() && flag == 0){
            for(string_size x = 0; x < seperator.size(); ++x)
                if(s[j] == seperator[x]){
                    flag = 1;
                    break;
                    }
            if(flag == 0)
                ++j;
        }
        if(i != j){
            result.push_back(s.substr(i, j-i));
            i = j;
        }
    }
    return result;
}

string integer_to_string(long long number) {
    std::vector<ui> sequence;
    if(number == 0) sequence.push_back(0);
    while(number > 0) {
        sequence.push_back(number%1000);
        number /= 1000;
    }
    
    char buf[5];
    std::string res;
    for(unsigned int i = sequence.size();i > 0;i --) {
        if(i == sequence.size()) sprintf(buf, "%u", sequence[i-1]);
        else sprintf(buf, ",%03u", sequence[i-1]);
        res += std::string(buf);
    }
    return res;
}

inline int psz(pair<vector<ui>, vector<ui>> & p)
{
    return p.first.size()+p.second.size();
}

#endif /* utility_h */


