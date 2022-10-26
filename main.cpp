//==========================    INCLUDES    ====================================================
#include <iostream>
#include <sstream>
#include <fstream>
#include <iomanip>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <algorithm>
#include <iterator>
#include <vector>
#include <string>
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <deque>
#include <stack>
#include <utility>
#include <numeric>
#include <random>
#include <chrono>
#include <cstdlib>

using namespace std;

//==============================================================================================

//==========================    TYPES    =======================================================
typedef long long ll;
typedef unsigned long long ull;
typedef long double ld;
typedef std::string str;
typedef pair <ll, ll> pll;
typedef pair <string, string> pss;
typedef pair <int, int> pii;
typedef pair <double, double> pdd;
typedef pair <long double, long double> plld;
typedef vector <ll> vell;
typedef vector <int> vi;
typedef vector <bool> vebo;
typedef vector <char> veca;
typedef vector <string> vestr;
typedef vector <double> ved;
typedef vector <long double> veld;
typedef vector <pll> vpll;
typedef set <int> si;
typedef set <ll> sl;
typedef multiset <ll> msl;
typedef map <int, int> mii;
typedef map <ll, ll> mll;
typedef multimap <ll, ll> mmll;
typedef unordered_set <ll> unsl;
typedef unordered_set <int> usi;
typedef unordered_map <ll, ll> unml;
typedef unordered_map <int, int> umii;
typedef queue <ll> qll;
//==============================================================================================

//==========================    DEFINES    =====================================================
#define pb push_back
#define out std::cout
#define in std::cin
#define fi first
#define vec vector
#define se second
#define null nullptr
#define spc " "
#define boo() booster()
#define del erase
#define into insert
#define jmp '\n'
#define be begin()
#define en end()
#define rb rbegin()
#define re rend()
#define mp make_pair
#define sz size()
#define pow2(x) ((x) * (x))
#define pow3(x) ((x) * (x) * (x))
#define min3(a, b, c) min(ll(a), min(ll(b), ll(c)))
#define max3(a, b, c) max(ll(a), max(ll(b), ll(c)))
#define fori(x) for (ll i = 0; i < (x); i++)
#define fordowni(x) for (ll i = ((x) - 1); i >= 0; i--)
#define forj(x) for (ll j = 0; j < (x); j++)
#define fordownj(x) for (ll j = ((x) - 1); j >= 0; j--)
#define forn(i, n) for (ll i = 0; (i) < (n); (i)++)
#define fordownn(i, n) for (ll i = ((n) - 1); (i) >= 0; (i)--)
#define all(i, a, b) for (ll i = (a); (i) < (b); (i)++)
#define alldown(i, a, b) for (ll i = (a); (i) >= (b); (i)--)
#define sim signed main()
//==============================================================================================

//=====================         CONST       ====================================================
const ld ZERO = 1e-15;
const ld EPS = 1e-10;
const ll MAXN = 100500;
const ld PI = acos (-1);
const ll MAXMOD = 1e9 + 7;
const int SIZE = 100500;
vell primals;
vell factorialsOfAlls;
//==============================================================================================

//=====================    FUNC DECLARATIONS    ================================================
ll gcd (ll a, ll c);
ll lcm (ll a, ll c);
ll getMod (str s, ll n);
void booster ();
void getPrimalCheck ();
ll primal_rest (ll a);
ll getDivsOf (ll x);
vell getAllDivs ();
ll mulmod (ll x, ll y, ll m);
ll euler (ll n);
ll binModExp (ll x, ll exp, ll mod);
ll factorial (ll n, ll m);
ll fact (ll n);
ll factmod (ll x);
ll ex_gcd (ll a, ll c, ll & x, ll & y);
ll revermod (ll number, ll mod);
void getAllFactors (ll to);
ll preCNK (ll n, ll k, ll mod);
ll curCNK (ll n, ll k, ll mod);
ll accurate_cnk (ll n, ll k);
ll sap (ll s, ll f, ll c);
ll bin_pow(ll a, ll n);


//=====================           CODE            ==============================================
//==============================================================================================

vector<vell> generate_table_v1(ll len, ll wid) {
    vector<vell> result(len, vell(wid));
    for (ll i = 0; i < len; ++i) {
        for (ll j = 0; j < wid; ++j) {
            result[i][j] = (len / wid * i + j) * 2;
        }
    }
    return result;
}

vector<vell> generate_table_v2(ll len, ll wid) {
    vector<vell> result(len, vell(wid));
    for (ll i = 0; i < len; ++i) {
        for (ll j = 0; j < wid; ++j) {
            result[i][j] = (len / wid * i * j) * 2;
        }
    }
    return result;
}

void print_table(vector<vell> &matrix) {
    ull len = matrix.sz;
    if (len == 0) return;
    ull wid = matrix[0].sz;
    if (wid == 0) return;

    for (int i = 0; i < len; ++i) {
        for (int j = 0; j < wid; ++j) {
            cout << matrix[i][j] << '\t';
        }
        cout << "\n";
    }
}

ll support_bin(vector<vell> &matrix, ll left, ll right, ll j, ll target) {
    ll ans = left;
    while (left <= right) {
        ll mid = (left + right) / 2;
        if (matrix[mid][j] < target) {
            ans = mid;
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }
    if (ans == matrix.sz - 1 && matrix[matrix.sz - 1][j] < target) return ans+1;
    return ans;
}

ll expo_algo(vector<vell> &table, ll i_start, ll j, ll target) {
    if (!i_start) i_start++;
    while (i_start < table.sz && table[i_start][j] < target)
        i_start *= 2;
    return support_bin(table, i_start/2, min(i_start, (ll)table.sz-1),j, target);
}

bool exp_solve(vector<vell> &matrix, ll target) {
    ll n = static_cast<ll>(matrix.sz);
    ll m = static_cast<ll>(matrix[0].sz);
    ll i = 0, j = m - 1;
    while (i > -1 && i < matrix.sz && j > -1 && j < matrix[0].sz) {
        if (matrix[i][j] == target)
            return true;
        if (matrix[i][j] > target)
            j--;
        else {
            i = expo_algo(matrix, i, j, target);
            if (i >= n) return false;
            i++;
        }
    }
    return false;
}

bool linear_solve(vector<vell> &matrix, ll target) {
    int i = 0;
    int j = static_cast<int>(matrix[0].sz) - 1;
    while (i > -1 && i < matrix.sz && j > -1 && j < matrix[0].sz) {
        if (matrix[i][j] > target) {
            j--;
        } else if (matrix[i][j] < target) {
            i++;
        } else {
            return true;
        }
    }
    return false;
}

bool log_solve(const vector<vell> &matrix, ll target) {
    fori(matrix.sz) {
        int l = 0, r = static_cast<int>(matrix[0].sz - 1);
        while (l <= r) {
            int mid = (l + r) / 2;
            if (matrix[i][mid] > target) {
                r = mid - 1;
            } else if (matrix[i][mid] < target) {
                l = mid + 1;
            } else {
                return true;
            }
        }
    }
    return false;
}

ll get_avr_log(vector<vell> &matrix, ll target) {
    ll avr = 0;
    int reps = 100;
    fori(reps) {
        auto start = chrono::high_resolution_clock::now();
        log_solve(matrix, target);
        auto stop = chrono::high_resolution_clock::now();
        ll log_duration = duration_cast<chrono::nanoseconds>(stop - start).count();
        avr += log_duration;
    }
    return avr/reps;
}
ll get_avr_linear(vector<vell> &matrix, ll target) {
    ll avr = 0;
    int reps = 100;
    fori(reps) {
        auto start = chrono::high_resolution_clock::now();
        linear_solve(matrix, target);
        auto stop = chrono::high_resolution_clock::now();
        ll log_duration = duration_cast<chrono::nanoseconds>(stop - start).count();
        avr += log_duration;
    }
    return avr/reps;
}
ll get_avr_exp(vector<vell> &matrix, ll target) {
    ll avr = 0;
    int reps = 100;
    fori(reps) {
        auto start = chrono::high_resolution_clock::now();
        exp_solve(matrix, target);
        auto stop = chrono::high_resolution_clock::now();
        ll log_duration = duration_cast<chrono::nanoseconds>(stop - start).count();
        avr += log_duration;
    }
    return avr/reps;
}

void make_test() {
    ll n = bin_pow(2, 13);
    ll m = bin_pow(2, 1);
    ofstream myfile;
    myfile.open ("сsvlog.txt");
    while (n >= m) {
        //generating
        vector<vell> table1 = generate_table_v1(m, n);
        vector<vell> table2 = generate_table_v2(m, n);
        ll target1 = 2*n + 1;
        ll target2 = 16*n + 1;
        //log execution
        ll avr_log1 = get_avr_log(table1, target1);
        ll avr_log2 = get_avr_log(table2, target2);
        //line execution
        ll avr_lin1 = get_avr_linear(table1, target1);
        ll avr_lin2 = get_avr_linear(table2, target2);
        //exp execution
        ll avr_exp1 = get_avr_exp(table1, target1);
        ll avr_exp2 = get_avr_exp(table2, target2);
        //logging
        m *= 2;

        myfile << m << "," << avr_lin1 << "," << avr_lin2 << ",m,lin1,lin2\n";
        myfile << m << ',' << avr_log1 << "," << avr_log2 << ",m,log1,log2\n";
        myfile << m << ',' << avr_exp1 << "," << avr_exp2 << ",m,exp1,exp2\n";
    }
    myfile.close();
}

sim {
    make_test();
};
//==============================================================================================
//=====================     FUNC IMPLEMENTATIONS    ==============================================
ll bin_pow (ll a, ll n) {
    ll res = 1;
    while (n)
        if (n & 1) {
            res *= a;
            --n;
        }
        else {
            a *= a;
            n >>= 1;
        }
    return res;
}

void booster () {
    std::ios::sync_with_stdio (false);
    std::cin.tie (nullptr);
    std::cout.tie (nullptr);
}

ll sap (ll start, ll fin, ll count_el) {
    return (start + fin) * count_el / 2;
}

long long gcd (long long a, long long c) {
    ll t;
    while (c != 0) {
        t = c;
        c = a % c;
        a = t;
    }
    return a;
}

ll ex_gcd (ll a, ll c, ll & x, ll & y) {
    if (c == 0) {
        x = 1;
        y = 0;
        return a;
    }
    ll x1, y1;
    ll d = ex_gcd (c, a % c, x1, y1);
    x = y1;
    y = x1 - (a / c) * y1;
    return d;
}

long long lcm (long long a, long long c) {
    return (a * c) / gcd (a, c);
}

ll getMod (str s, ll n) {
    ll i = 0;
    ll cur = 0;
    while (i < s.size ()) {
        while (cur < n && i < s.length ())
            cur = cur * 10 + s[i++] - '0';
        cur = cur % n;
    }
    return cur;
}

ll mulmod (ll x, ll y, ll m) {
    x = x % m;
    y = y % m;
    ll result = 0;
    while (y) {
        if (y & 1) {
            result += x;
            result %= m;
        }
        y >>= 1;
        if (x < m - x) {
            x <<= 1;
        } else {
            x -= (m - x);
        }
    }
    return result;
}

ll binModExp (ll x, ll exp, ll mod) {
    ll ans = 1;
    while (exp != 0) {
        if (exp % 2) {
            ans = ans * x % mod;
        }
        exp /= 2;
        x = x * x % mod;
    }
    return ans % mod;
}

ll revermod (ll number, ll mod) {
    ll res = gcd (number, mod);
    if (res != 1) {
        number /= res;
        mod /= res;
    }
    ll tmp1, tmp2;
    ex_gcd (number, mod, tmp1, tmp2);
    if (tmp1 < 0) {
        return tmp1 + mod;
    } else {
        return tmp1;
    }
}

ll euler (ll n) {
    ll ans = 1;
    ll sq = (ll) sqrt ((ld) n + .1);
    for (int i = 2 ; i <= sq ; ++i) {
        if (n % i == 0) {
            n /= i;
            ans *= i - 1;
            while (n % i == 0) {
                n /= i;
                ans *= i;
            }
        }
    }
    if (n > 1) {
        ans *= n - 1;
    }
    return ans;
}

vell getAllDivs () {
    vell divs (SIZE, 1);
    for (int i = 2 ; i < SIZE ; ++i) {
        for (int j = i ; j < SIZE ; j += i) {
            divs[j] += 1;
        }
    }
    return divs;
}

ll getDivsOf (ll x) {
    ll count = 1;
    ll sq = (ll) sqrt ((ld) x + .1);
    int i = 0;
    while (x != 1 && primals[i] <= sq) {
        int local = 1;
        while (x % primals[i] == 0) {
            local++;
            x /= primals[i];
        }
        i++;
        count *= local;
    }
    if (x != 1) {
        return count * 2;
    }
    return count;
}

ll factorial (ll n, ll m) {
    ll ans = 1;
    int i = 2;
    while (i <= n) {
        ans *= i;
        i++;
        ans %= m;
    }
    return ans;
}

ll factmod (ll x) {
    int i = 1;
    ll ans = 1;
    while (i < x) {
        ans *= ++i;
        ans %= MAXMOD;
    }
    return ans;
}

ll fact (ll n) {
    ll ans = 1;
    int i = 2;
    while (i <= n) {
        ans *= i;
        i++;
    }
    return ans;
}

void getAllFactors (ll to) {
    factorialsOfAlls.resize (to + 1);
    factorialsOfAlls[0] = 1;
    for (int i = 1 ; i <= to ; ++i) {
        factorialsOfAlls[i] = factorialsOfAlls[i - 1] * i % MAXMOD;
    }
}

ll preCNK (ll n, ll k, ll mod) {
    ll chisl = factorialsOfAlls[n];
    ll znk = factorialsOfAlls[k];
    ll znkn = factorialsOfAlls[n - k];
    ll zn = mulmod (znk, znkn, mod);
    ll rever = revermod (zn, mod);
    ll ans = mulmod (chisl, rever, mod);
    return ans;
}

ll curCNK (ll n, ll k, ll mod) {
    ll chisl = factorial (n, mod);
    ll znk = factorial (k, mod);
    ll znkn = factorial (n - k, mod);
    ll zn = mulmod (znk, znkn, mod);
    ll rever = revermod (zn, mod);
    ll ans = mulmod (chisl, rever, mod);
    return ans;
}

ll accurate_cnk (ll n, ll k) {
    if (k > n || k < 0) return 0;
    if (k == n || !k) return 1;
    if (k == 1 || k == n - 1) return n;

    ll sc = max (k, n - k);
    ll szn = min (k, n - k);
    vell zn (szn - 1);
    vell s (n - sc);
    s[0] = sc + 1;
    zn[0] = 2;

    all(i, 1, s.sz) { s[i] = s[i - 1] + 1; }
    all(i, 1, zn.sz) {
        zn[i] = zn[i - 1] + 1;
    }

    int i = 0, j = 0;
    while (i < s.sz) {
        while (j < zn.sz && zn[j] * 2 < s[i])
            j++;
        if (j < zn.sz && i < s.sz && s[i] % zn[j] == 0) {
            zn[j++] = 1;
            s[i++] = 2;
        } else {
            i++;
        }
    }

    ll ansu = 1, ansd = 1;
    all(x, 0, zn.sz) { ansd *= zn[x]; }
    all(y, 0, s.sz) {
        ll temp = gcd (ansu, ansd);
        ansu *= s[y];
        ansu /= temp;
        ansd /= temp;
    }

    return ansu / ansd;
}

void getPrimalCheck () {
    bool num[SIZE] = {false};
    num[0] = num[1] = false;
    for (int i = 2 ; i < SIZE ; ++i) {
        if (num[i] == 0) {
            primals.pb (i);
            for (int j = i * 2 ; j < SIZE ; j += i) {
                num[j] = true;
            }
        }
    }
}

ll primal_rest (ll a) {
    int i = 0;
    ll x = (ll) sqrt (a);
    while (primals[i] <= x) {
        if (a % primals[i] == 0) {
            return 0;
        }
        ++i;
    }
    return 1;
}

//==============================================================================================
