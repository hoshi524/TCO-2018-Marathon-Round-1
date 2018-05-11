#include <bits/stdc++.h>
#include <sys/time.h>
using namespace std;

constexpr double ticks_per_sec = 2800000000;
constexpr double ticks_per_sec_inv = 1.0 / ticks_per_sec;
inline double rdtsc() {
  uint64_t lo, hi;
  asm volatile("rdtsc" : "=a"(lo), "=d"(hi));
  return ((hi << 32) | lo) * ticks_per_sec_inv;
}

inline unsigned get_random() {
  static unsigned y = 2463534242;
  return y ^= (y ^= (y ^= y << 13) >> 17) << 5;
}

constexpr int MAX_N = 1 << 8;

int N;
double P[MAX_N][2];
double D[MAX_N][MAX_N];

double calcDistance(int a, int b) {
  int x = P[a][0] - P[b][0];
  int y = P[a][1] - P[b][1];
  return sqrt(x * x + y * y);
}

struct Node {
  bool cities;
  int size;
  int edge[MAX_N];
};
Node node[MAX_N];

void prim() {
  static double mincost[MAX_N];
  static int minedge[MAX_N];
  static int used[MAX_N];
  for (int i = 0; i < N; ++i) {
    mincost[i] = INT_MAX;
    used[i] = false;
    node[i].size = 0;
  }
  mincost[0] = 0;
  while (true) {
    int v = -1;
    for (int u = 0; u < N; ++u) {
      if (!used[u] and (v == -1 or mincost[u] < mincost[v])) v = u;
    }
    if (v == -1) break;
    if (mincost[v] > 1e-10) {
      int u = minedge[v];
      node[v].edge[node[v].size++] = u;
      node[u].edge[node[u].size++] = v;
    }
    used[v] = true;
    for (int u = 0; u < N; ++u) {
      if (mincost[u] > D[v][u]) {
        mincost[u] = D[v][u];
        minedge[u] = v;
      }
    }
  }
}

class RoadsAndJunctions {
 public:
  vector<int> buildJunctions(int S, const vector<int>& cities,
                             double junctionCost, double failureProbability) {
    N = cities.size() / 2;
    for (int i = 0; i < N; ++i) {
      P[i][0] = cities[i * 2 + 0];
      P[i][1] = cities[i * 2 + 1];
    }
    for (int i = 0; i < N; ++i) {
      for (int j = i + 1; j < N; ++j) {
        double d = calcDistance(i, j);
        D[i][j] = d;
        D[j][i] = d;
      }
    }
    return vector<int>();
  }

  vector<int> buildRoads(const vector<int>& junctionStatus) {
    prim();
    vector<int> ret(2 * (N - 1));
    for (int i = 0, t = 0; i < N; ++i) {
      Node& n = node[i];
      for (int j = 0; j < n.size; ++j) {
        int k = n.edge[j];
        if (i > k) continue;
        ret[2 * t + 0] = i;
        ret[2 * t + 1] = k;
        ++t;
      }
    }
    return ret;
  }
};

// -------8<------- end of solution submitted to the website -------8<-------
template <class T>
void getVector(vector<T>& v) {
  int s = v.size();
  for (int i = 0; i < s; ++i) cin >> v[i];
}

int main() {
  RoadsAndJunctions rj;
  int S, C;
  cin >> S >> C;
  vector<int> cities(C);
  getVector(cities);
  double junctionCost, failureProbability;
  cin >> junctionCost >> failureProbability;

  vector<int> ret =
      rj.buildJunctions(S, cities, junctionCost, failureProbability);
  cout << ret.size() << endl;
  for (int i = 0; i < (int)ret.size(); ++i) cout << ret[i] << endl;
  cout.flush();

  int J;
  cin >> J;
  vector<int> junctionStatus(J);
  getVector(junctionStatus);

  ret = rj.buildRoads(junctionStatus);
  cout << ret.size() << endl;
  for (int i = 0; i < (int)ret.size(); ++i) cout << ret[i] << endl;
  cout.flush();
}