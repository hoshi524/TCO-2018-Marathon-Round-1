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

void fermatPoint(double x1, double y1, double x2, double y2, double x3,
                 double y3, double& x, double& y) {
  static double pi = acos(-1);
  static double pi23 = pi * 2 / 3;
  auto angle = [&](double x1, double y1, double x2, double y2, double x3,
                   double y3) {
    double d1x = x2 - x1;
    double d1y = y2 - y1;
    double d2x = x2 - x3;
    double d2y = y2 - y3;
    double x = (d1x * d2x + d1y * d2y) /
               sqrt((d1x * d1x + d1y * d1y) * (d2x * d2x + d2y * d2y));
    return acos(x);
  };
  {
    double t = max({
        angle(x1, y1, x2, y2, x3, y3),
        angle(x2, y2, x3, y3, x1, y1),
        angle(x3, y3, x1, y1, x2, y2),
    });
    if (isnan(t) or t >= pi23 * 0.98) {
      x = -1;
      y = -1;
      return;
    }
  }
  auto E = [&](double x1, double y1, double x2, double y2, double x3, double y3,
               double& x, double& y) {
    static double sin_ = sin(pi / 3);
    static double cos_ = cos(pi / 3);
    double dx = x2 - x1;
    double dy = y2 - y1;
    double tx1, ty1, tx2, ty2;
    tx1 = x1 + (dx * cos_ - dy * sin_);
    ty1 = y1 + (dx * sin_ + dy * cos_);
    tx2 = x1 + (dx * cos_ + dy * sin_);
    ty2 = y1 + (-dx * sin_ + dy * cos_);
    auto D = [](double x1, double y1, double x2, double y2) {
      double x = x1 - x2;
      double y = y1 - y2;
      return sqrt(x * x + y * y);
    };
    if (D(x3, y3, tx1, ty1) > D(x3, y3, tx2, ty2)) {
      x = tx1;
      y = ty1;
    } else {
      x = tx2;
      y = ty2;
    }
  };
  double dx2, dy2, dx3, dy3;
  E(x1, y1, x3, y3, x2, y2, dx2, dy2);
  E(x1, y1, x2, y2, x3, y3, dx3, dy3);
  {
    double a = (dy3 - y3) * (dx3 - x2) - (dx3 - x3) * (dy3 - y2);
    double b = (dx2 - x2) * (dy3 - y3) - (dy2 - y2) * (dx3 - x3);
    double c = a / b;
    x = x2 + c * (dx2 - x2);
    y = y2 + c * (dy2 - y2);
  }
  auto check = [&](double a) { assert(abs(a - pi23) < 1e-5); };
  check(angle(x1, y1, x, y, x2, y2));
  check(angle(x2, y2, x, y, x3, y3));
  check(angle(x3, y3, x, y, x1, y1));
}

constexpr double TIME_LIMIT = 2;
constexpr int MAX_N = 1 << 8;

int N, NC;

struct Node {
  int id, size;
  bool used;
  double x, y;
  Node* edge[MAX_N];
};
Node node[MAX_N];

inline void fermatPoint(Node& a, Node& b, Node& c, Node& d) {
  fermatPoint(a.x, a.y, b.x, b.y, c.x, c.y, d.x, d.y);
}

double calcDistance(Node& a, Node& b) {
  double x = a.x - b.x;
  double y = a.y - b.y;
  return sqrt(x * x + y * y);
}

double prim() {
  static double mincost[MAX_N];
  static Node* minedge[MAX_N];
  static bool used[MAX_N];
  static double D[MAX_N][MAX_N];
  for (int i = 0; i < N; ++i) {
    mincost[i] = 100000;
    used[i] = node[i].used;
    node[i].size = 0;
    for (int j = i + 1; j < N; ++j) {
      double d = calcDistance(node[i], node[j]);
      D[i][j] = d;
      D[j][i] = d;
    }
  }
  mincost[0] = 0;
  double d = 0;
  while (true) {
    int v = -1;
    for (int u = 0; u < N; ++u) {
      if (!used[u] and (v == -1 or mincost[u] < mincost[v])) v = u;
    }
    if (v == -1) return d;
    if (mincost[v] > 1e-10) {
      Node& a = node[v];
      Node& b = *minedge[v];
      a.edge[a.size++] = &b;
      b.edge[b.size++] = &a;
      d += mincost[v];
    }
    used[v] = true;
    for (int u = 0; u < N; ++u) {
      if (mincost[u] > D[v][u]) {
        mincost[u] = D[v][u];
        minedge[u] = &node[v];
      }
    }
  }
}

class RoadsAndJunctions {
 public:
  vector<int> buildJunctions(int S, const vector<int>& cities,
                             double junctionCost, double failureProbability) {
    for (int i = 0; i < MAX_N; ++i) {
      node[i].id = i;
    }
    N = NC = cities.size() / 2;
    for (int i = 0; i < N; ++i) {
      Node& n = node[i];
      n.x = cities[i * 2 + 0];
      n.y = cities[i * 2 + 1];
      n.used = false;
    }
    double pos[MAX_N][2];
    int ps = 0;
    double value = prim(), first = value;
    auto init = [&]() {
      N = NC + ps;
      for (int i = 0; i < ps; ++i) {
        Node& n = node[NC + i];
        n.x = pos[i][0];
        n.y = pos[i][1];
      }
    };
    for (int T = 0; T < 0xffff; ++T) {
      init();
      auto adjust = [&]() {
        {  // remove2
          bool exe = false;
          for (int i = NC; i < NC + ps; ++i) {
            Node& n = node[i];
            if (n.size < 3) {
              --ps;
              n.size = node[NC + ps].size;
              pos[i - NC][0] = pos[ps][0];
              pos[i - NC][1] = pos[ps][1];
              --i;
              exe = true;
            }
          }
          if (exe) {
            init();
            value = prim() + (N - NC) * junctionCost;
          }
        }
      };
      int o = get_random() % 2;
      if (o == 0) {
        // add
        Node& a = node[get_random() % N];
        if (a.size < 2) continue;
        int i0 = get_random() % a.size, i1;
        do {
          i1 = get_random() % a.size;
        } while (i0 == i1);
        Node& b = *a.edge[i0];
        Node& c = *a.edge[i1];
        Node& d = node[N++];
        fermatPoint(a, b, c, d);
        if (d.x < 0) continue;
        double v = prim() + (N - NC) * junctionCost;
        if (value > v) {
          value = v;
          pos[ps][0] = d.x;
          pos[ps][1] = d.y;
          ++ps;
          adjust();
        }
      } else if (o == 1) {
        // merge
        if (ps < 1) continue;
        Node& a = node[NC + get_random() % ps];
        Node& b = *a.edge[get_random() % a.size];
        Node& c = node[--N];
        if (b.id >= NC) {
          int t = 0;
          double x = 0, y = 0;
          auto add = [&](Node& e) {
            for (int i = 0; i < e.size; ++i) {
              Node& n = *e.edge[i];
              if (n.id == a.id) continue;
              if (n.id == b.id) continue;
              x += n.x;
              y += n.y;
              t++;
            }
          };
          add(a);
          add(b);
          b.x = x / t;
          b.y = y / t;
        }
        a.x = c.x;
        a.y = c.y;
        double v = prim() + (N - NC) * junctionCost;
        if (value > v) {
          value = v;
          pos[a.id - NC][0] = a.x;
          pos[a.id - NC][1] = a.y;
          if (b.id >= NC) {
            pos[b.id - NC][0] = b.x;
            pos[b.id - NC][1] = b.y;
          }
          --ps;
          adjust();
        }
      }
    }
    {
      for (int i = 0; i < ps; ++i) {
        pos[i][0] = round(pos[i][0]);
        pos[i][1] = round(pos[i][1]);
      }
      init();
      for (int i = 0; i < ps; ++i) {
        int c = 0;
        for (int j = 0; j < N; ++j) {
          Node& n = node[j];
          if (abs(pos[i][0] - n.x) > 0.5) continue;
          if (abs(pos[i][1] - n.y) > 0.5) continue;
          ++c;
        }
        if (c > 1) {
          --ps;
          pos[i][0] = pos[ps][0];
          pos[i][1] = pos[ps][1];
          --i;
        }
      }
      init();
    }
    vector<int> ret(2 * ps);
    for (int i = 0; i < ps; ++i) {
      ret[2 * i + 0] = pos[i][0];
      ret[2 * i + 1] = pos[i][1];
    }
    return ret;
  }

  vector<int> buildRoads(const vector<int>& junctionStatus) {
    for (int i = 0; i < N; ++i) {
      node[i].used = i < NC ? false : junctionStatus[i - NC] == 0;
    }
    prim();
    vector<int> ret;
    for (int i = 0; i < N; ++i) {
      Node& n = node[i];
      for (int j = 0; j < n.size; ++j) {
        int a = n.id;
        int b = n.edge[j]->id;
        if (a > b) continue;
        ret.push_back(a);
        ret.push_back(b);
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