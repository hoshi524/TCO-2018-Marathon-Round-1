#include <bits/stdc++.h>
using namespace std;

inline double dist(double x1, double y1, double x2, double y2) {
  double x = x1 - x2;
  double y = y1 - y2;
  return sqrt(x * x + y * y);
};

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
    if (std::isnan(t) or t >= pi23 * 0.98 or t == 0) {
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
    if (dist(x3, y3, tx1, ty1) > dist(x3, y3, tx2, ty2)) {
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

constexpr int MAX_N = 1 << 8;
constexpr int dx[] = {0, 1, 0, -1, 1, 1, -1, -1, 0};
constexpr int dy[] = {1, 0, -1, 0, 1, -1, 1, -1, 0};
int N, NC;

struct Node {
  int id, size, x, y;
  bool used;
  Node* edge[MAX_N];
};
Node node[MAX_N];

inline double dist(Node& a, Node& b) { return dist(a.x, a.y, b.x, b.y); }

inline void fermatPoint(Node& a, Node& b, Node& c, Node& d) {
  double x, y;
  fermatPoint(a.x, a.y, b.x, b.y, c.x, c.y, x, y);
  if (x < 0) {
    d.x = -1;
    d.y = -1;
  } else {
    double v = 1e10;
    for (int i = x, ie = i + 2; i < ie; ++i) {
      for (int j = y, je = j + 2; j < je; ++j) {
        double t =
            dist(i, j, a.x, a.y) + dist(i, j, b.x, b.y) + dist(i, j, c.x, c.y);
        if (v > t) {
          v = t;
          d.x = i;
          d.y = j;
        }
      }
    }
  }
}

double prim() {
  static double mincost[MAX_N];
  static Node* minedge[MAX_N];
  static bool used[MAX_N];
  for (int i = 0; i < N; ++i) {
    mincost[i] = 100000;
    used[i] = node[i].used;
    node[i].size = 0;
  }
  int v = 0;
  mincost[v] = 0;
  double d = 0;
  while (true) {
    used[v] = true;
    int nv = -1;
    for (int u = 1; u < N; ++u) {
      if (used[u]) continue;
      double d = dist(node[v], node[u]);
      if (mincost[u] > d) {
        mincost[u] = d;
        minedge[u] = &node[v];
      }
      if (nv == -1 or mincost[u] < mincost[nv]) nv = u;
    }
    if (nv == -1) return d;
    v = nv;
    Node& a = node[v];
    Node& b = *minedge[v];
    a.edge[a.size++] = &b;
    b.edge[b.size++] = &a;
    d += mincost[v];
  }
}

double prim(int* p, int N) {
  static double mincost[MAX_N];
  static bool used[MAX_N];
  for (int i = 0; i < N; ++i) {
    mincost[i] = 100000;
    used[i] = false;
  }
  int v = 0;
  mincost[v] = 0;
  double d = 0;
  while (true) {
    used[v] = true;
    int nv = -1;
    int x1 = p[v] >> 16;
    int y1 = p[v] & ((1 << 16) - 1);
    for (int u = 1; u < N; ++u) {
      if (used[u]) continue;
      int x2 = p[u] >> 16;
      int y2 = p[u] & ((1 << 16) - 1);
      double d = dist(x1, y1, x2, y2);
      if (mincost[u] > d) {
        mincost[u] = d;
      }
      if (nv == -1 or mincost[u] < mincost[nv]) nv = u;
    }
    if (nv == -1) return d;
    v = nv;
    d += mincost[v];
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
    int pos[MAX_N][2];
    int ps = 0;
    auto init = [&]() {
      N = NC + ps;
      for (int i = 0; i < ps; ++i) {
        Node& n = node[NC + i];
        n.x = pos[i][0];
        n.y = pos[i][1];
      }
    };
    while (true) {
      double value = -1, x = -1, y = -1;
      init();
      double current = prim();
      Node& d = node[N++];
      for (int i = 0; i + 1 < N; ++i) {
        Node& a = node[i];
        static int list[MAX_N];
        static double D[MAX_N];
        for (int j = 0; j + 1 < N; ++j) {
          list[j] = j;
          D[j] = dist(a, node[j]);
        }
        sort(list, list + N - 1, [](int a, int b) { return D[a] < D[b]; });
        assert(i == list[0]);
        int T = 10;
        for (int j = 1; j < T; ++j) {
          Node& b = node[list[j]];
          for (int k = j + 1; k < T; ++k) {
            Node& c = node[list[k]];
            fermatPoint(a, b, c, d);
            if (d.x < 0) continue;
            double v = current - prim();
            if (value < v) {
              value = v;
              x = d.x;
              y = d.y;
            }
          }
        }
      }
      if (value * (1 - failureProbability) <= junctionCost + 1e-5) break;
      pos[ps][0] = x;
      pos[ps][1] = y;
      ++ps;
      {
        init();
        prim();
        for (int i = NC; i < NC + ps; ++i) {
          Node& n = node[i];
          if (n.size < 3) {
            --ps;
            n.size = node[NC + ps].size;
            pos[i - NC][0] = pos[ps][0];
            pos[i - NC][1] = pos[ps][1];
            --i;
          }
        }
        {
          static bool used[MAX_N];
          memset(used, false, sizeof(used));
          for (int i = NC; i < N; ++i) {
            if (used[i]) continue;
            used[i] = true;
            static int q[8];
            int qs = 0;
            q[qs++] = i;
            for (int j = 0; j < qs; ++j) {
              Node& n = node[q[j]];
              for (int k = 0; k < n.size; ++k) {
                Node& u = *n.edge[k];
                if (u.id < NC or used[u.id]) continue;
                used[u.id] = true;
                q[qs++] = u.id;
              }
            }
            init();
            prim();
            static double P[8 * 3][2];
            static int edge[8][3];
            static int toIndex[MAX_N];
            int ps = 0;
            for (int j = 0; j < qs; ++j) {
              Node& n = node[q[j]];
              assert(n.id >= NC);
              toIndex[n.id] = ps;
              P[ps][0] = n.x;
              P[ps][1] = n.y;
              ++ps;
            }
            for (int j = 0; j < qs; ++j) {
              Node& n = node[q[j]];
              assert(n.size > 2);
              for (int k = 0; k < 3; ++k) {
                Node& u = *n.edge[k];
                edge[j][k] = u.id;
                if (u.id >= NC) continue;
                toIndex[u.id] = ps;
                P[ps][0] = u.x;
                P[ps][1] = u.y;
                ++ps;
              }
            }
            for (int j = 0; j < qs; ++j) {
              for (int k = 0; k < 3; ++k) {
                edge[j][k] = toIndex[edge[j][k]];
              }
            }
            for (int t = 0; t < 8; ++t) {
              for (int j = 0; j < qs; ++j) {
                double* a = P[j];
                double* b = P[edge[j][0]];
                double* c = P[edge[j][1]];
                double* d = P[edge[j][2]];
                fermatPoint(b[0], b[1], c[0], c[1], d[0], d[1], a[0], a[1]);
              }
            }
            double value = 1e10;
            int x = -1;
            constexpr int dx[] = {0, 1, 0, 1};
            constexpr int dy[] = {0, 0, 1, 1};
            auto set = [&](int u) {
              for (int j = 0; j < qs; ++j) {
                int k = u % 4;
                u /= 4;
                Node& n = node[q[j]];
                n.x = (int)P[j][0] + dx[k];
                n.y = (int)P[j][1] + dy[k];
              }
            };
            for (int t = 0, te = pow(4, qs); t < te; ++t) {
              set(t);
              double d = prim();
              if (value > d) {
                value = d;
                x = t;
              }
            }
            set(x);
            for (int j = 0; j < qs; ++j) {
              Node& n = node[q[j]];
              pos[n.id - NC][0] = n.x;
              pos[n.id - NC][1] = n.y;
            }
          }
        }
      }
    }
    {
      constexpr int MAX = 4;
      constexpr int SIZE = 1 << 10;
      bool used[SIZE][SIZE];
      memset(used, false, sizeof(used));
      for (int i = NC, PN = NC + ps; i < PN; ++i) {
        init();
        prim();
        static int nl[32];
        int nls = 0;
        Node& n = node[i];
        assert(n.size == 3);
        auto add = [&](int a, int b) {
          used[a][b] = true;
          for (int i = 0; i < 4; ++i) {
            int x = a + dx[i];
            int y = b + dy[i];
            if (x < 0 || S <= x) continue;
            if (y < 0 || S <= y) continue;
            if (used[x][y]) continue;
            used[x][y] = true;
            nl[nls++] = (x << 16) | y;
          }
        };
        add(n.x, n.y);
        static int cl[8], pl[MAX_N];
        int cls = 0, pls = 0;
        for (int j = 0; j < N; ++j) {
          if (j == i) continue;
          Node& n = node[j];
          pl[pls++] = (n.x << 16) | n.y;
        }
        auto exp = [&]() {
          double x = junctionCost * cls;
          for (int i = 0; i < (1 << cls); ++i) {
            pls = N - 1;
            for (int j = 0; j < cls; ++j) {
              if (i & (1 << j)) pl[pls++] = cl[j];
            }
            int b = bitset<MAX>(i).count();
            double p = failureProbability;
            x += prim(pl, pls) * pow(1 - p, b) * pow(p, cls - b);
          }
          return x;
        };
        cl[cls++] = (n.x << 16) | n.y;
        double e = exp();
        for (int m = 1; m < MAX; ++m) {
          int p = -1;
          double v = 1e10;
          ++cls;
          for (int i = 0; i < nls; ++i) {
            int t = nl[i];
            cl[cls - 1] = t;
            double d = exp();
            if (v > d) {
              v = d;
              p = t;
            }
          }
          if (e > v) {
            e = v;
            cl[cls - 1] = p;
            int x = p >> 16;
            int y = p & ((1 << 16) - 1);
            for (int i = 0; i < nls; ++i) {
              if (nl[i] == p) nl[i--] = nl[--nls];
            }
            add(x, y);
            pos[ps][0] = x;
            pos[ps][1] = y;
            ++ps;
          } else {
            break;
          }
        }
      }
    }
    {
      for (int i = 0; i < ps; ++i) {
        init();
        int c = 0;
        for (int j = 0; j < N; ++j) {
          Node& n = node[j];
          if (pos[i][0] != n.x) continue;
          if (pos[i][1] != n.y) continue;
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
    for (int i = NC; i < N; ++i) {
      node[i].used = junctionStatus[i - NC] == 0;
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