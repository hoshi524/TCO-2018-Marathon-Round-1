#include <bits/stdc++.h>
using namespace std;

double dist(double x1, double y1, double x2, double y2) {
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

constexpr double TIME_LIMIT = 2;
constexpr int MAX_N = 1 << 8;

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
        for (int t = 0; t < 8; ++t) {
          init();
          prim();
          for (int i = NC; i < NC + ps; ++i) {
            Node& n = node[i];
            assert(n.size > 2);
            fermatPoint(*n.edge[0], *n.edge[1], *n.edge[2], n);
            pos[i - NC][0] = n.x;
            pos[i - NC][1] = n.y;
          }
        }
      }
    }
    if (false) {
      init();
      int minx = 0xffff, maxx = 0;
      int miny = 0xffff, maxy = 0;
      for (int i = 0; i < NC; ++i) {
        Node& n = node[i];
        if (minx > n.x) minx = n.x;
        if (maxx < n.x) maxx = n.x;
        if (miny > n.y) miny = n.y;
        if (maxy < n.y) maxy = n.y;
      }
      double x = prim();
      Node& n = node[N++];
      for (n.x = minx; n.x <= maxx; ++n.x) {
        for (n.y = miny; n.y <= maxy; ++n.y) {
          double t = prim();
          if ((x - t - 1e-3) * (1 - failureProbability) > junctionCost) {
            cerr << x << " " << t << endl;
            assert(false);
          }
        }
      }
    }
    if (false) {
      init();
      double t = prim();
      for (int i = NC; i < N; ++i) {
        Node& n = node[i];
        constexpr int dx[] = {0, 1, 0, -1, 1, 1, -1, -1};
        constexpr int dy[] = {1, 0, -1, 0, 1, -1, 1, -1};
        int x = n.x;
        int y = n.y;
        for (int j = 0; j < 8; ++j) {
          n.x = x + dx[j];
          n.y = y + dy[j];
          double u = prim();
          if (t > u) {
            cerr << t << " " << u << " " << x << " " << y << " " << n.x << " "
                 << n.y << endl;
            assert(false);
          }
        }
        n.x = x;
        n.y = y;
      }
    }
    {
      init();
      prim();
      constexpr int MAX = 6;
      double prob[MAX + 1][MAX + 1];
      {
        memset(prob, 0, sizeof(prob));
        prob[0][0] = 1;
        for (int i = 0; i < MAX; ++i) {
          for (int j = 0; j < MAX; ++j) {
            prob[i + 1][j] += prob[i][j] * failureProbability;
            prob[i + 1][j + 1] += prob[i][j] * (1 - failureProbability);
          }
        }
        int comb[MAX + 1][MAX + 1];
        for (int i = 0; i <= MAX; ++i) {
          comb[i][0] = 1;
          if (i == 0) continue;
          for (int j = 1; j <= i; ++j) {
            comb[i][j] = comb[i - 1][j - 1] + comb[i - 1][j];
            prob[i][j] /= comb[i][j];
          }
        }
      }
      constexpr int SIZE = 1 << 10;
      constexpr int dx[] = {0, 1, 0, -1};
      constexpr int dy[] = {1, 0, -1, 0};
      bool used[SIZE][SIZE];
      memset(used, false, sizeof(used));
      int PN = N;
      for (int i = NC; i < PN; ++i) {
        vector<int> nl;
        Node& n = node[i];
        assert(n.size == 3);
        auto add = [&](int a, int b) {
          for (int i = 0; i < 4; ++i) {
            int x = a + dx[i];
            int y = b + dy[i];
            if (x < 0 || SIZE <= x) continue;
            if (y < 0 || SIZE <= y) continue;
            if (used[x][y]) continue;
            used[x][y] = true;
            nl.push_back((x << 16) | y);
          }
        };
        double d0;
        {
          double a = dist(*n.edge[0], *n.edge[1]);
          double b = dist(*n.edge[1], *n.edge[2]);
          double c = dist(*n.edge[2], *n.edge[0]);
          d0 = a + b + c - max({a, b, c});
        }
        add(n.x, n.y);
        auto exp = [&](vector<int>& v) {
          int s = v.size();
          double x = junctionCost * v.size();
          for (int i = 0; i < (1 << s); ++i) {
            int b = bitset<MAX>(i).count();
            static double D[3];
            for (int j = 0; j < 3; ++j) D[j] = 1e10;
            for (int j = 0; j < s; ++j) {
              if ((i & (1 << j)) == 0) continue;
              int x = v[j] >> 16;
              int y = v[j] & ((1 << 16) - 1);
              for (int k = 0; k < 3; ++k) {
                double d = dist(x, y, n.edge[k]->x, n.edge[k]->y);
                if (D[k] > d) {
                  D[k] = d;
                }
              }
            }
            double d = i == 0 ? d0 : (b - 1) + D[0] + D[1] + D[2];
            x += d * prob[s][b];
          }
          return x;
        };
        vector<int> cl{(n.x << 16) | n.y};
        double e = exp(cl);
        for (int m = 1; m < MAX; ++m) {
          int p = -1;
          double v = 1e10;
          for (int t : nl) {
            int x = t >> 16;
            int y = t & ((1 << 16) - 1);
            double d = 0;
            for (int i = 0; i < n.size; ++i) {
              d += dist(x, y, n.edge[i]->x, n.edge[i]->y);
            }
            if (v > d) {
              v = d;
              p = t;
            }
          }
          if (p == -1) break;
          cl.push_back(p);
          double ne = exp(cl);
          if (e > ne) {
            e = ne;
            int x = p >> 16;
            int y = p & ((1 << 16) - 1);
            nl.erase(remove(nl.begin(), nl.end(), p), nl.end());
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