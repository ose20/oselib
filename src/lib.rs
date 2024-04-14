use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    ops::{Add, Sub},
};

struct CumulativeSum<T>
where
    T: Add<Output = T> + Sub<Output = T> + Copy,
{
    size: usize,
    cum_sum: Vec<T>,
}

impl<T> CumulativeSum<T>
where
    T: Add<Output = T> + Sub<Output = T> + Copy,
{
    fn new(v: &Vec<T>) -> CumulativeSum<T> {
        let size = v.len();
        let mut cum_sum = v.clone();
        for i in 1..size {
            cum_sum[i] = cum_sum[i] + cum_sum[i - 1];
        }

        CumulativeSum { size, cum_sum }
    }

    // [l, r]の区間和を求める
    fn get_interval_sum(&self, left: usize, right: usize) -> Result<T, String> {
        if left > right {
            Err(String::from("区間が不正です: left > right"))
        } else if right >= self.size {
            Err(String::from("区間が不正です: right >= size"))
        } else if left == 0 {
            Ok(self.cum_sum[right])
        } else {
            Ok(self.cum_sum[right] - self.cum_sum[left - 1])
        }
    }
}

// Todo: 専用のエラー型を定義するのもよさそう
// 専用のエラー型を定義
//#[derive(Debug)]
//enum CumulativeSumError {
//    InvalidInterval { left: usize, right: usize },
//    IntervalTooLarge { right: usize, size: usize },
//} こんな感じで。ヴァリアントの名前はもっと適当なのがある

// ------------------------------
// ------------------------------
// ------------------------------
// ------------------------------
// 組み合わせ数
struct Comb {
    modulo: i64,
    // fac[i] := i! mod modulo
    fac: Vec<i64>,
    // inv[i] := i^(-1) mod modulo
    inv: Vec<i64>,
    // fac_inv[i] := (i!)^(-1) mod modulo
    fac_inv: Vec<i64>,
}

impl Comb {
    fn init(n: i64, modulo: i64) -> Comb {
        // O(n)の前処理
        // nCk (k<=n)が求められるようになる
        let size: usize = n as usize;
        let mut fac = vec![0; size + 1];
        let mut inv = vec![0; size + 1];
        let mut fac_inv = vec![0; size + 1];

        // 配列初期化(0! = 1であることに注意)
        fac[0] = 1;
        fac[1] = 1;
        fac_inv[0] = 1;
        fac_inv[1] = 1;
        inv[1] = 1;

        for i in 2..=size {
            fac[i] = (fac[i - 1] * (i as i64)) % modulo;
            // modulo と i (2 <= i <= n) は互いに素である必要がある (moduloが素数であれば十分)
            inv[i] = modulo - inv[(modulo as usize) % i] * (modulo / (i as i64)) % modulo;
            fac_inv[i] = fac_inv[i - 1] * inv[i] % modulo
        }

        Comb {
            modulo,
            fac,
            inv,
            fac_inv,
        }
    }

    fn com(&self, n: i64, k: i64) -> i64 {
        let nsize = n as usize;
        let ksize = k as usize;
        if n < k {
            0
        } else if n < 0 || k < 0 {
            0
        } else {
            self.fac[nsize] * (self.fac_inv[ksize] * self.fac_inv[nsize - ksize] % self.modulo)
                % self.modulo
        }
    }
}

// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// String Hash
// Stringのハッシュ値を高速に求めるためのデータ構造
// Stringは大文字と小文字のアルファベットのみに対応している
struct StringHash {
    modulo: u64,
    // Stringの文字数
    len: usize,
    // Stringのi番目のu64表現
    t: Vec<u64>,
    // h[i] := String[1,i] のハッシュ値 (1-indexd）
    // つまり、h[i] := 100^(i-1) * t[1] + ... + 100^1 * t[i-1] + 100^0 * t[i]
    h: Vec<u64>,
    // pow100[i] := 100^i mod modulo (計算用のメモ)
    pow100: Vec<u64>,
}

impl StringHash {
    fn alpha_to_u64(c: char) -> Option<u64> {
        match c {
            'A'..='Z' => Some(c as u64 - 'A' as u64),
            'a'..='z' => Some(c as u64 - 'a' as u64),
            _ => None,
        }
    }
    fn init(string: &String) -> StringHash {
        let modulo: u64 = 21_4748_3647;
        let len = string.len();

        // t[] の設定
        let mut t = vec![0; len + 1];
        let mut t = vec![0; len + 1];
        for (i, c) in string.chars().enumerate() {
            t[i + 1] = StringHash::alpha_to_u64(c).expect("文字列にはアルファベットのみが含まれる");
        }

        // pow100[] の設定
        let mut pow100 = vec![1; len + 1];
        for i in 1..=len {
            pow100[i] = pow100[i - 1] * 100 % modulo
        }

        // h[] の設定
        let mut h = vec![0; len + 1];
        for i in 1..=len {
            h[i] = (100 * h[i - 1] + t[i]) % modulo
        }

        StringHash {
            modulo,
            len,
            t,
            h,
            pow100,
        }
    }

    // String[l..=r]のハッシュ値
    fn hash(&self, l: usize, r: usize) -> u64 {
        assert!(l <= r);
        assert!(1 <= l && r <= self.len);
        // h[r] - 100^(r-l+1) * h[l-1]
        (self.h[r] + self.modulo - (self.h[l - 1] * self.pow100[r - l + 1] % self.modulo))
            % self.modulo
    }
}

// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// セグメントツリー

// モノイド(S, op)を表現するトレイト
trait Monoid {
    // 単位元を返すメソッド
    // 単位元 e ∈ S は、任意の x ∈ S に対して、 e op x = x かつ x op e = x を満たす
    fn id() -> Self;

    // S上の二項演算を行うメソッド
    fn op(&self, other: &Self) -> Self;
}

// Segment Tree
// ref. https://tsutaj.hatenablog.com/entry/2017/03/29/204841
// ref. https://hcpc-hokudai.github.io/archive/structure_segtree_001.pdf
struct SegmentTree<T: Monoid> {
    // 内部的にもつ配列は2分木を模していて、その最下段の要素数
    // 対象となる配列の要素数以上となる最小の２べきの数にする
    n: usize,
    // 内部的にもつ配列
    // 1-indexedで持つ
    node: Vec<T>,
}

impl<T> SegmentTree<T>
where
    T: Monoid + Clone + Copy,
{
    // 初期化
    // v は 0-indexed
    fn init(v: &Vec<T>) -> SegmentTree<T> {
        let len = v.len();
        let n = len.next_power_of_two();

        // node を作成する
        // 最下段のノード数が n(=2^k) の二分木を模した配列なので、要素数は 1 + 2 + ... + 2^k = 2^(k+1) - 1 + 1 (= 2^(k+1))
        // 1-indexed なので要素数が +1 されている
        let mut node = vec![Monoid::id(); 2 * n];
        // 最下段以外の nodeの数は 2^(k+1) - 1 - 2^k = 2^k - 1 なので、
        // 1-indexedな node[] の添え字は 1 ~ 2^k - 1 を使う
        // したがって、 v[i] に対応する node[] の位置は 2^k(=n) + i (v[] は 0-indexed)
        for i in 0..len {
            node[n + i] = v[i].clone();
        }
        for i in (1..=n - 1).rev() {
            node[i] = node[2 * i].op(&node[2 * i + 1]);
        }

        SegmentTree { n, node }
    }

    //　元の配列 vにおける v[i] を T に変更する
    fn update(&mut self, i: usize, val: T) {
        // v[i] に対応するのは　node[n + i]
        let mut cur = self.n + i;
        self.node[cur] = val;

        // 最下段のノードを上に伝播させる
        loop {
            // 親 nodeの添え字を得る
            cur = cur / 2;
            if cur < 1 {
                break;
            }

            self.node[cur] = self.node[2 * cur].op(&self.node[2 * cur + 1]);
        }
    }

    // 元の配列　vと vの添え字での半開区間 [l, r) に対して op(v[l], v[l+1], ..., v[r-1]) を求める
    // op は二項演算子であるが、結合法則を満たすので、自然に拡張される n項演算子として定義されるものを用いている
    fn fold(&self, l: usize, r: usize) -> T {
        // 非再帰で fold するので、直観としては両端の添え字（l, r）を下から　nodeを見て被覆していく
        // 半開区間なので lは自身を含み、rは自身を含まないことに注意
        // - l側の時
        //      自分が親から見て左側の子供(添え字が偶数)である場合は親 node の方で集計して貰えばよく
        //      自分が親から見て右側の子供（添え字が奇数）である場合は親 node の方で集計すると兄弟まで集計対象に入って困るので今集計しないといけないのが注意点
        // - r側の時
        //      そもそもの注意点として、これが表現しているのは「添え字rが指す区間はギリギリ被覆対象に含まれない」、つまり、
        //      自分の左の nodeからちょうど被覆対象になっていることだという意識を持つとわかりやすい
        //      自分が親から見て左側の子供である場合は、自身は被覆対象ではないので /2 して親ノードに移る（この操作の前後で、　rの持つ「添え字rが指す区間はギリギリ被覆対象に含まれない」という意味は保存されている）
        //      自分が親かr見て右側の子供である場合は、自身の兄弟が集計対象なので node[r-1] を集計してから親に移る（ただ親に移るだけだと node[r-1]が集計から漏れてしまう。また rの持つ意味も変わらない）

        // Monoidの二項演算が交換法則を満たさない場合にも対応している
        let mut from_left: T = Monoid::id();
        let mut from_right: T = Monoid::id();

        let mut l = l + self.n;
        let mut r = r + self.n;

        while l < r {
            if l & 1 != 0 {
                from_left = from_left.op(&self.node[l]);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                from_right = self.node[r].op(&from_right);
            }
            l = l >> 1;
            r = r >> 1;
        }

        from_left.op(&from_right)
    }
}

// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// ダイクストラ法
// adj: 隣接リスト(0-indexed)
// 到達不可能な場合は　usize::max_value()が入ってる
fn dijkstra(start: usize, adj: &Vec<Vec<(usize, usize)>>) -> Vec<usize> {
    let inf = usize::max_value();
    let mut dist = vec![inf; adj.len()];
    dist[start] = 0;
    let mut que = BinaryHeap::new();
    que.push((Reverse(0), start));

    while !que.is_empty() {
        let (Reverse(d), now) = que.pop().unwrap();
        if d > dist[now] {
            continue;
        }

        dist[now] = d;
        for &(next, next_d) in adj[now].iter() {
            if dist[next] > dist[now] + next_d {
                dist[next] = dist[now] + next_d;
                que.push((Reverse(dist[now] + next_d), next))
            }
        }
    }

    dist
}

// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// UnifonFind
struct UnionFind {
    // 親の頂点番号
    par: Vec<Option<usize>>,
    // 要素が属する根つき木の高さ
    // 経路圧縮しているので実態は違うけど、経路圧縮しなかった場合の値を持っておく
    rank: Vec<usize>,
    // 要素と同じ集合に含まれる頂点の数
    size: Vec<usize>,
}

impl UnionFind {
    fn init(n: usize) -> Self {
        Self {
            par: vec![None; n],
            rank: vec![0; n],
            size: vec![1; n],
        }
    }

    fn root(&mut self, x: usize) -> usize {
        if self.par[x].is_none() {
            x
        } else {
            self.par[x] = Some(self.root(self.par[x].unwrap()));
            self.par[x].unwrap()
        }
    }

    fn is_same(&mut self, x: usize, y: usize) -> bool {
        self.root(x) == self.root(y)
    }

    fn unite(&mut self, x: usize, y: usize) {
        let (rx, ry) = {
            let rx = self.root(x);
            let ry = self.root(y);
            if self.rank[rx] < self.rank[ry] {
                (ry, rx)
            } else {
                (rx, ry)
            }
        };

        if rx == ry {
            return;
        }

        self.par[ry] = Some(rx);
        if self.rank[rx] == self.rank[ry] {
            self.rank[rx] += 1;
        }

        self.size[rx] += self.size[ry]
    }

    fn size(&mut self, x: usize) -> usize {
        let rt = self.root(x);
        self.size[rt]
    }
}

// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// ------------------------------------------------------------
// 最大流 Ford Fulkerson

pub mod max_flow {

    #[derive(Clone)]
    struct Edge {
        // 重みが capa である有向辺 from-to を表現する(隣接リストで管理する前提なので from は持たない)
        // rev: この辺の逆辺を参照するときの index
        to: usize,
        capa: usize,
        rev: usize,
    }

    impl Edge {
        fn new(to: usize, capa: usize, rev: usize) -> Edge {
            Edge { to, capa, rev }
        }
    }

    pub struct FordFulkerson {
        n: usize,
        graph: Vec<Vec<Edge>>,
    }

    impl FordFulkerson {
        // (from, to, capacity) のリストをもらって初期化する
        // 頂点番号は 0 ~ n-1 を想定している (0-indexed)
        pub fn new(n: usize) -> Self {
            FordFulkerson {
                n,
                graph: vec![vec![]; n],
            }
        }

        pub fn add_edge(&mut self, from: usize, to: usize, capa: usize) {
            // from-toの逆辺が追加されるインデックス
            let rev_for_from = self.graph[to].len();
            // from-toが追加されるインデックス
            let rev_for_to = self.graph[from].len();
            self.graph[from].push(Edge::new(to, capa, rev_for_from));
            self.graph[to].push(Edge::new(from, 0, rev_for_to));
        }

        pub fn max_flow(&mut self, s: usize, t: usize) -> usize {
            let mut flow = 0;
            loop {
                let mut visited = vec![false; self.n];
                let f = Self::dfs(&mut self.graph, s, t, usize::MAX, &mut visited);
                if f == 0 {
                    return flow;
                }
                flow += f;
            }
        }

        fn dfs(
            graph: &mut Vec<Vec<Edge>>,
            v: usize,
            t: usize,
            flow: usize,
            visited: &mut Vec<bool>,
        ) -> usize {
            if v == t {
                return flow;
            }
            visited[v] = true;
            for i in 0..graph[v].len() {
                let edge = graph[v][i].clone();
                if !visited[edge.to] && edge.capa > 0 {
                    let d = Self::dfs(graph, edge.to, t, flow.min(edge.capa), visited);
                    if d > 0 {
                        //edge.capa -= d;
                        graph[v][i].capa -= d;
                        graph[edge.to][edge.rev].capa += d;
                        return d;
                    }
                }
            }

            0
            //　ここで visited[v] = false をしなくていい理由（計算量が増える(だけ？)ので、しなくていいならしないほうがいい）
            // 次の命題を示せば十分である
            // s: スタート地点、 t: ゴール地点、 V: 頂点集合
            // 命題: 任意のパス s-x に対して
            //          パス s-x-t がこのアルゴリズムにおいて存在しない（同じ頂点を二度通れない） & パス s-t が存在するならば
            //      x を含まないパス　s-t が存在する
            // 証明:
            //  パス s-x を任意に取り（パス1と名付ける）、パス s-x-t が存在せず、パス s-t が存在することを仮定する
            //  この時、パス s-x の中継地点になってる頂点集合 U が取れる
            //  パス s-t が存在するとして、そのうち x が含まれるものは、x が含まれないパスに再構成できることを示す
            //  x が含まれるとして、経路 x-t の x と t の間にある頂点 y に注目する
            //  - x-t の間の頂点に少なくとも　1　つ U の頂点がある場合
            //      t 側から見ていって初めて　U の要素となる頂点を u とする（パス u-tが作れ、その中継点には U の要素も x も含まれない）。
            //      u はその定義よりパス1である s-x の中継点なので、s-u-t が作れる（これは x を含まない）
            //  - x-t の間に U の頂点が 1 つもない場合
            //      このパスとパス 1 を繋げることで、s-x-t が作れてしまって仮定に矛盾するのでこのケースは起きえない
        }
    }
}
