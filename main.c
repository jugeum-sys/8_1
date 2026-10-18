#define _CRT_SECURE_NO_WARNINGS  
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAX_V         50       
#define SPARSE_E     100       
#define DENSE_E      600      
#define MAX_E        (MAX_V * (MAX_V - 1) / 2)   
#define MAX_WEIGHT   100       
#define REPEAT      1000       
#define DEFAULT_SEED 12345
#define INF (1 << 29)


static unsigned long rngState = DEFAULT_SEED;
static void rng_seed(unsigned long seed) { rngState = seed; }
static int rng_next(int bound) {
    rngState = rngState * 1103515245UL + 12345UL;
    return (int)((rngState >> 16) % (unsigned long)bound);
}


typedef struct { int u, v, w; } Edge;

typedef struct {
    int  n, m;
    Edge edges[MAX_E];
    char exists[MAX_V][MAX_V];     
} EdgeSet;

static void add_edge(EdgeSet* set, int u, int v, int w) {
    set->exists[u][v] = 1;
    set->exists[v][u] = 1;
    set->edges[set->m].u = u;
    set->edges[set->m].v = v;
    set->edges[set->m].w = w;
    set->m++;
}

static void generate_graph(EdgeSet* set, int n, int m) {
    int i, u, v, w;

    set->n = n;
    set->m = 0;
    for (u = 0; u < n; u++)
        for (v = 0; v < n; v++) set->exists[u][v] = 0;

    for (i = 1; i < n; i++) {
        u = rng_next(i);                      
        w = rng_next(MAX_WEIGHT) + 1;         
        add_edge(set, u, i, w);
    }

    while (set->m < m) {
        u = rng_next(n);
        v = rng_next(n);
        if (u == v) continue;                
        if (set->exists[u][v]) continue;   
        w = rng_next(MAX_WEIGHT) + 1;
        add_edge(set, u, v, w);
    }
}


typedef struct ENode {
    int            vertex;
    int            weight;
    struct ENode* next;
} ENode;

typedef struct {
    int    n;
    ENode* head[MAX_V];
} ListGraph;

static long listNodeCount = 0;

static ListGraph* list_create(const EdgeSet* set) {
    ListGraph* g = (ListGraph*)malloc(sizeof(ListGraph));
    ENode* node;
    int i, u, v, w;
    if (g == NULL) return NULL;

    g->n = set->n;
    for (i = 0; i < g->n; i++) g->head[i] = NULL;
    listNodeCount = 0;

    for (i = 0; i < set->m; i++) {
        u = set->edges[i].u; v = set->edges[i].v; w = set->edges[i].w;

        node = (ENode*)malloc(sizeof(ENode));
        node->vertex = v; node->weight = w; node->next = g->head[u];
        g->head[u] = node; listNodeCount++;

        node = (ENode*)malloc(sizeof(ENode));
        node->vertex = u; node->weight = w; node->next = g->head[v];
        g->head[v] = node; listNodeCount++;
    }
    return g;
}

static void list_destroy(ListGraph* g) {
    ENode* cur, * tmp;
    int i;
    if (g == NULL) return;
    for (i = 0; i < g->n; i++) {
        cur = g->head[i];
        while (cur != NULL) { tmp = cur->next; free(cur); cur = tmp; }
    }
    free(g);
}


typedef struct {
    int n;
    int w[MAX_V][MAX_V];       
} MatrixGraph;

static MatrixGraph* matrix_create(const EdgeSet* set) {
    MatrixGraph* g = (MatrixGraph*)malloc(sizeof(MatrixGraph));
    int i, j;
    if (g == NULL) return NULL;

    g->n = set->n;
    for (i = 0; i < g->n; i++)
        for (j = 0; j < g->n; j++) g->w[i][j] = 0;

    for (i = 0; i < set->m; i++) {
        g->w[set->edges[i].u][set->edges[i].v] = set->edges[i].w;
        g->w[set->edges[i].v][set->edges[i].u] = set->edges[i].w;
    }
    return g;
}


typedef struct {
    int parent[MAX_V];
    int rank[MAX_V];
} UnionFind;

static void uf_init(UnionFind* uf, int n) {
    int i;
    for (i = 0; i < n; i++) { uf->parent[i] = i; uf->rank[i] = 0; }
}


static int uf_find(UnionFind* uf, int x) {
    while (uf->parent[x] != x) {
        uf->parent[x] = uf->parent[uf->parent[x]];   
        x = uf->parent[x];
    }
    return x;
}

static int uf_union(UnionFind* uf, int a, int b) {
    int ra = uf_find(uf, a), rb = uf_find(uf, b);
    if (ra == rb) return 0;
    if (uf->rank[ra] < uf->rank[rb])      uf->parent[ra] = rb;
    else if (uf->rank[ra] > uf->rank[rb]) uf->parent[rb] = ra;
    else { uf->parent[rb] = ra; uf->rank[ra]++; }
    return 1;
}


static void merge_sort_edges(Edge arr[], Edge tmp[], int left, int right) {
    int mid, i, j, k;
    if (left >= right) return;
    mid = (left + right) / 2;
    merge_sort_edges(arr, tmp, left, mid);
    merge_sort_edges(arr, tmp, mid + 1, right);

    i = left; j = mid + 1; k = left;
    while (i <= mid && j <= right)
        tmp[k++] = (arr[i].w <= arr[j].w) ? arr[i++] : arr[j++];
    while (i <= mid)   tmp[k++] = arr[i++];
    while (j <= right) tmp[k++] = arr[j++];
    for (i = left; i <= right; i++) arr[i] = tmp[i];
}

typedef struct {
    Edge mst[MAX_V];       
    int  count;            
    long cost;             
} MSTResult;


static void kruskal(const ListGraph* g, MSTResult* res) {
    static Edge edges[MAX_E], tmp[MAX_E];
    UnionFind uf;
    ENode* cur;
    int u, m = 0, i;

    for (u = 0; u < g->n; u++)
        for (cur = g->head[u]; cur != NULL; cur = cur->next)
            if (u < cur->vertex) {
                edges[m].u = u; edges[m].v = cur->vertex; edges[m].w = cur->weight;
                m++;
            }

    merge_sort_edges(edges, tmp, 0, m - 1);

    uf_init(&uf, g->n);
    res->count = 0;
    res->cost = 0;
    for (i = 0; i < m && res->count < g->n - 1; i++) {
        if (uf_union(&uf, edges[i].u, edges[i].v)) {
            res->mst[res->count++] = edges[i];
            res->cost += edges[i].w;
        }
    }
}

static void prim(const MatrixGraph* g, int start, MSTResult* res) {
    int key[MAX_V], parent[MAX_V], visited[MAX_V];
    int i, v, u, min, step;

    for (i = 0; i < g->n; i++) { key[i] = INF; parent[i] = -1; visited[i] = 0; }
    key[start] = 0;

    res->count = 0;
    res->cost = 0;

    for (step = 0; step < g->n; step++) {
        u = -1; min = INF;
        for (v = 0; v < g->n; v++)
            if (!visited[v] && key[v] < min) { min = key[v]; u = v; }
        if (u == -1) break;                      

        visited[u] = 1;
        if (parent[u] != -1) {                   
            res->mst[res->count].u = parent[u];
            res->mst[res->count].v = u;
            res->mst[res->count].w = key[u];
            res->count++;
            res->cost += key[u];
        }

        for (v = 0; v < g->n; v++) {
            if (!visited[v] && g->w[u][v] > 0 && g->w[u][v] < key[v]) {
                key[v] = g->w[u][v];
                parent[v] = u;
            }
        }
    }
}

static void print_case(int caseNo, const char* title, int n, int m,
    const MSTResult* res, long memory, double usec) {
    int i;
    printf("\nCase %d : %s\n", caseNo, title);
    printf("  Vertices      : %d\n", n);
    printf("  Edges         : %d\n", m);
    printf("  MST Edges     : %d\n", res->count);
    printf("  MST Cost      : %ld\n", res->cost);
    printf("  Memory        : %ld Bytes\n", memory);
    printf("  Execution Time: %.2f us (%d회 평균)\n", usec, REPEAT);
    printf("  MST 간선 :\n   ");
    for (i = 0; i < res->count; i++) {
        printf(" %d-%d(%d)", res->mst[i].u, res->mst[i].v, res->mst[i].w);
        if ((i + 1) % 7 == 0) printf("\n   ");
    }
    printf("\n");
}


static unsigned long ask_seed(void) {
    char line[64];
    unsigned long value = 0;
    int i = 0, digits = 0;

    printf("난수 시드를 입력하세요 (그냥 Enter를 누르면 %d): ", DEFAULT_SEED);
    if (fgets(line, sizeof(line), stdin) == NULL) return DEFAULT_SEED;
    while (line[i] == ' ' || line[i] == '\t') i++;
    while (line[i] >= '0' && line[i] <= '9') {
        value = value * 10 + (unsigned long)(line[i] - '0');
        digits++; i++;
    }
    return (digits > 0) ? value : DEFAULT_SEED;
}


static long run_kruskal_case(const EdgeSet* set, int caseNo, const char* title) {
    ListGraph* g = list_create(set);
    MSTResult  res;
    clock_t    start, end;
    double     usec;
    long       memory;
    int        r;

    memory = (long)sizeof(ListGraph)
        + listNodeCount * (long)sizeof(ENode)
        + (long)set->m * (long)sizeof(Edge) * 2   
        + (long)sizeof(UnionFind);

    start = clock();
    for (r = 0; r < REPEAT; r++) kruskal(g, &res);   
    end = clock();
    usec = (double)(end - start) * 1000000.0 / CLOCKS_PER_SEC / REPEAT;

    print_case(caseNo, title, set->n, set->m, &res, memory, usec);
    list_destroy(g);
    return res.cost;
}

static long run_prim_case(const EdgeSet* set, int caseNo, const char* title) {
    MatrixGraph* g = matrix_create(set);
    MSTResult    res;
    clock_t      start, end;
    double       usec;
    long         memory;
    int          r;

    memory = (long)sizeof(MatrixGraph) + 3L * MAX_V * (long)sizeof(int);

    start = clock();
    for (r = 0; r < REPEAT; r++) prim(g, 0, &res);
    end = clock();
    usec = (double)(end - start) * 1000000.0 / CLOCKS_PER_SEC / REPEAT;

    print_case(caseNo, title, set->n, set->m, &res, memory, usec);
    free(g);
    return res.cost;
}


int main(void) {
    static EdgeSet sparse, dense;
    long c1, c2, c3, c4;

    rng_seed(ask_seed());

    generate_graph(&sparse, MAX_V, SPARSE_E);
    generate_graph(&dense, MAX_V, DENSE_E);

    printf("\n===== 최소 비용 신장 트리 알고리즘 비교 =====\n");
    printf("구조체 크기 : 인접 행렬 %zu B, 리스트 머리 %zu B, 간선 노드 %zu B, 간선 %zu B\n",
        sizeof(MatrixGraph), sizeof(ListGraph), sizeof(ENode), sizeof(Edge));

    c1 = run_kruskal_case(&sparse, 1, "Sparse Graph - Adjacency List - Kruskal");
    c2 = run_kruskal_case(&dense, 2, "Dense Graph - Adjacency List - Kruskal");
    c3 = run_prim_case(&sparse, 3, "Sparse Graph - Adjacency Matrix - Prim");
    c4 = run_prim_case(&dense, 4, "Dense Graph - Adjacency Matrix - Prim");

    printf("\n===== 검증 =====\n");
    printf("희소 그래프 : Kruskal %ld, Prim %ld -> %s\n", c1, c3, (c1 == c3) ? "일치" : "불일치");
    printf("밀집 그래프 : Kruskal %ld, Prim %ld -> %s\n", c2, c4, (c2 == c4) ? "일치" : "불일치");
    return 0;
}