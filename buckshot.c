#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <math.h>
#include <ctype.h>
#include <pthread.h>
#include <stdatomic.h>

#ifdef _WIN32
#include <windows.h>
static double now_ms(void){ return (double)GetTickCount64(); }
static int    ncpu(void)  { SYSTEM_INFO s; GetSystemInfo(&s); return s.dwNumberOfProcessors; }
#else
#include <unistd.h>
#include <sys/time.h>
static double now_ms(void){ struct timeval t; gettimeofday(&t,NULL); return t.tv_sec*1e3+t.tv_usec*1e-3; }
static int    ncpu(void)  { int n=sysconf(_SC_NPROCESSORS_ONLN); return n>0?n:1; }
#endif

typedef uint64_t U64;
#define BB(s)        ((U64)1<<(s))
#define LSB(b)       __builtin_ctzll(b)
#define POP(b)       __builtin_popcountll(b)
#define POPLSB(b)    ((b)&=((b)-1))                             

#define W 0
#define B 1
#define P_ 0
#define N_ 1
#define B_ 2
#define R_ 3
#define Q_ 4
#define K_ 5
#define NONE 6

enum { A8,B8,C8,D8,E8,F8,G8,H8,
       A7,B7,C7,D7,E7,F7,G7,H7,
       A6,B6,C6,D6,E6,F6,G6,H6,
       A5,B5,C5,D5,E5,F5,G5,H5,
       A4,B4,C4,D4,E4,F4,G4,H4,
       A3,B3,C3,D3,E3,F3,G3,H3,
       A2,B2,C2,D2,E2,F2,G2,H2,
       A1,B1,C1,D1,E1,F1,G1,H1 };

static const char *SQ_NAME[64]={
 "a8","b8","c8","d8","e8","f8","g8","h8",
 "a7","b7","c7","d7","e7","f7","g7","h7",
 "a6","b6","c6","d6","e6","f6","g6","h6",
 "a5","b5","c5","d5","e5","f5","g5","h5",
 "a4","b4","c4","d4","e4","f4","g4","h4",
 "a3","b3","c3","d3","e3","f3","g3","h3",
 "a2","b2","c2","d2","e2","f2","g2","h2",
 "a1","b1","c1","d1","e1","f1","g1","h1"
};
#define RANK(s) ((s)>>3)
#define FILE(s) ((s)&7)
#define SQ(r,f) ((r)*8+(f))

#define CR_WK 1
#define CR_WQ 2
#define CR_BK 4
#define CR_BQ 8
static uint8_t castle_mask_t[64];

static U64 PAWN_ATTACKS[2][64];                   
static U64 KNIGHT_ATTACKS[64];
static U64 KING_ATTACKS[64];
static U64 RANK_MASK[64], FILE_MASK[64];
static U64 DIAG_MASK[64], ADIAG_MASK[64];                              

#define R_BITS 12
#define B_BITS 9

typedef struct { U64 mask,magic; int shift; U64 *tbl; } Magic;
static Magic ROOK_MAGIC[64];
static Magic BISH_MAGIC[64];
static U64 ROOK_TABLE[64][4096];
static U64 BISH_TABLE[64][512];

static U64 FILE_BB[8];                     
static U64 ADJ_FILES[8];                             
static U64 PASSED_MASK[2][64];                                                     
static U64 KING_ZONE[2][64];                                

static U64 BETWEEN[64][64];                                                        

static void init_tables(void) {
    for(int s=0;s<64;s++){
        int r=RANK(s),f=FILE(s);
        RANK_MASK[s]=0; for(int ff=0;ff<8;ff++) if(ff!=f) RANK_MASK[s]|=BB(SQ(r,ff));
        FILE_MASK[s]=0; for(int rr=0;rr<8;rr++) if(rr!=r) FILE_MASK[s]|=BB(SQ(rr,f));
        DIAG_MASK[s]=0;
        for(int d=1;r+d<8&&f+d<8;d++) DIAG_MASK[s]|=BB(SQ(r+d,f+d));
        for(int d=1;r-d>=0&&f-d>=0;d++) DIAG_MASK[s]|=BB(SQ(r-d,f-d));
        ADIAG_MASK[s]=0;
        for(int d=1;r+d<8&&f-d>=0;d++) ADIAG_MASK[s]|=BB(SQ(r+d,f-d));
        for(int d=1;r-d>=0&&f+d<8;d++) ADIAG_MASK[s]|=BB(SQ(r-d,f+d));
    }
    for(int s=0;s<64;s++){
        int r=RANK(s),f=FILE(s);
        PAWN_ATTACKS[W][s]=0;
        if(r>0&&f>0) PAWN_ATTACKS[W][s]|=BB(SQ(r-1,f-1));
        if(r>0&&f<7) PAWN_ATTACKS[W][s]|=BB(SQ(r-1,f+1));
        PAWN_ATTACKS[B][s]=0;
        if(r<7&&f>0) PAWN_ATTACKS[B][s]|=BB(SQ(r+1,f-1));
        if(r<7&&f<7) PAWN_ATTACKS[B][s]|=BB(SQ(r+1,f+1));
    }
    for(int s=0;s<64;s++){
        int r=RANK(s),f=FILE(s); U64 a=0;
        int kd[8][2]={{2,1},{1,2},{-1,2},{-2,1},{-2,-1},{-1,-2},{1,-2},{2,-1}};
        for(int i=0;i<8;i++){int nr=r+kd[i][0],nf=f+kd[i][1]; if(nr>=0&&nr<8&&nf>=0&&nf<8) a|=BB(SQ(nr,nf));}
        KNIGHT_ATTACKS[s]=a;
    }
    for(int s=0;s<64;s++){
        int r=RANK(s),f=FILE(s); U64 a=0;
        for(int dr=-1;dr<=1;dr++) for(int df=-1;df<=1;df++){
            if(!dr&&!df) continue;
            int nr=r+dr,nf=f+df; if(nr>=0&&nr<8&&nf>=0&&nf<8) a|=BB(SQ(nr,nf));
        }
        KING_ATTACKS[s]=a;
    }
    for(int f=0;f<8;f++){
        FILE_BB[f]=0; for(int r=0;r<8;r++) FILE_BB[f]|=BB(SQ(r,f));
        ADJ_FILES[f]=0;
        if(f>0) ADJ_FILES[f]|=FILE_BB[f-1];
        if(f<7) ADJ_FILES[f]|=FILE_BB[f+1];
    }
    for(int s=0;s<64;s++){
        int r=RANK(s),f=FILE(s);
        PASSED_MASK[W][s]=0;
        for(int rr=0;rr<r;rr++) for(int ff=f-1;ff<=f+1;ff++) if(ff>=0&&ff<8) PASSED_MASK[W][s]|=BB(SQ(rr,ff));
        PASSED_MASK[B][s]=0;
        for(int rr=r+1;rr<8;rr++) for(int ff=f-1;ff<=f+1;ff++) if(ff>=0&&ff<8) PASSED_MASK[B][s]|=BB(SQ(rr,ff));
    }
    for(int s=0;s<64;s++){
        int r=RANK(s),f=FILE(s);
        KING_ZONE[W][s]=0;
        for(int dr=-1;dr<=2;dr++) for(int df=-2;df<=2;df++){
            int nr=r+dr,nf=f+df; if(nr>=0&&nr<8&&nf>=0&&nf<8) KING_ZONE[W][s]|=BB(SQ(nr,nf));
        }
        KING_ZONE[B][s]=0;
        for(int dr=-2;dr<=1;dr++) for(int df=-2;df<=2;df++){
            int nr=r+dr,nf=f+df; if(nr>=0&&nr<8&&nf>=0&&nf<8) KING_ZONE[B][s]|=BB(SQ(nr,nf));
        }
    }
    for(int a=0;a<64;a++) for(int b=0;b<64;b++){
        BETWEEN[a][b]=0;
        int ra=RANK(a),fa=FILE(a),rb=RANK(b),fb=FILE(b);
        if(ra==rb){ int mn=fa<fb?fa:fb, mx=fa>fb?fa:fb; for(int f=mn+1;f<mx;f++) BETWEEN[a][b]|=BB(SQ(ra,f)); }
        else if(fa==fb){ int mn=ra<rb?ra:rb, mx=ra>rb?ra:rb; for(int r=mn+1;r<mx;r++) BETWEEN[a][b]|=BB(SQ(r,fa)); }
        else if(abs(ra-rb)==abs(fa-fb)){
            int dr=(rb>ra)?1:-1, df=(fb>fa)?1:-1;
            int r=ra+dr,f=fa+df;
            while(r!=rb||f!=fb){ BETWEEN[a][b]|=BB(SQ(r,f)); r+=dr; f+=df; }
        }
    }
    memset(castle_mask_t,0xFF,64);
    castle_mask_t[E8]=(uint8_t)~(CR_BK|CR_BQ); castle_mask_t[A8]=(uint8_t)~CR_BQ; castle_mask_t[H8]=(uint8_t)~CR_BK;
    castle_mask_t[E1]=(uint8_t)~(CR_WK|CR_WQ); castle_mask_t[A1]=(uint8_t)~CR_WQ; castle_mask_t[H1]=(uint8_t)~CR_WK;
}

static U64 sliding_attacks(int sq, U64 occ, const int dirs[][2], int ndirs) {
    U64 attacks=0;
    int r=RANK(sq),f=FILE(sq);
    for(int d=0;d<ndirs;d++){
        int nr=r+dirs[d][0],nf=f+dirs[d][1];
        while(nr>=0&&nr<8&&nf>=0&&nf<8){
            U64 bit=BB(SQ(nr,nf)); attacks|=bit;
            if(occ&bit) break;
            nr+=dirs[d][0]; nf+=dirs[d][1];
        }
    }
    return attacks;
}

static uint64_t g_rng_state=0x9E3779B97F4A7C15ULL;
static inline uint64_t rng_next(void){
    uint64_t x=g_rng_state;
    x^=x<<13; x^=x>>7; x^=x<<17;
    g_rng_state=x; return x;
}
static inline U64 rng_sparse(void){ return rng_next()&rng_next()&rng_next(); }

static U64 occ_subset(int idx, int n, U64 mask){
    U64 result=0, m=mask;
    for(int i=0;i<n;i++){
        U64 lsb=m&(-(int64_t)m);                             
        m^=lsb;
        if(idx&(1<<i)) result|=lsb;
    }
    return result;
}

static U64 find_magic(int sq, U64 mask, bool bishop){
    int n=POP(mask);
    int size=1<<n;
    static U64 occs[4096], atks[4096];
    static U64 used[4096]; static bool filled[4096];
    static const int RDIRS[4][2]={{0,1},{0,-1},{1,0},{-1,0}};
    static const int BDIRS[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};

    for(int i=0;i<size;i++){
        occs[i]=occ_subset(i,n,mask);
        atks[i]=bishop?sliding_attacks(sq,occs[i],BDIRS,4):sliding_attacks(sq,occs[i],RDIRS,4);
    }
    for(int try_=0; try_<100000000; try_++){
        U64 magic=rng_sparse();
        if(POP((mask*magic)&0xFF00000000000000ULL)<6) continue;
        memset(filled,0,sizeof(bool)*size);
        bool fail=false;
        for(int i=0;i<size&&!fail;i++){
            int idx=(int)((occs[i]*magic)>>(64-n));
            if(!filled[idx]){ filled[idx]=true; used[idx]=atks[i]; }
            else if(used[idx]!=atks[i]) fail=true;
        }
        if(!fail) return magic;
    }
    return 0;                          
}

static void init_magics(void) {
    static const int RDIRS[4][2]={{0,1},{0,-1},{1,0},{-1,0}};
    static const int BDIRS[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    for(int s=0;s<64;s++){
        {           
            int r=RANK(s),f=FILE(s);
            U64 mask=0;
            for(int rr=r+1;rr<7;rr++) mask|=BB(SQ(rr,f));
            for(int rr=r-1;rr>0;rr--) mask|=BB(SQ(rr,f));
            for(int ff=f+1;ff<7;ff++) mask|=BB(SQ(r,ff));
            for(int ff=f-1;ff>0;ff--) mask|=BB(SQ(r,ff));
            int bits=POP(mask);
            U64 magic=find_magic(s,mask,false);
            ROOK_MAGIC[s].mask=mask; ROOK_MAGIC[s].magic=magic;
            ROOK_MAGIC[s].shift=64-bits; ROOK_MAGIC[s].tbl=ROOK_TABLE[s];
            int size=1<<bits;
            for(int i=0;i<size;i++){
                U64 sub=occ_subset(i,bits,mask);
                U64 att=sliding_attacks(s,sub,RDIRS,4);
                int idx=(int)((sub*magic)>>(64-bits));
                ROOK_TABLE[s][idx]=att;
            }
        }
        {             
            U64 edges=((U64)0xFF|(U64)0xFF00000000000000ULL|0x0101010101010101ULL|0x8080808080808080ULL);
            U64 mask=(DIAG_MASK[s]|ADIAG_MASK[s])&~edges;
            int bits=POP(mask);
            U64 magic=find_magic(s,mask,true);
            BISH_MAGIC[s].mask=mask; BISH_MAGIC[s].magic=magic;
            BISH_MAGIC[s].shift=64-bits; BISH_MAGIC[s].tbl=BISH_TABLE[s];
            int size=1<<bits;
            for(int i=0;i<size;i++){
                U64 sub=occ_subset(i,bits,mask);
                U64 att=sliding_attacks(s,sub,BDIRS,4);
                int idx=(int)((sub*magic)>>(64-bits));
                BISH_TABLE[s][idx]=att;
            }
        }
    }
}

static inline U64 rook_attacks(int s, U64 occ){
    occ&=ROOK_MAGIC[s].mask;
    return ROOK_MAGIC[s].tbl[(occ*ROOK_MAGIC[s].magic)>>ROOK_MAGIC[s].shift];
}
static inline U64 bish_attacks(int s, U64 occ){
    occ&=BISH_MAGIC[s].mask;
    return BISH_MAGIC[s].tbl[(occ*BISH_MAGIC[s].magic)>>BISH_MAGIC[s].shift];
}
static inline U64 queen_attacks(int s, U64 occ){ return rook_attacks(s,occ)|bish_attacks(s,occ); }

typedef struct {
    U64  bb[2][6];                        
    U64  occ[2];                                        
    U64  all;                        
    int8_t piece_at[64];                               
    int8_t colour_at[64];
    uint8_t castle, ep_sq, side;
    uint16_t fifty;
    uint32_t hash;
} Pos;

static U64 ZOB[2][6][64], ZOB_SIDE, ZOB_CASTLE[16], ZOB_EP[8];
static void init_zob(void){
    uint64_t s=0xDEADBEEFCAFEBABEULL;
#define R64() (s^=s>>12,s^=s<<25,s^=s>>27,s*=0x2545F4914F6CDD1DULL)
    for(int c=0;c<2;c++) for(int p=0;p<6;p++) for(int q=0;q<64;q++) ZOB[c][p][q]=R64();
    ZOB_SIDE=R64();
    for(int i=0;i<16;i++) ZOB_CASTLE[i]=R64();
    for(int i=0;i<8;i++)  ZOB_EP[i]=R64();
#undef R64
}
static inline uint32_t hash32(uint64_t h){ return (uint32_t)(h^(h>>32)); }

static void refresh_hash(Pos*p){
    uint64_t h=0;
    for(int c=0;c<2;c++) for(int pc=0;pc<6;pc++){
        U64 bb=p->bb[c][pc]; while(bb){ int s=LSB(bb); POPLSB(bb); h^=ZOB[c][pc][s]; }
    }
    if(p->side==B) h^=ZOB_SIDE;
    h^=ZOB_CASTLE[p->castle&15];
    if(p->ep_sq) h^=ZOB_EP[p->ep_sq&7];
    p->hash=hash32(h);
}

static inline bool sq_attacked(const Pos*p, int s, int by){
    U64 occ=p->all;
    if(PAWN_ATTACKS[by^1][s]&p->bb[by][P_]) return true;
    if(KNIGHT_ATTACKS[s]&p->bb[by][N_])     return true;
    if(KING_ATTACKS[s]&p->bb[by][K_])       return true;
    U64 diag=bish_attacks(s,occ); if(diag&(p->bb[by][B_]|p->bb[by][Q_])) return true;
    U64 orth=rook_attacks(s,occ); if(orth&(p->bb[by][R_]|p->bb[by][Q_])) return true;
    return false;
}
static inline bool in_check(const Pos*p){ return sq_attacked(p,LSB(p->bb[p->side][K_]),p->side^1); }

static void place(Pos*p, int c, int pc, int s){
    p->bb[c][pc]|=BB(s); p->occ[c]|=BB(s); p->all|=BB(s);
    p->piece_at[s]=(int8_t)pc; p->colour_at[s]=(int8_t)c;
}

static void init_startpos(Pos*p){
    memset(p,0,sizeof(Pos));
    for(int i=0;i<64;i++){ p->piece_at[i]=NONE; p->colour_at[i]=-1; }
    p->castle=CR_WK|CR_WQ|CR_BK|CR_BQ; p->side=W;
    static const int8_t back[8]={R_,N_,B_,Q_,K_,B_,N_,R_};
    for(int f=0;f<8;f++){
        place(p,W,back[f],SQ(7,f)); place(p,B,back[f],SQ(0,f));
        place(p,W,P_,SQ(6,f)); place(p,B,P_,SQ(1,f));
    }
    refresh_hash(p);
}

void print_pos(const Pos*p){
    static const char PC_CHARS[]="PNBRQKpnbrqk.";
    printf("     a  b  c  d  e  f  g  h\n");
    printf("   +--+--+--+--+--+--+--+--+\n");
    for(int r=0;r<8;r++){
        printf(" %d |",8-r);
        for(int f=0;f<8;f++){
            int s=SQ(r,f); int pc=p->piece_at[s];
            if(pc==NONE) printf(".  ");
            else{ char ch=PC_CHARS[pc+(p->colour_at[s]==B?6:0)]; printf("%c  ",ch); }
        }
        printf("| %d\n",8-r);
    }
    printf("   +--+--+--+--+--+--+--+--+\n");
    printf("     a  b  c  d  e  f  g  h\n");
    printf("  %s | castle:%s%s%s%s | ep:%s | 50mv:%d\n\n",
           p->side==W?"White":"Black",
           (p->castle&CR_WK)?"K":"-",(p->castle&CR_WQ)?"Q":"-",
           (p->castle&CR_BK)?"k":"-",(p->castle&CR_BQ)?"q":"-",
           p->ep_sq?SQ_NAME[p->ep_sq]:"--", p->fifty);
}

typedef uint32_t Move;
#define MK_MOVE(f,t,pr,ep,ca,cp) ((f)|((t)<<6)|((pr)<<12)|((ep)<<15)|((ca)<<16)|((cp)<<17))
#define MV_FROM(m)   ((m)&63)
#define MV_TO(m)     (((m)>>6)&63)
#define MV_PROMO(m)  (((m)>>12)&7)                             
#define MV_EP(m)     (((m)>>15)&1)
#define MV_CASTLE(m) (((m)>>16)&1)
#define MV_CAP(m)    (((m)>>17)&1)
#define NULL_MOVE    0

static const int PROMO_PC[5]={NONE,N_,B_,R_,Q_};

typedef struct {
    uint32_t hash; uint8_t castle,ep,fifty;
    int8_t cap_pc, cap_col;
} Undo;

static inline void remove_piece(Pos*p, int c, int pc, int s){
    U64 b=BB(s); p->bb[c][pc]^=b; p->occ[c]^=b; p->all^=b;
    p->piece_at[s]=NONE; p->colour_at[s]=-1;
}
static inline void add_piece(Pos*p, int c, int pc, int s){
    U64 b=BB(s); p->bb[c][pc]|=b; p->occ[c]|=b; p->all|=b;
    p->piece_at[s]=(int8_t)pc; p->colour_at[s]=(int8_t)c;
}
static inline void move_piece(Pos*p, int c, int pc, int from, int to){
    U64 b=BB(from)|BB(to); p->bb[c][pc]^=b; p->occ[c]^=b; p->all^=b;
    p->piece_at[from]=NONE; p->colour_at[from]=-1;
    p->piece_at[to]=(int8_t)pc; p->colour_at[to]=(int8_t)c;
}

static void make_move(Pos*p, Move m, Undo*u){
    int from=MV_FROM(m), to=MV_TO(m);
    int c=p->side, ec=c^1;
    int mpc=p->piece_at[from];
    int cpc=p->piece_at[to];                    

    u->hash=p->hash; u->castle=p->castle; u->ep=p->ep_sq; u->fifty=p->fifty;
    u->cap_pc=(int8_t)cpc; u->cap_col=(int8_t)ec;

    uint64_t h64=(uint64_t)p->hash;                                      

    p->fifty++;
    if(mpc==P_||MV_CAP(m)) p->fifty=0;
    p->ep_sq=0;

    if(cpc!=NONE) remove_piece(p,ec,cpc,to);

    if(MV_EP(m)){
        int ep_pawn=(c==W)?(to+8):(to-8);
        remove_piece(p,ec,P_,ep_pawn);
        u->cap_pc=P_; u->cap_col=(int8_t)ec;
    }

    move_piece(p,c,mpc,from,to);

    int promo=MV_PROMO(m);
    if(promo){
        remove_piece(p,c,P_,to);
        add_piece(p,c,PROMO_PC[promo],to);
    }

    if(MV_CASTLE(m)){
        if(to==G1){ move_piece(p,W,R_,H1,F1); }
        else if(to==C1){ move_piece(p,W,R_,A1,D1); }
        else if(to==G8){ move_piece(p,B,R_,H8,F8); }
        else            { move_piece(p,B,R_,A8,D8); }
    }

    if(mpc==P_&&abs(to-from)==16)
        p->ep_sq=(uint8_t)((from+to)/2);

    p->castle &= castle_mask_t[from];
    p->castle &= castle_mask_t[to];
    p->side=(uint8_t)ec;
    refresh_hash(p);
    (void)h64;
}

static void undo_move(Pos*p, Move m, const Undo*u){
    int from=MV_FROM(m), to=MV_TO(m);
    int ec=p->side, c=ec^1;                             
    int mpc=p->piece_at[to];

    int promo=MV_PROMO(m);
    if(promo){ remove_piece(p,c,PROMO_PC[promo],to); mpc=P_; add_piece(p,c,P_,to); }

    move_piece(p,c,mpc,to,from);

    if(u->cap_pc!=NONE && !MV_EP(m))
        add_piece(p,(int)u->cap_col,(int)u->cap_pc,to);

    if(MV_EP(m)){
        int ep_pawn=(c==W)?(to+8):(to-8);
        add_piece(p,(int)u->cap_col,P_,ep_pawn);
    }

    if(MV_CASTLE(m)){
        if(to==G1){ move_piece(p,W,R_,F1,H1); }
        else if(to==C1){ move_piece(p,W,R_,D1,A1); }
        else if(to==G8){ move_piece(p,B,R_,F8,H8); }
        else            { move_piece(p,B,R_,D8,A8); }
    }

    p->castle=u->castle; p->ep_sq=u->ep; p->fifty=u->fifty;
    p->side=(uint8_t)c; p->hash=u->hash;
}

static int gen_all(const Pos*p, Move*buf){
    int n=0; int c=p->side, ec=c^1;
    U64 en=p->occ[ec], occ=p->all, empty=~occ;

#define ADD(f,t,pr,ep,ca,cp) buf[n++]=MK_MOVE(f,t,pr,ep,ca,cp)

    {
        U64 pawns=p->bb[c][P_];
        int up=(c==W)?-8:8;
        int promo_rank=(c==W)?0:7;
        int start_rank=(c==W)?6:1;
        U64 push1=(c==W)?(pawns>>8&empty):(pawns<<8&empty);
        U64 tmp=push1;
        while(tmp){ int to=LSB(tmp); POPLSB(tmp); int from=to-up;
            if(RANK(to)==promo_rank){ ADD(from,to,4,0,0,0);ADD(from,to,3,0,0,0);ADD(from,to,2,0,0,0);ADD(from,to,1,0,0,0); }
            else ADD(from,to,0,0,0,0); }
        U64 start_bb=0;
        for(int f=0;f<8;f++) start_bb|=BB(SQ(start_rank,f));
        U64 push2=(c==W)?((push1&(start_bb>>8))>>8&empty):((push1&(start_bb<<8))<<8&empty);
        tmp=push2;
        while(tmp){ int to=LSB(tmp); POPLSB(tmp); int from=to-2*up; ADD(from,to,0,0,0,0); }
        while(pawns){ int from=LSB(pawns); POPLSB(pawns);
            U64 atk=PAWN_ATTACKS[c][from]&en;
            while(atk){ int to=LSB(atk); POPLSB(atk);
                if(RANK(to)==promo_rank){ ADD(from,to,4,0,0,1);ADD(from,to,3,0,0,1);ADD(from,to,2,0,0,1);ADD(from,to,1,0,0,1); }
                else ADD(from,to,0,0,0,1); }
            if(p->ep_sq && (PAWN_ATTACKS[c][from]&BB(p->ep_sq)))
                ADD(from,p->ep_sq,0,1,0,1);
        }
    }
    { U64 kn=p->bb[c][N_]; while(kn){ int from=LSB(kn); POPLSB(kn);
        U64 a=KNIGHT_ATTACKS[from];
        U64 caps=a&en; while(caps){ int to=LSB(caps); POPLSB(caps); ADD(from,to,0,0,0,1); }
        U64 quq=a&empty; while(quq){ int to=LSB(quq); POPLSB(quq); ADD(from,to,0,0,0,0); }
    }}
    { U64 bs=p->bb[c][B_]; while(bs){ int from=LSB(bs); POPLSB(bs);
        U64 a=bish_attacks(from,occ);
        U64 caps=a&en; while(caps){ int to=LSB(caps); POPLSB(caps); ADD(from,to,0,0,0,1); }
        U64 quq=a&empty; while(quq){ int to=LSB(quq); POPLSB(quq); ADD(from,to,0,0,0,0); }
    }}
    { U64 rs=p->bb[c][R_]; while(rs){ int from=LSB(rs); POPLSB(rs);
        U64 a=rook_attacks(from,occ);
        U64 caps=a&en; while(caps){ int to=LSB(caps); POPLSB(caps); ADD(from,to,0,0,0,1); }
        U64 quq=a&empty; while(quq){ int to=LSB(quq); POPLSB(quq); ADD(from,to,0,0,0,0); }
    }}
    { U64 qs=p->bb[c][Q_]; while(qs){ int from=LSB(qs); POPLSB(qs);
        U64 a=queen_attacks(from,occ);
        U64 caps=a&en; while(caps){ int to=LSB(caps); POPLSB(caps); ADD(from,to,0,0,0,1); }
        U64 quq=a&empty; while(quq){ int to=LSB(quq); POPLSB(quq); ADD(from,to,0,0,0,0); }
    }}
    { int from=LSB(p->bb[c][K_]);
        U64 a=KING_ATTACKS[from];
        U64 caps=a&en; while(caps){ int to=LSB(caps); POPLSB(caps); ADD(from,to,0,0,0,1); }
        U64 quq=a&empty; while(quq){ int to=LSB(quq); POPLSB(quq); ADD(from,to,0,0,0,0); }
        if(!in_check(p)){
            if(c==W){
                if((p->castle&CR_WK)&&!(occ&0x6000000000000000ULL)&&!sq_attacked(p,F1,ec)&&!sq_attacked(p,G1,ec))
                    ADD(E1,G1,0,0,1,0);                                      
                if((p->castle&CR_WQ)&&!(occ&0x0E00000000000000ULL)&&!sq_attacked(p,D1,ec)&&!sq_attacked(p,C1,ec))
                    ADD(E1,C1,0,0,1,0);
            } else {
                if((p->castle&CR_BK)&&!(occ&0x60ULL)&&!sq_attacked(p,F8,ec)&&!sq_attacked(p,G8,ec))
                    ADD(E8,G8,0,0,1,0);
                if((p->castle&CR_BQ)&&!(occ&0x0EULL)&&!sq_attacked(p,D8,ec)&&!sq_attacked(p,C8,ec))
                    ADD(E8,C8,0,0,1,0);
            }
        }
    }
    (void)0;
#undef ADD
    return n;
}

static inline bool is_legal(Pos*p, Move m){
    Undo u; make_move(p,m,&u);
    bool ok=!sq_attacked(p,LSB(p->bb[p->side^1][K_]),p->side);
    undo_move(p,m,&u); return ok;
}

static const int SEE_VAL[6]={100,300,300,500,900,20000};

static U64 all_attackers(const Pos*p, int sq, U64 occ){
    return (PAWN_ATTACKS[W][sq]&p->bb[B][P_])
          |(PAWN_ATTACKS[B][sq]&p->bb[W][P_])
          |(KNIGHT_ATTACKS[sq]&(p->bb[W][N_]|p->bb[B][N_]))
          |(KING_ATTACKS[sq]&(p->bb[W][K_]|p->bb[B][K_]))
          |(bish_attacks(sq,occ)&(p->bb[W][B_]|p->bb[B][B_]|p->bb[W][Q_]|p->bb[B][Q_]))
          |(rook_attacks(sq,occ)&(p->bb[W][R_]|p->bb[B][R_]|p->bb[W][Q_]|p->bb[B][Q_]));
}

static int see(const Pos*p, Move m){
    int from=MV_FROM(m), to=MV_TO(m);
    int cap_pc=p->piece_at[to];
    if(cap_pc==NONE&&!MV_EP(m)) return 0;
    int gain[32]; int d=0;
    gain[d]=(cap_pc!=NONE)?SEE_VAL[cap_pc]:SEE_VAL[P_];
    int pc=p->piece_at[from];
    int side=p->side;
    U64 occ=p->all; occ^=BB(from);
    U64 atk=all_attackers(p,to,occ)&occ;
    side^=1;
    do {
        d++;
        gain[d]=SEE_VAL[pc]-gain[d-1];
        U64 mine=atk&p->occ[side];
        if(!mine) break;
        int lva_pc=-1;
        for(int pp=P_;pp<=K_;pp++){
            U64 bb=mine&p->bb[side][pp];
            if(bb){ from=LSB(bb); lva_pc=pp; break; }
        }
        if(lva_pc<0) break;
        pc=lva_pc;
        occ^=BB(from);
        atk=(all_attackers(p,to,occ)&occ);
        side^=1;
    } while(1);
    while(--d>0) gain[d-1]=(-gain[d]>gain[d-1])?-gain[d]:gain[d-1];
    return gain[0];
}

#define TT_SIZE (1<<23)                  
#define TT_EXACT 0
#define TT_LOWER 1
#define TT_UPPER 2
typedef struct { uint32_t key; int16_t eval; int8_t depth; uint8_t flag; Move best; uint8_t gen; } TTEntry;
typedef struct { TTEntry e[2]; } TTBucket;                                       
static TTBucket *g_tt;
static uint8_t g_gen=0;
static void tt_init(void){ if(!g_tt) g_tt=calloc(TT_SIZE,sizeof(TTBucket)); }
static void tt_new_search(void){ g_gen++; }
static void tt_store(uint32_t key, int eval, int depth, int flag, Move best){
    TTBucket*b=&g_tt[key&(TT_SIZE-1)];
    TTEntry*replace=&b->e[1];
    if(b->e[0].gen!=g_gen||depth>=(int)b->e[0].depth||b->e[0].key!=key) replace=&b->e[0];
    replace->key=key; replace->eval=(int16_t)eval; replace->depth=(int8_t)depth;
    replace->flag=(uint8_t)flag; replace->best=best; replace->gen=g_gen;
    if(replace==&b->e[0]){ b->e[1]=*replace; }
}
static bool tt_probe(uint32_t key, int depth, int*eval, int*flag, Move*best){
    TTBucket*b=&g_tt[key&(TT_SIZE-1)];
    *best=0;
    for(int i=0;i<2;i++){
        TTEntry*e=&b->e[i];
        if(e->key==key&&e->gen==g_gen){
            if(e->best) *best=e->best;
            if(e->depth>=depth){ *eval=e->eval; *flag=e->flag; return true; }
        }
    }
    return false;
}

static const int MAT_MG[6]={ 82,337,365,477,1025,0};
static const int MAT_EG[6]={106,281,297,512, 936,0};
static const int PHASE_INC[6]={0,1,1,2,4,0};

static const int16_t PST_MG[6][64]={
{        
  0,  0,  0,  0,  0,  0,  0,  0,
 98,134, 61, 95, 68,126, 34,-11,
 -6,  7, 26, 31, 65, 56, 25,-20,
-14, 13,  6, 21, 23, 12, 17,-23,
-27, -2, -5, 12, 17,  6, 10,-25,
-26, -4, -4,-10,  3,  3, 33,-12,
-35, -1,-20,-23,-15, 24, 38,-22,
  0,  0,  0,  0,  0,  0,  0,  0},
{        
-167,-89,-34,-49, 61,-97,-15,-107,
 -73,-41, 72, 36, 23, 62,  7, -17,
 -47, 60, 37, 65, 84,129, 73,  44,
  -9, 17, 19, 53, 37, 69, 18,  22,
 -13,  4, 16, 13, 28, 19, 21,  -8,
 -23, -9, 12, 10, 19, 17, 25, -16,
 -29,-53,-12, -3, -1, 18,-14, -19,
-105,-21,-58,-33,-17,-28,-19, -23},
{        
 -29,  4,-82,-37,-25,-42,  7, -8,
 -26, 16,-18,-13, 30, 59, 18,-47,
 -16, 37, 43, 40, 35, 50, 37, -2,
  -4,  5, 19, 50, 37, 37,  7, -2,
  -6, 13, 13, 26, 34, 12, 10,  4,
   0, 15, 15, 15, 14, 27, 18, 10,
   4, 15, 16,  0,  7, 21, 33,  1,
 -33, -3,-14,-21,-13,-12,-39,-21},
{        
  32, 42, 32, 51, 63,  9, 31, 43,
  27, 32, 58, 62, 80, 67, 26, 44,
  -5, 19, 26, 36, 17, 45, 61, 16,
 -24,-11,  7, 26, 24, 35, -8,-20,
 -36,-26,-12, -1,  9, -7,  6,-23,
 -45,-25,-16,-17,  3,  0, -5,-33,
 -44,-16,-20, -9, -1, 11, -6,-71,
 -19,-13,  1, 17, 16,  7,-37,-26},
{        
 -28,  0, 29, 12, 59, 44, 43, 45,
 -24,-39, -5,  1,-16, 57, 28, 54,
 -13,-17,  7,  8, 29, 56, 47, 57,
 -27,-27,-16,-16, -1, 17, -2,  1,
  -9,-26, -9,-10, -2, -4,  3, -3,
 -14,  2,-11,  2, -5,  2, 14,  5,
 -35, -8, 11,  2,  8, 15, -3,  1,
  -1,-18, -9, 10,-15,-25,-31,-50},
{           
 -65, 23, 16,-15,-56,-34,  2, 13,
  29, -1,-20, -7, -8, -4,-38,-29,
  -9, 24,  2,-16,-20,  6, 22,-22,
 -17,-20,-12,-27,-30,-25,-14,-36,
 -49, -1,-27,-39,-46,-44,-33,-51,
 -14,-14,-22,-46,-44,-30,-15,-27,
   1,  7, -8,-64,-43,-16,  9,  8,
 -15, 36, 12,-54,  8,-28, 24, 14}};

static const int16_t PST_EG[6][64]={
{        
  0,  0,  0,  0,  0,  0,  0,  0,
178,173,158,134,134,158,173,178,
 94,100, 85, 67, 67, 85,100, 94,
 32, 24, 13,  5,  5, 13, 24, 32,
 13,  9, -3, -7, -7, -3,  9, 13,
  4,  7, -6,  1,  0, -5,  6,  4,
 13,  8,  8,  8,  8,  8,  8, 13,
  0,  0,  0,  0,  0,  0,  0,  0},
{        
 -58,-38,-13,-28,-31,-27,-63,-99,
 -25, -8,-25, -2, -9,-25,-24,-52,
 -24,-20, 10,  9, -1, -9,-19,-41,
 -17,  3, 22, 22, 22, 11,  8,-18,
 -18, -6, 16, 25, 16, 17,  4,-18,
 -23, -3, -1, 15, 10, -3,-20,-22,
 -42,-20,-10, -5, -2,-20,-23,-44,
 -29,-51,-23,-15,-22,-18,-50,-64},
{        
 -14,-21,-11, -8, -7, -9,-17,-24,
  -8, -4,  7,-12, -3,-13, -4,-14,
   2, -8,  0, -1, -2,  6,  0,  4,
  -3,  9, 12,  9, 14, 10,  3,  2,
  -6,  3, 13, 19,  7, 10, -3, -9,
 -12, -3,  8, 10, 13,  3, -7,-15,
 -14,-18, -7, -1,  4, -9,-15,-27,
 -23, -9,-23, -5, -9,-16, -5,-17},
{        
  13, 10, 18, 15, 12, 12,  8,  5,
  11, 13, 13, 11, -3,  3,  8,  3,
   7,  7,  7,  5,  4, -3, -5, -3,
   4,  3, 13,  1,  2,  1, -1,  2,
   3,  5,  8,  4, -5, -6, -8,-11,
  -4,  0, -5, -1, -7,-12, -8,-16,
  -6, -6,  0,  2, -9, -9,-11, -3,
  -9,  2,  3, -1, -5,-13,  4,-20},
{        
  -9, 22, 22, 27, 27, 19, 10, 20,
 -17, 20, 32, 41, 58, 25, 30,  0,
 -20,  6,  9, 49, 47, 35, 19,  9,
   3, 22, 24, 45, 57, 40, 57, 36,
 -18, 28, 19, 47, 31, 34, 39, 23,
 -16,-27, 15,  6,  9, 17, 10,  5,
 -22,-23,-30,-16,-16,-23,-36,-32,
 -33,-28,-22,-43, -5,-32,-20,-41},
{           
 -74,-35,-18,-18,-11, 15,  4,-17,
 -12, 17, 14, 17, 17, 38, 23, 11,
  10, 17, 23, 15, 20, 45, 44, 13,
  -8, 22, 24, 27, 26, 33, 26,  3,
 -18, -4, 21, 24, 27, 23,  9,-11,
 -19, -3, 11, 21, 23, 16,  7, -9,
 -27,-11,  4, 13, 14,  4, -5,-17,
 -53,-34,-21,-11,-28,-14,-24,-43}};

static inline int pst_idx(int sq, int c){ return c==W ? sq : (sq^56); }

static inline U64 mob_area(const Pos*p, int c){
    int ec=c^1;
    U64 ep=p->bb[ec][P_];
    U64 ep_atk=(ec==B)?((ep>>7&~FILE_BB[0])|(ep>>9&~FILE_BB[7]))
                      :((ep<<7&~FILE_BB[7])|(ep<<9&~FILE_BB[0]));
    U64 blocked_pawns=p->bb[c][P_]&(c==W?(p->all>>8):(p->all<<8));
    return ~(ep_atk|blocked_pawns|p->bb[c][K_]);
}

static const int SAFETY_TABLE[100]={
  0,  0,  1,  2,  3,  5,  7, 10, 13, 16,
 20, 25, 30, 36, 42, 49, 56, 64, 72, 80,
 90,100,110,120,130,140,150,160,170,180,
190,200,210,220,230,240,250,260,270,280,
290,300,310,320,330,340,350,360,370,380,
390,400,410,420,430,440,450,460,470,480,
490,500,510,520,530,540,550,560,570,580,
590,600,610,620,630,640,650,660,670,680,
690,700,710,720,730,740,750,760,770,780,
790,800,810,820,830,840,850,860,870,880};

int evaluate(const Pos*p){
    int mg=0, eg=0;
    int phase=0;
    for(int c=0;c<2;c++) for(int pc=P_;pc<=Q_;pc++) phase+=PHASE_INC[pc]*POP(p->bb[c][pc]);
    if(phase>24) phase=24;
    int ph=(24-phase)*256/24;                   
    int sign[2]={-1,1};                                                 

    int ksq[2]={LSB(p->bb[W][K_]),LSB(p->bb[B][K_])};

    int ks_units[2]={0,0};
    int ks_atk_cnt[2]={0,0};

    U64 mob[2]; mob[W]=mob_area(p,W); mob[B]=mob_area(p,B);
    int wbish=POP(p->bb[W][B_]), bbish=POP(p->bb[B][B_]);

    for(int c=0;c<2;c++){
        int ec=c^1;
        int s_=sign[c];
        U64 occ=p->all;
        U64 ma=mob[c];

        U64 pawns=p->bb[c][P_];
        U64 ep_pawns=p->bb[ec][P_];
        while(pawns){
            int sq_=LSB(pawns); POPLSB(pawns);
            int pi=pst_idx(sq_,c);
            mg+=s_*(MAT_MG[P_]+PST_MG[P_][pi]);
            eg+=s_*(MAT_EG[P_]+PST_EG[P_][pi]);
            if(POP(p->bb[c][P_]&FILE_BB[FILE(sq_)])>1){ mg+=s_*-11; eg+=s_*-56; }
            if(!(p->bb[c][P_]&ADJ_FILES[FILE(sq_)])){ mg+=s_*-5; eg+=s_*-15; }
            if(!(PASSED_MASK[c][sq_]&ep_pawns)){
                int rank=(c==W)?(6-RANK(sq_)):(RANK(sq_)-1); if(rank<0)rank=0;
                static const int PP_MG[7]={0,5,10,20,35,55,80};
                static const int PP_EG[7]={0,10,20,40,70,110,160};
                mg+=s_*PP_MG[rank<7?rank:6]; eg+=s_*PP_EG[rank<7?rank:6];
                U64 behind=(c==W)?(FILE_BB[FILE(sq_)]&~((BB(sq_)<<1)-1))
                                 :(FILE_BB[FILE(sq_)]&((BB(sq_)<<1)-1));
                if(behind&p->bb[c][R_]){ mg+=s_*8; eg+=s_*18; }
            }
        }

        U64 kn=p->bb[c][N_];
        while(kn){ int sq_=LSB(kn); POPLSB(kn);
            int pi=pst_idx(sq_,c);
            mg+=s_*(MAT_MG[N_]+PST_MG[N_][pi]);
            eg+=s_*(MAT_EG[N_]+PST_EG[N_][pi]);
            U64 a=KNIGHT_ATTACKS[sq_]&ma;
            int mob_n=POP(a)-4;
            mg+=s_*mob_n*4; eg+=s_*mob_n*4;
            int r=RANK(sq_), f=FILE(sq_);
            bool in_opp=(c==W)?(r<=3):(r>=4);
            if(in_opp&&!(PASSED_MASK[c][sq_]&ep_pawns)){
                int bonus=18+((ADJ_FILES[f]|FILE_BB[f])&p->bb[c][P_]?10:0);
                mg+=s_*bonus; eg+=s_*(bonus/2);
            }
            if(KNIGHT_ATTACKS[sq_]&KING_ZONE[ec][ksq[ec]]){ ks_units[ec]+=2; ks_atk_cnt[ec]++; }
        }

        U64 bs=p->bb[c][B_];
        while(bs){ int sq_=LSB(bs); POPLSB(bs);
            int pi=pst_idx(sq_,c);
            mg+=s_*(MAT_MG[B_]+PST_MG[B_][pi]);
            eg+=s_*(MAT_EG[B_]+PST_EG[B_][pi]);
            U64 a=bish_attacks(sq_,occ)&ma;
            int mob_n=POP(a)-6;
            mg+=s_*mob_n*4; eg+=s_*mob_n*5;
            if(bish_attacks(sq_,p->bb[c][P_])&(BB(D5)|BB(E5)|BB(D4)|BB(E4))){ mg+=s_*15; }
            if(bish_attacks(sq_,occ)&KING_ZONE[ec][ksq[ec]]){ ks_units[ec]+=2; ks_atk_cnt[ec]++; }
        }
        if(wbish>=2&&c==W){ mg-=22; eg-=44; }
        if(bbish>=2&&c==B){ mg+=22; eg+=44; }

        U64 rs=p->bb[c][R_];
        while(rs){ int sq_=LSB(rs); POPLSB(rs);
            int pi=pst_idx(sq_,c);
            mg+=s_*(MAT_MG[R_]+PST_MG[R_][pi]);
            eg+=s_*(MAT_EG[R_]+PST_EG[R_][pi]);
            U64 a=rook_attacks(sq_,occ)&ma;
            int mob_n=POP(a)-7;
            mg+=s_*mob_n*3; eg+=s_*mob_n*4;
            U64 filebb=FILE_BB[FILE(sq_)];
            if(!(filebb&p->bb[c][P_])){                          
                if(!(filebb&p->bb[ec][P_])){ mg+=s_*25; eg+=s_*20; }           
                else                        { mg+=s_*12; eg+=s_*10; }           
            }
            int rank7=(c==W)?1:6;
            if(RANK(sq_)==rank7){ mg+=s_*30; eg+=s_*40; }
            if(rook_attacks(sq_,occ)&KING_ZONE[ec][ksq[ec]]){ ks_units[ec]+=3; ks_atk_cnt[ec]++; }
        }

        U64 qs=p->bb[c][Q_];
        while(qs){ int sq_=LSB(qs); POPLSB(qs);
            int pi=pst_idx(sq_,c);
            mg+=s_*(MAT_MG[Q_]+PST_MG[Q_][pi]);
            eg+=s_*(MAT_EG[Q_]+PST_EG[Q_][pi]);
            U64 a=queen_attacks(sq_,occ)&ma;
            int mob_n=POP(a)-14;
            mg+=s_*mob_n*2; eg+=s_*mob_n*3;
            if(queen_attacks(sq_,occ)&KING_ZONE[ec][ksq[ec]]){ ks_units[ec]+=5; ks_atk_cnt[ec]++; }
        }

        {   int sq_=ksq[c];
            int pi=pst_idx(sq_,c);
            mg+=s_*PST_MG[K_][pi];
            eg+=s_*PST_EG[K_][pi];
        }
    }

    for(int c=0;c<2;c++){
        if(ks_atk_cnt[c]>=2){
            int idx=ks_units[c]<100?ks_units[c]:99;
            int penalty=SAFETY_TABLE[idx];
            int ksq_=ksq[c]; int r=RANK(ksq_), f=FILE(ksq_);
            int shelter=0;
            int pstep=(c==W)?-1:1;
            for(int df=-1;df<=1;df++){
                int nf=f+df; if(nf<0||nf>7) continue;
                U64 col_pawns=p->bb[c][P_]&FILE_BB[nf];
                if(!col_pawns){ shelter+=15; continue; }                                 
                int best_dist=4;
                U64 tmp=col_pawns;
                while(tmp){ int s=LSB(tmp); POPLSB(tmp);
                    int dist=abs(RANK(s)-(r+pstep));
                    if(dist<best_dist) best_dist=dist;
                }
                shelter+=best_dist*4;
            }
            penalty+=shelter;
            if(c==W){ mg+=penalty; }                                                     
            else     { mg-=penalty; }
        }
    }

    int total=(mg*(256-ph)+eg*ph)/256;
    return total;                              
}

static uint32_t g_game_hist[1024];
static int g_game_hist_len=0;
static __thread uint32_t t_hist[1024];
static __thread int t_hist_len=0;

static bool is_rep(uint32_t key, int n){
    int found=0;
    for(int i=t_hist_len-1;i>=0;i--) if(t_hist[i]==key&&++found>=n) return true;
    for(int i=g_game_hist_len-1;i>=0;i--) if(g_game_hist[i]==key&&++found>=n) return true;
    return false;
}

static int  g_hist_h[2][64][64];
static Move g_killer[128][2];
static Move g_counter[64][64];                                                 

static inline void hist_bonus(int c, int f, int t, int d){ g_hist_h[c][f][t]+=d*d; if(g_hist_h[c][f][t]>1<<20) for(int a=0;a<64;a++) for(int b=0;b<64;b++) g_hist_h[c][a][b]>>=1; }
static inline void hist_malus(int c, int f, int t, int d){ g_hist_h[c][f][t]-=d*d; if(g_hist_h[c][f][t]<-(1<<20)) g_hist_h[c][f][t]=-(1<<20); }

static inline int score_move(const Pos*p, Move m, Move tt_move, int ply, Move prev){
    if(m==tt_move) return 10000000;
    int from=MV_FROM(m),to=MV_TO(m),promo=MV_PROMO(m);
    if(promo){ return 9000000+(promo==4?900:promo==3?500:promo==2?300:300); }
    if(MV_CAP(m)){
        int sv=see(p,m);
        if(sv>=0){
            int vic=p->piece_at[to]==NONE?SEE_VAL[P_]:SEE_VAL[p->piece_at[to]];
            return 8000000+vic-SEE_VAL[p->piece_at[from]];
        }
        return 3000000+sv;                                   
    }
    int c=p->side;
    if(ply<128&&m==g_killer[ply][0]) return 7000000;
    if(ply<128&&m==g_killer[ply][1]) return 6900000;
    if(prev && MV_FROM(prev)<64 && MV_TO(prev)<64 && m==g_counter[MV_FROM(prev)][MV_TO(prev)]) return 6800000;
    return g_hist_h[c][from][to];
}

static void sort_moves(const Pos*p, Move*mv, int n, Move tt_move, int ply, Move prev){
    int sc[256]; for(int i=0;i<n;i++) sc[i]=score_move(p,mv[i],tt_move,ply,prev);
    for(int i=1;i<n;i++){
        Move m=mv[i]; int s=sc[i]; int j=i-1;
        while(j>=0&&sc[j]<s){ mv[j+1]=mv[j]; sc[j+1]=sc[j]; j--; }
        mv[j+1]=m; sc[j+1]=s;
    }
}

static int LMR[64][64];
static void init_lmr(void){
    for(int d=1;d<64;d++) for(int m=1;m<64;m++)
        LMR[d][m]=(int)(0.75+log(d)*log(m)/2.25);
}

static volatile double g_tc_start=0, g_tc_soft=0, g_tc_hard=0;
static volatile bool g_stop=false;
static inline bool tc_soft(void){ return g_tc_soft>0&&(now_ms()-g_tc_start)>=g_tc_soft; }
static inline bool tc_hard(void){ return g_tc_hard>0&&(now_ms()-g_tc_start)>=g_tc_hard; }
static void calc_tc(double rem, double inc, double*soft, double*hard){
    double base=rem/20.0+inc*0.75;
    if(base<50) base=50;
    if(base>rem*0.4) base=rem*0.4;
    *soft=base; *hard=base*3.0;
    if(*hard>rem*0.45) *hard=rem*0.45;
    if(*hard<*soft+50) *hard=*soft+50;
}

#define INF  32000
#define MATE 30000
#define MATE_IN 29000
static int g_nodes_searched=0;                                             

static int qsearch(Pos*p, int alpha, int beta, int ply){
    if(tc_hard()){ g_stop=true; return 0; }
    g_nodes_searched++;
    int sign=(p->side==B)?1:-1;
    int stand_pat=sign*evaluate(p);
    if(stand_pat>=beta) return beta;
    if(stand_pat>alpha) alpha=stand_pat;

    Move mv[256]; int n=gen_all(p,mv);
    sort_moves(p,mv,n,0,ply,0);
    Undo u;
    for(int i=0;i<n;i++){
        if(!MV_CAP(mv[i])&&!MV_PROMO(mv[i])) continue;
        int cap_val=(p->piece_at[MV_TO(mv[i])]!=NONE)?SEE_VAL[p->piece_at[MV_TO(mv[i])]]:
                    (MV_EP(mv[i])?SEE_VAL[P_]:0);
        if(stand_pat+cap_val+200<alpha) continue;
        if(MV_CAP(mv[i])&&!MV_PROMO(mv[i])&&see(p,mv[i])<0) continue;
        if(!is_legal(p,mv[i])) continue;
        make_move(p,mv[i],&u);
        int val=-qsearch(p,-beta,-alpha,ply+1);
        undo_move(p,mv[i],&u);
        if(val>=beta) return beta;
        if(val>alpha) alpha=val;
    }
    return alpha;
}

static int search(Pos*p, int depth, int alpha, int beta, int ply, Move prev, bool cut_node, Move excluded);

static int search(Pos*p, int depth, int alpha, int beta, int ply, Move prev, bool cut_node, Move excluded){
    if(g_stop||tc_hard()){ g_stop=true; return 0; }
    g_nodes_searched++;

    int c=p->side; int ec=c^1;
    uint32_t key=p->hash;

    if(p->fifty>=100) return 0;
    if(ply>0&&is_rep(key,2)) return 0;

    int tt_eval=0,tt_flag=-1; Move tt_move=0;
    bool tt_hit = excluded ? false : tt_probe(key,depth,&tt_eval,&tt_flag,&tt_move);
    if(tt_hit&&tt_flag!=-1&&ply>0){
        if(tt_flag==TT_EXACT) return tt_eval;
        if(tt_flag==TT_LOWER&&tt_eval>=beta) return tt_eval;
        if(tt_flag==TT_UPPER&&tt_eval<=alpha) return tt_eval;
    }

    if(depth<=0) return qsearch(p,alpha,beta,ply);

    bool in_chk=in_check(p);
    if(in_chk) depth++;                      

    int sign=(c==B)?1:-1;
    int seval=(tt_hit&&tt_flag!=-1)?tt_eval:sign*evaluate(p);

    static const int RFP[9]={0,80,160,250,350,460,580,710,850};
    if(!in_chk&&depth<=8&&!cut_node&&seval-RFP[depth>=9?8:depth]>=beta&&seval<MATE_IN)
        return seval;

    if(!in_chk&&depth<=3&&seval+300+120*depth<alpha)
        return qsearch(p,alpha,beta,ply);

    if(!in_chk&&depth>=3&&ply>0&&seval>=beta&&POP(p->occ[c])>2){
        int R=3+(depth>=6)+(depth>=9)+(seval-beta)/200;
        if(R>depth-1) R=depth-1;
        t_hist[t_hist_len++]=key;
        uint8_t old_ep=p->ep_sq; p->ep_sq=0;
        p->side=(uint8_t)ec; p->hash^=ZOB_SIDE>>32;                 
        int ns=-search(p,depth-1-R,-beta,-beta+1,ply+1,0,!cut_node,0);
        p->side=(uint8_t)c; p->ep_sq=old_ep; p->hash=key;
        t_hist_len--;
        if(!g_stop&&ns>=beta){ if(ns>=MATE_IN) ns=beta; return ns; }
    }

    if(!tt_move&&depth>=6&&!in_chk){
        search(p,depth-4,alpha,beta,ply,prev,cut_node,0);
        tt_probe(key,0,&tt_eval,&tt_flag,&tt_move);
    }

    if(!in_chk&&depth>=5&&abs(beta)<MATE_IN){
        int pc_beta=beta+200;
        Move mv[256]; int nm=gen_all(p,mv);
        sort_moves(p,mv,nm,tt_move,ply,prev);
        Undo u; int tried=0;
        for(int i=0;i<nm&&tried<3;i++){
            if(!MV_CAP(mv[i])||!is_legal(p,mv[i])) continue;
            if(see(p,mv[i])<pc_beta-seval) continue;
            tried++;
            t_hist[t_hist_len++]=key;
            make_move(p,mv[i],&u);
            int val=-search(p,depth-4,-pc_beta,-pc_beta+1,ply+1,mv[i],!cut_node,0);
            undo_move(p,mv[i],&u); t_hist_len--;
            if(val>=pc_beta) return val;
        }
    }

    Move mv[256]; int n=gen_all(p,mv);
    sort_moves(p,mv,n,tt_move,ply,prev);

    int legal=0, best=-INF, orig_alpha=alpha;
    Move best_move=0;
    Move quiets_tried[64]; int qt=0;
    Undo u;

    for(int i=0;i<n;i++){
        if(excluded&&mv[i]==excluded) continue;
        if(!is_legal(p,mv[i])) continue;
        legal++;
        bool is_cap=(bool)MV_CAP(mv[i]);
        bool is_promo=(bool)MV_PROMO(mv[i]);
        bool is_cast=(bool)MV_CASTLE(mv[i]);

        make_move(p,mv[i],&u);
        bool gives_chk=in_check(p);
        undo_move(p,mv[i],&u);

        int new_d=depth-1;

        if(legal==1&&tt_hit&&mv[i]==tt_move&&tt_flag==TT_LOWER&&depth>=8&&!excluded&&abs(tt_eval)<MATE_IN){
            int s_beta=tt_eval-2*depth;
            int sv=search(p,(depth-1)/2,s_beta-1,s_beta,ply,prev,cut_node,mv[i]);
            if(!g_stop&&sv<s_beta) new_d++;                                           
        }

        if(!is_cap&&p->piece_at[MV_FROM(mv[i])]==P_){
            int to=MV_TO(mv[i]);
            int adv=(c==W)?(6-RANK(to)):(RANK(to)-1); if(adv<0)adv=0;
            if(adv>=4&&!(PASSED_MASK[c][to]&p->bb[ec][P_])) new_d++;
        }

        static const int FP[9]={0,100,175,275,400,550,725,925,1150};
        if(!in_chk&&!is_cap&&!is_promo&&!gives_chk&&!is_cast&&depth<=8&&legal>1&&ply>0){
            if(seval+FP[depth<=8?depth:8]<alpha){
                if(qt<64) quiets_tried[qt++]=mv[i];
                continue;
            }
        }

        if(is_cap&&!in_chk&&depth<=8&&!is_promo&&legal>1){
            if(see(p,mv[i])<-SEE_VAL[p->piece_at[MV_FROM(mv[i])]]*depth/2)
                continue;
        }

        int lmr=0;
        if(!in_chk&&!is_cap&&!is_promo&&!gives_chk&&legal>=4&&depth>=3){
            lmr=LMR[depth<64?depth:63][legal<64?legal:63];
            if(cut_node) lmr++;
            if(lmr>new_d-1) lmr=new_d-1;
            if(lmr<0) lmr=0;
        }

        t_hist[t_hist_len++]=key;
        make_move(p,mv[i],&u);
        int eval;
        if(legal==1){
            eval=-search(p,new_d,-beta,-alpha,ply+1,mv[i],false,0);
        } else {
            eval=-search(p,new_d-lmr,-alpha-1,-alpha,ply+1,mv[i],true,0);
            if(!g_stop&&eval>alpha&&(eval<beta||lmr>0))
                eval=-search(p,new_d,-beta,-alpha,ply+1,mv[i],false,0);
        }
        undo_move(p,mv[i],&u); t_hist_len--;

        if(g_stop) return 0;

        if(eval>best){ best=eval; best_move=mv[i]; }
        if(eval>alpha){
            alpha=eval;
            if(!is_cap&&!is_promo){
                if(ply<128){ g_killer[ply][1]=g_killer[ply][0]; g_killer[ply][0]=mv[i]; }
                hist_bonus(c,MV_FROM(mv[i]),MV_TO(mv[i]),depth);
                if(prev) g_counter[MV_FROM(prev)][MV_TO(prev)]=mv[i];
                for(int qi=0;qi<qt;qi++) hist_malus(c,MV_FROM(quiets_tried[qi]),MV_TO(quiets_tried[qi]),depth);
            }
        }
        if(alpha>=beta){
            if(!is_cap&&!is_promo){
                hist_bonus(c,MV_FROM(mv[i]),MV_TO(mv[i]),depth);
                for(int qi=0;qi<qt;qi++) hist_malus(c,MV_FROM(quiets_tried[qi]),MV_TO(quiets_tried[qi]),depth);
            }
            break;
        }
        if(!is_cap&&!is_promo&&qt<64) quiets_tried[qt++]=mv[i];
    }

    if(legal==0) best=excluded?alpha:(in_chk?(-MATE+ply):0);
    else if(best==-INF) best=alpha;                                                 

    if(!excluded){
        int flag=(best<=orig_alpha)?TT_UPPER:(best>=beta)?TT_LOWER:TT_EXACT;
        tt_store(key,best,depth,flag,best_move);
    }
    return best;
}

typedef struct { Pos pos; int max_depth; int thread_id; Move best; int best_eval; int best_depth; } WorkArg;
static pthread_mutex_t g_lock=PTHREAD_MUTEX_INITIALIZER;
static Move g_smp_best; static int g_smp_eval, g_smp_depth;
static int g_num_threads=1;

static void* worker(void*arg){
    WorkArg*wa=(WorkArg*)arg;
    Pos p=wa->pos;
    memcpy(t_hist,g_game_hist,g_game_hist_len*sizeof(uint32_t));
    t_hist_len=g_game_hist_len;
    memset(g_killer,0,sizeof(g_killer));
    memset(g_counter,0,sizeof(g_counter));

    Move best=0; int best_e=-INF, best_d=0;
    int start_d=1+(wa->thread_id&1);

    for(int depth=start_d;depth<=wa->max_depth;depth++){
        if(g_stop) break;
        if(tc_soft()&&depth>4) break;

        int asp=25, lo=(depth>=5)?(best_e-asp):-INF, hi=(depth>=5)?(best_e+asp):INF;
        int best_e_d=-INF; Move best_d_mv=0;
        int retries=0;

retry:
        retries++;
        if(retries>20){ fprintf(stderr,"[DBG] depth=%d too many retries lo=%d hi=%d asp=%d best_e_d=%d\n",depth,lo,hi,asp,best_e_d); g_stop=true; break; }
        best_e_d=-INF; best_d_mv=0;
        Move mv[256]; int n=gen_all(&p,mv);
        sort_moves(&p,mv,n,best,0,0);
        Undo u;
        for(int i=0;i<n;i++){
            if(g_stop||tc_hard()) break;
            if(!is_legal(&p,mv[i])) continue;
            t_hist[t_hist_len]=p.hash; t_hist_len++;
            make_move(&p,mv[i],&u);
            int eval;
            if(best_d_mv==0)
                eval=-search(&p,depth-1,-hi,-lo,1,mv[i],false,0);
            else {
                eval=-search(&p,depth-1,-lo-1,-lo,1,mv[i],true,0);
                if(!g_stop&&eval>lo&&eval<hi)
                    eval=-search(&p,depth-1,-hi,-lo,1,mv[i],false,0);
            }
            undo_move(&p,mv[i],&u); t_hist_len--;
            if(g_stop) break;
            if(eval>best_e_d){ best_e_d=eval; best_d_mv=mv[i]; }
            if(eval>lo) lo=eval;
            if(lo>=hi) break;
        }

        if(!g_stop&&depth>=5){
            if(best_e_d<=best_e-asp){ lo-=asp*3; asp*=2; goto retry; }
            if(best_e_d>=best_e+asp){ hi+=asp*3; asp*=2; goto retry; }
        }

        if(!g_stop&&best_d_mv){
            best=best_d_mv; best_e=best_e_d; best_d=depth;
            pthread_mutex_lock(&g_lock);
            if(best_d>g_smp_depth||(best_d==g_smp_depth&&best_e>g_smp_eval)){
                g_smp_best=best; g_smp_eval=best_e; g_smp_depth=best_d;
            }
            pthread_mutex_unlock(&g_lock);
            if(best_e>=MATE_IN){
                printf("  [depth %d] Mate in ~%d\n",depth,(MATE-best_e+1)/2);
                g_stop=true; break;
            }
        }
    }
    wa->best=best; wa->best_eval=best_e; wa->best_depth=best_d;
    return NULL;
}

void computer_move(Pos*p, int diff, int max_d, double soft_ms, double hard_ms){
    Move mv[256]; int n=gen_all(p,mv);
    Move legal[256]; int lc=0;
    for(int i=0;i<n;i++) if(is_legal(p,mv[i])) legal[lc++]=mv[i];
    if(!lc){ printf("No legal moves!\n"); return; }

    Move chosen=legal[0];
    if(diff==1){ chosen=legal[rand()%lc]; }
    else if(diff==2){
        for(int i=0;i<lc;i++) if(MV_CAP(legal[i])){ chosen=legal[i]; break; }
    } else {
        tt_new_search();
        memset(g_hist_h,0,sizeof(g_hist_h));
        memset(g_killer,0,sizeof(g_killer));
        memset(g_counter,0,sizeof(g_counter));
        g_tc_start=now_ms(); g_tc_soft=soft_ms; g_tc_hard=hard_ms; g_stop=false;
        g_smp_best=legal[0]; g_smp_eval=-INF; g_smp_depth=0;
        g_nodes_searched=0;

        int nt=g_num_threads;
        WorkArg*args=malloc(nt*sizeof(WorkArg));
        pthread_t*tids=malloc(nt*sizeof(pthread_t));
        for(int t=0;t<nt;t++){ args[t].pos=*p; args[t].max_depth=max_d; args[t].thread_id=t; }
        if(nt==1) worker(&args[0]);
        else{ for(int t=0;t<nt;t++) pthread_create(&tids[t],NULL,worker,&args[t]);
              for(int t=0;t<nt;t++) pthread_join(tids[t],NULL); }
        chosen=g_smp_best;
        double elapsed=now_ms()-g_tc_start;
        printf("  [depth %d, eval %+d, %.0fknps, %.0fms]\n",
               g_smp_depth, g_smp_eval,
               g_nodes_searched/elapsed, elapsed);
        free(args); free(tids);
    }

    int from=MV_FROM(chosen),to=MV_TO(chosen),pr=MV_PROMO(chosen);
    printf("\n=== COMPUTER MOVE: %s%s",SQ_NAME[from],SQ_NAME[to]);
    if(pr){ printf("%c","?nbrq"[pr]); }
    printf(" ===\n");
    Undo u; make_move(p,chosen,&u);
}

static bool load_fen(Pos*p, const char*fen){
    memset(p,0,sizeof(Pos));
    for(int i=0;i<64;i++){ p->piece_at[i]=NONE; p->colour_at[i]=-1; }
    int r=0,f=0;
    const char*s=fen;
    static const char*PCS="PNBRQKpnbrqk";
    while(*s&&*s!=' '){
        if(*s=='/'){r++;f=0;}
        else if(*s>='1'&&*s<='8'){f+=*s-'0';}
        else{
            const char*cp=strchr(PCS,*s);
            if(cp){ int idx=(int)(cp-PCS); int c=idx>=6?B:W; int pc=idx%6;
                    place(p,c,pc,SQ(r,f)); f++; }
        }
        s++;
    }
    while(*s==' ')s++;
    p->side=(*s=='w')?W:B; s++; while(*s==' ')s++;
    while(*s&&*s!=' '){
        if(*s=='K') p->castle|=CR_WK;
        if(*s=='Q') p->castle|=CR_WQ;
        if(*s=='k') p->castle|=CR_BK;
        if(*s=='q') p->castle|=CR_BQ;
        if(*s=='-') { s++; break; }
        s++;
    }
    while(*s==' ')s++;
    if(*s&&*s!='-'){
        int ef=(*s)-'a'; s++;
        int er=8-(*s-'0'); s++;
        p->ep_sq=(uint8_t)SQ(er,ef);
    } else if(*s=='-') s++;
    while(*s==' ')s++;
    if(*s) p->fifty=(uint16_t)atoi(s);
    refresh_hash(p);
    return true;
}

static void save_board(const Pos*p, const char*fname){
    FILE*f=fopen(fname,"w"); if(!f){fprintf(stderr,"Cannot write %s\n",fname);return;}
    static const char PC[]="PNBRQKpnbrqk";
    fprintf(f,"      A   B   C   D   E   F   G   H\n");
    fprintf(f,"    +---+---+---+---+---+---+---+---+\n");
    for(int r=0;r<8;r++){
        fprintf(f," %d  |",8-r);
        for(int fl=0;fl<8;fl++){
            int sq_=SQ(r,fl); int pc=p->piece_at[sq_];
            if(pc==NONE) fprintf(f,"   |");
            else{ char ch=PC[pc+(p->colour_at[sq_]==B?6:0)]; fprintf(f," %c |",ch); }
        }
        fprintf(f," %d\n",8-r);
        if(r<7) fprintf(f,"    +---+---+---+---+---+---+---+---+\n");
    }
    fprintf(f,"    +---+---+---+---+---+---+---+---+\n");
    fprintf(f,"      A   B   C   D   E   F   G   H\n");
    fprintf(f,"nu_side %d\nnu_castle %d\nnu_ep %d\nnu_fifty %d\n",
            p->side,p->castle,p->ep_sq,p->fifty);
    fclose(f);
}

static void load_board(Pos*p, const char*data){
    memset(p,0,sizeof(Pos));
    for(int i=0;i<64;i++){ p->piece_at[i]=NONE; p->colour_at[i]=-1; }
    p->castle=CR_WK|CR_WQ|CR_BK|CR_BQ; p->side=B;
    const char*q;
    if((q=strstr(data,"nu_side")))   p->side  =(uint8_t)atoi(q+7);
    if((q=strstr(data,"nu_castle"))) p->castle=(uint8_t)atoi(q+9);
    if((q=strstr(data,"nu_ep")))     p->ep_sq =(uint8_t)atoi(q+5);
    if((q=strstr(data,"nu_fifty")))  p->fifty =(uint16_t)atoi(q+8);
    char buf[8192]; strncpy(buf,data,sizeof(buf)-1); buf[sizeof(buf)-1]=0;
    static const char PC[]="PNBRQKpnbrqk";
    int row=0; char*line=strtok(buf,"\n");
    while(line&&row<8){
        if(strchr(line,'A')||strchr(line,'+')||strlen(line)<5){line=strtok(NULL,"\n");continue;}
        int col=0;
        for(int i=0;line[i]&&col<8;i++){
            if(line[i]=='|'){
                int j=i+1; while(line[j]==' ')j++;
                if(line[j]!='|'&&line[j]!='\0'){
                    char ch=line[j]; int pc=NONE, c=-1;
                    if(ch!=' '){ const char*cp=strchr(PC,ch); if(cp){ int idx=(int)(cp-PC); c=idx>=6?B:W; pc=idx%6; } }
                    if(pc!=NONE) place(p,c,pc,SQ(row,col));
                    col++;
                } else if(line[j]=='|') col++;
            }
        }
        if(col>=8) row++;
        line=strtok(NULL,"\n");
    }
    refresh_hash(p);
}

static int parse_sq(const char*s){ if(!s||strlen(s)<2)return -1; int f=s[0]-'a',r=8-(s[1]-'0'); return (f>=0&&f<8&&r>=0&&r<8)?SQ(r,f):-1; }
static bool apply_move_str(Pos*p, const char*from_s, const char*to_s, const char*pr_s, Undo*u){
    int from=parse_sq(from_s), to=parse_sq(to_s); if(from<0||to<0)return false;
    if(p->piece_at[from]==NONE||p->colour_at[from]!=(int)p->side)return false;
    int pr_pc=Q_; if(pr_s&&pr_s[0]) switch(tolower(pr_s[0])){ case 'n':pr_pc=N_;break; case 'b':pr_pc=B_;break; case 'r':pr_pc=R_;break; }
    int pr_code=(p->piece_at[from]==P_&&((p->side==W&&RANK(to)==0)||(p->side==B&&RANK(to)==7)))?pr_pc:0;
    Move mv[256]; int n=gen_all(p,mv);
    for(int i=0;i<n;i++){
        if(MV_FROM(mv[i])!=(unsigned)from||MV_TO(mv[i])!=(unsigned)to)continue;
        if((int)MV_PROMO(mv[i])!=pr_code&&pr_code)continue;
        if(!is_legal(p,mv[i]))continue;
        make_move(p,mv[i],u); return true;
    }
    return false;
}

static void human_turn(Pos*p){
    Undo u; char f[8],t[8],pr[4];
    while(1){
        printf("Your move (e.g. e2 e4 or e7e8q): "); fflush(stdout);
        if(scanf("%7s %7s",f,t)!=2){while(getchar()!='\n');continue;}
        {int c=getchar(); if(c!='\n'&&c!=EOF){pr[0]=(char)c;pr[1]=0;while(getchar()!='\n');}else pr[0]=0;}
        if(!apply_move_str(p,f,t,pr[0]?pr:NULL,&u)){printf("Illegal.\n");continue;}
        break;
    }
}

static void check_over(const Pos*p){
    Move mv[256]; int n=gen_all(p,mv);
    int lc=0; for(int i=0;i<n;i++) if(is_legal((Pos*)p,mv[i]))lc++;
    if(!lc){ printf("%s\n",in_check(p)?"Checkmate!":"Stalemate."); exit(0); }
    if(p->fifty>=100){ printf("Draw by 50-move rule.\n"); exit(0); }
    if(is_rep(p->hash,3)){ printf("Draw by repetition.\n"); exit(0); }
}

static char g_path[64][8];
static int  g_path_len=0;

static void test_makeundo(Pos*p, int depth){
    if(depth==0) return;
    Move mv[256]; int n=gen_all(p,mv);
    for(int i=0;i<n;i++){
        if(!is_legal(p,mv[i])) continue;
        Pos before=*p;
        Undo u; make_move(p,mv[i],&u);
        snprintf(g_path[g_path_len],8,"%s%s",SQ_NAME[MV_FROM(mv[i])],SQ_NAME[MV_TO(mv[i])]);
        g_path_len++;
        test_makeundo(p,depth-1);
        g_path_len--;
        undo_move(p,mv[i],&u);
        if(memcmp(&before,p,sizeof(Pos))!=0){
            printf("CORRUPT after %s%s at depth %d. Path: ",SQ_NAME[MV_FROM(mv[i])],SQ_NAME[MV_TO(mv[i])],depth);
            for(int k=0;k<g_path_len;k++) printf("%s ",g_path[k]);
            printf("%s\n",g_path[g_path_len]);                           
            printf("BEFORE:\n"); print_pos(&before);
            printf("AFTER (should match BEFORE):\n"); print_pos(p);
            for(int c=0;c<2;c++)for(int pc=0;pc<6;pc++) if(before.bb[c][pc]!=p->bb[c][pc])
                printf("  bb[%d][%d]: %016llx vs %016llx\n",c,pc,(unsigned long long)before.bb[c][pc],(unsigned long long)p->bb[c][pc]);
            for(int c=0;c<2;c++) if(before.occ[c]!=p->occ[c]) printf("  occ[%d]: %016llx vs %016llx\n",c,(unsigned long long)before.occ[c],(unsigned long long)p->occ[c]);
            if(before.all!=p->all) printf("  all: %016llx vs %016llx\n",(unsigned long long)before.all,(unsigned long long)p->all);
            for(int sq_=0;sq_<64;sq_++) if(before.piece_at[sq_]!=p->piece_at[sq_]||before.colour_at[sq_]!=p->colour_at[sq_])
                printf("  sq %s: piece %d/%d vs %d/%d\n",SQ_NAME[sq_],before.piece_at[sq_],before.colour_at[sq_],p->piece_at[sq_],p->colour_at[sq_]);
            if(before.castle!=p->castle) printf("  castle: %d vs %d\n",before.castle,p->castle);
            if(before.ep_sq!=p->ep_sq) printf("  ep_sq: %d vs %d\n",before.ep_sq,p->ep_sq);
            if(before.fifty!=p->fifty) printf("  fifty: %d vs %d\n",before.fifty,p->fifty);
            if(before.side!=p->side) printf("  side: %d vs %d\n",before.side,p->side);
            if(before.hash!=p->hash) printf("  hash: %08x vs %08x\n",before.hash,p->hash);
            exit(1);
        }
    }
}

static long long perft(Pos*p, int depth){
    if(depth==0) return 1;
    Move mv[256]; int n=gen_all(p,mv);
    long long total=0;
    Undo u;
    for(int i=0;i<n;i++){
        if(!is_legal(p,mv[i])) continue;
        make_move(p,mv[i],&u);
        total+=perft(p,depth-1);
        undo_move(p,mv[i],&u);
    }
    return total;
}

int main(int argc, char*argv[]){
    srand((unsigned)time(NULL));
    init_tables(); init_magics(); init_zob(); init_lmr(); tt_init();

    if(argc>1&&!strcmp(argv[1],"-test")){
        Pos p; init_startpos(&p);
        int d=(argc>2)?atoi(argv[2]):4;
        test_makeundo(&p,d);
        printf("OK: make/undo reversible to depth %d\n",d);
        return 0;
    }
    if(argc>1&&!strcmp(argv[1],"-perft")){
        Pos p; init_startpos(&p);
        int d=(argc>2)?atoi(argv[2]):5;
        for(int i=1;i<=d;i++){
            double t0=now_ms();
            long long c=perft(&p,i);
            printf("perft(%d) = %lld  (%.0fms)\n",i,c,now_ms()-t0);
        }
        return 0;
    }
    if(argc>2&&!strcmp(argv[1],"-perftfen")){
        Pos p; load_fen(&p,argv[2]);
        print_pos(&p);
        int d=(argc>3)?atoi(argv[3]):4;
        for(int i=1;i<=d;i++){
            double t0=now_ms();
            long long c=perft(&p,i);
            printf("perft(%d) = %lld  (%.0fms)\n",i,c,now_ms()-t0);
        }
        return 0;
    }

    if(argc>1){
        char*inf=NULL,*outf=NULL,*mf=NULL,*mt=NULL,*mpr=NULL,*fenarg=NULL;
        int diff=3,maxd=64,nu=0,dbg=0,nt=1;
        double soft=5000,hard=5000,rem=0,inc=0;
        for(int i=1;i<argc;i++){
            if(!strcmp(argv[i],"-nu")){nu=1;continue;}
            char*v=strchr(argv[i],'='); if(!v)continue; *v=0; v++;
            if(!strcmp(argv[i],"-i"))    inf=v;
            else if(!strcmp(argv[i],"-o")) outf=v;
            else if(!strcmp(argv[i],"-fen")) fenarg=v;
            else if(!strcmp(argv[i],"-m")){ mf=v;
                for(int j=i+1;j<argc;j++) if(argv[j][0]!='-'){ mt=argv[j]; i=j;
                    if(j+1<argc&&strlen(argv[j+1])==1&&isalpha((unsigned char)argv[j+1][0])){mpr=argv[j+1];i=j+1;} break; }
            }
            else if(!strcmp(argv[i],"-diff"))  diff=atoi(v);
            else if(!strcmp(argv[i],"-depth"))  maxd=atoi(v);
            else if(!strcmp(argv[i],"-t")||!strcmp(argv[i],"-threads")) nt=atoi(v);
            else if(!strcmp(argv[i],"-d"))      dbg=atoi(v);
            else if(!strcmp(argv[i],"-time")){  double t=atof(v)*1e3; soft=t*0.45; hard=t; }
            else if(!strcmp(argv[i],"-remain")) rem=atof(v)*1e3;
            else if(!strcmp(argv[i],"-inc"))    inc=atof(v)*1e3;
        }
        if(rem>0) calc_tc(rem,inc,&soft,&hard);

        if(!outf||(!mf&&!nu)){ fprintf(stderr,"Usage: chess -o=OUT [-i=IN|-fen=FEN] (-m=FROM TO|-nu) [-diff=1-3] [-time=N|-remain=N -inc=N] [-depth=N] [-t=N]\n"); return 1; }

        g_num_threads=(nt>0&&nt<=64)?nt:1;

        Pos pos;
        if(fenarg){
            load_fen(&pos,fenarg);
        } else if(inf){
            FILE*f_=fopen(inf,"r"); if(!f_){fprintf(stderr,"Cannot open %s\n",inf);return 1;}
            char buf[8192]={0}; size_t rdn=fread(buf,1,sizeof(buf)-1,f_); (void)rdn; fclose(f_);
            if(strchr(buf,'/')&&strchr(buf,' ')&&!strstr(buf,"nu_side")) load_fen(&pos,buf);
            else load_board(&pos,buf);
        } else init_startpos(&pos);

        if(dbg){ printf("Position:\n"); print_pos(&pos); }

        if(nu){
            computer_move(&pos,diff,maxd,soft,hard);
        } else {
            Undo u_;
            if(!apply_move_str(&pos,mf,mt,mpr,&u_)){ fprintf(stderr,"Illegal move: %s %s\n",mf,mt?mt:""); return 1; }
            if(dbg){ printf("After player:\n"); print_pos(&pos); }
            computer_move(&pos,diff,maxd,soft,hard);
        }
        if(dbg){ printf("Final:\n"); print_pos(&pos); }
        save_board(&pos,outf);
        return 0;
    }

    Pos pos; init_startpos(&pos); print_pos(&pos);

    { char buf[32]; int c=ncpu();
      printf("Threads (default=%d): ",c);
      if(scanf("%31s",buf)==1){ int t=atoi(buf); g_num_threads=(t>0&&t<=64)?t:c; }
      else g_num_threads=c;
      printf("Using %d thread(s)\n\n",g_num_threads); }

    int diff; { char b[8];
      while(1){ printf("Difficulty (1=Beginner 2=Easy 3=Hard): ");
        if(scanf("%7s",b)==1&&b[0]>='1'&&b[0]<='3'){diff=b[0]-'0';break;} } }

    double soft_ms=5000,hard_ms=8000; int maxd=64;
    if(diff==3){
        char buf[64];
        printf("\n=== Hard mode ===\n");
        printf("Seconds per move (default 5) or 'tc REMAIN INC': ");
        if(scanf("%63[^\n]",buf)==1){
            double rem=0,inc=0;
            if(sscanf(buf,"tc %lf %lf",&rem,&inc)==2) calc_tc(rem*1e3,inc*1e3,&soft_ms,&hard_ms);
            else{ double t=atof(buf); if(t>0){ soft_ms=t*0.45*1e3; hard_ms=t*1e3; } }
        }
        printf("Max depth (0=unlimited): ");
        if(scanf("%63s",buf)==1){ int d=atoi(buf); if(d>0) maxd=d; }
        printf("Soft %.1fs | Hard %.1fs | Depth %d\n\n",soft_ms/1e3,hard_ms/1e3,maxd);
    }

    printf("You play White. Good luck.\n\n");
    while(1){
        if(pos.side==W) human_turn(&pos);
        else computer_move(&pos,diff,maxd,soft_ms,hard_ms);
        print_pos(&pos);
        g_game_hist[g_game_hist_len++]=pos.hash;
        check_over(&pos);
    }
    return 0;
}
