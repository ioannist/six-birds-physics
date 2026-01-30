# Claim Index

## (No section)

## Introduction
- remark rem:tk-interoperability (lines 71-103): [Interoperability of certificates (toolkit safety)]\label{rem:tk-interoperability} This manuscript uses three logically 

### The organizing picture: a three-certificate loop

## Related work

## Conventions and notation

### Finite state spaces, distributions, and kernels

### Paths, time reversal, and relative entropy
- remark (no label) (lines 233-237): [Stationarity is not needed for $\Sigma_T$ or data processing] The definition in Section~\ref{sec:aot} makes sense for a

### Coarse-graining lenses
- remark (no label) (lines 245-251): WLOG, we replace $X$ by the image $f(Z)$ so that $f$ is surjective and every fiber $B_x=f^{-1}(x)$ is nonempty. This doe

### A unified theory package viewpoint
- remark (no label) (lines 255-259): [Emergence and open-endedness (terminology)] Throughout, \emph{emergence} means the appearance of stable fixed points of
- definition def:tk-theory-package (lines 262-281): [Finite theory package]\label{def:tk-theory-package} Assume \textbf{A\_FIN}. A \emph{finite theory package} is a tuple \
- remark (no label) (lines 283-286): We use the symbol $\Sigma$ in two unrelated roles: $\Sigma_f$ denotes the definability $\sigma$-algebra induced by a len
- remark rem:tk-theory-instantiations (lines 288-295): [Instantiations in this manuscript]\label{rem:tk-theory-instantiations} The components of $\mathcal T$ appear throughout

### A minimal instantiation recipe

### Support graphs and discrete 1-forms

### Assumption bundles

## Order-closure and closure ladders

### Order-theoretic closure and fixed points
- definition def:closure-operator (lines 358-365): [Closure operator]\label{def:closure-operator} Let $(L,\le)$ be a poset. A map $c:L\to L$ is a \emph{closure operator} i
- definition def:closed-points (lines 370-376): [Closed points / objects]\label{def:closed-points} Given a closure operator $c:L\to L$, its \emph{closed points} (or \em
- lemma lem:closed-antitone (lines 382-385): [Closed points are antitone in closure strength]\label{lem:closed-antitone} If $c \le d$ are closure operators on $L$, t

### Closure ladders and saturation
- lemma lem:closure-iterate-stabilizes (lines 397-403): [One-step stabilization under iteration]\label{lem:closure-iterate-stabilizes} Let $c$ be a closure operator on $L$. Def
- corollary cor:closure-saturates (lines 410-414): [Closure saturates]\label{cor:closure-saturates} Fix a closure operator $c$. For any $x\in L$, the sequence $x,\; c(x),\
- remark (no label) (lines 416-420): Viewed abstractly, a closure operator acts like a completion rule.\\ Iterating a fixed completion rule stabilizes. Thus 
- definition def:strictly-stronger (lines 425-428): [Strictly stronger closure]\label{def:strictly-stronger} For closure operators $c,d$ on $L$, write $c \prec d$ (``$d$ is
- definition def:closure-ladder (lines 430-437): [Closure ladder]\label{def:closure-ladder} A \emph{closure ladder} is a sequence of closure operators $(c_n)_{n\in\mathb
- remark (no label) (lines 439-446): The strictness relation $\prec$ is irreflexive and transitive on closure operators (by the pointwise order), and Lemma~\
- remark rem:lean-closure (lines 448-456): [Lean formalization note]\label{rem:lean-closure} The order-theoretic closure operator used here is formalized in the re

## Idempotent endomaps and induced closures

### Idempotent endomaps
- definition (no label) (lines 469-472): [Idempotent endomap] Let $A$ be a set (or type). An \emph{idempotent endomap} on $A$ is a function $e : A \to A$ such th
- definition (no label) (lines 474-480): [Fixed points] For an endomap $e : A \to A$ define its fixed-point set \[ \mathrm{Fix}(e) := \{a\in A : e(a)=a\}. \] We 
- lemma (no label) (lines 482-489): [Idempotents split] Let $e : A \to A$ be an idempotent endomap. Let $i:\mathrm{Fix}(e)\hookrightarrow A$ denote inclusio
- remark (no label) (lines 498-508): [Order-closures as a special case] If $L$ is a poset and $c:L\to L$ is an order-closure (extensive, monotone, idempotent
- remark (no label) (lines 510-521): [Formalization note] The constructions in this subsection are formalized in Lean: \begin{itemize} \item \texttt{formal/C

### Dynamics-induced empirical endomaps
- definition def:D-IC-01 (lines 532-553): [Coarse map and canonical lift; \textbf{D-IC-01}] \label{def:D-IC-01} Let $Q_f:\Delta(Z)\to \Delta(X)$ be the pushforwar
- remark (no label) (lines 559-565): [Not an order-closure] The map $E_{\tau,f}$ is an affine endomap of $\Delta(Z)$ (indeed a Markov kernel on $Z$), and it 
- definition def:D-IC-02 (lines 567-587): [TV idempotence defect; \textbf{D-IC-02}] \label{def:D-IC-02} Let $\|\cdot\|_{\mathrm{TV}}$ denote total variation on $\
- definition (no label) (lines 589-598): [Prototype stability at scale $\tau$] For each $x\in X$ define the (scale-$\tau$) stability of the prototype $u_x$ by \[
- theorem thm:T-IC-02 (lines 600-616): [Approximate idempotence from retention] \label{thm:T-IC-02} \textbf{T-IC-02.}\par Assume \textbf{A\_FIN}+\textbf{A\_LEN
- theorem thm:T-IC-01 (lines 658-677): [Refinement can help or hurt] \label{thm:T-IC-01} \textbf{T-IC-01.}\par Assume \textbf{A\_FIN}+\textbf{A\_LENS}. There e
- remark (no label) (lines 698-706): [Qualified ``theory birth''] The induced endomap $E_{\tau,f}$ packages a distribution by evolving for $\tau$ steps and t

## AUT + REV + ACC regime and graph 1-forms

### Bidirected support and the log-ratio 1-form
- definition def:edge-one-form (lines 732-740): [Edge log-ratio 1-form] \label{def:edge-one-form} Assume \textbf{A\_FIN}+\textbf{A\_REV}. The \emph{antisymmetric edge 1
- remark (no label) (lines 745-749): [Why \textbf{A\_REV} matters] If \textbf{A\_REV} fails, then ratios such as $P_{ij}/P_{ji}$ may be undefined, and many t

### Cycle integrals, exactness, and the null regime
- definition def:cycle-integral (lines 756-763): [Cycle integral / affinity along a cycle] \label{def:cycle-integral} Given an antisymmetric edge 1-form $a$ and an orien
- definition def:exact-one-form (lines 765-773): [Exact 1-forms] \label{def:exact-one-form} An antisymmetric 1-form $a$ on $\vec E$ is \emph{exact} if there exists a pot
- lemma lem:exact-zero-cycles (lines 775-780): [Exact forms have zero cycle integrals] \label{lem:exact-zero-cycles} \mbox{}\par Assume \textbf{A\_FIN}+\textbf{A\_REV}
- theorem thm:cycle-criterion-exact (lines 790-800): [Cycle criterion for exactness] \label{thm:cycle-criterion-exact} Assume \textbf{A\_FIN}+\textbf{A\_REV} and let $a$ be 
- corollary cor:null-regime (lines 816-826): [Null regime as ``no-drive'' / detailed-balance-like] \label{cor:null-regime} Assume \textbf{A\_FIN}+\textbf{A\_REV}+\te

### Accounting as coordinates on cycle space
- remark (no label) (lines 844-848): [Implementation note for Appendix C] The repository includes a small graph-theoretic routine that computes cycle affinit

## Arrow-of-time as path reversal asymmetry; data processing; protocol trap
- definition (no label) (lines 856-869): [Forward path law and reversal (D-AOT-01)] Fix a horizon $T\in \mathbb N$ with $T\ge 1$ and an initial distribution $\rh
- remark (no label) (lines 873-876): [Stationarity is not required (L-AOT-STAT-01)] The quantity $\Sigma_T(\rho)$ is defined for any initial distribution $\r
- definition (no label) (lines 878-882): [Steady-state entropy production (D-AOT-EP-01)] Assume additionally \textbf{A\_STAT} and let $\pi$ be a stationary distr

### Data processing: coarse-graining cannot create asymmetry
- theorem thm:dpi_path (lines 895-903): [Data processing for path reversal asymmetry (T-AOT-01)]\label{thm:dpi_path} Under \textbf{A\_FIN}+\textbf{A\_LENS}, for
- corollary (no label) (lines 916-921): [No false positives] Assume \textbf{A\_FIN}+\textbf{A\_LENS}. If the lifted system has zero asymmetry at horizon $T$, th

### Protocol trap: apparent stroboscopic arrows and the ``clock audit''
- definition (no label) (lines 935-944): [Autonomous $m$-phase protocol] \textbf{D-PROT-02.}\par Fix $\alpha\in[0,1]$ and define an autonomous Markov chain on th
- theorem thm:protocol_trap (lines 946-957): [Protocol trap / hidden-drive principle (T-AOT-02)]\label{thm:protocol_trap} Assume \textbf{A\_FIN}+\textbf{A\_AUT}. Sup
- corollary (no label) (lines 973-978): [``P3 needs P6\_drive'' under autonomy (C-ACC-01)] Under \textbf{A\_FIN}+\textbf{A\_REV}+\textbf{A\_AUT}+\textbf{A\_ACC}
- remark (no label) (lines 980-984): [What the ``protocol trap'' actually warns about] The theorem above is about \emph{true} path reversal asymmetry. In pra

## Generic extension and the finite forcing lemma

### Theories as partitions and definability
- definition (no label) (lines 998-1005): [Predicates and definability] A (Boolean) \emph{predicate} is a function $h:Z\to\{0,1\}$. We say that $h$ is \emph{defin
- remark (no label) (lines 1010-1014): In a fixed finite $Z$ there is a hard cap on how many strict refinements are possible; open-endedness is modeled by repe

### Counting lemma: definable predicates are rare
- lemma lem:count-definable (lines 1026-1033): [Counting definable predicates]\label{lem:count-definable} Assume \textbf{A\_FIN}+\textbf{A\_LENS}. The number of predic

### Finite forcing: generic extensions are non-definable
- theorem thm:finite-forcing (lines 1046-1053): [Finite forcing lemma / physical forcing lemma]\label{thm:finite-forcing} Assume \textbf{A\_FIN}+\textbf{A\_LENS}. Let $
- lemma (no label) (lines 1060-1074): Assume \textbf{A\_FIN}+\textbf{A\_LENS} and let $f:Z\to X$ have blocks $\Pi_f=\{B_x\}_{x\in X}$. For each block $B_x$, \
- corollary cor:strict-language-extension (lines 1081-1086): [Generic extension is strict]\label{cor:strict-language-extension} \mbox{}\par Assume \textbf{A\_FIN}+\textbf{A\_LENS}. 
- remark (no label) (lines 1093-1097): [Why this is the anti-saturation move] Closure (or packaging) at a fixed theory saturates by idempotence: repeated closu

## Why the primitives are unavoidable
- definition def:meta-proc (lines 1103-1106): [Process soup (D-META-PROC-01)]\label{def:meta-proc} A \emph{process soup} is a set $\mathcal P$ equipped with a partial
- definition def:meta-lens (lines 1108-1112): [Interface lens (D-META-LENS-01)]\label{def:meta-lens} An \emph{interface lens} is a map $f:\mathcal P\to X$ to a set of
- definition def:meta-ref (lines 1114-1120): [Refinement family (D-META-REF-01)]\label{def:meta-ref} A refinement family is a chain of equivalence relations $(\sim_j
- definition def:meta-bnd (lines 1122-1126): [Bounded interface (D-META-BND-01)]\label{def:meta-bnd} There exists $C_0\ge 1$ such that the quotient index satisfies $
- theorem thm:meta-prim (lines 1129-1148): [Self-generated primitives]\label{thm:meta-prim} Assume D-META-PROC-01, D-META-LENS-01, D-META-REF-01, and D-META-BND-01

## Primitives P1--P6 as closure-changing operations

### Definitions of P1--P6
- definition (no label) (lines 1174-1178): [P1: operator rewrite] P1 is a rewrite of the substrate operator: replace a Markov kernel $P$ by a new kernel $P'$ (or a
- definition (no label) (lines 1180-1184): [P2: gating / constraints] P2 restricts the support graph by deleting edges (setting selected $P_{ij}=0$) and renormaliz
- definition (no label) (lines 1186-1192): [P3: autonomous protocol holonomy] P3 is modeled in the autonomous lifted form on $Z:=X\times\Phi$. The phase $\phi\in\P
- definition (no label) (lines 1194-1198): [P4: sectors / invariants] P4 is a conserved sector label: the support decomposes into disconnected components (block st
- definition (no label) (lines 1200-1204): [P5: packaging] P5 is an idempotent endomap $e$ whose fixed points $\mathrm{Fix}(e)$ are the packaged objects of a given
- definition (no label) (lines 1206-1216): [P6: accounting / audit] P6 is an accounting/audit structure: a certificate or functional that is monotone under coarse 
- remark (no label) (lines 1218-1222): We write \emph{P6\_drive} for the ACC specialization: a non-exact log-ratio 1-form (equivalently, a nonzero cycle integr

### How the primitives compose to generate theory growth

### Downward influence across theories

### Two load-bearing propositions
- theorem (no label) (lines 1294-1306): [P2 gating shrinks cycle space] \textbf{T-P2-01.}\par Assume \textbf{A\_FIN}+\textbf{A\_REV}.\par Let $G=(V,E)$ be an un
- theorem (no label) (lines 1313-1317): [P1 can change cycle rank and spectral gap (T-P1-01)] Assume \textbf{A\_FIN}+\textbf{A\_REV}. P1 rewrites can increase o
- remark (no label) (lines 1329-1332): [Evidence pointers] Appendix~C records finite graph and kernel witnesses for the P1 and P2 behaviors described above, in

## Examples

### A biased three-cycle: a non-exact graph 1-form

### Protocol trap: external schedule vs autonomous lifted model

### Finite forcing count: definability is exponentially rare

## Discussion and scope boundary

### What the theory does and does not claim

### Outlook: forthcoming instantiations

## Appendix A: Reproducibility checklist

### A.1 Repository integrity checks (from repo root)

### A.2 Python evidence harness (deterministic tests)

### A.3 Notes on tool availability

## Appendix B: Lean formalization map

### B.1 What is mechanized

### B.2 File map and key declarations

### B.3 How to build

## Appendix C: Python evidence map

### C.1 How to run

### C.2 Evidence by theme (tests and scripts)

## Appendix D: Zeno cascades and depth

### Setup: frontier and Zeno criterion

### Bridges, ports, and accounting

### Storage-based activity and the WORK quantum (Option B)
- lemma lem:work-quantum (lines 1696-1703): [WORK from storage growth]\label{lem:work-quantum} Assume that the passive-storage inequality \eqref{eq:passive-storage}

### Integrated throughput (ICAP) and feasibility \texorpdfstring{$\Rightarrow$
- lemma lem:latency-lb (lines 1733-1743): [Latency lower bound from WORK+ICAP+FEAS]\label{lem:latency-lb} If Lemma~\ref{lem:work-quantum} holds at boundary $j$, \
- remark (no label) (lines 1754-1756): [When the alignment hypothesis holds] Condition \eqref{eq:align} is automatic for memoryless bridges and holds for memor

### No-Zeno criterion via divergence
- theorem thm:no-zeno (lines 1762-1769): [No-Zeno from divergent reciprocal capacity]\label{thm:no-zeno} Assume that for all sufficiently large $j$, Lemma~\ref{l

### Hard lemma slots (WORK/CAP/route)

### Checkable divergence criteria

### Toy model families (necessity witnesses)

### Decision tree (settlement frontier)

## Appendix E: Toolkit theory---defects

### Defects as quantitative relaxations of exact laws
- remark rem:tk-extreme-points (lines 1877-1884): [Extreme points attain the TV idempotence defect]\label{rem:tk-extreme-points} Because $\mu\mapsto \|\mu(E^2-E)\|_{\math

### Route dependence, capacity, and a one-step control inequality
- lemma lem:tk-route-capacity (lines 1922-1940): [Route mismatch controls gain growth]\label{lem:tk-route-capacity} In the default linear-operator setting above, the two
- remark rem:tk-holonomy-no-teleology (lines 1959-1965): [Holonomy without teleology]\label{rem:tk-holonomy-no-teleology} The purpose of $\mathrm{RM}(j)$ is to quantify \emph{ro

### Bridge objects: ports, passivity, and integrated throughput
- definition def:tk-bridge-ports (lines 1975-1992): [Ports, causal bridge, and accounting]\label{def:tk-bridge-ports} A \emph{port space} is a finite-dimensional real Hilbe
- definition def:tk-passive-storage (lines 1994-2003): [Passivity with storage]\label{def:tk-passive-storage} A causal bridge $\mathsf Z:\mathcal U\to\mathcal U$ is \emph{pass
- definition def:tk-icap (lines 2005-2015): [Integrated capacity inequality (ICAP)]\label{def:tk-icap} A causal bridge $\mathsf Z:\mathcal U\to\mathcal U$ satisfies
- remark (no label) (lines 2017-2020): The incremental (activated) form above avoids prehistory contamination in memory systems; a full-output per-subinterval 
- lemma lem:tk-causal-compose (lines 2022-2026): [Causality is closed under composition]\label{lem:tk-causal-compose} Assume the setup of Definition~\ref{def:tk-bridge-p
- lemma lem:tk-parallel-add (lines 2033-2043): [Parallel sum: passivity and ICAP constants add]\label{lem:tk-parallel-add} Assume the setup of Definition~\ref{def:tk-b
- remark rem:tk-serial-note (lines 2056-2064): [Serial composition: gain submultiplicativity is model-free; passivity needs port-compatibility]\label{rem:tk-serial-not
- remark rem:tk-bridge-to-primitives (lines 2066-2073): [Relation to primitives P5 and P6]\label{rem:tk-bridge-to-primitives} In the main text, \textbf{P5} (packaging) is expre

### Emergent coercivity template via sector compression

### Summary: slots and divergence consequence
- theorem thm:ect-summary (lines 2079-2108): [ECT summary: linear ICAP capacity and DIV from three slots]\label{thm:ect-summary} Fix a depth-indexed family of packag
- remark rem:ect-nonimplication (lines 2115-2125): [Non-implication: why ECT is an add-on, not automatic]\label{rem:ect-nonimplication} The ECT conclusion is \emph{not} a 
- definition def:ect-atom (lines 2129-2139): [Atomic/sector decompositions of a packaged bridge {\normalfont\textsf{(ID: D-ECT-ATOM-01)}}]\label{def:ect-atom} Fix a 

### Dissipative atoms and semigroup decay
- definition def:ect-atom-ss (lines 2142-2154): [Dissipative atom representation {\normalfont\textsf{(ID: D-ECT-ATOM-SS-01)}}]\label{def:ect-atom-ss} Let $\mathsf Z_r$ 
- definition def:ect-bal (lines 2156-2164): [Balanced coupling {\normalfont\textsf{(ID: D-ECT-BAL-01)}}]\label{def:ect-bal} \mbox{}\par In the setting of Definition
- definition def:ect-cap (lines 2166-2179): [ICAP capacity functional {\normalfont\textsf{(ID: D-ECT-CAP-01)}}]\label{def:ect-cap} For a causal bridge $\mathsf Z:\m
- lemma lem:ect-bal-kmass (lines 2181-2188): [Balanced decay implies a uniform kernel-mass bound {\normalfont\textsf{(ID: L-ECT-BAL-KMASS-01)}}]\label{lem:ect-bal-km
- lemma lem:ect-fmem (lines 2205-2218): [Finite kernel-mass convolution bridges satisfy ICAP for truncated inputs {\normalfont\textsf{(ID: L-ECT-FMEM-01)}}]\lab
- corollary cor:ect-bal-icap (lines 2236-2244): [Balanced atoms have uniform ICAP]\label{cor:ect-bal-icap} \mbox{}\par \textbf{C-ECT-BAL-ICAP-01.}\par Assume $\mathsf Z
- remark rem:ect-p5-fmem (lines 2254-2259): [Finite-memory bridges as a P5 packaging target]\label{rem:ect-p5-fmem} Lemma~\ref{lem:ect-fmem} provides a concrete suf
- lemma lem:ect-mech (lines 2261-2278): [Mechanical ECT: sector ICAP + mode count $\Rightarrow$ linear capacity {\normalfont\textsf{(ID: L-ECT-MECH-01)}}]\label
- remark rem:ect-div (lines 2287-2300): [DIV-ready chain]\label{rem:ect-div} Fix a depth $j$ and interval $[t_j,t_{j+1}]$ with input $u_j$ and output $y_j=\math
- remark rem:ect-route (lines 2302-2308): [Route mismatch as an additive gain error]\label{rem:ect-route} In the default linear-operator specialization of Appendi

### Coercivity from feasibility gating (P2)
- definition def:ect-gate (lines 2313-2329): [Feasibility gate and induced coercive norm {\normalfont\textsf{(ID: D-ECT-GATE-01)}}]\label{def:ect-gate} Fix a finite 
- lemma lem:ect-coer-feas (lines 2331-2341): [Coercivity on the feasible set {\normalfont\textsf{(ID: L-ECT-COER-01)}}]\label{lem:ect-coer-feas} Let $\mathsf Z_j:\ma
- remark rem:hl-p2-core (lines 2346-2352): [Hard slot HL-P2-CORE (P2 must eliminate lossless feasible directions)]\label{rem:hl-p2-core} \emph{Slot (HL-P2-CORE).} 
- lemma lem:ect-shrink (lines 2354-2367): [Feasibility shrinkage $\Rightarrow$ depth-scaled coercivity {\normalfont\textsf{(ID: L-ECT-SHRINK-01)}}]\label{lem:ect-
- remark rem:ect-shrink-examples (lines 2372-2376): [Examples of depth scaling]\label{rem:ect-shrink-examples} If $a_j \gtrsim (j+1)$, then $c_j=a_j^2 \gtrsim (j+1)^2$. If 

### Mode compression from sectorization (P4) and minimality (P5)
- definition def:ect-sectorization (lines 2381-2391): [Sectorization of the port space {\normalfont\textsf{(ID: D-ECT-SECT-01)}}]\label{def:ect-sectorization} Fix a depth $j$
- definition def:ect-p5min (lines 2393-2403): [Sector-respecting minimal decompositions (P5-min) {\normalfont\textsf{(ID: D-ECT-P5MIN-01)}}]\label{def:ect-p5min} Assu
- lemma lem:ect-mode-ub (lines 2405-2413): [Sectorization bounds the minimal mode count {\normalfont\textsf{(ID: L-ECT-MODE-UB-01)}}]\label{lem:ect-mode-ub} Assume
- definition def:ect-p4-idx (lines 2423-2432): [Quantized index hypothesis {\normalfont\textsf{(ID: D-ECT-P4IDX-01)}}]\label{def:ect-p4-idx} \mbox{}\par Fix depth $j$ 
- lemma lem:ect-qsize (lines 2434-2439): [Quantized index implies linear sector count {\normalfont\textsf{(ID: L-ECT-QSIZE-01)}}]\label{lem:ect-qsize} Under the 
- corollary cor:ect-hl1 (lines 2444-2452): [Linear mode bound from P4 index {\normalfont\textsf{(ID: C-ECT-HL1-01)}}]\label{cor:ect-hl1} \mbox{}\par Assume a secto
- remark rem:ect-slots (lines 2458-2463): [Hard lemma slots behind coercivity emergence]\label{rem:ect-slots} Lemma~\ref{lem:ect-mech} is purely algebraic. In app

### Defect propagation rules (toolkit)
