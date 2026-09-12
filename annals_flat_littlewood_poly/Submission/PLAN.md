# PLAN: Flat Littlewood Polynomials exist  (arXiv:1907.09464v1 = BBMST, Annals 192 (2020) 977-1004)

GOAL (Challenge theorem_1_1 in `namespace Submission`): exists Δ>δ>0 such that every n≥2 has a
Littlewood poly of degree n with δ√n ≤ |P(z)| ≤ Δ√n on |z|=1. ALL constants are ours to choose
(astronomical slack; never tune tightly).

## LEAN CONVENTIONS / TRAPS (IMPORTANT, learned the hard way)
- Finset sum syntax in THIS mathlib revision: `∑ x ∈ s, f x` (NOT `∑ x in s, f x`).
- Field notation `P.eval z` / `P.natDegree` fails unless `open Polynomial` + `open scoped Polynomial`
  are active at file top; if elaborating variables use `Polynomial.eval z P`, `Polynomial.derivative P`.
- `Real.le_sqrt hx hy : x ≤ √y ↔ x^2 ≤ y` (IFF; use `.mpr` to go from squares to roots).
- `Polynomial.coeff_X_pow_mul p n d : (X^n*p).coeff (d+n) = p.coeff d` (mind `d+n` orientation:
  rewrite `Nat.add_comm` when the index is `n + j`).
- namespace resolution: from `namespace Submission.X`, sibling `Submission.Y` is reachable as `Y.foo`.
- child fleet agents (prove_lemma) are VERY capable: they prove hard theorems incl. Bernstein and
  the Lovett--Meka partial-colouring lemma; give one lemma per file (a file already claimed by one
  child can't host another); children also clear any other sorries in their file.
- `lake build Submission.X` builds module X (+deps); needed before `import Submission.X` works.
- max-modulus principle in `Mathlib/Analysis/Complex/AbsMax.lean`; Cauchy integrals in
  `Mathlib/Analysis/Complex/CauchyIntegral.lean`.

## DONE & VERIFIED (all import via Submission/Agg.lean)
namespace Submission.RudinShapiro:
- RS.lean: `P t`,`Q t` : ℂ[X] (Rudin-Shapiro pair; P_0=Q_0=1, P_{t+1}=P_t+X^(2^t) Q_t,
  Q_{t+1}=P_t-X^(2^t) Q_t). `P_Q_bounds t`: natDegree(P t)≤2^t−1, natDegree(Q t)≤2^t−1,
  coefficients ±1 for i<2^t (P,Q). Accessors: `P_natDegree_le`, `Q_natDegree_le`, `P_coeff_mem`,
  `Q_coeff_mem`; `coeff_P_extend`/`coeff_Q_extend` (prefix rules), `coeff_P_top`/`coeff_Q_top`
  (top half rules: coeff_P_top t j : (P(t+1)).coeff(2^t+j) = (Q t).coeff j),
  `coeff_P_ge`/`coeff_Q_ge` (vanish ≥ 2^t).
  `normSq_eval_add t z hz : normSq((P t).eval z)+normSq((Q t).eval z) = 2^(t+1)` (‖z‖=1),
  `norm_P_eval_le` / `norm_Q_eval_le`: ‖(P t).eval z‖ ≤ Real.sqrt(2^(t+1)).
  helpers `pow_two_succ t : 2^(t+1) = 2*2^t` (ℕ), `two_pow_pos`, `two_pow_ge_one`, `normSq_add_sub`,
  `normSq_mul_pow`.
- RSPsum_defs.lean: `Psum t m`, `Qsum t m` : ℂ[X] = first m monomials of P t / Q t; eval lemmas.
- F_Psum_small/Qsum_small/Psum_large/Qsum_large/Psum_ge/Qsum_ge/Psum_stable (PROVED):
  Psum(t+1)m = Psum t m for m≤2^t; Qsum(t+1)m = Psum t m for m≤2^t;
  Psum(t+1)(2^t+m) = P t + X^(2^t)·Qsum t m; Qsum_large: minus; Psum_ge: Psum t m = P t for m≥2^t
  (Qsum_ge: = Q t); Psum_stable {t s m} (hm : m≤2^t) (hts : t≤s) : Psum s m = Psum t m.
- F_bound_level: `Psum_bound_level t m hm z hz : ‖(Psum t m).eval z‖ ≤ 4*sqrt(2^t) ∧ same Q`.
- F_norm_Psum: `norm_Psum_eval_le`, `norm_Qsum_eval_le`: for m≤2^t, |z|=1:
  ‖(Psum t m).eval z‖ ≤ 6*sqrt m.   (SHAPIRO partial-sum bound.)
- F_bernstein: `bernstein_poly P n hdeg M hM z hz : ‖Polynomial.eval z (Polynomial.derivative P)‖ ≤ (n:ℝ)*M`
  where hdeg: natDegree P ≤ n, hM: ∀w, ‖w‖=1 → ‖Polynomial.eval w P‖ ≤ M, hz: ‖z‖=1.
namespace Submission.Discrepancy (DiscrepancyDefs.lean + F_pcoloring.lean + F_cor42.lean):
- defs `dot`, `eucl` (sqrt Σ squares), `supAbs` (sSup |coord|); lemmas eucl_sq, eucl_nonneg,
  dot_comm, dot_add_sub. (children added more helpers, e.g. F_pcoloring has `toV` etc.)
- F_pcoloring: `partial_coloring n m v x0 hx0 c hc hsum : ∃ x, x∈[-1,1]^n ∧
  |dot (fun i => x i - x0 i) (v j)| ≤ c j * eucl (v j) ∀j ∧
  ((n+1)/2 ≤ Fintype.card {i // x i = -1 ∨ x i = 1})`
  given `hsum : ∑ j, Real.exp (-(c j)^2/16) ≤ n/16`.  [= Theorem 4.1, Lovett-Meka]
- F_cor42: `cor42 h41 n m v x0 hx0 c hc hsum : ∃ x, (∀i, x i = -1 ∨ x i = 1) ∧
  ∀j, |dot (fun i => x i - x0 i) (v j)| ≤ (c j + 30)*Real.sqrt n * supAbs (v j)`
  given h41 (partial-coloring as a hypothesis for all sizes) and
  `hsum : ∑ j, Real.exp (-(c j)^2/196) ≤ n/16`.   [= Corollary 4.2; NOTE: divisor is 196 = 14²,
  the paper's printed "142" is a typo/OCR; 196 makes b_j:=2c_j/7 satisfy b_j²/16 = c_j²/196]
namespace Submission.Sec3 (Sec3Defs.lean):
- `eθ θ := Complex.exp ((θ:ℂ)*Complex.I)`, `norm_eθ`; `zθ θ := eθ (2*θ)`, `norm_zθ`.
- `cval t θ := z^T P_t(z) + z^{2T} Q_t(z)` (z = zθ θ, T = 2^(t+10)); `c t θ := (cval t θ).re`.
- `seval s t n θ := Psum s (n+1) at z − z^T P_t(z) − z^{2T} P_t(z)`; `s_e s t n θ := im`.
- PROVED: `abs_c_le t θ : |c t θ| ≤ 2*sqrt(2^(t+1))`; `abs_s_e_le s t n hs θ :
  |s_e s t n θ| ≤ 6*sqrt(n+1) + 2*sqrt(2^(t+1))` (hs : n+1 ≤ 2^s).

## REMAINING WORK (mirror the paper; constants free, keep loose)
A. Def: odd positions & the final Laurent/ordinary polynomial assembly (paper Thm 2.1 & the
   reduction to all n ≥ 2). Structure: for a "special large N" (multiple of 4 etc.) produce a
   Littlewood poly of degree N flat; pad other degrees by adding ≤ 3 monomials ±z^k (|P| changes
   additively by ≤ 3), then choose final Δ,δ to cover both regimes.
B. Section 3 analysis (Theorem 2.3): with η, partition into intervals, show bad set of c is a
   union of ≤ 4γn "suitable & well-separated" arcs: each |I| ≤ 6π/n, pairwise distance ≥ π/n,
   endpoints in (π/n)ℤ, symmetric under θ↦π±θ, away from (π/2)ℤ+[-100π/n,100π/n]; and |c| ≥ δ√n
   off ∪I.  Needs: H(x)=e^{ix}α(x)+e^{2ix}β(x) with α(x)=2^-(t+1)/2·P_t(e^{ix/T}),
   β(x)=2^-(t+1)/2·Q_t(e^{ix/T}), T=2^(t+10) — derivative estimates via bernstein_poly
   (Lemmas 3.6, 3.7: |α^(k)| ≤ small, |H^(k)| ≤ 2^k+2, value/interp lemmas 3.4, 3.5 via Lagrange
   interpolation bound Theorem 3.8: for k+1-times differentiable real f on interval, k-th
   derivative at a point vs values at k+1 points y_i within length-ℓ interval:
   |f^(k)(x) − (interp)| ≤ (ℓ^{k+1}/(k+1)!)·sup|f^(k+1)| — a child can derive via iterated
   mean value theorem; needs Mathlib calculus `iteratedDeriv`/`deriv` on ℝ), then Lemmas 3.8-3.9
   (H big near 0 and Tπ) and Theorem 2.3's interval construction.
C. Section 5 (Theorem 2.4): define for a suitable well-separated family I of arcs (interface!),
   the colouring α : I → {±1} (Lemma 5.3 via cor42), ε̂_j integrals (Lemma 5.6 estimates:
   Claims 1-3, Lemmas 5.8-5.9: sine-integral bounds via substitution x=2n(θ-θ0),
   monotone-integration Lemma 5.9: |∫_a^b h(θ) sin(2nθ)dθ| ≤ |h(b)-h(a)|/n for monotone h and
   (b-a)∈(π/n)ℤ), then Lemma 5.4/5.5 (colouring ε via cor42 again, Taylor expansion in ℓ-th
   derivatives at θ_k grid, M=16n sample points, |s_o - ŝ| ≤ 72√n), Theorem 2.4 assembly
   (|s_o| ≥ (2K/3−72)√n on ∪I and ≤ (5K+72)√n everywhere; K=2^7 as paper or larger).
D. Interface design for interval families (do first): a family I : Finset (of arcs given by
   start/end reals with endpoints in (π/n)ℤ etc.), the maps θ↦π±θ symmetry, distances.
   Simplest faithful approach: work on the fundamental domain [0, π/2] ∪ symmetries, or define
   everything as properties of finite sets of closed intervals [a,b] ⊆ ℝ and state all bounds
   "for all θ ∈ ℝ" with periodicity of cos(kθ)/sin(kθ) handled by interval-length arguments.
   A cleaner route: replace the abstract suitable/well-separated family by the CONCRETE output
   of Theorem 2.3 and prove Theorem 2.4 directly for that concrete family.  (RECOMMENDED:
   develop both theorems together against one concrete interval object.)
E. Littlewood-ness & support bookkeeping for the final P: c's even coefficients on C = 2C'
   (C' = {T..T+2^t−1} ∪ {2T..2T+2^t−1}), s_e on evens [2n]\C, s_o on odds So={1,3,...,2n−1},
   coefficient facts via RudinShapiro prefix rules; each coefficient ±1; natDegree = 4n after
   shift by z^{2n}; convert Laurent bound to poly bound on |z|=1 (z^{-2n} has |z|=1).

## next_session suggestions (in priority order)
1. Read this PLAN.md and the paper Section 2-6 (arXiv:1907.09464v1, pdf also on disk /tmp/bbmst.txt).
2. Define the concrete interval-family interface + Theorem 2.3's object (bad intervals of c) and
   Theorem 2.4 over it; delegate Lemma 3.4-3.9 / Theorem 2.3 / Section 5 Lemmas 5.3-5.6 to children
   with precise statements (children proved partial_coloring + cor42 + Bernstein successfully).
3. Meanwhile write the Main-assembly module structure and its reduction lemmas (padding, Δ/δ choice,
   Laurent shift, Littlewood/natDegree bookkeeping).
4. Verify: keep `lake build Submission` green (Submission.lean's theorem_1_1 has sorry until the end).
