import Submission.Contracts
import Submission.SqueezeMink
import Submission.GcdInt
import Submission.NocommonGeneral
import Submission.Nocommon
import Submission.AdjustLemma
import Submission.RemezComplex
import Submission.Cwnorm
import Submission.RootData
import Submission.EnergyHalf
import Submission.MinkBox
import Submission.MinkLower
import Submission.WnormToolkit
import Submission.Contract1Core
import Submission.ArithmeticAssembly
import Submission.HjBound
import Submission.ExtendFamily
import Submission.SlackAbsorb
import Submission.ModTwoIndep
import Mathlib.Tactic

/-!
# Smith `lem:second_squeeze` (GON.tex) at the Serre data

This is the last major ingredient for Theorem squarefree (contract 1).  It
combines Theorem adjust (now `Submission.AdjustLemma.adjust_lemma`), the
squarefree linear-combination lemma (`Submission.GcdInt.gcd_int_quotient` +
`Submission.NocommonGeneral.nocommon_general`), the squeeze lemma
(`Submission.SqueezeMink.squeeze`), the complex Remez division
(`Submission.RemezComplex.complex_remez`), and elementary 𝔽₂-independence.

## Statement (paper lem:second_squeeze specialised, `k ≥ 1`)

There is `C > 0` (absolute, depending only on the Serre data) such that for
all naturals `1 ≤ k ≤ m ≤ n`, `n ≥ 2` and every family
`Q : Fin (m+1) → Polynomial ℤ` which is
  (i) ℚ-linearly independent as POLYNOMIALS in ℚ[X] (`FullIndepPoly (m+1) Q`,
    full independence — NOT truncated coefficient independence; the Hilbert
    family has degree ≤ n and full independence, and prefixes of it remain
    fully independent),
  (ii) of degree `≤ n` per element,
  (iii) norm-ordered `wnorm n (zmap (Q i)) ≤ wnorm n (zmap (Q (i+1)))`,
and given an integer polynomial `G ≠ 0` with `0 ≤ ∫ log|G| dμ` and quotient
polynomials `S : Fin (k+1) → Polynomial ℤ` satisfying (for `pre : Fin (k+1) ↪
Fin (m+1)` the natural embedding from `k ≤ m`)
  (iv) `Q (pre i) = G·(S i)` for all `i ≤ k`,
  (v) the `S i` (`i ≤ k`) have no common complex root,
  (vi) `natDegree (S i) ≤ m` for all `i ≤ k`, and
  (vii) `natDegree (S i₀) = m` for some `i₀ ≤ k`,
we have the lower bound
  `n^{−C·n} · exp((m·n − ½·m²)·energy) ≤ ∏_{i ≤ m} wnorm n (zmap (Q i))`

(`energy = EnergyHalf.energy = I(μ) ≤ 0`; the paper's `G = gcd(Q_0..Q_k)`
content is exactly the GcdInt quotient structure (iv)+(v) with the degree
maximality (vi)+(vii) — that is what the proof uses; no further `gcd` API).

## Proof roadmap (paper proof; k ≥ 1 so m ≥ 1)

Notation: `wn := wnorm n (zmap ·)`.

1. **The squarefree combination.**  Apply `GcdInt` content is given; apply
   `NocommonGeneral.nocommon_general` to the family `S : Fin (k+1) → ℤ[X]`
   (K := k ≥ 1, m := m): hypotheses `hnz` (each `S i ≠ 0`: from `Q i ≠ 0`
   (lin-indep family: a zero member is not independent — prove from
   `LinIndepInt` that all `Q i ≠ 0`), `G ≠ 0`, and `Q (pre i) = G·S i`),
   `hdeg` (vi), `hlead` (vii), `hnc` (v).  Get `i₀ : Fin (k+1)`,
   `b : Fin (k+1) → ℕ` with `b i₀ = 1`, `∀i, b i ≤ 2m+1`, and
   `A := CombPoly k S b = ∑_i C(b i)·S i` satisfies
   `A.natDegree = m` and `(A.map (algebraMap ℤ ℂ)).Separable`.
   Let `QA := ∑_i C(b i)·Q (pre i) = G·A` (integer poly, prove identity by
   (iv)).  From the norm ordering and `b i ≤ 2m+1`:
   `wn (zmap A·zmap G) = wn (zmap QA) ≤ (∑_i b i)·wn (zmap (Q (pre i₀)))
   ≤ (k+1)(2m+1)·wn (Q_k)`  — call this (∗): `wn(G·A) ≤ 3k·m·wn(Q_k)`
   (slack OK).

2. **Roots of A.**  `(A.map ℂ).Separable` and `A.natDegree = m` give root
   data via `RootData.root_data_of_separable` at degree `m`: an injective
   `α : Fin m → ℂ` with `A.map = C(lc)·∏(X − C(α i))`; `m ≥ 1`.  (For
   `m = 1` the adjust step below is not needed — see step 5.)

3. **Adjustment for `P = ½ X^j`.**  For `m ≥ 2` and each `j < m`, apply
   `AdjustLemma.adjust_lemma` to `Q := A`, `n := m`, `P := ½·X^{j.val}` (real
   poly; note `natDegree P ≤ m−1` since `j < m`), with the root data of A:
   obtain `Rⱼ : Polynomial ℤ` (`natDegree ≤ m−1`), `βⱼ : Fin m → ℂ` with
     `Σ_i ‖βⱼ i‖ ≤ m^{Cadj}`, and the complex identity
     `(Pⱼ).map ℂ − (zmap Rⱼ).map ℂ = ∑_i βⱼ i • (qDiv A (α i))`,
     `qDiv A (α i) = (A.map ℂ)/ₘ (X − C(α i))`.
   Define `Hⱼ : Polynomial ℤ := X^{j.val} − 2·Rⱼ`.  Complexified:
   `(Hⱼ).map ℂ = 2·∑_i βⱼ i • (qDiv A (α i))`; in particular
   `natDegree Hⱼ ≤ m−1` (coefficient bookkeeping: `X^{j.val}` has degree
   `j.val ≤ m−1`, `Rⱼ` degree `≤ m−1`) and `Hⱼ ≡ X^{j.val} (mod 2)`
   coefficient-wise (`coeff` of `−2·Rⱼ` are even).

4. **𝔽₂ / ℚ independence of the `Hⱼ`.**  Since `(Hⱼ).map` to 𝔽₂[X] (reduce
   coefficients mod 2) equals `X^{j.val}`, the family `{Hⱼ : j < m}` is
   linearly independent over 𝔽₂, hence over ℚ (a ℚ-relation cleared to a
   content-1 ℤ-relation would give a nontrivial 𝔽₂-relation; Mathlib:
   `Polynomial` mod 2 via `map (Int.castRingHom (ZMod 2))` or
   `(ZMod 2)`-coefficient polynomials; alternatively prove ℚ-independence
   directly: they have distinct degrees with odd leading coefficients
   (`Hⱼ.coeff j = 1 − 2·(Rⱼ.coeff j)` is ODD, and `coeff k` for `k > j` even
   ⟹ degree `Hⱼ = j` with odd leading coeff ⟹ triangular w.r.t. degrees ⟹
   ℚ-independent).  The triangular-degree route is EASIEST: `Hⱼ` has degree
   exactly `j` with ODD leading coefficient (since `Hⱼ.coeff j.val = 1 − 2·odd?`
   — `Rⱼ.coeff j.val` any integer, so `1 − 2·z` odd, nonzero ⟹ degree = j).
   Then `{H_0..H_{m−1}}` is ℚ-independent (each degree `j` distinct with
   nonzero coefficient).  Also `{Hⱼ}` spans the degree-`≤(m−1)` space (m
   independent vectors in the m-dimensional space).

5. **Basis extension.**  The family `{S 0,..,S k}` is ℚ-independent (from (i)
   and `G ≠ 0`: a ℚ-relation among `S` gives one among `Q` after multiplying
   by G).  Let `U = span{S_i : i ≤ k}` and `V = {deg ≤ m−1} = span{H_j}`.
   Since some `S_{i₀}` has degree exactly `m`, `U ⊄ V`, and the degree-`m`
   parts of elements of U form a 1-dimensional space (multiples of `X^m`),
   so `dim(U ∩ V) = k` and `dim(U + V) = m+1`: PROVE the needed consequence
   directly and concretely instead of abstract dimensions:
   **there exists a subset `Sset : Finset (Fin m)` of cardinality `m − k`**
   such that the `(m+1)`-element family
   `{S 0,…,S k} ∪ {H_j : j ∈ Sset}` is ℚ-independent (hence a basis of the
   degree-`≤ m` space).
   Concrete proof of existence (greedy + triangular argument): extend `U` by
   vectors of `{H_j}` one at a time in increasing `j`-order, adding `H_j` iff
   it is not in the span so far.  Since the `H_j` are a ℚ-basis of the degree
   `≤ m−1` space and `U` contains a degree-`m` vector, show the greedy process
   adds exactly `m − k` vectors: the number of added vectors equals
   `dim((U+V)/U)`-type rank = `m+1 − (k+1) = m − k` (use
   `LinearIndependent`/`Module.finrank` or elementary linear algebra on
   coefficient vectors — your choice of API, e.g.
   `LinearIndependent`, `Submodule`, or the concrete row-echelon via
   `Matrix`).  You may instead prove directly: `U ∩ span{H_j}` has
   dimension `k` (it contains the k independent `S_i` of degree `≤ m−1`...
   CAREFUL: only `S_{i₀}` is known to have degree `m`; other `S_i` could also
   have degree `m`.  Argue: `U ∩ V ⊆ U`, and if `dim(U ∩ V) = k+1` then
   `U ⊆ V` contradicting `S_{i₀} ∈ U` of degree `m`; and `U ∩ V` contains at
   least the elements of U of degree `≤ m−1`, in particular `dim ≥ k` is NOT
   automatic if several `S_i` have degree `m`.  Better argument: the degree-m
   parts `lead(S_i)·X^m` all lie in the one-dimensional space `span{X^m}`;
   the image of U in the quotient `(deg ≤ m)/(deg ≤ m−1)` is spanned by at
   most one vector, but is nonzero (`S_{i₀}`), so the kernel `U∩V` has
   dimension exactly `(k+1)−1 = k`; then `dim(U+V) = (k+1) + m − k = m+1`.)
   Then choose a ℚ-basis of `U+V = W` extending a basis of U, and show it
   can be taken from `{H_j}` (exchange argument; any basis of the complement
   can be chosen among the `H_j` since the `H_j` span V and U+V = W; state
   and prove a small lemma: if `{h_0..h_{m−1}}` is a basis of V and
   `U + V = W`, `dim U = k+1`, then some `m−k` of the `h`'s complete U to a
   basis of W — greedy works because each non-added `h_j` lies in `U + span`
   of previously added ones).

6. **Squeeze.**  Apply `SqueezeMink.squeeze` (rcase `Contract1Core.squeeze`)
   to: `m' := m`, `n := n`, `R := G` (nonzero, and `0 ≤ ∫log|G|dμ` given),
   and the family `Qfam : Fin (m+1) → ℤ[X]` whose first `k+1` entries are
   `S 0,…,S k` and whose remaining `m−k` entries are `H_j` for `j ∈ Sset`
   (build via `Finset` enumeration; index carefully).  Need `deg ≤ m` per
   member and `LinIndepInt (m+1) Qfam`.  The squeeze bound:
   `n^{−C₀·n}·exp((m+1)(n − m/2)·energy) ≤ ∏ over the basis of wnorm n
   (zmap(member)·zmap G)`.  Note `zmap(S i)·zmap G = zmap(Q (pre i))` (iv)
   and `zmap(H_j)·zmap G = zmap(H_j·G)` — the H-side terms are NOT directly
   `Q`-terms; they are bounded from above in step 7.

7. **Upper bounds for `wn(H_j·G)` and assembly.**  Complexified:
   `H_j·G = 2·∑_i βⱼ i • (qDiv A (α i))·G`.  For each i:
   `A.map ℂ · (zmap G).map ℂ = (X − C(α i))·(qDiv A (α i))·Gc` (root
   factorization), so `RemezComplex.complex_remez` with `P := (zmap(A·G)).map
   ℂ` (degree = m + deg G ≤ n; nonzero), root `α i` gives
   `cwnorm n (qDiv A (α i)·Gc) ≤ (2·n)^C·cwnorm n (A·G as complex)` =
   `(2n)^C·wnorm n (zmap(A·G)) ≤ (2n)^C·(3km)·wn(Q_k)` by (∗) (convert
   complex norms to real wnorm via `cwnorm_map_eq_wnorm`).  Hence with
   `Σ_i ‖βⱼ i‖ ≤ m^{Cadj}`:
   `wn(H_j·G) ≤ 2·m^{Cadj}·(2n)^C·3km·wn(Q_k)` for each j — a common
   polynomial factor `p(n,m,k)` (with ABSOLUTE exponents): `wn(H_j·G) ≤
   p(n,m,k)·wn(Q_k)`.
   Substitute into the step-6 product lower bound: the product factors as
   `(∏_{i≤k} wn(Q (pre i)))·(∏_{j ∈ Sset} wn(H_j·G))`.  The H-side is
   `≤ p(n,m,k)^{m−k}·wn(Q_k)^{m−k} ≤ p'·∏_{i=k+1}^{m} wn(Q_i)` by the norm
   ordering (`wn(Q_k) ≤ wn(Q_i)` for `i ≥ k`, and `p^{m−k}` ≤
   `n^{C·n}`-type for an absolute C — absorb with slack).  Conclude
   `∏_{i=0}^{m} wn(Q_i) ≥ n^{−C'·n}·exp((m+1)(n−m/2)·energy)`.
   Finally absorb the deficit: since `energy ≤ 0` and `n ≥ m`, the exponent
   `(m+1)(n−m/2) = (mn − ½m²) + (n − m/2)` differs from `mn − ½m²` by the
   nonnegative amount `n − m/2`; as `exp((n−m/2)·energy) ≤ 1` and the
   relative deficit `exp((m/2 − n)·energy) = exp((n − m/2)(−energy)) ≤
   exp(n·(−energy)) ≤ n^{C''·n}` for an absolute `C''` (because `−energy` is
   a fixed nonnegative real and `e^{cn} ≤ n^{C'' n}` for `C''` large), we can
   move it into the `n^{−C·n}` factor.  Deliver `secondSqueeze` with its own
   `C` (no relation to the inner constants).

## FIX REQUEST (restated hypothesis — READ THIS FIRST)

The previous version of this file demanded `MinkBox.LinIndepInt (m+1) Q`
(linear independence of the length-`(m+1)` COEFFICIENT TRUNCATIONS of the
family `Q : Fin (m+1) → ℤ[X]`).  That is the WRONG hypothesis: the Hilbert
family members have degree `≤ n` (possibly `> m`), and truncated independence
does NOT follow from full independence — e.g. `X^5+X^3` has zero truncation at
length 3.  The theorem statement now correctly uses `FullIndepPoly (m+1) Q`
(ℚ-linear independence of the full polynomials in `ℚ[X]`), which is what the
assembly can supply (Hilbert's family has full independence, and prefixes of a
fully-independent family are fully independent).

CONSEQUENCE: the proof below (`second_squeeze_from_data` and its helpers) must
be reworked: anywhere the family `Q`'s independence is used to conclude
independence of the quotients `S i = (Q (pre i))/G` or of the constructed
degree-≤-m basis, use FULL polynomial independence instead (multiplying a
ℚ-relation among the `S i` by `G ≠ 0` gives a relation among the `Q (pre i)`,
which are fully independent).  Where a DEGREE-≤-m family is fed to
`SqueezeMink.squeeze` (whose `LinIndepInt` hypothesis is fine because for
degree-`≤ m` members the length-`(m+1)` coefficient vector is the whole
polynomial), you may either prove `LinIndepInt` directly or add a small bridge
lemma `full_indep_of_deg_le_of_LinIndepInt`-style in the OTHER direction
(deg ≤ m + full indep ⟹ LinIndepInt d).  Do NOT try to derive
`LinIndepInt (m+1) Q` from `FullIndepPoly (m+1) Q` in general (false).
Deliver `second_squeeze : secondSqueezeProp` compiling with no sorries.

## Notes / API
- `wnorm`, `zmap`, `muSerre` : `Submission.Contracts`;
- `energy` : `EnergyHalf.energy` (≤ 0, from `Contract1Core.energy_nonpos`);
- `LinIndepInt`: `Submission.MinkBox`;
- `squeeze` (theorem with `squeezeProp` content): `Contract1Core.squeeze`;
- `nocommon_general`, `CombPoly`/`DistinctRootData`: `Submission.NocommonGeneral`
  / `Submission.Nocommon`;
- `gcd_int_quotient`: `Submission.GcdInt`;
- `adjust_lemma`, `qDiv`: `Submission.AdjustLemma`;
- `complex_remez`: `Submission.RemezComplex`; `cwnorm_map_eq_wnorm`: `Submission.Cwnorm`;
- `root_data_of_separable`/`RootDataOf`: `Submission.RootData`; `Squarefree
  (A.map …).Separable`: use `DistinctRootData` directly.
- `ArithmeticOn muSerre` (`ArithmeticAssembly.serre_arithmetic`) supplies
  `0 ≤ ∫ log|G|dμ` when needed by consumers; in the STATEMENT below the
  integral hypothesis is explicit.

Axioms ⊆ {propext, Quot.sound, Classical.choice}; no placeholders, no `axiom`.
This is a LONG lemma (1000+ lines expected).  You may add private helpers in
this file or create your own auxiliary `Submission/*.lean` modules (one lemma
per file, all placeholder-free at the end).  Deliver exactly `second_squeeze`.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.SecondSqueeze

open Submission.Contracts
open Submission.MinkBox
open Submission.AdjustLemma
open Submission.Nocommon
open Submission.Cwnorm
open Submission.RootData
open Submission.WnormToolkit
/-- Embedding of the prefix index `Fin (k+1)` into `Fin (m+1)` (`k ≤ m`). -/
def pre {m k : ℕ} (hkm : k ≤ m) (i : Fin (k + 1)) : Fin (m + 1) :=
  ⟨i.val, by omega⟩


/-! ## auxiliary facts: ordering chain, independence, combination -/

open Submission.WnormToolkit

lemma wn_chain_step {n m : ℕ} {Q : Fin (m + 1) → Polynomial ℤ}
    (hord : ∀ i : Fin m, wnorm n (zmap (Q (Fin.castSucc i))) ≤
      wnorm n (zmap (Q (Fin.succ i))))
    {t : ℕ} (htm : t < m) :
    wnorm n (zmap (Q ⟨t, by omega⟩)) ≤ wnorm n (zmap (Q ⟨t + 1, by omega⟩)) := by
  have hcast : Fin.castSucc (⟨t, htm⟩ : Fin m) = (⟨t, by omega⟩ : Fin (m + 1)) := by
    ext; simp
  have hsucc : Fin.succ (⟨t, htm⟩ : Fin m) = (⟨t + 1, by omega⟩ : Fin (m + 1)) := by
    ext; simp
  simpa [hcast, hsucc] using hord (⟨t, htm⟩ : Fin m)

lemma wn_chain {n m : ℕ} {Q : Fin (m + 1) → Polynomial ℤ}
    (hord : ∀ i : Fin m, wnorm n (zmap (Q (Fin.castSucc i))) ≤
      wnorm n (zmap (Q (Fin.succ i))))
    {a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) (hab : a ≤ b) :
    wnorm n (zmap (Q ⟨a, Nat.lt_succ_of_le ha⟩)) ≤
      wnorm n (zmap (Q ⟨b, Nat.lt_succ_of_le hb⟩)) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ t hle ih =>
      have htm : t < m := by omega
      exact le_trans (ih (by omega)) (wn_chain_step (Q := Q) hord htm)

lemma pre_injective {m k : ℕ} (hkm : k ≤ m) : Function.Injective (pre hkm) := by
  intro a b hab
  apply Fin.ext
  have hval : (pre hkm a).val = (pre hkm b).val := congrArg Fin.val hab
  simpa [pre] using hval

/-- Full ℚ-linear independence of a family of integer polynomials viewed
in `ℚ[X]` (as polynomials, i.e. no truncation). -/
def FullIndepPoly (d : ℕ) (Q : Fin d → Polynomial ℤ) : Prop :=
  LinearIndependent ℚ (fun i : Fin d => (Q i).map (algebraMap ℤ ℚ))

/-- each member of a fully independent family is nonzero. -/
lemma full_indep_member_ne_zero {d : ℕ} {Q : Fin d → Polynomial ℤ}
    (hQ : FullIndepPoly d Q) (i : Fin d) : Q i ≠ 0 := by
  have hQ' : LinearIndependent ℚ (fun x : Fin d => (Q x).map (algebraMap ℤ ℚ)) := hQ
  intro hz
  have hzmap : (Q i).map (algebraMap ℤ ℚ) = 0 := by simp [hz]
  exact hQ'.ne_zero i hzmap

/-- `Q (pre i) ≠ 0` and `S i ≠ 0` under the hypotheses. -/
lemma S_ne_zero_of {m k : ℕ} (hkm : k ≤ m) (Q : Fin (m + 1) → Polynomial ℤ)
    (hQ : FullIndepPoly (m + 1) Q) (G : Polynomial ℤ)
    (S : Fin (k + 1) → Polynomial ℤ)
    (hdiv : ∀ i : Fin (k + 1), Q (pre hkm i) = G * S i) :
    ∀ i : Fin (k + 1), S i ≠ 0 := by
  intro i hi
  have hQi : Q (pre hkm i) ≠ 0 := full_indep_member_ne_zero hQ (pre hkm i)
  have : Q (pre hkm i) = 0 := by
    rw [hdiv i, hi]
    simp
  exact hQi this

/-- ℚ-independence of the `S`-family (coefficient vectors of length m+1),
from the FULL ℚ-polynomial independence of `Q` and `Q (pre i) = G * S i`. -/
lemma linIndep_S {m k : ℕ} (hkm : k ≤ m) (Q : Fin (m + 1) → Polynomial ℤ)
    (hQ : FullIndepPoly (m + 1) Q) (G : Polynomial ℤ)
    (S : Fin (k + 1) → Polynomial ℤ)
    (hdiv : ∀ i : Fin (k + 1), Q (pre hkm i) = G * S i)
    (hdegS : ∀ i : Fin (k + 1), (S i).natDegree ≤ m) :
    LinearIndependent ℚ (fun i : Fin (k + 1) => coeffVec (m + 1) (S i)) := by
  classical
  let Sq : Fin (k + 1) → Polynomial ℚ := fun i => (S i).map (Int.castRingHom ℚ)
  let Qq : Fin (m + 1) → Polynomial ℚ := fun i => (Q i).map (Int.castRingHom ℚ)
  let Gq : Polynomial ℚ := G.map (Int.castRingHom ℚ)
  have hQq : LinearIndependent ℚ (fun i : Fin (m + 1) => Qq i) := by
    simpa [FullIndepPoly, Qq] using hQ
  have hQfull : LinearIndependent ℚ (fun i : Fin (k + 1) => Qq (pre hkm i)) := by
    change LinearIndependent ℚ (Qq ∘ (fun i : Fin (k + 1) => pre hkm i))
    exact hQq.comp (fun i : Fin (k + 1) => pre hkm i) (pre_injective hkm)
  rw [Fintype.linearIndependent_iff]
  intro g hrel i
  have hpoly0 : (∑ x : Fin (k + 1), g x • Sq x) = 0 := by
    apply Polynomial.ext
    intro t
    by_cases htm : t ≤ m
    · have ht : t < m + 1 := by omega
      calc
        (∑ x : Fin (k + 1), g x • Sq x).coeff t
            = ∑ x : Fin (k + 1), g x * ((S x).coeff t : ℚ) := by
                simp [Sq]
        _ = (∑ x : Fin (k + 1), g x • coeffVec (m + 1) (S x)) ⟨t, ht⟩ := by
                simp [coeffVec, Pi.smul_apply]
        _ = 0 := by exact congrFun hrel ⟨t, ht⟩
    · have hgt : m < t := by omega
      calc
        (∑ x : Fin (k + 1), g x • Sq x).coeff t
            = ∑ x : Fin (k + 1), g x * ((S x).coeff t : ℚ) := by
                simp [Sq]
        _ = ∑ x : Fin (k + 1), g x * (0 : ℚ) := by
                congr 1
                ext x
                congr 1
                exact_mod_cast (Polynomial.coeff_eq_zero_of_natDegree_lt
                  (lt_of_le_of_lt (hdegS x) hgt) : (S x).coeff t = 0)
        _ = 0 := by simp
  have hQrel : (∑ x : Fin (k + 1), g x • Qq (pre hkm x)) = 0 := by
    calc
      (∑ x : Fin (k + 1), g x • Qq (pre hkm x))
          = ∑ x : Fin (k + 1), Gq * (g x • Sq x) := by
              apply Finset.sum_congr rfl
              intro x hx
              dsimp [Qq, Sq, Gq]
              rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
              rw [hdiv x, Polynomial.map_mul]
              ring
      _ = Gq * (∑ x : Fin (k + 1), g x • Sq x) := by
              rw [← Finset.mul_sum]
      _ = 0 := by rw [hpoly0, mul_zero]
  exact (Fintype.linearIndependent_iff.mp hQfull) g hQrel i

lemma wnorm_zero (k : ℕ) : wnorm k (0 : Polynomial ℝ) = 0 := by
  apply le_antisymm
  · apply wnorm_sSup_le
    intro x hx
    simp
  · exact wnorm_nonneg k 0

lemma wnorm_sum_le (k : ℕ) {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) :
    wnorm k (∑ i ∈ s, P i) ≤ ∑ i ∈ s, wnorm k (P i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [wnorm_zero]
  · intro a s has ih
    rw [Finset.sum_insert has]
    calc
      wnorm k (P a + ∑ i ∈ s, P i) ≤ wnorm k (P a) + wnorm k (∑ i ∈ s, P i) :=
        wnorm_add_le k (P a) (∑ i ∈ s, P i)
      _ ≤ wnorm k (P a) + ∑ i ∈ s, wnorm k (P i) := by
          exact add_le_add le_rfl ih
      _ = ∑ i ∈ insert a s, wnorm k (P i) := by
          rw [Finset.sum_insert has]

/-- The combination of the S_i by weights b, multiplied by G, has Q·G norm
bounded by (k+1)(2m+1)·wn(Q_k). -/
lemma combination_data {k m n : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (Q : Fin (m + 1) → Polynomial ℤ) (hQ : FullIndepPoly (m + 1) Q)
    (hord : ∀ i : Fin m, wnorm n (zmap (Q (Fin.castSucc i))) ≤
      wnorm n (zmap (Q (Fin.succ i))))
    (G : Polynomial ℤ)
    (S : Fin (k + 1) → Polynomial ℤ)
    (hdiv : ∀ i : Fin (k + 1), Q (pre hkm i) = G * S i)
    (hnc : ∀ z : ℂ, ¬ (∀ i : Fin (k + 1), Polynomial.aeval z (S i) = 0))
    (hdegS : ∀ i : Fin (k + 1), (S i).natDegree ≤ m)
    (hleadS : ∃ i₀ : Fin (k + 1), (S i₀).natDegree = m) :
    ∃ (A : Polynomial ℤ) (b : Fin (k + 1) → ℕ),
      A ≠ 0 ∧ A.natDegree = m ∧ (A.map (algebraMap ℤ ℂ)).Separable ∧
      (∀ i, b i ≤ 2 * m + 1) ∧
      wnorm n (zmap (G * A)) ≤ ((k + 1) * (2 * m + 1) : ℕ) *
        wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := by
  classical
  have hSnz : ∀ i : Fin (k + 1), S i ≠ 0 := S_ne_zero_of hkm Q hQ G S hdiv
  rcases Submission.NocommonGeneral.nocommon_general (K := k) hk1 S hSnz hdegS hleadS hnc with
    ⟨i₀, b, hdeg_i0, hb_i0, hb_le, hDRD⟩
  let A : Polynomial ℤ := ∑ i : Fin (k + 1), Polynomial.C (((b i : ℕ) : ℤ)) * S i
  have hAdef : A = ∑ i : Fin (k + 1), Polynomial.C (((b i : ℕ) : ℤ)) * S i := rfl
  have hDRD' : Submission.Nocommon.DistinctRootData A m := by
    simpa [A] using hDRD
  have hdegA : A.natDegree = m := hDRD'.1
  have hsepA : (A.map (algebraMap ℤ ℂ)).Separable := hDRD'.2
  have hA0 : A ≠ 0 := by
    intro hz
    have : (0 : Polynomial ℤ).natDegree = m := by simpa [hz] using hdegA
    simp at this
    have : m = 0 := this.symm
    omega
  refine ⟨A, b, hA0, hdegA, hsepA, hb_le, ?_⟩
  have hGA : G * A = ∑ i : Fin (k + 1), Polynomial.C (((b i : ℕ) : ℤ)) * Q (pre hkm i) := by
    calc
      G * A = ∑ i : Fin (k + 1), G * (Polynomial.C (((b i : ℕ) : ℤ)) * S i) := by
                rw [hAdef, Finset.mul_sum]
      _ = ∑ i : Fin (k + 1), Polynomial.C (((b i : ℕ) : ℤ)) * (G * S i) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = ∑ i : Fin (k + 1), Polynomial.C (((b i : ℕ) : ℤ)) * Q (pre hkm i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hdiv i]
  have hGAz : zmap (G * A) =
      ∑ i : Fin (k + 1), ((b i : ℕ) : ℝ) • (zmap (Q (pre hkm i))) := by
    rw [hGA, zmap, Polynomial.map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.map_mul]
    rw [Polynomial.smul_eq_C_mul]
    simp [zmap]
  have hsum_bound : wnorm n (∑ i : Fin (k + 1), ((b i : ℕ) : ℝ) • (zmap (Q (pre hkm i))))
        ≤ ∑ i : Fin (k + 1), (b i : ℝ) * wnorm n (zmap (Q (pre hkm i))) := by
    calc
      wnorm n (∑ i : Fin (k + 1), ((b i : ℕ) : ℝ) • (zmap (Q (pre hkm i))))
          ≤ ∑ i : Fin (k + 1), wnorm n (((b i : ℕ) : ℝ) • (zmap (Q (pre hkm i)))) := by
              simpa using (wnorm_sum_le n (Finset.univ : Finset (Fin (k + 1)))
                (fun i => ((b i : ℕ) : ℝ) • (zmap (Q (pre hkm i)))))
      _ = ∑ i : Fin (k + 1), (b i : ℝ) * wnorm n (zmap (Q (pre hkm i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [wnorm_smul]
              congr 1
              exact abs_of_nonneg (by positivity)
  have hwnk0 : 0 ≤ wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := wnorm_nonneg _ _
  calc
    wnorm n (zmap (G * A))
        = wnorm n (∑ i : Fin (k + 1), ((b i : ℕ) : ℝ) • (zmap (Q (pre hkm i)))) := by
            rw [hGAz]
    _ ≤ ∑ i : Fin (k + 1), (b i : ℝ) * wnorm n (zmap (Q (pre hkm i))) := hsum_bound
    _ ≤ ∑ i : Fin (k + 1), (b i : ℝ) * wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hchain : wnorm n (zmap (Q (pre hkm i))) ≤
                wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := by
              have ha2 : (pre hkm i).val ≤ m := by omega
              have hab2 : (pre hkm i).val ≤ k := by
                have : i.val ≤ k := by
                  have := i.isLt
                  omega
                simpa [pre] using this
              exact wn_chain (Q := Q) hord ha2 hkm hab2
            exact mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = (∑ i : Fin (k + 1), (b i : ℝ)) * wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := by
            rw [Finset.sum_mul]
    _ ≤ (((k + 1) * (2 * m + 1) : ℕ) : ℝ) * wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := by
            have hbsum : (∑ i : Fin (k + 1), (b i : ℝ)) ≤ (((k + 1) * (2 * m + 1) : ℕ) : ℝ) := by
              have hbN : (∑ i : Fin (k + 1), b i) ≤ (k + 1) * (2 * m + 1) := by
                calc
                  (∑ i : Fin (k + 1), b i) ≤ ∑ i : Fin (k + 1), (2 * m + 1) := by
                    exact Finset.sum_le_sum (fun i hi => hb_le i)
                  _ = (k + 1) * (2 * m + 1) := by simp
              exact_mod_cast hbN
            exact mul_le_mul_of_nonneg_right hbsum hwnk0
    _ = (((k + 1) * (2 * m + 1) : ℕ) : ℝ) * wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := rfl


/-- coefficient at the top degree of a degree-`m` polynomial (m ≥ 1) is nonzero. -/
lemma coeff_m_ne_zero_of_natDegree_eq {m : ℕ} {P : Polynomial ℤ} (hm : 1 ≤ m)
    (hdeg : P.natDegree = m) : P.coeff m ≠ 0 := by
  have hP0 : P ≠ 0 := by
    intro h
    have : (0 : Polynomial ℤ).natDegree = m := by simpa [h] using hdeg
    simp at this
    omega
  intro hz
  apply (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  rw [← Polynomial.coeff_natDegree, hdeg]
  exact hz

/-- `H := X^j − 2R` has degree `≤ m−1` when `R` does and `j < m`. -/
lemma natDegree_H_le {m : ℕ} {j : Fin m} {R : Polynomial ℤ}
    (hR : R.natDegree ≤ m - 1) :
    (Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R : Polynomial ℤ).natDegree ≤ m - 1 := by
  have h1 : (Polynomial.X ^ (j : ℕ) : Polynomial ℤ).natDegree ≤ m - 1 := by
    rw [Polynomial.natDegree_X_pow]
    exact (Nat.le_sub_one_of_lt j.isLt)
  have h2 : ((2 : ℤ) • R : Polynomial ℤ).natDegree ≤ m - 1 :=
    le_trans (Polynomial.natDegree_smul_le (2 : ℤ) R) hR
  exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)
/-- degree of `½·X^j` is ≤ m−1 for `j : Fin m`. -/
lemma natDegree_half_smul_X_pow_le {m : ℕ} (j : Fin m) :
    (((1 / 2 : ℝ) • Polynomial.X ^ (j : ℕ)) : Polynomial ℝ).natDegree ≤ m - 1 := by
  have h1 : (((1 / 2 : ℝ) • Polynomial.X ^ (j : ℕ)) : Polynomial ℝ).natDegree ≤
      (Polynomial.X ^ (j : ℕ) : Polynomial ℝ).natDegree :=
    Polynomial.natDegree_smul_le (1 / 2 : ℝ) (Polynomial.X ^ (j : ℕ))
  rw [Polynomial.natDegree_X_pow] at h1
  exact le_trans h1 (Nat.le_sub_one_of_lt j.isLt)

/-- per-`j` adjust data: `R` (degree ≤ m−1), identity and ℓ₁ bound. -/
lemma adjust_at_j {m : ℕ} (hm2 : 2 ≤ m) {Cadj : ℝ}
    (hadj0 : ∀ (n : ℕ), 2 ≤ n → ∀ (Q : Polynomial ℤ), Q ≠ 0 → Q.natDegree = n →
      ∀ (α : Fin n → ℂ), Function.Injective α →
        Q.map (algebraMap ℤ ℂ) = Polynomial.C (Q.leadingCoeff : ℂ) *
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) →
      ∀ (P : Polynomial ℝ), P.natDegree ≤ n - 1 →
        ∃ (R : Polynomial ℤ) (β : Fin n → ℂ),
          R.natDegree ≤ n - 1 ∧
          P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ) =
            ∑ i : Fin n, β i • qDiv Q (α i) ∧
          (∑ i : Fin n, ‖β i‖ ≤ (n : ℝ) ^ Cadj))
    (A : Polynomial ℤ) (hA0 : A ≠ 0) (hdegA : A.natDegree = m)
    (α : Fin m → ℂ) (hαinj : Function.Injective α)
    (hαfac : A.map (algebraMap ℤ ℂ) = Polynomial.C (A.leadingCoeff : ℂ) *
      ∏ i : Fin m, (Polynomial.X - Polynomial.C (α i))) :
    ∀ j : Fin m,
      ∃ (R : Polynomial ℤ) (β : Fin m → ℂ),
        R.natDegree ≤ m - 1 ∧
        (Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R : Polynomial ℤ).map (algebraMap ℤ ℂ) =
          (2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i)) ∧
        (∑ i : Fin m, ‖β i‖ ≤ (m : ℝ) ^ Cadj) := by
  intro j
  let P : Polynomial ℝ := (1 / 2 : ℝ) • Polynomial.X ^ (j : ℕ)
  have hdegP : P.natDegree ≤ m - 1 := by
    simpa [P] using (natDegree_half_smul_X_pow_le (m := m) j)
  rcases hadj0 m hm2 A hA0 hdegA α hαinj hαfac P hdegP with ⟨R, β, hRdeg, hid, hβsum⟩
  refine ⟨R, β, hRdeg, ?_, hβsum⟩
  -- H := X^j − 2R ; complexified:
  have hmapR : (zmap R).map (algebraMap ℝ ℂ) = R.map (algebraMap ℤ ℂ) := by
    apply Polynomial.ext
    intro n
    simp [zmap, Polynomial.coeff_map]
  have hhid : ((1 / 2 : ℂ) • (Polynomial.X ^ (j : ℕ) : Polynomial ℂ)) -
        R.map (algebraMap ℤ ℂ) = ∑ i : Fin m, β i • qDiv A (α i) := by
    simpa [P, hmapR] using hid
  -- multiply the identity by 2
  have htimes : Polynomial.X ^ (j : ℕ) - (2 : ℂ) • (R.map (algebraMap ℤ ℂ)) =
      (2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i)) := by
    calc
      Polynomial.X ^ (j : ℕ) - (2 : ℂ) • (R.map (algebraMap ℤ ℂ))
          = (2 : ℂ) • ((1 / 2 : ℂ) • (Polynomial.X ^ (j : ℕ) : Polynomial ℂ)) -
              (2 : ℂ) • (R.map (algebraMap ℤ ℂ)) := by
            simp [smul_smul]
      _ = (2 : ℂ) • (((1 / 2 : ℂ) • (Polynomial.X ^ (j : ℕ) : Polynomial ℂ)) -
              R.map (algebraMap ℤ ℂ)) := by
            rw [← smul_sub]
      _ = (2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i)) := by
            rw [hhid]
  -- complexification of (X^j − (2:ℤ)•R) equals the same expression
  have hmap2 : ((2 : ℤ) • R : Polynomial ℤ).map (algebraMap ℤ ℂ) =
      (2 : ℂ) • R.map (algebraMap ℤ ℂ) := by
    apply Polynomial.ext
    intro n
    simp [Polynomial.coeff_map]
  calc
    (Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R : Polynomial ℤ).map (algebraMap ℤ ℂ)
        = (Polynomial.X ^ (j : ℕ) : Polynomial ℤ).map (algebraMap ℤ ℂ) -
            ((2 : ℤ) • R : Polynomial ℤ).map (algebraMap ℤ ℂ) := by
            rw [Polynomial.map_sub]
    _ = Polynomial.X ^ (j : ℕ) - (2 : ℂ) • R.map (algebraMap ℤ ℂ) := by
            rw [hmap2]
            simp
    _ = (2 : ℂ) • (∑ i : Fin m, β i • qDiv A (α i)) := htimes

/-- `H = X^j − 2R` reduces to `X^j` modulo 2. -/
lemma H_mod2 {m : ℕ} {j : Fin m} (R : Polynomial ℤ) :
    ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R : Polynomial ℤ).map (Int.castRingHom (ZMod 2))) =
      (Polynomial.X ^ (j : ℕ) : Polynomial (ZMod 2)) := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
  rw [Polynomial.coeff_sub, Polynomial.coeff_smul]
  simp only [smul_eq_mul]
  have hz : ((2 : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_ofNat]
    exact CharP.cast_eq_zero (ZMod 2) 2
  have hz' : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  by_cases h : n = (j : ℕ)
  · subst n
    simp [hz, hz']
  · simp [h, hz, hz']

/-- the whole family of adjust outputs `H j = X^j − 2·R j`. -/
lemma hj_family_full {m : ℕ} (hm2 : 2 ≤ m) {Cadj : ℝ}
    (hadj0 : ∀ (n : ℕ), 2 ≤ n → ∀ (Q : Polynomial ℤ), Q ≠ 0 → Q.natDegree = n →
      ∀ (α : Fin n → ℂ), Function.Injective α →
        Q.map (algebraMap ℤ ℂ) = Polynomial.C (Q.leadingCoeff : ℂ) *
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) →
      ∀ (P : Polynomial ℝ), P.natDegree ≤ n - 1 →
        ∃ (R : Polynomial ℤ) (β : Fin n → ℂ),
          R.natDegree ≤ n - 1 ∧
          P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ) =
            ∑ i : Fin n, β i • qDiv Q (α i) ∧
          (∑ i : Fin n, ‖β i‖ ≤ (n : ℝ) ^ Cadj))
    (A : Polynomial ℤ) (hA0 : A ≠ 0) (hdegA : A.natDegree = m)
    (α : Fin m → ℂ) (hαinj : Function.Injective α)
    (hαfac : A.map (algebraMap ℤ ℂ) = Polynomial.C (A.leadingCoeff : ℂ) *
      ∏ i : Fin m, (Polynomial.X - Polynomial.C (α i))) :
    ∃ (H R : Fin m → Polynomial ℤ) (β : Fin m → Fin m → ℂ),
      (∀ j, H j = Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j) ∧
      (∀ j, (H j).natDegree ≤ m - 1) ∧
      (∀ j, (H j).map (algebraMap ℤ ℂ) = (2 : ℂ) • (∑ i : Fin m, β j i • qDiv A (α i))) ∧
      (∀ j, ∑ i : Fin m, ‖β j i‖ ≤ (m : ℝ) ^ Cadj) ∧
      (∀ j, (H j).map (Int.castRingHom (ZMod 2)) = Polynomial.X ^ (j : ℕ)) := by
  classical
  let hspec : ∀ j : Fin m, ∃ (R0 : Polynomial ℤ) (β0 : Fin m → ℂ),
        R0.natDegree ≤ m - 1 ∧
        (Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R0 : Polynomial ℤ).map (algebraMap ℤ ℂ) =
          (2 : ℂ) • (∑ i : Fin m, β0 i • qDiv A (α i)) ∧
        (∑ i : Fin m, ‖β0 i‖ ≤ (m : ℝ) ^ Cadj) :=
      fun j => adjust_at_j (m := m) hm2 hadj0 A hA0 hdegA α hαinj hαfac j
  let R : Fin m → Polynomial ℤ := fun j => (hspec j).choose
  let β : Fin m → Fin m → ℂ := fun j => (hspec j).choose_spec.choose
  let H : Fin m → Polynomial ℤ := fun j => Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j
  refine ⟨H, R, β, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    have hdegj : (R j).natDegree ≤ m - 1 := (hspec j).choose_spec.choose_spec.1
    exact natDegree_H_le hdegj
  · intro j
    have hidj : ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j : Polynomial ℤ).map (algebraMap ℤ ℂ)) =
        (2 : ℂ) • (∑ i : Fin m, β j i • qDiv A (α i)) :=
      (hspec j).choose_spec.choose_spec.2.1
    exact hidj
  · intro j
    exact (hspec j).choose_spec.choose_spec.2.2
  · intro j
    have hm2' := H_mod2 (m := m) (j := j) (R j)
    simpa [H, R, hspec] using hm2'/-! ## final conclusion: absorb slack into `n^{−C·n}` -/

open Submission.SlackAbsorb

/-- product comparison `∏ A ≤ p^{card}·∏ B` from pointwise `A ≤ p·B`. -/
lemma prod_le_pow_prod {ι : Type*} [Fintype ι] (A B : ι → ℝ) (p : ℝ)
    (hA0 : ∀ t, 0 ≤ A t) (hAB : ∀ t, A t ≤ p * B t) :
    (∏ t : ι, A t) ≤ p ^ Fintype.card ι * (∏ t : ι, B t) := by
  classical
  have h1 : (∏ t : ι, A t) ≤ ∏ t : ι, p * B t := by
    exact Finset.prod_le_prod (s := (Finset.univ : Finset ι)) (f := A)
      (g := fun t : ι => p * B t) (fun t ht => hA0 t) (fun t ht => hAB t)
  calc
    (∏ t : ι, A t) ≤ ∏ t : ι, p * B t := h1
    _ = (∏ t : ι, p) * (∏ t : ι, B t) := by
        rw [Finset.prod_mul_distrib]
    _ = p ^ Fintype.card ι * (∏ t : ι, B t) := by simp

/-- the product-lower bound `n^{−C0n}·exp((m+1)(n−m/2)E) ≤ p^{m+1}·∏B`
followed by slack absorption gives the target `n^{−Ctot·n}` bound. -/
lemma final_conclude {n m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n)
    (hn2 : 2 ≤ n) {C0 Ctot : ℝ} (hC0 : 0 ≤ C0)
    {Cadj Crem e0 energy : ℝ} (hCadj : 0 ≤ Cadj) (hCrem : 0 ≤ Crem) (he0 : 0 ≤ e0)
    (hCtot : Ctot = sqC C0 Cadj Crem e0)
    {A B : Fin (m + 1) → ℝ}
    (hA0 : ∀ t, 0 ≤ A t) (hB0 : ∀ t, 0 ≤ B t)
    (hAB : ∀ t, A t ≤ sqp0 Cadj Crem n m k * B t)
    (hsq : (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * energy) ≤
      ∏ t : Fin (m + 1), A t)
    (hE : energy = -e0) :
    (n : ℝ) ^ (-Ctot * (n : ℝ)) *
        Real.exp (((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * energy) ≤
      ∏ t : Fin (m + 1), B t := by
  classical
  let p : ℝ := sqp0 Cadj Crem n m k
  have hpm1 : 1 ≤ m := by omega
  have hp_pos : 0 < p := by simpa [p] using (sqp0_pos Cadj Crem hn2 hpm1)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  -- 1. push the squeeze bound through the product bound
  have hAprod : (∏ t : Fin (m + 1), A t) ≤ p ^ (m + 1) * (∏ t : Fin (m + 1), B t) := by
    have h1 := prod_le_pow_prod (ι := Fin (m + 1)) A B p hA0 hAB
    simpa [p] using h1
  have hEarg : (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * energy =
      -(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0 := by
    rw [hE]
    ring
  have hsqE : (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) ≤
      p ^ (m + 1) * (∏ t : Fin (m + 1), B t) := by
    calc
      (n : ℝ) ^ (-C0 * (n : ℝ)) *
          Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0)
          = (n : ℝ) ^ (-C0 * (n : ℝ)) *
              Real.exp ((((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * energy) := by
            rw [← hEarg]
      _ ≤ ∏ t : Fin (m + 1), A t := hsq
      _ ≤ p ^ (m + 1) * (∏ t : Fin (m + 1), B t) := hAprod
  -- 2. divide by p^(m+1)
  have hsqE2 : (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) *
          (p ^ (m + 1))⁻¹ ≤ ∏ t : Fin (m + 1), B t := by
    have hp : 0 < p ^ (m + 1) := pow_pos hp_pos (m + 1)
    have hd : (n : ℝ) ^ (-C0 * (n : ℝ)) *
          Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) ≤
        (∏ t : Fin (m + 1), B t) * p ^ (m + 1) := by
      simpa [mul_comm] using hsqE
    simpa [div_eq_mul_inv] using (div_le_iff₀ hp).mpr hd
  -- 3. key power inequality from the absorb lemma
  have habs : (Ctot - C0) * (n : ℝ) * Real.log (n : ℝ) ≥
      ((n : ℝ) - (m : ℝ) / 2) * e0 + ((m + 1 : ℕ) : ℝ) * Real.log (sqp0 Cadj Crem n m k) := by
    simpa [hCtot, p] using (absorb hk1 hkm hmn hn2 hCadj hCrem he0)
  have hpPow : 0 < p ^ (m + 1) := pow_pos hp_pos (m + 1)
  have hlogp : Real.log (p ^ (m + 1)) = ((m + 1 : ℕ) : ℝ) * Real.log p := by
    rw [Real.log_pow]
  have hp_inv_exp : (p ^ (m + 1))⁻¹ = Real.exp (-((m + 1 : ℕ) : ℝ) * Real.log p) := by
    rw [← Real.exp_log hpPow, ← Real.exp_neg]
    congr 1
    rw [hlogp]
    ring
  have hKey : (n : ℝ) ^ (-Ctot * (n : ℝ)) ≤
      (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (-((n : ℝ) - (m : ℝ) / 2) * e0) * (p ^ (m + 1))⁻¹ := by
    rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos]
    rw [hp_inv_exp]
    rw [← Real.exp_add, ← Real.exp_add]
    rw [Real.exp_le_exp]
    -- transform to the exact form of `habs`:
    have hexp_goal : Real.log (n : ℝ) * (-Ctot * (n : ℝ)) ≤
        Real.log (n : ℝ) * (-C0 * (n : ℝ)) +
          (-((n : ℝ) - (m : ℝ) / 2) * e0) + (-((m + 1 : ℕ) : ℝ) * Real.log p) := by
      nlinarith [habs]
    exact hexp_goal
  -- 4. final exponent comparison and assembly
  have hKeyL : (n : ℝ) ^ (-Ctot * (n : ℝ)) *
        Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) ≤
      (n : ℝ) ^ (-C0 * (n : ℝ)) * Real.exp (-((n : ℝ) - (m : ℝ) / 2) * e0) *
        (p ^ (m + 1))⁻¹ *
          Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) := by
    exact mul_le_mul_of_nonneg_right hKey (Real.exp_pos _).le
  have hExpComb : Real.exp (-((n : ℝ) - (m : ℝ) / 2) * e0) *
        Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) =
      Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hLE : (n : ℝ) ^ (-Ctot * (n : ℝ)) *
        Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) ≤
      (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) *
          (p ^ (m + 1))⁻¹ := by
    calc
      (n : ℝ) ^ (-Ctot * (n : ℝ)) *
          Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0)
          ≤ (n : ℝ) ^ (-C0 * (n : ℝ)) * Real.exp (-((n : ℝ) - (m : ℝ) / 2) * e0) *
              (p ^ (m + 1))⁻¹ *
                Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) := hKeyL
      _ = ((n : ℝ) ^ (-C0 * (n : ℝ)) * (p ^ (m + 1))⁻¹) *
            (Real.exp (-((n : ℝ) - (m : ℝ) / 2) * e0) *
              Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0)) := by
            ring
      _ = ((n : ℝ) ^ (-C0 * (n : ℝ)) * (p ^ (m + 1))⁻¹) *
            Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) := by
            rw [hExpComb]
      _ = (n : ℝ) ^ (-C0 * (n : ℝ)) *
            Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) *
              (p ^ (m + 1))⁻¹ := by
            ring
  -- target uses energy; convert:
  have hTarg : Real.exp (((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * energy) =
      Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) := by
    rw [hE]
    congr 1
    ring
  calc
    (n : ℝ) ^ (-Ctot * (n : ℝ)) *
        Real.exp (((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * energy)
        = (n : ℝ) ^ (-Ctot * (n : ℝ)) *
            Real.exp (-((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) * e0) := by
          rw [hTarg]
    _ ≤ (n : ℝ) ^ (-C0 * (n : ℝ)) *
          Real.exp (-(((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2)) * e0) *
            (p ^ (m + 1))⁻¹ := hLE
    _ ≤ ∏ t : Fin (m + 1), B t := hsqE2

/-- Smith `lem:second_squeeze` for `1 ≤ k ≤ m ≤ n`. -/
def secondSqueezeProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (k m n : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n) (hn2 : 2 ≤ n),
      ∀ Q : Fin (m + 1) → Polynomial ℤ,
        FullIndepPoly (m + 1) Q →
        (∀ i : Fin (m + 1), (Q i).natDegree ≤ n) →
        (∀ i : Fin m, wnorm n (zmap (Q (Fin.castSucc i))) ≤
          wnorm n (zmap (Q (Fin.succ i)))) →
        ∀ G : Polynomial ℤ, G ≠ 0 →
          (0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x G| ∂muSerre) →
          ∀ S : Fin (k + 1) → Polynomial ℤ,
            (∀ i : Fin (k + 1), Q (pre hkm i) = G * S i) →
            (∀ z : ℂ, ¬ (∀ i : Fin (k + 1), Polynomial.aeval z (S i) = 0)) →
            (∀ i : Fin (k + 1), (S i).natDegree ≤ m) →
            (∃ i₀ : Fin (k + 1), (S i₀).natDegree = m) →
            (n : ℝ) ^ (-C * (n : ℝ)) *
                Real.exp (((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                  Submission.EnergyHalf.energy) ≤
              ∏ i : Fin (m + 1), wnorm n (zmap (Q i))

/-! ## main assembly -/

/-- case `k = m`: apply squeeze to the `S` family itself. -/
lemma second_squeeze_eq_m (C0 Cadj Crem : ℝ) (hC0pos : 0 < C0) (hCadjpos : 0 < Cadj)
    (hCrempos : 0 < Crem)
    (hsq0 : ∀ (m n : ℕ), 2 ≤ n → m ≤ n → ∀ (R : Polynomial ℤ), R ≠ 0 →
      (0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x R| ∂muSerre) →
      ∀ (Q : Fin (m + 1) → Polynomial ℤ), LinIndepInt (m + 1) Q →
        (∀ i, (Q i).natDegree ≤ m) →
      (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) *
          Submission.EnergyHalf.energy) ≤
        ∏ i : Fin (m + 1), wnorm n (zmap (Q i) * zmap R))
    {k m n : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n) (hn2 : 2 ≤ n)
    (hmk : m ≤ k)
    (Q : Fin (m + 1) → Polynomial ℤ) (hQlin : FullIndepPoly (m + 1) Q)
    (hQdeg : ∀ i : Fin (m + 1), (Q i).natDegree ≤ n)
    (hord : ∀ i : Fin m, wnorm n (zmap (Q (Fin.castSucc i))) ≤
      wnorm n (zmap (Q (Fin.succ i))))
    (G : Polynomial ℤ) (hG : G ≠ 0)
    (hGint : 0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x G| ∂muSerre)
    (S : Fin (k + 1) → Polynomial ℤ)
    (hdiv : ∀ i : Fin (k + 1), Q (pre hkm i) = G * S i)
    (hnc : ∀ z : ℂ, ¬ (∀ i : Fin (k + 1), Polynomial.aeval z (S i) = 0))
    (hdegS : ∀ i : Fin (k + 1), (S i).natDegree ≤ m)
    (hleadS : ∃ i₀ : Fin (k + 1), (S i₀).natDegree = m) :
    (n : ℝ) ^ (-(sqC C0 Cadj Crem (-Submission.EnergyHalf.energy)) * (n : ℝ)) *
        Real.exp (((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
          Submission.EnergyHalf.energy) ≤
      ∏ i : Fin (m + 1), wnorm n (zmap (Q i)) := by
  classical
  let e0 : ℝ := -Submission.EnergyHalf.energy
  have he0 : 0 ≤ e0 := by
    dsimp [e0]
    linarith [Submission.Contract1Core.energy_nonpos]
  have hE : Submission.EnergyHalf.energy = -e0 := by
    simp [e0]
  let Ctot : ℝ := sqC C0 Cadj Crem e0
  let p : ℝ := sqp0 Cadj Crem n m k
  have hCadj0 : 0 ≤ Cadj := le_of_lt hCadjpos
  have hCrem0 : 0 ≤ Crem := le_of_lt hCrempos
  have hpm1 : 1 ≤ m := by omega
  have hp_ge : 1 ≤ p := by
    simpa [p] using (sqp0_ge_one (Cadj := Cadj) (Crem := Crem) hn2 hpm1 hCadj0 hCrem0)
  have hCtot : Ctot = sqC C0 Cadj Crem e0 := rfl
  let Ffam : Fin (m + 1) → Polynomial ℤ := fun t => S ⟨(t : ℕ), by omega⟩
  have hFpre : ∀ i : Fin (k + 1), Ffam ⟨(i : ℕ), by omega⟩ = S i := by
    intro i
    have hIdx : (⟨(i : ℕ), by omega⟩ : Fin (k + 1)) = i := by
      ext
      simp
    simp [Ffam, hIdx]
  have hFlin : LinIndepInt (m + 1) Ffam := by
    let f : Fin (m + 1) → Fin (k + 1) := fun t => ⟨(t : ℕ), by omega⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      have : (f a).val = (f b).val := congrArg Fin.val hab
      simpa [f] using this
    have hSlin : LinearIndependent ℚ (fun i : Fin (k + 1) => coeffVec (m + 1) (S i)) :=
      linIndep_S hkm Q hQlin G S hdiv hdegS
    change LinearIndependent ℚ (fun t : Fin (m + 1) => coeffVec (m + 1) (Ffam t))
    have hcomp : LinearIndependent ℚ
        ((fun i : Fin (k + 1) => coeffVec (m + 1) (S i)) ∘ f) := hSlin.comp f hfinj
    have hEq : (fun t : Fin (m + 1) => coeffVec (m + 1) (Ffam t)) =
        ((fun i : Fin (k + 1) => coeffVec (m + 1) (S i)) ∘ f) := by
      funext t
      dsimp [Ffam, f]
    rw [hEq]
    exact hcomp
  have hFdeg : ∀ t : Fin (m + 1), (Ffam t).natDegree ≤ m := by
    intro t
    have : (Ffam t) = S ⟨(t : ℕ), by omega⟩ := rfl
    rw [this]
    exact hdegS ⟨(t : ℕ), by omega⟩
  let A : Fin (m + 1) → ℝ := fun t => wnorm n (zmap (Ffam t) * zmap G)
  let B : Fin (m + 1) → ℝ := fun t => wnorm n (zmap (Q t))
  have hA0 : ∀ t, 0 ≤ A t := by intro t; dsimp [A]; exact wnorm_nonneg _ _
  have hB0 : ∀ t, 0 ≤ B t := by intro t; dsimp [B]; exact wnorm_nonneg _ _
  have hAB : ∀ t, A t ≤ p * B t := by
    intro t
    let i : Fin (k + 1) := ⟨(t : ℕ), by omega⟩
    have hF : Ffam t = S i := by
      dsimp [Ffam, i]
    have hpre_t : pre hkm i = t := by
      apply Fin.ext
      simp [pre, i]
    have hAeqB : A t = B t := by
      dsimp [A, B]
      calc
        wnorm n (zmap (Ffam t) * zmap G)
            = wnorm n (zmap (S i) * zmap G) := by rw [hF]
        _ = wnorm n (zmap (S i * G)) := by simp [zmap]
        _ = wnorm n (zmap (Q (pre hkm i))) := by
              have hz : zmap (S i * G) = zmap (Q (pre hkm i)) := by
                rw [hdiv i]
                simp [zmap, mul_comm]
              rw [hz]
        _ = wnorm n (zmap (Q t)) := by rw [hpre_t]
    calc
      A t = B t := hAeqB
      _ ≤ p * B t := by
        simpa [one_mul] using (mul_le_mul_of_nonneg_right hp_ge (hB0 t))
  have hsq : (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * Submission.EnergyHalf.energy) ≤
      ∏ t : Fin (m + 1), A t := by
    have hs := hsq0 m n hn2 hmn G hG hGint Ffam hFlin hFdeg
    simpa [A] using hs
  have hfinal := final_conclude (k := k) (m := m) (n := n) hk1 hkm hmn hn2 (le_of_lt hC0pos)
    hCadj0 hCrem0 he0 hCtot hA0 hB0 hAB hsq hE
  simpa [Ctot, e0, A, B] using hfinal
/-- coefficient vector of `H j` at the top slot vanishes. -/
lemma coeffVec_last_zero_of_deg_le {m : ℕ} (hm1 : 1 ≤ m) {H : Polynomial ℤ}
    (hdeg : H.natDegree ≤ m - 1) :
    coeffVec (m + 1) H (Fin.last m) = 0 := by
  simp [coeffVec]
  have hlt : H.natDegree < m := lt_of_le_of_lt hdeg (by omega)
  exact_mod_cast (Polynomial.coeff_eq_zero_of_natDegree_lt hlt : H.coeff m = 0)

/-- extend the independent family `S` by vectors from the degree-`≤ m−1`
family `H` to a full independent family of size `m+1`. -/
lemma extended_family {m k : ℕ} (hkm : k ≤ m) (hm1 : 1 ≤ m)
    (S : Fin (k + 1) → Polynomial ℤ)
    (hdegS : ∀ i, (S i).natDegree ≤ m)
    (hSlin : LinearIndependent ℚ (fun i : Fin (k + 1) => coeffVec (m + 1) (S i)))
    (hSlead : ∃ i₀ : Fin (k + 1), (S i₀).natDegree = m)
    (H : Fin m → Polynomial ℤ)
    (hdegH : ∀ j, (H j).natDegree ≤ m - 1)
    (hHlin : LinearIndependent ℚ (fun j : Fin m => coeffVec (m + 1) (H j))) :
    ∃ (Ffam : Fin (m + 1) → Polynomial ℤ)
      (jmap : {t : Fin (m + 1) // k < (t : ℕ)} → Fin m),
      (∀ i : Fin (k + 1), Ffam ⟨(i : ℕ), by omega⟩ = S i) ∧
      (∀ (t : Fin (m + 1)) (ht : k < (t : ℕ)), Ffam t = H (jmap ⟨t, ht⟩)) ∧
      (∀ t : Fin (m + 1), (Ffam t).natDegree ≤ m) ∧
      LinIndepInt (m + 1) Ffam := by
  classical
  let u : Fin (k + 1) → Fin (m + 1) → ℚ := fun i => coeffVec (m + 1) (S i)
  let v : Fin m → Fin (m + 1) → ℚ := fun j => coeffVec (m + 1) (H j)
  have hu : LinearIndependent ℚ u := by simpa [u] using hSlin
  have hv : LinearIndependent ℚ v := by simpa [v] using hHlin
  have hlead : ∃ i₀ : Fin (k + 1), u i₀ (Fin.last m) ≠ 0 := by
    rcases hSlead with ⟨i₀, hi₀⟩
    refine ⟨i₀, ?_⟩
    dsimp [u]
    rw [coeffVec]
    have hc : (S i₀).coeff m ≠ 0 := coeff_m_ne_zero_of_natDegree_eq hm1 hi₀
    simpa [Fin.last] using hc
  have hvlast : ∀ j : Fin m, v j (Fin.last m) = 0 := by
    intro j
    dsimp [v]
    exact coeffVec_last_zero_of_deg_le hm1 (hdegH j)
  rcases ExtendFamily.exists_basis_extension hkm u hu hlead v hv hvlast with
    ⟨Fv, hFvpre, hFvextra, hFvlin⟩
  let jmap : {t : Fin (m + 1) // k < (t : ℕ)} → Fin m := fun it =>
    Classical.choose (hFvextra it.1 it.2)
  let Ffam : Fin (m + 1) → Polynomial ℤ := fun t =>
    if hle : (t : ℕ) ≤ k then S ⟨(t : ℕ), by omega⟩ else H (jmap ⟨t, by omega⟩)
  refine ⟨Ffam, jmap, ?_, ?_, ?_, ?_⟩
  · intro i
    have hik : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.isLt
    simp [Ffam, hik]
  · intro t ht
    have hn : ¬ (t : ℕ) ≤ k := by omega
    simp [Ffam, hn]
  · intro t
    by_cases ht : (t : ℕ) ≤ k
    · have hF : Ffam t = S ⟨(t : ℕ), by omega⟩ := by
        simp [Ffam, ht]
      rw [hF]
      exact hdegS ⟨(t : ℕ), by omega⟩
    · have ht' : k < (t : ℕ) := by omega
      have hF : Ffam t = H (jmap ⟨t, ht'⟩) := by
        simp [Ffam, ht]
      rw [hF]
      exact le_trans (hdegH _) (by omega : m - 1 ≤ m)
  · have hvec_eq : (fun t : Fin (m + 1) => coeffVec (m + 1) (Ffam t)) = Fv := by
      funext t
      by_cases ht : (t : ℕ) ≤ k
      · let i0 : Fin (k + 1) := ⟨(t : ℕ), by omega⟩
        have hF : Ffam t = S i0 := by
          simp [Ffam, ht, i0]
        calc
          coeffVec (m + 1) (Ffam t) = coeffVec (m + 1) (S i0) := by rw [hF]
          _ = u i0 := rfl
          _ = Fv ⟨(i0 : ℕ), by omega⟩ := (hFvpre i0).symm
          _ = Fv t := by
                have hI : (⟨(i0 : ℕ), by omega⟩ : Fin (m + 1)) = t := by
                  apply Fin.ext
                  simp [i0]
                rw [hI]
      · have ht' : k < (t : ℕ) := by omega
        let j0 : Fin m := jmap ⟨t, ht'⟩
        have hF : Ffam t = H j0 := by
          simp [Ffam, ht, j0]
        have hspec := Classical.choose_spec (hFvextra t ht')
        calc
          coeffVec (m + 1) (Ffam t) = coeffVec (m + 1) (H j0) := by rw [hF]
          _ = v j0 := rfl
          _ = Fv t := by
                simpa [j0] using hspec.symm
    change LinearIndependent ℚ (fun t : Fin (m + 1) => coeffVec (m + 1) (Ffam t))
    rw [hvec_eq]
    exact hFvlin

/-- case `k < m`: build the extended family via adjust/H and squeeze. -/
lemma second_squeeze_lt_m (C0 Cadj Crem : ℝ) (hC0pos : 0 < C0) (hCadjpos : 0 < Cadj)
    (hCrempos : 0 < Crem)
    (hsq0 : ∀ (m n : ℕ), 2 ≤ n → m ≤ n → ∀ (R : Polynomial ℤ), R ≠ 0 →
      (0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x R| ∂muSerre) →
      ∀ (Q : Fin (m + 1) → Polynomial ℤ), LinIndepInt (m + 1) Q →
        (∀ i, (Q i).natDegree ≤ m) →
      (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) *
          Submission.EnergyHalf.energy) ≤
        ∏ i : Fin (m + 1), wnorm n (zmap (Q i) * zmap R))
    (hadj0 : ∀ (n : ℕ), 2 ≤ n → ∀ (Q : Polynomial ℤ), Q ≠ 0 → Q.natDegree = n →
      ∀ (α : Fin n → ℂ), Function.Injective α →
        Q.map (algebraMap ℤ ℂ) = Polynomial.C (Q.leadingCoeff : ℂ) *
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) →
      ∀ (P : Polynomial ℝ), P.natDegree ≤ n - 1 →
        ∃ (R : Polynomial ℤ) (β : Fin n → ℂ),
          R.natDegree ≤ n - 1 ∧
          P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ) =
            ∑ i : Fin n, β i • qDiv Q (α i) ∧
          (∑ i : Fin n, ‖β i‖ ≤ (n : ℝ) ^ Cadj))
    (hrem0 : ∀ (N m : ℕ), 1 ≤ m → ∀ (P : Polynomial ℂ), P.natDegree = m →
      ∀ (α : ℂ), P.eval α = 0 →
        ∃ (Q : Polynomial ℂ), P = (Polynomial.X - Polynomial.C α) * Q ∧
          cwnorm N Q ≤ ((2 * max N m : ℕ) : ℝ) ^ Crem * cwnorm N P)
    {k m n : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n) (hn2 : 2 ≤ n)
    (hkm_lt : k < m)
    (Q : Fin (m + 1) → Polynomial ℤ) (hQlin : FullIndepPoly (m + 1) Q)
    (hQdeg : ∀ i : Fin (m + 1), (Q i).natDegree ≤ n)
    (hord : ∀ i : Fin m, wnorm n (zmap (Q (Fin.castSucc i))) ≤
      wnorm n (zmap (Q (Fin.succ i))))
    (G : Polynomial ℤ) (hG : G ≠ 0)
    (hGint : 0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x G| ∂muSerre)
    (S : Fin (k + 1) → Polynomial ℤ)
    (hdiv : ∀ i : Fin (k + 1), Q (pre hkm i) = G * S i)
    (hnc : ∀ z : ℂ, ¬ (∀ i : Fin (k + 1), Polynomial.aeval z (S i) = 0))
    (hdegS : ∀ i : Fin (k + 1), (S i).natDegree ≤ m)
    (hleadS : ∃ i₀ : Fin (k + 1), (S i₀).natDegree = m) :
    (n : ℝ) ^ (-(sqC C0 Cadj Crem (-Submission.EnergyHalf.energy)) * (n : ℝ)) *
        Real.exp (((m : ℝ) * (n : ℝ) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
          Submission.EnergyHalf.energy) ≤
      ∏ i : Fin (m + 1), wnorm n (zmap (Q i)) := by
  classical
  let e0 : ℝ := -Submission.EnergyHalf.energy
  have he0 : 0 ≤ e0 := by
    dsimp [e0]
    linarith [Submission.Contract1Core.energy_nonpos]
  have hE : Submission.EnergyHalf.energy = -e0 := by
    simp [e0]
  let Ctot : ℝ := sqC C0 Cadj Crem e0
  let p : ℝ := sqp0 Cadj Crem n m k
  let wnQk : ℝ := wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩))
  let bnd : ℝ := ((((k + 1) * (2 * m + 1) : ℕ) : ℝ) * wnQk)
  have hCadj0 : 0 ≤ Cadj := le_of_lt hCadjpos
  have hCrem0 : 0 ≤ Crem := le_of_lt hCrempos
  have hpm1 : 1 ≤ m := by omega
  have hpm2 : 2 ≤ m := by omega
  have hCtot : Ctot = sqC C0 Cadj Crem e0 := rfl
  have hp_pos : 0 < p := by
    simpa [p] using (sqp0_pos Cadj Crem hn2 hpm1)
  have hp_ge : 1 ≤ p := by
    simpa [p] using (sqp0_ge_one (Cadj := Cadj) (Crem := Crem) hn2 hpm1 hCadj0 hCrem0)
  rcases combination_data (k := k) (m := m) (n := n) hk1 hkm Q hQlin hord G S hdiv hnc
    hdegS hleadS with ⟨A, b, hA0, hdegA, hsepA, hb_le, hcomb⟩
  have hRD : RootDataOf A m := root_data_of_separable (n := m) hpm1 A hA0 hdegA hsepA
  rcases hRD with ⟨α, hαinj, hαfac⟩
  rcases hleadS with ⟨i0, hi0deg⟩
  have hSnz : ∀ i : Fin (k + 1), S i ≠ 0 := S_ne_zero_of hkm Q hQlin G S hdiv
  have hdegQ_i0 : (Q (pre hkm i0)).natDegree ≤ n := hQdeg (pre hkm i0)
  have hdegGS : (G * S i0).natDegree = G.natDegree + m := by
    rw [Polynomial.natDegree_mul hG (hSnz i0), hi0deg]
  have hdeg_sum : G.natDegree + m ≤ n := by
    have hh : (Q (pre hkm i0)).natDegree ≤ n := hdegQ_i0
    rw [hdiv i0] at hh
    rwa [hdegGS] at hh
  have hdAG : (A * G).natDegree = G.natDegree + m := by
    rw [Polynomial.natDegree_mul hA0 hG, hdegA]
    rw [Nat.add_comm]
  have hdegAG : (A * G).natDegree ≤ n := by
    rw [hdAG]
    exact hdeg_sum
  have hdegAG1 : 1 ≤ (A * G).natDegree := by
    rw [hdAG]
    omega
  rcases hj_family_full hpm2 hadj0 A hA0 hdegA α hαinj hαfac with
    ⟨H, R, β, hHdef, hdegH, hHid, hβsum, hmod2⟩
  have hHlin_m : LinearIndependent ℚ (fun j : Fin m => coeffVec m (H j)) :=
    ModTwoIndep.linIndep_coeffVec H hdegH hmod2
  have hHlin : LinearIndependent ℚ (fun j : Fin m => coeffVec (m + 1) (H j)) :=
    ModTwoIndep.linIndep_coeffVec_succ H hdegH hmod2
  have hSlin : LinearIndependent ℚ (fun i : Fin (k + 1) => coeffVec (m + 1) (S i)) :=
    linIndep_S hkm Q hQlin G S hdiv hdegS
  rcases extended_family hkm hpm1 S hdegS hSlin ⟨i0, hi0deg⟩ H hdegH hHlin with
    ⟨Ffam, jmap, hFpre, hFextra, hFdeg, hFlin⟩
  have hAwn : wnorm n (zmap (A * G)) ≤ bnd := by
    dsimp [bnd, wnQk]
    calc
      wnorm n (zmap (A * G)) = wnorm n (zmap (G * A)) := by
            congr 1
            rw [mul_comm]
      _ ≤ (((k + 1) * (2 * m + 1) : ℕ) : ℝ) * wnorm n (zmap (Q ⟨k, Nat.lt_succ_of_le hkm⟩)) := hcomb
  have hbnd0 : 0 ≤ bnd := by
    dsimp [bnd]
    exact mul_nonneg (by positivity) (wnorm_nonneg _ _)
  let Aq : Fin (m + 1) → ℝ := fun t => wnorm n (zmap (Ffam t) * zmap G)
  let B : Fin (m + 1) → ℝ := fun t => wnorm n (zmap (Q t))
  have hAq0 : ∀ t, 0 ≤ Aq t := by intro t; dsimp [Aq]; exact wnorm_nonneg _ _
  have hBq0 : ∀ t, 0 ≤ B t := by intro t; dsimp [B]; exact wnorm_nonneg _ _
  have hAB : ∀ t, Aq t ≤ p * B t := by
    intro t
    by_cases hle : (t : ℕ) ≤ k
    · let i : Fin (k + 1) := ⟨(t : ℕ), by omega⟩
      have hF : Ffam t = S i := by
        have hI : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = t := by
          apply Fin.ext
          simp [i]
        simpa [hI] using (hFpre i)
      have hpre_t : pre hkm i = t := by
        apply Fin.ext
        simp [pre, i]
      have hAeqB : Aq t = B t := by
        dsimp [Aq, B]
        calc
          wnorm n (zmap (Ffam t) * zmap G)
              = wnorm n (zmap (S i) * zmap G) := by rw [hF]
          _ = wnorm n (zmap (S i * G)) := by simp [zmap]
          _ = wnorm n (zmap (Q (pre hkm i))) := by
                have hz : zmap (S i * G) = zmap (Q (pre hkm i)) := by
                  rw [hdiv i]
                  simp [zmap, mul_comm]
                rw [hz]
          _ = wnorm n (zmap (Q t)) := by rw [hpre_t]
      calc
        Aq t = B t := hAeqB
        _ ≤ p * B t := by
          simpa [one_mul] using (mul_le_mul_of_nonneg_right hp_ge (hBq0 t))
    · have ht : k < (t : ℕ) := by omega
      let j : Fin m := jmap ⟨t, ht⟩
      have hF : Ffam t = H j := by
        simpa [j] using (hFextra t ht)
      have hwnk_le : wnQk ≤ B t := by
        dsimp [wnQk, B]
        have ha : k ≤ m := hkm
        have hb : (t : ℕ) ≤ m := by omega
        have hab : k ≤ (t : ℕ) := le_of_lt ht
        exact wn_chain (Q := Q) hord ha hb hab
      have hjm : ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j) : Polynomial ℤ).map (algebraMap ℤ ℂ) =
          (2 : ℂ) • (∑ i : Fin m, β j i • qDiv A (α i)) := by
        simpa [hHdef j] using (hHid j)
      have hβj : (∑ i : Fin m, ‖β j i‖) ≤ (m : ℝ) ^ Cadj := hβsum j
      have hbij := HjBound.hj_wn_bound (n := n) (m := m) (k := k) hmn hn2
        (Cadj := Cadj) (Crem := Crem) hCadj0 hCrem0 (hrem := hrem0)
        A G hA0 hdegA hG hdegAG hdegAG1 α hαfac (bnd := bnd) hbnd0 hAwn
        (j := j) (R := R j) (β := β j) hβj hjm
      have hbij' : wnorm n (zmap ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j) * G)) ≤ p * wnQk := by
        calc
          wnorm n (zmap ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j) * G))
              ≤ 2 * (m : ℝ) ^ Cadj * (((2 * n : ℕ) : ℝ) ^ Crem) * bnd := hbij
          _ = p * wnQk := by
                dsimp [bnd, wnQk, p, sqp0]
                ring
      calc
        Aq t = wnorm n (zmap (H j) * zmap G) := by dsimp [Aq]; rw [hF]
        _ = wnorm n (zmap ((Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j) * G)) := by
              have hd2 : H j = Polynomial.X ^ (j : ℕ) - (2 : ℤ) • R j := hHdef j
              rw [hd2]
              simp [zmap]
        _ ≤ p * wnQk := hbij'
        _ ≤ p * B t := by
              exact mul_le_mul_of_nonneg_left hwnk_le (le_of_lt hp_pos)
  have hsq : (n : ℝ) ^ (-C0 * (n : ℝ)) *
        Real.exp (((m : ℝ) + 1) * ((n : ℝ) - (m : ℝ) / 2) * Submission.EnergyHalf.energy) ≤
      ∏ t : Fin (m + 1), Aq t := by
    have hs := hsq0 m n hn2 hmn G hG hGint Ffam hFlin hFdeg
    simpa [Aq] using hs
  have hfinal := final_conclude (k := k) (m := m) (n := n) hk1 hkm hmn hn2 (le_of_lt hC0pos)
    hCadj0 hCrem0 he0 hCtot hAq0 hBq0 hAB hsq hE
  simpa [Ctot, e0, Aq, B] using hfinal


/-- instantiate the three data theorems. -/
lemma second_squeeze_from_data : secondSqueezeProp := by
  classical
  rcases Submission.Contract1Core.squeeze with ⟨C0, hC0pos, hsq0⟩
  rcases Submission.AdjustLemma.adjust_lemma with ⟨Cadj, hCadjpos, hadj0⟩
  rcases Submission.RemezComplex.complex_remez with ⟨Crem, hCrempos, hrem0⟩
  let hadj' : ∀ (n : ℕ), 2 ≤ n → ∀ (Q : Polynomial ℤ), Q ≠ 0 → Q.natDegree = n →
      ∀ (α : Fin n → ℂ), Function.Injective α →
        Q.map (algebraMap ℤ ℂ) = Polynomial.C (Q.leadingCoeff : ℂ) *
          ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) →
      ∀ (P : Polynomial ℝ), P.natDegree ≤ n - 1 →
        ∃ (R : Polynomial ℤ) (β : Fin n → ℂ),
          R.natDegree ≤ n - 1 ∧
          P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ) =
            ∑ i : Fin n, β i • qDiv Q (α i) ∧
          (∑ i : Fin n, ‖β i‖ ≤ (n : ℝ) ^ Cadj) := by
    intro n hn Q hQ0 hdegQn α hinj hfac P hdegP
    rcases hadj0 n hn Q hQ0 hdegQn α hinj hfac P hdegP with ⟨R, β, h1, h2, h3, _h4⟩
    exact ⟨R, β, h1, h2, h3⟩
  refine ⟨sqC C0 Cadj Crem (-Submission.EnergyHalf.energy), ?pos, ?body⟩
  · have he0 : 0 ≤ -Submission.EnergyHalf.energy := by
      linarith [Submission.Contract1Core.energy_nonpos]
    exact sqC_pos hC0pos (le_of_lt hCadjpos) (le_of_lt hCrempos) he0
  · intro k m n hk1 hkm hmn hn2 Q hQlin hQdeg hord G hG hGint S hdiv hnc hdegS hleadS
    by_cases hmk : m ≤ k
    · exact second_squeeze_eq_m C0 Cadj Crem hC0pos hCadjpos hCrempos hsq0 hk1 hkm hmn
        hn2 hmk Q hQlin hQdeg hord G hG hGint S hdiv hnc hdegS hleadS
    · have hlt : k < m := by omega
      exact second_squeeze_lt_m C0 Cadj Crem hC0pos hCadjpos hCrempos hsq0 hadj' hrem0
        hk1 hkm hmn hn2 hlt Q hQlin hQdeg hord G hG hGint S hdiv hnc hdegS hleadS

/-- MAIN RESULT. -/
theorem second_squeeze : secondSqueezeProp := by
  exact second_squeeze_from_data

end Submission.SecondSqueeze
