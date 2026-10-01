import Mathlib
import Submission.Work.LinnikBurgess.DdBits

/-!
# Vocabulary for the singleton-pair sixth-moment bound (`r = 3`, moduli divisible by a cube)

This module collects the definitions used by `Work.LinnikBurgess.singleton_sum_nonCubefree`
and its helper lemmas.  All of it is stated in terms of the six shifts
`v = ![a 0, a 1, a 2, b 0, b 1, b 2]` attached to a pair of triples `(a, b)`.

* `shift`  : the six shifts as natural numbers.
* `ddDefect`: the `p`-adic criticality defect `∑ (r+a_l)⁻¹ - ∑ (r+b_l)⁻¹ ∈ ZMod (p^e)`.
* `IsDD`   : `r` is a *doubly degenerate* critical class: all six shifts are units mod `p`,
             the two triples of inverses agree to first and second order mod `p`, and
             `p^2` divides the defect.
* `IsDDLevel` : a DD class whose defect has `p`-adic valuation exactly `j`.
* `IsDDHigh`  : a DD class whose defect is divisible by `p^(e-1)`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The six shifts `a 0, a 1, a 2, b 0, b 1, b 2` attached to a pair of triples, as naturals. -/
noncomputable def shift (a b : Fin 3 → ℕ) : Fin 6 → ℕ :=
  ![a 0, a 1, a 2, b 0, b 1, b 2]

/-- The `p`-adic criticality defect of the pair `(a,b)` at the class `r`. -/
noncomputable def ddDefect (p e : ℕ) (a b : Fin 3 → ℕ) (r : ZMod p) : ZMod (p ^ e) :=
  (∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ))⁻¹)
    - (∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))⁻¹)

/-- `r` is a *doubly degenerate* critical class for the pair `(a,b)` modulo `p^e`: all six shifts
`r + a l`, `r + b l` are units mod `p`, the two triples of inverses agree to first and second order
mod `p`, and `p ^ 2` divides the `p`-adic defect. -/
def IsDD (p e : ℕ) (a b : Fin 3 → ℕ) (r : ZMod p) : Prop :=
  (∀ l : Fin 3, (r + (a l : ZMod p)) ≠ 0 ∧ (r + (b l : ZMod p)) ≠ 0)
  ∧ (∑ l : Fin 3, (r + (a l : ZMod p))⁻¹) = (∑ l : Fin 3, (r + (b l : ZMod p))⁻¹)
  ∧ (∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹) ^ 2)
      = (∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹) ^ 2)
  ∧ (p ^ 2 ∣ (ddDefect p e a b r).val)

/-- A doubly degenerate critical class of *exact level* `j`: the defect has `p`-adic valuation `j`. -/
def IsDDLevel (p e : ℕ) (a b : Fin 3 → ℕ) (r : ZMod p) (j : ℕ) : Prop :=
  IsDD p e a b r ∧ p ^ j ∣ (ddDefect p e a b r).val
    ∧ ¬ (p ^ (j + 1) ∣ (ddDefect p e a b r).val)

/-- A doubly degenerate critical class of *high* level: the defect is divisible by `p^(e-1)`. -/
def IsDDHigh (p e : ℕ) (a b : Fin 3 → ℕ) (r : ZMod p) : Prop :=
  IsDD p e a b r ∧ p ^ (e - 1) ∣ (ddDefect p e a b r).val

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The six shifts of a pair `q = (f,g)` of triples of residues, lifted to `ℕ`. -/
noncomputable def pairVec {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Fin 6 → ℕ :=
  shift (fun l => ((q.1 l : Fin H) : ℕ)) (fun l => ((q.2 l : Fin H) : ℕ))

/-- The `i`-th shift of the pair is unique among the six (the pair is a *singleton* pair with
unique index `i`). -/
def PairUnique {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) (i : Fin 6) : Prop :=
  ∀ l ∈ Finset.univ.erase i, pairVec q l ≠ pairVec q i

/-- The pair `q` carries a doubly degenerate critical class modulo `p` (with defect computed in
`ZMod (p^e)`). -/
def PairIsDD {H : ℕ} (p e : ℕ) (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ r : ZMod p,
    IsDD p e (fun l => ((q.1 l : Fin H) : ℕ)) (fun l => ((q.2 l : Fin H) : ℕ)) r

/-- The pair `q` carries a doubly degenerate critical class modulo `p` whose defect is divisible
by `p^j` (i.e. the degeneracy level is at least `j`). -/
def PairIsDDLevel {H : ℕ} (p e j : ℕ) (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ r : ZMod p,
    IsDD p e (fun l => ((q.1 l : Fin H) : ℕ)) (fun l => ((q.2 l : Fin H) : ℕ)) r
      ∧ p ^ j ∣ (ddDefect p e (fun l => ((q.1 l : Fin H) : ℕ))
          (fun l => ((q.2 l : Fin H) : ℕ)) r).val

/-- The weighted `gcd` factor attached to the unique index `i` of a pair,
`∏_{l ≠ i} gcd N |v_i - v_l|`. -/
noncomputable def gcdWeight {H : ℕ} (N : ℕ) (i : Fin 6)
    (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : ℝ :=
  ∏ l ∈ Finset.univ.erase i,
    ((Nat.gcd N (((pairVec q i : ℤ) - (pairVec q l : ℤ)).natAbs) : ℕ) : ℝ)

/-- The set of pairs `q` whose `i`-th shift is unique and which carry a doubly degenerate critical
class modulo each `p ∈ s` with degeneracy level at least `j p`. -/
noncomputable def ddPairSet (s : Finset ℕ) (j e : ℕ → ℕ) (H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q => PairUnique q i ∧ ∀ p ∈ s, PairIsDDLevel p (e p) (j p) q)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The graded doubly-degenerate correction at a prime power `p^e`: for each level `j` at which the
pair `(a,b)` carries a doubly degenerate critical class modulo `p` of *exact* level `j`, the term
`p^(j/2)`; and, if a class of *high* level (defect divisible by `p^(e-1)`) exists, the term
`p^((e-2)/2)`. -/
noncomputable def ddCorr (p e : ℕ) (a b : Fin 3 → ℕ) : ℝ := by
  classical
  exact (∑ j ∈ Finset.Icc 2 (e - 2),
      if ∃ r : ZMod p, IsDDLevel p e a b r j then (p : ℝ) ^ ((j : ℝ) / 2) else 0)
    + (if ∃ r : ZMod p, IsDDHigh p e a b r then (p : ℝ) ^ (((e : ℝ) - 2) / 2) else 0)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The `k`-th power-sum defect of the pair `(a,b)` at the class `r`:
`∑_l (r+a_l)^{-k} - ∑_l (r+b_l)^{-k}`, taken in `ZMod (p^e)`.

`IsDD` uses `k = 1`; the *refuted* `D₁`-grading is replaced by reading off the whole sequence
`(ddDefectK p e a b r k)_k`, which is what governs the size of the level sum (the level sum is a
`p`-adic exponential sum whose leading term is the lowest-degree term with the least `p`-adic
valuation, cf. `Θ_k ∼ p^{k-3} (k')⁻¹ D_k`). -/
noncomputable def ddDefectK (p e : ℕ) (a b : Fin 3 → ℕ) (r : ZMod p) (k : ℕ) : ZMod (p ^ e) :=
  (∑ l : Fin 3, ((((r.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ))⁻¹) ^ k)
    - (∑ l : Fin 3, ((((r.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))⁻¹) ^ k)

/-- The pair carries a *cubic* doubly-degenerate class: a DD class `r` at which the third
power-sum defect is a `p`-unit.  By the expansion of the level-`1` phase this makes the cubic term
the leading one, so the level sum is a genuine cubic `p`-adic exponential sum. -/
def IsDDCubic (p e : ℕ) (a b : Fin 3 → ℕ) (r : ZMod p) : Prop :=
  IsDD p e a b r ∧ ¬ (p ∣ (ddDefectK p e a b r 3).val)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **RETRACTED** (do not consume).  `ddCorrCubic` fires only for *cubic* DD classes (`D₃ ≢ 0 mod p`),
but `IsDDCubic` is not automatic for DD pairs: with the uniqueness hypothesis the two *triples* may
be congruent mod `p` (only the six *integers* must be distinct), so a DD pair can have
`D₁ ≡ … ≡ D_m ≡ 0 (mod p)` and then a higher-degree term leads.  Since
`|∑_{z mod p^k} e(z^d/p^k)| = p^{k(1-1/d)}` *increases* with `d`, a fixed cubic correction is wrong;
the correction must be graded by the Weyl degree `d` (`local_corr6_weyl`, `PairIsDDWeyl`).
Kept only as the historical definition.

The (withdrawn) doubly-degenerate correction at a prime power `p^e`: `p^(e/6)` when the pair
carries a cubic DD class (`IsDDCubic`), and `0` otherwise.

This replaces the refuted `ddCorr` (which graded by `v_p(D₁)` alone).  The exponent `e/6` is
exactly the scale of the extremal family: the level sum is a cubic `p`-adic Weyl sum of size
`p^{2(e-3)/3}`, so the correlation is `p^{2e/3} = p^{e/2} · p^{e/6}`.  For `e = 3` it also agrees
with the proved `charCorrelation6_cube_local` (`100 p^{3/2}(PG + p^{1/2})`). -/
noncomputable def ddCorrCubic (p e : ℕ) (a b : Fin 3 → ℕ) : ℝ := by
  classical
  exact if ∃ r : ZMod p, IsDDCubic p e a b r then (p : ℝ) ^ ((e : ℝ) / 6) else 0

end Work.LinnikBurgess


namespace Work.LinnikBurgess

/-- The pair `q` carries a DD class of *Weyl degree at least* `d`: a doubly degenerate critical
class `r` whose defect sequence satisfies `p ∣ D_j(r)` for all `1 ≤ j ≤ d - 1`
(`D_j = ddDefectK p e a b r j`).

The degree is the invariant that governs *both* the size of the level sum (a `d`-th power
`p`-adic Weyl sum, of size `p^{2 + (e-3)(1-1/d)}` for the correlation) and its density
(`d - 1` independent congruences, hence `p^{-(d-1)}`), via Newton's identities. -/
def PairIsDDWeyl {H : ℕ} (p e d : ℕ) (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ r : ZMod p,
    IsDD p e (fun l => ((q.1 l : Fin H) : ℕ)) (fun l => ((q.2 l : Fin H) : ℕ)) r
      ∧ ∀ j : ℕ, 1 ≤ j → j ≤ d - 1 →
          p ∣ (ddDefectK p e (fun l => ((q.1 l : Fin H) : ℕ))
                (fun l => ((q.2 l : Fin H) : ℕ)) r j).val

/-- The set of pairs whose `i`-th shift is unique and which carry a DD class of Weyl degree at
least `d`. -/
noncomputable def ddWeylSet (p e d H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q => PairUnique q i ∧ PairIsDDWeyl p e d q)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- A triple is **cube-progressive** modulo `p`: its residues satisfy `e₁ ≡ e₂ ≡ 0`, equivalently
(Newton, `p ≠ 2`) `Σ t_l ≡ Σ t_l² ≡ 0`.  Then the residues are the roots of `X³ = e₃`, i.e.
`{t, tω, tω²}` when `p ≡ 1 (mod 3)` (`(t, tω, tω²)` with `ω` a primitive cube root of 1).

This is the residue structure of the extremal family for the cubic Weyl sum
(`(y+p)³ = p³ ± 1`), i.e. the locus on which the cubic unit part `U(3j)` vanishes and the level sum
attains its maximal size `p^{2e/3}`. -/
def IsCubeProg (p : ℕ) (t : Fin 3 → ℕ) : Prop :=
  (∑ l : Fin 3, ((t l : ℕ) : ZMod p)) = 0 ∧ (∑ l : Fin 3, (((t l : ℕ) : ZMod p)) ^ 2) = 0

/-- The set of pairs whose `i`-th shift is unique and whose two triples are both cube-progressive
modulo `p` — the extremal locus for the cubic doubly-degenerate case. -/
noncomputable def cubeProgSet (p H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q =>
    PairUnique q i
      ∧ IsCubeProg p (fun l => ((q.1 l : Fin H) : ℕ))
      ∧ IsCubeProg p (fun l => ((q.2 l : Fin H) : ℕ)))

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- Cube-progressiveness stated directly on residues: `Σ t_l = Σ t_l² = 0` in `ZMod p`. -/
def IsCubeProgZ (p : ℕ) (t : Fin 3 → ZMod p) : Prop :=
  (∑ l : Fin 3, t l) = 0 ∧ (∑ l : Fin 3, (t l) ^ 2) = 0

/-- **The extremal locus of the cubic doubly-degenerate case.**  The pair carries a DD class `r`
such that *both shifted triples* `{r + a_l}` and `{r + b_l}` are cube-progressive.

This is the exact locus on which the peeled level sum is a *pure* cubic Weyl sum and attains its
maximal size `p^{2k/3}` (`k = e - 3`): the phase's expansion coefficients are the power sums of the
units `A_l = (r+a_l)⁻¹`, and cube-progressiveness of the shifted triples forces `ΣA_l ≡ ΣA_l² ≡ 0`,
killing the `w`-linear and `w`-quadratic coefficients.  `cubeProgSet` (raw triples) is the `r = 0`
slice, realised by the family `(y+p)³ = p³ ± 1`. -/
def PairExtremal {H : ℕ} (p e : ℕ) (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ r : ZMod p,
    IsDD p e (fun l => ((q.1 l : Fin H) : ℕ)) (fun l => ((q.2 l : Fin H) : ℕ)) r
      ∧ IsCubeProgZ p (fun l => r + (((q.1 l : Fin H) : ℕ) : ZMod p))
      ∧ IsCubeProgZ p (fun l => r + (((q.2 l : Fin H) : ℕ) : ZMod p))

/-- The set of pairs with unique index `i` lying in the extremal locus `PairExtremal p e`. -/
noncomputable def extremalSet (p e H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q => PairUnique q i ∧ PairExtremal p e q)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The `gcd`-weighted count over the pairs whose `i`-th shift is unique.  This is the `S = ∅` term
of the assembly: by `bmr3sc_sum_prod_gcd_diff_le` (Commons) it is `≤ 32 H⁶ τ(q)⁵`, the transport
from that lemma's sum over vectors `w : Fin 6 → Fin H` to pairs being the bijection `pairVec`. -/
noncomputable def gcdWeightSum (q H : ℕ) (i : Fin 6) : ℝ := by
  classical
  exact ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
    (if PairUnique p i then gcdWeight q i p else 0)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The *local* `gcd` weight at a single prime `p` of `q`: `∏_{l ≠ i} gcd (p^{e_p}) |v_i - v_l|`,
with `e_p = q.factorization p`.  These are the factors `PG_p` of the assembly's local bounds, and
`∏_{p | q} PG_p = gcdWeight q i q'`. -/
noncomputable def localPG {H : ℕ} (q : ℕ) (p : ℕ) (i : Fin 6)
    (q' : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : ℝ :=
  ∏ l ∈ Finset.univ.erase i,
    ((Nat.gcd (p ^ q.factorization p)
      (((pairVec q' i : ℤ) - (pairVec q' l : ℤ)).natAbs) : ℕ) : ℝ)

/-- The complementary modulus attached to a set `S` of primes of `q`:
`N_S = q / ∏_{p ∈ S} p^{factorization q p}`.  For `S = {p}` this is `q / p^{e_p}` and for
`S = {p, p'}` it is `q / (p^{e_p} p'^{e_{p'}})` — the same reading at every `|S|`. -/
def complMod (q : ℕ) (S : Finset ℕ) : ℕ :=
  q / ∏ p ∈ S, p ^ q.factorization p

/-- The assembly's `S ≠ ∅` term: over a set `S` of prime divisors of `q`, the product of the local
corrections `D` at the primes of `S`, weighted by the `gcd` weight at the complementary modulus
`N_S = complMod q S`.  This is the summand of the subset expansion in `prod_add_expand` after
`∏_{p ∉ S} PG_p` has been collapsed to `gcdWeight N_S`. -/
noncomputable def extremalTermSum {H : ℕ} (q : ℕ) (S : Finset ℕ) (D : ℕ → ℝ) (i : Fin 6) : ℝ := by
  classical
  exact ∑ q' : (Fin 3 → Fin H) × (Fin 3 → Fin H),
    (∏ p ∈ S, D p) * (if PairUnique q' i then gcdWeight (complMod q S) i q' else 0)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The pair is in the extremal locus at *every* prime of `S` simultaneously (with the respective
exponents `e p`).  This is the `|S| ≥ 2` analogue of `PairExtremal`: the count-side quantity whose
density should multiply as `∏_{p ∈ S} p⁻⁴`. -/
def PairExtremalAll {H : ℕ} (S : Finset ℕ) (e : ℕ → ℕ)
    (q' : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∀ p ∈ S, PairExtremal p (e p) q'

/-- The set of pairs with unique index `i` lying in the joint extremal locus of `S`. -/
noncomputable def extremalJointSet (S : Finset ℕ) (e : ℕ → ℕ) (H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q' => PairUnique q' i ∧ PairExtremalAll S e q')

end Work.LinnikBurgess


namespace Work.LinnikBurgess

/-- The local correction at a single prime `p` of `q`: `p^{e_p/6}` on the extremal locus
(`PairExtremal`, i.e. a DD class with both *shifted* triples cube-progressive) and `0` otherwise.
Together with `localPG` this is the local factor of the CRT product bound. -/
noncomputable def localCorr {H : ℕ} (q : ℕ) (p : ℕ) (i : Fin 6)
    (q' : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : ℝ := by
  classical
  exact (p : ℝ) ^ ((q.factorization p : ℝ) / 6)
    * (if PairExtremal p (q.factorization p) q' then 1 else 0)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **The corrected extremal locus.**  The pair carries a doubly degenerate critical class `r` at
which the *second* power-sum defect `Δ₂ = ddDefectK p e a b r 2` is divisible by `p²`.

This replaces the `PairExtremal` (shifted cube-progressive) reading.  The peeled level sum at a DD
class `r` is `p · Tsum(p^{e-3}, H)` with phase `H = βX + γX² + δX³`, where
`γ ≡ E₂/p (mod p)`, `E₂ = (Δ₁² - Δ₂)/2`; so `γ` is a *unit* exactly when `p² ∤ Δ₂`
(the branch covered by `weyl_cubic_unit_quad`), while `p² ∣ Δ₂` makes the cubic term lead and the
level sum reach `≍ p^{2e/3 - 1}`.  Cube-progressiveness of the shifted triples is *sufficient* for
this but not equivalent, so it under-describes the locus. -/
def PairDDDelta2 {H : ℕ} (p e : ℕ) (q' : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ r : ZMod p,
    IsDD p e (fun l => ((q'.1 l : Fin H) : ℕ)) (fun l => ((q'.2 l : Fin H) : ℕ)) r
      ∧ p ^ 2 ∣ (ddDefectK p e (fun l => ((q'.1 l : Fin H) : ℕ))
          (fun l => ((q'.2 l : Fin H) : ℕ)) r 2).val

/-- The set of pairs with unique index `i` lying in the corrected extremal locus
(`p² ∣ Δ₂` at the DD class). -/
noncomputable def ddDelta2Set (p e H : ℕ) (i : Fin 6) :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q' => PairUnique q' i ∧ PairDDDelta2 p e q')

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **The re-keyed local correction.**  At a prime `p` of `q`, the correction is `p^{e_p/6}` on the
*corrected* extremal locus `PairDDDelta2` (a DD class `r` with `p² ∣ Δ₂(r)`) and `0` off it.

This supersedes `localCorr` (keyed on the sufficient-but-not-necessary `PairExtremal` locus): by the
reviewers' computation `γ ≡ E₂/p` with `E₂ = (Δ₁² − Δ₂)/2`, so `p² ∤ Δ₂` is exactly the
nondegenerate branch covered by the proved `weyl_cubic_unit_quad`, and `p² ∣ Δ₂` is the branch whose
count is `ddDelta2_count` (`L470`).  Together with `localPG` this is the local factor of the CRT
product bound in its corrected indexing. -/
noncomputable def localCorrDelta2 {H : ℕ} (q : ℕ) (p : ℕ) (i : Fin 6)
    (q' : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : ℝ := by
  classical
  exact (p : ℝ) ^ ((q.factorization p : ℝ) / 6)
    * (if PairDDDelta2 p (q.factorization p) q' then 1 else 0)

end Work.LinnikBurgess
