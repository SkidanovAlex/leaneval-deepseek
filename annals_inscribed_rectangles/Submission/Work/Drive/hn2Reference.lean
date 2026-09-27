import Mathlib
import Submission.Work.Drive.hn2CountInterface
import Submission.Work.Drive.orderTripleParity
import Submission.Work.Drive.blockFactorIdentification
import Submission.Work.Drive.tripleProductIdentity

/-!
# `hn2` from the **reference triple**: the pair analogue of the design's `Lemma 4` assembly

`HN2_MIXED_FACTOR_STATUS.md` §2–§3 and `F1_GENERICITY_RESOLUTION.md` §7 record the reduction of
`hn2` (Hugelmeyer's Lemma 3, the antisymmetry of the side function) to the **reference triple**

> `(P 0, P 1, P 2) = (the rotated configuration at the angle `u 0`, the rotated configuration at `u 1`,
>   the linear reference plane above all levels)`,

run at a *coupled perturbation parameter* `τ` (block `k` perturbed by `τ k`).  The reference triple is
the exact analogue of the design's triple of `Work.Drive.sum_CntAt_products_eq_one_of_blockT6`
(`perturbedTripleIdentity.lean`), except that the *reference* block replaces the third rotated
configuration block: its two factors vanish by the **levels** (Hugelmeyer's `n_{-λ} = 0`), and the two
*mixed* factors — the pairing of a configuration block with the reference plane — are odd (the
`(F1)` theorem, `Work.Drive.exists_delta_odd_coreSideCountPt_mixed`).

This file performs the **assembly** of that computation:

1. `Work.Drive.pairParity_of_threeBlockT6` — the pure parity algebra: from the oddness of the total top
   count, the three block multiplicativities T6, the vanishing of the reference block's two factors and
   the oddness of the two mixed factors, the two *configuration* factors satisfy
   `f 0 1 + f 1 0 = 1` in `ZMod 2`.  (In the paper's language: the four-face count `n_P + n_Q ≡ 1`.)
2. `Work.Drive.cntAt_pair_eq_one_of_threeBlockT6` — the same with the two configuration factors
   identified with the germ's own counts `CntAt Ξ Q (cblk 1) (u 1 - u 0) (τ 0, τ 1)` and
   `CntAt Ξ Q (cblk 0) (u 0 - u 1) (τ 1, τ 0)` (the identification is
   `Work.Drive.coreSideCount_block_eq_CntAt`, so the consumer passes it as the two equalities `hg01`,
   `hg10` of the hypothesis).
3. `Work.Drive.sideGerm_add_neg_eq_one_of_counts_of_refTriple` — the composition with the germ
   dictionary `Work.Drive.sideGerm_add_neg_eq_one_of_counts` (`hn2CountInterface.lean`), which turns the
   count parity at good parameters into the germ antisymmetry at the angle `u 1 - u 0`.

The hypotheses left explicit are exactly the four heavier inputs of the lane, in the shape its other
files deliver them:

* `htop` — the engine plus the ends clause at the reference triple
  (`Work.Drive.odd_sum_topBdryMeet_of_ends`, with `Meet3Hyp` from
  `Work.Drive.meet3Hyp_of_classTripleRegular` and the ends clause from
  `Work.Drive.odd_sum_bottomBdryMeet_of_classTriple` / `…_of_hasClassLinearization`);
* `hblock` — the transport's multiplicity T6 at the three blocks (block `0`, `1`: the transported
  configuration blocks; block `2`: the reference chart against the two configuration planes);
* `h20`, `h21` — the **vanishing of the reference block's factors** by levels
  (`Work.Drive.not_odd_coreSideCount_reference`, proved);
* `h02`, `h12` — the **mixed factors** (`(F1)`, `Work.Drive.exists_delta_odd_coreSideCountPt_mixed`,
  proved).

Nothing in this file is geometric: it is the composition of the already-proved dictionaries.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- In `ZMod 2`, an even natural casts to `0`. -/
lemma zmod2_natCast_eq_zero_of_even {n : ℕ} (h : Even n) : ((n : ℕ) : ZMod 2) = 0 :=
  zmod2_eq_zero_of_ne_one fun h1 => (Nat.not_odd_iff_even.mpr h) ((zmod2_natCast_eq_one_iff_odd n).mp h1)

/-! ## 1. The pure parity algebra of the reference triple -/

/-- **The antisymmetry of the two configuration factors from the reference-triple data.**

`T k` are the three *top* boundary counts of the reference triple, `g k j` the six *block factors*
(the count of the block-`k` chart against the block-`j` plane).  The hypotheses are exactly the
structural output of the reference triple:

* `htop` — the engine plus the ends clause (`Odd (T 0 + T 1 + T 2)`, Hugelmeyer's Lemma 4);
* `hblock` — the multiplicativity T6 at the three blocks;
* `h20`, `h21` — the reference block's two factors are **even** (they are the level pairings, vanishing
  because the reference plane lies above the configuration);
* `h02`, `h12` — the two **mixed** factors are **odd** (`(F1)`);

and the conclusion is `f 0 1 + f 1 0 = 1` in `ZMod 2`: exactly one of the two configuration pairings is
odd.  This is Hugelmeyer's Lemma 3 at the level of the reference triple. -/
theorem pairParity_of_threeBlockT6 (T : Fin 3 → ℕ) (g : Fin 3 → Fin 3 → ℕ)
    (htop : Odd (T 0 + T 1 + T 2))
    (hblock : ∀ k : Fin 3, Odd (T k) ↔ (Odd (g k (k + 1)) ∧ Odd (g k (k + 2))))
    (h20 : Even (g 2 0)) (h21 : Even (g 2 1)) (h02 : Odd (g 0 2)) (h12 : Odd (g 1 2)) :
    ((g 0 1 : ℕ) : ZMod 2) + ((g 1 0 : ℕ) : ZMod 2) = 1 := by
  have hsum := zmod2_sum_three_eq_one_of_odd T htop
  have hk : ∀ k : Fin 3, ((T k : ℕ) : ZMod 2)
      = ((g k (k + 1) : ℕ) : ZMod 2) * ((g k (k + 2) : ℕ) : ZMod 2) :=
    fun k => zmod2_natCast_eq_mul_of_odd_iff (hblock k)
  rw [hk 0, hk 1, hk 2] at hsum
  have e20 : ((g 2 0 : ℕ) : ZMod 2) = 0 := zmod2_natCast_eq_zero_of_even h20
  have e21 : ((g 2 1 : ℕ) : ZMod 2) = 0 := zmod2_natCast_eq_zero_of_even h21
  have e02 : ((g 0 2 : ℕ) : ZMod 2) = 1 := (zmod2_natCast_eq_one_iff_odd _).mpr h02
  have e12 : ((g 1 2 : ℕ) : ZMod 2) = 1 := (zmod2_natCast_eq_one_iff_odd _).mpr h12
  have h0 : (0 : Fin 3) + 1 = 1 := by decide
  have h1 : (1 : Fin 3) + 1 = 2 := by decide
  have h2 : (2 : Fin 3) + 1 = 0 := by decide
  have h0' : (0 : Fin 3) + 2 = 2 := by decide
  have h1' : (1 : Fin 3) + 2 = 0 := by decide
  have h2' : (2 : Fin 3) + 2 = 1 := by decide
  rw [h0, h1, h2, h0', h1', h2'] at hsum
  rw [e02, e12, e20, e21] at hsum
  simp only [mul_one, one_mul, zero_mul, add_zero] at hsum
  exact hsum

/-! ## 2. The same, with the two configuration factors identified with the germ's counts -/

/-- **The two-term `CntAt` identity of the reference triple.**

This is `pairParity_of_threeBlockT6` with the two configuration factors `g 0 1`, `g 1 0` identified
with the germ's own counts at the coupled parameter `τ` (the identification is
`Work.Drive.coreSideCount_block_eq_CntAt` / `Work.Drive.coreSideCount_block_eq_CntAt_chartPert`, so it
enters as the two equalities `hg01`, `hg10`).

The conclusion `CntAt (u 1 - u 0) (τ 0, τ 1) + CntAt (u 0 - u 1) (τ 1, τ 0) = 1` is the exact input of
the germ dictionary `Work.Drive.sideGerm_add_neg_eq_one_of_counts`. -/
theorem cntAt_pair_eq_one_of_threeBlockT6 {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (cblk : Fin 3 → ℝ)
    (T : Fin 3 → ℕ) (g : Fin 3 → Fin 3 → ℕ)
    (hg01 : g 0 1 = CntAt Ξ Q (cblk 1) (u 1 - u 0) (τ 0, τ 1))
    (hg10 : g 1 0 = CntAt Ξ Q (cblk 0) (u 0 - u 1) (τ 1, τ 0))
    (htop : Odd (T 0 + T 1 + T 2))
    (hblock : ∀ k : Fin 3, Odd (T k) ↔ (Odd (g k (k + 1)) ∧ Odd (g k (k + 2))))
    (h20 : Even (g 2 0)) (h21 : Even (g 2 1)) (h02 : Odd (g 0 2)) (h12 : Odd (g 1 2)) :
    ((CntAt Ξ Q (cblk 1) (u 1 - u 0) (τ 0, τ 1) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk 0) (u 0 - u 1) (τ 1, τ 0) : ℕ) : ZMod 2) = 1 := by
  have h := pairParity_of_threeBlockT6 T g htop hblock h20 h21 h02 h12
  rw [hg01, hg10] at h
  exact h

/-! ## 3. The germ antisymmetry at the angle `u 1 - u 0` -/

/-- **`hn2` at the angle `u 1 - u 0`, from the reference-triple count identity.**

Composing `cntAt_pair_eq_one_of_threeBlockT6` (the count parity) with the germ dictionary
`Work.Drive.sideGerm_add_neg_eq_one_of_counts` (`hn2CountInterface.lean`): the two germ values
`sideGerm (u 1 - u 0)` and `sideGerm (u 0 - u 1)` are computed at the good coupled parameters
`(τ 0, τ 1)` and `(τ 1, τ 0)` respectively, and the oddness of the sum of the two counts gives the
antisymmetry.

The two `GoodAt` hypotheses are the *pair-goodness* of the two perturbed configurations — the two
conditions produced by the reference-triple genericity
`Work.Drive.exists_meet3Hyp_and_goodAt_refTriple` (`Drive/refTripleGeneric`) at the same parameter `τ`,
and the locality data `hUa`/`hUn` are the parity localities of the germ lane at the two angles. -/
theorem sideGerm_add_neg_eq_one_of_refTriple {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (c : ℝ) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c (u 1 - u 0) t → GoodAt Ξ Q c (u 1 - u 0) t' →
        Odd (CntAt Ξ Q c (u 1 - u 0) t) = Odd (CntAt Ξ Q c (u 1 - u 0) t'))
    (hUn : ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c (u 0 - u 1) t → GoodAt Ξ Q c (u 0 - u 1) t' →
        Odd (CntAt Ξ Q c (u 0 - u 1) t) = Odd (CntAt Ξ Q c (u 0 - u 1) t'))
    (ht : ‖(τ 0, τ 1)‖ < ε) (ht' : ‖(τ 1, τ 0)‖ < ε)
    (hg01 : GoodAt Ξ Q c (u 1 - u 0) (τ 0, τ 1))
    (hg10 : GoodAt Ξ Q c (u 0 - u 1) (τ 1, τ 0))
    (hpar : Odd (CntAt Ξ Q c (u 1 - u 0) (τ 0, τ 1) + CntAt Ξ Q c (u 0 - u 1) (τ 1, τ 0))) :
    sideGerm Ξ Q c (u 1 - u 0) + sideGerm Ξ Q c (u 0 - u 1) = 1 := by
  have e : (u 0 - u 1 : UnitAddCircle) = -(u 1 - u 0) := by abel
  rw [e] at hUn hg10 hpar
  have h := sideGerm_add_neg_eq_one_of_counts Ξ Q c (u 1 - u 0) hε hUa hUn hΞ hQ hc
    ht ht' hg01 hg10 hpar
  rw [← e] at h
  exact h

end

end Work.Drive
