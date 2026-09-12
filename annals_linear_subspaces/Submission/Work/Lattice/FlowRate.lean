import Mathlib
import Submission.GeometryOfNumbers.WedgeBlocks

/-!
# The flow rate of a wedge is its top-block eigenvalue (Prop-5 "large block" engine)

Coordinate model: `ℝᵈ = EuclideanSpace ℝ (Fin d)`, `L = modelX ℓ = span {e i | i < ℓ}` and its
orthogonal complement `Lᗮ`; for a `k`-vector `w ∈ ⋀^k ℝᵈ` the **block** `blockElem w u` is the
component with exactly `u` factors in `Lᗮ` (`Submission.ExteriorCoordinates`).

Under the two-scale diagonal flow `D = scaleMap (twoScale a b ℓ)` (coefficient `a` on `L`,
`b` on `Lᗮ`) the block `u` is an *eigenvector* of the exterior-power action with eigenvalue
`a^(k-u) * b^u` (`Submission.DiagonalFlow.blockElem_map_scaleMap_twoScale`).  This module turns
that eigen-structure into the quantitative statements used by Prop 5's "large block" input:

* `blockElem_mixed_wedge` / `map_mixed_wedge` / `norm_map_mixed_wedge`: a wedge all of whose
  factors lie in `L ∪ Lᗮ` (the "adapted" wedge, `T` = the set of `Lᗮ`-factors) is *exactly* an
  eigenvector of the flow, with eigenvalue `a^(j-|T|) * b^|T|` — no error term;
* `eigen_mul_norm_blockElem_le`: for **every** `k`-vector and every block `u`,
  `a^(k-u) b^u * ‖blockElem w u‖ ≤ ‖D w‖` (one comparison, exact, no hypotheses beyond
  `0 ≤ a, b`);
* `IsTopBlock` + `norm_map_le_of_isTopBlock`: if `u` is the top nonvanishing block of `w`
  (all blocks above it vanish) and `0 < a ≤ b`, then
  `‖D w‖ ≤ (k+1) * a^(k-u) * b^u * ‖w‖`;
  together with the previous item the flow rate of the wedge is pinched between the top-block
  eigenvalue and `(k+1)` times it — the mechanism by which covolume-minimality at a large time
  `t` forces the *position* (`dim (realSpan V ⊓ L)`) of the minimising subspace.

All declarations are Mathlib + `Submission.GeometryOfNumbers.{ExteriorCoordinates,DiagonalFlow,
WedgeBlocks}` (the latter for the load-bearing Vanishing lemma
`WedgeBlocks.wcoord_wedge_zero_of_block_mismatch`).
-/

noncomputable section

open Module exteriorPower
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.FlowRate

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks

variable {d : ℕ}

/-- Block projection of a `k`-vector is the whole vector as soon as all its coordinates outside
the block vanish. -/
lemma blockElem_eq_self_of_wcoord_zero_outside {k ℓ t : ℕ} (w : WK d k) (_ht : t ≤ k)
    (h : ∀ I : IDX d k, I ∉ blockFinset (d := d) (k := k) (ℓ := ℓ) t →
      wcoord (d := d) (k := k) w I = 0) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w t = w := by
  classical
  rw [blockElem]
  conv_rhs => rw [← sum_wcoord_smul_basis (d := d) (k := k) w]
  exact Finset.sum_subset (Finset.subset_univ _) (fun I _ hI => by rw [h I hI]; simp)

/-- The "mixed" wedge family: factors indexed by `T` live in `Lᗮ`, the others in `L`. -/
def mixedWedge {j : ℕ} (e c : Fin j → RD d) (T : Finset (Fin j)) : Fin j → RD d :=
  fun r => if r ∈ T then c r else e r

/-- **Vanishing**: the Plücker coordinates of a mixed wedge vanish outside the block `|T|`. -/
lemma wcoord_mixedWedge_eq_zero_of_mismatch {j ℓ : ℕ} (e c : Fin j → RD d)
    (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ)
    (T : Finset (Fin j)) (I : IDX d j)
    (hneq : T.card ≠ ((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) :
    wcoord (d := d) (k := j) (exteriorPower.ιMulti ℝ j (mixedWedge e c T)) I = 0 := by
  have h2 : T.card ≠ ((Finset.univ : Finset (Fin j)).filter (fun r : Fin j =>
      ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I r : Fin d).val))).card := by
    rw [card_filter_enum_ge (d := d) (k := j) (ℓ := ℓ) I]
    exact hneq
  unfold mixedWedge
  exact wcoord_wedge_zero_of_block_mismatch (d := d) (k := j) ℓ e c he hc T I h2

/-- A mixed wedge lies in the block `|T|`. -/
lemma blockElem_mixedWedge {j ℓ : ℕ} (e c : Fin j → RD d)
    (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ) (T : Finset (Fin j)) :
    blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ j (mixedWedge e c T)) T.card
      = exteriorPower.ιMulti ℝ j (mixedWedge e c T) := by
  refine blockElem_eq_self_of_wcoord_zero_outside (k := j) (ℓ := ℓ) _
    (by simpa using Finset.card_le_univ T) ?_
  intro I hI
  refine wcoord_mixedWedge_eq_zero_of_mismatch e c he hc T I ?_
  intro h
  exact hI (by simp [blockFinset, h])

/-- The other blocks of a mixed wedge vanish. -/
lemma blockElem_mixedWedge_eq_zero {j ℓ : ℕ} (e c : Fin j → RD d)
    (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ) (T : Finset (Fin j))
    {u : ℕ} (hu : u ≠ T.card) :
    blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ j (mixedWedge e c T)) u = 0 := by
  have h1 := blockElem_mixedWedge (d := d) (ℓ := ℓ) e c he hc T
  have h2 := blockElem_blockElem_of_ne (d := d) (k := j) (ℓ := ℓ)
    (i := T.card) (j := u) (Ne.symm hu)
    (exteriorPower.ιMulti ℝ j (mixedWedge e c T))
  rwa [h1] at h2

/-- **A mixed wedge is an eigenvector of the two-scale flow**, with eigenvalue
`a^(j-|T|) * b^|T|` — exactly, with no error term. -/
lemma map_mixedWedge {j ℓ : ℕ} (a b : ℝ) (e c : Fin j → RD d)
    (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ) (T : Finset (Fin j)) :
    exteriorPower.map j (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ j (mixedWedge e c T))
      = (a ^ (j - T.card) * b ^ T.card) •
        exteriorPower.ιMulti ℝ j (mixedWedge e c T) := by
  classical
  set w := exteriorPower.ιMulti ℝ j (mixedWedge e c T) with hw
  have h1 : blockElem (d := d) (k := j) (ℓ := ℓ) w T.card = w :=
    blockElem_mixedWedge (d := d) (ℓ := ℓ) e c he hc T
  have h0 : ∀ u : ℕ, u ≠ T.card → blockElem (d := d) (k := j) (ℓ := ℓ) w u = 0 :=
    fun u hu => blockElem_mixedWedge_eq_zero (d := d) (ℓ := ℓ) e c he hc T hu
  calc exteriorPower.map j (scaleMap (twoScale a b ℓ)) w
      = exteriorPower.map j (scaleMap (twoScale a b ℓ))
          ((Finset.range (j + 1)).sum
            (fun u => blockElem (d := d) (k := j) (ℓ := ℓ) w u)) := by
          rw [sum_blockElem]
    _ = (Finset.range (j + 1)).sum (fun u =>
          exteriorPower.map j (scaleMap (twoScale a b ℓ))
            (blockElem (d := d) (k := j) (ℓ := ℓ) w u)) := by
          rw [map_sum]
    _ = (Finset.range (j + 1)).sum (fun u =>
          (a ^ (j - u) * b ^ u) • blockElem (d := d) (k := j) (ℓ := ℓ) w u) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [map_scaleMap_twoScale_blockElem]
    _ = (a ^ (j - T.card) * b ^ T.card) • w := by
          rw [Finset.sum_eq_single (T.card)]
          · rw [h1]
          · intro u _ hu
            rw [h0 u hu, smul_zero]
          · intro hnot
            have hmem : T.card ∈ Finset.range (j + 1) := by
              have : T.card ≤ j := by simpa using Finset.card_le_univ T
              exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr this)
            exact absurd hmem hnot

/-- **Norm of a flowed mixed wedge**: exact eigenvalue identity. -/
lemma norm_map_mixedWedge {j ℓ : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e c : Fin j → RD d) (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ)
    (T : Finset (Fin j)) :
    ‖exteriorPower.map j (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ j (mixedWedge e c T))‖
      = (a ^ (j - T.card) * b ^ T.card) *
        ‖exteriorPower.ιMulti ℝ j (mixedWedge e c T)‖ := by
  rw [map_mixedWedge a b e c he hc T, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))]

/-! ### The two-sided flow-rate pinch for an arbitrary wedge -/

/-- **One-sided eigenvalue bound**: for every block `u` of any `k`-vector, the eigenvalue
times the block norm is at most the norm of the flowed vector. -/
lemma eigen_mul_norm_blockElem_le {k ℓ u : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (w : WK d k) (hu : u ≤ k) :
    (a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
      ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ := by
  have h := norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ)
    (exteriorPower.map k (scaleMap (twoScale a b ℓ)) w) hu
  rw [blockElem_map_scaleMap_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b)
      (w := w) hu, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))] at h
  exact h

/-- Triangle-inequality expansion of the flowed norm in terms of the block norms. -/
lemma norm_map_le_sum_eigen {k ℓ : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (w : WK d k) :
    ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ≤
      (Finset.range (k + 1)).sum (fun u =>
        (a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖) := by
  have hsum : exteriorPower.map k (scaleMap (twoScale a b ℓ)) w =
      (Finset.range (k + 1)).sum (fun u =>
        exteriorPower.map k (scaleMap (twoScale a b ℓ))
          (blockElem (d := d) (k := k) (ℓ := ℓ) w u)) := by
    rw [← map_sum, sum_blockElem]
  rw [hsum]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun u _ => ?_)
  rw [map_scaleMap_twoScale_blockElem, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))]

/-- `u` is the **top nonvanishing block** of `w`: block `u` is nonzero and all higher blocks
vanish. -/
def IsTopBlock {k : ℕ} (ℓ : ℕ) (w : WK d k) (u : ℕ) : Prop :=
  blockElem (d := d) (k := k) (ℓ := ℓ) w u ≠ 0 ∧
    ∀ u', u < u' → u' ≤ k → blockElem (d := d) (k := k) (ℓ := ℓ) w u' = 0

/-- The eigenvalue is monotone in the block index (for `a > 0`, `a ≤ b`). -/
lemma eigen_mono {k u u' : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hu : u' ≤ u)
    (huk : u ≤ k) :
    a ^ (k - u') * b ^ u' ≤ a ^ (k - u) * b ^ u := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hr : (1 : ℝ) ≤ b / a := (one_le_div ha).mpr hab
  have hu'k : u' ≤ k := le_trans hu huk
  have h1 : a ^ (k - u') * b ^ u' = a ^ k * (b / a) ^ u' := by
    rw [div_pow, pow_sub₀ a (ne_of_gt ha) hu'k]
    field_simp
  have h2 : a ^ (k - u) * b ^ u = a ^ k * (b / a) ^ u := by
    rw [div_pow, pow_sub₀ a (ne_of_gt ha) huk]
    field_simp
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hu) (pow_nonneg (le_of_lt ha) k)

/-- **Top-block upper bound**: the flowed norm of a wedge is at most `(k+1)` times the
top-block eigenvalue times the norm of the wedge. -/
lemma norm_map_le_of_isTopBlock {k ℓ u : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (w : WK d k) (hu : u ≤ k) (htop : IsTopBlock (d := d) (ℓ := ℓ) w u) :
    ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ≤
      ((k : ℝ) + 1) * (a ^ (k - u) * b ^ u) * ‖w‖ := by
  have hb : 0 ≤ b := le_trans (le_of_lt ha) hab
  have hle : ∀ v : ℕ, v ∈ Finset.range (k + 1) →
      (a ^ (k - v) * b ^ v) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ≤
        (a ^ (k - u) * b ^ u) * ‖w‖ := by
    intro v hv
    have hvk : v ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
    have hblk : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ ≤ ‖w‖ :=
      norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ) w hvk
    by_cases h : v ≤ u
    · have he : a ^ (k - v) * b ^ v ≤ a ^ (k - u) * b ^ u :=
        eigen_mono (k := k) (u := u) (u' := v) ha hab h hu
      have hnn : (0 : ℝ) ≤ a ^ (k - u) * b ^ u :=
        mul_nonneg (pow_nonneg (le_of_lt ha) _) (pow_nonneg hb _)
      calc (a ^ (k - v) * b ^ v) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖
          ≤ (a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w v‖ :=
            mul_le_mul_of_nonneg_right he (norm_nonneg _)
        _ ≤ (a ^ (k - u) * b ^ u) * ‖w‖ := mul_le_mul_of_nonneg_left hblk hnn
    · have hvlt : u < v := lt_of_not_ge h
      have hz : blockElem (d := d) (k := k) (ℓ := ℓ) w v = 0 := htop.2 v hvlt hvk
      rw [hz, norm_zero, mul_zero]
      have hnn : (0 : ℝ) ≤ a ^ (k - u) * b ^ u :=
        mul_nonneg (pow_nonneg (le_of_lt ha) _) (pow_nonneg hb _)
      exact mul_nonneg hnn (norm_nonneg w)
  calc ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖
      ≤ (Finset.range (k + 1)).sum (fun u =>
          (a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖) :=
        norm_map_le_sum_eigen a b (le_of_lt ha) hb w
    _ ≤ (Finset.range (k + 1)).sum (fun _ =>
          (a ^ (k - u) * b ^ u) * ‖w‖) := Finset.sum_le_sum hle
    _ = ((k : ℝ) + 1) * ((a ^ (k - u) * b ^ u) * ‖w‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((k : ℝ) + 1) * (a ^ (k - u) * b ^ u) * ‖w‖ := by ring

/-- The mixed wedge has the top block `|T|` in the sense of `IsTopBlock`. -/
lemma isTopBlock_mixedWedge {j ℓ : ℕ} (e c : Fin j → RD d)
    (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ) (T : Finset (Fin j))
    (hw : exteriorPower.ιMulti ℝ j (mixedWedge e c T) ≠ 0) :
    IsTopBlock (d := d) (ℓ := ℓ) (exteriorPower.ιMulti ℝ j (mixedWedge e c T)) T.card := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := blockElem_mixedWedge (d := d) (ℓ := ℓ) e c he hc T
    rw [← h1, h] at hw
    exact hw rfl
  · intro u' hu' _hu'k
    exact blockElem_mixedWedge_eq_zero (d := d) (ℓ := ℓ) e c he hc T (Ne.symm (ne_of_lt hu'))

/-! ### Exponential-flow forms

`a = exp (-t/ℓ)`, `b = exp (t/(d-ℓ))` give the §3 flow `a_t`, whose block-`u` eigenvalue
`a^(k-u) b^u` equals `exp (t * (-(k-u)/ℓ + u/(d-ℓ)))`. -/

/-- The two-scale eigenvalue in exponential-flow form. -/
lemma eigen_exp {k u ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    Real.exp (-t / ↑ℓ) ^ (k - u) * Real.exp (t / ↑(d - ℓ)) ^ u =
      Real.exp (t * (-(((k - u : ℕ) : ℝ) / ↑ℓ) + ((u : ℝ) / ↑(d - ℓ)))) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hℓne : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hℓ0)
  have hdm : ((d : ℝ) - (ℓ : ℝ)) = ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
  have hdmne : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    rw [← hdm]
    have : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
      have h1 : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
      linarith
    exact ne_of_gt this
  rw [← hdm]
  field_simp

/-- **Block dominates the flowed norm** (exponential flow, `t ≥ 0`): the block-`u`
eigenvalue times the block norm is at most the norm of the flowed `k`-vector. -/
lemma eigen_exp_mul_norm_blockElem_le {k ℓ u : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    (_ht : 0 ≤ t) (w : WK d k) (hu : u ≤ k) :
    Real.exp (t * (-(((k - u : ℕ) : ℝ) / ↑ℓ) + ((u : ℝ) / ↑(d - ℓ)))) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
      ‖exteriorPower.map k (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w‖ := by
  have ha : 0 ≤ Real.exp (-t / ↑ℓ) := le_of_lt (Real.exp_pos _)
  have hb : 0 ≤ Real.exp (t / ↑(d - ℓ)) := le_of_lt (Real.exp_pos _)
  have h := eigen_mul_norm_blockElem_le (d := d) (k := k) (ℓ := ℓ)
    (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ha hb w hu
  rwa [eigen_exp (d := d) (k := k) (u := u) (ℓ := ℓ) hℓ0 hℓd t] at h

/-- **Adapted wedge under the exponential flow**: exact eigenvalue identity. -/
lemma norm_map_mixedWedge_exp {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ} (_ht : 0 ≤ t)
    (e c : Fin j → RD d) (he : ∀ r, e r ∈ modelX ℓ) (hc : ∀ r, c r ∈ (modelX ℓ)ᗮ)
    (T : Finset (Fin j)) :
    ‖exteriorPower.map j
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ))
        (exteriorPower.ιMulti ℝ j (mixedWedge e c T))‖
      = Real.exp (t * (-(((j - T.card : ℕ) : ℝ) / ↑ℓ) + ((T.card : ℝ) / ↑(d - ℓ)))) *
        ‖exteriorPower.ιMulti ℝ j (mixedWedge e c T)‖ := by
  rw [norm_map_mixedWedge (d := d) (ℓ := ℓ) (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ)))
      (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)) e c he hc T]
  rw [eigen_exp (d := d) (k := j) (u := T.card) (ℓ := ℓ) hℓ0 hℓd t]

/-- **Top-block pinch in exponential-flow form**: for a `k`-vector whose top block is `u`
(`0 < u ≤ k` optional; here `t ≥ 0`), the flowed norm is at most `(k+1)` times the
top-block eigenvalue times the norm. -/
lemma norm_map_le_eigen_exp_of_isTopBlock {k ℓ u : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    (ht : 0 ≤ t) (w : WK d k) (hu : u ≤ k) (htop : IsTopBlock (d := d) (ℓ := ℓ) w u) :
    ‖exteriorPower.map k
        (scaleMap (twoScale (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ℓ)) w‖ ≤
      ((k : ℝ) + 1) *
        Real.exp (t * (-(((k - u : ℕ) : ℝ) / ↑ℓ) + ((u : ℝ) / ↑(d - ℓ)))) * ‖w‖ := by
  have ha : 0 < Real.exp (-t / ↑ℓ) := Real.exp_pos _
  have hℓne : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hℓ0)
  have hdmne : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    have h1 : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    have h2 : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hℓd)]
      linarith
    exact ne_of_gt h2
  have hab : Real.exp (-t / ↑ℓ) ≤ Real.exp (t / ↑(d - ℓ)) := by
    rw [Real.exp_le_exp]
    rw [div_le_div_iff₀ (by exact_mod_cast hℓ0) (by positivity)]
    nlinarith [ht]
  have h := norm_map_le_of_isTopBlock (d := d) (k := k) (ℓ := ℓ)
    (Real.exp (-t / ↑ℓ)) (Real.exp (t / ↑(d - ℓ))) ha hab w hu htop
  rwa [eigen_exp (d := d) (k := k) (u := u) (ℓ := ℓ) hℓ0 hℓd t] at h

/-- **The top block is flow-invariant**: the block pattern of a wedge is unchanged by the flow
(with `a, b ≠ 0`), since each block is scaled by a nonzero eigenvalue. -/
lemma isTopBlock_map {k ℓ u : ℕ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (w : WK d k) (hu : u ≤ k)
    (htop : IsTopBlock (d := d) (ℓ := ℓ) w u) :
    IsTopBlock (d := d) (ℓ := ℓ)
      (exteriorPower.map k (scaleMap (twoScale a b ℓ)) w) u := by
  have heig : (a ^ (k - u) * b ^ u) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)
  constructor
  · rw [blockElem_map_scaleMap_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) (w := w) hu]
    simp [htop.1, heig]
  · intro u' hu' hu'k
    rw [blockElem_map_scaleMap_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) (w := w) hu'k,
      htop.2 u' hu' hu'k, smul_zero]

/-- **Two-sided flow-rate pinch**: for `0 < a ≤ b` the flowed norm of a `k`-vector is pinched
between the top-block eigenvalue times the top-block norm and `(k+1)` times the top-block
eigenvalue times the norm of the vector.  (The flow rate of a wedge is its top-block
eigenvalue.) -/
theorem norm_map_pinch {k ℓ u : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (w : WK d k)
    (hu : u ≤ k) (htop : IsTopBlock (d := d) (ℓ := ℓ) w u) :
    (a ^ (k - u) * b ^ u) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w u‖ ≤
        ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ∧
      ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) w‖ ≤
        ((k : ℝ) + 1) * (a ^ (k - u) * b ^ u) * ‖w‖ :=
  ⟨eigen_mul_norm_blockElem_le a b (le_of_lt ha) (le_trans (le_of_lt ha) hab) w hu,
   norm_map_le_of_isTopBlock a b ha hab w hu htop⟩

end Submission.FlowRate
