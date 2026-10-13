/-
# `Work.FTS.LocData.HlocFactor` — the separated form of the bump `hLoc α = φ(z)·Γ(θ)`

The localised bump of the route is a product of a function of `z` and a function of `θ`,

  `hLoc α z θ = bumpZ z * Γ(θ)`,

so every operator of the workspace (`D_z = z∂_z`, `D_θ = sin(2θ)∂_θ` and their iterates) acts
on the two factors independently:

* `DzIter i (hLoc α) z θ = Γ(θ) · (T1^[i] bumpZ z)`;
* `DthIter i (hLoc α) z θ = (dthU^[i] Γ) θ · bumpZ z`;
* `mixed j i (hLoc α) z θ = (DthIter i Γ)(0,θ) · (T1^[j] bumpZ z)`.

These identities are what turn `HkIntegrand α 4 (hLoc α)` into a finite sum of products
(angular factor)·(radial factor), so that the angular jet bound `DthIter_Gam_abs_le` and the
radial bound `DzIter_bumpZ_bound` apply term by term.

They also give the *vanishing off the support*: since every `T1`-iterate of `bumpZ` vanishes off
`[3/4, 7/4]`, all the derivatives of `hLoc α` vanish there, hence so does `HkIntegrand`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.HkFstarDefs
import Submission.Work.FTS.LocData.DzIter_bumpZ_bound
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The factorisation of `hLoc` -/

/-- `hLoc α = φ(z)·Γ(θ)` written with the angular factor first, as required by
`DzIter_mul_theta_factor` / `DthIter_decomp`. -/
theorem hLoc_eq_Gam_mul_bumpZ (α : ℝ) :
    hLoc α = fun z θ => Work.Spaces.Gam α θ * bumpZ z := by
  funext z θ
  rw [hLoc_apply]
  ring

/-- **The `D_z`-derivatives of the bump separate**: `D_z^i (φ·Γ) = Γ · (T1^[i] φ)`. -/
theorem DzIter_hLoc (α : ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (hLoc α)
      = fun z θ => Work.Spaces.Gam α θ * (T1^[i]) bumpZ z := by
  rw [hLoc_eq_Gam_mul_bumpZ α,
    DzIter_mul_theta_factor i (fun t => Work.Spaces.Gam α t) (fun z _ => bumpZ z)]
  funext z θ
  rw [DzIter_bumpZ_eq i θ z]

/-- **The `D_θ`-derivatives of the bump separate**: `D_θ^i (φ·Γ) = (dthU^[i] Γ) · φ`. -/
theorem DthIter_hLoc (α : ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (hLoc α)
      = fun z θ => Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ * bumpZ z := by
  rw [hLoc_eq_Gam_mul_bumpZ α]
  funext z θ
  exact Work.Spaces.DthIter_decomp i (fun t => Work.Spaces.Gam α t) bumpZ z θ

/-- **The mixed derivatives of the bump separate**: `D_z^j D_θ^i (φ·Γ) = (D_θ^i Γ)(0,·) · (T1^[j] φ)`.
(The angular factor is written as the two-variable iterate evaluated at `z = 0`, which is where
the angular estimate `DthIter_Gam_abs_le` is stated.) -/
theorem mixed_hLoc (α : ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (hLoc α)
      = fun z θ => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
          * (T1^[j]) bumpZ z := by
  rw [Work.Spaces.mixed, DthIter_hLoc α i,
    DzIter_mul_theta_factor j (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t))
      (fun z _ => bumpZ z)]
  funext z θ
  rw [DzIter_bumpZ_eq j θ z, ← DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]

/-! ## Vanishing off the support -/

/-- Every `D_z`-iterate of the bump vanishes off the closed interval `[3/4, 7/4]`. -/
theorem T1_iterate_bumpZ_eq_zero {z : ℝ} (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4)) (c : ℕ) :
    (T1^[c]) bumpZ z = 0 :=
  (T1_iterate_contDiff BumpZ_contDiff bumpZ_eq_zero_of_notMem_Icc c).2 z hz

/-- The bump vanishes off `[3/4, 7/4]`. -/
theorem hLoc_eq_zero_off {α z : ℝ} (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4)) (θ : ℝ) :
    hLoc α z θ = 0 := by
  rw [hLoc_apply, bumpZ_eq_zero_of_notMem_Icc z hz]
  ring

/-- **`HkIntegrand α 4 (hLoc α)` vanishes off the support of the bump.**  Every summand of the
integrand is a square of a product in which one factor is a `D_z`-iterate of `bumpZ`, and all of
those vanish for `z ∉ [3/4, 7/4]`. -/
theorem HkIntegrand_hLoc_eq_zero_off {α z : ℝ} (hz : z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4))
    (θ : ℝ) : Work.Spaces.HkIntegrand α 4 (hLoc α) z θ = 0 := by
  have h1 : ∀ i : ℕ, Work.Spaces.DzIter i (hLoc α) z θ = 0 := by
    intro i
    rw [congrFun (congrFun (DzIter_hLoc α i) z) θ, T1_iterate_bumpZ_eq_zero hz i, mul_zero]
  have h2 : ∀ j i : ℕ, Work.Spaces.mixed j i (hLoc α) z θ = 0 := by
    intro j i
    rw [congrFun (congrFun (mixed_hLoc α j i) z) θ, T1_iterate_bumpZ_eq_zero hz j, mul_zero]
  rw [Work.Spaces.HkIntegrand]
  have hs1 : (∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i (hLoc α) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h1 i]
    ring
  have hs2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i (hLoc α) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, h2 j i]
      ring
    · rw [if_neg hc]
  rw [hs1, hs2, add_zero]

/-! ## The weight bound on the support -/

/-- **The weight is bounded by the far-field factor on the support of the bump.**  For
`z ∈ [3/4, 7/4]`,

  `w(z)² ≤ (1771561/1296)/(1+z)²`,

i.e. `(1+z)^6/z^4 ≤ (11/4)^6/(3/4)^4 = 1771561/1296`.  This is what converts the pointwise bound
`HkIntegrand ≤ K·w²·angMaj` of the bump (which holds on the whole quadrant, since `φ` is bounded)
into the far-field-decaying bound `≤ K²·angMaj/(1+z)²` of the localised data. -/
theorem w_sq_le_on_support {z : ℝ} (hz : z ∈ Set.Icc (3 / 4 : ℝ) (7 / 4)) :
    (Work.Spaces.w z) ^ 2 ≤ (1771561 / 1296 : ℝ) / (1 + z) ^ 2 := by
  have hz0 : 0 < z := by linarith [hz.1]
  have hzne : z ≠ 0 := ne_of_gt hz0
  have hz4 : 0 < z ^ 4 := by positivity
  have hpos : 0 < (1 + z) ^ 2 := by positivity
  rw [le_div_iff₀ hpos, Work.Spaces.w]
  have hsplit : ((1 + z) ^ 2 / z ^ 2) ^ 2 * (1 + z) ^ 2 = (1 + z) ^ 6 / z ^ 4 := by
    field_simp
  rw [hsplit, div_le_iff₀ hz4]
  have h1 : (1 + z) ^ 6 ≤ (11 / 4 : ℝ) ^ 6 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith [hz.2]
  have h2 : ((3 : ℝ) / 4) ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ (by norm_num) hz.1 4
  calc (1 + z) ^ 6 ≤ (11 / 4 : ℝ) ^ 6 := h1
    _ = (1771561 / 1296 : ℝ) * ((3 : ℝ) / 4) ^ 4 := by norm_num
    _ ≤ (1771561 / 1296 : ℝ) * z ^ 4 :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)

end Work.FTS.LocData
