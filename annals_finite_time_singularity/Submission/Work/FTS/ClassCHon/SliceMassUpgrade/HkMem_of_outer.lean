/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkMem_of_outer` — every-`z` level-`k` honesty from the *outer* bound two orders up

The elliptic node `EllNode7` needs the **every-`z`** honesty `Work.Spaces.HkMem α k (slot)` of
the second-order slots of the solution, whereas the workspace's elliptic estimates produce
*integrated* (`∫⁻`) bounds.  This file supplies the transfer at a general level `k`, in the
direction in which the workspace's estimates actually provide the two ingredients:

  > `HkMem α k F`  ⟸  the outer `∫⁻`-bound of `HkIntegrand α k F`
  >                    and the outer `∫⁻`-bound of `HkIntegrand α (k+1) F`.

**Why the *level-`(k+1)`*-bound of `F` itself suffices.**  The level-`k` integrand is a finite
sum of squares of two families of weighted derivatives:

* the `D_z`-family `(D_z^i F · w/sin(2θ)^{η/2})²`, `0 ≤ i ≤ k`, and
* the mixed family `(D_z^j D_θ^i F · W)²`, `1 ≤ i`, `i + j ≤ k` (`W = w·sin(2θ)^{-γ/2}`).

`HkIntegrand α (k+1) F` contains, term for term, every summand of `HkIntegrand α k F` **and**
one `D_z`-order more (`D_z^{k+1}F`, and the mixed slots with `i + j = k+1`); hence the single
outer bound at level `k+1` dominates the inner (`∫⁻_θ`) masses and their radial fluxes for both
families, which is precisely the shape in which the slice-mass upgrade
(`sliceMass_lintegral_up_gen`, packaged as `piece_mass_lt_top`) consumes its hypotheses on

  `g = D_z^i F`       with weight `τ = sin(2θ)^{-η}`,
  `g = D_z^j D_θ^i F` with weight `τ = sin(2θ)^{-γ}`,

namely `∫⁻_z ∫⁻_θ τ θ g² < ⊤` and `∫⁻_z ∫⁻_θ τ θ (z ∂_z g)² < ⊤` — because
`z ∂_z (D_z^i F) = D_z^{i+1} F` and `z ∂_z (D_z^j D_θ^i F) = D_z^{j+1} D_θ^i F`, and the extra
factor `(w z)² ≥ 1` on `z > 0` turns each `τ`-form into the corresponding summand of
`HkIntegrand α (k+1) F`.

**The two halves of `HkMem`.**

* The *outer* half is `HkMemAe_of_lintegral_k` applied to the level-`k` outer bound, upgraded
  a.e. from `(0,∞)` to `[0,∞)` (the two sets differ by the null point `{0}`);
* the *slice* half is the new content: the slice-mass upgrade at **every** `z > 0`.  There the
  level-`k` integrand is `(w z)²` times a finite sum of `τ`-forms, each of which is honest at
  every single `z` by `piece_mass_lt_top`; a finite sum of honest functions is honest, and the
  remaining point `z = 0` is trivial because `w 0 = 0` kills every summand.

Of the hypotheses of the statement, `hC₁`, `hslmeas1` and `hmeas1` are not needed: only the
outer *bound* `hfin1` at level `k+1` carries content for the slice estimate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_lintegral_up_gen
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.HkMem_zero_of_outer
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.piece_mass_lt_top
import Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral_k
import Submission.Work.FTS.PhiStar.Honesty.CapstoneMeasurability

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ
local notation "HkInt" => Work.Spaces.HkIntegrand
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-! ## The angular weight of the mixed slots and its elementary properties -/

/-- The angular weight `sin(2θ)^{-γ}` of the mixed slots, `γ = 1 + α/10` (the square of the
angular factor of `W = w · w_θ`). -/
noncomputable def gamWt (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sEta_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 ≤ sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem sEta_contOn : ContinuousOn sEta (Set.Ioo 0 (π / 2)) := by
  rw [show sEta = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hx))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn

theorem gamWt_nonneg_Ioo (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 ≤ gamWt α θ := by
  rw [gamWt]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

theorem gamWt_contOn (α : ℝ) : ContinuousOn (gamWt α) (Set.Ioo 0 (π / 2)) := by
  rw [show gamWt α = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo hx))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn

/-- **The square of the full weight `W = w · w_θ`**: `(W α z θ)² = (w z)² sin(2θ)^{-γ}`. -/
theorem Wt_sq_eq_gamWt (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * gamWt α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, gamWt, mul_pow, h1]

/-! ## The level-`0` form of the two families of summands -/

/-- **The `D_z`-summand is `(w z)²` times its `η`-form**: the level-`0` identity
`HkIntegrand α 0 g = (w z)² · (σ θ · g²)`, `σ = sin(2θ)^{-η}`, read backwards. -/
theorem zp_id {F : ℝ → ℝ → ℝ} (i : ℕ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.DzIter i F z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) := by
  rw [← slm_HkIntegrand_zero_profile (0 : ℝ) (Work.Spaces.DzIter i F) z θ,
    slm_HkIntegrand_zero_radial (0 : ℝ) (Work.Spaces.DzIter i F) hθ]

/-- **The mixed summand is `(w z)²` times its `γ`-form**: `(g · W)² = (w z)² · (sin(2θ)^{-γ} g²)`. -/
theorem mp_id (α : ℝ) {F : ℝ → ℝ → ℝ} (j i : ℕ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) := by
  rw [mul_pow, Wt_sq_eq_gamWt α hθ]
  ring

/-! ## The integrand as a sum of `τ`-forms -/

/-- The level-`k` integrand, written as the `(w z)²`-multiple of a finite sum of the `τ`-forms
`τ θ · h z θ²` to which the slice-mass upgrade applies term by term. -/
noncomputable def pieceSum (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2))
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 *
          (if 1 ≤ i ∧ i + j ≤ k then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0)

/-- **The integrand is `pieceSum`.** -/
theorem HkInt_eq_pieceSum (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Iθ) :
    HkInt α k F z θ = pieceSum α k F z θ := by
  simp only [Work.Spaces.HkIntegrand, pieceSum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => zp_id i hθ
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]
      exact mp_id α j i hθ
    · rw [if_neg hc, if_neg hc, mul_zero]

/-- At `z = 0` the radial weight vanishes, so the whole integrand does. -/
theorem HkInt_zero (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) : HkInt α k F 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]
  simp

/-! ## The angular interval rewriting -/

/-- The two restricted measures on the angular intervals agree (`(0,π/2)` and `[0,π/2]`
differ by two null points). -/
theorem restrict_Iθ_eq_restrict_Ioo :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))

/-! ## Honest integrability of a `τ`-form from finiteness of its mass -/

theorem integrableOn_of_lt_top {g : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z : ℝ} (hz : 0 < z)
    (hτc : ContinuousOn τ (Set.Ioo 0 (π / 2)))
    (hτ : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ τ θ)
    (h : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g z θ) ^ 2)) < ⊤) :
    IntegrableOn (fun θ => τ θ * (g z θ) ^ 2) (Set.Ioo 0 (π / 2)) := by
  have hcont : ContinuousOn (fun θ => τ θ * (g z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
    hτc.mul ((hg.curry_θ hz).continuousOn.pow 2)
  have hnnae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))]
      fun θ => τ θ * (g z θ) ^ 2 := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))), 0 ≤ τ θ * (g z θ) ^ 2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => mul_nonneg (hτ θ hθ) (sq_nonneg _)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (hcont.aestronglyMeasurable measurableSet_Ioo) hnnae).mp (ne_of_lt h)

/-! ## Finite sums of integrable functions -/

theorem integrable_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {μ : Measure ℝ}
    (h : ∀ i ∈ s, Integrable (f i) μ) : Integrable (fun θ => ∑ i ∈ s, f i θ) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integrable_zero ℝ ℝ μ)
  | insert a s ha ih =>
      have hsum : (fun θ : ℝ => ∑ i ∈ insert a s, f i θ)
          = fun θ => f a θ + ∑ i ∈ s, f i θ := by
        funext θ
        exact Finset.sum_insert ha
      rw [hsum]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The pointwise dominations by the level-`(k+1)` integrand -/

/-- For `z > 0` the `η`-form of the `i`-th `D_z`-derivative is at most the level-`(k+1)`
integrand, as soon as `i ≤ k + 1`. -/
theorem sEta_mul_sq_le_HkInt {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {i : ℕ} (hi : i ≤ k + 1)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2 ≤ HkInt α (k + 1) F z θ := by
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hnn : 0 ≤ sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2 :=
    mul_nonneg (sEta_nonneg_Ioo hθ) (sq_nonneg _)
  calc sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2
      = 1 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) := (one_mul _).symm
    _ ≤ (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (slm_one_le_w hz)) hnn
    _ = (Work.Spaces.DzIter i F z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        (zp_id i hθI).symm
    _ ≤ HkInt α (k + 1) F z θ := Work.Spaces.sq_le_HkIntegrand_z α (k + 1) F z θ i hi

/-- For `z > 0` the `γ`-form of `D_z^j D_θ^i F` is at most the level-`(k+1)` integrand, as soon
as `1 ≤ i` and `i + j ≤ k + 1`. -/
theorem gamWt_mul_sq_le_HkInt {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {i j : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ k + 1)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 ≤ HkInt α (k + 1) F z θ := by
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hnn : 0 ≤ gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 :=
    mul_nonneg (gamWt_nonneg_Ioo α hθ) (sq_nonneg _)
  calc gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2
      = 1 * (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) := (one_mul _).symm
    _ ≤ (Work.Spaces.w z) ^ 2 * (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (slm_one_le_w hz)) hnn
    _ = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := (mp_id α j i hθI).symm
    _ ≤ HkInt α (k + 1) F z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α (k + 1) F z θ i j hi hij

/-! ## The outer bounds of the two families, from the level-`(k+1)` bound -/

/-- The outer bound of the `η`-form of `D_z^i F`, from the level-`(k+1)` outer bound. -/
theorem zOuter0 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i : ℕ} (hi : i ≤ k + 1) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hfin1 ENNReal.ofReal_lt_top)
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall fun z hz => lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun θ hθ =>
          ENNReal.ofReal_le_ofReal (sEta_mul_sq_le_HkInt (α := α) (k := k) (F := F)
            hi hz hθ)
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (slm_lintegral_Iθ_eq_Ioo
          (fun θ => ENNReal.ofReal (HkInt α (k + 1) F z θ))).symm

/-- The outer bound of the `η`-form of the radial derivative `z ∂_z (D_z^i F) = D_z^{i+1} F`. -/
theorem zOuter1 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i : ℕ} (hi : i ≤ k) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ
          * (z * Work.Spaces.pz (Work.Spaces.DzIter i F) z θ) ^ 2)) < ⊤ := by
  have hDz : ∀ z θ : ℝ, z * Work.Spaces.pz (Work.Spaces.DzIter i F) z θ
      = Work.Spaces.DzIter (i + 1) F z θ := fun z θ => rfl
  rw [show (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (z * Work.Spaces.pz (Work.Spaces.DzIter i F) z θ) ^ 2))
      = (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter (i + 1) F z θ) ^ 2)) from by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact lintegral_congr fun θ => by rw [hDz z θ]]
  exact zOuter0 (k := k) hfin1 (i := i + 1) (by omega)

/-- The outer bound of the `γ`-form of `D_z^j D_θ^i F`. -/
theorem mOuter0 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k + 1) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2)) < ⊤ := by
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hfin1 ENNReal.ofReal_lt_top)
  calc (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall fun z hz => lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun θ hθ =>
          ENNReal.ofReal_le_ofReal (gamWt_mul_sq_le_HkInt (α := α) (k := k) (F := F)
            hi (by omega) hz hθ)
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (slm_lintegral_Iθ_eq_Ioo
          (fun θ => ENNReal.ofReal (HkInt α (k + 1) F z θ))).symm

/-- The outer bound of the `γ`-form of the radial derivative
`z ∂_z (D_z^j D_θ^i F) = D_z^{j+1} D_θ^i F`. -/
theorem mOuter1 {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ
          * (z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2)) < ⊤ := by
  have hDz : ∀ z θ : ℝ, z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ
      = Work.Spaces.mixed (j + 1) i F z θ := fun z θ => rfl
  rw [show (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (z * Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2))
      = (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed (j + 1) i F z θ) ^ 2)) from by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact lintegral_congr fun θ => by rw [hDz z θ]]
  exact mOuter0 (k := k) hfin1 (i := i) (j := j + 1) hi (by omega)

/-! ## The every-`z` finiteness of the two families

These are the two instantiations of the general slice-mass upgrade `piece_mass_lt_top`: the datum
`g` is one of the weighted derivatives, the weight `τ` one of the two angular weights, and the
two outer bounds come from `zOuter0`/`zOuter1` resp. `mOuter0`/`mOuter1`. -/

theorem zMass_lt_top {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i : ℕ} (hi : i ≤ k) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2)) < ⊤ :=
  piece_mass_lt_top (hg := hF.DzIter i) (hτc := sEta_contOn)
    (hτ := fun _ hθ => sEta_nonneg_Ioo hθ) (zOuter0 hfin1 (by omega)) (zOuter1 hfin1 hi)

theorem mMass_lt_top {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₁ : ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ, ENNReal.ofReal (HkInt α (k + 1) F z θ))
      ≤ ENNReal.ofReal C₁)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2)) < ⊤ :=
  piece_mass_lt_top (hg := hF.mixed j i) (hτc := gamWt_contOn α)
    (hτ := fun _ hθ => gamWt_nonneg_Ioo α hθ)
    (mOuter0 hfin1 hi (by omega)) (mOuter1 hfin1 hi hij)

/-! ## The main transfer -/

theorem HkMem_of_outer {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ} {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ)) ≤ ENNReal.ofReal C₀)
    (hslmeas1 : ∀ z ∈ Work.Spaces.Iz, AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) F z θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmeas1 : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) F z θ)) (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hfin1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) F z θ)) ≤ ENNReal.ofReal C₁) :
    Work.Spaces.HkMem α k F := by
  -- the two families of `τ`-forms are honest at every `z > 0`
  have hZ : ∀ i ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
    fun i hi z hz => integrableOn_of_lt_top (hsm.DzIter i) hz sEta_contOn
      (fun _ hθ => sEta_nonneg_Ioo hθ) (zMass_lt_top hsm hfin1 hi z hz)
  have hM : ∀ i j, 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2)
        (Set.Ioo 0 (π / 2)) :=
    fun i j hi hij z hz => integrableOn_of_lt_top (hsm.mixed j i) hz (gamWt_contOn α)
      (fun _ hθ => gamWt_nonneg_Ioo α hθ) (mMass_lt_top hsm hfin1 hi hij z hz)
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes and the integrand is identically zero
      rw [show (fun θ : ℝ => HkInt α k F z θ) = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [← hz0]
        exact HkInt_zero α k F θ]
      exact integrableOn_zero
    · -- `z > 0`: `pieceSum` is a finite sum of honest `τ`-forms
      have hA : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (sEta θ * (Work.Spaces.DzIter i F z θ) ^ 2))
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
        integrable_finset_sum' _ fun i hi =>
          (hZ i (by have h := Finset.mem_range.mp hi; omega) z hzpos).const_mul _
      have hterm : ∀ i j : ℕ,
          Integrable (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            (if 1 ≤ i ∧ i + j ≤ k
              then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
            (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) := by
        intro i j
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · have heq : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
              (if 1 ≤ i ∧ i + j ≤ k
                then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
              = fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
                  (gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2) := by
            funext θ
            rw [if_pos hc]
          rw [heq]
          exact (hM i j hc.1 (by omega) z hzpos).const_mul _
        · have heq : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
              (if 1 ≤ i ∧ i + j ≤ k
                then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
              = fun _ : ℝ => (0 : ℝ) := by
            funext θ
            rw [if_neg hc, mul_zero]
          rw [heq]
          exact integrable_zero ℝ ℝ _
      have hB : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
            ∑ j ∈ Finset.range (k + 1),
              (Work.Spaces.w z) ^ 2 *
                (if 1 ≤ i ∧ i + j ≤ k
                  then gamWt α θ * (Work.Spaces.mixed j i F z θ) ^ 2 else 0))
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
        integrable_finset_sum' _ fun i hi => integrable_finset_sum' _ fun j hj => hterm i j
      have hsum : Integrable (fun θ : ℝ => pieceSum α k F z θ)
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) := by
        simp only [pieceSum]
        exact hA.add hB
      have hHk : Integrable (fun θ : ℝ => HkInt α k F z θ)
          (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
        hsum.congr (by
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
          exact (HkInt_eq_pieceSum α k (F := F) (z := z) (θ := θ)
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).symm)
      show Integrable (fun θ : ℝ => HkInt α k F z θ) (MeasureTheory.volume.restrict Iθ)
      rw [← restrict_Iθ_eq_restrict_Ioo]
      exact hHk
  · -- the outer conjunct: a.e. integrability, upgraded from `(0,∞)` to `[0,∞)`
    have houter : IntegrableOn (fun z => ∫ θ in Iθ, HkInt α k F z θ) (Set.Ioi 0) :=
      (Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral_k hC₀ hslmeas hfin0 hmeas).2
    refine houter.congr_set_ae ?_
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

end Work.FTS.ClassCHon.SliceMassUpgrade
