import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

namespace Work.FTS_RegExport.RXT.velPertAux

/-!
# `paramC2`: `C²`-regularity of the angular parametric integral

`z ↦ ∫_θ F z θ · φ θ` is `C²` on `(0,∞)` when `F` is `C²` on the open quadrant
`(0,∞) × (0,π/2)`, `φ` is continuous on `Iθ = [0,π/2]` and `F`, `D_z F`, `D_z² F` are
bounded by `C` on the open quadrant.

The proof differentiates twice under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), the local dominating function being
the constant `C/(z/2) · |φ|_∞`.  In order to avoid a second-order product-rule identity in
`∂_z`, the second derivative is computed for the scaled integrand `D_z F = z ∂_z F` (whose
`z`-derivative is `z ∂_z² F`, bounded by `C/z` because of the hypothesis on `D_z² F`), and
the two parametric integrals are related by `∫_θ D_z F = z ∫_θ ∂_z F`.
-/

/-! ## Elementary calculus helpers -/

/-- The `z`-partial derivative is the Fréchet derivative in the direction `(1,0)`. -/
private theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv

/-- The `z`-slice of a differentiable function of two variables is differentiable. -/
private theorem differentiableAt_slice_left {G : ℝ → ℝ → ℝ} {x θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (x, θ)) :
    DifferentiableAt ℝ (fun x' => G x' θ) x := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) x := by
    simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
  exact (h.hasFDerivAt.comp_hasDerivAt x hcurve).differentiableAt

/-- The `θ`-slice at a positive `z` of a function continuous on the open quadrant is
continuous. -/
private theorem slice_continuousOn {G : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {x : ℝ} (hx : 0 < x) : ContinuousOn (fun θ => G x θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hg : ContinuousOn (fun θ : ℝ => (x, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Continuous.prodMk_right x).continuousOn
  have hmap : Set.MapsTo (fun θ : ℝ => (x, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hx, hθ⟩
  exact (h.comp hg hmap).congr (fun θ _ => rfl)

/-- The `z`-slice at an interior angle of a function continuous on the open quadrant is
continuous at a positive `x`. -/
private theorem slice_continuousAt {G : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {x θ : ℝ} (hx : 0 < x) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousAt (fun x' => G x' θ) x := by
  have hV : (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ∈ 𝓝 (x, θ) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hx, hθ⟩
  have hcont : ContinuousAt (Function.uncurry G) (x, θ) := h.continuousAt hV
  have hcurve : Filter.Tendsto (fun x' : ℝ => (x', θ)) (𝓝 x) (𝓝 (x, θ)) :=
    (Continuous.prodMk_left θ).continuousAt
  show Filter.Tendsto (fun x' : ℝ => G x' θ) (𝓝 x) (𝓝 (G x θ))
  exact hcont.tendsto.comp hcurve

/-- `∂_z` lowers the order of differentiability on the open quadrant by one. -/
private theorem contDiffOn_uncurry_pz {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hdiff : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)),
      DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.fderiv_of_isOpen hV le_rfl
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => pz_eq_fderiv (hdiff p hp))

/-- `D_z` lowers the order of differentiability on the open quadrant by one. -/
private theorem contDiffOn_uncurry_Dz {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hpz := contDiffOn_uncurry_pz (n := n) h
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiff_fst.contDiffOn
  refine (h1.mul hpz).congr (fun p _ => ?_)
  simp only [Function.uncurry, Work.Spaces.Dz]

/-- **Parametric integral with one differentiation.**  If the slices of `G` and of `G'` are
continuous on `(0,π/2)`, `G` is bounded by `Kg` there, `G'` is bounded by `Cg/z`, `φ` is
continuous and bounded by `B` on `Iθ`, and `G'` is the `z`-derivative of `G` pointwise,
then `z ↦ ∫_θ G z θ · φ θ` is `C¹` on `(0,∞)` with derivative `z ↦ ∫_θ G' z θ · φ θ`. -/
private theorem paramIntegral_aux {G G' : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {B Kg Cg : ℝ}
    (hB0 : 0 ≤ B) (hKg0 : 0 ≤ Kg) (hCg0 : 0 ≤ Cg)
    (hφcont : ContinuousOn φ (Set.Ioo 0 (Real.pi / 2)))
    (hφB : ∀ θ ∈ Work.Spaces.Iθ, |φ θ| ≤ B)
    (hGbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |G z θ| ≤ Kg)
    (hG'bd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |G' z θ| ≤ Cg / z)
    (hGcont : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG'cont : ContinuousOn (Function.uncurry G') (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hdiff : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun x' => G x' θ) (G' x θ) x) :
    ContDiffOn ℝ 1 (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G u θ * φ θ) (Set.Ioi 0) ∧
      ∀ z : ℝ, 0 < z →
        HasDerivAt (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G u θ * φ θ)
          (∫ θ in Set.Ioo 0 (Real.pi / 2), G' z θ * φ θ) z := by
  have haesmφ : AEStronglyMeasurable φ (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hφcont.aestronglyMeasurable measurableSet_Ioo
  have haesmG : ∀ x : ℝ, 0 < x → AEStronglyMeasurable (fun θ => G x θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    fun x hx => (slice_continuousOn hGcont hx).aestronglyMeasurable measurableSet_Ioo
  have haesmG' : ∀ x : ℝ, 0 < x → AEStronglyMeasurable (fun θ => G' x θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    fun x hx => (slice_continuousOn hG'cont hx).aestronglyMeasurable measurableSet_Ioo
  -- local bound for `G'` on a neighbourhood of a positive point
  have hloc : ∀ z : ℝ, 0 < z → ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ : ℝ,
      0 < θ → θ < Real.pi / 2 → |G' x θ| ≤ Cg / (z / 2) := by
    intro z hz x hx θ hθ hθ2
    exact le_trans (hG'bd x (by linarith [hx.1]) θ hθ hθ2)
      (div_le_div_of_nonneg_left hCg0 (by linarith) (le_of_lt hx.1))
  -- integrability of the integrands
  have hint : ∀ z : ℝ, 0 < z → Integrable (fun θ => G z θ * φ θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    intro z hz
    refine MeasureTheory.Integrable.of_bound ((haesmG z hz).mul haesmφ) (Kg * B) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGbd z hz θ hθ.1 hθ.2) (hφB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      (abs_nonneg _) hKg0
  have hderiv : ∀ z : ℝ, 0 < z → HasDerivAt
      (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G u θ * φ θ)
      (∫ θ in Set.Ioo 0 (Real.pi / 2), G' z θ * φ θ) z := by
    intro z hz
    have hs : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hK0 : 0 ≤ Cg / (z / 2) := div_nonneg hCg0 (by linarith)
    have h1 : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun θ => G x θ * φ θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
      filter_upwards [hs] with x hx
      exact (haesmG x (by linarith [hx.1])).mul haesmφ
    have h2 : Integrable (fun θ => G z θ * φ θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hint z hz
    have h3 : AEStronglyMeasurable (fun θ => G' z θ * φ θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := (haesmG' z hz).mul haesmφ
    have h4 : ∀ᵐ a ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ∀ x ∈ Set.Ioo (z / 2) (2 * z),
          ‖G' x a * φ a‖ ≤ (fun _ : ℝ => Cg / (z / 2) * B) a := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hloc z hz x hx θ hθ.1 hθ.2)
        (hφB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _) hK0
    have h5 : Integrable (fun _ : ℝ => Cg / (z / 2) * B)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)
    have h6 : ∀ᵐ a ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ∀ x ∈ Set.Ioo (z / 2) (2 * z),
          HasDerivAt (fun x' => G x' a * φ a) (G' x a * φ a) x := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro x hx
      exact (hdiff x θ (by linarith [hx.1]) hθ.1 hθ.2).mul_const (φ θ)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      (F := fun u θ => G u θ * φ θ) (F' := fun u θ => G' u θ * φ θ)
      (bound := fun _ => Cg / (z / 2) * B) (x₀ := z) (s := Set.Ioo (z / 2) (2 * z))
      hs h1 h2 h3 h4 h5 h6).2
  have hcontderiv : ContinuousOn
      (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G' u θ * φ θ) (Set.Ioi 0) := by
    intro z hz
    have hz0 : 0 < z := by simpa using hz
    have hs : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hK0 : 0 ≤ Cg / (z / 2) := div_nonneg hCg0 (by linarith)
    refine (MeasureTheory.continuousAt_of_dominated
      (μ := volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      (F := fun u θ => G' u θ * φ θ) (bound := fun _ => Cg / (z / 2) * B) (x₀ := z)
      ?_ ?_ ?_ ?_).continuousWithinAt
    · filter_upwards [hs] with x hx
      exact (haesmG' x (by linarith [hx.1, hz0])).mul haesmφ
    · filter_upwards [hs] with x hx
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hloc z hz0 x hx θ hθ.1 hθ.2)
        (hφB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _) hK0
    · exact MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (slice_continuousAt hG'cont hz0 hθ).mul_const (φ θ)
  refine ⟨?_, hderiv⟩
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (0 : WithTop ℕ∞)) isOpen_Ioi).mpr
    ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (hderiv z (by simpa using hz)).differentiableAt.differentiableWithinAt
  · exact fun h => absurd h (by simp)
  · rw [contDiffOn_zero]
    exact hcontderiv.congr (fun z hz => (hderiv z (by simpa using hz)).deriv)

/-! ## The main statement -/

theorem paramC2 {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    ContDiffOn ℝ 2 (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ) (Set.Ioi 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi42 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hquarter : Real.pi / 4 ∈ Work.Spaces.Iθ := ⟨le_of_lt hpi4, le_of_lt hpi42⟩
  -- a bound for `φ` on `Iθ`
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hB0 : 0 ≤ B := by
    have h := hB (Real.pi / 4) hquarter
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  have hφB : ∀ θ ∈ Work.Spaces.Iθ, |φ θ| ≤ B := by
    intro θ hθ
    have h := hB θ hθ
    rwa [Real.norm_eq_abs] at h
  have hφcont : ContinuousOn φ (Set.Ioo 0 (Real.pi / 2)) :=
    hφ.mono (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hC0 : 0 ≤ C := by
    have h := (hb 1 (Real.pi / 4) one_pos hpi4 hpi42).1
    exact le_trans (abs_nonneg _) h
  have hVopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hquad : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      (x, θ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun x θ hx hθ hθ2 => ⟨hx, hθ, hθ2⟩
  -- the pointwise hypotheses
  have hFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ C :=
    fun z hz θ hθ hθ2 => (hb z θ hz hθ hθ2).1
  have hDzFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz F z θ| ≤ C := fun z hz θ hθ hθ2 => (hb z θ hz hθ hθ2).2.1
  have hDzIterFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter 2 F z θ| ≤ C := fun z hz θ hθ hθ2 => (hb z θ hz hθ hθ2).2.2
  have hpzFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pz F z θ| ≤ C / z := by
    intro z hz θ hθ hθ2
    have h : z * |Work.Spaces.pz F z θ| ≤ C := by
      have h := hDzFbd z hz θ hθ hθ2
      rw [show Work.Spaces.Dz F z θ = z * Work.Spaces.pz F z θ from rfl, abs_mul,
        abs_of_pos hz] at h
      exact h
    rw [mul_comm] at h
    exact (le_div_iff₀ hz).mpr h
  have hpzDzFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pz (Work.Spaces.Dz F) z θ| ≤ C / z := by
    intro z hz θ hθ hθ2
    have h : z * |Work.Spaces.pz (Work.Spaces.Dz F) z θ| ≤ C := by
      have h := hDzIterFbd z hz θ hθ hθ2
      rw [show Work.Spaces.DzIter 2 F z θ
          = z * Work.Spaces.pz (Work.Spaces.Dz F) z θ from rfl, abs_mul, abs_of_pos hz] at h
      exact h
    rw [mul_comm] at h
    exact (le_div_iff₀ hz).mpr h
  -- the joint continuity of the integrands
  have hFcont : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hF.continuousOn
  have hpzFcont : ContinuousOn (Function.uncurry (Work.Spaces.pz F))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (contDiffOn_uncurry_pz (n := 1) hF).continuousOn
  have hDzFcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz F))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (contDiffOn_uncurry_Dz (n := 1) hF).continuousOn
  have hpzDzFcont : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz F)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_uncurry_pz (n := 0) (contDiffOn_uncurry_Dz (n := 1) hF)).continuousOn
  -- pointwise `z`-derivatives
  have hdiffF : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun x' => F x' θ) (Work.Spaces.pz F x θ) x := by
    intro x θ hx hθ hθ2
    have hd : DifferentiableAt ℝ (Function.uncurry F) (x, θ) :=
      (hF.differentiableOn (by norm_num)).differentiableAt
        (hVopen.mem_nhds (hquad x θ hx hθ hθ2))
    exact (differentiableAt_slice_left hd).hasDerivAt
  have hdiffDz : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun x' => Work.Spaces.Dz F x' θ)
        (Work.Spaces.pz (Work.Spaces.Dz F) x θ) x := by
    intro x θ hx hθ hθ2
    have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.Dz F)) (x, θ) :=
      ((contDiffOn_uncurry_Dz (n := 1) hF).differentiableOn (by norm_num)).differentiableAt
        (hVopen.mem_nhds (hquad x θ hx hθ hθ2))
    exact (differentiableAt_slice_left hd).hasDerivAt
  -- the two parametric integrals
  have hFaux := paramIntegral_aux (G := F) (G' := Work.Spaces.pz F) (φ := φ)
    (B := B) (Kg := C) (Cg := C) hB0 hC0 hC0 hφcont hφB hFbd hpzFbd
    hFcont hpzFcont hdiffF
  have hDzaux := paramIntegral_aux (G := Work.Spaces.Dz F)
    (G' := Work.Spaces.pz (Work.Spaces.Dz F)) (φ := φ) (B := B) (Kg := C) (Cg := C)
    hB0 hC0 hC0 hφcont hφB hDzFbd hpzDzFbd hDzFcont hpzDzFcont hdiffDz
  -- the scaled integral is `z` times the unscaled one
  have hA'eq : ∀ z : ℝ, 0 < z →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.Dz F z θ * φ θ)
        = z * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.pz F z θ * φ θ) := by
    intro z _
    rw [← integral_const_mul z (fun θ => Work.Spaces.pz F z θ * φ θ)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [show Work.Spaces.Dz F z θ = z * Work.Spaces.pz F z θ from rfl]
    ring
  -- continuity of the derivative of the scaled integral
  have hB'cont : ContinuousOn
      (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.Spaces.pz (Work.Spaces.Dz F) u θ * φ θ) (Set.Ioi 0) := by
    have hmp := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (0 : WithTop ℕ∞))
      (f := fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.Dz F u θ * φ θ)
      (s := Set.Ioi 0) isOpen_Ioi).mp hDzaux.1
    exact (contDiffOn_zero.mp hmp.2.2).congr
      (fun z hz => (hDzaux.2 z (by simpa using hz)).deriv.symm)
  -- `C¹` for the unscaled integral
  have hAcd : ContDiffOn ℝ 1
      (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.pz F z θ * φ θ) (Set.Ioi 0) := by
    refine (hDzaux.1.div contDiffOn_id (fun z hz => ne_of_gt (by simpa using hz))).congr
      (fun z hz => ?_)
    have hz0 : 0 < z := by simpa using hz
    have h := hA'eq z hz0
    change (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.pz F z θ * φ θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.Dz F z θ * φ θ) / z
    rw [h, eq_div_iff (ne_of_gt hz0)]
    ring
  -- `C²` for the parametric integral over `(0,π/2)`
  have hG0cd : ContDiffOn ℝ 2
      (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ * φ θ) (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (1 : WithTop ℕ∞))
      (f := fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ * φ θ)
      (s := Set.Ioi 0) isOpen_Ioi).mpr ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (hFaux.2 z (by simpa using hz)).differentiableAt.differentiableWithinAt
    · exact fun h => absurd h (by simp)
    · exact hAcd.congr (fun z hz => (hFaux.2 z (by simpa using hz)).deriv)
  -- transfer from `(0,π/2)` to `[0,π/2]`
  have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have hset : ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))
  have hIccdiff : Work.Spaces.Iθ \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro x hx
    obtain ⟨hxI, hxnot⟩ := hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hxnot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hxnot with h | h
    · exact Or.inl (le_antisymm h hxI.1)
    · exact Or.inr (le_antisymm hxI.2 h)
  have hIoodiff : Set.Ioo 0 (Real.pi / 2) \ Work.Spaces.Iθ ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro x hx
    exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
  have haeeq : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨measure_mono_null hIccdiff hnull, measure_mono_null hIoodiff hnull⟩
  exact hG0cd.congr (fun _ _ => setIntegral_congr_set haeeq)

end Work.FTS_RegExport.RXT.velPertAux
