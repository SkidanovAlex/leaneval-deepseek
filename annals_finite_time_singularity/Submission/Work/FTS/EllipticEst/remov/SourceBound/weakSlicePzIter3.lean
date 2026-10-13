import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceIntegrable
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBoxIntegrable
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceDeriv
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceDerivBox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The three angular slices involved

Writing `A`, `B`, `C` for the slices `∂_z(z²∂_z²Ψ)·sinθcos²θ`, `∂_z²Ψ·sinθcos²θ` and
`∂_z³Ψ·sinθcos²θ`, the product rule for `∂_z` reads `A = 2z·B + z²·C` on `(0,∞) × (0,π/2)`,
so that `C = z^{-2}A - 2z^{-1}B` there.  The two lemmas below make this precise. -/

/-- The slice `θ ↦ ∂_z³Ψ(z,θ)·sinθcos²θ`, whose integrability is the target. -/
private noncomputable def pzIter3Slice (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ

/-- The slice `θ ↦ ∂_z(z²∂_z²Ψ)(z,θ)·sinθcos²θ`. -/
private noncomputable def zsqPzIter2Slice (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
    * Work.Elliptic.sinCos2 θ

/-- The slice `θ ↦ ∂_z²Ψ(z,θ)·sinθcos²θ`. -/
private noncomputable def pzIter2Slice (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ

/-! ## Elementary analytic facts -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
private lemma continuous_sinCos2_snd :
    Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
  simp only [Work.Elliptic.sinCos2]
  exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).comp continuous_snd

/-- The product rule for `∂_z` on a slice of an open-quadrant-smooth function:
`∂_z(z²g) = 2zg + z²∂_zg` for `z > 0`, `θ ∈ (0,π/2)`. -/
private lemma pz_zsq_mul_eq (g : ℝ → ℝ → ℝ) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    Work.Spaces.pz (fun z θ => z ^ 2 * g z θ) z θ
      = 2 * z * g z θ + z ^ 2 * Work.Spaces.pz g z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  have hd : DifferentiableAt ℝ (fun z' => g z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hg.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem))
  have hderiv : HasDerivAt (fun z' : ℝ => z' ^ 2 * g z' θ)
      (2 * z ^ (2 - 1) * g z θ + z ^ 2 * deriv (fun z' => g z' θ) z) z :=
    (hasDerivAt_pow 2 z).mul hd.hasDerivAt
  show deriv (fun z' : ℝ => z' ^ 2 * g z' θ) z
      = 2 * z * g z θ + z ^ 2 * deriv (fun z' => g z' θ) z
  rw [hderiv.deriv]
  have h2 : (2 : ℕ) - 1 = 1 := rfl
  rw [h2, pow_one]

/-- The product rule at `g = ∂_z²Ψ`: `∂_z(z²∂_z²Ψ) = 2z∂_z²Ψ + z²∂_z³Ψ` in the interior. -/
private lemma pz_zsq_pzIter2_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = 2 * z * Work.Spaces.pzIter 2 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ :=
  pz_zsq_mul_eq (Work.Spaces.pzIter 2 Ψ) (hS.pzIter 2) hz hθ

/-- The division form of the product rule, on the slices: in the interior,
`∂_z³Ψ·sinθcos²θ = z^{-2}·(∂_z(z²∂_z²Ψ)·sinθcos²θ) - 2z^{-1}·(∂_z²Ψ·sinθcos²θ)`. -/
private lemma pzIter3Slice_eq {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    pzIter3Slice Ψ z θ
      = (z ^ 2)⁻¹ * zsqPzIter2Slice Ψ z θ - (2 * z⁻¹) * pzIter2Slice Ψ z θ := by
  simp only [pzIter3Slice, zsqPzIter2Slice, pzIter2Slice]
  rw [pz_zsq_pzIter2_eq hS hz hθ]
  have hz0 : z ≠ 0 := ne_of_gt hz
  field_simp
  ring

/-- The absolute-value form of `pzIter3Slice_eq`, valid on **all** of `Iθ`: at the two
endpoints both sides of the inequality vanish because `sinθcos²θ = 0` there. -/
private lemma pzIter3Slice_abs_le {Ψ : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |pzIter3Slice Ψ z θ|
      ≤ (z ^ 2)⁻¹ * |zsqPzIter2Slice Ψ z θ| + (2 * z⁻¹) * |pzIter2Slice Ψ z θ| := by
  by_cases hint : θ ∈ Set.Ioo (0 : ℝ) (π/2)
  · rw [pzIter3Slice_eq hS hz hint]
    have h1 : (0 : ℝ) ≤ (z ^ 2)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ 2 * z⁻¹ := by positivity
    calc |(z ^ 2)⁻¹ * zsqPzIter2Slice Ψ z θ - (2 * z⁻¹) * pzIter2Slice Ψ z θ|
        ≤ |(z ^ 2)⁻¹ * zsqPzIter2Slice Ψ z θ| + |(2 * z⁻¹) * pzIter2Slice Ψ z θ| :=
          abs_sub _ _
      _ = (z ^ 2)⁻¹ * |zsqPzIter2Slice Ψ z θ| + (2 * z⁻¹) * |pzIter2Slice Ψ z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
  · have hs : Work.Elliptic.sinCos2 θ = 0 := by
      have hmemθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
      rcases eq_or_lt_of_le hmemθ.1 with h0 | h0
      · rw [← h0]; simp [Work.Elliptic.sinCos2]
      · rcases eq_or_lt_of_le hmemθ.2 with hpi | hpi
        · rw [hpi]; simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]
        · exact absurd ⟨h0, hpi⟩ hint
    simp only [pzIter3Slice, zsqPzIter2Slice, pzIter2Slice, hs, mul_zero, abs_zero, add_zero]
    exact le_refl 0

/-! ## The main lemma -/

/-- **Slice and box integrability of `∂_z³Ψ · sinθcos²θ`.**

For a datum of the weak class `EllWeakPos α k F Ψ` with `k ≥ 2`:
* for every `z > 0` the slice `θ ↦ pzIter 3 Ψ z θ * sinCos2 θ` is integrable on `Iθ`;
* for every `a > 0` and every `b` the function `(z,θ) ↦ pzIter 3 Ψ z θ * sinCos2 θ` is integrable
  on the product of `(a,b]` and `Iθ`.

Proof sketch.  The pointwise product rule gives, for `θ ∈ (0,π/2)`,
`pz (fun z θ => z^2 * pzIter 2 Ψ z θ) z θ = 2 * z * pzIter 2 Ψ z θ + z^2 * pzIter 3 Ψ z θ`
(the differentiability of `z ↦ pzIter 2 Ψ z θ` on `(0,∞)` comes from the smoothness of `Ψ` on the
open quadrant; the endpoints `θ = 0, π/2` are irrelevant because one works a.e. on `Iθ`).
`weakSliceDeriv` of this directory gives the slice integrability of
`pz (fun z θ => z^2 * pzIter 2 Ψ z θ) · sinCos2`, `weakSliceDerivBox` the corresponding box
integrability, and `weakSliceIntegrable` (resp. `weakSliceBoxIntegrable`) the slice (resp. box)
integrability of `pzIter 2 Ψ · sinCos2`.  For fixed `z > 0` (resp. on `(a,b]`, where `z ≥ a > 0`)
one divides by `z^2`: the difference of the two integrable functions is integrable, and
multiplication by the bounded scalar `z^{-2}` preserves integrability. -/
theorem weakSlicePzIter3 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∀ z, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
      (∀ a b : ℝ, 0 < a → MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  constructor
  · -- ## The slice integrability
    intro z hz
    have hA : MeasureTheory.IntegrableOn (zsqPzIter2Slice Ψ z) Work.Spaces.Iθ :=
      (weakSliceDeriv hk h).2 z hz
    have hB : MeasureTheory.IntegrableOn (pzIter2Slice Ψ z) Work.Spaces.Iθ :=
      (weakSliceIntegrable hk h).2 z hz
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2)⁻¹ * zsqPzIter2Slice Ψ z θ - (2 * z⁻¹) * pzIter2Slice Ψ z θ)
        Work.Spaces.Iθ :=
      (hA.const_mul ((z ^ 2)⁻¹)).sub (hB.const_mul (2 * z⁻¹))
    refine hint.congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    exact (pzIter3Slice_eq hS hz hθ).symm
  · -- ## The box integrability
    intro a b ha
    have hA : MeasureTheory.Integrable (Function.uncurry (zsqPzIter2Slice Ψ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      (weakSliceDerivBox hk h) a b ha |>.2
    have hB : MeasureTheory.Integrable (Function.uncurry (pzIter2Slice Ψ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      weakSliceBoxIntegrable hk h a b ha
    refine MeasureTheory.Integrable.mono'
      (g := fun p : ℝ × ℝ => (a ^ 2)⁻¹ * |Function.uncurry (zsqPzIter2Slice Ψ) p|
        + (2 * a⁻¹) * |Function.uncurry (pzIter2Slice Ψ) p|) ?_ ?_ ?_
    · exact (hA.abs.const_mul ((a ^ 2)⁻¹)).add (hB.abs.const_mul (2 * a⁻¹))
    · refine Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ ?_ ha.le
      exact (hS.pzIter 3).continuousOn.mul continuous_sinCos2_snd.continuousOn
    · rw [MeasureTheory.Measure.prod_restrict (Set.Ioc a b) Work.Spaces.Iθ]
      refine MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ioc.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc))
        (fun p hp => ?_)
      obtain ⟨hzp, hθp⟩ := hp
      rw [Real.norm_eq_abs]
      have hz1 : 0 < p.1 := lt_trans ha hzp.1
      have hb := pzIter3Slice_abs_le hS hz1 hθp
      have hh1 : (p.1 ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hzp.1.le 2)
      have hh2 : 2 * p.1⁻¹ ≤ 2 * a⁻¹ := by
        have hle : p.1⁻¹ ≤ a⁻¹ := inv_anti₀ ha hzp.1.le
        linarith
      have h1 := mul_le_mul_of_nonneg_right hh1 (abs_nonneg (zsqPzIter2Slice Ψ p.1 p.2))
      have h2 := mul_le_mul_of_nonneg_right hh2 (abs_nonneg (pzIter2Slice Ψ p.1 p.2))
      exact le_trans hb (add_le_add h1 h2)

end Work.FTS.EllipticEst.remov.SourceBound
