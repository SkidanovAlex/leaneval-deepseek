/-
# `Coer1SO/zibpO_of` — the `ZIBPO` package in the open class

This file proves `Work.FTS.CoercivityFix.Coer1SO.ZIBPO u` from

* the open-quadrant smoothness `SmoothOpen u` (instead of the analytic `Spaces.SmoothNbhd`),
* the two boundary limits of `z (u w)²` at `z = 0⁺` and `z = ∞` (for *every* interior angle),
* the joint integrability of `(u w)²` and of the `𝓛`-pairing `𝓛u·u·w²` on the quadrant.

It is the verbatim open-class analogue of `Work.FTS.CoercivityFix.Coer1.zibp_of` (proved for
`Work.FTS.LocData.SmoothQuad` in `Coer1/IntFacts.lean`): the two pointwise identities

* `l_self_w_sq_O` : `𝓛u·u·w² = (u w)² + ½ z ∂_z((u w)²)`,
* `deriv_zw_sq_O`  : `∂_z(z (u w)²) = (u w)² + z ∂_z((u w)²)`,

hence `deriv_zw_sq_eq_O` : `∂_z(z (u w)²) = 2 (𝓛u·u·w²) − (u w)²`,

are proved with the *open* `z`-slice differentiability `SmoothOpen.curry_z` (the whole
`SmoothQuad` proof used only the differentiability of the `z`-slice at `z > 0`, which
`SmoothOpen` supplies on `Ioi 0`).  The a.e.-in-`θ` slicing of the two joint integrability
certificates is `Coer1.ae_slice_of_integrableOn`, and the identification of the restricted
measure `volume.restrict Iz` with `volume.restrict (Ioi 0)` is `Coer1.iz_ae_restrict` (the two
differ only by the null point `z = 0`).  Everything is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1SO.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1SO

open scoped Real Topology
open MeasureTheory Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The pointwise identities in the open class -/

/-- `𝓛u·u·w² = (u w)² + ½ z ∂_z((u w)²)` on the open quadrant, for `SmoothOpen u`. -/
theorem l_self_w_sq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (u z θ * Work.Spaces.w z) ^ 2
        + (1 / 2) * (z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z) := by
  have hd : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hf : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z := hd.hasDerivAt
  have hLw : Work.Coercivity.L u z θ * Work.Spaces.w z
      = u z θ * Work.Spaces.w z
        + z * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ :=
    Work.Coercivity.L_mul_w_deriv hz hf
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Work.Spaces.w z') z :=
    (hf.mul (Work.Coercivity.hasDerivAt_w (ne_of_gt hz))).differentiableAt
  have hgsq : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (u z θ * Work.Spaces.w z)
          * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
        = 2 * (u z θ * Work.Spaces.w z) ^ (2 - 1)
            * deriv (fun z' => u z' θ * Work.Spaces.w z') z := h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one]
    rfl
  have hkey : Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (Work.Coercivity.L u z θ * Work.Spaces.w z) * (u z θ * Work.Spaces.w z) := by
    ring
  rw [hkey, hLw, hgsq]
  ring

/-- `∂_z(z (u w)²) = (u w)² + z ∂_z((u w)²)` on the open quadrant, for `SmoothOpen u`. -/
theorem deriv_zw_sq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = (u z θ * Work.Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z := by
  have hd : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hw : DifferentiableAt ℝ (Work.Spaces.w) z :=
    (Work.Coercivity.hasDerivAt_w (ne_of_gt hz)).differentiableAt
  have hg : DifferentiableAt ℝ (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    (hd.mul hw).pow 2
  have hmain : deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = 1 * (u z θ * Work.Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    HasDerivAt.deriv ((hasDerivAt_id z).mul hg.hasDerivAt)
  rw [hmain]; ring

/-- The form of `deriv_zw_sq_O` that identifies the derivative with the `𝓛`-pairing:
`∂_z(z (u w)²) = 2 (𝓛u·u·w²) − (u w)²`. -/
theorem deriv_zw_sq_eq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2)
        - (u z θ * Work.Spaces.w z) ^ 2 := by
  have h1 := deriv_zw_sq_O hu hz hθ
  have h2 := l_self_w_sq_O hu hz hθ
  linarith [h1, h2]

/-! ## The package -/

theorem zibpO_of {u : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hbd0 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbdT : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0))
    (hSq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.FTS.CoercivityFix.Coer1SO.ZIBPO u := by
  refine ⟨hs, hbd0, hbdT, ?_, ?_⟩
  · refine (Work.FTS.CoercivityFix.Coer1.ae_slice_of_integrableOn hSq).mono (fun θ hθ => ?_)
    rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    exact hθ
  · refine (((Work.FTS.CoercivityFix.Coer1.ae_slice_of_integrableOn hL).and
      (Work.FTS.CoercivityFix.Coer1.ae_slice_of_integrableOn hSq)).and
      Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo).mono (fun θ hθ => ?_)
    obtain ⟨⟨hLθ, hSqθ⟩, hθIoo⟩ := hθ
    have h1 : MeasureTheory.IntegrableOn
        (fun z => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2) (Set.Ioi 0) := by
      rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
      exact hLθ
    have h2 : MeasureTheory.IntegrableOn
        (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
      rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
      exact hSqθ
    have h3 := (h1.const_mul 2).sub h2
    refine MeasureTheory.IntegrableOn.congr_fun h3 (fun z hz => ?_) measurableSet_Ioi
    exact (deriv_zw_sq_eq_O hs hz hθIoo).symm

end Work.FTS.CoercivityFix.Coer1SO
