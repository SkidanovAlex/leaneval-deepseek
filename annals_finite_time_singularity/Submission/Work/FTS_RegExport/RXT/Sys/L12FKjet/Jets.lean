import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Basic
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKjet.Jets` — the `D_z`-jet identities and the linearity of `D_z^j`

Third part of the jet package of `L12_FK_jets_of_datum`: the identities

* `D_z L₁₂(F) = -Qang F 0 = -𝔽K(F)`,   `D_z² L₁₂(F) = -Qang F 1`,
* `D_z 𝔽K(F) = Qang F 1`,               `D_z² 𝔽K(F) = Qang F 2`

(where `D_z = z∂_z` and `Qang F m z = ∫_θ K(θ)D_z^mF(z,θ) dθ`), together with the linearity of
`D_z^j` (`j ≤ 2`) in the function at a point at which the function and its iterates are
differentiable, and the elementary real bound `C ≤ C⁴` for `C ≥ 1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `D_z L₁₂(F) = -Qang F 0` eventually (hence on all of `(0,∞)`). -/
theorem lfj_DzdIter_one_L12_eq {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hL : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => Work.Construction.L12 F z) (-(Work.Construction.L12dens F u)) u) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)
      =ᶠ[𝓝 z] fun u => -(Work.Elliptic.Qang F 0 u) := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
  have h1 : u * Work.Construction.L12dens F u = Work.Construction.FK F u :=
    Work.Construction.mul_L12dens_eq_FK (F := F) (ne_of_gt hu)
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z) u
      = u * deriv (fun z => Work.Construction.L12 F z) u from rfl, (hL u hu).deriv,
    lfj_Qang_zero_eq_FK F u, ← h1]
  ring

/-- **`D_z L₁₂(F) = -𝔽K(F)`.** -/
theorem lfj_DzdIter_one_L12 {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hL : HasDerivAt (fun z => Work.Construction.L12 F z)
      (-(Work.Construction.L12dens F z)) z) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z) z
      = - Work.Construction.FK F z := by
  have h1 : z * Work.Construction.L12dens F z = Work.Construction.FK F z :=
    Work.Construction.mul_L12dens_eq_FK (F := F) (ne_of_gt hz)
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z) z
      = z * deriv (fun z => Work.Construction.L12 F z) z from rfl, hL.deriv, ← h1]
  ring

/-- **`D_z² L₁₂(F) = -Qang F 1`.** -/
theorem lfj_DzdIter_two_L12 {F : ℝ → ℝ → ℝ} {z : ℝ}
    (h1e : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)
      =ᶠ[𝓝 z] fun u => -(Work.Elliptic.Qang F 0 u))
    (hQ0 : HasDerivAt (Work.Elliptic.Qang F 0) (Work.Elliptic.Qang F 1 z / z) z)
    (hz : 0 < z) :
    Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 F z) z
      = -(Work.Elliptic.Qang F 1 z) := by
  have hder : deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)) z
      = -(Work.Elliptic.Qang F 1 z / z) := by
    rw [h1e.deriv_eq]
    exact hQ0.neg.deriv
  show z * deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)) z
      = -(Work.Elliptic.Qang F 1 z)
  rw [hder, show z * (-(Work.Elliptic.Qang F 1 z / z))
      = -(z * Work.Elliptic.Qang F 1 z / z) by ring,
    mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-- `D_z 𝔽K(F) = Qang F 1` eventually. -/
theorem lfj_DzdIter_one_FK_eq {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Construction.FK F z)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F u θ * Work.Spaces.K θ) u) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) =ᶠ[𝓝 z]
      Work.Elliptic.Qang F 1 := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) u
      = u * deriv (fun z => Work.Construction.FK F z) u from rfl, (hF u hu).deriv,
    lfj_Qang_one_eq F u]

/-- **`D_z 𝔽K(F) = Qang F 1`.** -/
theorem lfj_DzdIter_one_FK {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : HasDerivAt (fun z => Work.Construction.FK F z)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ) z) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) z
      = Work.Elliptic.Qang F 1 z := by
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) z
      = z * deriv (fun z => Work.Construction.FK F z) z from rfl, hF.deriv,
    lfj_Qang_one_eq F z]

/-- **`D_z² 𝔽K(F) = Qang F 2`.** -/
theorem lfj_DzdIter_two_FK {F : ℝ → ℝ → ℝ} {z : ℝ}
    (h1e : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) =ᶠ[𝓝 z]
      Work.Elliptic.Qang F 1)
    (hQ1 : HasDerivAt (Work.Elliptic.Qang F 1) (Work.Elliptic.Qang F 2 z / z) z)
    (hz : 0 < z) :
    Work.Elliptic.DzdIter 2 (fun z => Work.Construction.FK F z) z
      = Work.Elliptic.Qang F 2 z := by
  have hder : deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z)) z
      = Work.Elliptic.Qang F 2 z / z := by
    rw [h1e.deriv_eq, hQ1.deriv]
  show z * deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z)) z
      = Work.Elliptic.Qang F 2 z
  rw [hder, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-! ## Linearity of the `D_z`-jets in the function -/

/-- `D_z^j` (`j ≤ 2`) is linear at a point at which `u`, `v` and their `D_z`-iterates are
differentiable. -/
theorem lfj_DzdIter_linear {u v : ℝ → ℝ} {a b z : ℝ}
    (hu1 : DifferentiableAt ℝ u z) (hv1 : DifferentiableAt ℝ v z)
    (hue : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ u w)
    (hve : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ v w)
    (hu2 : DifferentiableAt ℝ (Work.Elliptic.DzdIter 1 u) z)
    (hv2 : DifferentiableAt ℝ (Work.Elliptic.DzdIter 1 v) z) :
    ∀ j : ℕ, j ≤ 2 →
      Work.Elliptic.DzdIter j (fun w => a * u w + b * v w) z
        = a * Work.Elliptic.DzdIter j u z + b * Work.Elliptic.DzdIter j v z := by
  intro j hj
  interval_cases j
  · simp only [Work.Elliptic.DzdIter_zero]
  · simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
    have hsum : HasDerivAt (fun w => a * u w + b * v w)
        (a * deriv u z + b * deriv v z) z :=
      (hu1.hasDerivAt.const_mul a).add (hv1.hasDerivAt.const_mul b)
    rw [hsum.deriv]
    ring
  · have hev : Work.Elliptic.DzdIter 1 (fun w => a * u w + b * v w)
        =ᶠ[𝓝 z] fun w => a * Work.Elliptic.DzdIter 1 u w + b * Work.Elliptic.DzdIter 1 v w := by
      filter_upwards [hue, hve] with w huw hvw
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
      have hsum : HasDerivAt (fun w' => a * u w' + b * v w')
          (a * deriv u w + b * deriv v w) w :=
        (huw.hasDerivAt.const_mul a).add (hvw.hasDerivAt.const_mul b)
      rw [hsum.deriv]
      ring
    have hder : deriv (Work.Elliptic.DzdIter 1 (fun w => a * u w + b * v w)) z
        = a * deriv (Work.Elliptic.DzdIter 1 u) z
          + b * deriv (Work.Elliptic.DzdIter 1 v) z := by
      rw [hev.deriv_eq]
      have hsum : HasDerivAt
          (fun w => a * Work.Elliptic.DzdIter 1 u w + b * Work.Elliptic.DzdIter 1 v w)
          (a * deriv (Work.Elliptic.DzdIter 1 u) z + b * deriv (Work.Elliptic.DzdIter 1 v) z) z :=
        (hu2.hasDerivAt.const_mul a).add (hv2.hasDerivAt.const_mul b)
      exact hsum.deriv
    show z * deriv (Work.Elliptic.DzdIter 1 (fun w => a * u w + b * v w)) z
        = a * (z * deriv (Work.Elliptic.DzdIter 1 u) z)
          + b * (z * deriv (Work.Elliptic.DzdIter 1 v) z)
    rw [hder]
    ring

/-- The bound for a linear combination of two functions whose `D_z`-jets of order `≤ 2` are
bounded by `B`. -/
theorem lfj_DzdIter_lin_bound {u v : ℝ → ℝ} {a b z B : ℝ}
    (hlin : ∀ j : ℕ, j ≤ 2 →
      Work.Elliptic.DzdIter j (fun w => a * u w + b * v w) z
        = a * Work.Elliptic.DzdIter j u z + b * Work.Elliptic.DzdIter j v z)
    (hBu : ∀ j : ℕ, j ≤ 2 → |Work.Elliptic.DzdIter j u z| ≤ B)
    (hBv : ∀ j : ℕ, j ≤ 2 → |Work.Elliptic.DzdIter j v z| ≤ B) :
    ∀ j : ℕ, j ≤ 2 →
      |Work.Elliptic.DzdIter j (fun w => a * u w + b * v w) z| ≤ (|a| + |b|) * B := by
  intro j hj
  rw [hlin j hj]
  calc |a * Work.Elliptic.DzdIter j u z + b * Work.Elliptic.DzdIter j v z|
      ≤ |a * Work.Elliptic.DzdIter j u z| + |b * Work.Elliptic.DzdIter j v z| := abs_add_le _ _
    _ = |a| * |Work.Elliptic.DzdIter j u z| + |b| * |Work.Elliptic.DzdIter j v z| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a| * B + |b| * B :=
        add_le_add (mul_le_mul_of_nonneg_left (hBu j hj) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (hBv j hj) (abs_nonneg b))
    _ = (|a| + |b|) * B := by ring

/-- `C ≤ C⁴` for `C ≥ 1`. -/
theorem lfj_le_pow_four {C : ℝ} (hC1 : 1 ≤ C) : C ≤ C ^ 4 := by
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have h1 : (1 : ℝ) ≤ C ^ 3 := one_le_pow₀ (n := 3) hC1
  calc C = C * 1 := by ring
    _ ≤ C * C ^ 3 := mul_le_mul_of_nonneg_left h1 hC0
    _ = C ^ 4 := by ring

/-- `|x| ≤ 18 C` upgrades to `|x| ≤ 64 C⁴` for `C ≥ 1`. -/
theorem lfj_le_const {x C : ℝ} (hC1 : 1 ≤ C) (h : |x| ≤ 18 * C) : |x| ≤ 64 * C ^ 4 := by
  have hC4 := lfj_le_pow_four hC1
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [h, hC4, hC0, hC1]

end Work.FTS_RegExport.RXT.Sys
