import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The iterated derivatives `D_z^j D_θ^i` in the logarithmic coordinates

Let `sOf z = log z`, `zetaOf θ = log tan θ` be the logarithmic coordinates of
`Submission.Work.FTS.StrongEps.Basic`, in which the paper's operators become

  `D_z = z ∂_z = ∂_s`,   `D_θ = sin(2θ) ∂_θ = 2 ∂_ζ`.

This file proves that for a function `C` of class `C^∞` on `ℝ × ℝ` the pull-back
`(z,θ) ↦ C (sOf z, zetaOf θ)` satisfies

  `D_z^j D_θ^i (C ∘ (sOf, zetaOf)) = 2^i · ∂₁^j ∂₂^i C ∘ (sOf, zetaOf)`

on the open quadrant `(0,∞) × (0,π/2)`.  Since `∂₁^j ∂₂^i C` is `Kd C j i`
(`Kd_eq` of `Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial`), this is the
statement `mixed_logCoords` below.

The proof is by induction on the two indices, the induction steps being the two
chain rules

* `Dz (fun z θ => c * V (sOf z, zetaOf θ)) = fun z θ => c * ∂₁V (sOf z, zetaOf θ)`
  (`Dz_scalar_pull`), with `deriv sOf z = 1/z` so that the factor `z` cancels;
* `Dth (fun z θ => c * V (sOf z, zetaOf θ)) = fun z θ => c * 2 * ∂₂V (sOf z, zetaOf θ)`
  (`Dth_scalar_pull`), with `sin(2θ) · deriv zetaOf θ = 2` (`deriv_zetaOf_mul_sin`).

Everything is stated as an equality on the open quadrant, because the pull-back is
not differentiable at `z ≤ 0` (`log` is junk there).
-/

noncomputable section

open scoped Real Topology
open Set Filter

open Work.FTS.StrongEps (sOf zetaOf Kd Quad partFst partSnd
  Kd_eq Kd_zero_eq Kd_succ_eq Kd_zero_succ Kd_smooth Kd_zero_zero)

namespace Work.FTS.EpsEngine

namespace MixLog

set_option autoImplicit false

/-! ## The open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
theorem isOpen_quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioo

/-! ## The `θ`-derivative of the log-tangent coordinate -/

/-- `sin(2θ) · d/dθ (log tan θ) = 2`: the derivative of `zetaOf` is `1/(sin θ cos θ)`. -/
theorem deriv_zetaOf_mul_sin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) * deriv zetaOf θ = 2 := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have htan : Real.tan θ ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero (ne_of_gt hsin) hcos
  have hd : HasDerivAt (fun θ : ℝ => Real.log (Real.tan θ))
      ((1 / Real.cos θ ^ 2) / Real.tan θ) θ :=
    (Real.hasDerivAt_tan hcos).log htan
  have hderiv : deriv zetaOf θ = (1 / Real.cos θ ^ 2) / Real.tan θ := by
    show deriv (fun θ : ℝ => Real.log (Real.tan θ)) θ = _
    exact hd.deriv
  rw [hderiv, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  field_simp

/-- `zetaOf` is differentiable on the open interval `(0,π/2)`. -/
theorem differentiableAt_zetaOf {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ zetaOf θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have htan : Real.tan θ ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero (ne_of_gt hsin) hcos
  exact ((Real.hasDerivAt_tan hcos).log htan).differentiableAt

/-! ## The two scalar chain rules -/

/-- **The `z`-chain rule.**
`D_z (z,θ ↦ c · V (log z, log tan θ)) = c · ∂₁V ∘ (log, logtan)` on the open quadrant:
`D_z = z ∂_z` and `∂_z` of the pull-back is `∂₁V · (1/z)`. -/
theorem Dz_scalar_pull (c : ℝ) {V : ℝ × ℝ → ℝ} (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    EqOn (Function.uncurry (Work.Spaces.Dz (fun z θ => c * V (sOf z, zetaOf θ))))
      (Function.uncurry (fun z θ => c * partFst V (sOf z, zetaOf θ))) Quad := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ⟩ := hp
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hslice : DifferentiableAt ℝ (fun s : ℝ => V (s, zetaOf θ)) (sOf z) := by
    have hd : DifferentiableAt ℝ V (sOf z, zetaOf θ) := ((hV 1).contDiffAt).differentiableAt_one
    have hp2 : DifferentiableAt ℝ (fun s : ℝ => (s, zetaOf θ)) (sOf z) := by fun_prop
    exact hd.comp (sOf z) hp2
  have hcomp := (hslice.hasDerivAt.const_mul c).comp z (Real.hasDerivAt_log hz0)
  have hd : deriv (fun z' : ℝ => c * V (sOf z', zetaOf θ)) z
      = (c * partFst V (sOf z, zetaOf θ)) * z⁻¹ := hcomp.deriv
  show z * deriv (fun z' : ℝ => c * V (sOf z', zetaOf θ)) z = c * partFst V (sOf z, zetaOf θ)
  rw [hd]
  field_simp

/-- **The `θ`-chain rule.**
`D_θ (z,θ ↦ c · V (log z, log tan θ)) = c · 2 · ∂₂V ∘ (log, logtan)` on the open quadrant:
`D_θ = sin(2θ) ∂_θ` and `sin(2θ) · ∂_θ(log tan θ) = 2`. -/
theorem Dth_scalar_pull (c : ℝ) {V : ℝ × ℝ → ℝ} (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    EqOn (Function.uncurry (Work.Spaces.Dth (fun z θ => c * V (sOf z, zetaOf θ))))
      (Function.uncurry (fun z θ => c * 2 * partSnd V (sOf z, zetaOf θ))) Quad := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ⟩ := hp
  have hslice : DifferentiableAt ℝ (fun t : ℝ => V (sOf z, t)) (zetaOf θ) := by
    have hd : DifferentiableAt ℝ V (sOf z, zetaOf θ) := ((hV 1).contDiffAt).differentiableAt_one
    have hp2 : DifferentiableAt ℝ (fun t : ℝ => (sOf z, t)) (zetaOf θ) := by fun_prop
    exact hd.comp (zetaOf θ) hp2
  have hcomp := (hslice.hasDerivAt.const_mul c).comp θ
    (differentiableAt_zetaOf hθ).hasDerivAt
  have hd : deriv (fun θ' : ℝ => c * V (sOf z, zetaOf θ')) θ
      = (c * partSnd V (sOf z, zetaOf θ)) * deriv zetaOf θ := hcomp.deriv
  have hsin : Real.sin (2 * θ) * deriv zetaOf θ = 2 := deriv_zetaOf_mul_sin hθ
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => c * V (sOf z, zetaOf θ')) θ
      = c * 2 * partSnd V (sOf z, zetaOf θ)
  rw [hd]
  rw [show Real.sin (2 * θ) * ((c * partSnd V (sOf z, zetaOf θ)) * deriv zetaOf θ)
        = (c * partSnd V (sOf z, zetaOf θ)) * (Real.sin (2 * θ) * deriv zetaOf θ) from by
    ring]
  rw [hsin]
  ring

/-! ## Congruence of `D_z`, `D_θ` and their iterates on an open set -/

theorem Dz_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') U) :
    EqOn (Function.uncurry (Work.Spaces.Dz f)) (Function.uncurry (Work.Spaces.Dz f')) U := by
  intro p hp
  have h' := Work.Spaces.pz_congr_of_isOpen hU h hp
  show p.1 * Work.Spaces.pz f p.1 p.2 = p.1 * Work.Spaces.pz f' p.1 p.2
  rw [h']

theorem Dth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') U) :
    EqOn (Function.uncurry (Work.Spaces.Dth f)) (Function.uncurry (Work.Spaces.Dth f')) U := by
  intro p hp
  have h' := Work.Spaces.pth_congr_of_isOpen hU h hp
  show Real.sin (2 * p.2) * Work.Spaces.pth f p.1 p.2
    = Real.sin (2 * p.2) * Work.Spaces.pth f' p.1 p.2
  rw [h']

theorem DzIter_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') U) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j f')) U := by
  induction j with
  | zero => exact h
  | succ j ih => exact Dz_congr_of_isOpen hU ih

theorem DthIter_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') U) (i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i f')) U := by
  induction i with
  | zero => exact h
  | succ i ih => exact Dth_congr_of_isOpen hU ih

/-! ## The two iterations -/

/-- **The `D_z`-iteration.**
`D_z^j (z,θ ↦ c · V (log z, log tan θ)) = c · ∂₁^j V ∘ (log, logtan)` on the open quadrant. -/
theorem ZIter_scalar (c : ℝ) {V : ℝ × ℝ → ℝ} (hV : ∀ n : ℕ, ContDiff ℝ n V) (j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => c * V (sOf z, zetaOf θ))))
      (Function.uncurry (fun z θ => c * Kd V j 0 (sOf z, zetaOf θ))) Quad := by
  induction j with
  | zero =>
    intro p hp
    simp only [Function.uncurry, Work.Spaces.DzIter_zero, Kd_zero_zero]
  | succ j ih =>
    have hstep : EqOn (Function.uncurry (Work.Spaces.Dz
        (Work.Spaces.DzIter j (fun z θ => c * V (sOf z, zetaOf θ)))))
        (Function.uncurry (Work.Spaces.Dz
          (fun z θ => c * Kd V j 0 (sOf z, zetaOf θ)))) Quad :=
      Dz_congr_of_isOpen isOpen_quad ih
    have h2 := Dz_scalar_pull c (Kd_smooth V hV j 0)
    have h3 : EqOn (Function.uncurry (fun z θ => c * partFst (Kd V j 0) (sOf z, zetaOf θ)))
        (Function.uncurry (fun z θ => c * Kd V (j + 1) 0 (sOf z, zetaOf θ))) Quad := by
      intro p hp
      simp only [Function.uncurry, ← Kd_succ_eq V j 0]
    exact hstep.trans (h2.trans h3)

/-- **The `D_θ`-iteration.**
`D_θ^i (z,θ ↦ c · V (log z, log tan θ)) = c · 2^i · ∂₂^i V ∘ (log, logtan)` on the open
quadrant. -/
theorem ThIter_scalar (c : ℝ) {V : ℝ × ℝ → ℝ} (hV : ∀ n : ℕ, ContDiff ℝ n V) (i : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c * V (sOf z, zetaOf θ))))
      (Function.uncurry (fun z θ => c * (2 : ℝ) ^ i * Kd V 0 i (sOf z, zetaOf θ))) Quad := by
  induction i with
  | zero =>
    intro p hp
    simp only [Function.uncurry, Work.Spaces.DthIter_zero, pow_zero, Kd_zero_zero]
    ring
  | succ i ih =>
    have hstep : EqOn (Function.uncurry (Work.Spaces.Dth
        (Work.Spaces.DthIter i (fun z θ => c * V (sOf z, zetaOf θ)))))
        (Function.uncurry (Work.Spaces.Dth
          (fun z θ => c * (2 : ℝ) ^ i * Kd V 0 i (sOf z, zetaOf θ)))) Quad :=
      Dth_congr_of_isOpen isOpen_quad ih
    have h2 := Dth_scalar_pull (c * (2 : ℝ) ^ i) (Kd_smooth V hV 0 i)
    have h3 : EqOn (Function.uncurry (fun z θ =>
          (c * (2 : ℝ) ^ i) * 2 * partSnd (Kd V 0 i) (sOf z, zetaOf θ)))
        (Function.uncurry (fun z θ =>
          c * (2 : ℝ) ^ (i + 1) * Kd V 0 (i + 1) (sOf z, zetaOf θ))) Quad := by
      intro p hp
      simp only [Function.uncurry, ← Kd_zero_succ V i, pow_succ]
      ring
    exact hstep.trans (h2.trans h3)

/-! ## `∂₁^j ∂₂^i` does not depend on the order in which the iterates are grouped -/

/-- `∂₁^j (∂₂^i C) = ∂₁^j ∂₂^i C`, i.e. `Kd (Kd C 0 i) j 0 = Kd C j i`. -/
theorem Kd_Kd_zero (C : ℝ × ℝ → ℝ) (i j : ℕ) : Kd (Kd C 0 i) j 0 = Kd C j i := by
  rw [Kd_eq (Kd C 0 i) j 0, Kd_eq C j i]
  funext p
  simp only [iteratedDeriv_zero]
  apply congrArg (fun g : ℝ → ℝ => iteratedDeriv j g p.1)
  funext s
  have h := congrFun (Kd_eq C 0 i) (s, p.2)
  simpa only [iteratedDeriv_zero] using h

end MixLog

/-! ## The target -/

theorem mixed_logCoords {C : ℝ × ℝ → ℝ} (hC : ∀ n : ℕ, ContDiff ℝ n C)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i
        (fun z θ => C (Work.FTS.StrongEps.sOf z, Work.FTS.StrongEps.zetaOf θ)) z θ
      = (2 : ℝ) ^ i *
        Work.FTS.StrongEps.Kd C j i (Work.FTS.StrongEps.sOf z, Work.FTS.StrongEps.zetaOf θ) := by
  have hp : (z, θ) ∈ Quad := ⟨hz, hθ⟩
  -- `1 *` vs. no scalar: the two trivial `EqOn`s
  have hone : EqOn (Function.uncurry (fun z θ => C (sOf z, zetaOf θ)))
      (Function.uncurry (fun z θ => (1 : ℝ) * C (sOf z, zetaOf θ))) Quad := by
    intro p hp
    simp only [Function.uncurry]
    ring
  have htwo : EqOn (Function.uncurry (fun z θ =>
        (1 : ℝ) * (2 : ℝ) ^ i * Kd C 0 i (sOf z, zetaOf θ)))
      (Function.uncurry (fun z θ => (2 : ℝ) ^ i * Kd C 0 i (sOf z, zetaOf θ))) Quad := by
    intro p hp
    simp only [Function.uncurry]
    ring
  -- the `θ`-part
  have hA : EqOn
      (Function.uncurry (Work.Spaces.DthIter i (fun z θ => C (sOf z, zetaOf θ))))
      (Function.uncurry (fun z θ => (2 : ℝ) ^ i * Kd C 0 i (sOf z, zetaOf θ))) Quad :=
    (MixLog.DthIter_congr_of_isOpen MixLog.isOpen_quad hone i).trans
      ((MixLog.ThIter_scalar 1 hC i).trans htwo)
  -- push the `D_z`-iterations across
  have hB : EqOn
      (Function.uncurry (Work.Spaces.DzIter j
        (Work.Spaces.DthIter i (fun z θ => C (sOf z, zetaOf θ)))))
      (Function.uncurry (Work.Spaces.DzIter j
        (fun z θ => (2 : ℝ) ^ i * Kd C 0 i (sOf z, zetaOf θ)))) Quad :=
    MixLog.DzIter_congr_of_isOpen MixLog.isOpen_quad hA j
  have hD : EqOn
      (Function.uncurry (Work.Spaces.DzIter j
        (fun z θ => (2 : ℝ) ^ i * Kd C 0 i (sOf z, zetaOf θ))))
      (Function.uncurry (fun z θ =>
        (2 : ℝ) ^ i * Kd (Kd C 0 i) j 0 (sOf z, zetaOf θ))) Quad :=
    MixLog.ZIter_scalar ((2 : ℝ) ^ i) (Kd_smooth C hC 0 i) j
  have hfin := (hB.trans hD) hp
  have hK : Kd (Kd C 0 i) j 0 = Kd C j i := MixLog.Kd_Kd_zero C i j
  simpa only [Function.uncurry, Work.Spaces.mixed, hK] using hfin

end Work.FTS.EpsEngine
