import Mathlib
import Submission.Work.Milnor.ChartDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Facts about `η` for the Milnor exotic sphere construction

`eta u = 1/√(1+‖u‖²)` on `E4 = ℝ⁴`.  We compute its Fréchet derivative at an arbitrary
point, its derivative at the origin, the derivative of `fderiv η` at the origin, and show
that `fderiv η` vanishes only at `0`.

The key point is that `eta` is the function `u ↦ (1 + ‖u‖²)^(-1/2)`, so that its derivative
is `-(1 + ‖u‖²)^(-3/2) • innerSL ℝ u = ceta u • innerSL ℝ u`.
-/

namespace Work.Milnor

noncomputable section

open scoped Topology

/-- `eta` rewritten as a real power. -/
lemma eta_eq_rpow (u : E4) : eta u = (1 + ‖u‖^2) ^ (-(1/2 : ℝ)) := by
  rw [eta, Real.sqrt_eq_rpow]
  exact (Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖u‖^2) (1/2)).symm

/-- The scalar factor `ceta` never vanishes. -/
lemma ceta_ne_zero (u : E4) : ceta u ≠ 0 := by
  have hp : (0:ℝ) < (1 + ‖u‖^2) ^ (-(3/2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  rw [ceta]
  intro h
  linarith

/-- The Fréchet derivative of `eta`. -/
lemma hasFDerivAt_eta (x : E4) : HasFDerivAt eta (ceta x • innerSL ℝ x) x := by
  have ha : (0:ℝ) < 1 + ‖x‖^2 := by positivity
  have hg : HasFDerivAt (fun y : E4 => 1 + ‖y‖^2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1
  have hderiv : HasDerivAt (fun z : ℝ => z ^ (-(1/2:ℝ)))
      ((-(1/2:ℝ)) * (1+‖x‖^2)^((-(1/2:ℝ))-1)) (1+‖x‖^2) :=
    Real.hasDerivAt_rpow_const (Or.inl ha.ne')
  have hp := hderiv.comp_hasFDerivAt x hg
  have hpow : HasFDerivAt (fun y : E4 => (1 + ‖y‖^2) ^ (-(1/2 : ℝ)))
      (ceta x • innerSL ℝ x) x := by
    refine hp.congr_fderiv ?_
    rw [ceta, show (-(1/2:ℝ)) - 1 = -(3/2) by norm_num]
    rw [← Nat.cast_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ x), smul_smul]
    ring_nf
  rw [show eta = (fun y : E4 => (1 + ‖y‖^2) ^ (-(1/2 : ℝ))) from funext eta_eq_rpow]
  exact hpow

/-- `ceta` is (strictly) differentiable, with the indicated derivative. -/
lemma hasFDerivAt_ceta (x : E4) :
    HasFDerivAt ceta
      (-((( -(3/2:ℝ)) * (1 + ‖x‖^2) ^ ((-(3/2:ℝ)) - 1)) • (2 • innerSL ℝ x))) x := by
  have ha : (0:ℝ) < 1 + ‖x‖^2 := by positivity
  have hg : HasFDerivAt (fun y : E4 => 1 + ‖y‖^2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1
  have hderiv : HasDerivAt (fun z : ℝ => z ^ (-(3/2:ℝ)))
      ((-(3/2:ℝ)) * (1+‖x‖^2)^((-(3/2:ℝ))-1)) (1+‖x‖^2) :=
    Real.hasDerivAt_rpow_const (Or.inl ha.ne')
  have hp := (hderiv.comp_hasFDerivAt x hg).neg
  have hc : ceta = (-(fun z : ℝ => z ^ (-(3/2:ℝ)))) ∘ (fun y : E4 => 1 + ‖y‖^2) := by
    funext y; simp [ceta, Function.comp]
  rw [hc]
  exact hp

theorem eta_facts :
    (fderiv ℝ eta 0 = 0) ∧
    (∀ x : E4, fderiv ℝ eta x = ceta x • innerSL ℝ x) ∧
    (fderiv ℝ (fderiv ℝ eta) 0 = - (innerSL ℝ : E4 →L[ℝ] E4 →L[ℝ] ℝ)) ∧
    (∀ x : E4, fderiv ℝ eta x = 0 ↔ x = 0) := by
  have h2 : ∀ x : E4, fderiv ℝ eta x = ceta x • innerSL ℝ x :=
    fun x => (hasFDerivAt_eta x).fderiv
  refine ⟨?_, h2, ?_, ?_⟩
  · rw [h2 0]; simp
  · rw [show fderiv ℝ eta = (fun x : E4 => ceta x • innerSL ℝ x) from funext h2]
    rw [fderiv_fun_smul ((hasFDerivAt_ceta 0).differentiableAt)
      (ContinuousLinearMap.differentiableAt (innerSL ℝ))]
    simp [ceta]
  · intro x
    rw [h2 x, smul_eq_zero_iff_right (ceta_ne_zero x)]
    constructor
    · intro h
      have h' : innerSL ℝ x = innerSL ℝ (0 : E4) := by simpa using h
      exact (innerSL_inj (𝕜 := ℝ) (x := x) (y := (0:E4))).mp h'
    · rintro rfl; simp

end

end Work.Milnor
