/-
# `omegaStar_eq_Aom`: the model field is the amplitude `Aom` times `e_θ`

`Work.ConstructionInstance.omegaStar β x = Γ(θ x) · F_*(ρ(x)^{3β}) • e_θ(x)` is the model field
of `Defs.lean` (`Γ(θ) = (sin θ cos²θ)^β`, `F_*(z) = 2z/(1+z)²`).  This file identifies its scalar
amplitude with the explicit `Aom β x = cSign β (x₂) · A0 β x` of `AuxOmegaStar.lean`, i.e.

  `Γ(θ x) · F_*(ρ(x)^{3β}) = Aom β x`,

so that `omegaStar β x = Aom β x • e_θ(x)`.  The point of the statement is the *bookkeeping of
`Real.rpow` at a negative base*: on the half space `x₂ < 0` the angular base
`sin θ cos²θ = x₂ r²/ρ³` is negative, and `Real.rpow` there equals `|·|^β` times the constant
`cos (βπ)` (`Real.rpow_def_of_neg`, `Real.log_neg_eq_log`) — exactly the factor `cSign β (x₂)`
that `Aom` carries.  The remaining content is the polar dictionary
`sin θ = x₂/ρ`, `cos θ = r/ρ` (`Work.Cyl.sin_thetaP`, `Work.Cyl.cos_thetaP`) and the
`Real.rpow` algebra of `(x₂ r²/ρ³)^β`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.AuxOmegaStar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## `Real.rpow` algebra -/

/-- `(r³)^β = r^{3β}` for `r ≥ 0` (the cube analogue of `AuxOmegaStar.rpow_sq_mul`). -/
lemma rpow_cube_mul (β r : ℝ) (hr : 0 ≤ r) : ((r ^ 3 : ℝ)) ^ β = r ^ (3 * β) := by
  rcases eq_or_ne β 0 with h | h
  · subst h; simp
  · have h' : (r ^ 3 : ℝ) = r ^ 2 * r := by ring
    rw [h', Real.mul_rpow (by positivity) hr, rpow_sq_mul β r hr,
      ← Real.rpow_add' hr (by intro hc; exact h (by linarith))]
    congr 1
    ring

/-- **`Real.rpow` at the negative base `-a`**: for `0 ≤ a` and `β ≠ 0`,
`(-a)^β = a^β · cos (βπ)`.  This is the `Real.toReal`-free form of `Real.rpow_def_of_neg`
(`x^y = exp (y log x) cos (yπ)`), using `Real.log (-a) = Real.log a`; the case `a = 0` is the
trivial one `0^β = 0`. -/
lemma rpow_neg_base (a β : ℝ) (ha : 0 ≤ a) (hβ : β ≠ 0) :
    (-a) ^ β = a ^ β * Real.cos (β * Real.pi) := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; rw [neg_zero, Real.zero_rpow hβ, zero_mul]
  · rw [Real.rpow_def_of_neg (neg_lt_zero.mpr h), Real.rpow_def_of_pos h, Real.log_neg_eq_log]

/-! ## The amplitude of `Γ(θ)·F_*(ρ^{3β})` -/

/-- **The amplitude on a non-negative base.**  For `0 ≤ t`, `0 ≤ s`, `c > 0`,
`(t s²/c³)^β · F_*(c^{3β}) = 2 t^β s^{2β} / (1 + c^{3β})²`: the numerator collects
`(t s²)^β = t^β s^{2β}` (`Real.mul_rpow`, `rpow_sq_mul`) and the denominator
`c^{3β}` (`rpow_cube_mul`) cancels against the `c^{3β}` of `F_*`. -/
lemma amp_of_nonneg_base (β t s c : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (hc : 0 < c) :
    (t * s ^ 2 / c ^ 3) ^ β * Work.FM.Fstar (c ^ (3 * β))
      = 2 * t ^ β * s ^ (2 * β) / (1 + c ^ (3 * β)) ^ 2 := by
  have hc3 : 0 ≤ s ^ 2 / c ^ 3 := div_nonneg (sq_nonneg s) (by positivity)
  have hsplit : t * s ^ 2 / c ^ 3 = t * (s ^ 2 / c ^ 3) := by ring
  rw [hsplit, Real.mul_rpow ht hc3, Real.div_rpow (sq_nonneg s) (by positivity),
    rpow_sq_mul β s hs, rpow_cube_mul β c hc.le, Work.FM.Fstar]
  field_simp

/-- **The amplitude on a strictly negative base** `-t s²/c³`: `Real.rpow` produces the extra
factor `cos (βπ)`, which is precisely `cSign β` on the region `x₂ < 0`. -/
lemma amp_of_neg_base (β t s c : ℝ) (hβ : β ≠ 0) (ht : 0 ≤ t) (hs : 0 ≤ s) (hc : 0 < c) :
    (-(t * s ^ 2 / c ^ 3)) ^ β * Work.FM.Fstar (c ^ (3 * β))
      = 2 * Real.cos (β * Real.pi) * t ^ β * s ^ (2 * β) / (1 + c ^ (3 * β)) ^ 2 := by
  have hb : 0 ≤ t * s ^ 2 / c ^ 3 := div_nonneg (mul_nonneg ht (sq_nonneg s)) (by positivity)
  rw [rpow_neg_base _ β hb hβ]
  rw [show (t * s ^ 2 / c ^ 3) ^ β * Real.cos (β * Real.pi) * Work.FM.Fstar (c ^ (3 * β))
      = Real.cos (β * Real.pi) * ((t * s ^ 2 / c ^ 3) ^ β * Work.FM.Fstar (c ^ (3 * β)))
      by ring,
    amp_of_nonneg_base β t s c ht hs hc]
  ring

/-! ## The angular base `Γ = (x₂ r²/ρ³)^β` -/

/-- **The angular factor is the `β`-th power of the single quotient `x₂ r²/ρ³`.**

For `r(x) > 0` this is the polar dictionary `sin θ = x₂/ρ`, `cos θ = r/ρ`
(`Work.Cyl.sin_thetaP`, `Work.Cyl.cos_thetaP`, with `ρ = ρP (r) (x₂)`); on the axis `r = 0` both
sides are `0^β` (`θ = arctan 0 = 0` on the axis, so `sin θ cos²θ = 0`, and the quotient is
`x₂·0/ρ³ = 0`). -/
lemma Gamma_eq_rpow_base (β : ℝ) (x : R3) :
    Gamma β (Work.Cyl.theta x)
      = (x 2 * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3) ^ β := by
  rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with hr | hr
  · -- axis: `r = 0`, both sides are `0^β`
    have hr0 : Work.Cyl.radial x = 0 := hr.symm
    have hL : Gamma β (Work.Cyl.theta x) = (0:ℝ) ^ β := by
      have hθ : Work.Cyl.theta x = 0 := by
        rw [Work.Cyl.theta, hr0, div_zero, Real.arctan_zero]
      rw [hθ, Gamma]
      simp
    have hR : (x 2 * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3) ^ β = (0:ℝ) ^ β := by
      rw [hr0]; simp
    rw [hL, hR]
  · -- off the axis: the polar dictionary
    have hρP : Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
      rw [Work.Cyl.rho, Work.Cyl.rhoP, Work.Cyl.radial_sq]
    have hsin : Real.sin (Work.Cyl.theta x) = x 2 / Work.Cyl.rho x := by
      rw [show Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)
            from rfl,
        Work.Cyl.sin_thetaP hr (Work.Cyl.axial x), ← hρP]
      rfl
    have hcos : Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x / Work.Cyl.rho x := by
      rw [show Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x)
            from rfl,
        Work.Cyl.cos_thetaP hr (Work.Cyl.axial x), ← hρP]
    rw [Gamma, hsin, hcos]
    congr 1
    field_simp

/-! ## The scalar amplitude identity -/

/-- **`Γ(θ x) · F_*(ρ(x)^{3β}) = Aom β x`.**  `Aom β x = cSign β (x₂) · A0 β x` with
`A0 β x = 2 |x₂|^β r^{2β}/(1 + ρ^{3β})²`: on `x₂ ≥ 0` the `cSign` is `1` and the base
`x₂ r²/ρ³ ≥ 0`, so `amp_of_nonneg_base` applies; on `x₂ < 0` the base is
`-(|x₂| r²/ρ³)` and `rpow_neg_base`/`amp_of_neg_base` produce the factor `cos (βπ) = cSign β x₂`.
At the origin (`ρ = 0`) both sides vanish. -/
lemma Gamma_mul_Fstar_eq_Aom (β : ℝ) (hβ : 0 < β) (x : R3) :
    Gamma β (Work.Cyl.theta x) * Work.FM.Fstar (Work.Cyl.rho x ^ (3 * β)) = Aom β x := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  rcases eq_or_lt_of_le (Work.Cyl.rho_nonneg x) with hρ0 | hρ
  · -- `ρ = 0` forces `x = 0`, where `Γ = 0` and `A0 = 0`
    have hρ0' : Work.Cyl.rho x = 0 := hρ0.symm
    have hx0 : x = 0 := by
      by_contra hx
      have hp := (Work.Cyl.rho_pos_iff x).mpr hx
      rw [hρ0'] at hp
      exact lt_irrefl 0 hp
    subst hx0
    have hΓ : Gamma β (Work.Cyl.theta (0:R3)) = 0 := by
      have hθ : Work.Cyl.theta (0:R3) = 0 := by
        rw [Work.Cyl.theta, Work.Cyl.axial]
        simp [Work.Cyl.radial, Work.Cyl.radSq]
      rw [hθ, Gamma]
      simp [Real.zero_rpow hβne]
    have hA : A0 β (0:R3) = 0 :=
      A0_eq_zero_of_radial_eq_zero β hβ (by simp [Work.Cyl.radial, Work.Cyl.radSq])
    rw [hΓ, zero_mul, Aom, cSign, hA, mul_zero]
  · rw [Gamma_eq_rpow_base β x]
    rcases lt_or_ge (x 2) 0 with hx2 | hx2
    · -- `x₂ < 0`: the negative base, `cSign = cos (βπ)`
      have hneg : x 2 * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3
          = -(|x 2| * (Work.Cyl.radial x) ^ 2 / (Work.Cyl.rho x) ^ 3) := by
        rw [abs_of_neg hx2]; ring
      rw [hneg, amp_of_neg_base β (|x 2|) (Work.Cyl.radial x) (Work.Cyl.rho x) hβne
          (abs_nonneg _) (Work.Cyl.radial_nonneg x) hρ,
        Aom, cSign, ite_eq_right (not_le.mpr hx2), A0, abs_of_neg hx2]
      ring
    · -- `x₂ ≥ 0`: the base is non-negative, `cSign = 1`
      rw [amp_of_nonneg_base β (x 2) (Work.Cyl.radial x) (Work.Cyl.rho x) hx2
        (Work.Cyl.radial_nonneg x) hρ,
      Aom, cSign, ite_eq_left hx2, A0, abs_of_nonneg hx2]
      ring

/-! ## The theorem -/

theorem omegaStar_eq_Aom (β : ℝ) (hβ : 0 < β) (x : Work.ConstructionInstance.R3) :
    Work.ConstructionInstance.omegaStar β x
      = Work.ConstructionInstance.Aom β x • Work.Cyl.eTheta x := by
  rw [omegaStar_apply, Gamma_mul_Fstar_eq_Aom β hβ x]

end Work.ConstructionInstance
