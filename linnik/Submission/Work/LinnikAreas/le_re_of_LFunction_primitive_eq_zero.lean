import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

set_option linter.style.haveILetI false

namespace Work.LinnikAreas

/-- The primitive character inducing a non-trivial Dirichlet character is non-trivial. -/
private theorem primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
  exact hχ h2.symm

theorem le_re_of_LFunction_primitive_eq_zero {q : ℕ} [NeZero q]
    (χ₀ χ : DirichletCharacter ℂ q) (ρ₀ : ℂ) (hmin : Work.LinnikContract.IsMin1 χ₀ ρ₀)
    (hχ : χ ≠ 1) [NeZero χ.conductor] {u : ℂ}
    (hu : DirichletCharacter.LFunction χ.primitiveCharacter u = 0) (him : |u.im| ≤ 1) :
    u.re ≤ ρ₀.re := by
  classical
  -- `q ≥ 2`, so `log q > 0`
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqne1 : q ≠ 1 := by
    rintro rfl
    exact hχ (Subsingleton.elim χ (1 : DirichletCharacter ℂ 1))
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  -- `ρ₀` is a non-trivial zero, hence `0 < ρ₀.re`
  have hρ₀pos : 0 < ρ₀.re := by
    haveI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
    have hψ₀ : χ₀.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hmin.1.1
    have hΛ : DirichletCharacter.completedLFunction χ₀.primitiveCharacter ρ₀ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hmin.1.2.1
    exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ₀.primitiveCharacter hψ₀
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₀) hΛ).1
  by_cases hpos : 0 < u.re
  · -- `u` lies in the open right half-plane, hence is a zero of the completed L-function
    have hψ : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one hχ
    have hu1 : u.re < 1 := by
      by_contra hcon
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter (Or.inl hψ)
        (le_of_not_gt hcon)) hu
    -- the vanishing orders of `L(·,χ*)` and `Λ(·,χ*)` agree on the critical strip
    have horder :=
      Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
        χ.primitiveCharacter hψ hpos hu1
    have hL_an : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) z :=
      fun z => (DirichletCharacter.differentiable_LFunction hψ).analyticAt z
    have hL_ne : DirichletCharacter.LFunction χ.primitiveCharacter ≠ 0 := by
      intro h0
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.primitiveCharacter (Or.inl hψ)
        (s := (2 : ℂ)) (by norm_num)) (by simp [h0])
    have hord_ne : analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hL_an u, hu⟩
    have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ ⊤ := by
      intro htop
      exact hL_ne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u hL_an).mp htop)
    have hNat_ne :
        analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
      intro h0
      have hcast := Nat.cast_analyticOrderNatAt (f := DirichletCharacter.LFunction χ.primitiveCharacter)
        (z₀ := u) hfinite
      rw [h0, Nat.cast_zero] at hcast
      exact hord_ne hcast.symm
    -- transport to the multiplicity of `u` as a zero of `χ`
    have hzu : Work.LinnikContract.zeroMult χ u ≠ 0 := by
      have hΛne :
          analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
        rw [← horder]
        exact hNat_ne
      simpa only [Work.LinnikContract.zeroMult] using hΛne
    have hZu : Work.LinnikContract.IsZ χ u := ⟨hχ, hzu, him⟩
    have hle2 := hmin.2 χ u hZu
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at hle2
    have h3 : 1 - ρ₀.re ≤ 1 - u.re := (mul_le_mul_iff_left₀ hlogpos).mp hle2
    linarith
  · -- a zero in the closed left half-plane is certainly to the left of `ρ₀`
    have hle : u.re ≤ 0 := le_of_not_gt hpos
    linarith

end Work.LinnikAreas
