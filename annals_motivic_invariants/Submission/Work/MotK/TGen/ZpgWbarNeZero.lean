import Mathlib
import Submission.Work.MotK.TGen.ZpgPsiDefs
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

theorem ZpgWbarNeZero (K : Type) [Field K] (a b h : K) [IsDomain (Work.MotK.TGen.ZP K a b h)] (hb : b ≠ 0) : Work.MotK.TGen.zpgW a b h ∉ Ideal.span ({Work.MotK.TGen.zpgE a b h} : Set (MvPolynomial (Fin 2) K)) := by
  rw [Ideal.mem_span_singleton]
  intro hdvd
  -- The `K`-algebra endomorphism `X₁ ↦ 0`.
  set ψ : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then MvPolynomial.X (0 : Fin 2) else 0) with hψ
  have hE : ψ (Work.MotK.TGen.zpgE a b h)
      = MvPolynomial.C (a ^ 3 * b ^ 6 * h ^ 2) * (MvPolynomial.X (0 : Fin 2)) ^ 5
        + MvPolynomial.C (a ^ 3 * b ^ 6) := by
    simp [hψ, Work.MotK.TGen.zpgE]
  have hW : ψ (Work.MotK.TGen.zpgW a b h)
      = MvPolynomial.C (b ^ 4) * MvPolynomial.X (0 : Fin 2) := by
    simp [hψ, Work.MotK.TGen.zpgW]
  have hWne : ψ (Work.MotK.TGen.zpgW a b h) ≠ 0 := by
    rw [hW]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (pow_ne_zero 4 hb))
      (MvPolynomial.X_ne_zero (0 : Fin 2))
  obtain ⟨q, hq⟩ := hdvd
  have hdvd' : ψ (Work.MotK.TGen.zpgE a b h) ∣ ψ (Work.MotK.TGen.zpgW a b h) :=
    ⟨ψ q, by rw [hq, map_mul]⟩
  have hEne : ψ (Work.MotK.TGen.zpgE a b h) ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := hdvd'
    exact hWne (by rw [ht, h0, zero_mul])
  have hWdeg : (ψ (Work.MotK.TGen.zpgW a b h)).totalDegree ≤ 1 := by
    rw [hW]
    calc (MvPolynomial.C (b ^ 4) * MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree
        ≤ (MvPolynomial.C (b ^ 4) : MvPolynomial (Fin 2) K).totalDegree
            + (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = 1 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hdeg_le : (ψ (Work.MotK.TGen.zpgE a b h)).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd' hWne).trans hWdeg
  -- the `X₀⁵`-coefficient of `ψ zpgE` is `a³b⁶h²`
  have hcoeff : (ψ (Work.MotK.TGen.zpgE a b h)).coeff (Finsupp.single (0 : Fin 2) 5)
      = a ^ 3 * b ^ 6 * h ^ 2 := by
    rw [hE]
    have h5 : ¬ ((0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 5) := by
      rw [eq_comm]
      exact Finsupp.single_ne_zero.mpr (by norm_num)
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
      MvPolynomial.coeff_C, ite_true, h5, ite_false, mul_one, add_zero]
  have hzero : (ψ (Work.MotK.TGen.zpgE a b h)).coeff (Finsupp.single (0 : Fin 2) 5) = 0 := by
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    have hsum : (∑ i ∈ (Finsupp.single (0 : Fin 2) 5).support,
        (Finsupp.single (0 : Fin 2) 5) i) = 5 := by simp
    rw [hsum]
    omega
  have hab : a ^ 3 * b ^ 6 * h ^ 2 = 0 := by rw [← hcoeff, hzero]
  rcases mul_eq_zero.mp hab with hab' | hab'
  · -- `a³b⁶ = 0`, so `a = 0` (as `b ≠ 0`); then `ψ zpgE = 0`, contradiction.
    rcases mul_eq_zero.mp hab' with ha3 | hb6z
    · have ha0 : a = 0 := (pow_eq_zero_iff (n := 3) (by norm_num)).mp ha3
      exact hEne (by rw [hE]; simp [ha0])
    · exact absurd hb6z (pow_ne_zero 6 hb)
  · -- `h = 0`, so `zpgE = C(a³b⁶)` is a unit; then `ZP` is the trivial ring.
    have hh0 : h = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hab'
    have ha : a ≠ 0 := by
      intro ha0
      exact hEne (by rw [hE]; simp [ha0])
    have hzpgE : Work.MotK.TGen.zpgE a b h = MvPolynomial.C (a ^ 3 * b ^ 6) := by
      rw [Work.MotK.TGen.zpgE]; simp [hh0]
    have hunit : IsUnit (Work.MotK.TGen.zpgE a b h) := by
      rw [hzpgE]
      exact IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K)
        (isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 6 hb)))
    have hnt : Nontrivial (Work.MotK.TGen.ZP K a b h) := inferInstance
    haveI : Subsingleton (Work.MotK.TGen.ZP K a b h) :=
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hunit)
    obtain ⟨x, y, hxy⟩ := hnt
    exact hxy (Subsingleton.elim x y)

end Work.MotK.TGen
