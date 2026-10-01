import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip

/-!
# `Work.LinnikAreas.TuranOther.multL_ne_zero`

A zero of the Linnik-contract `L`-function of a non-principal character `χ` (i.e. a point `u` with
`zeroMult χ u ≠ 0`, meaning that the *completed* `L`-function of the primitive character inducing
`χ` vanishes to positive order at `u`) is a zero of the ordinary, possibly imprimitive,
Dirichlet `L`-function `L(s,χ)` **to positive order** — that is, `multL χ u ≠ 0`.

The argument:
* `u` is a zero of `Λ(s, χ*)`, `χ* = χ.primitiveCharacter`, hence (the primitive character
  inducing a non-principal character is non-principal, and `Λ` of a primitive non-principal
  character only vanishes in the strip) `0 < Re u < 1`;
* on the strip the vanishing orders of `Λ(·,χ*)` and `L(·,χ*)` agree, so
  `analyticOrderNatAt (LFunction χ*) u ≠ 0`;
* `LFunction_changeLevel` writes `L(s,χ) = L(s,χ*) · ∏_{p ∣ q} (1 - χ*(p) p^{-s})` for all `s`
  (here `χ* ≠ 1`, so no exception at `s = 1`), and the finite correction factor is analytic and
  non-zero at `u` because `Re u > 0`; orders are additive under multiplication, so the vanishing
  order of `L(s,χ)` is the same as that of `L(s,χ*)`, in particular non-zero.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option linter.style.haveILetI false

noncomputable section

namespace Work.LinnikAreas.TuranOther

theorem multL_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {u : ℂ} (hu : 0 < u.re)
    (h : Work.LinnikContract.zeroMult χ u ≠ 0) :
    Work.LinnikAreas.TuranOther.multL χ u ≠ 0 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- `u` is a zero of the completed `L`-function of the primitive character inducing `χ`
  have hmult :
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using h
  have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hmult
  -- the primitive character inducing a non-principal character is non-principal
  have hχc : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    have h' : DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ :=
      DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [h1, DirichletCharacter.changeLevel_one] at h'
    exact h'.symm
  have hprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  obtain ⟨hre0, hre1⟩ :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hχc hprim hcomp
  -- vanishing order of the primitive `L`-function at `u` is non-zero
  have hA : analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u ≠ 0 := by
    rw [Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip
      χ.primitiveCharacter hχc hre0 hre1]
    exact hmult
  -- the level-correction factor relating `L(s,χ)` to `L(s,χ*)`
  let Q : ℂ → ℂ := fun s => ∏ p ∈ q.primeFactors,
    (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))
  have hQdef : Q = fun s => ∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) := rfl
  have hfun : DirichletCharacter.LFunction χ =
      DirichletCharacter.LFunction χ.primitiveCharacter * Q := by
    funext s
    have hcl := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level χ.primitiveCharacter (s := s) (Or.inl hχc)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hcl
    rw [Pi.mul_apply, hQdef]
    exact hcl
  have hQdiff : Differentiable ℂ Q := by
    intro x
    rw [hQdef]
    refine DifferentiableAt.fun_finsetProd ?_
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (p : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      exact_mod_cast (ne_of_gt hpos)
    refine DifferentiableAt.sub (differentiableAt_const (1 : ℂ)) ?_
    refine DifferentiableAt.mul
      (differentiableAt_const (χ.primitiveCharacter (p : ZMod χ.conductor))) ?_
    exact (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  have hQan : AnalyticAt ℂ Q u := hQdiff.analyticAt u
  have hQne : Q u ≠ 0 := by
    rw [hQdef]
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hnorm :
        ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)‖ < 1 := by
      have h1 : ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-u.re) := by
        simpa using Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-u)
      calc ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u)‖
          ≤ ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-u)‖ :=
            norm_mul_le _ _
        _ ≤ 1 * (p : ℝ) ^ (-u.re) := by
              rw [h1]
              exact mul_le_mul_of_nonneg_right
                (DirichletCharacter.norm_le_one χ.primitiveCharacter _) (by positivity)
        _ < 1 := by
              rw [one_mul, Real.rpow_neg hp0.le]
              exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1 hu)
    intro hzero
    have hz : χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-u) = 1 :=
      (sub_eq_zero.mp hzero).symm
    rw [hz, norm_one] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  have hLfun_an : AnalyticAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) u :=
    (DirichletCharacter.differentiable_LFunction hχc).analyticAt u
  have horder_eq : analyticOrderAt (DirichletCharacter.LFunction χ) u =
      analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) u := by
    rw [hfun, analyticOrderAt_mul hLfun_an hQan,
      (hQan.analyticOrderAt_eq_zero).mpr hQne, add_zero]
  have hnat : analyticOrderNatAt (DirichletCharacter.LFunction χ) u =
      analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) u :=
    congrArg ENat.toNat horder_eq
  show analyticOrderNatAt (DirichletCharacter.LFunction χ) u ≠ 0
  rw [hnat]
  exact hA

end Work.LinnikAreas.TuranOther

end
