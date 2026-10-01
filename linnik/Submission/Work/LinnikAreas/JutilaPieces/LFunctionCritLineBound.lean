import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow

open DirichletCharacter Complex
open scoped BigOperators

namespace Work.LinnikAreas.JutilaPieces

/-- Absorption of a logarithm by an arbitrarily small power: for every `δ > 0` there is `C > 0`
with `Real.log x + 2 ≤ C * x ^ δ` for every `x ≥ 1`. -/
theorem log_add_two_le_mul_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → Real.log x + 2 ≤ C * x ^ δ := by
  refine ⟨1 / δ + 2, by positivity, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hxpos.le hδ
  have hx1 : (1 : ℝ) ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h2 : (2 : ℝ) ≤ 2 * x ^ δ := by linarith
  have h : x ^ δ / δ + 2 * x ^ δ = (1 / δ + 2) * x ^ δ := by ring
  linarith

/-- **Convexity bound on the imaginary axis for a primitive non-principal character.**
For every `δ > 0` there is `C > 0` such that for every modulus `N ≥ 1` and every primitive
non-principal character `χ` mod `N` and every real `y`,

  `‖L(iy, χ)‖ ≤ C · (N (1 + |y|))^{1/2 + δ}`. -/
theorem prim_LFunction_imag_convex {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ y : ℝ,
        ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
          ≤ C * ((N : ℝ) * (1 + |y|)) ^ ((1 : ℝ) / 2 + δ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := log_add_two_le_mul_rpow hδ
  refine ⟨Real.exp 6 * 2 ^ ((1 : ℝ) / 2 + δ) * C₁, by positivity, ?_⟩
  intro N _inst χ hχ hprim y
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hx1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hxpos : (0 : ℝ) < 1 + |y| := by linarith [abs_nonneg y]
  set U : ℝ := (N : ℝ) * (2 + |y|) with hU
  have hU1 : (1 : ℝ) ≤ U := by rw [hU]; nlinarith [abs_nonneg y]
  have hUpos : 0 < U := lt_of_lt_of_le one_pos hU1
  have hlogU : 0 < Real.log U + 2 := by
    have := Real.log_nonneg hU1; linarith
  set V : ℝ := (N : ℝ) * (1 + |y|) with hV
  have hV1 : (1 : ℝ) ≤ V := by
    rw [hV]; exact one_le_mul_of_one_le_of_one_le hN1 hx1
  have hVpos : 0 < V := lt_of_lt_of_le one_pos hV1
  have hUleV : U ≤ 2 * V := by rw [hU, hV]; nlinarith [abs_nonneg y]
  -- the log-form convexity bound at `σ = 0`
  have hcx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs χ hχ hprim
      (σ := 0) (T := y) (le_refl 0) (by norm_num)
  have harg : ((0 : ℝ) : ℂ) + Complex.I * (y : ℂ) = (y : ℂ) * Complex.I := by
    rw [Complex.ofReal_zero, zero_add, mul_comm]
  rw [harg] at hcx
  have hcxU : Real.log ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖ ≤
      ((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|))
        + Real.log (Real.log U + 2) + 6 := by
    rw [hU]; exact hcx
  -- exponentiate
  have hexp : Real.exp (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|))
        + Real.log (Real.log U + 2) + 6)
      = Real.exp 6 * (U ^ ((1 : ℝ) / 2) * (Real.log U + 2)) := by
    have hX : Real.exp (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|)))
        = U ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hUpos]
      congr 1
      rw [hU, Real.log_mul (by positivity) (by positivity)]
      ring
    have hY : Real.exp (Real.log (Real.log U + 2)) = Real.log U + 2 := Real.exp_log hlogU
    calc Real.exp (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|))
          + Real.log (Real.log U + 2) + 6)
        = Real.exp (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|))
            + Real.log (Real.log U + 2)) * Real.exp 6 := Real.exp_add _ 6
      _ = (Real.exp (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|)))
            * Real.exp (Real.log (Real.log U + 2))) * Real.exp 6 := by
            rw [Real.exp_add (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|)))
              (Real.log (Real.log U + 2))]
      _ = U ^ ((1 : ℝ) / 2) * (Real.log U + 2) * Real.exp 6 := by rw [hX, hY]
      _ = Real.exp 6 * (U ^ ((1 : ℝ) / 2) * (Real.log U + 2)) := by ring
  have hnorm_le : ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
      ≤ Real.exp 6 * (U ^ ((1 : ℝ) / 2) * (Real.log U + 2)) := by
    rcases eq_or_lt_of_le
      (norm_nonneg (DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I))) with h | h
    · rw [← h]
      exact (mul_pos (Real.exp_pos 6) (mul_pos (Real.rpow_pos_of_pos hUpos _) hlogU)).le
    · calc ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
          = Real.exp (Real.log ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖) :=
            (Real.exp_log h).symm
        _ ≤ Real.exp (((1 - 0) / 2) * (Real.log (N : ℝ) + Real.log (2 + |y|))
              + Real.log (Real.log U + 2) + 6) := Real.exp_le_exp.mpr hcxU
        _ = Real.exp 6 * (U ^ ((1 : ℝ) / 2) * (Real.log U + 2)) := hexp
  -- bound `U ^ (1/2)` and `log U + 2`
  have hsqrt_le : U ^ ((1 : ℝ) / 2) ≤ 2 ^ ((1 : ℝ) / 2) * V ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow hUpos.le hUleV (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hVpos.le] at h
  have hpowδ : U ^ δ ≤ 2 ^ δ * V ^ δ := by
    have h := Real.rpow_le_rpow hUpos.le hUleV hδ.le
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hVpos.le] at h
  have hlog_le : Real.log U + 2 ≤ C₁ * 2 ^ δ * V ^ δ := by
    calc Real.log U + 2 ≤ C₁ * U ^ δ := hC₁ U hU1
      _ ≤ C₁ * (2 ^ δ * V ^ δ) := mul_le_mul_of_nonneg_left hpowδ hC₁pos.le
      _ = C₁ * 2 ^ δ * V ^ δ := by ring
  calc ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
      ≤ Real.exp 6 * (U ^ ((1 : ℝ) / 2) * (Real.log U + 2)) := hnorm_le
    _ ≤ Real.exp 6 * ((2 ^ ((1 : ℝ) / 2) * V ^ ((1 : ℝ) / 2)) * (C₁ * 2 ^ δ * V ^ δ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 6).le
        exact mul_le_mul hsqrt_le hlog_le hlogU.le (by positivity)
    _ = (Real.exp 6 * 2 ^ ((1 : ℝ) / 2 + δ) * C₁) * V ^ ((1 : ℝ) / 2 + δ) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) ((1 : ℝ) / 2) δ,
          Real.rpow_add hVpos ((1 : ℝ) / 2) δ]
        ring

/-- **Imprimitive reduction on the imaginary axis.** For a non-principal character `χ` mod `q`,
`‖L(iy, χ)‖ ≤ 2^{ω(q)} · ‖L(iy, χ*)‖` where `χ* = χ.primitiveCharacter`: the local Euler factors
`1 - χ*(p) p^{-iy}` have modulus at most `1 + 1 = 2` because `‖p^{-iy}‖ = 1`. -/
theorem lfunction_at_zero_le_primitive (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) (y : ℝ) :
    ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
      ≤ (2 : ℝ) ^ q.primeFactors.card
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((y : ℂ) * Complex.I)‖ := by
  have hne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hcl := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level χ.primitiveCharacter (s := (y : ℂ) * Complex.I) (Or.inl hne)
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hcl
  have hprod : ‖∏ p ∈ q.primeFactors,
        ((1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor)
          * (p : ℂ) ^ (-((y : ℂ) * Complex.I)))‖
      ≤ (2 : ℝ) ^ q.primeFactors.card := by
    rw [norm_prod]
    have hconst : (∏ _p ∈ q.primeFactors, (2 : ℝ)) = (2 : ℝ) ^ q.primeFactors.card :=
      Finset.prod_const (s := q.primeFactors) (2 : ℝ)
    rw [← hconst]
    refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p hp => ?_)
    have hp2 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have hnorm : ‖(p : ℂ) ^ (-((y : ℂ) * Complex.I))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp2]
      have hre : (-((y : ℂ) * Complex.I)).re = 0 := by simp
      rw [hre, Real.rpow_zero]
    have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 :=
      DirichletCharacter.norm_le_one _ _
    have h1nn : (0 : ℝ) ≤ ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ := norm_nonneg _
    calc ‖(1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor)
            * (p : ℂ) ^ (-((y : ℂ) * Complex.I))‖
        ≤ ‖(1 : ℂ)‖ + ‖χ.primitiveCharacter (p : ZMod χ.conductor)
            * (p : ℂ) ^ (-((y : ℂ) * Complex.I))‖ := norm_sub_le _ _
      _ = 1 + ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖
            * ‖(p : ℂ) ^ (-((y : ℂ) * Complex.I))‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + 1 * 1 := by rw [hnorm]; linarith
      _ = 2 := by norm_num
  calc ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
      = ‖DirichletCharacter.LFunction χ.primitiveCharacter ((y : ℂ) * Complex.I)‖
        * ‖∏ p ∈ q.primeFactors, ((1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor)
            * (p : ℂ) ^ (-((y : ℂ) * Complex.I)))‖ := by
        rw [hcl, norm_mul]
    _ ≤ ‖DirichletCharacter.LFunction χ.primitiveCharacter ((y : ℂ) * Complex.I)‖
          * (2 : ℝ) ^ q.primeFactors.card := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (2 : ℝ) ^ q.primeFactors.card
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((y : ℂ) * Complex.I)‖ := by ring

/-- **The convexity bound for `L(s,χ)` on the imaginary axis, uniform in the conductor.**

For every `ε > 0` there is `C > 0` such that for every `q ≥ 1`, every non-principal Dirichlet
character `χ` mod `q` (primitive **or not**) and every real `y`,

  `‖L(iy,χ)‖ ≤ C·(q(1+|y|))^(1/2+ε)`.

Route (all inputs are already proved in this workspace, in `Submission/Commons`):
* for a primitive character use the log-form convexity bound
  `Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs`
  (`log‖L(σ+iT,ψ)‖ ≤ ((1-σ)/2)(log N + log(2+|T|)) + log(log(N(2+|T|))+2) + 6` for `0 ≤ σ ≤ 1`
  and `ψ` primitive non-trivial — this is the sharp Phragmén–Lindelöf bound with an *absolute*
  constant; `LFunction_strip_convexity_explicit` is the same but with a constant that may depend on
  the character) at `σ = 0`;
* reduce an imprimitive `χ` to its primitive character via `DirichletCharacter.LFunction_changeLevel`
  (as `Work.LinnikAreas.JutilaPieces.LFunctionStripPoly` already does), bounding the local factors
  `Π_{p ∣ q, p ∤ cond} (1 - χ_prim(p)p^{-s})` at `Re s = 0` by `2^(ω(q)) ≤ C_ε q^{ε}`;
* absorb the logarithm `log(q(2+|y|)) + 2 ≤ C_ε (q(1+|y|))^{ε}` and collect the powers.

This is Jutila (1977), §2 preliminary estimate `L(iu,χ) ≪ (q(1+|u|))^{1/2+ε}`, and it is exactly what
makes the right-hand side of the zero detector's Mellin representation `≪ 1`. -/
theorem LFunctionCritLineBound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ y : ℝ,
      ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
        ≤ C * ((q : ℝ) * (1 + |y|)) ^ ((1 : ℝ) / 2 + ε) := by
  intro ε hε
  set δ : ℝ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ := prim_LFunction_imag_convex hδ
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow δ hδ
  refine ⟨C₁ * C₂, mul_pos hC₁pos hC₂pos, ?_⟩
  intro q _inst χ hχ y
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hbasepos : 0 < (q : ℝ) * (1 + |y|) := by
    exact lt_of_lt_of_le one_pos (one_le_mul_of_one_le_of_one_le hq1 hx1)
  have hψne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hcondle : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_neZero q) χ.conductor_dvd_level
  have htwo : (2 : ℝ) ^ q.primeFactors.card ≤ C₂ * ((q : ℝ) * (1 + |y|)) ^ δ := by
    refine (hC₂ q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hqnn (by nlinarith [abs_nonneg y]) hδ.le) hC₂pos.le
  have hprim : ‖DirichletCharacter.LFunction χ.primitiveCharacter ((y : ℂ) * Complex.I)‖
      ≤ C₁ * ((q : ℝ) * (1 + |y|)) ^ ((1 : ℝ) / 2 + δ) := by
    refine (hC₁ χ.conductor χ.primitiveCharacter hψne hψprim y).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC₁pos.le
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    nlinarith [abs_nonneg y, hcondle]
  have hexp : δ + ((1 : ℝ) / 2 + δ) = (1 : ℝ) / 2 + ε := by rw [hδdef]; ring
  calc ‖DirichletCharacter.LFunction χ ((y : ℂ) * Complex.I)‖
      ≤ (2 : ℝ) ^ q.primeFactors.card
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((y : ℂ) * Complex.I)‖ :=
        lfunction_at_zero_le_primitive q χ hχ y
    _ ≤ (C₂ * ((q : ℝ) * (1 + |y|)) ^ δ)
          * (C₁ * ((q : ℝ) * (1 + |y|)) ^ ((1 : ℝ) / 2 + δ)) :=
        mul_le_mul htwo hprim (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * (((q : ℝ) * (1 + |y|)) ^ δ
          * ((q : ℝ) * (1 + |y|)) ^ ((1 : ℝ) / 2 + δ)) := by ring
    _ = C₁ * C₂ * ((q : ℝ) * (1 + |y|)) ^ ((1 : ℝ) / 2 + ε) := by
        rw [← Real.rpow_add hbasepos, hexp]

end Work.LinnikAreas.JutilaPieces
