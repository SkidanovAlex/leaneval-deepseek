import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow
import Submission.Work.LinnikAreas.JutilaPieces.LFunctionCritLineBound

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.ZeroDensity.LogFree

/-! ## Support lemmas for the strip bound

The pieces of the proof of `Work.ZeroDensity.LogFree.LFunction_strip_bound`:

* `norm_LFunction_le_exp_six_mul` exponentiates the Phragmén–Lindelöf (convexity) bound
  `Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs` for a primitive
  non-principal character;
* `norm_LFunction_le_prod_mul_primitive` reduces an imprimitive `L`-function to its primitive part
  (Mathlib's `DirichletCharacter.LFunction_changeLevel`), with no lower bound on `σ`;
* `prod_primeFactors_le_two_pow_omega` bounds the resulting local Euler product by `2 ^ ω(q)`;
* `log_absorb_mul_rpow` is the pure real-arithmetic absorption step. -/

/-- **Exponentiated convexity bound in the strip, primitive case.**  For a primitive non-principal
character `χ` mod `N` and `0 ≤ σ ≤ 1`, exponentiating
`Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs` gives

  `‖L(σ + it, χ)‖ ≤ exp 6 · (N(2+|t|))^((1-σ)/2) · (log (N(2+|t|)) + 2)`. -/
private lemma norm_LFunction_le_exp_six_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
          * (Real.log ((N : ℝ) * (2 + |t|)) + 2)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hx1 : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hxpos : (0 : ℝ) < 2 + |t| := by linarith [abs_nonneg t]
  have hU1 : (1 : ℝ) ≤ (N : ℝ) * (2 + |t|) := one_le_mul_of_one_le_of_one_le hN1 hx1
  have hUpos : (0 : ℝ) < (N : ℝ) * (2 + |t|) := lt_of_lt_of_le one_pos hU1
  have hlogU : (0 : ℝ) < Real.log ((N : ℝ) * (2 + |t|)) + 2 := by
    have := Real.log_nonneg hU1; linarith
  have hEpos : (0 : ℝ) < ((N : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
      * (Real.log ((N : ℝ) * (2 + |t|)) + 2) :=
    mul_pos (Real.rpow_pos_of_pos hUpos _) hlogU
  have hlogE : Real.log (((N : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
        * (Real.log ((N : ℝ) * (2 + |t|)) + 2))
      = ((1 - σ) / 2) * (Real.log (N : ℝ) + Real.log (2 + |t|))
        + Real.log (Real.log ((N : ℝ) * (2 + |t|)) + 2) := by
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hUpos _)) (ne_of_gt hlogU),
      Real.log_rpow hUpos]
    rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hxpos)]
  have hcx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
    χ hχ hprim (σ := σ) (T := t) hσ0 hσ1
  have hnorm_eq : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    rw [mul_comm]
  have hcx' : Real.log ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ((1 - σ) / 2) * (Real.log (N : ℝ) + Real.log (2 + |t|))
        + Real.log (Real.log ((N : ℝ) * (2 + |t|)) + 2) + 6 := by
    rw [hnorm_eq]; exact hcx
  have hmain : Real.log ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.log (Real.exp 6 * (((N : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
          * (Real.log ((N : ℝ) * (2 + |t|)) + 2))) := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 6)) (ne_of_gt hEpos), Real.log_exp, hlogE]
    linarith
  rcases eq_or_lt_of_le
    (norm_nonneg (DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I))) with h0 | hpos
  · rw [← h0]
    exact le_of_lt (mul_pos (Real.exp_pos 6) hEpos)
  · have h := (Real.log_le_iff_le_exp hpos).mp hmain
    rwa [Real.exp_log (mul_pos (Real.exp_pos 6) hEpos)] at h

/-- **Imprimitive reduction with no lower bound on `σ`.**  A non-principal character `χ` mod `q`
is the `changeLevel` of its primitive character `χ* = χ.primitiveCharacter` (of conductor
`d = χ.conductor` dividing `q`), and Mathlib's `DirichletCharacter.LFunction_changeLevel` gives
`L(s,χ) = L(s,χ*) · ∏_{p ∣ q} (1 - χ*(p) p^{-s})`.  Taking norms and using `‖χ*(p)‖ ≤ 1` and
`‖p^{-s}‖ = p^{-σ}` bounds the product of local factors by `∏_{p ∣ q}(1 + p^{-σ})`.

This is the proof of `Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le` *without*
the hypothesis `1/2 ≤ σ`; none of the steps uses that hypothesis. -/
private lemma norm_LFunction_le_prod_mul_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) (σ t : ℝ) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ)))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hcl := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level χ.primitiveCharacter (s := s)
      (Or.inl (Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ))
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hcl
  have hprod : ‖∏ p ∈ q.primeFactors,
        ((1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))‖
      ≤ ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ)) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      rw [Nat.mem_primeFactors] at hp
      calc ‖(1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)‖
          ≤ ‖(1 : ℂ)‖ + ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)‖ :=
            norm_sub_le _ _
        _ ≤ 1 + (p : ℝ) ^ (-σ) := by
            have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)‖
                ≤ (p : ℝ) ^ (-σ) := by
              rw [norm_mul]
              have hbase : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
              rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.1.pos)]
              have hre : (-s).re = -σ := by simp [hsdef]
              rw [hre]
              exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
                (DirichletCharacter.norm_le_one _ _)
            rw [show ‖(1 : ℂ)‖ = 1 by norm_num]; linarith
  calc ‖DirichletCharacter.LFunction χ s‖
      = ‖DirichletCharacter.LFunction χ.primitiveCharacter s
          * ∏ p ∈ q.primeFactors,
              ((1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))‖ := by
          rw [hcl]
    _ = ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖
          * ‖∏ p ∈ q.primeFactors,
              ((1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))‖ :=
          norm_mul _ _
    _ ≤ ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖
          * (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ))) :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ)))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖ := by ring

/-- **The local product at exponent `σ ≥ 0`.**  For every `q` and every real `σ ≥ 0`, the product
of the local Euler factors `1 + p^{-σ}` over the primes dividing `q` is at most `2 ^ ω(q)`: indeed
`p^{-σ} ≤ p^0 = 1` for `p ≥ 1`, so each factor is at most `2`. -/
private lemma prod_primeFactors_le_two_pow_omega (q : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ))) ≤ (2 : ℝ) ^ q.primeFactors.card := by
  have hconst : (∏ _p ∈ q.primeFactors, (2 : ℝ)) = (2 : ℝ) ^ q.primeFactors.card :=
    Finset.prod_const (s := q.primeFactors) (2 : ℝ)
  rw [← hconst]
  refine Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => ?_)
  rw [Nat.mem_primeFactors] at hp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.one_le
  have hle : (p : ℝ) ^ (-σ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  linarith

/-- **Absorption of the logarithm.**  If `log x + 2 ≤ C₁ x^γ` for all `x ≥ 1` (which holds with
some `C₁` for every `γ > 0`), then for `d ≤ q`, `d ≥ 1`, `q ≥ 1`, `0 ≤ σ ≤ 1` and every real `t`,

  `(d(2+|t|))^((1-σ)/2) · (log (d(2+|t|)) + 2) ≤ C₁ · (q(2+|t|))^(1/2+γ)`. -/
private lemma log_absorb_mul_rpow {γ C₁ : ℝ} (hγ : 0 ≤ γ) (hC₁pos : 0 < C₁)
    (hC₁ : ∀ x : ℝ, 1 ≤ x → Real.log x + 2 ≤ C₁ * x ^ γ)
    {d q : ℕ} {σ t : ℝ} (hd : (d : ℝ) ≤ (q : ℝ)) (hd1 : (1 : ℝ) ≤ (d : ℝ))
    (hq1 : (1 : ℝ) ≤ (q : ℝ)) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ((d : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2) * (Real.log ((d : ℝ) * (2 + |t|)) + 2)
      ≤ C₁ * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ) := by
  have hx1 : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hxpos : (0 : ℝ) < 2 + |t| := by linarith [abs_nonneg t]
  have hD1 : (1 : ℝ) ≤ (d : ℝ) * (2 + |t|) := one_le_mul_of_one_le_of_one_le hd1 hx1
  have hDpos : (0 : ℝ) < (d : ℝ) * (2 + |t|) := lt_of_lt_of_le one_pos hD1
  have hB1 : (1 : ℝ) ≤ (q : ℝ) * (2 + |t|) := one_le_mul_of_one_le_of_one_le hq1 hx1
  have hBpos : (0 : ℝ) < (q : ℝ) * (2 + |t|) := lt_of_lt_of_le one_pos hB1
  have hBnn : (0 : ℝ) ≤ (q : ℝ) * (2 + |t|) := hBpos.le
  have hDle : (d : ℝ) * (2 + |t|) ≤ (q : ℝ) * (2 + |t|) :=
    mul_le_mul_of_nonneg_right hd (by linarith [abs_nonneg t])
  have hlog : Real.log ((d : ℝ) * (2 + |t|)) + 2 ≤ C₁ * ((q : ℝ) * (2 + |t|)) ^ γ :=
    (hC₁ _ hD1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hDpos.le hDle hγ) hC₁pos.le)
  have hpowle : ((d : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2)
      ≤ ((q : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2) :=
    Real.rpow_le_rpow hDpos.le hDle (by linarith)
  have hBeq : ((q : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2) * ((q : ℝ) * (2 + |t|)) ^ γ
      ≤ ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ) := by
    rw [← Real.rpow_add hBpos]
    apply Real.rpow_le_rpow_of_exponent_le hB1
    linarith
  calc ((d : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2) * (Real.log ((d : ℝ) * (2 + |t|)) + 2)
      ≤ ((q : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2) * (C₁ * ((q : ℝ) * (2 + |t|)) ^ γ) :=
        mul_le_mul hpowle hlog (by have := Real.log_nonneg hD1; linarith)
          (Real.rpow_nonneg hBnn _)
    _ = C₁ * (((q : ℝ) * (2 + |t|)) ^ ((1 - σ) / 2) * ((q : ℝ) * (2 + |t|)) ^ γ) := by ring
    _ ≤ C₁ * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ) :=
        mul_le_mul_of_nonneg_left hBeq hC₁pos.le

/-- **Convexity (Phragmén–Lindelöf) bound in the whole critical strip for a non-principal
character, imprimitive included.** For every `η > 0` there is `C > 0` such that for every
`q ≥ 2`, every non-principal `χ mod q`, every `σ ∈ [0,1]` and every real `t`,
`‖L(σ+it, χ)‖ ≤ C·(q(2+|t|))^{1/2+η}`. This extends
`Work.LinnikAreas.JutilaPieces.LFunctionCritLineBound` (the case `σ = 0`) to the whole strip, and
is the horizontal-edge input of the contour shift.

Route: for the primitive character use
`Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs` (valid for `0 ≤ σ ≤ 1`),
which gives `log ‖L(σ+iT,χ*)‖ ≤ ((1-σ)/2)(log d + log(2+|T|)) + log(log(d(2+|T|))+2) + 6` with
`d = χ.conductor`; exponentiate and absorb the logarithm into `(q(2+|t|))^{η/2}`. For an
imprimitive `χ` reduce to `χ.primitiveCharacter` via `DirichletCharacter.LFunction_changeLevel`
(as in `Work.LinnikAreas.JutilaPieces.lfunction_at_zero_le_primitive`), bounding the local factors
`∏_{p ∣ q}(1 + p^{-σ})` by `∏(1 + p^{-max σ 0}) ≤ 2^{ω(q)}` and then
`2 ^ q.primeFactors.card ≤ C_ε q^ε` (`Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow`).
Finally `d ≤ q` and `log(d(2+|T|)) + 2 ≤ C_ε (q(2+|t|))^{η/2}` combine the powers. -/
theorem LFunction_strip_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
      ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + η) := by
  set γ : ℝ := η / 2 with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.LinnikAreas.JutilaPieces.log_add_two_le_mul_rpow hγ
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow γ hγ
  refine ⟨Real.exp 6 * C₁ * C₂, mul_pos (mul_pos (Real.exp_pos 6) hC₁pos) hC₂pos, ?_⟩
  intro q _inst χ hq2 hχ σ t hσ0 hσ1
  have hq1nat : 1 ≤ q := by omega
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1nat
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hxnn : (0 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hB1 : (1 : ℝ) ≤ (q : ℝ) * (2 + |t|) := one_le_mul_of_one_le_of_one_le hq1 hx1
  have hBpos : (0 : ℝ) < (q : ℝ) * (2 + |t|) := lt_of_lt_of_le one_pos hB1
  have hqleB : (q : ℝ) ≤ (q : ℝ) * (2 + |t|) := by
    have := mul_le_mul_of_nonneg_left hx1 hqnn
    simpa using this
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 :=
    Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
  have hdle : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) χ.conductor_dvd_level
  have hd1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
    have h : (1 : ℕ) ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr (NeZero.ne χ.conductor)
    exact_mod_cast h
  -- the primitive character, convexity estimate
  have hpb := norm_LFunction_le_exp_six_mul (σ := σ) (t := t) χ.primitiveCharacter hprimne hprim hσ0 hσ1
  have hlogabs := log_absorb_mul_rpow (γ := γ) (C₁ := C₁) (d := χ.conductor) (q := q)
    (σ := σ) (t := t) hγ.le hC₁pos hC₁ hdle hd1 hq1 hσ0 hσ1
  have hprim_bound : ‖DirichletCharacter.LFunction χ.primitiveCharacter
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp 6 * (C₁ * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ)) := by
    refine hpb.trans ?_
    exact mul_le_mul_of_nonneg_left hlogabs (Real.exp_pos 6).le
  -- the imprimitive reduction and the local product
  have hred := norm_LFunction_le_prod_mul_primitive χ hχ σ t
  have hprod := prod_primeFactors_le_two_pow_omega q hσ0
  have homega : (2 : ℝ) ^ q.primeFactors.card
      ≤ C₂ * ((q : ℝ) * (2 + |t|)) ^ γ := by
    refine (hC₂ q hq1nat).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂pos.le
    exact Real.rpow_le_rpow hqnn hqleB hγ.le
  calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ)))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hred
    _ ≤ (2 : ℝ) ^ q.primeFactors.card
          * (Real.exp 6 * (C₁ * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ))) :=
        mul_le_mul hprod hprim_bound (norm_nonneg _) (by positivity)
    _ ≤ (C₂ * ((q : ℝ) * (2 + |t|)) ^ γ)
          * (Real.exp 6 * (C₁ * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ))) :=
        mul_le_mul_of_nonneg_right homega
          (mul_nonneg (Real.exp_pos 6).le (mul_nonneg hC₁pos.le (Real.rpow_nonneg hBpos.le _)))
    _ = (Real.exp 6 * C₁ * C₂)
          * (((q : ℝ) * (2 + |t|)) ^ γ * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + γ)) := by ring
    _ = (Real.exp 6 * C₁ * C₂) * ((q : ℝ) * (2 + |t|)) ^ ((1 : ℝ) / 2 + η) := by
        rw [← Real.rpow_add hBpos,
          show γ + ((1 : ℝ) / 2 + γ) = (1 : ℝ) / 2 + η by rw [hγdef]; ring]

end Work.ZeroDensity.LogFree
