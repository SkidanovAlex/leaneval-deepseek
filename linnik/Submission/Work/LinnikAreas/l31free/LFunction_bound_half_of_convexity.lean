import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Work.LinnikAreas.l31free.absorb_log_factor
import Submission.Work.LinnikAreas.l31free.crude_absorb_half

set_option autoImplicit false

namespace Work.LinnikAreas.l31free

/-! ## Convexity bound in the strip `1 - 1/k ≤ σ ≤ 1`

`Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs` gives, for a primitive
non-trivial `χ` at level `N` and `0 ≤ σ ≤ 1`,
`log ‖L(σ+iT,χ)‖ ≤ ((1-σ)/2)(log N + log(2+|T|)) + log(log(N(2+|T|)) + 2) + 6`.
Exponentiating produces the factor `N^((1-σ)/2)·(2+|T|)^((1-σ)/2)·(log(N(2+|T|)) + 2)`.
Since `σ ≥ 1 - 1/k` the exponent `(1-σ)/2 ≤ 1/6`, so `(2+|T|)^((1-σ)/2) ≤ (2+|T|)^(1/6)`, and
the remaining factor `(2+|T|)^d·(log(N(2+|T|)) + 2)` with `d ≤ 1/6` is absorbed by
`C N^η (1+|T|)` (this is the delegated lemma `absorb_log_factor`).  Finally
`N^((1-σ)/2) ≤ N^((1/2)(1-σ)(1+1/k))` since `σ ≤ 1` and `1 ≤ 1 + 1/k`. -/

/-- **Convexity bound for primitive `χ`, multiplicative form.**  Given the absorption estimate
`hCa` (whose proof is `absorb_log_factor`), the Phragmén–Lindelöf bound of
`LFunction_strip_convexity_abs` yields
`‖L(σ+it,χ)‖ ≤ C·N^((1/2)(1-σ)(1+1/k) + η)·(1+|t|)` on `1 - 1/k ≤ σ ≤ 1`. -/
lemma convexity_primitive_bound (k : ℕ) (hk : 3 ≤ k) {η : ℝ}
    (Ca : ℝ) (hCapos : 0 < Ca)
    (hCa : ∀ (N : ℕ) (T d : ℝ), 1 ≤ N → 0 ≤ d → d ≤ 1/6 →
      (2 + |T|)^d * (Real.log ((N:ℝ)*(2+|T|)) + 2) ≤ Ca * (N:ℝ)^η * (1+|T|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 →
      ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤
        C * (N:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + η) * (1+|t|) := by
  have hkR : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h1k : (1:ℝ)/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) hkR
  refine ⟨Real.exp 6 * Ca, by positivity, ?_⟩
  intro N _inst χ hprim hχ σ t hσk hσ1
  have hσ0 : (0:ℝ) ≤ σ := by linarith
  have hd0 : 0 ≤ (1-σ)/2 := by linarith
  have hd16 : (1-σ)/2 ≤ 1/6 := by linarith
  have hN1nat : (1:ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1nat
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
  have ht2pos : (0:ℝ) < 2 + |t| := by positivity
  have hcvx := Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs
    χ hχ hprim (σ := σ) (T := t) hσ0 hσ1
  have hnorm : ‖DirichletCharacter.LFunction χ ((σ:ℂ) + Complex.I * (t:ℂ))‖
      = ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖ := by rw [mul_comm]
  rw [hnorm] at hcvx
  set E : ℝ := (N:ℝ)^((1-σ)/2) * (2+|t|)^((1-σ)/2) * (Real.log ((N:ℝ)*(2+|t|)) + 2) with hEdef
  have harg1 : (1:ℝ) ≤ (N:ℝ)*(2+|t|) := by
    have h2 : (1:ℝ) ≤ 2 + |t| := by have := abs_nonneg t; linarith
    nlinarith [hN1, h2]
  have hlog2 : 0 < Real.log ((N:ℝ)*(2+|t|)) + 2 := by
    have := Real.log_nonneg harg1; linarith
  have hEpos : 0 < E := by rw [hEdef]; positivity
  have hlogE : Real.log E = (1-σ)/2 * (Real.log (N:ℝ) + Real.log (2+|t|))
      + Real.log (Real.log ((N:ℝ)*(2+|t|)) + 2) := by
    rw [hEdef]
    rw [Real.log_mul (x := (N:ℝ)^((1-σ)/2) * (2+|t|)^((1-σ)/2))
        (y := Real.log ((N:ℝ)*(2+|t|)) + 2) (ne_of_gt (by positivity)) (ne_of_gt hlog2)]
    rw [Real.log_mul (x := (N:ℝ)^((1-σ)/2)) (y := (2+|t|)^((1-σ)/2))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
    rw [Real.log_rpow hNpos, Real.log_rpow ht2pos]
    ring
  have hLle : ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤ Real.exp 6 * E := by
    rcases eq_or_lt_of_le
      (norm_nonneg (DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I))) with h0 | hpos
    · rw [← h0]; positivity
    · have h1 : Real.log ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
          ≤ Real.log (Real.exp 6 * E) := by
        rw [Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < Real.exp 6)) (ne_of_gt hEpos),
          Real.log_exp, hlogE]
        linarith [hcvx]
      have h2 := (Real.log_le_iff_le_exp hpos).mp h1
      rwa [Real.exp_log (by positivity : (0:ℝ) < Real.exp 6 * E)] at h2
  calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
      ≤ Real.exp 6 * E := hLle
    _ = Real.exp 6 * ((N:ℝ)^((1-σ)/2)
          * ((2+|t|)^((1-σ)/2) * (Real.log ((N:ℝ)*(2+|t|)) + 2))) := by
        rw [hEdef]; ring
    _ ≤ Real.exp 6 * ((N:ℝ)^((1-σ)/2) * (Ca * (N:ℝ)^η * (1+|t|))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left (hCa N t ((1-σ)/2) hN1nat hd0 hd16)
        positivity
    _ = (Real.exp 6 * Ca) * ((N:ℝ)^((1-σ)/2) * (N:ℝ)^η) * (1+|t|) := by ring
    _ = (Real.exp 6 * Ca) * (N:ℝ)^((1-σ)/2 + η) * (1+|t|) := by rw [Real.rpow_add hNpos]
    _ ≤ (Real.exp 6 * Ca) * (N:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + η) * (1+|t|) := by
        have h01 : (1:ℝ) ≤ 1 + 1/(k:ℝ) := by
          have : (0:ℝ) < 1/(k:ℝ) := by positivity
          linarith
        have hstep : (1-σ)/2 + η ≤ ((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + η := by
          have hσle : 0 ≤ 1 - σ := by linarith
          have hmul : (1-σ) ≤ (1-σ)*(1+1/(k:ℝ)) := le_mul_of_one_le_right hσle h01
          have hdiv : (1-σ)/2 ≤ (1-σ)*(1+1/(k:ℝ))/2 :=
            div_le_div_of_nonneg_right hmul (by norm_num)
          linarith
        have h1' : (Real.exp 6 * Ca) * (N:ℝ)^((1-σ)/2 + η) ≤
            (Real.exp 6 * Ca) * (N:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hstep) (by positivity)
        exact mul_le_mul_of_nonneg_right h1' (by positivity)

/-! ## Assembly

For `σ ≤ 1` reduce `χ` to its primitive character `χ*` (`LFunction_nonprimitive_le`), apply the
convexity bound at level `χ.conductor ≤ N` (absorbing the prime-factor product into `N^{ε/2}`),
and for `σ ≥ 1` use `LFunction_crude_bound` together with `crude_absorb_half`. -/

/-- **Assembly of the `φ = 1/2` bound from the two absorption estimates.** -/
lemma half_bound_of_absorb {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k)
    (Ca : ℝ) (hCapos : 0 < Ca)
    (hCa : ∀ (N : ℕ) (T d : ℝ), 1 ≤ N → 0 ≤ d → d ≤ 1/6 →
      (2 + |T|)^d * (Real.log ((N:ℝ)*(2+|T|)) + 2) ≤ Ca * (N:ℝ)^(ε/2) * (1+|T|))
    (Cf : ℝ) (hCfpos : 0 < Cf)
    (hCf : ∀ (N : ℕ), 1 ≤ N → ∀ σ : ℝ, 1 ≤ σ →
      σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
      (1 + Real.log (N:ℝ)) ≤ Cf * (N:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
          ≤ C * (N:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
  have hε2 : (0:ℝ) < ε/2 := by linarith
  obtain ⟨C1, hC1pos, hC1⟩ := convexity_primitive_bound k hk (η := ε/2) Ca hCapos hCa
  obtain ⟨Cc, hCcpos, hCc⟩ := Commons.NumberTheory.DirichletCharacter.LFunction_crude_bound
  obtain ⟨Cpd, hCpdpos, hCpd⟩ :=
    Commons.NumberTheory.DirichletCharacter.prod_primeFactors_one_add_rpow_le'
      (σ := (1:ℝ)/2) (by norm_num) hε2
  refine ⟨max (C1 * Cpd) (Cc * Cf) + 1, by positivity, ?_⟩
  intro N _inst χ hχ σ t hσk hσle
  have hkR : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have h1k : (1:ℝ)/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) hkR
  have hσ12 : (1:ℝ)/2 ≤ σ := by linarith
  have hN1nat : (1:ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1nat
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
  set A : ℝ := ((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) with hAdef
  by_cases hσ1 : σ ≤ 1
  · haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim : χ.primitiveCharacter.IsPrimitive :=
      DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hprimne : χ.primitiveCharacter ≠ 1 :=
      Commons.NumberTheory.DirichletCharacter.primitiveCharacter_ne_one χ hχ
    have hpb := hC1 χ.primitiveCharacter hprim hprimne σ t hσk hσ1
    have hred := Commons.NumberTheory.DirichletCharacter.LFunction_nonprimitive_le
      χ hχ (σ := σ) hσ12 (t := t)
    have hprod_le : (∏ p ∈ N.primeFactors, (1 + (p:ℝ)^(-σ))) ≤ Cpd * (N:ℝ)^(ε/2) := by
      refine (Finset.prod_le_prod₀ (fun p hp => by positivity) ?_).trans (hCpd N (NeZero.ne N))
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1/2:ℝ) by linarith)
      linarith
    have hexp0 : 0 ≤ ((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε/2 := by
      have h1 : (0:ℝ) ≤ 1-σ := by linarith
      have h2 : (0:ℝ) < 1 + 1/(k:ℝ) := by positivity
      nlinarith [h1, h2, hε2]
    have hcond_le : (χ.conductor:ℝ) ≤ (N:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level
    have hqstar : (χ.conductor:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε/2)
        ≤ (N:ℝ)^(((1:ℝ)/2)*(1-σ)*(1+1/(k:ℝ)) + ε/2) :=
      Real.rpow_le_rpow (by positivity) hcond_le hexp0
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ (∏ p ∈ N.primeFactors, (1 + (p:ℝ)^(-σ)))
            * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((σ:ℂ) + (t:ℂ)*Complex.I)‖ :=
          hred
      _ ≤ (Cpd * (N:ℝ)^(ε/2)) * (C1 * (χ.conductor:ℝ)^(A + ε/2) * (1+|t|)) := by
          apply mul_le_mul hprod_le hpb (norm_nonneg _) (by positivity)
      _ = (C1 * Cpd) * ((χ.conductor:ℝ)^(A + ε/2) * (N:ℝ)^(ε/2)) * (1+|t|) := by ring
      _ ≤ (C1 * Cpd) * ((N:ℝ)^(A + ε/2) * (N:ℝ)^(ε/2)) * (1+|t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hqstar (Real.rpow_nonneg (by positivity) (ε/2))
      _ = (C1 * Cpd) * (N:ℝ)^(A + ε) * (1+|t|) := by
          rw [← Real.rpow_add hNpos, show A + ε/2 + ε/2 = A + ε by ring]
      _ ≤ (max (C1 * Cpd) (Cc * Cf) + 1) * (N:ℝ)^(A + ε) * (1+|t|) := by
          have hle : C1 * Cpd ≤ max (C1 * Cpd) (Cc * Cf) + 1 :=
            le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
          have h1 : (C1 * Cpd) * (N:ℝ)^(A + ε)
              ≤ (max (C1 * Cpd) (Cc * Cf) + 1) * (N:ℝ)^(A + ε) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by positivity) _)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hσ1)
    have hcb := hCc N χ hχ σ t hσge
    have hca := hCf N hN1nat σ hσge hσle
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ Cc * (1 + Real.log (N:ℝ)) * (1 + |t|) := hcb
      _ ≤ Cc * (Cf * (N:ℝ)^(A + ε)) * (1+|t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hca (le_of_lt hCcpos)
      _ = (Cc * Cf) * (N:ℝ)^(A + ε) * (1+|t|) := by ring
      _ ≤ (max (C1 * Cpd) (Cc * Cf) + 1) * (N:ℝ)^(A + ε) * (1+|t|) := by
          have hle : Cc * Cf ≤ max (C1 * Cpd) (Cc * Cf) + 1 :=
            le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
          have h1 : (Cc * Cf) * (N:ℝ)^(A + ε)
              ≤ (max (C1 * Cpd) (Cc * Cf) + 1) * (N:ℝ)^(A + ε) :=
            mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by positivity) _)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **HB Lemma 2.5 with exponent `φ = 1/2`, from convexity** (no Burgess input).  File to create:
`Submission/Work/LinnikAreas/l31free/LFunction_bound_half_of_convexity.lean`, namespace
`Work.LinnikAreas.l31free` (module `Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity`).

This is the `φ = 1/2` case of the "L-function bound near `σ = 1`" hypothesis consumed by
`Work.LinnikAreas.l31free.lemma3_1_free_gen` (the `hbound` slot of HB Lemma 3.1).  With `φ = 1/2`
the bound follows from the *convexity* (Phragmén–Lindelöf) bound for `L(·,χ)`, so it needs no
character-sum input.  Only clash-free modules may be imported: in particular
`Submission.Commons.NumberTheory.DirichletCharacter.LFunction_strip_convexity_abs` gives, for
primitive non-trivial `χ` and `0 ≤ σ ≤ 1`,
`log ‖L(σ+iT,χ)‖ ≤ ((1-σ)/2)·(log N + log(2+|T|)) + log(log(N·(2+|T|)) + 2) + 6`,
whose `N`-exponent `(1-σ)/2` is `≤ (1/2)(1-σ)(1+1/k) + ε` (since `(1-σ) ≥ 0` and `k > 0`), while
the factors `(2+|T|)^{(1-σ)/2} ≤ 1+|T|` and `log(log(N(2+|T|))+2) ≤ C_ε N^ε (1+|T|)` are absorbed
into the constant.  Do **not** import
`Submission.Commons.NumberTheory.DirichletCharacter.completedL_diskZeroCount_explicit`,
`…siegel_walfisz_chi`, `…exists_LFunction_disc_zeroCount`,
`…logDeriv_horizontal_split` or `…finite_zeroHeights_window` (duplicate-declaration clash).

For `σ ≥ 1` use the Euler product / `LFunction_crude_bound` with the exponent adapted from `1/3` to
`1/2` (as in `crude_absorb` of `LFunction_bound_third_of_burgess`, whose argument only needs
`1 - σ + loglog N/log N ≥ 0`), and for non-primitive `χ` the reduction
`‖L(s,χ)‖ ≤ (∏_{p|N}(1+p^{-σ}))·‖L(s,χ*)‖` with the prime-factor product absorbed into `N^ε`; both
ingredients are in the clash-free
`Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess`. -/
theorem LFunction_bound_half_of_convexity {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
          ≤ C * (N:ℝ) ^ (((1:ℝ)/2) * (1 - σ) * (1 + 1/(k:ℝ)) + ε) * (1 + |t|) := by
  obtain ⟨Ca, hCapos, hCa⟩ := absorb_log_factor (η := ε/2) (by linarith)
  obtain ⟨Cf, hCfpos, hCf⟩ := crude_absorb_half hk hε
  exact half_bound_of_absorb hε k hk Ca hCapos hCa Cf hCfpos hCf

end Work.LinnikAreas.l31free
