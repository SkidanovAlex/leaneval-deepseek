import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

/-!
# `Work.LinnikAreas.sameCharRepelHalf`

Off-line regime of the same-character repulsion (see the docstring of the main theorem).

The Siegel input is the (already proved, in `LinnikAreas/siegelRepelMaximal.lean`) reduction
`siegelLogBound`; because that module drags in unrelated in-progress files, its proof is
reproduced here as the local helper `siegelLogBoundLoc` on top of the two Commons modules it
actually needs.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas

/-- *Siegel's bound in logarithmic form* (local copy of `Work.LinnikAreas.siegelLogBound`):
for a real character `χ₀ = χ̄₀ ≠ 1` of level `q` with a zero `ρ₀` on the real axis,
`log(1/λ(ρ₀)) ≤ ε log q + C` for every `ε > 0`, with `C = C(ε)`. -/
theorem siegelLogBoundLoc (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ [NeZero q] (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
      χ₀ ≠ 1 → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
      Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 →
      Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ eps * Real.log q + C := by
  obtain ⟨Cs, hCspos, hCs⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform eps heps
  refine ⟨max 1 (-Real.log Cs + 1), ?_, ?_⟩
  · rw [lt_max_iff]; left; norm_num
  · intro q _inst χ₀ ρ₀ hχ₀ hreal him hzm
    haveI : NeZero χ₀.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₀⟩
    have hprim : χ₀.primitiveCharacter.IsPrimitive := χ₀.primitiveCharacter_isPrimitive
    have hne : χ₀.primitiveCharacter ≠ 1 := by
      intro h1
      apply hχ₀
      rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ := χ₀), h1,
        DirichletCharacter.changeLevel_one χ₀.conductor_dvd_level]
    have hreal' : χ₀ * χ₀ = 1 := by rw [← pow_two]; exact hreal
    have hsq : χ₀.primitiveCharacter * χ₀.primitiveCharacter = 1 := by
      have hmap : DirichletCharacter.changeLevel χ₀.conductor_dvd_level
          (χ₀.primitiveCharacter * χ₀.primitiveCharacter) =
          DirichletCharacter.changeLevel χ₀.conductor_dvd_level χ₀.primitiveCharacter *
            DirichletCharacter.changeLevel χ₀.conductor_dvd_level χ₀.primitiveCharacter :=
        map_mul _ _ _
      have h1 : DirichletCharacter.changeLevel χ₀.conductor_dvd_level
          (χ₀.primitiveCharacter * χ₀.primitiveCharacter) = 1 := by
        rw [hmap, DirichletCharacter.changeLevel_primitiveCharacter, hreal']
      exact (DirichletCharacter.changeLevel_eq_one_iff χ₀.conductor_dvd_level).mp h1
    have hΛ : DirichletCharacter.completedLFunction χ₀.primitiveCharacter ρ₀ = 0 := by
      unfold Work.LinnikContract.zeroMult at hzm
      exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
    have hstrip :=
      Commons.NumberTheory.Linnik.completedL_zero_strip χ₀.primitiveCharacter hne hprim hΛ
    have hdpos : 0 < 1 - ρ₀.re := by linarith [hstrip.2]
    have hr0 : ρ₀ ≠ 0 := by
      intro h0
      rw [h0] at hstrip
      simp at hstrip
    have hL : DirichletCharacter.LFunction χ₀.primitiveCharacter ρ₀ = 0 := by
      have h0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
        χ₀.primitiveCharacter ρ₀ (Or.inl hr0)
      have hgf : DirichletCharacter.gammaFactor χ₀.primitiveCharacter ρ₀ ≠ 0 := by
        have key : ∀ z : ℂ, 0 < z.re → z.Gammaℝ ≠ 0 := by
          intro z hz h0
          obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
          rw [hn] at hz
          have hre : ((-(2 * (n : ℂ)) : ℂ)).re = -(2 * (n : ℝ)) := by simp
          rw [hre] at hz
          have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
          linarith
        unfold DirichletCharacter.gammaFactor
        split_ifs with h
        · exact key ρ₀ hstrip.1
        · exact key (ρ₀ + 1) (by rw [Complex.add_re, Complex.one_re]; linarith [hstrip.1])
      rw [h0, hΛ, zero_div]
    have him0 : ((ρ₀.re : ℂ)) = ρ₀ := by
      rw [← Complex.re_add_im ρ₀, him]
      simp
    have hL' : DirichletCharacter.LFunction χ₀.primitiveCharacter (ρ₀.re : ℂ) = 0 := by
      rw [him0]; exact hL
    have hSiegel :=
      hCs χ₀.conductor χ₀.primitiveCharacter hprim hne hsq ρ₀.re hstrip.1 hstrip.2 hL'
    have hq2 : 2 ≤ q := by
      rcases Nat.lt_or_ge q 2 with h | h
      · exfalso
        have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        have hq1 : q = 1 := by omega
        exact hχ₀ (DirichletCharacter.level_one' χ₀ hq1)
      · exact h
    have hNpos : 0 < ((χ₀.conductor : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ₀.conductor)
    have hNq : ((χ₀.conductor : ℕ) : ℝ) ≤ (q : ℝ) := by
      have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ₀.conductor_dvd_level
      exact_mod_cast h
    have hdlower : Cs * (q : ℝ) ^ (-eps) ≤ 1 - ρ₀.re := by
      refine le_trans ?_ hSiegel
      have hrp : (q : ℝ) ^ (-eps) ≤ ((χ₀.conductor : ℕ) : ℝ) ^ (-eps) :=
        Real.rpow_le_rpow_of_nonpos hNpos hNq (by linarith)
      exact mul_le_mul_of_nonneg_left hrp hCspos.le
    have hqcastpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hlogqpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    have hlog1 : Real.log (1 / (1 - ρ₀.re)) ≤ eps * Real.log q - Real.log Cs := by
      have hqpow : (0 : ℝ) < (q : ℝ) ^ eps := Real.rpow_pos_of_pos hqcastpos eps
      have h1 : 1 / (1 - ρ₀.re) ≤ (q : ℝ) ^ eps / Cs := by
        rw [div_le_div_iff₀ hdpos hCspos, one_mul]
        have h2 : Cs * (q : ℝ) ^ (-eps) * (q : ℝ) ^ eps ≤ (1 - ρ₀.re) * (q : ℝ) ^ eps :=
          mul_le_mul_of_nonneg_right hdlower hqpow.le
        rw [mul_assoc, ← Real.rpow_add hqcastpos, neg_add_cancel, Real.rpow_zero,
          mul_one] at h2
        nlinarith [h2]
      calc Real.log (1 / (1 - ρ₀.re)) ≤ Real.log ((q : ℝ) ^ eps / Cs) :=
            Real.log_le_log (by positivity) h1
        _ = eps * Real.log q - Real.log Cs := by
            rw [Real.log_div (ne_of_gt hqpow) (ne_of_gt hCspos), Real.log_rpow hqcastpos eps]
    have hloglog : Real.log (1 / Real.log q) ≤ 1 := by
      have h2 : Real.log 2 ≤ Real.log q :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have hlogqhalf : (1 / 2 : ℝ) ≤ Real.log q := le_trans hlog2 h2
      have hpos : 0 < 1 / Real.log q := div_pos one_pos (by linarith)
      have h1 : 1 / Real.log q ≤ 1 / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlogqhalf
      have h3 : Real.log (1 / Real.log q) ≤ Real.log (1 / (1 / 2 : ℝ)) :=
        Real.log_le_log hpos h1
      have h4 : Real.log (1 / (1 / 2 : ℝ)) ≤ 1 := by
        have h5 : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
        rw [h5]
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      linarith
    rw [Work.LinnikContract.lamOf]
    have hsplit : 1 / ((1 - ρ₀.re) * Real.log q) =
        (1 / (1 - ρ₀.re)) * (1 / Real.log q) := by
      simp only [div_eq_mul_inv, mul_inv, one_mul]
    have hpos1 : 0 < 1 / (1 - ρ₀.re) := div_pos one_pos hdpos
    have hpos2 : 0 < 1 / Real.log q := div_pos one_pos hlogqpos
    rw [hsplit, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
    have hCbound : -Real.log Cs + 1 ≤ max 1 (-Real.log Cs + 1) := le_max_right _ _
    linarith [hlog1, hloglog, hCbound]

/-- **Off-line regime of the same-character repulsion.**

A zero `ρ` of `χ₀` with `|Im ρ| ≤ 1` and `Re ρ ≤ 1/2` satisfies the repulsion trivially:
`λ(ρ) = (1 − Re ρ)·log q ≥ (1/2)·log q`, and Siegel's bound
(`Commons.NumberTheory.DirichletCharacter.LFunction_realZero_siegel_uniform`: for every `ε > 0`
there is `C(ε) > 0` with `C(ε)·N^{−ε} ≤ 1 − β` for every real zero `β` of a primitive real
character modulo `N`) applied to the primitive real character inducing `χ₀` gives
`log(1/λ(ρ₀)) ≤ ε·log q + O(1)`; with `ε` fixed (e.g. `ε = 1/8`) this yields
`c·log(1/λ(ρ₀)) ≤ λ(ρ)` for an absolute `c > 0` (e.g. `c = 1/4`).

This case also covers the *trivial* zeros of the completed `L`-function (they have `Re ρ ≤ 0`),
which the frozen statement's quantifier `∀ ρ, zeroMult χ₀ ρ ≠ 0 ∧ |ρ.im| ≤ 1 ∧ ρ ≠ ρ₀` includes.

Reviewer notes: the Siegel step in this exact shape already exists, sorry-free, as
`SiegalLogBound` in `Submission/Work/LinnikAreas/siegelRepelMaximal.lean` (giving
`log(1/lamOf q ρ₀) ≤ ε log q + C` from `χ₀ ≠ 1`, `χ₀² = 1`, `ρ₀.im = 0`, `zeroMult χ₀ ρ₀ ≠ 0`);
that file does NOT import this one, so it may be imported here (do not import
`Submission.Work.LinnikAreas.dhRepelSameChar`).  Remaining plumbing: `0 < ρ₀.re < 1` and the
ordinary `L`-zero of the primitive character (`Work.A7.isZ_LFunction_zero` /
`Work.LinnikAreas.DhRepel.LFunction_primitive_eq_zero`), the reality
`χ₀² = 1 ⟹ χ₀.primitiveCharacter * χ₀.primitiveCharacter = 1`, and
`(χ₀.conductor : ℝ) ≤ q`. -/
theorem sameCharRepelHalf : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ ρ : ℂ, Work.LinnikContract.zeroMult χ₀ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ → ρ.re ≤ 1 / 2 →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q ρ := by
  -- Siegel's bound with the fixed exponent `ε = 1/8`.
  obtain ⟨C, hCpos, hsig⟩ := siegelLogBoundLoc (1 / 8) (by norm_num)
  refine ⟨1 / 4, by norm_num, max 2 (Nat.ceil (Real.exp (8 * C / 15)) + 1), ?_⟩
  intro q hq inst χ₀ ρ₀ hmin hreal him _hsmall ρ _hzm _himρ _hne hre
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hqe : Nat.ceil (Real.exp (8 * C / 15)) + 1 ≤ q := le_trans (le_max_right _ _) hq
  -- `log q` is large enough that the Siegel loss `C` is absorbed.
  have hlogq_ge : 8 * C / 15 ≤ Real.log q := by
    have h1 : Real.exp (8 * C / 15) ≤ ((Nat.ceil (Real.exp (8 * C / 15)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (8 * C / 15)) : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans (Nat.le_succ _) hqe)
    calc 8 * C / 15 = Real.log (Real.exp (8 * C / 15)) := (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) (le_trans h1 h2)
  have hlogqpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  -- the Siegel bound for the exceptional zero `ρ₀`
  have hlog : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ (1 / 8) * Real.log q + C :=
    hsig q χ₀ ρ₀ hmin.1.1 hreal him hmin.1.2.1
  have hstep1 : (1 / 4 : ℝ) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤
      (1 / 4) * ((1 / 8) * Real.log q + C) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hstep2 : (1 / 4 : ℝ) * ((1 / 8) * Real.log q + C) ≤ (1 / 2) * Real.log q := by
    nlinarith [hlogq_ge]
  -- the off-line regime bound: `λ(ρ) ≥ (1/2) log q`
  have hstep3 : (1 / 2 : ℝ) * Real.log q ≤ Work.LinnikContract.lamOf q ρ := by
    rw [Work.LinnikContract.lamOf]
    nlinarith [hlogqpos, hre]
  linarith [hstep1, hstep2, hstep3]

end Work.LinnikAreas
