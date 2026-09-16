import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Submission.Commons.NumberTheory.Linnik.completedL_growth_circle
import Submission.Commons.Analysis.Complex.jensenCarleman

open Complex DirichletCharacter Metric
open scoped Real

noncomputable section

namespace Commons.NumberTheory.Linnik

/-!
# Zero count for the completed Dirichlet L-function in a disk

`completedL_zeroCount`: for a primitive non-trivial character `χ mod N` there is a constant
`c` (depending on `χ` and `N`) such that for every `R ≥ 2` the (signed) sum of the divisor
coefficients of the completed L-function `Λ(χ, ·)` inside the closed ball `|s| ≤ R` is bounded by

`c * R * (log (R + 2) + log N + 2)`.

Since `Λ(χ, ·)` is entire (nontrivial `χ`), all divisor coefficients are nonnegative and the sum
is the number of zeros (with multiplicity) of `Λ(χ, ·)` in the ball.  The proof combines

* Jensen's inequality (`AnalyticOnNhd.sum_divisor_le`, Mathlib), bounding zeros in `|s| ≤ R`
  through the maximum of `‖Λ‖` on the circle `|s| = 2R`, and
* the circle growth bound `completedL_growth_circle` for `‖Λ(χ, s)‖` on `|s| = 2R`.

The value `Λ(χ, 0)` is non-zero (functional equation + `L(χ⁻¹, 1) ≠ 0`), so Jensen's inequality
applies with centre `0`.
-/

/-- The archimedean gamma factor of a character does not vanish at `s = 1`. -/
lemma gammaFactor_one_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    gammaFactor χ 1 ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (s := (1 : ℂ)) (by norm_num)
  · rw [Odd.gammaFactor_def hO]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (s := ((1 : ℂ) + 1)) (by
      rw [Complex.add_re, Complex.one_re]
      norm_num)

/-- The completed L-function of a non-trivial character does not vanish at `s = 1`
(`L(χ,1) ≠ 0`, Dirichlet, and the gamma factor is finite and non-zero there). -/
lemma completedLFunction_one_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : completedLFunction χ 1 ≠ 0 := by
  intro hz
  have hfac : completedLFunction χ 1 = LFunction χ 1 * gammaFactor χ 1 := by
    simpa using (completedLFunction_eq_mul_gammaFactor_re_pos χ (s := (1 : ℂ)) (by norm_num))
  have hL : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero hχ
  exact (mul_ne_zero hL (gammaFactor_one_ne_zero χ)) (by simpa [hfac] using hz)

/-- The completed L-function of a primitive non-trivial character does not vanish at `s = 0`.
This follows from the functional equation `Λ(χ,0) = N^{1/2} ε(χ) Λ(χ⁻¹, 1)` and the
non-vanishing of the latter factor. -/
lemma completedLFunction_zero_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) : completedLFunction χ 0 ≠ 0 := by
  have hnorm := completedLFunction_norm_fe χ hχprim (0 : ℂ)
  have hfac1 : 0 < ‖completedLFunction χ⁻¹ (1 - 0)‖ := by
    simpa using (norm_pos_iff.mpr (completedLFunction_one_ne_zero χ⁻¹ (inv_ne_one_of_ne_one χ hχ)))
  have hpow : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hN : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N) : 0 < N)
    exact Real.rpow_pos_of_pos hN (1 / 2 : ℝ)
  intro hz
  have hnorm0 : ‖completedLFunction χ 0‖ = 0 := by simp [hz]
  have hpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) * ‖completedLFunction χ⁻¹ (1 - 0)‖ := by
    exact mul_pos hpow hfac1
  have hnorm' : ‖completedLFunction χ 0‖ = (N : ℝ) ^ (1 / 2 : ℝ) * ‖completedLFunction χ⁻¹ (1 - 0)‖ := by
    simpa using hnorm
  linarith

/-- `log (2R + 2) ≤ 2 log (R + 2)` for `R ≥ 2`. -/
lemma log_two_mul_add_two_le_two_log_add_two {R : ℝ} (hR : 2 ≤ R) :
    Real.log (2 * R + 2) ≤ 2 * Real.log (R + 2) := by
  have hpos1 : 0 < 2 * R + 2 := by nlinarith
  have hpos2 : 0 < (R + 2) ^ 2 := by positivity
  have hsq : 2 * R + 2 ≤ (R + 2) ^ 2 := by
    nlinarith [sq_nonneg (R + 2)]
  have hlog := Real.log_le_log hpos1 hsq
  rw [Real.log_pow (R + 2) 2] at hlog
  norm_num at hlog
  exact hlog

/-- **Zero count of the completed Dirichlet L-function in a disk.**  For a primitive non-trivial
character `χ mod N` there is a constant `c` such that for every `R ≥ 2` the sum of the divisor
coefficients of `Λ(χ, ·)` on the closed ball `|s| ≤ R` is at most
`c * R * (log (R + 2) + log N + 2)`. -/
theorem completedL_zeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction hχ)
  have hΛan (s : Set ℂ) : AnalyticOnNhd ℂ Λ s := by
    intro z hz
    exact hΛdiff.analyticAt z
  have hΛ0 : Λ 0 ≠ 0 := by simpa [Λ] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  rcases Commons.NumberTheory.Linnik.completedL_growth_circle χ hχ hχprim with ⟨cg0, hg0⟩
  let cg : ℝ := max cg0 0
  have hcg : 0 ≤ cg := by dsimp [cg]; exact le_max_right cg0 0
  have hg : ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ = R →
      ‖Λ s‖ ≤ Real.exp (cg * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) := by
    intro R hR s hs
    have hcg0le : cg0 ≤ cg := by dsimp [cg]; exact le_max_left cg0 0
    have hb := hg0 R hR s hs
    have hR0 : 0 ≤ R := by linarith
    have hT : 0 ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
      have h1 : 0 ≤ Real.log (R + 2) := by
        refine Real.log_nonneg ?_
        linarith
      have h2 : 0 ≤ Real.log (N : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
      linarith
    refine le_trans hb ?_
    exact Real.exp_le_exp.mpr (by
      have hprod : cg0 * R ≤ cg * R := mul_le_mul_of_nonneg_right hcg0le hR0
      exact mul_le_mul_of_nonneg_right hprod hT)
  let A : ℝ := ‖Λ 0‖
  have hApos : 0 < A := by dsimp [A]; exact norm_pos_iff.mpr hΛ0
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
  refine ⟨(4 * cg + |Real.log A|) / Real.log 2, ?_⟩
  intro R hR
  let T : ℝ := Real.log (R + 2) + Real.log (N : ℝ) + 2
  let R₂ : ℝ := 2 * R
  have hR₂ : 2 ≤ R₂ := by dsimp [R₂]; linarith
  have hRpos : 0 < R := by linarith
  have hR₂pos : 0 < R₂ := by dsimp [R₂]; linarith
  have hR₂ne : R₂ ≠ 0 := ne_of_gt hR₂pos
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hT2 : 2 ≤ T := by
    dsimp [T]
    have h1 : 0 ≤ Real.log (R + 2) := by
      refine Real.log_nonneg ?_
      linarith
    linarith
  have hRT1 : (1 : ℝ) ≤ R * T := by nlinarith
  have hRT0 : 0 ≤ R * T := by nlinarith
  let E : ℝ := cg * R₂ * (Real.log (R₂ + 2) + Real.log (N : ℝ) + 2)
  let M : ℝ := Real.exp E
  have hE0 : 0 ≤ E := by
    dsimp [E]
    have h1 : 0 ≤ Real.log (R₂ + 2) := by
      refine Real.log_nonneg ?_
      linarith
    have h3 : 0 ≤ cg * R₂ := mul_nonneg hcg (by dsimp [R₂]; linarith)
    have h4 : 0 ≤ Real.log (R₂ + 2) + Real.log (N : ℝ) + 2 := by linarith
    exact mul_nonneg h3 h4
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact Real.exp_le_exp.mp (by
      have he : Real.exp 0 ≤ Real.exp E := Real.exp_le_exp.mpr hE0
      simpa using he)
  have hMpos : 0 < M := by dsimp [M]; exact Real.exp_pos E
  have hM_log : Real.log M = E := by dsimp [M]; rw [Real.log_exp]
  have hfb : ∀ z ∈ sphere (0 : ℂ) |R₂|, ‖Λ z‖ ≤ M := by
    intro z hz
    have hznorm : ‖z‖ = |R₂| := by
      simpa [dist_eq_norm] using hz
    have hznorm' : ‖z‖ = R₂ := by rw [hznorm, abs_of_nonneg (by linarith : 0 ≤ R₂)]
    have hb := hg R₂ hR₂ z hznorm'
    dsimp [M, E] at hb ⊢
    exact hb
  have hjs := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := R) (R := R₂) (M := M) (f := Λ)
      (r_pos := by rw [abs_of_nonneg (by linarith : 0 ≤ R)]; exact hRpos)
      (r_lt_R := by
        rw [abs_of_nonneg (by linarith : 0 ≤ R), abs_of_nonneg (by linarith : 0 ≤ R₂)]
        dsimp [R₂]; linarith)
      (hM := hM1) (h₁f := hΛan _) (h₂f := hΛ0) (f_bound := hfb)
  have hRHS : Real.log (M / A) / Real.log (R₂ / R) = Real.log (M / A) / Real.log 2 := by
    congr 1
    dsimp [R₂]
    field_simp [hRne]
  have hjs2 : ↑(∑ᶠ u : ℂ, (MeromorphicOn.divisor Λ (closedBall 0 |R|)) u) ≤
      Real.log (M / A) / Real.log 2 := by
    simpa [A] using (hjs.trans_eq hRHS)
  have hDiv (u : ℂ) : (MeromorphicOn.divisor Λ (closedBall 0 R)) u =
      (MeromorphicOn.divisor Λ (closedBall 0 |R|)) u := by
    have hCB : Metric.closedBall (0 : ℂ) R = Metric.closedBall (0 : ℂ) |R| := by
      ext z
      simp [abs_of_nonneg (by linarith : 0 ≤ R)]
    rw [hCB]
  have hfin : Function.HasFiniteSupport (fun u : ℂ => (MeromorphicOn.divisor Λ (closedBall 0 R)) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor Λ (closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R))
  have hsumEq : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall 0 R)) u : ℤ) : ℝ)) =
      ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (closedBall 0 |R|)) u : ℤ)) := by
    calc
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall 0 R)) u : ℤ) : ℝ))
          = ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (closedBall 0 R)) u : ℤ)) := by
              simpa using ((Int.castRingHom ℝ).map_finsum hfin).symm
      _ = ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (closedBall 0 |R|)) u : ℤ)) := by
              congr 1
              apply finsum_congr
              intro u
              exact hDiv u
  have hlogDiv : Real.log (M / A) = Real.log M - Real.log A := by
    exact Real.log_div (ne_of_gt hMpos) (ne_of_gt hApos)
  have hExp_le : E ≤ 4 * cg * R * T := by
    have hS : Real.log (R₂ + 2) + Real.log (N : ℝ) + 2 ≤ 2 * T := by
      have hlogR : Real.log (R₂ + 2) ≤ 2 * Real.log (R + 2) := by
        have h : Real.log (2 * R + 2) ≤ 2 * Real.log (R + 2) :=
          log_two_mul_add_two_le_two_log_add_two hR
        dsimp [R₂] at h ⊢
        simpa [two_mul] using h
      have hlogR2 : 2 * Real.log (R + 2) + Real.log (N : ℝ) + 2 ≤ 2 * T := by
        dsimp [T]
        nlinarith [hlogN0]
      linarith
    have hcgR₂ : 0 ≤ cg * R₂ := mul_nonneg hcg (by dsimp [R₂]; linarith)
    have h1 : E ≤ cg * R₂ * (2 * T) := by
      dsimp [E]
      exact mul_le_mul_of_nonneg_left hS hcgR₂
    calc
      E ≤ cg * R₂ * (2 * T) := h1
      _ = 4 * cg * R * T := by
        dsimp [R₂]
        ring
  have hbnd1 : Real.log (M / A) ≤ 4 * cg * R * T + |Real.log A| := by
    calc
      Real.log (M / A) = Real.log M - Real.log A := hlogDiv
      _ = E - Real.log A := by rw [hM_log]
      _ ≤ 4 * cg * R * T - Real.log A := by
        exact sub_le_sub_right hExp_le (Real.log A)
      _ ≤ 4 * cg * R * T + |Real.log A| := by
        have hneg : -(Real.log A) ≤ |Real.log A| := neg_le_abs (Real.log A)
        linarith
  have hlg2pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hbnd2 : Real.log (M / A) / Real.log 2 ≤ (4 * cg * R * T + |Real.log A|) / Real.log 2 := by
    exact div_le_div_of_nonneg_right hbnd1 (le_of_lt hlg2pos)
  have hAbs : |Real.log A| ≤ |Real.log A| * (R * T) := by
    calc
      |Real.log A| = |Real.log A| * 1 := by ring
      _ ≤ |Real.log A| * (R * T) := by
        exact mul_le_mul_of_nonneg_left hRT1 (abs_nonneg (Real.log A))
  have hnum : 4 * cg * R * T + |Real.log A| ≤ (4 * cg + |Real.log A|) * (R * T) := by
    calc
      4 * cg * R * T + |Real.log A| ≤ 4 * cg * R * T + |Real.log A| * (R * T) := by
        simpa [add_comm] using (add_le_add_right hAbs (4 * cg * R * T))
      _ = (4 * cg + |Real.log A|) * (R * T) := by ring
  have hbnd3 : (4 * cg * R * T + |Real.log A|) / Real.log 2 ≤
      (4 * cg + |Real.log A|) / Real.log 2 * (R * T) := by
    rw [div_le_iff₀ hlg2pos]
    calc
      4 * cg * R * T + |Real.log A| ≤ (4 * cg + |Real.log A|) * (R * T) := hnum
      _ = ((4 * cg + |Real.log A|) / Real.log 2 * (R * T)) * Real.log 2 := by
        field_simp [ne_of_gt hlg2pos]
  calc
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall 0 R)) u : ℤ) : ℝ))
        = ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (closedBall 0 |R|)) u : ℤ)) := hsumEq
    _ ≤ Real.log (M / A) / Real.log 2 := hjs2
    _ ≤ (4 * cg * R * T + |Real.log A|) / Real.log 2 := hbnd2
    _ ≤ (4 * cg + |Real.log A|) / Real.log 2 * (R * T) := hbnd3
    _ = (4 * cg + |Real.log A|) / Real.log 2 * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
      dsimp [T]
      ring

end Commons.NumberTheory.Linnik
