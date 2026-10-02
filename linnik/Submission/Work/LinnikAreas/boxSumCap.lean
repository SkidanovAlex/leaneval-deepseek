import Mathlib
import Submission.Work.LinnikAreas.area6Box
import Submission.Work.LinnikAreas.RepulsionCapDefs

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
open Work.LinnikContract
open Siegel

/-- `Work.LinnikAreas.boxSumBound_of_inputs` (`Submission/Work/LinnikAreas/area6.lean`)
with the same proof.  The repulsion hypothesis `hRep : Work.LinnikAreas.Siegel.RepulsionInput`
(which exhibits its own constant `cr`) becomes `hrep : Work.LinnikAreas.RepulsionWithCap ε₀ c`
(constant `c` given): `obtain ⟨cr, hcrpos, qR, hRep'⟩ := hRep` becomes
`obtain ⟨qR, hRep'⟩ := hrep` with `cr := c` and `hc : 0 < c`.  The internal threshold (the
existential `lamS ≤ 1/100` of `Work.LinnikAreas.Siegel.BoxSumBound`) must additionally satisfy
`lamS ≤ ε₀`: append `ε₀` to the nested `min` defining `lamS` (using `hε₀` for positivity), and use
`hlamE0 : lam ≤ ε₀` for the `λ₁ ≤ ε₀` hypothesis of `RepulsionWithCap`, while `hlam2 : lam ≤ 1/2`
is still used for `hHigh'` and `hlam1 : lam ≤ 1/100` for `hSimple'`.  Everything else
--- `Work.LinnikAreas.Siegel.signedBoxSumAll_le_exceptional`,
`Work.LinnikAreas.Siegel.farZeroSum_le_restLow_add_restHigh`, `Siegel.Hk_norm_le_exp_lamOf`,
`Work.LinnikAreas.Siegel.siegel_close_arith` and the arithmetic --- is used verbatim. -/
theorem boxSumCap {ε₀ c : ℝ} (R : ℝ) (hR : 1 ≤ R) (hε₀ : 0 < ε₀) (hc : 0 < c)
    (hSimple : Work.LinnikAreas.Siegel.SimpleInput)
    (hrep : Work.LinnikAreas.RepulsionWithCap ε₀ c)
    (hsum : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), Summable (fun ρ : ℂ =>
      (Work.LinnikContract.zeroMult χ ρ : ℝ) *
        ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - ρ) * (Real.log q : ℂ))‖))
    (hLow : ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ ε₀ →
        Work.LinnikAreas.Siegel.restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * (Work.LinnikContract.lamOf q (β₁ : ℂ)) ^ (1 + δ))
    (hHigh : ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 2 →
        Work.LinnikAreas.Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * Work.LinnikContract.lamOf q (β₁ : ℂ) * (Real.log q) ^ e) :
    Work.LinnikAreas.Siegel.BoxSumBound R := by
  obtain ⟨C₁, hC₁pos, δ, hδpos, qL, hLow'⟩ := hLow
  obtain ⟨C₂, hC₂pos, e, heneg, qH, hHigh'⟩ := hHigh
  obtain ⟨qR, hRep'⟩ := hrep
  obtain ⟨qS, hSimple'⟩ := hSimple
  have ha₀ : (0 : ℝ) < 49 / 10 := by norm_num
  have hK : (0 : ℝ) < 3 / 10 := by norm_num
  have hK2 : (0 : ℝ) < (3 / 10 : ℝ) ^ 2 := by norm_num
  set e' : ℝ := -e with he'def
  have he'pos : 0 < e' := by rw [he'def]; linarith only [heneg]
  set L₀ : ℝ := (8 * C₂ / ((3 / 10 : ℝ) ^ 2 * (49 / 10))) ^ (1 / e') with hL₀def
  have hL₀pos : 0 < L₀ := by rw [hL₀def]; exact Real.rpow_pos_of_pos (by positivity) _
  have hL₀pow : L₀ ^ e = (3 / 10 : ℝ) ^ 2 * (49 / 10) / (8 * C₂) := by
    rw [hL₀def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 8 * C₂ / ((3/10)^2 * (49/10)))]
    have hene : e ≠ 0 := ne_of_lt heneg
    have h1 : (1 / e') * e = -1 := by
      rw [he'def]
      field_simp
    rw [h1, Real.rpow_neg_one, inv_div]
  -- thresholds
  set qR' : ℕ := ⌈Real.exp R⌉₊ + 1 with hqR'def
  set qH' : ℕ := ⌈Real.exp L₀⌉₊ + 1 with hqH'def
  set lamS : ℝ := min (min (min (1 / 100) (min (1 / 2) (2 / (5 * (49 / 10))))) ε₀)
    (min (((3 / 10 : ℝ) ^ 2 * (49 / 10) / (8 * C₁)) ^ (1 / δ))
      (Real.exp (-(R + 1) / c))) with hlamSdef
  have hlamSpos : 0 < lamS := by
    rw [hlamSdef]
    exact lt_min (lt_min (lt_min (by norm_num) (lt_min (by norm_num) (by norm_num))) hε₀)
      (lt_min (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _))
  refine ⟨lamS, hlamSpos, ?_, max (max qS qR) (max (max qL qH) (max (max 3 qR') qH')), ?_⟩
  · rw [hlamSdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  intro q hq hqne χ₁ β₁ hχ hsq hβ1 hz hle a ha
  haveI := hqne
  have hqS : qS ≤ q :=
    le_trans (le_trans (le_max_left qS qR) (le_max_left (max qS qR) _)) hq
  have hqR : qR ≤ q :=
    le_trans (le_trans (le_max_right qS qR) (le_max_left (max qS qR) _)) hq
  have hqL : qL ≤ q := le_trans (le_trans (le_trans (le_max_left qL qH)
    (le_max_left (max qL qH) _)) (le_max_right (max qS qR) _)) hq
  have hqH : qH ≤ q := le_trans (le_trans (le_trans (le_max_right qL qH)
    (le_max_left (max qL qH) _)) (le_max_right (max qS qR) _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_trans (le_trans (le_max_left 3 qR')
    (le_max_left (max 3 qR') qH')) (le_max_right (max qL qH) _))
    (le_max_right (max qS qR) _)) hq
  have hqR' : qR' ≤ q := le_trans (le_trans (le_trans (le_trans (le_max_right 3 qR')
    (le_max_left (max 3 qR') qH')) (le_max_right (max qL qH) _))
    (le_max_right (max qS qR) _)) hq
  have hqH' : qH' ≤ q := le_trans (le_trans (le_trans (le_max_right (max 3 qR') qH')
    (le_max_right (max qL qH) _)) (le_max_right (max qS qR) _)) hq
  have hq2 : 2 ≤ q := by omega
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hRlog : R < Real.log q := by
    have h1 : Real.exp R < (qR' : ℝ) := by
      rw [hqR'def]
      have h2 : Real.exp R ≤ ((⌈Real.exp R⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : ((⌈Real.exp R⌉₊ : ℕ) : ℝ) < ((⌈Real.exp R⌉₊ : ℕ) : ℝ) + 1 := by norm_num
      push_cast
      linarith only [h2]
    have h2 : (qR' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqR'
    have h3 : Real.log (Real.exp R) < Real.log q :=
      Real.log_lt_log (Real.exp_pos R) (lt_of_lt_of_le h1 h2)
    rwa [Real.log_exp] at h3
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  set lam : ℝ := lamOf q (β₁ : ℂ) with hlamdef
  have hlampos : 0 < lam := lamOf_pos hχ hβ1 hz
  have hlam1 : lam ≤ 1 / 100 :=
    le_trans hle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hlamE0 : lam ≤ ε₀ :=
    le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hlam2' : lam ≤ min (1 / 2) (2 / (5 * (49 / 10))) :=
    le_trans hle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hlam2 : lam ≤ 1 / 2 := le_trans hlam2' (min_le_left _ _)
  have hlamA : lam ≤ ((3 / 10 : ℝ) ^ 2 * (49 / 10) / (8 * C₁)) ^ (1 / δ) :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlamE : lam ≤ Real.exp (-(R + 1) / c) :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the repulsion in the form used below
  have hrepbdd : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → c * Real.log (1 / lam) ≤ lamOf q ρ := by
    intro χ ρ hzρ him hne
    rw [hlamdef]
    exact hRep' q hqR χ₁ β₁ hχ hsq hβ1 hz hlamE0 χ ρ hzρ him hne
  have hΛR : R < c * Real.log (1 / lam) := by
    have h1 : Real.exp ((R + 1) / c) ≤ 1 / lam := by
      have h2 : lam ≤ Real.exp (-(R + 1) / c) := hlamE
      have h3 : 1 / Real.exp (-(R + 1) / c) ≤ 1 / lam :=
        one_div_le_one_div_of_le hlampos h2
      have h4 : (1 : ℝ) / Real.exp (-(R + 1) / c) = Real.exp ((R + 1) / c) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
      linarith only [h3, h4]
    have h5 : (R + 1) / c ≤ Real.log (1 / lam) := by
      have h6 : Real.log (Real.exp ((R + 1) / c)) ≤ Real.log (1 / lam) :=
        Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h6
    have h7 : c * ((R + 1) / c) = R + 1 := by field_simp
    nlinarith only [h5, hc, h7]
  -- the box part
  have hsimple : zeroMult χ₁ (β₁ : ℂ) = 1 := hSimple' q hqS χ₁ β₁ hχ hsq hβ1 hz hlam1
  have hlamR : lam ≤ R := le_trans hlam1 (le_trans (by norm_num) hR)
  have him0 : |(β₁ : ℂ).im| * Real.log q ≤ R := by
    simp only [Complex.ofReal_im, abs_zero, zero_mul]
    exact hR0
  have hbox : signedBoxSumAll q (11 / 2) (3 / 10) R a
      ≤ ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖ :=
    signedBoxSumAll_le_exceptional hq2 hRlog hsq hrepbdd hΛR hR0
      (by rw [hlamdef] at hlamR; exact hlamR) hsimple ha
  -- the far part
  have hfar : farZeroSum q (11 / 2) (3 / 10) R
      ≤ restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        + restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10) :=
    farZeroSum_le_restLow_add_restHigh hq2 hRlog hrepbdd hΛR
      (by rw [hlamdef] at hlamR; exact hlamR) him0 (hsum q)
  have hlow : restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10) ≤ C₁ * lam ^ (1 + δ) := by
    have h := hLow' q hqL χ₁ β₁ hχ hsq hβ1 hz hlamE0
    rwa [← hlamdef] at h
  have hhigh : restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      ≤ C₂ * lam * (Real.log q) ^ e := by
    have h := hHigh' q hqH χ₁ β₁ hχ hsq hβ1 hz hlam2
    rwa [← hlamdef] at h
  -- the kernel bound
  have hkern' : ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖
      ≤ (3 / 10 : ℝ) ^ 2 * Real.exp (-(49 / 10 * lam)) := by
    have h := Hk_norm_le_exp_lamOf (q := q) (L := 11 / 2) (K := 3 / 10) (ρ := (β₁ : ℂ)) hK
      (by omega) (by simpa using hβ1)
    rw [← hlamdef] at h
    have h1 : -(11 / 2 - 2 * (3 / 10)) * lamOf q (β₁ : ℂ) = -(49 / 10 * lamOf q (β₁ : ℂ)) := by
      ring
    rw [h1] at h
    exact h
  -- the height threshold
  have hC₂L : C₂ * (Real.log q) ^ e ≤ (3 / 10 : ℝ) ^ 2 * (49 / 10) / 8 := by
    have hleL₀ : L₀ ≤ Real.log q := by
      have h1 : Real.exp L₀ ≤ (qH' : ℝ) := by
        rw [hqH'def]
        have h2 : Real.exp L₀ ≤ ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have h3 : ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) ≤ ((⌈Real.exp L₀⌉₊ : ℕ) : ℝ) + 1 := by linarith only []
        push_cast
        linarith only [h2]
      have h2 : (qH' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqH'
      calc L₀ = Real.log (Real.exp L₀) := (Real.log_exp L₀).symm
        _ ≤ Real.log q := Real.log_le_log (Real.exp_pos L₀) (le_trans h1 h2)
    have h3 : (Real.log q) ^ e ≤ L₀ ^ e :=
      Real.rpow_le_rpow_of_nonpos hL₀pos hleL₀ heneg.le
    have h4 : C₂ * L₀ ^ e = (3 / 10 : ℝ) ^ 2 * (49 / 10) / 8 := by
      rw [hL₀pow]
      field_simp
    calc C₂ * (Real.log q) ^ e ≤ C₂ * L₀ ^ e := mul_le_mul_of_nonneg_left h3 hC₂pos.le
      _ = (3 / 10 : ℝ) ^ 2 * (49 / 10) / 8 := h4
  -- the closing arithmetic
  have hlog1 : 1 ≤ Real.log q := by
    have h1 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans h1.le (Real.log_le_log (by norm_num) (by exact_mod_cast hq3))
  have hclose := siegel_close_arith (K := 3 / 10) (a₀ := 49 / 10) (C₁ := C₁) (δ := δ)
    (C₂ := C₂) (e := e) (Lq := Real.log q) hK ha₀ hC₁pos hδpos hC₂pos.le heneg hlog1 hC₂L
  have hmain := hclose lam hlampos (le_min hlam2' hlamA)
  calc signedBoxSumAll q (11 / 2) (3 / 10) R a + farZeroSum q (11 / 2) (3 / 10) R
      ≤ ‖Hk (11 / 2) (3 / 10) ((1 - (β₁ : ℂ)) * (Real.log q : ℂ))‖
          + (restLowZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
            + restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)) := add_le_add hbox hfar
    _ ≤ (3 / 10 : ℝ) ^ 2 * Real.exp (-(49 / 10 * lam))
          + (C₁ * lam ^ (1 + δ) + C₂ * lam * (Real.log q) ^ e) :=
        add_le_add hkern' (add_le_add hlow hhigh)
    _ ≤ (3 / 10 : ℝ) ^ 2 * (1 - (49 / 10) * lam / 2) := by linarith only [hmain]
    _ = (3 / 10 : ℝ) ^ 2 * (1 - (49 / 10) * lamOf q (β₁ : ℂ) / 2) := by rw [hlamdef]

end

end Work.LinnikAreas
