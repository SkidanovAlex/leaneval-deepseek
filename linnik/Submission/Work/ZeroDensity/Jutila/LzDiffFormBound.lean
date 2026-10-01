import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffDefs
import Submission.Work.ZeroDensity.Jutila.LzSubEqSumSteps
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs
import Submission.Work.ZeroDensity.Jutila.mainTerm
import Submission.Work.LinnikAreas.JutilaPieces.SelbergFormBound
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization

namespace Work.ZeroDensity.Jutila

open Finset
open scoped BigOperators

noncomputable section

/-! ## 1. The step weights of the integer partition of `[w,y]` -/

/-- The log-length of the `j`-th piece of the partition of `[w,y]` cut at the integers. -/
def stepWt (w y : ℝ) (j : ℕ) : ℝ :=
  Real.log (min y ((j : ℝ) + 1)) - Real.log (max w (j : ℝ))

/-- The step weights are nonnegative. -/
lemma stepWt_nonneg {w y : ℝ} (hw : 0 < w) (hwy : w < y) {j : ℕ}
    (hj1 : ⌊w⌋₊ ≤ j) (hj2 : j ≤ ⌊y⌋₊) : 0 ≤ stepWt w y j := by
  have hle1 : w ≤ min y ((j : ℝ) + 1) := by
    rw [le_min_iff]
    refine ⟨le_of_lt hwy, ?_⟩
    have h1 : w < ((⌊w⌋₊ : ℕ) : ℝ) + 1 := by simpa using Nat.lt_floor_add_one w
    have h2 : ((⌊w⌋₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    linarith
  have hle2 : (j : ℝ) ≤ min y ((j : ℝ) + 1) := by
    rw [le_min_iff]
    refine ⟨?_, by push_cast; linarith⟩
    have h2 : (j : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hj2
    have h3 : (0 : ℝ) ≤ y := le_of_lt (lt_trans hw hwy)
    linarith [Nat.floor_le h3]
  have hle : max w (j : ℝ) ≤ min y ((j : ℝ) + 1) := max_le hle1 hle2
  have hpos : 0 < max w (j : ℝ) := lt_of_lt_of_le hw (le_max_left _ _)
  unfold stepWt
  exact sub_nonneg.mpr (Real.log_le_log hpos hle)

/-- **The step weights sum to `log (y/w)`.** -/
lemma sum_stepWt {w y : ℝ} (hw : 1 < w) (hwy : w < y) :
    ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j = Real.log (y / w) := by
  simpa only [stepWt] using stepWFull hw hwy

/-- **The step decomposition of the difference weights.** -/
lemma bvLam_eq_mu_mul_sum_stepWt {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 ⌊y⌋₊) :
    bvLam w y d = (ArithmeticFunction.moebius d : ℝ) *
      ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (if d ≤ j then stepWt w y j else 0) := by
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have h := stepWFilter (w := w) (y := y) hw hwy (d := d) hd1
  have h' : (∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (if d ≤ j then stepWt w y j else 0))
      = (if (d : ℝ) ≤ y then Real.log (y / (d : ℝ)) else 0)
        - (if (d : ℝ) ≤ w then Real.log (w / (d : ℝ)) else 0) := by
    simp only [stepWt]
    rw [← Finset.sum_filter, h]
  rw [bvLam, h']

/-! ## 2. The Selberg diagonalization of the `lcm` form

`Σ_{d,e ≤ Y} a d · a e / lcm(d,e) = Σ_{k ≤ Y} φ(k)·(Σ_{k ∣ d ≤ Y} a d / d)²`. -/

/-- **Selberg diagonalization of the `lcm` quadratic form.** -/
lemma selbergForm_diag (Y : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 Y, ∑ e ∈ Finset.Icc 1 Y, a d * a e / (Nat.lcm d e : ℝ))
      = ∑ k ∈ Finset.Icc 1 Y, (Nat.totient k : ℝ) *
          (∑ d ∈ Finset.Icc 1 Y, (if k ∣ d then a d / (d : ℝ) else 0)) ^ 2 := by
  rcases Nat.eq_zero_or_pos Y with hY | hY
  · subst hY; simp
  have hTpos : ∀ d ∈ Finset.Icc 1 Y, 0 < d := by
    intro d hd; rw [Finset.mem_Icc] at hd; omega
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ Finset.Icc 1 Y → l ∈ Finset.Icc 1 Y := by
    intro l d hld hd
    rw [Finset.mem_Icc] at hd ⊢
    exact ⟨Nat.pos_of_dvd_of_pos hld (by omega),
      le_trans (Nat.le_of_dvd (by omega) hld) hd.2⟩
  have hpoint : ∀ d ∈ Finset.Icc 1 Y, ∀ e ∈ Finset.Icc 1 Y,
      a d * a e / (Nat.lcm d e : ℝ) = a d / (d : ℝ) * (a e / (e : ℝ)) * (Nat.gcd d e : ℝ) := by
    intro d hd e he
    rw [Finset.mem_Icc] at hd he
    exact Commons.NumberTheory.Sieve.lcm_term a (by omega) (by omega)
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hpoint d hd e he))]
  rw [Commons.NumberTheory.Sieve.sum_gcd_eq_sum_totient_sq (Finset.Icc 1 Y) hTpos hTclosed
    (fun d => a d / (d : ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [Finset.sum_filter]

/-- The diagonal values of the Möbius `lcm` form, written with the truncated weights. -/
lemma mobius_form_eq (V : ℕ) (hV : 1 ≤ V) :
    (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
          / (Nat.lcm d e : ℝ))
      = ∑ k ∈ Finset.Icc 1 V, (Nat.totient k : ℝ) *
          (∑ d ∈ Finset.Icc 1 V, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            else 0)) ^ 2 :=
  selbergForm_diag V (fun d => (ArithmeticFunction.moebius d : ℝ))

/-! ## 3. The weight sums along the partition -/

/-- **The `k`-th diagonalized weight is the step-weighted sum of the truncated partial sums.** -/
lemma bk_eq_step_sum {w y : ℝ} (hw : 1 < w) (hwy : w < y) (k : ℕ) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, (if k ∣ d then bvLam w y d / (d : ℝ) else 0))
      = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
          (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            else 0)) := by
  have hstep : ∀ d ∈ Finset.Icc 1 ⌊y⌋₊,
      (if k ∣ d then bvLam w y d / (d : ℝ) else 0)
        = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
            (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0) *
              (if d ≤ j then stepWt w y j else 0) := by
    intro d hd
    by_cases hk : k ∣ d
    · rw [if_pos hk, if_pos hk, bvLam_eq_mu_mul_sum_stepWt hw hwy hd]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [if_neg hk, if_neg hk, Finset.sum_eq_zero]
      intro j _
      rw [zero_mul]
  calc (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, (if k ∣ d then bvLam w y d / (d : ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
          (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0) *
            (if d ≤ j then stepWt w y j else 0) :=
        Finset.sum_congr rfl (fun d hd => hstep d hd)
    _ = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
          (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0) *
            (if d ≤ j then stepWt w y j else 0) := Finset.sum_comm
    _ = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
          (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjy : j ≤ ⌊y⌋₊ := (Finset.mem_Icc.mp hj).2
        have hIcc : Finset.Icc 1 j = (Finset.Icc 1 ⌊y⌋₊).filter (fun d => d ≤ j) := by
          ext d; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
        have h1 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
              (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0) *
                (if d ≤ j then stepWt w y j else 0))
            = ∑ d ∈ Finset.Icc 1 j,
                (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0) *
                  stepWt w y j := by
          rw [hIcc, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _
          by_cases h2 : d ≤ j <;> simp [h2]
        rw [h1, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring

/-! ## 4. The small-`log(y/w)` bound -/

/-- **The form bound for `log(y/w) ≤ 1`.** -/
lemma form_bound_small {w y : ℝ} (hw : 1 < w) (hwy : w < y) {C : ℝ} (hCpos : 0 < C)
    (hA : ∀ V : ℕ, 1 ≤ V → (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
          / (Nat.lcm d e : ℝ)) ≤ C)
    (hL1 : Real.log (y / w) ≤ 1) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      ≤ 2 * C * Real.log (y / w) := by
  have hw0 : 0 < w := by linarith
  have hY1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1:ℝ) ≤ y))
  have hw1 : 1 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast (le_of_lt hw))
  have hLnn : 0 ≤ Real.log (y / w) :=
    Real.log_nonneg (by rw [le_div_iff₀ hw0, one_mul]; linarith)
  -- diagonalize the difference form
  have hdiag := selbergForm_diag ⌊y⌋₊ (fun d => bvLam w y d)
  -- Cauchy–Schwarz in the step index, for each `k`
  have hcs : ∀ k : ℕ, (∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
        (if k ∣ d then bvLam w y d / (d : ℝ) else 0)) ^ 2
      ≤ Real.log (y / w) * ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
          (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            else 0)) ^ 2 := by
    intro k
    have hstepnn : ∀ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, 0 ≤ stepWt w y j := by
      intro j hj
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
      exact stepWt_nonneg hw0 hwy h1 h2
    have hdec := bk_eq_step_sum hw hwy k
    rw [hdec]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc ⌊w⌋₊ ⌊y⌋₊)
      (fun j => Real.sqrt (stepWt w y j))
      (fun j => Real.sqrt (stepWt w y j) *
        (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
          else 0)))
    have h1 : (∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
          (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
            else 0)))
        = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, Real.sqrt (stepWt w y j) *
            (Real.sqrt (stepWt w y j) *
              (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
                else 0))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_assoc, ← sq, Real.sq_sqrt (hstepnn j hj)]
    have h2 : (∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (Real.sqrt (stepWt w y j)) ^ 2)
        = Real.log (y / w) := by
      rw [← sum_stepWt hw hwy]
      exact Finset.sum_congr rfl (fun j hj => Real.sq_sqrt (hstepnn j hj))
    have h3 : (∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
          (Real.sqrt (stepWt w y j) *
            (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
              else 0))) ^ 2)
        = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
            (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
              else 0)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow, Real.sq_sqrt (hstepnn j hj)]
    rw [← h1] at h
    rw [h2, h3] at h
    exact h
  -- assemble
  have hkey : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      = ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
          (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, (if k ∣ d then bvLam w y d / (d : ℝ) else 0)) ^ 2 := hdiag
  have hterm : ∀ k ∈ Finset.Icc 1 ⌊y⌋₊,
      (Nat.totient k : ℝ) * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
          (if k ∣ d then bvLam w y d / (d : ℝ) else 0)) ^ 2
        ≤ (Nat.totient k : ℝ) * (Real.log (y / w) * ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊,
            stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
              (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2) := by
    intro k _
    exact mul_le_mul_of_nonneg_left (hcs k) (Nat.cast_nonneg _)
  calc (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      = ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
          (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, (if k ∣ d then bvLam w y d / (d : ℝ) else 0)) ^ 2 := hkey
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
          (Real.log (y / w) * ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
            (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
              else 0)) ^ 2) := Finset.sum_le_sum hterm
    _ = Real.log (y / w) * ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
            (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
              else 0)) ^ 2) := by
        have key : ∀ k : ℕ, (Nat.totient k : ℝ) * (Real.log (y / w) *
              ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
                (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then
                  (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2)
              = Real.log (y / w) * ((Nat.totient k : ℝ) *
                ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j *
                  (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then
                    (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2) :=
          fun k => by ring
        have h1 : (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) * (Real.log (y / w) *
              ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2))
            = Real.log (y / w) * ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
                ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                  (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2 := by
          rw [Finset.sum_congr rfl (fun k _ => key k)]
          rw [Finset.mul_sum]
        have h2 : (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
              ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2)
            = ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (Nat.totient k : ℝ) *
                (stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                  (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
        have h3 : (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, (Nat.totient k : ℝ) *
                (stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                  (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2))
            = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
                (stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                  (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2) :=
          Finset.sum_comm
        have h4 : (∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
                (stepWt w y j * (∑ d ∈ Finset.Icc 1 j,
                  (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2))
            = ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j * (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
                (∑ d ∈ Finset.Icc 1 j,
                  (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [h1, h2, h3, h4]
    _ ≤ Real.log (y / w) * ∑ j ∈ Finset.Icc ⌊w⌋₊ ⌊y⌋₊, stepWt w y j * C := by
        apply mul_le_mul_of_nonneg_left _ hLnn
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        have hj1' : 1 ≤ j := le_trans hw1 hj1
        have hIcc : Finset.Icc 1 j ⊆ Finset.Icc 1 ⌊y⌋₊ := Finset.Icc_subset_Icc_right hj2
        have hzero : ∀ k ∈ Finset.Icc 1 ⌊y⌋₊, k ∉ Finset.Icc 1 j →
            (Nat.totient k : ℝ) * (∑ d ∈ Finset.Icc 1 j,
              (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) ^ 2 = 0 := by
          intro k hk hk'
          have hkj : j < k := by
            by_contra hcon
            exact hk' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, le_of_not_gt hcon⟩)
          have hinner : (∑ d ∈ Finset.Icc 1 j,
              (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) else 0)) = 0 := by
            apply Finset.sum_eq_zero
            intro d hd
            have hd1' : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            have hdj : d ≤ j := (Finset.mem_Icc.mp hd).2
            have hnd : ¬ k ∣ d := by
              intro hkd
              have hkd' : k ≤ d := Nat.le_of_dvd (by omega) hkd
              omega
            simp [hnd]
          rw [hinner]; ring
        have hsum_eq : (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) *
              (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
                else 0)) ^ 2)
            = ∑ k ∈ Finset.Icc 1 j, (Nat.totient k : ℝ) *
              (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
                else 0)) ^ 2 := by
          rw [← Finset.sum_subset hIcc hzero]
        have hbound : (∑ k ∈ Finset.Icc 1 j, (Nat.totient k : ℝ) *
              (∑ d ∈ Finset.Icc 1 j, (if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)
                else 0)) ^ 2) ≤ C := by
          rw [← mobius_form_eq j hj1']
          exact hA j hj1'
        rw [hsum_eq]
        exact mul_le_mul_of_nonneg_left hbound (stepWt_nonneg hw0 hwy hj1 hj2)
    _ = C * Real.log (y / w) * Real.log (y / w) := by
        rw [← Finset.sum_mul, sum_stepWt hw hwy]
        ring
    _ ≤ 2 * C * Real.log (y / w) := by
        have hL2 : Real.log (y / w) * Real.log (y / w) ≤ Real.log (y / w) := by
          nlinarith [hLnn, hL1]
        nlinarith [hL2, hCpos, hLnn]

/-! ## 5. The Selberg form identity for the difference weights -/

/-- The Selberg weight of cutoff `w`, extended by `0` past `⌊w⌋₊`. -/
def selWc (w : ℝ) (d : ℕ) : ℝ := if d ≤ ⌊w⌋₊ then selW w d else 0

/-- Restriction of a weighted sum of the conditional Selberg weight. -/
lemma sum_selWc {w y : ℝ} (hle : ⌊w⌋₊ ≤ ⌊y⌋₊) (f : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 1 ⌊y⌋₊, selWc w e * f e)
      = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊, selW w e * f e := by
  have h := Finset.sum_subset (s₁ := Finset.Icc 1 ⌊w⌋₊) (s₂ := Finset.Icc 1 ⌊y⌋₊)
    (f := fun e => selWc w e * f e) (Finset.Icc_subset_Icc_right hle)
    (fun e he he' => by
      have h1 : ¬ e ≤ ⌊w⌋₊ := by
        intro h
        exact he' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1, h⟩)
      simp only [selWc]
      rw [if_neg h1, zero_mul])
  rw [← h]
  exact Finset.sum_congr rfl (fun e he => by
    simp only [selWc]; rw [if_pos (Finset.mem_Icc.mp he).2])

/-- `bvLam` is the difference of the two Selberg weights. -/
lemma bvLam_eq_selW_sub {w y : ℝ} (hw : 1 < w) (hwy : w < y) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 ⌊y⌋₊) :
    bvLam w y d = selW y d - selWc w d := by
  obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
  have hy0 : 0 < y := by linarith
  have hw0 : 0 < w := by linarith
  have hdy' : (d : ℝ) ≤ y := le_trans (by exact_mod_cast hdy) (Nat.floor_le (le_of_lt hy0))
  have hdir1 : (d : ℝ) ≤ w → d ≤ ⌊w⌋₊ := fun h => Nat.le_floor h
  have hdir2 : d ≤ ⌊w⌋₊ → (d : ℝ) ≤ w :=
    fun h => le_trans (by exact_mod_cast h) (Nat.floor_le (le_of_lt hw0))
  simp only [bvLam, selW, selWc]
  rw [if_pos hdy']
  by_cases h : d ≤ ⌊w⌋₊
  · rw [if_pos (hdir2 h), if_pos h]
    ring
  · rw [if_neg (fun hh => h (hdir1 hh)), if_neg h]
    ring

/-- **The form of the difference weights is the second difference of the Selberg form.** -/
lemma form_eq_Msq {w y : ℝ} (hw : 1 < w) (hwy : w < y) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      = Msq y y - 2 * Msq w y + Msq w w := by
  have hle : ⌊w⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono (le_of_lt hwy)
  have hXY : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
      selW y d * selWc w e / (Nat.lcm d e : ℝ)) = Msq w y := by
    have h1 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        selW y d * selWc w e / (Nat.lcm d e : ℝ))
        = ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
            selW y d * selWc w e / (Nat.lcm d e : ℝ) := Finset.sum_comm
    have h2 : (∑ e ∈ Finset.Icc 1 ⌊y⌋₊, ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
        selW y d * selWc w e / (Nat.lcm d e : ℝ))
        = ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selWc w e * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, selW y d / (Nat.lcm d e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    have h3 : (∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        selWc w e * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, selW y d / (Nat.lcm d e : ℝ)))
        = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
            selW w e * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, selW y d / (Nat.lcm d e : ℝ)) :=
      sum_selWc hle (fun m => ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, selW y d / (Nat.lcm d m : ℝ))
    have h4 : (∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
        selW w e * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, selW y d / (Nat.lcm d e : ℝ)))
        = ∑ e ∈ Finset.Icc 1 ⌊w⌋₊, ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
            selW w e * selW y d / (Nat.lcm e d : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Nat.lcm_comm]
      ring
    have h5 : (∑ e ∈ Finset.Icc 1 ⌊w⌋₊, ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
        selW w e * selW y d / (Nat.lcm e d : ℝ)) = Msq w y := by
      rw [Msq]
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hYY : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
      selWc w d * selWc w e / (Nat.lcm d e : ℝ)) = Msq w w := by
    have h1 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        selWc w d * selWc w e / (Nat.lcm d e : ℝ))
        = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
            selWc w d * (∑ e ∈ Finset.Icc 1 ⌊y⌋₊, selWc w e / (Nat.lcm d e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    have h2 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
        selWc w d * (∑ e ∈ Finset.Icc 1 ⌊y⌋₊, selWc w e / (Nat.lcm d e : ℝ)))
        = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
            selWc w d * (∑ e ∈ Finset.Icc 1 ⌊w⌋₊, selW w e / (Nat.lcm d e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      have h := sum_selWc hle (fun m => (Nat.lcm d m : ℝ)⁻¹)
      simpa only [div_eq_mul_inv] using h
    have h3 : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊,
        selWc w d * (∑ e ∈ Finset.Icc 1 ⌊w⌋₊, selW w e / (Nat.lcm d e : ℝ)))
        = ∑ d ∈ Finset.Icc 1 ⌊w⌋₊,
            selW w d * (∑ e ∈ Finset.Icc 1 ⌊w⌋₊, selW w e / (Nat.lcm d e : ℝ)) :=
      sum_selWc hle (fun m => ∑ e ∈ Finset.Icc 1 ⌊w⌋₊, selW w e / (Nat.lcm m e : ℝ))
    have h4 : (∑ d ∈ Finset.Icc 1 ⌊w⌋₊,
        selW w d * (∑ e ∈ Finset.Icc 1 ⌊w⌋₊, selW w e / (Nat.lcm d e : ℝ)))
        = ∑ d ∈ Finset.Icc 1 ⌊w⌋₊, ∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
            selW w d * selW w e / (Nat.lcm d e : ℝ) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    have h5 : (∑ d ∈ Finset.Icc 1 ⌊w⌋₊, ∑ e ∈ Finset.Icc 1 ⌊w⌋₊,
        selW w d * selW w e / (Nat.lcm d e : ℝ)) = Msq w w := by
      rw [Msq]
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hstep : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          (selW y d - selWc w d) * (selW y e - selWc w e) / (Nat.lcm d e : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [bvLam_eq_selW_sub hw hwy hd, bvLam_eq_selW_sub hw hwy he]
  have hexp : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        (selW y d - selWc w d) * (selW y e - selWc w e) / (Nat.lcm d e : ℝ))
      = (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selW y d * selW y e / (Nat.lcm d e : ℝ))
        - 2 * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selW y d * selWc w e / (Nat.lcm d e : ℝ))
        + (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selWc w d * selWc w e / (Nat.lcm d e : ℝ)) := by
    have hp : ∀ d e : ℕ,
        (selW y d - selWc w d) * (selW y e - selWc w e) / (Nat.lcm d e : ℝ)
          = selW y d * selW y e / (Nat.lcm d e : ℝ)
            - selW y d * selWc w e / (Nat.lcm d e : ℝ)
            - selWc w d * selW y e / (Nat.lcm d e : ℝ)
            + selWc w d * selWc w e / (Nat.lcm d e : ℝ) := by
      intro d e; ring
    have hsym : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        selWc w d * selW y e / (Nat.lcm d e : ℝ))
        = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selW y d * selWc w e / (Nat.lcm d e : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Nat.lcm_comm]
      ring
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => hp d e))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsym]
    ring
  have hXX : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
      selW y d * selW y e / (Nat.lcm d e : ℝ)) = Msq y y := by
    rw [Msq]
  calc (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      = ∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          (selW y d - selWc w d) * (selW y e - selWc w e) / (Nat.lcm d e : ℝ) := hstep
    _ = (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selW y d * selW y e / (Nat.lcm d e : ℝ))
        - 2 * (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selW y d * selWc w e / (Nat.lcm d e : ℝ))
        + (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            selWc w d * selWc w e / (Nat.lcm d e : ℝ)) := hexp
    _ = Msq y y - 2 * Msq w y + Msq w w := by rw [hXX, hXY, hYY]

/-! ## 6. The large-`log(y/w)` bound -/

/-- **The form bound for `log(y/w) ≥ 1`**, from the sharp two-parameter Selberg main term. -/
lemma form_bound_large {w y : ℝ} (hw : 1 < w) (hwy : w < y) {Cm : ℝ} (hCm : 0 < Cm)
    (hmain : ∀ a b : ℝ, 1 < a → a ≤ b →
      |Msq a b - Real.log a| ≤ Cm * (1 + Real.log (b / a)))
    (hL1 : 1 ≤ Real.log (y / w)) :
    (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
        bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
      ≤ (1 + 6 * Cm) * Real.log (y / w) := by
  have hw0 : 0 < w := by linarith
  have hy1 : 1 < y := lt_trans hw (by linarith)
  have hyy : |Msq y y - Real.log y| ≤ Cm := by
    have h := hmain y y hy1 le_rfl
    rwa [div_self (ne_of_gt (by linarith : (0:ℝ) < y)), Real.log_one, add_zero, mul_one] at h
  have hwy' : |Msq w y - Real.log w| ≤ Cm * (1 + Real.log (y / w)) :=
    hmain w y hw (le_of_lt hwy)
  have hww : |Msq w w - Real.log w| ≤ Cm := by
    have h := hmain w w hw le_rfl
    rwa [div_self (ne_of_gt hw0), Real.log_one, add_zero, mul_one] at h
  have hlog : Real.log (y / w) = Real.log y - Real.log w :=
    Real.log_div (by linarith) (by linarith)
  have h1 : Msq y y ≤ Real.log y + Cm := by linarith [(abs_le.1 hyy).2]
  have h2 : Real.log w - Cm * (1 + Real.log (y / w)) ≤ Msq w y := by
    linarith [(abs_le.1 hwy').1]
  have h3 : Msq w w ≤ Real.log w + Cm := by linarith [(abs_le.1 hww).2]
  have hLnn : 0 ≤ Real.log (y / w) := le_trans zero_le_one hL1
  rw [form_eq_Msq hw hwy]
  nlinarith [h1, h2, h3, hlog, hL1, hLnn, hCm]

/-! ## 7. The theorem -/

/-- **The Selberg quadratic form of the difference weights.**  There is an absolute
`κ > 0` with `Σ_{d,e ≤ y} bvLam w y d · bvLam w y e / lcm(d,e) ≤ κ·log(y/w)` for all
`1 < w < y`. -/
theorem LzDiffFormBound :
    ∃ κ : ℝ, 0 < κ ∧ ∀ w y : ℝ, 1 < w → w < y →
      (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
        ≤ κ * Real.log (y / w) := by
  obtain ⟨C, hCpos, hA⟩ := Work.LinnikAreas.JutilaPieces.SelbergFormBound
  obtain ⟨Cm, hCmpos, hmain⟩ := mainTerm
  refine ⟨max (2 * C) (1 + 6 * Cm), by positivity, fun w y hw hwy => ?_⟩
  have hw0 : 0 < w := by linarith
  have hLpos : 0 < Real.log (y / w) :=
    Real.log_pos (by rw [lt_div_iff₀ hw0, one_mul]; linarith)
  have hLnn : 0 ≤ Real.log (y / w) := le_of_lt hLpos
  by_cases hL : Real.log (y / w) ≤ 1
  · have hsmall : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ)) ≤ 2 * C * Real.log (y / w) :=
      form_bound_small hw hwy hCpos hA hL
    calc (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
        ≤ 2 * C * Real.log (y / w) := hsmall
      _ ≤ max (2 * C) (1 + 6 * Cm) * Real.log (y / w) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hLnn
  · have hLge : 1 ≤ Real.log (y / w) := le_of_lt (lt_of_not_ge hL)
    have hlarge : (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
          bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ)) ≤ (1 + 6 * Cm) * Real.log (y / w) :=
      form_bound_large hw hwy hCmpos hmain hLge
    calc (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, ∑ e ∈ Finset.Icc 1 ⌊y⌋₊,
            bvLam w y d * bvLam w y e / (Nat.lcm d e : ℝ))
        ≤ (1 + 6 * Cm) * Real.log (y / w) := hlarge
      _ ≤ max (2 * C) (1 + 6 * Cm) * Real.log (y / w) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hLnn

end

end Work.ZeroDensity.Jutila
