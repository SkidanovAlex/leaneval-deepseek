import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs

namespace Work.Maximal

open Work.BourgainPlan.Maximal

/-- **The MST threshold `2^{κ_s}` is killed by the exponential gain.**  For `c > 0`, `C > 0` and `P ∈ ℤ[X]` of positive degree, for all large `s`

  `(2^{κ_s} + 1) · C · exp(-c √(s+1)) ≤ 1`,   `κ_s = mstKappa P s = 20 · deg P · (⌊(s+1)^{1/10}⌋ + 1)`.

This is the arithmetic that absorbs the `2^{κ_s}`-fold sum of the freezing errors (each of size `exp(-c√(s+1))`, uniformly in the scale `k`) into the `(s+1)log(s+2)` of the small-scale estimate of MST Theorem 7.

Route.  `κ_s log 2 ≤ 20 d log 2 ((s+1)^{1/10} + 1) ≤ 20 d log 2 · (B √(s+1) + 1) ≤ 40 d log 2 · B √(s+1) = (c/2)√(s+1)` for large `s`, with `B := c/(80 d log 2)` and the asymptotic `(s+1)^{1/10} ≤ B√(s+1)` (`rpow_ten_le_mul_sqrt`, in `mst_lvl_defs`; the sibling `mstKappa_exp_le_one` there is the special case `c = 1/4`, `C = 1`), whence `2^{κ_s} ≤ exp((c/2)√(s+1))`.  Then

  `(2^{κ_s}+1)C e^{-c√} ≤ (e^{c√/2}+1) C e^{-c√} = C e^{-c√/2} + C e^{-c√} ≤ 1/2 + 1/2`,

each term being `≤ 1/2` once `√(s+1) ≥ 2log(2C)/c`.  The three "for large `s`" thresholds are combined with `max`; the elementary facts `∃S, ∀s ≥ S, K ≤ √(s+1)` (take `S = ⌈K²⌉+1` and `Real.sqrt_le_sqrt`) are part of the proof. -/
theorem kappa_exp_le_inv (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) :
    ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
      ((2 : ℝ) ^ (Work.BourgainPlan.Maximal.mstKappa P s) + 1) * C
        * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) ≤ 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hdR : 0 < (P.natDegree : ℝ) := by
    have : 0 < P.natDegree := by omega
    exact_mod_cast this
  obtain ⟨N₁, hN₁⟩ := rpow_ten_le_mul_sqrt (c / (80 * (P.natDegree : ℝ) * Real.log 2))
    (by positivity)
  set K : ℝ := 2 * Real.log (2 * C) / c with hKdef
  refine ⟨max N₁ (⌈(max K 0) ^ 2⌉₊), fun s hs => ?_⟩
  have hsN : N₁ ≤ s := le_trans (le_max_left _ _) hs
  have hsK : ⌈(max K 0) ^ 2⌉₊ ≤ s := le_trans (le_max_right _ _) hs
  have hsqrtK : K ≤ Real.sqrt ((s : ℝ) + 1) := by
    have hM2 : ((⌈(max K 0) ^ 2⌉₊ : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsK
    have hceil : (max K 0) ^ 2 ≤ ((⌈(max K 0) ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hMs : (max K 0) ^ 2 ≤ (s : ℝ) := le_trans hceil hM2
    have h1 : max K 0 ≤ Real.sqrt ((s : ℝ) + 1) := by
      rw [← Real.sqrt_sq (le_max_right K 0)]
      exact Real.sqrt_le_sqrt (by linarith)
    exact le_trans (le_max_left K 0) h1
  have hx1 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 10 : ℝ) := (Real.one_rpow _).symm
      _ ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s]) (by norm_num)
  have hfloor : ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1
      ≤ 2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
    have hle : ((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ)
        ≤ ((s : ℝ) + 1) ^ (1 / 10 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    linarith
  have hpow : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      ≤ (c / (80 * (P.natDegree : ℝ) * Real.log 2)) * Real.sqrt ((s : ℝ) + 1) :=
    hN₁ s hsN
  have hκ : (mstKappa P s : ℝ) * Real.log 2 ≤ (c / 2) * Real.sqrt ((s : ℝ) + 1) := by
    rw [mstKappa]
    push_cast
    have h1 : (20 : ℝ) * (P.natDegree : ℝ)
          * (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1)
        ≤ 20 * (P.natDegree : ℝ) * (2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor (by positivity)
    have h2 : 20 * (P.natDegree : ℝ) * (2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ))
        ≤ 20 * (P.natDegree : ℝ)
          * (2 * ((c / (80 * (P.natDegree : ℝ) * Real.log 2))
              * Real.sqrt ((s : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith [hpow]) (by positivity)
    have h3 : 20 * (P.natDegree : ℝ)
          * (2 * ((c / (80 * (P.natDegree : ℝ) * Real.log 2))
              * Real.sqrt ((s : ℝ) + 1)))
          * Real.log 2 = (c / 2) * Real.sqrt ((s : ℝ) + 1) := by
      field_simp
      ring
    calc (20 : ℝ) * (P.natDegree : ℝ)
            * (((⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) + 1) * Real.log 2
        ≤ (20 * (P.natDegree : ℝ) * (2 * ((s : ℝ) + 1) ^ (1 / 10 : ℝ))) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h1 hlog2.le
      _ ≤ (20 * (P.natDegree : ℝ)
            * (2 * ((c / (80 * (P.natDegree : ℝ) * Real.log 2))
                * Real.sqrt ((s : ℝ) + 1)))) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h2 hlog2.le
      _ = (c / 2) * Real.sqrt ((s : ℝ) + 1) := h3
  have h2pow : (2 : ℝ) ^ (mstKappa P s)
      ≤ Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (2 : ℝ) (mstKappa P s),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by rw [mul_comm]; exact hκ)
  have hlog2C : Real.log (2 * C) ≤ (c / 2) * Real.sqrt ((s : ℝ) + 1) := by
    have hK : Real.log (2 * C) = (c / 2) * K := by
      rw [hKdef]; field_simp
    rw [hK]
    exact mul_le_mul_of_nonneg_left hsqrtK (by positivity)
  have hexp_half : Real.exp (-(c / 2) * Real.sqrt ((s : ℝ) + 1)) ≤ 1 / (2 * C) := by
    have h1 : -(c / 2) * Real.sqrt ((s : ℝ) + 1) ≤ -Real.log (2 * C) := by linarith
    have h2 : Real.exp (-Real.log (2 * C)) = 1 / (2 * C) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
    calc Real.exp (-(c / 2) * Real.sqrt ((s : ℝ) + 1))
        ≤ Real.exp (-Real.log (2 * C)) := Real.exp_le_exp.mpr h1
      _ = 1 / (2 * C) := h2
  have hfinal : 2 * C * Real.exp (-(c / 2) * Real.sqrt ((s : ℝ) + 1)) ≤ 1 := by
    calc 2 * C * Real.exp (-(c / 2) * Real.sqrt ((s : ℝ) + 1))
        ≤ 2 * C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hexp_half (by positivity)
      _ = 1 := by field_simp
  have hexp_eq : Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1))
        * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))
      = Real.exp (-(c / 2) * Real.sqrt ((s : ℝ) + 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  have step1 : ((2 : ℝ) ^ (mstKappa P s) + 1) * C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))
      ≤ (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1) * C
        * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by
    have h := add_le_add h2pow (le_refl (1 : ℝ))
    have hE : 0 ≤ C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by positivity
    calc ((2 : ℝ) ^ (mstKappa P s) + 1) * C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))
        = ((2 : ℝ) ^ (mstKappa P s) + 1)
            * (C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))) := by ring
      _ ≤ (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1)
            * (C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_right h hE
      _ = (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1) * C
            * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by ring
  have step2 : (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1) * C
        * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))
      ≤ 2 * Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) * C
        * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by
    have h1e : (1 : ℝ) ≤ Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    have h : Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1
        ≤ 2 * Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) := by linarith
    have hE : 0 ≤ C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by positivity
    calc (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1) * C
          * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))
        = (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) + 1)
            * (C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))) := by ring
      _ ≤ (2 * Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)))
            * (C * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_right h hE
      _ = 2 * Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) * C
            * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) := by ring
  have step3 : 2 * Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) * C
        * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1))) ≤ 1 := by
    rw [show 2 * Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1)) * C
          * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))
        = 2 * C * (Real.exp ((c / 2) * Real.sqrt ((s : ℝ) + 1))
            * Real.exp (-(c * Real.sqrt ((s : ℝ) + 1)))) by ring, hexp_eq]
    exact hfinal
  exact le_trans step1 (le_trans step2 step3)

end Work.Maximal
