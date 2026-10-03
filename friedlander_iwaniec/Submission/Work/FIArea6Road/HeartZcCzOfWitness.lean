import Mathlib
import Submission.Work.FIArea6Road.HeartZcDefs

namespace Work.FIArea6Road

/-!
# `HeartZcCzOfWitness`

The correctly stated `C_z` lower bound of the §16 heart.  In
`Submission/Work/FIArea6Road/NOTES_HeartZcCzLower.md` it is shown that the sibling
`HeartZcCzLower` is false as stated: the continuation interface `heartZcHyp` only carries *upper*
bounds for `Zc`, so a lower bound on `C_z` can only follow if the datum supplies

* the size restriction `|m| ≤ 4 exp(√log N)` (the one `S16.HeartHyp` carries), and
* a *lower* bound `1/2 ≤ ‖Zsfun Pa χ m s‖` at some point `s` of the right edge `σ = 1 + 1/log N`.

Those are exactly the two extra hypotheses of the statement proved here.  The proof is elementary:
`heartZcHyp`'s strip clause bounds `‖Zc s‖` by `C_z · d · L(s)^6` with
`L(s) = log N + log(|m| + |Im s| + 3) + 2`, `Zc` agrees with `Zsfun` at `s`, and the two added
hypotheses give `L(s) ≤ c · log N` for a constant `c = c(K_w)` depending only on the height budget
`K_w`.  Hence `1 ≤ 2 c^6 · C_z · d · (log N)^6`, which is the claim with `K = 2 c^6`.

The only difference from the proved sibling `HeartZcCzLower_corrected` is that the height window of
the witness is `K_w ((log N)^4 + 1)` with `K_w > 0` *arbitrary*, so the constant `c` (and hence `K`)
must be allowed to depend on `K_w`.
-/

/-- **The elementary log-bound driving the lower bound.**  For `log N ≥ 100`, if
`|m| ≤ 4 exp(√log N)` and `|t| ≤ K_w ((log N)^4 + 1)` with `K_w > 0`, then

`log N + log(|m| + |t| + 3) + 2 ≤ (6 + (4 + log(2 K_w + 3))/100) · log N`.

The two ingredients are `log(|m| + 3) ≤ 2 + log N` (from `|m| ≤ 4 exp(√log N) ≤ 4 N`) and
`log(|t| + 3) ≤ log(2 K_w + 3) + 4 log N` (from `|t| + 3 ≤ (2 K_w + 3)(log N)^4`); together with
`log(|m| + |t| + 3) ≤ log(|m| + 3) + log(|t| + 3)` this gives the claim after absorbing the
additive constant into `(1/100)·log N`, legitimate because `log N ≥ 100`. -/
lemma heart_log_L_le (K_w : ℝ) (hKw : 0 < K_w) (N : ℝ) (m : ℤ) (t : ℝ)
    (hN : 100 ≤ Real.log N)
    (hm : |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log N)))
    (ht : |t| ≤ K_w * ((Real.log N) ^ (4 : ℕ) + 1)) :
    Real.log N + Real.log (|(m : ℝ)| + |t| + 3) + 2
      ≤ (6 + (4 + Real.log (2 * K_w + 3)) / 100) * Real.log N := by
  have hLpos : 0 < Real.log N := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log N := by linarith
  -- `√log N ≤ log N`
  have hsqrt_le : Real.sqrt (Real.log N) ≤ Real.log N := by
    have h := Real.sq_sqrt hLpos.le
    have h0 : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
    nlinarith [h, hL1]
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.sqrt (Real.log N)) :=
    Real.one_le_exp (Real.sqrt_nonneg _)
  have hexpmono : Real.exp (Real.sqrt (Real.log N)) ≤ Real.exp (Real.log N) :=
    Real.exp_le_exp.mpr hsqrt_le
  -- `|m| + 3 ≤ 7 exp(√log N) ≤ 7 exp(log N)`
  have hA_le : |(m : ℝ)| + 3 ≤ 7 * Real.exp (Real.log N) := by
    nlinarith [hm, hexp1, hexpmono]
  have hlogA : Real.log (|(m : ℝ)| + 3) ≤ 2 + Real.log N := by
    have hpos : 0 < |(m : ℝ)| + 3 := by positivity
    have h1 := Real.log_le_log hpos hA_le
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at h1
    have h7 : Real.log 7 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 7)]
      have h : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have he : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [he]
      nlinarith [h, Real.exp_pos 1]
    linarith
  -- `|t| + 3 ≤ (2 K_w + 3)(log N)^4`
  have hL4 : (1 : ℝ) ≤ (Real.log N) ^ (4 : ℕ) := one_le_pow₀ hL1
  have hB_le : |t| + 3 ≤ (2 * K_w + 3) * (Real.log N) ^ (4 : ℕ) := by
    nlinarith [ht, hL4, hKw, abs_nonneg t]
  have h2K : 0 < 2 * K_w + 3 := by linarith
  have hlogB : Real.log (|t| + 3) ≤ Real.log (2 * K_w + 3) + 4 * Real.log N := by
    have hpos : 0 < |t| + 3 := by positivity
    have h1 := Real.log_le_log hpos hB_le
    rw [Real.log_mul (ne_of_gt h2K) (pow_ne_zero 4 (ne_of_gt hLpos)), Real.log_pow] at h1
    have hloglog : Real.log (Real.log N) ≤ Real.log N := by
      have := Real.log_le_sub_one_of_pos hLpos
      linarith
    push_cast at h1
    linarith
  -- split the log of the sum
  have hsplit : Real.log (|(m : ℝ)| + |t| + 3)
      ≤ Real.log (|(m : ℝ)| + 3) + Real.log (|t| + 3) := by
    have hA1 : (1 : ℝ) ≤ |(m : ℝ)| + 3 := by have := abs_nonneg (m : ℝ); linarith
    have hB1 : (1 : ℝ) ≤ |t| + 3 := by have := abs_nonneg t; linarith
    have hle : |(m : ℝ)| + |t| + 3 ≤ (|(m : ℝ)| + 3) * (|t| + 3) := by
      nlinarith [abs_nonneg (m : ℝ), abs_nonneg t]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < |(m : ℝ)| + |t| + 3) hle
    rw [Real.log_mul (ne_of_gt (by linarith : (0 : ℝ) < |(m : ℝ)| + 3))
      (ne_of_gt (by linarith : (0 : ℝ) < |t| + 3))] at h
    exact h
  have hfinal : Real.log N + Real.log (|(m : ℝ)| + |t| + 3) + 2
      ≤ 6 * Real.log N + (4 + Real.log (2 * K_w + 3)) := by
    linarith [hsplit, hlogA, hlogB]
  have hc0nn : 0 ≤ 4 + Real.log (2 * K_w + 3) := by
    have : 0 ≤ Real.log (2 * K_w + 3) := Real.log_nonneg (by linarith)
    linarith
  have hc0 : 4 + Real.log (2 * K_w + 3)
      ≤ (4 + Real.log (2 * K_w + 3)) / 100 * Real.log N := by
    nlinarith [hc0nn, hN]
  calc Real.log N + Real.log (|(m : ℝ)| + |t| + 3) + 2
      ≤ 6 * Real.log N + (4 + Real.log (2 * K_w + 3)) := hfinal
    _ ≤ 6 * Real.log N + (4 + Real.log (2 * K_w + 3)) / 100 * Real.log N := by linarith [hc0]
    _ = (6 + (4 + Real.log (2 * K_w + 3)) / 100) * Real.log N := by ring

/-- `L(m,s) := log N + log(|m| + |Im s| + 3) + 2` is nonnegative (local copy of the sibling's
lemma, kept here so that this file depends only on `HeartZcDefs`). -/
lemma heart_L_nonneg' (Pa : Work.FITop.Params) (m : ℤ) (s : ℂ) :
    0 ≤ Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 := by
  have h1 : (0 : ℝ) ≤ Real.log (Pa.N) := Real.log_nonneg Pa.hN1
  have h2 : (0 : ℝ) ≤ Real.log (|(m : ℝ)| + |s.im| + 3) :=
    Real.log_nonneg (by
      have ha := abs_nonneg (m : ℝ)
      have hb := abs_nonneg s.im
      linarith)
  linarith

theorem HeartZcCzOfWitness (K_w : ℝ) (hKw : 0 < K_w) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (ε c_h C_z : ℝ)
        (Zc : ℂ → ℂ),
        1 ≤ d → 4 ≤ Real.log (Pa.Pz : ℝ) → 100 ≤ Real.log Pa.N →
        |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N)) →
        (∃ s : ℂ, 1 < s.re ∧ s.re ≤ 1 + 1 / Real.log Pa.N ∧ s.re ≤ 2 ∧
          |s.im| ≤ K_w * ((Real.log Pa.N) ^ (4 : ℕ) + 1) ∧
          (1 : ℝ) / 2 ≤ ‖Work.FIArea6.TauPieces.Zsfun Pa chi m s‖) →
        Work.FIArea6Road.heartZcHyp Pa chi m d ε c_h C_z Zc →
        (1 : ℝ) / (K * (d : ℝ) * (Real.log Pa.N) ^ (6 : ℕ)) ≤ C_z := by
  set cc : ℝ := 6 + (4 + Real.log (2 * K_w + 3)) / 100 with hcc
  have hccpos : 0 < cc := by
    rw [hcc]
    have hlog : 0 ≤ Real.log (2 * K_w + 3) := Real.log_nonneg (by linarith)
    linarith
  refine ⟨2 * cc ^ (6 : ℕ), by positivity, ?_⟩
  intro Pa chi m d ε c_h C_z Zc hd hlogPz hlogN hm hs hzc
  obtain ⟨s, hs1, hs2, hs3, hsim, hval⟩ := hs
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd)
  have hLpos : 0 < Real.log Pa.N := by linarith
  have hLnn : 0 ≤ Real.log Pa.N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 :=
    heart_L_nonneg' Pa m s
  -- the elementary log bound, with the definition of `cc` unfolded
  have hLle : Real.log Pa.N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2
      ≤ cc * Real.log Pa.N := by
    rw [hcc]
    exact heart_log_L_le K_w hKw Pa.N m s.im hlogN hm hsim
  have hpow : (Real.log Pa.N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ)
      ≤ (cc * Real.log Pa.N) ^ (6 : ℕ) := pow_le_pow_left₀ hLnn hLle 6
  -- `heartZcHyp`'s strip clause at the witness point
  have hb : ‖Zc s‖ ≤ C_z * (d : ℝ)
      * (Real.log Pa.N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ) :=
    hzc.2.2.2.2 s hs1 hs2 hs3
  have heq : Zc s = Work.FIArea6.TauPieces.Zsfun Pa chi m s := hzc.2.1 s hs1
  have h1 : (1 : ℝ) / 2 ≤ C_z * (d : ℝ) * (cc * Real.log Pa.N) ^ (6 : ℕ) := by
    have h2 : (1 : ℝ) / 2 ≤ ‖Zc s‖ := by rw [heq]; exact hval
    refine h2.trans (hb.trans ?_)
    exact mul_le_mul_of_nonneg_left hpow (le_of_lt (mul_pos hzc.1 hdpos))
  rw [mul_pow] at h1
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * cc ^ (6 : ℕ) * (d : ℝ)
    * (Real.log Pa.N) ^ (6 : ℕ))]
  nlinarith [h1]

end Work.FIArea6Road
