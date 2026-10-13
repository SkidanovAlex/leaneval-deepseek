import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Interp.V2rem

/-- For `d + 1 ≤ b`, `(d+1)^(b-d-1) ≤ (b+1)!`.  This is the elementary factorial
estimate underlying the Taylor remainder bound: `(b+1)! ≥ (d+2)^(b-d-1)`. -/
lemma pow_sub_le_factorial (b d : ℕ) (h : d + 1 ≤ b) :
    ((d : ℝ) + 1) ^ (b - d - 1) ≤ (((b + 1).factorial : ℕ) : ℝ) := by
  have h1 : b + 1 - (d + 1) = b - d := by omega
  have hfac := Nat.factorial_mul_pow_sub_le_factorial (n := d + 1) (m := b + 1) (by omega)
  rw [h1] at hfac
  have h2 : (d + 1) ^ (b - d - 1) ≤ (d + 1) ^ (b - d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (d + 1) ^ (b - d) ≤ (d + 1).factorial * (d + 1) ^ (b - d) :=
    Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  have h4 := le_trans h2 (le_trans h3 hfac)
  have hcast : ((d : ℝ) + 1) ^ (b - d - 1) = ((d + 1 : ℕ) : ℝ) ^ (b - d - 1) := by
    push_cast; ring
  rw [hcast]
  exact_mod_cast h4

/-- Logarithmic form of `pow_sub_le_factorial`. -/
lemma sub_mul_log_le_log_factorial (b d : ℕ) (h : d + 1 ≤ b) :
    ((b : ℝ) - (d : ℝ) - 1) * Real.log ((d : ℝ) + 1) ≤
      Real.log ((((b + 1).factorial : ℕ) : ℝ)) := by
  have hcast : ((b : ℝ) - (d : ℝ) - 1) = ((b - d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (show 1 ≤ b - d by omega), Nat.cast_sub (show d ≤ b by omega)]
    norm_num
  rw [hcast, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (pow_sub_le_factorial b d h)

/-- The numerical core: from the hypothesis `hB` (the master inequality in logarithmic form)
and `d + 1 ≤ b`, the Taylor remainder `N1·Q·(d+1)^(b+1)·(√μ·K⁻¹)^(b+1)/(b+1)!` is strictly
smaller than the Liouville bound `1/((N1·Q·H^((μ+2)dg))^g)/4`. -/
lemma rem_aux (b d g μ : ℕ) (N1 Q K H : ℝ)
    (hdb : d + 1 ≤ b) (hN1 : 0 < N1) (hQ : 0 < Q) (hK : 1 < K) (hH : 0 < H)
    (hB : ((b : ℝ) + 1) * (Real.log K - (1 / 2) * Real.log μ) >
      Real.log 4 + Real.log (N1 * Q) + ((d : ℝ) + 2) * Real.log ((d : ℝ) + 1) +
        (g : ℝ) * Real.log (N1 * Q) +
        ((μ : ℝ) + 2) * (d : ℝ) * (g : ℝ) ^ 2 * Real.log H) :
    N1 * Q * ((d : ℝ) + 1) ^ (b + 1) * (Real.sqrt μ * K⁻¹) ^ (b + 1) /
        (((b + 1).factorial : ℕ) : ℝ) <
      1 / ((N1 * Q * H ^ (((μ + 1) + 1) * d * g)) ^ g) / 4 := by
  rw [mul_sub] at hB
  set s : ℕ := ((μ + 1) + 1) * d * g with hs
  have hFpos : 0 < (((b + 1).factorial : ℕ) : ℝ) := by positivity
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  -- Step 1: the two products satisfy `L < M`.
  have hLM : 4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) * (Real.sqrt μ) ^ (b + 1) *
        H ^ (s * g) < (((b + 1).factorial : ℕ) : ℝ) * K ^ (b + 1) := by
    rcases Nat.eq_zero_or_pos μ with hμ0 | hμ1
    · subst hμ0
      have hz : (Real.sqrt ((0 : ℕ) : ℝ)) ^ (b + 1) = 0 := by
        simp only [Nat.cast_zero, Real.sqrt_zero, zero_pow (by omega : b + 1 ≠ 0)]
      rw [hz]
      simp only [mul_zero, zero_mul]
      exact mul_pos hFpos (by positivity)
    · have hμpos : 0 < (μ : ℝ) := by exact_mod_cast hμ1
      have hx : 0 < 4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) *
          (Real.sqrt μ) ^ (b + 1) * H ^ (s * g) := by positivity
      have hy : 0 < (((b + 1).factorial : ℕ) : ℝ) * K ^ (b + 1) :=
        mul_pos hFpos (by positivity)
      exact (Real.log_lt_log_iff hx hy).mp (by
        have hlogL : Real.log (4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) *
              (Real.sqrt μ) ^ (b + 1) * H ^ (s * g))
            = Real.log 4 + Real.log (N1 * Q) + (g : ℝ) * Real.log (N1 * Q) +
              ((b : ℝ) + 1) * Real.log ((d : ℝ) + 1) +
              ((b : ℝ) + 1) * Real.log (Real.sqrt μ) +
              ((s * g : ℕ) : ℝ) * Real.log H := by
          rw [Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul]
          · simp only [Real.log_pow]
            push_cast
            ring
          all_goals positivity
        have hlogM : Real.log ((((b + 1).factorial : ℕ) : ℝ) * K ^ (b + 1))
            = Real.log ((((b + 1).factorial : ℕ) : ℝ)) + ((b : ℝ) + 1) * Real.log K := by
          rw [Real.log_mul]
          · simp only [Real.log_pow]
            push_cast
            ring
          all_goals positivity
        rw [hlogL, hlogM]
        have hsqrt : Real.log (Real.sqrt μ) = (1 / 2) * Real.log μ := by
          rw [Real.log_sqrt (le_of_lt hμpos)]; ring
        rw [hsqrt]
        have hsg : ((s * g : ℕ) : ℝ) = ((μ : ℝ) + 2) * (d : ℝ) * (g : ℝ) ^ 2 := by
          rw [hs]
          push_cast; ring
        rw [hsg]
        have hfact : ((b : ℝ) + 1) * Real.log ((d : ℝ) + 1) ≤
            ((d : ℝ) + 2) * Real.log ((d : ℝ) + 1) +
              Real.log ((((b + 1).factorial : ℕ) : ℝ)) := by
          have h := sub_mul_log_le_log_factorial b d hdb
          have heq2 : ((b : ℝ) - (d : ℝ) - 1) = ((b : ℝ) + 1) - ((d : ℝ) + 2) := by ring
          rw [heq2] at h
          have heq : ((b : ℝ) + 1) * Real.log ((d : ℝ) + 1) =
              (((b : ℝ) + 1) - ((d : ℝ) + 2)) * Real.log ((d : ℝ) + 1) +
                ((d : ℝ) + 2) * Real.log ((d : ℝ) + 1) := by ring
          rw [heq]
          linarith [h]
        linarith [hB, hfact])
  -- Step 2: divide `L < M` by `K^(b+1)` to obtain the core product inequality.
  have hcore : 4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) *
      (Real.sqrt μ * K⁻¹) ^ (b + 1) * H ^ (s * g) < (((b + 1).factorial : ℕ) : ℝ) := by
    have hkinv : 0 < (K⁻¹) ^ (b + 1) := by positivity
    have h2 := mul_lt_mul_of_pos_right hLM hkinv
    have h3 : ((((b + 1).factorial : ℕ) : ℝ) * K ^ (b + 1)) * (K⁻¹) ^ (b + 1) =
        (((b + 1).factorial : ℕ) : ℝ) := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hKpos), one_pow, mul_one]
    rw [h3] at h2
    have heq : 4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) *
          (Real.sqrt μ * K⁻¹) ^ (b + 1) * H ^ (s * g)
        = (4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) * (Real.sqrt μ) ^ (b + 1) *
            H ^ (s * g)) * (K⁻¹) ^ (b + 1) := by
      rw [mul_pow (Real.sqrt μ) K⁻¹ (b + 1)]
      ring
    rw [heq]
    exact h2
  -- Step 3: translate the core product inequality into the goal.
  rw [lt_div_iff₀ (show (0 : ℝ) < 4 by norm_num)]
  rw [lt_div_iff₀ (show (0 : ℝ) < (N1 * Q * H ^ s) ^ g by positivity)]
  rw [show (N1 * Q * ((d : ℝ) + 1) ^ (b + 1) * (Real.sqrt μ * K⁻¹) ^ (b + 1) /
            (((b + 1).factorial : ℕ) : ℝ)) * 4 * ((N1 * Q * H ^ s) ^ g)
        = (4 * (N1 * Q) ^ (g + 1) * ((d : ℝ) + 1) ^ (b + 1) *
            (Real.sqrt μ * K⁻¹) ^ (b + 1) * H ^ (s * g)) /
            (((b + 1).factorial : ℕ) : ℝ) from by
      rw [mul_pow (N1 * Q) (H ^ s) g, mul_pow (Real.sqrt μ) K⁻¹ (b + 1),
          ← pow_mul H s g, pow_succ (N1 * Q) g]
      ring]
  rw [div_lt_one hFpos]
  exact hcore

-- The second (Taylor remainder) term of `above` is `< liou/4`, assuming `hB`.
-- Ingredients: `Nat.factorial_mul_pow_sub_le_factorial` gives `(b+1)! ≥ (d+2)^(b-d-1)`
-- (using `d + 1 ≤ b`), and `rhoV μ = 1/KK μ`, `KK μ = 2μ+4`.
theorem remV_lt (μ g H : ℕ) (hH : 1 ≤ H)
    (hdb : Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) + 1 ≤ Work.WilkiesH.Interp.bV μ g H)
    (hB : (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 1) *
        (Real.log ((Work.WilkiesH.Interp.KK μ : ℕ) : ℝ) - (1 / 2) * Real.log (μ : ℝ)) >
      Real.log 4 + Real.log (((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) *
          ((Work.WilkiesH.Interp.QV μ g H : ℕ) : ℝ)) +
        (((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 2) *
          (Real.log (((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) + 1)) +
        (g : ℝ) * Real.log (((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) *
          ((Work.WilkiesH.Interp.QV μ g H : ℕ) : ℝ)) +
        ((μ : ℝ) + 2) * ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) *
          (g : ℝ) ^ 2 * Real.log (H : ℝ)) :
    Work.WilkiesH.Interp.remV μ g H <
      Work.WilkiesH.Interp.liou μ (Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H))
        (Work.WilkiesH.Interp.QV μ g H) g H / 4 := by
  have hN1 : (0 : ℝ) < ((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) := by
    have := Work.WilkiesH.Interp.one_le_N1V μ g H
    exact_mod_cast this
  have hQ : (0 : ℝ) < ((Work.WilkiesH.Interp.QV μ g H : ℕ) : ℝ) := by
    have := Work.WilkiesH.Interp.one_le_QV μ g H
    exact_mod_cast this
  have hK : (1 : ℝ) < ((Work.WilkiesH.Interp.KK μ : ℕ) : ℝ) := by
    have := Work.WilkiesH.Interp.one_lt_KK μ
    exact_mod_cast this
  have hH' : (0 : ℝ) < (H : ℝ) := by
    have := hH
    exact_mod_cast this
  have key := rem_aux (Work.WilkiesH.Interp.bV μ g H)
      (Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H)) g μ
      (((Work.WilkiesH.Interp.N1V μ g H : ℕ)) : ℝ)
      (((Work.WilkiesH.Interp.QV μ g H : ℕ)) : ℝ)
      (((Work.WilkiesH.Interp.KK μ : ℕ)) : ℝ) (H : ℝ)
      hdb hN1 hQ hK hH' hB
  simpa only [Work.WilkiesH.Interp.remV, Work.WilkiesH.Interp.liou,
    Work.WilkiesH.Interp.rhoV, Work.WilkiesH.Interp.N1V] using key

end Work.WilkiesH.Interp.V2rem
