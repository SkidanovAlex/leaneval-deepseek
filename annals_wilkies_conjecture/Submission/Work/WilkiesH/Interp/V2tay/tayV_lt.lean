import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

namespace Work.WilkiesH.Interp.V2tay

/-- A purely numerical core: given the sufficient inequality `hA` relating the flatness order `b`
to the other parameters, the exponential Taylor bound is strictly smaller than a quarter of the
Liouville bound.  Written for variables so that only the two definitions `N1V`, `dV` (via their
values) have to be reconciled at the call site. -/
private lemma key_ineq (μ b d N1 Q K g H : ℕ)
    (hK : 1 < K) (hN1 : 1 ≤ N1) (hQ : 1 ≤ Q) (hH : 1 ≤ H)
    (hA : (b:ℝ) * Real.log (K:ℝ) >
      Real.log 4 + (1/2) * Real.log (N1:ℝ) + (Real.sqrt (μ:ℝ))^3 * (d:ℝ) +
        (g:ℝ) * Real.log ((N1:ℝ)*(Q:ℝ)) + ((μ:ℝ)+2) * (d:ℝ) * (g:ℝ)^2 * Real.log (H:ℝ)) :
    Real.sqrt (N1:ℝ) * (1/(K:ℝ))^b * Real.exp ((Real.sqrt (μ:ℝ))^3 * (d:ℝ)) <
      (1 / ((N1:ℝ)*(Q:ℝ)*((H:ℝ)^(((μ+1)+1)*d*g))))^g / 4 := by
  have hN1R : (0:ℝ) < (N1:ℝ) := by exact_mod_cast (show 0 < N1 by omega)
  have hQR : (0:ℝ) < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hK1 : (1:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  set x := (Real.sqrt (μ:ℝ))^3 * (d:ℝ) with hx
  set M := (N1:ℝ)*(Q:ℝ)*((H:ℝ)^(((μ+1)+1)*d*g)) with hM
  set T := Real.sqrt (N1:ℝ) * (1/(K:ℝ))^b * Real.exp x with hT
  have hMpos : 0 < M := by rw [hM]; positivity
  have hTpos : 0 < T := by rw [hT]; positivity
  have hlogT : Real.log T = (1/2)*Real.log (N1:ℝ) - (b:ℝ)*Real.log (K:ℝ) + x := by
    rw [hT]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.sqrt_eq_rpow, Real.log_rpow hN1R]
    rw [Real.log_pow, Real.log_div (by norm_num) (by positivity), Real.log_one]
    rw [Real.log_exp]
    ring
  have hlogM : Real.log M = Real.log (N1:ℝ) + Real.log (Q:ℝ)
      + (((μ+1)+1)*d*g : ℕ) * Real.log (H:ℝ) := by
    rw [hM]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
  have hlog : Real.log (4 * T * M^g) =
      Real.log 4 + (1/2)*Real.log (N1:ℝ) - (b:ℝ)*Real.log (K:ℝ) + x
        + (g:ℝ)*(Real.log (N1:ℝ) + Real.log (Q:ℝ))
        + ((μ:ℝ)+2)*(d:ℝ)*(g:ℝ)^2*Real.log (H:ℝ) := by
    rw [show (4:ℝ)*T*M^g = 4 * (T * M^g) by ring]
    rw [Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [hlogT, Real.log_pow, hlogM]
    push_cast
    ring
  have hA' : (b:ℝ) * Real.log (K:ℝ) >
      Real.log 4 + (1/2) * Real.log (N1:ℝ) + x +
        (g:ℝ) * (Real.log (N1:ℝ) + Real.log (Q:ℝ)) +
        ((μ:ℝ)+2) * (d:ℝ) * (g:ℝ)^2 * Real.log (H:ℝ) := by
    have h := hA
    rw [Real.log_mul (by positivity) (by positivity)] at h
    linarith [h]
  have hE : Real.log 4 + (1/2)*Real.log (N1:ℝ) - (b:ℝ)*Real.log (K:ℝ) + x
        + (g:ℝ)*(Real.log (N1:ℝ) + Real.log (Q:ℝ))
        + ((μ:ℝ)+2)*(d:ℝ)*(g:ℝ)^2*Real.log (H:ℝ) < 0 := by
    linarith [hA']
  have hp : (0:ℝ) < 4 * T * M^g := by positivity
  have h4T : 4 * T * M^g < 1 := by
    have hlt : Real.log (4 * T * M^g) < Real.log 1 := by rw [hlog, Real.log_one]; linarith
    exact (Real.log_lt_log_iff hp (by norm_num)).mp hlt
  have hfin : T < 1/(4*M^g) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [h4T]
  have heq : (1/M)^g/4 = 1/(4*M^g) := by
    rw [one_div_pow, div_div]; congr 1; ring
  rw [heq]
  exact hfin

-- The first (Taylor) term of `above` is `< liou/4`, assuming the sufficient inequality `hA`.
-- Ingredients: `∑_{j≤b} (√μ)^{3j} d^j / j! ≤ exp ((√μ)^3 d)` (`Real.sum_le_exp_of_nonneg`),
-- `rhoV μ = 1/KK μ` with `KK μ = 2μ+4` a natural, and `liou μ d Q g H = ((N1·Q)·H^((μ+2)dg))^(-g)`.
theorem tayV_lt (μ g H : ℕ) (hH : 1 ≤ H)
    (hA : ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) * Real.log ((Work.WilkiesH.Interp.KK μ : ℕ) : ℝ) >
      Real.log 4 + (1 / 2) * Real.log ((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) +
        (Real.sqrt (μ : ℝ)) ^ 3 * ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) +
        (g : ℝ) * Real.log (((Work.WilkiesH.Interp.N1V μ g H : ℕ) : ℝ) *
          ((Work.WilkiesH.Interp.QV μ g H : ℕ) : ℝ)) +
        ((μ : ℝ) + 2) * ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) *
          (g : ℝ) ^ 2 * Real.log (H : ℝ)) :
    Work.WilkiesH.Interp.tayV μ g H <
      Work.WilkiesH.Interp.liou μ (Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H))
        (Work.WilkiesH.Interp.QV μ g H) g H / 4 := by
  -- a local name for the sum appearing in `tayV`
  have hsum : (∑ j ∈ Finset.range (Work.WilkiesH.Interp.bV μ g H + 1),
      ((Real.sqrt (μ:ℝ))^(3*j) *
        ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ)^j)
          / (((j.factorial:ℕ):ℝ)))
      ≤ Real.exp ((Real.sqrt (μ:ℝ))^3 *
        ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ)) := by
    have hx0 : 0 ≤ (Real.sqrt (μ:ℝ))^3 *
        ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ) :=
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
        (Nat.cast_nonneg (Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H)))
    have h := Real.sum_le_exp_of_nonneg hx0 (Work.WilkiesH.Interp.bV μ g H + 1)
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro j hj
    have hp : ((Real.sqrt (μ:ℝ))^3 *
        ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ))^j
        = (Real.sqrt (μ:ℝ))^(3*j) *
          ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ)^j := by
      rw [mul_pow, pow_mul]
    rw [hp]
  unfold Work.WilkiesH.Interp.tayV
  rw [Work.WilkiesH.Interp.rhoV_eq]
  have hK0 : 0 ≤ (1/(Work.WilkiesH.Interp.KK μ : ℝ)) := by
    rw [one_div]; exact inv_nonneg.mpr (Nat.cast_nonneg (Work.WilkiesH.Interp.KK μ))
  have hA0 : 0 ≤ Real.sqrt (Work.WilkiesH.Interp.N1V μ g H : ℝ) *
      (1/(Work.WilkiesH.Interp.KK μ : ℝ))^(Work.WilkiesH.Interp.bV μ g H) :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hK0 _)
  calc Real.sqrt (Work.WilkiesH.Interp.N1V μ g H : ℝ) *
        (1/(Work.WilkiesH.Interp.KK μ : ℝ))^(Work.WilkiesH.Interp.bV μ g H)
        * (∑ j ∈ Finset.range (Work.WilkiesH.Interp.bV μ g H + 1),
            ((Real.sqrt (μ:ℝ))^(3*j) *
              ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ)^j)
                / (((j.factorial:ℕ):ℝ)))
      ≤ Real.sqrt (Work.WilkiesH.Interp.N1V μ g H : ℝ) *
        (1/(Work.WilkiesH.Interp.KK μ : ℝ))^(Work.WilkiesH.Interp.bV μ g H)
        * Real.exp ((Real.sqrt (μ:ℝ))^3 *
            ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H):ℕ):ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsum hA0
    _ < Work.WilkiesH.Interp.liou μ
          (Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H))
          (Work.WilkiesH.Interp.QV μ g H) g H / 4 := by
        rw [Work.WilkiesH.Interp.liou, ← one_div_pow]
        exact key_ineq μ (Work.WilkiesH.Interp.bV μ g H)
          (Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H))
          (Work.WilkiesH.Interp.N1V μ g H) (Work.WilkiesH.Interp.QV μ g H)
          (Work.WilkiesH.Interp.KK μ) g H
          (Work.WilkiesH.Interp.one_lt_KK μ) (Work.WilkiesH.Interp.one_le_N1V μ g H)
          (Work.WilkiesH.Interp.one_le_QV μ g H) hH hA

end Work.WilkiesH.Interp.V2tay
