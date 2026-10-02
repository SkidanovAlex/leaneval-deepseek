/-
# ZeroFreeTables/P9/prim/masterP3_assembly

The single-point `P₃` master bound of HB §9, assembled from the prim-stack pieces:
`SigmaP3L_le_nearP3sum_add` (zero-sum substitution), `invNearSum_eq_tsum` + `LogDerivHyp`
(the `(L'/L)` slot), `paritySum_re_bound` (`T₂, T₃`), `invSqSum_uniform_le` (far zeros),
and `P3NearSumL_eq_nearP3sum` (bridge back).

The bound `M` on `λ₁` is taken before `L₀`: the errors are `O((a+λ₁)²/L)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum
import Submission.Work.ZeroFreeTables.P9.prim.masterP3_zero
import Submission.Work.ZeroFreeTables.P9.prim.parityBound
import Submission.Work.ZeroFreeTables.P9.prim.invSqSum_bound

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P9.prim

open Work.ZeroFreeTables

/-- The elementary error bookkeeping of `masterP3`: given the far-zero bound
`J ≤ C(L+2)`, the parity bounds `-T_j ≤ Ct` and the threshold condition
`K ≤ A·e·L`, the accumulated error is at most `A·e`. -/
private lemma error_bound {A Amax k2 k3 C Ct J T2r T3r L e : ℝ}
    (hA : 0 ≤ A) (hAle : A ≤ Amax) (hAmax : 0 ≤ Amax) (hk2 : 0 ≤ k2) (hk3 : 0 ≤ k3)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) (hJ : J ≤ C * (L + 2)) (hT2 : -T2r ≤ Ct) (hT3 : -T3r ≤ Ct)
    (hL2 : 2 ≤ L) (hLpos : 0 < L) (hae : 0 < A * e)
    (hK : 2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct) ≤ A * e * L) :
    (A / L) ^ 2 * (k2 * J - T2r) + (2 / 3) * (A / L) ^ 3 * (k3 * J - T3r) ≤ A * e := by
  have hB2 : k2 * J + Ct ≤ (k2 * C + Ct) * (L + 2) := by
    have h1 : k2 * J ≤ k2 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk2
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith)
    have heq : (k2 * C + Ct) * (L + 2) = k2 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith [h1, h2, heq.le, heq.ge]
  have hB3 : k3 * J + Ct ≤ (k3 * C + Ct) * (L + 2) := by
    have h1 : k3 * J ≤ k3 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk3
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith)
    have heq : (k3 * C + Ct) * (L + 2) = k3 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith [h1, h2, heq.le, heq.ge]
  have hin2 : k2 * J - T2r ≤ (k2 * C + Ct) * (L + 2) := by linarith [hB2, hT2]
  have hin3 : k3 * J - T3r ≤ (k3 * C + Ct) * (L + 2) := by linarith [hB3, hT3]
  have hC2nn : 0 ≤ k2 * C + Ct := by positivity
  have hC3nn : 0 ≤ k3 * C + Ct := by positivity
  have hC2L2nn : 0 ≤ (k2 * C + Ct) * (L + 2) := mul_nonneg hC2nn (by linarith)
  have hC3L2nn : 0 ≤ (k3 * C + Ct) * (L + 2) := mul_nonneg hC3nn (by linarith)
  have hnum : A ^ 2 ≤ Amax ^ 2 := pow_le_pow_left₀ hA hAle 2
  have hnum3 : A ^ 3 ≤ Amax ^ 3 := pow_le_pow_left₀ hA hAle 3
  have hA2eq : (A / L) ^ 2 = A ^ 2 / L ^ 2 := by rw [div_pow]
  have hA3eq : (A / L) ^ 3 = A ^ 3 / L ^ 3 := by rw [div_pow]
  have hL2' : (L + 2) / L ^ 2 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 2) hLpos]
    linarith only [mul_nonneg hLpos.le (sub_nonneg.2 hL2)]
  have hL3' : (L + 2) / L ^ 3 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 3) hLpos]
    linarith only [mul_nonneg (mul_nonneg hLpos.le hLpos.le) (sub_nonneg.2 hL2),
      mul_nonneg hLpos.le (sub_nonneg.2 hL2), hLpos]
  have herr2 : (A / L) ^ 2 * (k2 * J - T2r) ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) := by
    rw [hA2eq]
    calc A ^ 2 / L ^ 2 * (k2 * J - T2r)
        ≤ A ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hin2 (by positivity)
      _ ≤ Amax ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hC2L2nn
          exact div_le_div_of_nonneg_right hnum (pow_pos hLpos 2).le
      _ = Amax ^ 2 * (k2 * C + Ct) * ((L + 2) / L ^ 2) := by ring
      _ ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL2' (mul_nonneg (pow_nonneg hAmax 2) hC2nn)
  have herr3 : (2 / 3) * (A / L) ^ 3 * (k3 * J - T3r)
      ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) := by
    rw [hA3eq]
    calc (2 / 3) * (A ^ 3 / L ^ 3) * (k3 * J - T3r)
        ≤ (2 / 3) * (A ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hin3 (by positivity)
      _ ≤ (2 / 3) * (Amax ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hC3L2nn
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum3 (pow_pos hLpos 3).le) (by norm_num)
      _ = (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * ((L + 2) / L ^ 3) := by ring
      _ ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL3' (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hAmax 3)) hC3nn)
  have hsum : Amax ^ 2 * (k2 * C + Ct) * (2 / L) + (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L)
      = (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L := by ring
  have hKL : (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L ≤ A * e := by
    rw [div_le_iff₀ hLpos]; linarith [hK]
  linarith only [herr2, herr3, hsum, hKL]

set_option maxHeartbeats 1000000 in
theorem masterP3 {a δ c e : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (he : 0 < e) :
    ∀ M : ℝ, ∃ L₀ : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {L lam₁ : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → 0 ≤ lam₁ →
      lam₁ ≤ M → Work.ZeroFreeTables.LogDerivHyp χ δ L c →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL N L χ s a lam₁ δ + (a + lam₁) * (c + e) := by
  intro M
  obtain ⟨C, hCpos, hC⟩ := invSqSum_uniform_le
  obtain ⟨Ct, hCtpos, hCt⟩ := paritySum_re_bound
  have hC2pos : 0 < (1 + 4 / δ ^ 2) * C + Ct := by
    have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
    positivity
  have hC3pos : 0 < (2 / δ) * (1 + 4 / δ ^ 2) * C + Ct := by
    have h1 : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by
      have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
      linarith
    have : 0 < (2 / δ) := by positivity
    positivity
  set K : ℝ := 2 * (a + M) ^ 2 * ((1 + 4 / δ ^ 2) * C + Ct)
    + (4 / 3) * (a + M) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2) * C + Ct) with hKdef
  refine ⟨max 4 (max (a + 2) (max (2 * a / δ)
    (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))))), ?_⟩
  intro N _ χ hχ hprim L lam₁ hL hlogN hlam₁ hM hyp s hsre hsim
  have hX : max (a + 2) (max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e)))) ≤ L :=
    le_trans (le_max_right 4 _) hL
  have hY : max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))) ≤ L :=
    le_trans (le_max_right (a + 2) _) hX
  have hZ : max (Real.exp (max a a⁻¹) + 4) (K / (a * e)) ≤ L :=
    le_trans (le_max_right (2 * a / δ) _) hY
  have hLge4 : 4 ≤ L := le_trans (le_max_left 4 _) hL
  have hLge2 : 2 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLge1 : 1 ≤ L := by linarith
  have ha2 : a + 2 ≤ L := le_trans (le_max_left (a + 2) _) hX
  have haL : a ≤ L := by linarith
  have h2aδ : 2 * a ≤ δ * L := by
    have h := le_trans (le_max_left (2 * a / δ) _) hY
    rw [div_le_iff₀ hδ0] at h
    linarith
  have hlogL_ge : max a a⁻¹ ≤ Real.log L := by
    have hexp : Real.exp (max a a⁻¹) ≤ L := by linarith [le_trans (le_max_left _ _) hZ]
    have h := Real.log_le_log (Real.exp_pos (max a a⁻¹)) hexp
    rwa [Real.log_exp] at h
  have hmpos : 0 < max a a⁻¹ := lt_of_lt_of_le ha (le_max_left a a⁻¹)
  have hlogL_pos : 0 < Real.log L := lt_of_lt_of_le hmpos hlogL_ge
  have hKe : K ≤ a * e * L := by
    have h := le_trans (le_max_right _ _) hZ
    rw [div_le_iff₀ (mul_pos ha he)] at h
    linarith
  -- facts at `s`
  have hsre_gt : 1 < s.re := by rw [hsre]; linarith [div_pos ha hLpos]
  have hsδ : s.re ≤ 1 + δ / 2 := by
    rw [hsre]
    have h : a / L ≤ δ / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  have hα : 0 ≤ a + lam₁ := by linarith
  obtain ⟨par, hpar0, hpar1⟩ : ∃ par : ℕ, (χ.Even → par = 0) ∧ (χ.Odd → par = 1) := by
    rcases χ.even_or_odd with hE | hO
    · exact ⟨0, fun _ => rfl, fun hO => absurd hO hE.not_odd⟩
    · exact ⟨1, fun hE => absurd hE hO.not_even, fun _ => rfl⟩
  have hpar_le : par ≤ 1 := by
    rcases χ.even_or_odd with hE | hO
    · rw [hpar0 hE]; exact zero_le_one
    · rw [hpar1 hO]
  obtain ⟨hsum2, _⟩ := Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 1 (by norm_num) par hpar0 hpar1 hsre_gt
  obtain ⟨hsum3, _⟩ := Work.ZeroFreeTables.P9.lDiffExplicit_gen χ hχ hprim 2 (by norm_num) par hpar0 hpar1 hsre_gt
  have hmain := SigmaP3L_le_nearP3sum_add χ hχ hprim hα hLpos hδ0 hδ1 hsre_gt hsδ par hpar0 hpar1 hsum2 hsum3
  -- the `(L'/L)` slot
  have hbridge := Work.ZeroFreeTables.P9.invNearSum_eq_tsum χ hχ hprim (by linarith [hsim] : |s.im| ≤ 10) hδ0 (le_of_lt hδ1)
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have h1 : 1 ≤ a * Real.log L := by
      have h := mul_le_mul_of_nonneg_left (le_trans (le_max_right a a⁻¹) hlogL_ge) (le_of_lt ha)
      rwa [mul_inv_cancel₀ (ne_of_gt ha)] at h
    have : 1 / (L * Real.log L) ≤ a / L := by
      rw [div_le_div_iff₀ (by positivity : 0 < L * Real.log L) hLpos]
      linarith only [mul_le_mul_of_nonneg_left h1 hLpos.le]
    linarith only [this]
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h2 : a ≤ Real.log L := le_trans (le_max_left a a⁻¹) hlogL_ge
    have : a / L ≤ Real.log L / L := by
      rw [div_le_div_iff₀ hLpos hLpos]; exact mul_le_mul_of_nonneg_right h2 hLpos.le
    linarith only [this]
  have hs3 : |s.im| ≤ L := le_trans hsim hLge4
  have hlog := hyp s hs1 hs2 hs3
  have hlog' : (-logDeriv (DirichletCharacter.LFunction χ) s).re + nearInvSum N χ s δ ≤ c * L := by
    rw [← hbridge]; exact hlog
  have hterm1 : ((a + lam₁) / L) *
      ((-logDeriv (DirichletCharacter.LFunction χ) s).re + nearInvSum N χ s δ)
      ≤ (a + lam₁) * c := by
    have h := mul_le_mul_of_nonneg_left hlog' (div_nonneg hα (le_of_lt hLpos))
    have heq : (a + lam₁) / L * (c * L) = (a + lam₁) * c := by field_simp
    linarith [heq.le, heq.ge]
  -- far zeros and parity
  have hnorm_s : ‖s‖ ≤ L + 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (lt_trans zero_lt_one hsre_gt)] at h
    calc ‖s‖ ≤ s.re + |s.im| := h
      _ = 1 + a / L + |s.im| := by rw [hsre]
      _ ≤ 1 + a / L + 4 := by linarith [hsim]
      _ ≤ L + 5 := by
          have hdiv : a / L ≤ a := by rw [div_le_iff₀ hLpos]; exact le_mul_of_one_le_right ha.le hLge1
          linarith
  have hJ : invSqSum N χ s ≤ C * (L + 2) := hC χ hχ hprim hLge1 hlogN hnorm_s
  obtain ⟨hT2abs, hT3abs⟩ := hCt s (by linarith) par hpar_le
  have hnegT2 : -(∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re ≤ Ct := by
    linarith [(abs_le.mp hT2abs).1]
  have hnegT3 : -(∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re ≤ Ct := by
    linarith [(abs_le.mp hT3abs).1]
  have hAle : a + lam₁ ≤ a + M := by linarith
  have hAe_pos : 0 < (a + lam₁) * e := mul_pos (by linarith) he
  have hKL : K ≤ (a + lam₁) * e * L := by
    have h1 : a * e ≤ (a + lam₁) * e := mul_le_mul_of_nonneg_right (by linarith only [hlam₁]) he.le
    have h2 : a * e * L ≤ (a + lam₁) * e * L := mul_le_mul_of_nonneg_right h1 hLpos.le
    linarith only [hKe, h2]
  have herr := error_bound (A := a + lam₁) (Amax := a + M) (k2 := 1 + 4 / δ ^ 2)
    (k3 := (2 / δ) * (1 + 4 / δ ^ 2)) (C := C) (Ct := Ct)
    (J := invSqSum N χ s)
    (T2r := (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2).re)
    (T3r := (∑' n : ℕ, (1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3).re)
    (L := L) (e := e)
    hα hAle (by linarith) (by positivity) (by positivity) hCpos.le hCtpos.le hJ hnegT2 hnegT3 hLge2 hLpos hAe_pos
    (by rw [← hKdef]; exact hKL)
  have hbridge2 := Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum (s := s) (a := a) (lam₁ := lam₁) (L := L)
    χ hχ hprim hδ0 (le_of_lt hδ1)
  rw [← hbridge2] at hmain
  linarith only [hmain, hterm1, herr]

end Work.ZeroFreeTables.P9.prim
