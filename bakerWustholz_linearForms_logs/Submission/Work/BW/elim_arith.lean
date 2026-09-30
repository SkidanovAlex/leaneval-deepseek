import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.elim_Cstep
import Submission.Work.BW.elim_Cdom
import Submission.Work.BW.elim_Xbw
import Submission.Work.BW.elim_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Arithmetic elimination step of BW §6 (BW p. 27): the `(n-1)`-variable bound
`C(n-1,d)·M'·P + log Y` is absorbed by the `n`-variable bound `C(n,d)·M·H0·P`,
using `M' ≤ M + log 2 + log Y`, `H0 ≥ 1/d`, `A ≤ H0^m`, `A ≥ d^{-m}`,
`P ≥ A/(H0 d^{n-m})`, `Y ≤ (9md^3)^m A` and `M ≥ max(Xbw n d, log 2)`. -/
theorem elim_arith {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) {d : ℕ} (hd : 1 ≤ d)
    {A H0 P Y M M' : ℝ} (hA : 0 < A) (hH0 : 0 < H0) (hP : 0 < P)
    (hH0d : 1 / (d : ℝ) ≤ H0)
    (hAlo : 1 / (d : ℝ) ^ m ≤ A)
    (hAhi : A ≤ H0 ^ m)
    (hPlow : A / H0 / (d : ℝ) ^ (n - m) ≤ P)
    (hY1 : 1 ≤ Y) (hY : Y ≤ (9 * m * (d : ℝ) ^ 3) ^ m * A)
    (hM : Work.BW.Xbw n d ≤ M) (hM2 : Real.log 2 ≤ M)
    (hM' : M' ≤ M + Real.log 2 + Real.log Y) :
    BakerWustholz.C (n - 1) d * M' * P + Real.log Y ≤ BakerWustholz.C n d * M * H0 * P := by
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmnat : m ≠ 0 := by omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hMnn : 0 ≤ M := le_trans (le_of_lt hlog2pos) hM2
  -- ## The parameter `ψ := d·A^{1/m}` and its basic properties
  set a : ℝ := Real.log A with ha
  set s : ℝ := a / (m:ℝ) with hs
  set ψ : ℝ := Real.exp s * (d:ℝ) with hψdef
  have hψpos : 0 < ψ := by rw [hψdef]; positivity
  have hexps : Real.exp s = ψ / (d:ℝ) := by rw [hψdef]; field_simp
  have hms : (m:ℝ) * s = a := by rw [hs]; field_simp
  have hAeq : A = ψ^m / (d:ℝ)^m := by
    calc A = Real.exp a := (Real.exp_log hA).symm
      _ = Real.exp ((m:ℝ)*s) := by rw [hms]
      _ = (Real.exp s)^m := Real.exp_nat_mul s m
      _ = (ψ/(d:ℝ))^m := by rw [hexps]
      _ = ψ^m/(d:ℝ)^m := by rw [div_pow]
  have hAeq2 : A = (Real.exp s)^m := by
    rw [hAeq, hψdef, mul_pow]; field_simp
  have hlogA : -((m:ℝ) * Real.log (d:ℝ)) ≤ a := by
    have h1 : Real.log (1 / (d:ℝ)^m) ≤ a := by
      rw [ha]; exact Real.log_le_log (by positivity) hAlo
    have h2 : Real.log (1 / (d:ℝ)^m) = -((m:ℝ) * Real.log (d:ℝ)) := by
      rw [one_div, Real.log_inv, Real.log_pow]
    linarith [h1, h2]
  have hs_ge : -(Real.log (d:ℝ)) ≤ s := by
    rw [hs, le_div_iff₀ hmR]; nlinarith [hlogA]
  have hψ1 : 1 ≤ ψ := by
    have h1 : Real.exp (-(Real.log (d:ℝ))) ≤ Real.exp s := Real.exp_le_exp.mpr hs_ge
    rw [hψdef]
    have h2 : (Real.exp (-(Real.log (d:ℝ)))) * (d:ℝ) ≤ Real.exp s * (d:ℝ) :=
      mul_le_mul h1 le_rfl (le_of_lt hd0) (le_of_lt (Real.exp_pos s))
    rw [Real.exp_neg, Real.exp_log hd0, inv_mul_cancel₀ (ne_of_gt hd0)] at h2
    simpa using h2
  have hexps_le : Real.exp s ≤ H0 := by
    have h1 : (Real.exp s)^m ≤ H0^m := by rw [← hAeq2]; exact hAhi
    exact (pow_le_pow_iff_left₀ (le_of_lt (Real.exp_pos s)) (le_of_lt hH0) hmnat).mp h1
  have hψH0 : ψ ≤ (d:ℝ)*H0 := by
    rw [hψdef]
    calc Real.exp s * (d:ℝ) ≤ H0 * (d:ℝ) := mul_le_mul_of_nonneg_right hexps_le (le_of_lt hd0)
      _ = (d:ℝ) * H0 := by ring
  have hlogψ : Real.log ψ = s + Real.log (d:ℝ) := by
    rw [hψdef, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  -- ## The bound on `log Y`, in the form of `W`
  have hlogY : Real.log Y ≤ (m:ℝ) * Real.log (9 * (m:ℝ) * (d:ℝ)^2) + (m:ℝ) * Real.log ψ := by
    have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
    have h1 : Real.log Y ≤ (m:ℝ) * Real.log (9 * (m:ℝ) * (d:ℝ)^3) + a := by
      have h2 : Real.log Y ≤ Real.log ((9*(m:ℝ)*(d:ℝ)^3)^m * A) := Real.log_le_log hY0 hY
      rw [Real.log_mul (by positivity) (ne_of_gt hA), Real.log_pow] at h2
      rw [← ha] at h2; exact h2
    have h3 : Real.log (9*(m:ℝ)*(d:ℝ)^3) = Real.log (9*(m:ℝ)*(d:ℝ)^2) + Real.log (d:ℝ) := by
      have h4 : (9*(m:ℝ)*(d:ℝ)^3) = (9*(m:ℝ)*(d:ℝ)^2) * (d:ℝ) := by ring
      rw [h4, Real.log_mul (by positivity) (by positivity)]
    have h5 : (m:ℝ) * Real.log ψ = a + (m:ℝ) * Real.log (d:ℝ) := by
      rw [hlogψ, mul_add, hms]
    rw [h3] at h1
    have h6 : (m:ℝ) * (Real.log (9*(m:ℝ)*(d:ℝ)^2) + Real.log (d:ℝ)) + a
        = (m:ℝ) * Real.log (9*(m:ℝ)*(d:ℝ)^2) + (m:ℝ) * Real.log ψ := by
      rw [h5]; ring
    linarith [h1, h6]
  set W : ℝ := M + Real.log 2 + (m:ℝ) * Real.log (9 * (m:ℝ) * (d:ℝ)^2) + (m:ℝ) * Real.log ψ with hW
  have hY_W : Real.log Y ≤ W := by rw [hW]; linarith [hlogY]
  have hM'W : M' ≤ W := by rw [hW]; linarith [hM', hlogY]
  have hWnn : 0 ≤ W := by
    have h1 : (1:ℝ) ≤ 9*(m:ℝ)*(d:ℝ)^2 := by
      have hd2 : (1:ℝ) ≤ (d:ℝ)^2 := one_le_pow₀ hd1
      nlinarith [hm1, hd2]
    have hl : 0 ≤ Real.log (9*(m:ℝ)*(d:ℝ)^2) := Real.log_nonneg h1
    have hlψ : 0 ≤ Real.log ψ := Real.log_nonneg hψ1
    rw [hW]
    linarith [hl, hlψ, hMnn, le_of_lt hlog2pos,
      mul_nonneg (le_of_lt hmR) hl, mul_nonneg (le_of_lt hmR) hlψ]
  -- ## The core numeric estimate `2W ≤ 64 n (n+1) ψ M`
  have hcore : 2*W ≤ 64*(n:ℝ)*((n:ℝ)+1)*ψ*M := by
    have h1 : (n:ℝ)*Real.log n + Real.log d ≤ M := le_trans (elim_Xbw hn hd) hM
    rw [hW]
    exact elim_core hn hm hmn hd hψ1 h1 hM2
  have hMψ : 0 ≤ 64*(n:ℝ)*((n:ℝ)+1)*M := by positivity
  have hcoef : W ≤ 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 := by
    have h1 : 64*(n:ℝ)*((n:ℝ)+1)*ψ*M ≤ 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 := by
      calc 64*(n:ℝ)*((n:ℝ)+1)*ψ*M = (64*(n:ℝ)*((n:ℝ)+1)*M)*ψ := by ring
        _ ≤ (64*(n:ℝ)*((n:ℝ)+1)*M)*((d:ℝ)*H0) := mul_le_mul_of_nonneg_left hψH0 hMψ
        _ = 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 := by ring
    linarith [hcore, h1]
  -- ## The constant `C`
  set Cn : ℝ := BakerWustholz.C n d with hCn
  set Cn1 : ℝ := BakerWustholz.C (n-1) d with hCn1
  have hCstep : 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*Cn1 ≤ Cn := by
    rw [hCn, hCn1]; exact elim_Cstep hn hd
  have hCdom : (d:ℝ)^(n-1) ≤ Cn1 := by rw [hCn1]; exact elim_Cdom hn hd
  have hCn1pos : 0 < Cn1 := by
    have h2 : (1:ℝ) ≤ (d:ℝ)^(n-1) := one_le_pow₀ hd1
    linarith [hCdom, h2]
  -- ## `Pmin`
  set Pmin : ℝ := A / H0 / (d:ℝ)^(n-m) with hPmin
  have hPmin_le : Pmin ≤ P := by rw [hPmin]; exact hPlow
  have hcoef_nn : 0 ≤ 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W := by linarith [hcoef]
  -- ## The key estimate
  have hinvH0 : 1/H0 ≤ (d:ℝ)/ψ := by
    have hpsi_d : ψ/(d:ℝ) ≤ H0 := by
      rw [div_le_iff₀ hd0]; linarith [hψH0]
    have hp : 0 < ψ/(d:ℝ) := by positivity
    have h := one_div_le_one_div_of_le hp hpsi_d
    rwa [one_div_div] at h
  have hH0P : H0 * Pmin = A/(d:ℝ)^(n-m) := by
    rw [hPmin]; field_simp
  have hterm1 : 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0*Pmin
      = (A*(d:ℝ)/(d:ℝ)^(n-m))*(64*(n:ℝ)*((n:ℝ)+1)*M) := by
    have h1 : 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0*Pmin
        = 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*(H0*Pmin) := by ring
    rw [h1, hH0P]; ring
  have hterm2 : W*Pmin ≤ (A*(d:ℝ)/(d:ℝ)^(n-m))*(W/ψ) := by
    have hWA : 0 ≤ W*A/(d:ℝ)^(n-m) := by positivity
    have hdd : Pmin = A/(H0*(d:ℝ)^(n-m)) := by rw [hPmin, div_div]
    calc W*Pmin = (W*A/(d:ℝ)^(n-m)) * (1/H0) := by rw [hdd]; field_simp
      _ ≤ (W*A/(d:ℝ)^(n-m)) * ((d:ℝ)/ψ) := mul_le_mul_of_nonneg_left hinvH0 hWA
      _ = (A*(d:ℝ)/(d:ℝ)^(n-m))*(W/ψ) := by ring
  have hB : A*(d:ℝ)/(d:ℝ)^(n-m) = ψ^m/(d:ℝ)^(n-1) := by
    rw [hAeq]
    have hp : (d:ℝ)^m * (d:ℝ)^(n-m) = (d:ℝ)^n := by rw [← pow_add]; congr 1; omega
    have hp' : (d:ℝ) * (d:ℝ)^(n-1) = (d:ℝ)^n := by rw [← pow_succ']; congr 1; omega
    rw [div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity),
      mul_assoc, hp', hp]
  have hψpow : ψ^(m-1) * ψ = ψ^m := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have hprod1 : (A*(d:ℝ)/(d:ℝ)^(n-m))*(64*(n:ℝ)*((n:ℝ)+1)*M - W/ψ)
      = (ψ^(m-1)/(d:ℝ)^(n-1))*(64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W) := by
    rw [hB, ← hψpow]
    field_simp
  have hKey : W ≤ Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * Pmin) := by
    have hstep : (ψ^(m-1)/(d:ℝ)^(n-1))*(64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W)
        ≤ (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * Pmin := by
      have h1 : (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W)*Pmin
          = 64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0*Pmin - W*Pmin := by ring
      rw [h1, hterm1]
      have hA4 : (A*(d:ℝ)/(d:ℝ)^(n-m))*(64*(n:ℝ)*((n:ℝ)+1)*M) - W*Pmin
          ≥ (A*(d:ℝ)/(d:ℝ)^(n-m))*(64*(n:ℝ)*((n:ℝ)+1)*M)
            - (A*(d:ℝ)/(d:ℝ)^(n-m))*(W/ψ) := by linarith [hterm2]
      have hA5 : (A*(d:ℝ)/(d:ℝ)^(n-m))*(64*(n:ℝ)*((n:ℝ)+1)*M)
            - (A*(d:ℝ)/(d:ℝ)^(n-m))*(W/ψ)
          = (ψ^(m-1)/(d:ℝ)^(n-1))*(64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W) := by
        rw [← mul_sub, hprod1]
      rw [← hA5]
      exact hA4
    have hb : 1 ≤ Cn1/(d:ℝ)^(n-1) := by
      rw [one_le_div (by positivity)]; exact hCdom
    have hbψ : 1 ≤ ψ^(m-1) := one_le_pow₀ hψ1
    have hKnn : 0 ≤ 64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W := by linarith [hcore]
    have hmul10 : (1:ℝ) ≤ (Cn1/(d:ℝ)^(n-1)) * ψ^(m-1) := by
      have h1 : (1:ℝ) * 1 ≤ (Cn1/(d:ℝ)^(n-1)) * ψ^(m-1) :=
        mul_le_mul hb hbψ (by norm_num) (by linarith [hb])
      simpa using h1
    have hmul : (1:ℝ) * (64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W)
        ≤ (Cn1/(d:ℝ)^(n-1)) * ψ^(m-1) * (64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W) :=
      mul_le_mul_of_nonneg_right hmul10 hKnn
    have hK : W ≤ 64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W := by linarith [hcore]
    have h2 : (Cn1/(d:ℝ)^(n-1)) * ψ^(m-1) * (64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W)
        = Cn1 * ((ψ^(m-1)/(d:ℝ)^(n-1))*(64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W)) := by
      field_simp
    rw [h2] at hmul
    calc W ≤ (64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W) := hK
      _ ≤ Cn1 * ((ψ^(m-1)/(d:ℝ)^(n-1))*(64*(n:ℝ)*((n:ℝ)+1)*M*ψ - W)) := by
          linarith [hmul]
      _ ≤ Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * Pmin) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hCn1pos)
  -- ## Final assembly
  have hstep1 : Cn1 * (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0) * P ≤ Cn * M * H0 * P := by
    have h := mul_le_mul_of_nonneg_right hCstep (by positivity : (0:ℝ) ≤ M*H0*P)
    calc Cn1 * (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0) * P
        = (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*Cn1) * (M*H0*P) := by ring
      _ ≤ Cn * (M*H0*P) := h
      _ = Cn * M * H0 * P := by ring
  have hstep2 : Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * P)
      ≤ Cn1 * (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0) * P := by
    have h1 : Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * P)
        = Cn1 * (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0) * P - Cn1 * W * P := by ring
    have h2 : 0 ≤ Cn1 * W * P := by positivity
    linarith [h1, h2]
  have hstep3 : Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * Pmin)
      ≤ Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * P) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCn1pos)
    exact mul_le_mul_of_nonneg_left hPmin_le hcoef_nn
  have hsharp : Cn1 * W * P + W ≤ Cn * M * H0 * P := by
    have heq : Cn1 * W * P
        = Cn1 * (64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0) * P
          - Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * P) := by ring
    have hlow : W ≤ Cn1 * ((64*(n:ℝ)*((n:ℝ)+1)*(d:ℝ)*M*H0 - W) * P) :=
      le_trans hKey hstep3
    linarith [heq, hlow, hstep1]
  have hM'P : Cn1 * M' * P ≤ Cn1 * W * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM'W (le_of_lt hCn1pos)) (le_of_lt hP)
  linarith [hsharp, hM'P, hY_W]

end Work.BW
