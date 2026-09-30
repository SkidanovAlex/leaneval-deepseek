import Mathlib
import Submission.Work.BMF.mr_core_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_core.badPart_le2_pieceA`

Arithmetic assembly piece for the bad-set (far region) bound `badPart_le2`.

After the Ramaré decomposition on the coarse interval `[P_c, Q_c]` one is left with a factor
`#I_c · (K (A_c - 1) log P_c) · (K (A_c - 1) log P_c + 2)` times the per-cell bound, where
`#I_c ≍ K (A_c - 1) log P_c`.  Writing `P := logPc Y = (log Y)^{47/48}` and
`E := (log Y)^{-47/24}` one has `P² · E = 1` and `P · E = (log Y)^{-47/48}`, so the whole
product splits into the two pieces already dominated by the hypotheses `hfree` and `hev`:

* `K² (A_c - 1)² ≤ K² A_c⁴` (piece of `hfree`),
* `2 K (A_c - 1) A_c² · (log Y)^{-47/48} ≤ 2 K A_c³ · (log Y)^{-47/48}` (piece of `hev`).

This lemma performs exactly that reduction: `logPc Y` is replaced by the two rpow identities
above, and the remaining factor `(log Y)^{-47/24}` is cancelled against `(logPc Y)²`.
-/

namespace Work.BMF.mr_core

theorem badPart_le2_pieceA (ε Cbs Cm K Ac B Y : ℝ)
    (hε : 0 < ε) (hCbs : 0 < Cbs) (hCm : 0 < Cm) (hK : 2 ≤ K) (hAc : 1 ≤ Ac)
    (hY : 1 ≤ Y)
    (hfree : Cbs * Cm * K ^ 2 * Ac ^ 4 * (1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) ≤ ε / 64)
    (hev : 2 * Cbs * Cm * K * Ac ^ 3 * (1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) *
        (Real.log Y) ^ (-(47 / 48 : ℝ)) ≤ ε / 64) :
    Cbs * (K * (Ac - 1) * Work.BMF.mrCore.logPc Y) *
        (K * (Ac - 1) * Work.BMF.mrCore.logPc Y + 2) *
        (Cm * Ac ^ 2 * ((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) *
          (Real.log Y) ^ (-(47 / 24 : ℝ))))
      ≤ ε / 32 := by
  -- `logPc Y = (log Y)^{47/48}`
  simp only [Work.BMF.mrCore.logPc]
  -- `log Y ≥ 0`; the degenerate case `log Y = 0` makes the whole product vanish.
  rcases lt_or_eq_of_le (Real.log_nonneg hY) with hLpos | hL0
  · -- main case: `0 < log Y`
    set L := Real.log Y with hL
    set P := L ^ (47/48:ℝ) with hP
    set E := L ^ (-(47/24:ℝ)) with hE
    set W := (1 + B^2)^2 * Real.exp (-(B^2/4)) with hW
    set D := K * (Ac-1) * P with hD
    have hLpos' : 0 < L := by rw [hL]; exact hLpos
    have hLnn : 0 ≤ L := hLpos'.le
    have hPpos : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hLpos' _
    have hPnn : 0 ≤ P := hPpos.le
    have hEnn : 0 ≤ E := by rw [hE]; exact Real.rpow_nonneg hLnn _
    have hEnn48 : 0 ≤ L ^ (-(47/48:ℝ)) := Real.rpow_nonneg hLnn _
    have hWnn : 0 ≤ W := by rw [hW]; positivity
    have hKnn : 0 ≤ K := by linarith
    have hDnn : 0 ≤ D := by rw [hD]; positivity
    have hAcm1 : 0 ≤ Ac - 1 := by linarith
    -- the two rpow identities
    have hPP : P * P = L ^ (47/24:ℝ) := by
      rw [hP, ← Real.rpow_add hLpos']
      norm_num
    have hPPE : (P*P) * E = 1 := by
      rw [hPP, hE, ← Real.rpow_add hLpos']
      rw [show (47/24:ℝ) + -(47/24) = 0 by norm_num, Real.rpow_zero]
    have hPE : P * E = L ^ (-(47/48:ℝ)) := by
      rw [hP, hE, ← Real.rpow_add hLpos']
      norm_num
    -- `(K(Ac-1)P)² E = K² (Ac-1)²`
    have hDDE : (D*D) * E = K^2 * (Ac-1)^2 := by
      have hh : (D*D)*E = (P*P*E) * (K^2*(Ac-1)^2) := by rw [hD]; ring
      rw [hh, hPPE, one_mul]
    have hAc_sq : (Ac-1)^2 ≤ Ac^2 := by nlinarith [hAc]
    -- piece 1: the square, bounded by `hfree`
    have h1 : Cbs * (D*D) * (Cm*Ac^2*(W*E)) ≤ ε/64 := by
      have e1 : Cbs * (D*D) * (Cm*Ac^2*(W*E)) = Cbs*Cm*Ac^2*W*(K^2*(Ac-1)^2) := by
        rw [← hDDE]; ring
      rw [e1]
      have step1 : Ac^2 * (Ac-1)^2 ≤ Ac^2 * Ac^2 :=
        mul_le_mul_of_nonneg_left hAc_sq (by positivity)
      have step2 : Cbs*Cm*K^2*W*(Ac^2*(Ac-1)^2) ≤ Cbs*Cm*K^2*W*(Ac^2*Ac^2) :=
        mul_le_mul_of_nonneg_left step1 (by positivity)
      have hb : Cbs*Cm*Ac^2*W*(K^2*(Ac-1)^2) ≤ Cbs*Cm*K^2*Ac^4*W := by
        calc Cbs*Cm*Ac^2*W*(K^2*(Ac-1)^2) = Cbs*Cm*K^2*W*(Ac^2*(Ac-1)^2) := by ring
          _ ≤ Cbs*Cm*K^2*W*(Ac^2*Ac^2) := step2
          _ = Cbs*Cm*K^2*Ac^4*W := by ring
      linarith [hfree, hb]
    -- `(K(Ac-1)P) E = K(Ac-1) (log Y)^{-47/48}`
    have hDE : D * E = K*(Ac-1)*L^(-(47/48:ℝ)) := by
      have hh : D*E = (K*(Ac-1))*(P*E) := by rw [hD]; ring
      rw [hh, hPE]
    have hAc_cube : Ac^2*(Ac-1) ≤ Ac^3 := by nlinarith [sq_nonneg Ac]
    -- piece 2: the linear term, bounded by `hev`
    have h2 : Cbs * (2*D) * (Cm*Ac^2*(W*E)) ≤ ε/64 := by
      have e2 : Cbs * (2*D) * (Cm*Ac^2*(W*E)) = 2*Cbs*Cm*K*(Ac-1)*Ac^2*W*L^(-(47/48:ℝ)) := by
        calc Cbs * (2*D) * (Cm*Ac^2*(W*E)) = 2*Cbs*Cm*Ac^2*W*(D*E) := by ring
          _ = 2*Cbs*Cm*Ac^2*W*(K*(Ac-1)*L^(-(47/48:ℝ))) := by rw [hDE]
          _ = 2*Cbs*Cm*K*(Ac-1)*Ac^2*W*L^(-(47/48:ℝ)) := by ring
      rw [e2]
      have stepb : Cbs*Cm*K*W*L^(-(47/48:ℝ)) * (Ac^2*(Ac-1)) ≤
          Cbs*Cm*K*W*L^(-(47/48:ℝ)) * Ac^3 :=
        mul_le_mul_of_nonneg_left hAc_cube (by positivity)
      have hb2 : 2*Cbs*Cm*K*(Ac-1)*Ac^2*W*L^(-(47/48:ℝ)) ≤
          2*Cbs*Cm*K*Ac^3*W*L^(-(47/48:ℝ)) := by
        calc 2*Cbs*Cm*K*(Ac-1)*Ac^2*W*L^(-(47/48:ℝ))
            = 2*(Cbs*Cm*K*W*L^(-(47/48:ℝ))*(Ac^2*(Ac-1))) := by ring
          _ ≤ 2*(Cbs*Cm*K*W*L^(-(47/48:ℝ))*Ac^3) := by linarith [stepb]
          _ = 2*Cbs*Cm*K*Ac^3*W*L^(-(47/48:ℝ)) := by ring
      linarith [hev, hb2]
    -- `D(D+2) = D² + 2D`, and the two pieces add up to `ε/64 + ε/64 = ε/32`
    have hsplit : Cbs * D * (D+2) * (Cm*Ac^2*(W*E))
        = Cbs*(D*D)*(Cm*Ac^2*(W*E)) + Cbs*(2*D)*(Cm*Ac^2*(W*E)) := by ring
    linarith [h1, h2, hsplit]
  · -- degenerate case `log Y = 0`: the factor `K(Ac-1)·logPc Y` vanishes
    rw [← hL0]
    rw [Real.zero_rpow (by norm_num : (47/48:ℝ) ≠ 0)]
    rw [Real.zero_rpow (by norm_num : (-(47/24):ℝ) ≠ 0)]
    have h : (0:ℝ) ≤ ε/32 := by linarith
    linarith [h]

end Work.BMF.mr_core
