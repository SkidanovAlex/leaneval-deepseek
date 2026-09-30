import Mathlib
import Submission.Work.BMF.mr_core_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_core.badPart_le2_pieceB`

Arithmetic assembly piece for the bad-set (far region) bound `badPart_le2`: the `1/T₀` part of
the per-cell bound.

Writing `P := logPc Y = (log Y)^{47/48}`, `E := (log Y)^{-47/24}` and `D := K (A_c - 1) P`, one
has `P² E = 1` and `P E = (log Y)^{-47/48}`, so

`D (D + 2) E = K² (A_c - 1)² + 2 K (A_c - 1) (log Y)^{-47/48}`.

The factor `1/T₀` is dominated by `4/W` (`hT₀`), after which the two resulting pieces
`K² (A_c - 1)² ≤ K² A_c⁴` and `2 K (A_c - 1) A_c² (log Y)^{-47/48} ≤ 2 K A_c³ (log Y)^{-47/48}`
are exactly the two hypotheses `hfree` and `hev`.
-/

namespace Work.BMF.mr_core

theorem badPart_le2_pieceB (ε Cbs Cm K Ac B Y W T₀ : ℝ)
    (hε : 0 < ε) (hCbs : 0 < Cbs) (hCm : 0 < Cm) (hK : 2 ≤ K) (hAc : 1 ≤ Ac)
    (hY : 1 ≤ Y) (hW : 0 < W)
    (hT₀ : 1 / T₀ ≤ 4 / W)
    (hfree : 4 * Cbs * Cm * K ^ 2 * Ac ^ 4 / W ≤ ε / 64)
    (hev : 8 * Cbs * Cm * K * Ac ^ 3 * (Real.log Y) ^ (-(47 / 48 : ℝ)) / W ≤ ε / 64) :
    Cbs * (K * (Ac - 1) * Work.BMF.mrCore.logPc Y) *
        (K * (Ac - 1) * Work.BMF.mrCore.logPc Y + 2) *
        (Cm * Ac ^ 2 * ((1 / T₀) * (Real.log Y) ^ (-(47 / 24 : ℝ))))
      ≤ ε / 32 := by
  simp only [Work.BMF.mrCore.logPc]
  -- `log Y ≥ 0`; the degenerate case `log Y = 0` makes the whole product vanish
  rcases lt_or_eq_of_le (Real.log_nonneg hY) with hLpos | hL0
  · -- main case: `0 < log Y`
    set L := Real.log Y with hL
    set P := L ^ (47/48:ℝ) with hP
    set E := L ^ (-(47/24:ℝ)) with hE
    have hLnn : 0 ≤ L := le_of_lt hLpos
    have hKnn : 0 ≤ K := by linarith
    have hAcm1 : 0 ≤ Ac - 1 := by linarith
    have hL48nn : 0 ≤ L^(-(47/48:ℝ)) := Real.rpow_nonneg hLnn _
    -- the two rpow identities
    have hPPE : (P*P)*E = 1 := by
      rw [hP, hE, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      norm_num
    have hPE : P*E = L^(-(47/48:ℝ)) := by
      rw [hP, hE, ← Real.rpow_add hLpos]; norm_num
    set XX := K^2*(Ac-1)^2 + 2*K*(Ac-1)*L^(-(47/48:ℝ)) with hXX
    set YY := K^2*Ac^2 + 2*K*Ac*L^(-(47/48:ℝ)) with hYY
    -- `D (D+2) E = XX`
    have hcore : (K*(Ac-1)*P)*((K*(Ac-1)*P)+2)*E = XX := by
      have expand : (K*(Ac-1)*P)*((K*(Ac-1)*P)+2)*E
          = (K*(Ac-1))^2*(P*P*E) + 2*(K*(Ac-1))*(P*E) := by ring
      rw [expand, hPPE, hPE, hXX]
      ring
    have hfact : Cbs*(K*(Ac-1)*P)*(K*(Ac-1)*P+2)*(Cm*Ac^2*((1/T₀)*E))
        = Cbs*Cm*Ac^2*(1/T₀)*XX := by
      calc Cbs*(K*(Ac-1)*P)*(K*(Ac-1)*P+2)*(Cm*Ac^2*((1/T₀)*E))
          = Cbs*Cm*Ac^2*(1/T₀)*((K*(Ac-1)*P)*((K*(Ac-1)*P)+2)*E) := by ring
        _ = Cbs*Cm*Ac^2*(1/T₀)*XX := by rw [hcore]
    have hXXnn : 0 ≤ XX := by
      rw [hXX]
      have h1 : 0 ≤ K^2*(Ac-1)^2 := mul_nonneg (sq_nonneg K) (sq_nonneg (Ac-1))
      have h2 : 0 ≤ 2*K*(Ac-1)*L^(-(47/48:ℝ)) := by
        have hKAc : 0 ≤ 2*K*(Ac-1) := mul_nonneg (mul_nonneg (by norm_num) hKnn) hAcm1
        exact mul_nonneg hKAc hL48nn
      linarith
    have hXY : XX ≤ YY := by
      rw [hXX, hYY]
      have ha : (Ac-1)^2 ≤ Ac^2 := by nlinarith [hAc]
      have h1 : K^2*(Ac-1)^2 ≤ K^2*Ac^2 := mul_le_mul_of_nonneg_left ha (sq_nonneg K)
      have hb : 2*K*(Ac-1)*L^(-(47/48:ℝ)) ≤ 2*K*Ac*L^(-(47/48:ℝ)) := by
        have hle : Ac - 1 ≤ Ac := by linarith
        have h2K : 0 ≤ 2*K*L^(-(47/48:ℝ)) :=
          mul_nonneg (mul_nonneg (by norm_num) hKnn) hL48nn
        have h := mul_le_mul_of_nonneg_right hle h2K
        convert h using 1 <;> ring
      linarith
    have hCbsCmAcnn : 0 ≤ Cbs*Cm*Ac^2 := by positivity
    -- replace `1/T₀` by `4/W`, then bound the two resulting pieces
    calc Cbs*(K*(Ac-1)*P)*(K*(Ac-1)*P+2)*(Cm*Ac^2*((1/T₀)*E))
        = Cbs*Cm*Ac^2*(1/T₀)*XX := hfact
      _ ≤ Cbs*Cm*Ac^2*(4/W)*XX := by
          have hinner : (1/T₀)*XX ≤ (4/W)*XX := mul_le_mul_of_nonneg_right hT₀ hXXnn
          have h := mul_le_mul_of_nonneg_left hinner hCbsCmAcnn
          simpa [mul_assoc] using h
      _ ≤ Cbs*Cm*Ac^2*(4/W)*YY := by
          have h := mul_le_mul_of_nonneg_left hXY
            (by positivity : (0:ℝ) ≤ Cbs*Cm*Ac^2*(4/W))
          simpa [mul_assoc] using h
      _ = 4*Cbs*Cm*K^2*Ac^4/W + 8*Cbs*Cm*K*Ac^3*L^(-(47/48:ℝ))/W := by
          rw [hYY]; ring
      _ ≤ ε/32 := by linarith [hfree, hev]
  · -- degenerate case `log Y = 0`: the factor `K(Ac-1)·logPc Y` vanishes
    rw [← hL0]
    rw [Real.zero_rpow (by norm_num : (47/48:ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (-(47/24):ℝ) ≠ 0)]
    simp
    linarith

end Work.BMF.mr_core
