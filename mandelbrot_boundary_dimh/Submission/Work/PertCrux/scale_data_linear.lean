import Mathlib
import Submission.Work.PertCrux.log_cube_absorb
import Submission.Work.PertCrux.lin_absorb
import Submission.Work.PertCrux.cubic_absorb

namespace Work.PertCrux

/-- **The scale `Λ` of the linear-landing crux, with a *linear* upper bound.**

Companion of `Work.Analysis.PertCrux.scale_data_v2` (which only bounds `Λ` by a *cubic* expression
`10^6 (Ξ'+MK+CW+Rgl+1)^3 + 10^6`).  Here `Λ` is the natural fixed point of the logarithmic
condition, so that `Λ ≲ (Ξ'+MK+CW+1)(2+log(Ξ'+MK+CW+2))`.

Witness: `Λ := max 64 (max Ξ' (max MK (max (8*Rgl) (100*CW*(2 + log (4*N))))))` where
`N := Ξ'+MK+CW+1`.  The hypothesis `8*Rgl ≤ Ξ'` keeps the datum constant `8*Rgl` inside `Ξ' ≤ N`,
and `64 ≤ Ξ'` gives `log N ≥ 2.7`, which is what the constant `190` (and the `100` in the last term)
was chosen for. -/
theorem scale_data_linear {Ξ' MK CW Rgl : ℝ} (hΞ' : 64 ≤ Ξ') (hMK : 0 ≤ MK)
    (hCW : 0 ≤ CW) (hRgl : 0 ≤ Rgl) (hΞ'Rgl : 8 * Rgl ≤ Ξ') :
    ∃ Lam : ℝ, 64 ≤ Lam ∧ Ξ' ≤ Lam ∧ MK ≤ Lam ∧ CW ≤ Lam ∧ Rgl ≤ Lam / 8 ∧
      Lam ≤ 10 ^ 6 * (Ξ' + MK + CW + Rgl + 1) ^ 3 + 10 ^ 6 ∧
      32 * CW * (2 + Real.log (Ξ' + 3 * Lam + MK + 5 * CW + 4)) ≤ Lam ∧
      Lam ≤ 190 * (Ξ' + MK + CW + 1) * (2 + Real.log (Ξ' + MK + CW + 2)) := by
  set N : ℝ := Ξ' + MK + CW + 1 with hN
  set L : ℝ := max 64 (max Ξ' (max MK (max (8 * Rgl) (100 * CW * (2 + Real.log (4 * N)))))) with hL
  have hN65 : 65 ≤ N := by rw [hN]; linarith
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hΞ'N : Ξ' ≤ N := by rw [hN]; linarith
  have hMKN : MK ≤ N := by rw [hN]; linarith
  have hCWN : CW ≤ N := by rw [hN]; linarith
  have h4Npos : 0 < 4 * N := by linarith
  have h4N1 : 1 ≤ 4 * N := by linarith
  have hlog4Nnn : 0 ≤ Real.log (4 * N) := Real.log_nonneg h4N1
  -- domination by the witness `L`
  have h64L : (64:ℝ) ≤ L := by rw [hL]; exact le_max_of_le_left le_rfl
  have hΞ'L : Ξ' ≤ L := by rw [hL]; exact le_max_of_le_right (le_max_of_le_left le_rfl)
  have hMKL : MK ≤ L := by
    rw [hL]; exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl))
  have h8RglL : 8 * Rgl ≤ L := by
    rw [hL]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left le_rfl)))
  have hXL : 100 * CW * (2 + Real.log (4 * N)) ≤ L := by
    rw [hL]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right le_rfl)))
  have hCWL : CW ≤ L := by
    have h1 : CW ≤ 100 * CW * (2 + Real.log (4 * N)) := by
      nlinarith [hCW, hlog4Nnn, mul_nonneg hCW hlog4Nnn]
    linarith [h1, hXL]
  -- the uniform upper bound `L ≤ 100·N·(2 + log 4N)`
  have hL_le : L ≤ 100 * N * (2 + Real.log (4 * N)) := by
    rw [hL]
    refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
    · nlinarith [hN65, hlog4Nnn]
    · nlinarith [hΞ'N, hNpos, mul_nonneg hNpos.le hlog4Nnn]
    · nlinarith [hMKN, hNpos, mul_nonneg hNpos.le hlog4Nnn]
    · nlinarith [hΞ'Rgl, hΞ'N, hNpos, mul_nonneg hNpos.le hlog4Nnn]
    · have h2 : (0:ℝ) ≤ 2 + Real.log (4 * N) := by linarith
      have hml := mul_le_mul_of_nonneg_right hCWN h2
      nlinarith [hml]
  have hYpos : 0 < Ξ' + 3 * L + MK + 5 * CW + 4 := by linarith [hΞ', hMK, hCW, h64L]
  have hYle : Ξ' + 3 * L + MK + 5 * CW + 4 ≤ (4 * N) ^ 3 := by
    have hlog4N_le : Real.log (4 * N) ≤ 4 * N := by
      have h := Real.log_le_sub_one_of_pos h4Npos
      linarith
    have hL' : L ≤ 100 * N * (2 + 4 * N) := by
      have hm := mul_le_mul_of_nonneg_left (show 2 + Real.log (4 * N) ≤ 2 + 4 * N by linarith)
        (by positivity : (0:ℝ) ≤ 100 * N)
      linarith [hL_le, hm]
    have h3 : 3 * L ≤ 3 * (100 * N * (2 + 4 * N)) := by linarith [hL']
    have hN2nn : (0:ℝ) ≤ N ^ 2 := sq_nonneg N
    have hN3 : 65 * N ^ 2 ≤ N ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right hN65 hN2nn
      nlinarith [hm]
    have hkey : 4160 * N ^ 2 ≤ 64 * N ^ 3 := by nlinarith [hN3]
    have hN2ge1 : 1 ≤ N ^ 2 := by nlinarith [hN1]
    nlinarith [h3, hΞ'N, hMKN, hCWN, hkey, hN2nn, hN65, hN2ge1]
  have h82 : Ξ' + MK + CW + 2 = N + 1 := by rw [hN]; ring
  -- the logarithmic condition
  have hstep : 32 * CW * (2 + Real.log (Ξ' + 3 * L + MK + 5 * CW + 4))
      ≤ 100 * CW * (2 + Real.log (4 * N)) := by
    have hlogY := log_cube_absorb hYpos h4N1 hYle
    have h1 : 32 * CW * (2 + Real.log (Ξ' + 3 * L + MK + 5 * CW + 4))
        ≤ 32 * CW * ((25 / 8) * (2 + Real.log (4 * N))) :=
      mul_le_mul_of_nonneg_left hlogY (by positivity)
    have h2 : 32 * CW * ((25 / 8) * (2 + Real.log (4 * N)))
        = 100 * CW * (2 + Real.log (4 * N)) := by ring
    linarith [h1, h2]
  refine ⟨L, h64L, hΞ'L, hMKL, hCWL, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
    linarith [h8RglL]
  · have hS : N ≤ Ξ' + MK + CW + Rgl + 1 := by rw [hN]; linarith
    exact cubic_absorb hN65 hS hL_le
  · exact le_trans hstep hXL
  · rw [h82]
    exact le_trans hL_le (lin_absorb hN65)

end Work.PertCrux
