import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.green_bound_notA
import Submission.Work.TMC16Core.Basic.green_bound_notA_win
import Submission.Work.TMC16Core.Basic.dirMat_det

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- **AJ §9 endgame: the regularity of the site `y` from a non-resonant large continuant and
two-sided decay.**  Suppose `y` lies in the window `[j₀, j₀+K-1]` (`h1`, `h2`), with `y` at
distance `≥ K/40` from both endpoints (`hd1`, `hd2`, `hn₀`, `hn₁`), the continuant
`P_K(θ+j₀α)` is large (`hlarge`), and the windowed two-sided bound `hd` holds on the scale
window `K/40 ≤ n ≤ K`.  If the two exponents obtained from the endpoint Green's function
formula decay at rate `m` in both directions (`hdec1`, `hdec2`), then `y` is `(m, ≥K)`-regular
in the sense of `IsRegularBig`.  This is the assembly of `Basic.green_bound_notA_win` with the
determinant identity `Basic.dirMat_det`. -/
theorem nr_endgame {α lam : ℝ} {E : ℂ} {θ L ε ε₁ m : ℝ} {K : ℕ} {y j₀ : ℤ}
    (hL : 0 < L) (hε : ε₁ < ε) (hm : 0 < m)
    (hK : 1 ≤ K)
    (h1 : j₀ ≤ y) (h2 : y ≤ j₀ + (K : ℤ) - 1)
    (hd1 : (K : ℤ) ≤ 40 * (y - j₀)) (hd2 : (K : ℤ) ≤ 40 * (j₀ + (K : ℤ) - 1 - y))
    (hn₀ : K / 40 ≤ (y - j₀).toNat) (hn₁ : K / 40 ≤ (j₀ + (K : ℤ) - 1 - y).toNat)
    (hlarge : Real.exp (((K : ℝ) + 1) * (L - ε)) <
      ‖Work.TMC16Core.pd α lam (θ + (j₀ : ℝ) * α) E (K + 1)‖)
    (hbd : ∀ n : ℕ, K / 40 ≤ n → n ≤ K → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hdec1 : (L + ε₁) * (((j₀ + (K : ℤ) - 1 - y : ℤ)) : ℝ) - ((K : ℝ) + 1) * (L - ε)
      ≤ -m * (((y - j₀ : ℤ)) : ℝ))
    (hdec2 : (L + ε₁) * (((y - j₀ : ℤ)) : ℝ) - ((K : ℝ) + 1) * (L - ε)
      ≤ -m * (((j₀ + (K : ℤ) - 1 - y : ℤ)) : ℝ)) :
    Work.TMC16Core.IsRegularBig α lam θ E m (K : ℝ) y := by
  rw [Work.TMC16Core.IsRegularBig]
  have hlen : j₀ + (K : ℤ) - 1 - j₀ + 1 = (K : ℤ) := by omega
  -- The continuant at the window phase is nonzero, hence the Dirichlet operator is invertible.
  have hpdne : Work.TMC16Core.pd α lam (θ + (j₀ : ℝ) * α) E (K + 1) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlarge
    exact absurd hlarge (not_lt.mpr (Real.exp_pos _).le)
  have hdet : (Work.TMC16Core.dirMat α lam (θ + (j₀ : ℝ) * α) E
      (j₀ + (K : ℤ) - 1 - j₀ + 1).toNat).det ≠ 0 := by
    rw [hlen, Int.toNat_natCast, Work.TMC16Core.Basic.dirMat_det]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hpdne
  -- The two endpoint Green's function bounds from the windowed continuant estimate.
  have hwin := Work.TMC16Core.Basic.green_bound_notA_win
    (α := α) (lam := lam) (E := E) (θ := θ) (r := L - ε) (L := L) (ε₁ := ε₁)
    (k := K) (x₁ := j₀) (x₂ := j₀ + (K:ℤ) - 1) (y := y) (n₀ := K / 40)
    hbd hn₁ hn₀ rfl h1 h2 hlarge
  obtain ⟨hg1, hg2⟩ := hwin
  refine ⟨j₀, j₀ + (K:ℤ) - 1, h1, h2, ?_, ?_, ?_, hdet, ?_, ?_⟩
  · rw [hlen]; simp
  · rw [hlen]; exact_mod_cast hd1
  · rw [hlen]; exact_mod_cast hd2
  · refine lt_of_lt_of_le hg1 ?_
    apply Real.exp_le_exp.mpr
    linarith [hdec1]
  · refine lt_of_lt_of_le hg2 ?_
    apply Real.exp_le_exp.mpr
    linarith [hdec2]

end Work.TMC16Core.Core
