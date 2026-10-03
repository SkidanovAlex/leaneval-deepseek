import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.SeriesP
import Submission.Work.ORHughesFree.NaturalExtension.blimRank_toeplitzT
import Submission.Work.ORHughesFree.NaturalExtension.rk_toeplitzSeries_sub_mul_le
import Submission.Work.ORHughesFree.NaturalExtension.blim_mono
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.RankAPI.rk_le_right

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- A real sequence squeezed between `0` and `C / (n+1)` has ultralimit `0` along any ultrafilter
containing the cofinite filter.

This is the elementary estimate used to show that the multiplicativity defect of the Toeplitz
family has rank zero: its `n`-th rank is bounded independently of `n`, so after dividing by `n+1`
and letting the ultrafilter send `n` to infinity the ultralimit vanishes. -/
theorem blim_eq_zero_of_le_div_aux (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.atTop) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h0 : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ C / (((n + 1 : ℕ) : ℝ))) :
    blim ω f = 0 := by
  have hg : Filter.Tendsto (fun n : ℕ => C / (((n + 1 : ℕ) : ℝ))) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  have htend : Filter.Tendsto f Filter.atTop (nhds 0) :=
    squeeze_zero h0 hle hg
  have hbdd : ∀ n, |f n| ≤ C := by
    intro n
    have h1 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
      have : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
      exact_mod_cast this
    have h2 : C / (((n + 1 : ℕ) : ℝ)) ≤ C := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)))]
      calc C = C * 1 := (mul_one C).symm
        _ ≤ C * (((n + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h1 hC
    rw [abs_of_nonneg (h0 n)]
    exact le_trans (hle n) h2
  exact blim_of_tendsto ω hω hbdd htend

theorem tok_sub_mul_mem_SPideal {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop)
    (rk : Work.ORHughesFree.SylvesterRank U)
    (p q : Work.ORHughesFree.SkewLaurentSeries U) :
    Work.ORHughesFree.NaturalExtension.tok (p * q)
      - Work.ORHughesFree.NaturalExtension.tok p * Work.ORHughesFree.NaturalExtension.tok q
      ∈ Work.ORHughesFree.NaturalExtension.SPideal ω rk := by
  classical
  rw [mem_SPideal, rkAmp_apply, blimRank_oneByOne]
  set C : ℝ := ((max 0 (-(Work.ORHughesFree.SkewLaurentSeries.lo p)) : ℤ) : ℝ)
      + ((max 0 (-(Work.ORHughesFree.SkewLaurentSeries.lo q)) : ℤ) : ℝ) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    apply add_nonneg
    · exact_mod_cast (le_max_left (0 : ℤ) (-(Work.ORHughesFree.SkewLaurentSeries.lo p)))
    · exact_mod_cast (le_max_left (0 : ℤ) (-(Work.ORHughesFree.SkewLaurentSeries.lo q)))
  have h0 : ∀ n, (0 : ℝ) ≤ rk.rk (n + 1) (n + 1)
      ((tok (p * q) - tok p * tok q) n) / (((n + 1 : ℕ) : ℝ)) :=
    fun n => div_nonneg (rk.rk_nonneg _ _ _) (by positivity)
  have hle : ∀ n, rk.rk (n + 1) (n + 1) ((tok (p * q) - tok p * tok q) n)
        / (((n + 1 : ℕ) : ℝ)) ≤ C / (((n + 1 : ℕ) : ℝ)) := by
    intro n
    have h : rk.rk (n + 1) (n + 1) ((tok (p * q) - tok p * tok q) n) ≤ C := by
      rw [tok_sub_mul_apply p q n, hC]
      exact rk_toeplitzSeries_sub_mul_le rk p q (n + 1)
    exact div_le_div_of_nonneg_right h (by positivity)
  exact blim_eq_zero_of_le_div_aux ω hω hC0 h0 hle

end Work.ORHughesFree.NaturalExtension
