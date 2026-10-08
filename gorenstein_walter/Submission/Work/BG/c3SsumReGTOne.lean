import Mathlib
import Submission.Work.BG.thm32
import Submission.Work.BG.S02
import Submission.Work.BG.ThmABCCharDefs

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3SsumReGTOne {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hComp : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : Work.BG.IsPmIrr χ)
    (h3 : (Work.GW2.C16.bset C f χ).ncard = 3) :
    1 < (Work.BG.Ssum C f χ).re := by
  classical
  haveI : Fintype ↥(Uin C) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(Uin C) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- The main identity of §3 (`Work.BG.chi_sum_T_eq`, the content of Theorem 3.2):
  --   `Σ_{g ∈ T} ‖χ(g)‖² = |H₀| · (|𝒮(χ)| - Ssum)`.
  have hC := chi_sum_T_eq D C hComp f hf χ hχ
  -- `Ssum` is a real number.
  have hSsum_real : Ssum C f χ = (((Ssum C f χ).re : ℝ) : ℂ) := by
    rw [Ssum, Complex.re_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Ssum_term_ofReal C f hf χ hχ ν, Complex.ofReal_re]
  -- The same identity, read in `ℝ`.
  have hreal : (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) =
      (Nat.card ↥C.P.H0 : ℝ) * (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re) := by
    have hL : (∑ g ∈ TfinH C, χ (g : G) * star (χ (g : G))) =
        Complex.ofReal (∑ g ∈ TfinH C, ‖χ (g : G)‖ ^ 2) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Complex.star_def, ← Complex.normSq_eq_norm_sq]
      exact Complex.mul_conj (χ (g : G))
    have hR : (Nat.card ↥C.P.H0 : ℂ) * (((bset C f χ).ncard : ℂ) - Ssum C f χ) =
        Complex.ofReal ((Nat.card ↥C.P.H0 : ℝ) *
          (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re)) := by
      rw [hSsum_real]
      rw [show ((((Ssum C f χ).re : ℝ) : ℂ)).re = (Ssum C f χ).re from
        Complex.ofReal_re ((Ssum C f χ).re)]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
        ← Complex.ofReal_mul]
    exact Complex.ofReal_inj.mp (hL.symm.trans (hC.trans hR))
  -- The strict TI-counting bound `Σ_{g ∈ T} ‖χ(g)‖² < 2|H₀|` (Theorem 3.2, second input).
  have hbound := sum_TfinH_normSq_lt C χ hχ
  have hHpos : (0 : ℝ) < (Nat.card ↥C.P.H0 : ℝ) := by exact_mod_cast Nat.card_pos
  have hmain2 : (Nat.card ↥C.P.H0 : ℝ) * (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re) <
      2 * (Nat.card ↥C.P.H0 : ℝ) := by
    rw [← hreal]
    exact hbound
  -- Divide by `|H₀| > 0`: `|𝒮(χ)| - Ssum < 2`.
  have hlt2 : ((bset C f χ).ncard : ℝ) - (Ssum C f χ).re < 2 := by
    rw [show ((bset C f χ).ncard : ℝ) - (Ssum C f χ).re =
        ((Nat.card ↥C.P.H0 : ℝ) * (((bset C f χ).ncard : ℝ) - (Ssum C f χ).re)) /
        (Nat.card ↥C.P.H0 : ℝ) from (mul_div_cancel_left₀ _ hHpos.ne').symm]
    exact (div_lt_iff₀ hHpos).mpr hmain2
  -- With `|𝒮(χ)| = 3`: `3 - Ssum < 2`, i.e. `Ssum > 1`.
  rw [h3] at hlt2
  norm_num at hlt2
  linarith

end Work.BG
