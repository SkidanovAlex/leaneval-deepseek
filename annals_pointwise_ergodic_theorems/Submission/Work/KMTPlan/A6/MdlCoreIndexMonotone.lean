import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7.randSymb_coeff_aux

namespace Work.KMTPlan.A6

/-- A `Λ`-lacunary sequence with `Λ > 1` is strictly increasing: from
`Λ < a (n+1) / a n` and `1 < Λ` we get `a n < a (n+1)` (the case `a n = 0` being impossible,
since then `a (n+1) / a n = 0 < Λ ≤ 0`). -/
theorem lacunary_strictMono {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (hlac : PointwiseErgodicTheorems.Lacunary Λ a) : StrictMono a := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hpos : 0 < a n := by
    rcases lt_or_eq_of_le (show (0 : NNReal) ≤ a n from zero_le) with h0 | h0
    · exact h0
    · exfalso
      have hz : a (n + 1) / a n = 0 := by rw [← h0, div_zero]
      have hlt := hlac n
      rw [hz] at hlt
      exact absurd hlt (not_lt.mpr (zero_le : (0 : NNReal) ≤ Λ))
  have hlt := (lt_div_iff₀ hpos).mp (hlac n)
  calc a n = 1 * a n := (one_mul _).symm
    _ < Λ * a n := mul_lt_mul_of_pos_right hΛ hpos
    _ < a (n + 1) := hlt

/-- `⌊a ·⌋` is monotone for a `Λ`-lacunary `a` with `Λ > 1`. -/
theorem lacunary_floor_monotone {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (hlac : PointwiseErgodicTheorems.Lacunary Λ a) :
    Monotone fun n => Nat.floor (a n) :=
  Work.KMTAreas.A7.monotone_floor_nnreal (lacunary_strictMono hΛ hlac).monotone

/-- The core condition `mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n` (`MdlDefs.lean`) is upward closed in the
index `n`: `mdlCore … n` and `n ≤ m` give `mdlCore … m`.

Its three components are all monotone in the scale `N = ⌊a n⌋`:
`inIndexSet C₀ l s₁ s₂ N = (l ≤ heightScale C₀ N ∧ s₁ ≤ heightScale C₀ N ∧ s₂ ≤ heightScale C₀ N)`
grows with `N` (`Work.Analysis.EndVar.heightScale_mono`), `splitCut ρ L < N` is upward closed in
`N`, and `mainRegime ρ k₁ k₂ N` (`Work.KMTAreas.A7.mainRegime`, an inequality involving
`(logN N).toNat`) grows with `N` (`Work.KMTAreas.A7.monotone_logN_toNat`).  Finally `⌊a ·⌋` is
monotone because `Lacunary Λ a` with `1 < Λ` forces `0 < a n` and `a n < a (n+1)` for all `n`, so
`Monotone a` and hence `Monotone (fun n => Nat.floor (a n))` (`Nat.floor_mono`). -/
theorem MdlCoreIndexMonotone (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (hΛ : 1 < Λ) (hlac : PointwiseErgodicTheorems.Lacunary Λ a)
    {n m : ℕ} (hnm : n ≤ m) :
    Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ m := by
  intro h
  have hnm' : Nat.floor (a n) ≤ Nat.floor (a m) := lacunary_floor_monotone hΛ hlac hnm
  have hheight : (Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℤ)
      ≤ (Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a m)) : ℤ) :=
    Int.ofNat_le.mpr (Work.Analysis.EndVar.heightScale_mono C₀ hnm')
  have hlog : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat :=
    Work.KMTAreas.A7.monotone_logN_toNat hnm'
  simp only [Work.KMTPlan.A6.mdlCore, Work.Analysis.EndVar.inIndexSet,
    Work.KMTAreas.A7.mainRegime] at h ⊢
  exact ⟨⟨le_trans h.1.1 hheight, le_trans h.1.2.1 hheight, le_trans h.1.2.2 hheight⟩,
    lt_of_lt_of_le h.2.1 hnm', le_trans h.2.2.1 hlog, le_trans h.2.2.2 hlog⟩

end Work.KMTPlan.A6
