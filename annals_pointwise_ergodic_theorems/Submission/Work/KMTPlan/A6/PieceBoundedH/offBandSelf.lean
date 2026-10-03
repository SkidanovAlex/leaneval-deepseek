/-
# Fallback proof of the off-band half of `Work.KMTPlan.A6.PieceBoundedH.errorBound`

The delegated module `Submission/Work/KMTPlan/A6/PieceBoundedH/errorBoundOffBand.lean` states the
off-band half; this module contains an independent proof of the *same* statement (under the name
`offBandSelf`, so that the two can coexist).  It is used by `errorBound.lean` only if the delegated
statement turns out to be unavailable.

Off the band the repaired model vanishes (`modelTupleRep`'s guard contains `bandCond`), so the
family is the concrete column `Work.Analysis.EndVar.varpPiece`; the height bound together with
`¬ bandCond` bounds the logarithmic scale (`logN_toNat_lt_of_not_bandCond`), whence by lacunarity
(`Work.KMTAreas.A7.offBand_lt_nBound`) the family is supported on the finite initial segment
`Finset.range (nBound Λ (offBandLog ρ B) + 1)`.  The finite-support spike bound
(`Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_sum`), the crude single-scale
estimate `Work.KMTAreas.A7.RepOffBandCrude` and `Work.KMTAreas.A7.term_sum_le` finish.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.errorBoundAux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.PieceBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems Work.KMTContract

/-- **The off-band half of `errorBound`, proved here directly.** -/
theorem offBandSelf (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
              Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              else 0))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  -- the crude single-scale estimate at the enlarged height bound
  set Boff : ℕ := max B (offBandLog ρ B) with hBoff
  obtain ⟨Cv, hCv, hCvB⟩ := Work.KMTAreas.A7.RepOffBandCrude P 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (le_of_eq ENNReal.inv_two_add_inv_two) ρ hρ hρ1 Boff
  refine ⟨fun Λ => ⟨max 1 (4 * (((Work.KMTAreas.A7.nBound Λ (offBandLog ρ B) + 1 : ℕ)) : ℝ) * Cv),
      le_trans zero_le_one (le_max_left _ _)⟩, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hl₁ hl₂
  set Mv : ℕ := Work.KMTAreas.A7.nBound Λ (offBandLog ρ B) + 1 with hMv
  set X : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
    * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hX
  set off : ℕ → ℤ → ℂ := (fun n x =>
      if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0) with hoff
  -- the support is a finite initial segment
  have hsupp : ∀ n : ℕ, n ∉ Finset.range Mv → off n = 0 := by
    intro n hn
    by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
        ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · exfalso
      have hlt := offBand_lt_nBound hΛ ha ha1 ρ hρ.le P C₀ hLB hc.1 hc.2
      have hnm : Work.KMTAreas.A7.nBound Λ (offBandLog ρ B) + 1 ≤ n := by
        have h1 : ¬ (n < Work.KMTAreas.A7.nBound Λ (offBandLog ρ B) + 1) := by
          simpa only [Finset.mem_range, hMv] using hn
        omega
      omega
    · funext x
      rw [hoff]
      simp only []
      rw [if_neg hc]
      rfl
  -- the per-scale bound
  have hper : ∀ n ∈ Finset.range Mv,
      4 * MeasureTheory.eLpNorm (off n) 1 MeasureTheory.Measure.count
        ≤ 4 * (ENNReal.ofReal Cv * X) := by
    intro n _
    by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
        ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · have hguard : Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ))
          (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
          ∧ Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
          ∧ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) := hc.1
      obtain ⟨hl₁B, hl₂B, hk₁B, hk₂B⟩ := le_of_lcL_le hLB
      have hNle : Nat.floor (a n) ≤ 2 ^ Boff := by
        have hlog := logN_toNat_lt_of_not_bandCond ρ hρ.le hLB hc.2
        exact le_trans (le_two_pow_of_logN_toNat_lt hlog)
          (Nat.pow_le_pow_right (by norm_num) (le_max_right B (offBandLog ρ B)))
      have hmain : ∀ x : ℤ,
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            = Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree
                (((Nat.floor (a n) : ℕ)) : NNReal) f g l₁ l₂ k₁ k₂ x := by
        intro x
        rw [Work.KMTAreas.A7.mainPartTuple, if_pos hguard]
        simp only [Work.Analysis.EndVar.varpPiece, AhalfR, Nat.floor_natCast]
      have hmodel : Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
        funext x
        rw [Work.KMTAreas.A7.modelTupleRep, if_neg (fun h => hc.2 h.2.2.2), Pi.zero_apply]
      have hunf : off n = fun x : ℤ =>
          Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree
            (((Nat.floor (a n) : ℕ)) : NNReal) f g l₁ l₂ k₁ k₂ x := by
        funext x
        rw [hoff]
        simp only []
        rw [if_pos hc]
        rw [hmain x, congrFun hmodel x, Pi.zero_apply, sub_zero]
      have hb := hCvB l₁ l₂ k₁ k₂ (Nat.floor (a n)) f g
        (le_trans hl₁B (le_max_left B (offBandLog ρ B)))
        (le_trans hl₂B (le_max_left B (offBandLog ρ B)))
        (le_trans hk₁B (le_max_left B (offBandLog ρ B)))
        (le_trans hk₂B (le_max_left B (offBandLog ρ B))) hNle
      rw [inv_two_add_inv_two_inv] at hb
      rw [hunf, hX]
      exact mul_le_mul' le_rfl hb
    · have hzero : off n = 0 := by
        funext x
        rw [hoff]
        simp only []
        rw [if_neg hc]
        rfl
      rw [hzero, MeasureTheory.eLpNorm_zero, hX]
      simp
  -- the finite spike-sum bound
  have hsum1 := Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_sum
    (μ := MeasureTheory.Measure.count) (r := r) (p := (1 : ENNReal)) hr1 le_rfl
    (s := Finset.range Mv) hsupp
    (fun n _ => (measurable_of_countable (off n)).aestronglyMeasurable)
  refine hsum1.trans ?_
  refine (Finset.sum_le_sum (fun n hn => hper n hn)).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hX]
  have hscalar : ((Mv : ℕ) : ℝ) * (4 * Cv)
      ≤ max 1 (4 * (((Work.KMTAreas.A7.nBound Λ (offBandLog ρ B) + 1 : ℕ)) : ℝ) * Cv) := by
    rw [hMv]
    exact le_trans (le_of_eq (by ring)) (le_max_right _ _)
  rw [mul_assoc]
  exact Work.KMTAreas.A7.term_sum_le Mv Cv
    (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) hscalar

end

end Work.KMTPlan.A6.PieceBoundedH
