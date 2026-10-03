/-
# The uniform `ℓ²` bound for the §5 frequency pieces on a rectangle of scales

`Work.KMTPlan.A6.pieceL2BoundRect`: for **fixed** bounds `l ≤ B₀` on the dyadic scale and
`|κ s|, |κ (s-1)| ≤ KB` on the two frequency scales occurring in the piece
`piece (kmtPj ρ) l κ a s f`, there is a constant `C = C(ρ, B₀, KB) > 0` with

`‖piece (kmtPj ρ) l κ a s f‖_{ℓ²} ≤ C ‖f‖_{ℓ²}`   for every `f`.

This is the crude (`ℓ² → ℓ²`) bound used when the number of relevant scales is *finite*: the
constant is allowed to depend on the rectangle `[0,B₀] × [-KB,KB]` of parameters but not on the
individual `(l, κ, a, s)`.  It is proved from the single-scale projection bound
`Work.KMTAreas.A7.KmtProjCrude` (`‖Π_{l,≤k} f‖_{ℓ²} ≤ C_{l,k} ‖f‖_{ℓ²}`) by taking the maximum of
the finitely many constants `C_{l,k}` over the rectangle, then the triangle inequality written in
`A6/HHAux.lean` as `crude_piece_of`.

No hypothesis on `ρ` (in particular no smallness) is needed: `ρ` is a fixed parameter of the
statement, and all the oscillation in `ρ` is absorbed in the constant.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.HHAux
import Submission.Work.KMTAreas.A7.KmtProjCrude

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar

/-- **The single-scale `ℓ²` bound.**  For every pair of parameters `(l,k)` the projection
`kmtProj ρ l k` is bounded on `ℓ²`; the constant is the one supplied by
`Work.KMTAreas.A7.KmtProjCrude` at `q = 2`. -/
theorem exists_eLpNorm_kmtProj_two_le (ρ : ℝ) (p : ℕ × ℤ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : ℤ → ℂ,
      eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := Work.KMTAreas.A7.KmtProjCrude (ρ := ρ) p.1 p.2 (q := 2) (by norm_num)
  exact ⟨C, hCpos, fun f => by simpa using hC f⟩

/-- **The uniform `ℓ²` bound on a finite rectangle of parameters.**  The maximum of the finitely
many single-scale constants dominates each of them. -/
theorem exists_eLpNorm_kmtProj_two_le_finset (ρ : ℝ) (S : Finset (ℕ × ℤ)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ p ∈ S, ∀ f : ℤ → ℂ,
      eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
        ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count := by
  classical
  choose C _hCpos hC using fun p : ℕ × ℤ => exists_eLpNorm_kmtProj_two_le ρ p
  refine ⟨max (S.sup C) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp f
  refine (hC p f).trans ?_
  gcongr
  exact le_trans (Finset.le_sup hp) (le_max_left _ _)

/-- **The uniform `ℓ²` bound for the §5 frequency pieces on a rectangle of scales.**  With `l ≤ B₀`
and both frequency scales `κ s`, `κ (s-1)` in `[-KB, KB]`, the piece `piece (kmtPj ρ) l κ a s f` is
bounded on `ℓ²` by a constant depending only on `(ρ, B₀, KB)`. -/
theorem pieceL2BoundRect (ρ : ℝ) (B₀ KB : ℕ) :
    ∃ C : NNReal, 0 < C ∧ ∀ (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) (f : ℤ → ℂ),
      l ≤ B₀ → κ s ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ) →
      κ (s - 1) ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ) →
      MeasureTheory.eLpNorm (Work.Analysis.EndVar.piece (Work.KMTContract.kmtPj ρ) l κ a s f) 2
          MeasureTheory.Measure.count
        ≤ (C : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ :=
    crude_piece_of exists_eLpNorm_kmtProj_two_le_finset ρ (max B₀ KB) KB
  refine ⟨C, hCpos, ?_⟩
  intro l κ a s f hl hs hs1
  refine hC l κ a s f (le_trans hl (le_max_left _ _)) ?_
  intro t ht
  rcases ht with hts | hts
  · subst hts
    exact ⟨(Finset.mem_Icc.mp hs).1,
      le_trans (Finset.mem_Icc.mp hs).2 (by exact_mod_cast le_max_right B₀ KB)⟩
  · subst hts
    exact ⟨(Finset.mem_Icc.mp hs1).1,
      le_trans (Finset.mem_Icc.mp hs1).2 (by exact_mod_cast le_max_right B₀ KB)⟩

end

end Work.KMTPlan.A6
