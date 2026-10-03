import Mathlib
import Submission.Work.KMTPlan.A6.HHBasic
import Submission.Work.KMTAreas.A7.KmtProjCrude

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal

/-- **A finite family of Ionescu--Wainger projections obeys a uniform `ℓ²` bound.**

The crude convolution bound `Work.KMTAreas.A7.KmtProjCrude` gives, for every *single* pair of
parameters `(l,k)`, a constant `C(ρ,l,k) > 0` with `‖Π_{≤l,≤k} f‖_{ℓ²} ≤ C(ρ,l,k) ‖f‖_{ℓ²}`
(the kernel of `Π_{≤l,≤k}` decays like `j^{-2}`, hence is in `ℓ¹`, and Young's inequality at the
endpoint `p = 1` gives the bound).  Since `S` is finite, taking the maximum of these constants
over `p ∈ S` (and adding `1` to keep it positive, which also handles the empty family) produces a
single constant working simultaneously for all `p ∈ S`.  This is the uniformity in the parameters
that one needs in order to handle a finite family of projections at once. -/
theorem kmtProj_l2_bound_finset (ρ : ℝ) (S : Finset (ℕ × ℤ)) :
    ∃ C : NNReal, 0 < C ∧ ∀ p ∈ S, ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ p.1 p.2 f) 2 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  -- For each pair of parameters, the crude kernel bound at the exponent `q = 2`.
  have h : ∀ p : ℕ × ℤ, ∃ C : NNReal, 0 < C ∧ ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ p.1 p.2 f) (ENNReal.ofReal 2)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (C : ℝ)
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
    fun p => Work.KMTAreas.A7.KmtProjCrude (ρ := ρ) p.1 p.2 (q := 2) (by norm_num)
  -- The constants `c p`, extracted by choice.
  set c : ℕ × ℤ → NNReal := fun p => Classical.choose (h p) with hc
  have hcbd : ∀ p : ℕ × ℤ, ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ p.1 p.2 f) (ENNReal.ofReal 2)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (c p : ℝ)
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
    fun p => (Classical.choose_spec (h p)).2
  -- The exponent `2` and the coercion `ℝ≥0 → ℝ≥0∞` rewritten in the form the bound uses.
  have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  have hcoe : ∀ r : NNReal, ((r : ENNReal)) = ENNReal.ofReal (r : ℝ) :=
    fun r => (@ENNReal.ofReal_coe_nnreal r).symm
  refine ⟨S.sup c + 1, by simp, ?_⟩
  intro p hp f
  have hcp : c p ≤ S.sup c + 1 := le_trans (Finset.le_sup hp) (le_add_right le_rfl)
  calc MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ p.1 p.2 f) 2 MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ p.1 p.2 f) (ENNReal.ofReal 2)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by rw [htwo]
    _ ≤ ENNReal.ofReal (c p : ℝ)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2)
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := hcbd p f
    _ = (c p : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
          rw [htwo, ← hcoe (c p)]
    _ ≤ ((S.sup c + 1 : NNReal) : ENNReal) * MeasureTheory.eLpNorm f 2
          MeasureTheory.Measure.count :=
          mul_le_mul_left (ENNReal.coe_le_coe.mpr hcp) _

end Work.KMTPlan.A6
