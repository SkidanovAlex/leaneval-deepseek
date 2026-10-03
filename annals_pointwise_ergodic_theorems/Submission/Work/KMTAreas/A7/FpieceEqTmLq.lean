import Mathlib
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.A5.Basic

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

/-! ## The `G` analogue of the func-calculus identity, for bounded input

`FpieceEqTm_of_bounded` (`A7/FpieceEqTm.lean`) is the `F` half of the func-calculus identity for
bounded input.  The `G` half is the same argument with the scale function
`κ s = d * (-(logN N) + s)` of `Gpiece` in place of `κ s = -(logN N) + s`: the only difference is
that the `periodize`-of-the-symbol identity has to be extracted from `pieceSymG`, which is where the
`d *` sits inside the cutoff. -/

/-- **The func-calculus identity for the `G` piece**, for bounded input: the exact-height piece
`Gpiece (kmtPj ρ) d 0 l s N f` is the `diffFreqs ρ l` multiplier with symbol `pieceSymG d s N`. -/
theorem GpieceEqTm_of_bounded {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℤ) (l s N : ℕ)
    (f : ℤ → ℂ) {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Gpiece (kmtPj ρ) d 0 l (s : ℤ) N f = Tm ρ l (pieceSymG d s N) f := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have hL : Gpiece (kmtPj ρ) d 0 l (((0 : ℕ) : ℤ)) N f
        = piExact (kmtPj ρ) l (d * (-(logN N))) f := by
      simp only [Gpiece, piece]
      split_ifs with h
      · simp
      · exact absurd (by simp) h
    have hR : pieceSymG d 0 N = etaCut kmtEta (d * (-(logN N))) := by
      funext ξ
      simp only [pieceSymG]
      simp
    have hTm : Tm ρ l (pieceSymG d 0 N) f
        = iwConv (diffFreqs ρ l) (periodize (etaCut kmtEta (d * (-(logN N))))) f := by
      simp only [Tm, hR]
    rw [hL, hTm]
    exact piExact_eq_iwConv_diffFreqs ρ hρ hρ1 l (d * (-(logN N))) f hB
  · have hL : Gpiece (kmtPj ρ) d 0 l (s : ℤ) N f
        = piExact (kmtPj ρ) l (d * (-(logN N) + (s : ℤ))) f
          - piExact (kmtPj ρ) l (d * (-(logN N) + ((s : ℤ) - 1))) f := by
      simp only [Gpiece, piece]
      split_ifs with h
      · exact absurd (by simpa using h) hs
      · rfl
    have hsym : periodize (pieceSymG d s N)
        = periodize (etaCut kmtEta (d * (-(logN N) + (s : ℤ))))
          - periodize (etaCut kmtEta (d * (-(logN N) + ((s : ℤ) - 1)))) := by
      have h1 : pieceSymG d s N
          = fun θ : ℝ => etaCut kmtEta (d * (-(logN N) + (s : ℤ))) θ
              - etaCut kmtEta (d * (-(logN N) + ((s : ℤ) - 1))) θ := by
        funext θ
        simp only [pieceSymG, if_neg hs]
        ring_nf
      rw [h1, periodize_sub_etaCut]
    have hI : Integrable (iwSymbolSet (diffFreqs ρ l)
        (periodize (etaCut kmtEta (d * (-(logN N) + (s : ℤ)))))) circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut _)).integrable le_top
    have hI2 : Integrable (iwSymbolSet (diffFreqs ρ l)
        (periodize (etaCut kmtEta (d * (-(logN N) + ((s : ℤ) - 1)))))) circleMeasure :=
      (memLp_iwSymbolSet _ (memLp_periodize_etaCut _)).integrable le_top
    have hsub : iwConv (diffFreqs ρ l)
          (periodize (etaCut kmtEta (d * (-(logN N) + (s : ℤ))))
            - periodize (etaCut kmtEta (d * (-(logN N) + ((s : ℤ) - 1))))) f
        = iwConv (diffFreqs ρ l) (periodize (etaCut kmtEta (d * (-(logN N) + (s : ℤ))))) f
          - iwConv (diffFreqs ρ l)
              (periodize (etaCut kmtEta (d * (-(logN N) + ((s : ℤ) - 1))))) f :=
      iwConv_sub_of_bounded hB hI hI2
        (summable_iwKernel_diffFreqs ρ hρ hρ1 l (d * (-(logN N) + (s : ℤ))))
        (summable_iwKernel_diffFreqs ρ hρ hρ1 l (d * (-(logN N) + ((s : ℤ) - 1))))
    have hTm : Tm ρ l (pieceSymG d s N) f
        = piExact (kmtPj ρ) l (d * (-(logN N) + (s : ℤ))) f
          - piExact (kmtPj ρ) l (d * (-(logN N) + ((s : ℤ) - 1))) f := by
      simp only [Tm]
      rw [hsym, hsub]
      rw [← piExact_eq_iwConv_diffFreqs ρ hρ hρ1 l (d * (-(logN N) + (s : ℤ))) f hB,
        ← piExact_eq_iwConv_diffFreqs ρ hρ hρ1 l (d * (-(logN N) + ((s : ℤ) - 1))) f hB]
    exact hL.trans hTm.symm

/-- The functional calculus for the §5 pieces, in the form in which the §6 model approximation
uses it: for `0 < ρ ≤ 1`, `1 < q` and `f ∈ ℓ^q(ℤ)`, the exact-height arithmetic projection of §5
agrees with the multiplier whose frequency set is the *difference*
`(ℚ/ℤ)_l \ (ℚ/ℤ)_{l-1}`.  The `MemLp` hypothesis is what makes the two `tsum`s (the `Fpiece` side
is a difference of up to four `tsum`s, the `Tm` side a single one) comparable; `A7/FpieceEqTm.lean`
contains the algebra (`periodize_sub_etaCut`, `iwKernel_iwSymbolSet_sdiff`, `iwArithFreqs_mono`,
`FpieceEqTm_of_bounded`) and the machine-checked refutation of the unconditional form.  The
`MemLp → BoundedZ` bridge is `Work.KMTAreas.A5.boundedZ_of_memLp`. -/
theorem FpieceEqTmLq (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {q : ℝ} (hq : 1 < q) (d : ℤ)
    (l s N : ℕ) {f : ℤ → ℂ} (hf : MemLp f (ENNReal.ofReal q) Measure.count) :
    (Fpiece (kmtPj ρ) 0 l (s : ℤ) N f = Tm ρ l (pieceSymF s N) f) ∧
      (Gpiece (kmtPj ρ) d 0 l (s : ℤ) N f = Tm ρ l (pieceSymG d s N) f) := by
  obtain ⟨C, hC⟩ := Work.KMTAreas.A5.boundedZ_of_memLp (ENNReal.one_lt_ofReal.mpr hq) hf
  exact ⟨FpieceEqTm_of_bounded hρ hρ1 l s N f hC,
    GpieceEqTm_of_bounded hρ hρ1 d l s N f hC⟩

end Work.KMTAreas.A7
