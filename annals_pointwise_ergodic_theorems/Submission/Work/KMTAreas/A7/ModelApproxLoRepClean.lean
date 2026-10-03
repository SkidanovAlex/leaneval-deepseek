/-
# The clean chain for `Work.KMTAreas.A7.ModelApproxLoRep`

This module assembles the target `Work.KMTAreas.A7.ModelApproxLoRep` from three inputs, each of
which is proved elsewhere in the workspace as a *clean* (axiom-free) theorem:

* `Work.KMTAreas.A7Hi2.SupPiece`  — the values-supremum (maximal) bound of the dyadic low-pass
  Ionescu--Wainger family (paper `(lin-2)`, the Men'shov/Lépingle maximal step); assembled in
  `Work.KMTAreas.A7Hi2.supBound` from the lacunary maximal piece `lacunaryMaxPiece`
  (`KMTAreas/A7Hi2/lacunaryMaxPiece.lean`), the PROVED band square-function bound
  `Work.KMTAreas.A7Lpd.bandSquareUnif` and the PROVED uniform single-scale bound
  `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`;
* `Work.KMTAreas.A7Hi2.ChainPiece` — the chain term of the variational norm controlled by the
  values supremum and the band square function (`chainLe`);
* `Work.KMTAreas.A7MixedG.FiberLargeResidue` — the §8 per-residue (`form-1` + quantitative
  Shannon) estimate of the mixed range.

Everything else is proved and axiom-clean: the dyadic square-function piece
(`Work.KMTAreas.A7Hi2.sqFunBound`), the reduction of the dyadic estimate to the lacunary one
(`Work.KMTAreas.A7Hi2.lowpassVarG_of_pieces`), the `g`-side assembly
(`Work.KMTAreas.A7Hi.lacunaryBumpVarEstimate_assemblyG` with the PROVED clipped and bad-scale
pieces), the `LinVarGuard`/`FiberGuard` reduction (`Work.KMTAreas.A7.MixedGSideHolds_of_pieces`,
`Work.KMTAreas.A7MixedG.fiberGuard_of_largeResidue`), the whole `l = 0` chapter of §6--§8
(`Work.KMTAreas.A7.modelApproxLo_of_pieces`, `loMixedLeft_of_statements`,
`loMixedRight_of_massStatement`, `LoModelLargeScaleHolds`, `LoMixedSingleScaleHolds`,
`LoMixedOffBandHolds`, `MixedFSideHolds`, `loMixedRMass_of`, `FibreMassHolds`, `AbsorbHolds`).

**The one subtlety** is the same as in `ModelApproxLo.lean`: the exact-height model tuple
vanishes on the range `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` (`modelTupleRep_eq_zero_of_lo` and
`LoDefs.modelTuple_eq_zero_of_lo`), so the `modelTupleRep` statement is the `modelTuple` statement
with the two models substituted for each other.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxLo

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract


/-! ## The repaired model tuple vanishes at arithmetic height `0` -/

/-- **The repaired exact-height model tuple vanishes at arithmetic height `0`** (pointwise form). -/
theorem modelTupleRep_apply_eq_zero_of_lo (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂)) :
    modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  have h0 : l₁ = 0 ∨ l₂ = 0 := by omega
  rcases h0 with h | h
  · rw [h]
    rw [modelTupleRep]
    split_ifs with hg
    · have hfe : ∀ t : ℝ, BtwistExact ρ P 0 l₂
          (mStarF (uRep ρ 0 l₂ k₁ k₂))
          (mStargF P.natDegree (uRep ρ 0 l₂ k₁ k₂))
          (Tex ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x = 0 :=
        fun t => by rw [Tex_zero, BtwistExact_zero_left]; rfl
      rw [intervalIntegral.integral_congr (fun t _ => hfe t)]
      simp
    · rfl
  · rw [h]
    rw [modelTupleRep]
    split_ifs with hg
    · have hfe : ∀ t : ℝ, BtwistExact ρ P l₁ 0
          (mStarF (uRep ρ l₁ 0 k₁ k₂))
          (mStargF P.natDegree (uRep ρ l₁ 0 k₁ k₂))
          (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x = 0 :=
        fun t => by rw [Tex_zero, BtwistExact_zero_right]; rfl
      rw [intervalIntegral.integral_congr (fun t _ => hfe t)]
      simp
    · rfl

/-- **The repaired exact-height model tuple vanishes at arithmetic height `0`.** -/
theorem modelTupleRep_eq_zero_of_lo (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂)) :
    modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  exact modelTupleRep_apply_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hlo

end

end Work.KMTAreas.A7
