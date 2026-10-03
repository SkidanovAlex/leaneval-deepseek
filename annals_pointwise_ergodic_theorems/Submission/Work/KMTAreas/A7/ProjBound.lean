/-
# Lemma `iw-prop`(i) for the concrete KMT Ionescu--Wainger projections

Combining the `q ≥ 2` multiplier bounds (`A7/EtaProjGeTwo.lean`) with the duality argument of
`A7/ProjLq.lean` and the extension from finitely supported functions to all of `ℓ^p`
(`A7/ProjLq.lean`), this file records the boundedness half of Lemma `iw-prop` of
Krause--Mirek--Tao in the form in which the §5--§8 analysis of the area-`A7` development uses it:

  `GoodMajorArcs ρ Cρ l k → ‖kmtProj ρ l k f‖_{ℓ^p} ≤ C_{ρ,p} ⟨l⟩ ‖f‖_{ℓ^p}`,  `1 < p < ∞`,

for arbitrary `f : ℤ → ℂ` (both sides may be infinite).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ProjLq
import Submission.Work.KMTAreas.A7.EtaProjGeTwo
import Submission.Work.KMTAreas.A7.EtaMult

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **Lemma `iw-prop`(i)** for the concrete projections `kmtProj ρ l k = Π_{≤l,≤k}`: on good
major arcs the projection is bounded on `ℓ^p(ℤ)` with norm `≲_{ρ,p} ⟨l⟩`, for every real exponent
`p > 1`, and for *arbitrary* `f` (no finite-support hypothesis; the bound is trivial when
`f ∉ ℓ^p`). -/
theorem kmtProj_lp_bound (hG : GeTwoBounds) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {p : ℝ} (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ f : ℤ → ℂ,
        eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal p) Measure.count
          ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
              * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hb⟩ := iwLqBound_etaCut_ofreal hG hρ hρ1 hp
  refine ⟨Cρ, hCρ, C, hC, fun l k hgood f => ?_⟩
  have hb' := hb l k hgood
  have hpos : (0 : NNReal) < C * angleBracket l := mul_pos hC (angleBracket_pos l)
  refine (eLpNorm_kmtProj_le_of_IWLqBound l k hp hpos hb' f).trans (le_of_eq ?_)
  rw [NNReal.coe_mul, ENNReal.ofReal_mul (by positivity)]

/-- `GeTwoBounds` follows from area `A1` and the crude multiplier bound for the KMT cutoff
(`EtaMult`). -/
theorem geTwoBounds_holds (hA1 : Work.KMTContract.AreaA1) : GeTwoBounds := by
  obtain ⟨M, hM, hMbound⟩ := EtaMult
  exact EtaProjGeTwo hA1 hM hMbound

/-- **Lemma `iw-prop`(i) for the KMT projections, unconditionally from area `A1`.** -/
theorem kmtProj_lp_bound_holds (hA1 : Work.KMTContract.AreaA1) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ℝ), 1 < p →
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
        ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ f : ℤ → ℂ,
          eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal p) Measure.count
            ≤ ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
                * eLpNorm f (ENNReal.ofReal p) Measure.count :=
  fun ρ hρ hρ1 p hp => kmtProj_lp_bound (geTwoBounds_holds hA1) hρ hρ1 hp

end Work.KMTAreas.A7
