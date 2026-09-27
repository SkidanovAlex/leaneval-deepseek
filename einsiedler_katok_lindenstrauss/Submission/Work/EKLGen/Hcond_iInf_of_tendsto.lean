import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLGen.tendsto_Hcond_iSup_univ
import Submission.Work.EKLC6Core.Hcond_mono

/-!
# `Hcond (⨆ l, m l) = ⨅ l, Hcond (m l)` for a monotone sequence of σ-algebras

`Hcond μ P m = ∫ ∑ᵢ -𝔼[1_{Pᵢ}|m] log 𝔼[1_{Pᵢ}|m] dμ` is the conditional entropy of the finite
partition `P` given the σ-algebra `m`.  It is antitone in `m`, and Lévy's upward theorem gives
*continuity from above*: for a monotone sequence `m : ℕ → MeasurableSpace X` of sub-σ-algebras of
`mX` with `⨆ l, m l = mtop`, the values `Hcond μ P (m l)` decrease to `Hcond μ P mtop`.  Hence the
value at the supremum is the infimum of the approximating values.

The Lévy input is `Work.EKLGen.tendsto_Hcond_iSup_univ` (the universe-general form of the already
proved `Work.EKLComp.Hpart.tendsto_Hcond_iSup`); the reduction of the limit statement to the
infimum is `tendsto_atTop_ciInf` together with the monotonicity `Hcond_mono`.
-/

namespace Work.EKLGen

open MeasureTheory Filter Topology

theorem Hcond_iInf_of_tendsto {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : @Work.EKLContract.FinPart X mX)
    (m : ℕ → MeasurableSpace X) (mtop : MeasurableSpace X)
    (hmono : Monotone m) (hmX : ∀ l, m l ≤ mX) (hmXle : mtop ≤ mX) (hsup : (⨆ l, m l) = mtop) :
    @Work.EKLContract.Hcond X mX μ P mtop = ⨅ l, @Work.EKLContract.Hcond X mX μ P (m l) := by
  -- `Hcond μ P (m ·)` is antitone because `Hcond` is antitone in the conditioning σ-algebra.
  have hanti : Antitone (fun l => @Work.EKLContract.Hcond X mX μ P (m l)) :=
    fun i j hij => Work.EKLC6Core.Hcond_mono (mX := mX) μ P (m i) (m j) (hmono hij)
  -- `m l ≤ ⨆ l, m l = mtop`, hence `Hcond μ P mtop ≤ Hcond μ P (m l)`.
  have hle_top : ∀ l, m l ≤ mtop := fun l => by rw [← hsup]; exact le_iSup m l
  have htop_le : ∀ l, @Work.EKLContract.Hcond X mX μ P mtop
      ≤ @Work.EKLContract.Hcond X mX μ P (m l) :=
    fun l => Work.EKLC6Core.Hcond_mono (mX := mX) μ P (m l) mtop (hle_top l)
  refine le_antisymm (le_ciInf htop_le) ?_
  -- For the reverse inequality, use the convergence `Hcond μ P (m l) → Hcond μ P (⨆ l, m l)`.
  have hbdd : BddBelow (Set.range (fun l => @Work.EKLContract.Hcond X mX μ P (m l))) :=
    ⟨_, by rintro _ ⟨l, rfl⟩; exact htop_le l⟩
  have h1 : Tendsto (fun l => @Work.EKLContract.Hcond X mX μ P (m l)) atTop
      (nhds (⨅ l, @Work.EKLContract.Hcond X mX μ P (m l))) :=
    tendsto_atTop_ciInf hanti hbdd
  have h2 : Tendsto (fun l => @Work.EKLContract.Hcond X mX μ P (m l)) atTop
      (nhds (@Work.EKLContract.Hcond X mX μ P mtop)) := by
    have h := tendsto_Hcond_iSup_univ (mX := mX) μ P m hmono hmX
    rwa [hsup] at h
  exact le_of_eq (tendsto_nhds_unique h1 h2)

end Work.EKLGen
