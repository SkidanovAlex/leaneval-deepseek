import Mathlib
import Submission.Work.Lattice.FlagMemberCriterion

/-!
# The §3 flag at the angular ranks of the flow polygon, with the capacity criterion

This module instantiates `MaxPhiFlag.exists_tight_flag` at the §3 flowed lattice
`Λ_t = imageSpan (s.trans (eEquiv ℓ t))` (`s` the orthogonal representative of the plane `x`) and
applies `FlagMemberCriterion.exists_activeBlock_and_effPos_le` to every member.  The result is the
*production interface* of the §3 extraction: at the angular ranks of the flow polygon of `Λ_t`
there is a flag of tight members, and for each member `V s` (of rank `j_s = jb s`) there is a
preimage family `w s` in `Λ₀ = imageSpan s` and a first active block `u s` with

`effPos s ≤ j_s − u_s`.

Module `Submission.Work.Lattice.FlagInstantiation`, namespace `Submission.FlagInstantiation`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.FlagInstantiation

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormPolygon
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.ImageLattice
open Submission.MaxPhiPolygon
open Submission.MaxPhiFlag
open Submission.MaxPhi
open Submission.MaxRankData
open Submission.AngularRanks
open Submission.AngularTightness
open Submission.ActiveBlock
open Submission.MaxCovol
open Submission.LatticePolygon
open Submission.GraysonLattice
open Submission.AccountingOneSided
open Submission.FlagMemberCriterion
open Submission.CnormDataBdd
open Submission.MaxPhiAccounting
open Submission.JoinSubmodularity
open Submission.FlowLatticeImage

variable {d : ℕ}

/-- **The §3 flag with the capacity criterion.** -/
theorem exists_flag_with_criterion {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (s : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ)
    (A : ℝ) (hA : (d : ℝ) * Real.log 2 / 2 < A)
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun x => phiSlope (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A x i.val) t) :
    ∃ (V : {n : ℕ // 1 ≤ n ∧ n < numBlocks d
        (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t)} →
        Submodule ℤ (RD d))
      (hV : ∀ n, V n ≤ imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))),
      (∀ n, Saturated (imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t))) (V n)) ∧
      (∀ n, subDim (V n) =
        blockStart d (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t) n.1) ∧
      (∀ n m, n ≤ m → V n ≤ V m) ∧
      (∀ n, maxPhi (d := d) (imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)))
          (finrank_imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)))
          A (V n) (hV n) =
        maxphiPolygon (d := d) (imageSpan (d := d) ((s : RD d ≃ₗ[ℝ] RD d).trans (eEquiv (d := d) ℓ t)))
          A (subDim (V n))) ∧
      (∀ n, ∃ (w : Fin (subDim (V n)) → RD d) (u : ℕ),
        (∀ i, w i ∈ imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ∧ LinearIndependent ℝ w ∧
        IsFirstActiveBlock (d := d) ℓ (subDim_le_ambient (V n)) t
          (exteriorPower.ιMulti ℝ (subDim (V n)) w) u ∧
        effPos d ℓ (fun m => (blockStart d
            (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t) m : ℝ))
          (phiLevelDeriv (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t
            (blockStart d (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t)))
          n.1 ≤ (subDim (V n) : ℝ) - (u : ℝ) ∧
        Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (w i))) = realSpan (V n)) := by
  classical
  set g : RD d ≃ₗ[ℝ] RD d := (s : RD d ≃ₗ[ℝ] RD d) with hg
  set H : Submodule ℤ (RD d) := imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)) with hH
  have hfin : Module.finrank ℤ H = d := by
    rw [hH]; exact finrank_imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))
  have hBdd : ∀ (j : ℕ) (hjd : j ≤ d), BddBelow (maxRankDataSet (d := d) H j hjd) := by
    intro j hjd
    by_cases hj1 : 1 ≤ j
    · rw [hH]
      exact bddBelow_maxRankDataSet_imageSpan (d := d) hℓ0 hℓd hjd hj1 s t
    · have hj0 : j = 0 := by omega
      subst hj0
      exact bddBelow_maxRankDataSet_zero (d := d) H (Nat.zero_le d)
  obtain ⟨V, hV, hVsat, hVspec, hVmono⟩ :=
    exists_tight_flag H hfin hA hBdd
  -- transport the flag to the angular ranks of the flow polygon
  have hN : numBlocks d (maxphiPolygon (d := d) H A) =
      numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t) := by
    rw [hH]
    exact (numBlocks_phiPolygonT_eq (d := d) g ℓ t A).symm
  have hidx : ∀ n : {m : ℕ // 1 ≤ m ∧ m < numBlocks d
      (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t)},
      n.1 < numBlocks d (maxphiPolygon (d := d) H A) := by
    intro n
    rw [hN]
    exact n.2.2
  let idx := fun n : {m : ℕ // 1 ≤ m ∧ m < numBlocks d
      (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t)} =>
    (⟨n.1, n.2.1, hidx n⟩ :
      {m : ℕ // 1 ≤ m ∧ m < numBlocks d (maxphiPolygon (d := d) H A)})
  have hbs : ∀ n : {m : ℕ // 1 ≤ m ∧ m < numBlocks d
      (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t)},
      blockStart d (phiPolygonT (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ A t) n.1 =
        blockStart d (maxphiPolygon (d := d) H A) n.1 := by
    intro n
    rw [hH]
    exact blockStart_phiPolygonT_eq (d := d) g ℓ t A n.1
  refine ⟨fun n => V (idx n), fun n => hV (idx n), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hVsat (idx n)
  · intro n
    have hdim := (hVspec (idx n)).1
    rw [hbs n]
    exact hdim
  · intro n m hnm
    exact hVmono (idx n) (idx m) (by dsimp only [idx]; exact hnm)
  · intro n
    have hdim := (hVspec (idx n)).1
    have htight := (hVspec (idx n)).2
    rw [hdim]
    exact htight
  · intro n
    have hdim := (hVspec (idx n)).1
    have htightV := (hVspec (idx n)).2
    have hV1 : 1 ≤ subDim (V (idx n)) := by
      rw [hdim]
      exact le_trans n.2.1 (blockStart_n_ge d (maxphiPolygon (d := d) H A) n.1
        (le_trans (Nat.le_of_lt (hidx n)) (numBlocks_le _)))
    have hV0 : V (idx n) ≠ ⊥ := by
      intro hbot
      have h1 : subDim (V (idx n)) = 0 := by
        rw [hbot]
        exact (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (RD d))).mpr rfl
      omega
    have htightData : maxPhi (d := d) H hfin A (V (idx n)) (hV (idx n)) =
        maxphiData (d := d) H A (subDim (V (idx n))) := by
      have hang := maxphiPolygon_eq_data_at_angular H hfin A n.2.1 (hidx n)
      rw [htightV]
      simpa [hdim] using hang
    have hbdd : ∀ x, BddBelow (flowMaxDataSet (d := d) (imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d))
        ℓ x (subDim (V (idx n))) (subDim_le_ambient (V (idx n)))) := fun x =>
      bddBelow_flowMaxDataSet_imageSpan (d := d)
        (j := subDim (V (idx n))) (ℓ := ℓ) hℓ0 hℓd (subDim_le_ambient _) hV1 s x
    obtain ⟨w, u, hwmem, hwli, hu, hle, hspan⟩ :=
      exists_activeBlock_and_effPos_le (d := d) hℓ0 hℓd g t A (hV (idx n)) hV0 hV1 htightData hbdd
        hdiff (s := n.1) n.2.1 n.2.2 (by rw [hbs n]; exact hdim.symm)
    exact ⟨w, u, hwmem, hwli, hu, hle, hspan⟩

end Submission.FlagInstantiation

end
