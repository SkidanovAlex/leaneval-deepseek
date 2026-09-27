import Mathlib
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.finite_nearStab

/-!
# Finiteness of the normal part of a discrete subgroup at the geodesic stratum

For a discrete subgroup `C ≤ PO (1+m) 1`, the set of normal isometries
`R : E m ≃ₗᵢ[ℝ] E m` for which the block element `blk 1 m 1 R` lies in `C` is finite.

The proof is short: `blk 1 m 1 R` acts by `R` on the normal fibre and by `1` on the
stratum, hence fixes the base point `0 : E (1+m)` of the chart.  So the set of such
elements is contained in `{γ ∈ C | hdist 0 (γ • 0) ≤ 0}`, which is finite by
`finite_nearStab` (properness of the orbit map for a discrete subgroup).  As
`R ↦ blk 1 m 1 R` is injective (`blk_hom`), the set of `R` is finite too.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The block element `blk 1 m 1 R` (identity on the geodesic foot, `R` on the normal
fibre) fixes the base point `0 : E (1+m)` of the chart. -/
lemma blk_one_one_fixes_zero (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : E m ≃ₗᵢ[ℝ] E m) :
    blk 1 m (1 : PO 1 1) R • (0 : E (1 + m)) = 0 := by
  have h0 : fermi 1 m (0 : E 1) (0 : E m) = (0 : E (1 + m)) := by
    simp [fermi]
    funext i
    exact Fin.addCases (fun j => by simp [Fin.append]) (fun j => by simp [Fin.append]) i
  have hOne : ∀ u : E 1, (1 : PO 1 1) • u = u := hA1.2.2.2.1
  rw [← h0, blk_smul_fermi 1 m hA1 hI1 hA hI (1 : PO 1 1) R (0 : E 1) (0 : E m), hOne]
  simp [h0]

theorem blockNormalPartFinite (m : ℕ) (hm : 0 < m)
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (C : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (hdisc : IsDiscrete (SetLike.coe C)) :
    {R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m | Submission.Mostow.blk 1 m 1 R ∈ C}.Finite := by
  have _hm : 0 < m := hm
  -- the map `R ↦ blk 1 m 1 R` is injective (component of `blk_hom`)
  have hinj : Set.InjOn (fun R : E m ≃ₗᵢ[ℝ] E m => blk 1 m (1 : PO 1 1) R) Set.univ := by
    intro R _ R' _ h
    exact ((blk_hom 1 m hA1 hI1 hA hI).2.2 (1 : PO 1 1) (1 : PO 1 1) R R' h).2
  -- the elements of `C` displacing the origin by at most `0` form a finite set
  have hfin :
      {γ : C | hdist (0 : E (1 + m)) ((γ : PO (1 + m) 1) • (0 : E (1 + m))) ≤ 0}.Finite :=
    finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc 0
  have hF : (((↑) : C → PO (1 + m) 1) ''
      {γ : C | hdist (0 : E (1 + m)) ((γ : PO (1 + m) 1) • (0 : E (1 + m))) ≤ 0}).Finite :=
    hfin.image _
  refine (hF.preimage (hinj.mono (fun _ _ => Set.mem_univ _))).subset ?_
  intro R hR
  have hz : hdist (0 : E (1 + m)) (blk 1 m (1 : PO 1 1) R • (0 : E (1 + m))) ≤ 0 := by
    rw [blk_one_one_fixes_zero m hA1 hI1 hA hI R, hdist_self]
  exact ⟨⟨blk 1 m 1 R, hR⟩, hz, rfl⟩

end Work.Mostow
