import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Serre.C1SphOne
import Submission.Work.Serre.C1Loop
import Submission.Work.Serre.sphOneAspherical
import Submission.Work.Stems.homotopyGroup_prod
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.EMFG.torusDefs
import Submission.Work.EMFG.piSubtypeHomeo
import Submission.Work.EMFG.contractibleSpace_pi
import Submission.Work.EMFG.circlePatch_isGoodFam

/-!
# EMFG — the torus `(S¹)^r` has finitely generated homology and is a `K(ℤ^r, 1)`

Target (`Work.EMFG.torusFGandEM`): for every `r`, the `r`-torus `Fin r → Sph 1` has finitely
generated integral homology in every degree, and is a range model of `K(ℤ^r, 1)` in every range.

## Homology finiteness

`S¹` carries the good cover `circlePatch : Fin 4 → Set (Sph 1)` (`Work.EMFG.circlePatch_isGoodFam`):
the four open semicircles `±e₀ > 0`, `±e₁ > 0`.  The product pieces
`torusPatch r η = Set.pi Set.univ (fun i => circlePatch (η i))` (`η : Fin r → Fin 4`) are then a good
cover of the torus: a finite intersection is `Set.pi Set.univ (fun i => ⋂_η circlePatch (η i))`,
which is homeomorphic (through `Work.EMFG.piSubtypeHomeo`) to the product of the coordinate
intersections, each of which is a finite intersection of `circlePatch`es and therefore contractible;
a product of contractible spaces is contractible (`Work.EMFG.contractibleSpace_pi`).
`Work.ThomBordism.finiteHomology_of_goodFam` then gives finite generation.

## The `K(ℤ^r,1)` statement

`S¹` is a range model of `K(ℤ,1)`: `π₁(S¹) ≅* ℤ` (`Work.Serre.pi1SphOne_addEquiv_int`), `π₀(S¹)`
is trivial (path connectedness) and `π_i(S¹) = 0` for `i ≥ 2` (`Work.Serre.sphOneAspherical`).  The
`Fin r`-fold product of range models is again a range model
(`Work.RatHurewicz.isEMSpaceUpTo_pi_fin`), and `π₁((S¹)^r) = ℤ^r`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped Topology

namespace Work.EMFG

noncomputable section

/-! ## The circle is a range model of `K(ℤ,1)` -/

theorem sphOne_isEMSpaceUpTo (N : ℕ) :
    Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N (Work.Serre.Sph 1) Work.Serre.sphOneBase := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Work.Serre.pi1SphOne_addEquiv_int Work.Serre.sphOneBase
    exact ⟨(Work.Serre.multiplicativeAdditiveSelf _).symm.trans (AddEquiv.toMultiplicative e)⟩
  · intro i hi hc
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      haveI : PathConnectedSpace (Work.Serre.Sph 1) := Work.Serre.sphOnePathConnected
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Work.Serre.Sph 1)
        (x := Work.Serre.sphOneBase)).subsingleton
    · exact Work.Serre.sphOneAspherical i (by omega) Work.Serre.sphOneBase

/-- **The `r`-torus `(S¹)^r` is a range model of `K(ℤ^r, 1)` in every range.** -/
theorem torusEM (r : ℕ) (N : ℕ) :
    Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) 1 (by norm_num) N
      (Fin r → Work.Serre.Sph 1) (fun _ => Work.Serre.sphOneBase) :=
  Work.RatHurewicz.isEMSpaceUpTo_pi_fin (A := ℤ) (k := 1) (N := N) (by norm_num) r
    Work.Serre.sphOneBase (sphOne_isEMSpaceUpTo N)

/-! ## The product pieces of the circle's good cover are a good cover of the torus -/

theorem torusPatch_isGoodFam (r : ℕ) :
    Work.ThomBordism.IsGoodFam (torusPatch r) ∧ (⋃ η, torusPatch r η) = Set.univ := by
  obtain ⟨hVgood, hVcov⟩ := circlePatch_isGoodFam
  constructor
  · refine ⟨?_, ?_⟩
    · intro η
      have h1 : torusPatch r η =
          ⋂ i : Fin r, {f : Fin r → Work.Serre.Sph 1 | f i ∈ circlePatch (η i)} := by
        ext f
        simp only [torusPatch, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_iInter,
          Set.mem_ofPred_eq]
      rw [h1]
      exact isOpen_iInter_of_finite (fun i => (hVgood.1 (η i)).preimage (continuous_apply i))
    · intro β _ f b hne
      have hset : (⋂ i : β, torusPatch r (f i)) =
          Set.pi Set.univ (fun k : Fin r => ⋂ i : β, circlePatch (f i k)) := by
        ext g
        simp only [Set.mem_iInter, mem_torusPatch, Set.mem_pi, Set.mem_univ, true_implies]
        exact ⟨fun h k i => h i k, fun h i k => h k i⟩
      rw [hset]
      have hW : ∀ k : Fin r, ContractibleSpace ↥(⋂ i : β, circlePatch (f i k)) := by
        intro k
        obtain ⟨g, hg⟩ := hne
        have h2 : ∀ i : β, g ∈ torusPatch r (f i) := Set.mem_iInter.mp hg
        refine hVgood.2 β (fun i => f i k) b ?_
        refine ⟨g k, ?_⟩
        simp only [Set.mem_iInter]
        intro i
        exact (mem_torusPatch.mp (h2 i)) k
      obtain ⟨e⟩ := piSubtypeHomeo (fun k : Fin r => ⋂ i : β, circlePatch (f i k))
      haveI := contractibleSpace_pi hW
      exact e.contractibleSpace
  · rw [Set.eq_univ_iff_forall]
    intro g
    rw [Set.mem_iUnion]
    have hg : ∀ i, ∃ j, g i ∈ circlePatch j := by
      intro i
      have h1 : g i ∈ (⋃ j, circlePatch j) := by rw [hVcov]; exact Set.mem_univ _
      exact Set.mem_iUnion.mp h1
    choose η hη using hg
    exact ⟨η, by rw [mem_torusPatch]; exact hη⟩

/-! ## The homology of the torus is finitely generated -/

theorem torusFG (r : ℕ) : ∀ N : ℕ, Work.PiS.FGUpTo (Fin r → Work.Serre.Sph 1) N := by
  intro N
  obtain ⟨hgood, hcov⟩ := torusPatch_isGoodFam r
  let e := Fintype.equivFin (Fin r → Fin 4)
  have hgood' : Work.ThomBordism.IsGoodFam
      (fun k : Fin (Fintype.card (Fin r → Fin 4)) => torusPatch r (e.symm k)) :=
    Work.ThomBordism.fgch_isGoodFam_comp hgood (fun k => e.symm k)
  have hcov' : (⋃ k : Fin (Fintype.card (Fin r → Fin 4)),
      torusPatch r (e.symm k)) = Set.univ := by
    rw [← hcov]
    ext g
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨k, hk⟩ => ⟨e.symm k, hk⟩, fun ⟨η, hη⟩ => ⟨e η, by simpa using hη⟩⟩
  intro i hi
  exact Work.ThomBordism.finiteHomology_of_goodFam (Fintype.card (Fin r → Fin 4))
    (Fin r → Work.Serre.Sph 1) (fun k => torusPatch r (e.symm k)) hgood' hcov' i

/-- **The `r`-torus `(S¹)^r` has finitely generated integral homology and is a range model of
`K(ℤ^r, 1)` in every range.** -/
theorem torusFGandEM (r : ℕ) :
    (∀ N : ℕ, Work.PiS.FGUpTo (Fin r → Work.Serre.Sph 1) N) ∧
      (∀ N : ℕ, Work.Serre.IsEMSpaceUpTo (Fin r → ℤ) 1 (by norm_num) N
        (Fin r → Work.Serre.Sph 1) (fun _ => Work.Serre.sphOneBase)) :=
  ⟨torusFG r, fun N => torusEM r N⟩

end

end Work.EMFG
