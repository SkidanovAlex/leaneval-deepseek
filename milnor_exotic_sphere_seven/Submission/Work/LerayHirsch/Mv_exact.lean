import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.LerayHirsch.MvAux.BiprodElem
import Submission.Work.LerayHirsch.MvAux.IsoSquare
import Submission.Work.LerayHirsch.MvAux.HonestDegree
import Submission.Work.LerayHirsch.MvAux.Ladder

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [-instance] AddCommGroup.toIntModule

namespace Work.LerayHirsch

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

/-!
# The exactness of the two-cover Mayer–Vietoris ladder of the Leray–Hirsch induction

`Submission/Work/LerayHirsch/LhTwoCoverDefs.lean` sets up the ladder

  `MvM k --MvF--> MvP k --MvG--> MvQ k --MvD--> MvM (k+1)`

with `MvM k = ∏_{2i ≤ k} H^{k-2i}(B)`, `MvP k = (∏_{2i ≤ k} H^{k-2i}(U)) ⊞ (∏_{2i ≤ k} H^{k-2i}(V))`
and `MvQ k = ∏_{2i ≤ k} H^{k-2i}(U∩V)`: the Mayer–Vietoris sequence of the cover `U ∪ V = B`,
*with coefficients in the free module on the powers of the hyperplane class*.  This module proves
that it is exact in every degree, and that `MvF` is injective in degree `0` (its kernel is `⊥`).

Every map of the ladder is the product, over the powers `2i ≤ k`, of the corresponding map of the
honest Mayer–Vietoris sequence of the single degree `k - 2i`; the exactness statements of the
chapter (`Work.Cohomology.honest_exact₁`, `honest_exact₂`, `honest_exact₃`) therefore imply the
exactness of the ladder component by component, which is what the elementwise lemmas of
`Submission/Work/LerayHirsch/MvAux/Ladder.lean` spell out.
-/

theorem Mv_exact {B : Type} [TopologicalSpace B] {m : ℕ} {U V : Set B} (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    (∀ k : ℕ, (Work.LerayHirsch.MvF (B := B) m k U V).hom.range
        = (Work.LerayHirsch.MvG (B := B) m k U V).hom.ker) ∧
    (∀ k : ℕ, (Work.LerayHirsch.MvG (B := B) m k U V).hom.range
        = (Work.LerayHirsch.MvD (B := B) m k U V hU hV hcov).hom.ker) ∧
    (∀ k : ℕ, (Work.LerayHirsch.MvD (B := B) m k U V hU hV hcov).hom.range
        = (Work.LerayHirsch.MvF (B := B) m (k + 1) U V).hom.ker) ∧
    (Work.LerayHirsch.MvF (B := B) m 0 U V).hom.ker = ⊥ := by
  have hF2 : ∀ d : ℕ,
      (honestF (TopCat.of B) (∅ : Set B) U V d).hom.range
        = (honestG (TopCat.of B) (∅ : Set B) U V d).hom.ker := fun d =>
    ShortComplex.Exact.moduleCat_range_eq_ker
      (honest_exact₂ (TopCat.of B) (∅ : Set B) U V hU hV hcov d)
  have hG3 : ∀ d : ℕ,
      (honestG (TopCat.of B) (∅ : Set B) U V d).hom.range
        = (honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov d).hom.ker := fun d =>
    ShortComplex.Exact.moduleCat_range_eq_ker
      (honest_exact₃ (TopCat.of B) (∅ : Set B) U V hU hV hcov d)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have hprod : ((MvF (B := B) m k U V) ≫ (MvAux.MvPIso m k U V).hom).hom.range
        = ((MvAux.MvPIso m k U V).inv ≫ (MvG (B := B) m k U V)).hom.ker := by
      refine le_antisymm (fun w hw => ?_) (fun w hw => ?_)
      · rw [MvAux.mem_ker_MvG_prod (B := B) k w]
        intro i
        rw [← hF2 (k - 2 * (i : ℕ))]
        exact (MvAux.mem_range_MvF_prod (B := B) k w).mp hw i
      · rw [MvAux.mem_range_MvF_prod (B := B) k w]
        intro i
        rw [hF2 (k - 2 * (i : ℕ))]
        exact (MvAux.mem_ker_MvG_prod (B := B) k w).mp hw i
    have hinj : Function.Injective (ModuleCat.Hom.hom (MvAux.MvPIso m k U V).hom) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have hmap : Submodule.map (ModuleCat.Hom.hom (MvAux.MvPIso m k U V).hom)
          ((MvF (B := B) m k U V).hom.range)
        = Submodule.map (ModuleCat.Hom.hom (MvAux.MvPIso m k U V).hom)
            ((MvG (B := B) m k U V).hom.ker) := by
      rw [MvAux.map_range_of_iso_square (Iso.refl (MvM B m k)) (MvAux.MvPIso m k U V)
            (MvF (B := B) m k U V) ((MvF (B := B) m k U V) ≫ (MvAux.MvPIso m k U V).hom)
            (Category.id_comp _),
          MvAux.map_ker_of_iso_square (MvAux.MvPIso m k U V) (Iso.refl (MvQ B m k U V))
            (MvG (B := B) m k U V) ((MvAux.MvPIso m k U V).inv ≫ (MvG (B := B) m k U V))
            (by rw [Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id])]
      exact hprod
    exact Submodule.map_injective_of_injective hinj hmap
  · intro k
    have hsurj : Function.Surjective (ModuleCat.Hom.hom (MvAux.MvPIso m k U V).inv) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    have hrange : ((MvAux.MvPIso m k U V).inv ≫ (MvG (B := B) m k U V)).hom.range
        = (MvG (B := B) m k U V).hom.range := by
      rw [ModuleCat.hom_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj,
        Submodule.map_top]
    rw [← hrange]
    refine le_antisymm (fun c hc => ?_) (fun c hc => ?_)
    · rw [MvAux.mem_ker_MvD hU hV hcov k c]
      intro i
      have hci := (MvAux.mem_range_MvG_prod (B := B) k c).mp hc i
      rw [hG3 (k - 2 * (i : ℕ))] at hci
      exact LinearMap.mem_ker.mp hci
    · rw [MvAux.mem_range_MvG_prod (B := B) k c]
      intro i
      rw [hG3 (k - 2 * (i : ℕ))]
      exact LinearMap.mem_ker.mpr ((MvAux.mem_ker_MvD hU hV hcov k c).mp hc i)
  · intro k
    refine le_antisymm (fun d hd => ?_) (fun d hd => ?_)
    · exact (MvAux.mem_ker_MvF (B := B) (k + 1) d).mpr
        ((MvAux.mem_range_MvD hU hV hcov k d).mp hd)
    · exact (MvAux.mem_range_MvD hU hV hcov k d).mpr
        ((MvAux.mem_ker_MvF (B := B) (k + 1) d).mp hd)
  · rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' := (MvAux.mem_ker_MvF (B := B) 0 x).mp hx
    funext i
    rw [Pi.zero_apply]
    have hd : 0 - 2 * (i : ℕ) = 0 := by
      have hi := i.2
      omega
    have hz : x i ∈ (ModuleCat.Hom.hom
        (honestF (TopCat.of B) (∅ : Set B) U V (0 - 2 * (i : ℕ)))).ker := by
      rw [MvAux.mem_ker_honestF]
      exact ⟨by rw [← MvRes_apply]; exact (hx' i).1,
        by rw [← MvRes_apply]; exact (hx' i).2⟩
    exact MvAux.honestF_apply_eq_zero_of_degree_zero hU hV hcov hd (x i) hz

end Work.LerayHirsch
