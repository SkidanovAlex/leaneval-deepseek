import Mathlib
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Serre.serreK2Int
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.SphLoopModel
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Serre.Assembly.pullbackPairMap_isIso
import Submission.Work.Serre.Assembly.hZeroOfPiZeroInt
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Serre.SPC.pbHelpers

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The comparison of the pair `(Γ ×_B E, q⁻¹γ₀) → (E, p⁻¹b₀)` for an `N`-connected `g`

`Work.Serre.SPC.pullbackPairComparison` is the "pullback square" comparison theorem of the Serre
exactness assembly: for a Serre fibration `p : E → B` and a map `g : Γ → B` which is bijective on
`π_i` for every `i ≤ N`, the map of pairs
`(Γ ×_B E, pullbackFst g p ⁻¹' {γ₀}) → (E, p ⁻¹' {b₀})` induced by the second projection of the
fibre product is an isomorphism on integral singular homology in every degree `< N`.

The proof is the five lemma for a map of pairs (`Work.Serre.Assembly.relChainsMapOf_isIso_range`)
applied to the map of pairs whose space component is `pullbackSnd g p` and whose subspace component
is the homeomorphism `Work.Serre.Assembly.fibrePairMap`; the space component is an isomorphism in
the range by `Work.Serre.Assembly.serreK2IntSharp` in positive degrees and by
`Work.Serre.Assembly.hZeroOfPiZeroInt` in degree `0`, both fed by the connectivity
`Work.Serre.SPC.piMapN_pullbackSnd_bijective` of the base change (this file's parent module
`Submission.Work.Serre.SPC.pbHelpers`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.SPC

noncomputable section

set_option maxHeartbeats 1000000

theorem pullbackPairComparison {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀)
    (hp : Work.StemsB.IsSerreFibration p) (N : ℕ)
    (hΓ : PathConnectedSpace Γ) (hB : PathConnectedSpace B)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) :
    ∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase) i) := by
  intro i hi
  by_cases hne : Nonempty (Work.StemsB.Pullback g p)
  · haveI : Nonempty (Work.StemsB.Pullback g p) := hne
    have hconn := piMapN_pullbackSnd_bijective g p γ₀ hp N (by omega) hg
    have hf : ∀ k : ℕ, k ≤ i → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
          (TopCat.ofHom (Work.StemsB.pullbackSnd g p))) k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact Work.Serre.Assembly.hZeroOfPiZeroInt _
          (fun x => hconn 0 (by omega) x)
      · refine Work.Serre.Assembly.serreK2IntSharp _ N (fun j hj x => hconn j (by omega) x)
          k hkpos (by omega)
    have hg' : ∀ k : ℕ, k ≤ i → CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ
          (TopCat.of ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of ↥(p ⁻¹' ({b₀} : Set B)))
          (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase)) k) := by
      intro k _
      haveI : CategoryTheory.IsIso (Work.Cohomology.chainMap ℤ
          (TopCat.of ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of ↥(p ⁻¹' ({b₀} : Set B)))
          (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase)) :=
        Work.Serre.Assembly.isIso_chainMap_fibrePairMap g p γ₀ b₀ hbase
      exact Functor.map_isIso
        (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k)
        (Work.Cohomology.chainMap ℤ
          (TopCat.of ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)))
          (TopCat.of ↥(p ⁻¹' ({b₀} : Set B)))
          (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase))
    exact Work.Serre.Assembly.relChainsMapOf_isIso_range
      (X := TopCat.of (Work.StemsB.Pullback g p)) (Y := TopCat.of E)
      ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
      (TopCat.ofHom (Work.StemsB.pullbackSnd g p))
      (Work.Serre.Assembly.fibrePairMap g p γ₀ b₀ hbase)
      (Work.Serre.Assembly.fibrePairMap_comp g p γ₀ b₀ hbase) i hf hg'
  · -- `Γ ×_B E` is empty; then so is `E`
    haveI hX : IsEmpty (Work.StemsB.Pullback g p) := not_nonempty_iff.mp hne
    haveI hE : IsEmpty E := by
      rcases isEmpty_or_nonempty E with h | h
      · exact h
      · exact absurd (by
          obtain ⟨e⟩ := h
          obtain ⟨e', he'⟩ := Work.Serre.Assembly.exists_preimage_of_isSerreFibration p hp hB e (g γ₀)
          exact ⟨(γ₀, e'), he'.symm⟩) hne
    have hA : (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)
        = (∅ : Set (Work.StemsB.Pullback g p)) :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hX.false x)
    have hC : p ⁻¹' ({b₀} : Set B) = (∅ : Set E) :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x _ => hE.false x)
    have hz1 : CategoryTheory.Limits.IsZero
        ((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback g p))
          ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ))).homology i) := by
      rw [hA]
      haveI := Work.Cohomology.relChains_empty_homology_iso
        (TopCat.of (Work.StemsB.Pullback g p)) i
      exact IsZero.of_iso
        (Work.Cohomology.isZero_singularChains_homology_of_isEmpty
          (TopCat.of (Work.StemsB.Pullback g p)) i)
        (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback g p)) ∅)) i)).symm
    have hz2 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of E)
        (p ⁻¹' ({b₀} : Set B))).homology i) := by
      rw [hC]
      haveI := Work.Cohomology.relChains_empty_homology_iso (TopCat.of E) i
      exact IsZero.of_iso
        (Work.Cohomology.isZero_singularChains_homology_of_isEmpty (TopCat.of E) i)
        (asIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains (TopCat.of E) ∅)) i)).symm
    exact CategoryTheory.Limits.IsZero.isIso hz1 hz2 _

end

end Work.Serre.SPC
