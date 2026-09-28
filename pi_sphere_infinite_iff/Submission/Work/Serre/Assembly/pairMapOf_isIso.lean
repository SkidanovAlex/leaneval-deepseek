import Mathlib
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.Serre.serreK2Int
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.epsilonNaturality

/-!
# The comparison `(Γ, {γ₀}) → (B, {b₀})` is a homology iso below `N`

`pairMapOf_isIso` is the relative (pair) form of `Work.Serre.serreK2Int`: if `g : Γ → B` induces
bijections on `πᵢ` at every base point for `i ≤ N`, then the map of pairs
`(Γ, {γ₀}) → (B, {b₀})` induces an isomorphism on relative integral homology in every degree `i < N`
(the point-subspaces being nonempty, hence path connected).

The proof is the five lemma for the long exact sequences of the two pairs
(`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃`, applied to the morphism
`hPairShortMap` of short exact sequences of chain complexes), together with

* `isIso_chainMap_subsingleton`: the chain map of a continuous map between *one-point* spaces is a
  quasi-isomorphism (both `H₀ ≅ ℤ` via the natural augmentation `epsilonNaturality`, and all higher
  homologies vanish by `homologyContractible`);
* `isIso_homologyMap_zero_of_pathConnected`: in degree `0` the induced map is an isomorphism
  between path-connected spaces, again by naturality of the augmentation;
* degree `0` of the absolute map is *not* covered by `serreK2Int`, but the five lemma at `i = 0`
  only needs it as `IsIso` at `i` and as `Mono` at `i - 1` (a vacuous request at `i = 0`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.Assembly

noncomputable section

/-- **Degree zero of a map of path-connected spaces.**  For path-connected `X`, `Y` and any
continuous map `f : X ⟶ Y`, the induced map `H₀(X;ℤ) ⟶ H₀(Y;ℤ)` is an isomorphism: the
augmentation `H₀(-;ℤ) ⟶ ℤ` is natural (`Work.Cohomology.epsilonNaturality`) and an isomorphism on
path-connected spaces. -/
lemma isIso_homologyMap_zero_of_pathConnected {X Y : TopCat}
    [PathConnectedSpace ↥X] [PathConnectedSpace ↥Y] (f : X ⟶ Y) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) 0) := by
  haveI hX : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hY : IsIso (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)) := inferInstance
  have hnat := Work.Cohomology.epsilonNaturality X Y f
  have hα : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) 0
      = TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-- **A continuous map between one-point spaces is a quasi-isomorphism** on singular chains: both
homologies are isomorphic to `ℤ` in degree `0` (naturality of the augmentation) and vanish in
positive degrees (contractibility, `Work.Cohomology.homologyContractible`). -/
lemma isIso_chainMap_subsingleton {X Y : TopCat} [Subsingleton ↥X] [Nonempty ↥X]
    [Subsingleton ↥Y] [Nonempty ↥Y] (f : X ⟶ Y) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : PathConnectedSpace ↥X := inferInstance
    haveI : PathConnectedSpace ↥Y := inferInstance
    exact isIso_homologyMap_zero_of_pathConnected f
  · haveI : ContractibleSpace ↥X := inferInstance
    haveI : ContractibleSpace ↥Y := inferInstance
    haveI hX : IsZero ((Work.Cohomology.singularChains ℤ X).homology n) :=
      Work.Cohomology.homologyContractible n hn
    haveI hY : IsZero ((Work.Cohomology.singularChains ℤ Y).homology n) :=
      Work.Cohomology.homologyContractible n hn
    have he : HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ X Y f) n
        = (IsZero.iso hX hY).hom := IsZero.eq_of_src hX _ _
    rw [he]
    infer_instance

theorem pairMapOf_isIso {Γ B : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    (g : C(Γ, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) (N : ℕ)
    (hΓ : PathConnectedSpace Γ) (hB : PathConnectedSpace B)
    (hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g i x)) :
    ∀ i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) i) := by
  haveI : Nonempty Γ := hΓ.nonempty
  intro i hi
  -- The morphism of short exact sequences of chain complexes of the two pairs.
  let φ := Work.Cohomology.hPairShortMap (TopCat.of Γ) (TopCat.of B) ({γ₀} : Set Γ)
      ({b₀} : Set B) (TopCat.ofHom g)
      (TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩)
      (by ext x; exact (congrArg g x.2).trans hbase)
  have hτ₃ : φ.τ₃ = Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase := rfl
  -- The map on the point subspaces is a quasi-isomorphism, hence epi and iso as needed.
  have hEpiτ₁ : Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ({γ₀} : Set Γ)) (TopCat.of ({b₀} : Set B))
        (TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩)) i) := by
    haveI := isIso_chainMap_subsingleton (X := TopCat.of ({γ₀} : Set Γ))
      (Y := TopCat.of ({b₀} : Set B))
      (TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩) i
    infer_instance
  have hτ₁' : ∀ j, (ComplexShape.down ℕ).Rel i j → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ({γ₀} : Set Γ)) (TopCat.of ({b₀} : Set B))
        (TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩)) j) :=
    fun j _ => isIso_chainMap_subsingleton _ j
  -- The absolute map in degree `i`: `serreK2Int` above degree `0`, connectedness in degree `0`.
  have habs : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of Γ) (TopCat.of B) (TopCat.ofHom g)) i) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact isIso_homologyMap_zero_of_pathConnected (TopCat.ofHom g)
    · exact Work.Serre.serreK2Int g N hg i hi0 hi
  -- The neighbouring degree, where only monomorphy is needed (the datum `c.Rel i j` reads
  -- `j + 1 = i`, and there is no such `j` when `i = 0`).
  have habs' : ∀ j, (ComplexShape.down ℕ).Rel i j → Mono (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of Γ) (TopCat.of B) (TopCat.ofHom g)) j) := by
    intro j hij
    have hji : j < i := by
      have hij' : j + 1 = i := hij
      omega
    have hjN : j < N := lt_trans hji hi
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · haveI := isIso_homologyMap_zero_of_pathConnected (TopCat.ofHom g)
      infer_instance
    · haveI := Work.Serre.serreK2Int g N hg j hj0 hjN
      infer_instance
  -- The five lemma for the long exact sequences of the pairs.
  have key : IsIso (HomologicalComplex.homologyMap φ.τ₃ i) :=
    HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ
      (Work.Cohomology.hPairShort_shortExact (TopCat.of Γ) ({γ₀} : Set Γ))
      (Work.Cohomology.hPairShort_shortExact (TopCat.of B) ({b₀} : Set B)) i
      hEpiτ₁ habs hτ₁' habs'
  exact hτ₃ ▸ key

end

end Work.Serre.Assembly
