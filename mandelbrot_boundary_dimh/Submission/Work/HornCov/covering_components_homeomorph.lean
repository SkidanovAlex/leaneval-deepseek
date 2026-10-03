import Mathlib
import Submission.Work.HornCov.isClosed_range_of_continuous_section
import Submission.Work.HornCov.isOpenMap_of_isLocalHomeomorphOn_comp

/-!
# Components of a covering of a simply connected open set are sheets

If `p : X → ℂ` is a covering map over an open set `S ⊆ ℂ` that is simply connected and locally
path connected, and `X` is Hausdorff and locally path connected, then every connected component
of `p ⁻¹' S` is mapped homeomorphically onto `S` by `p`.

The proof has two halves.

* The covering of the (simply connected) base admits a global continuous section: lifting the
  inclusion `S ↪ ℂ` along `p` starting at the prescribed point `x ∈ p ⁻¹' S` gives a continuous
  `F : C(↥S, X)` with `p (F s) = s` (`IsCoveringMapOn.existsUnique_continuousMap_lifts`).
* The image of such a section is both open (it is a continuous local section of the local
  homeomorphism `p`, `isOpenMap_of_isLocalHomeomorphOn_comp`) and closed (the range of a
  continuous section is closed in a Hausdorff target), hence it is a connected component.

The two general topology lemmas used above live in the sibling files
`isOpenMap_of_isLocalHomeomorphOn_comp` and `isClosed_range_of_continuous_section`.
-/

set_option linter.unusedVariables false

namespace Work.HornCov

open Set Topology

theorem covering_components_homeomorph {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyPathConnectedSpace X] {p : X → ℂ} {S : Set ℂ} (hS : IsOpen S) [SimplyConnectedSpace ↥S] [LocallyPathConnectedSpace ↥S] (hp : IsCoveringMapOn p S) (hsurj : ∀ s ∈ S, ∃ x, p x = s) : ∀ x ∈ p ⁻¹' S, ∃ H : ↥(connectedComponentIn (p ⁻¹' S) x) ≃ₜ ↥S, ∀ z, (H z : ℂ) = p (z : X) := by
  intro x hx
  classical
  -- The section of `p` over `S` through `x` provided by the unique lifting property.
  obtain ⟨F, hF1, hF2⟩ := (hp.existsUnique_continuousMap_lifts
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, ℂ))
      (a₀ := (⟨p x, hx⟩ : ↥S)) (e₀ := x) (by rfl) (fun a => a.2)).exists
  have hsec : ∀ s : ↥S, p (F s) = (s : ℂ) := fun s => congr_fun hF2 s
  set C : Set X := connectedComponentIn (p ⁻¹' S) x with hC
  have hxmem : x ∈ Set.range (⇑F) := ⟨⟨p x, hx⟩, hF1⟩
  -- the image of the section is connected
  have hpreconn : IsPreconnected (Set.range (⇑F)) := by
    simpa [Set.image_univ] using isPreconnected_univ.image (⇑F) F.continuous.continuousOn
  have hrange_sub : Set.range (⇑F) ⊆ p ⁻¹' S := by
    rintro y ⟨s, rfl⟩
    rw [Set.mem_preimage, hsec s]
    exact s.2
  have hCsub : Set.range (⇑F) ⊆ C := by
    rw [hC]
    exact IsPreconnected.subset_connectedComponentIn hpreconn hxmem hrange_sub
  let φC : ↥S → ↥C := fun s => ⟨⇑F s, hCsub ⟨s, rfl⟩⟩
  have hφC_cont : Continuous φC := Continuous.subtype_mk F.continuous (fun s => hCsub ⟨s, rfl⟩)
  -- the image of the section is open: it is a local section of the local homeomorphism `p`
  have hF_open : IsOpenMap (⇑F : ↥S → X) :=
    isOpenMap_of_isLocalHomeomorphOn_comp hp.isLocalHomeomorphOn (fun a => hrange_sub ⟨a, rfl⟩)
      F.continuous hsec hS.isOpenEmbedding_subtypeVal
  have hopenF : IsOpen (Set.range (⇑F)) := hF_open.isOpen_range
  have himg : Set.range φC = Subtype.val ⁻¹' (Set.range (⇑F)) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s, rfl⟩
    · rintro ⟨s, hs⟩; exact ⟨s, Subtype.ext hs⟩
  have : PreconnectedSpace ↥C :=
    Subtype.preconnectedSpace (by rw [hC]; exact isPreconnected_connectedComponentIn)
  -- the projection `z ↦ p z` on the component, which will be the inverse homeomorphism
  let p' : ↥C → ↥S := fun (z : ↥C) => ⟨p (z : X), connectedComponentIn_subset (p ⁻¹' S) x z.2⟩
  have hp'cont : Continuous p' := by
    change Continuous fun z : ↥C => (⟨p (z : X), connectedComponentIn_subset (p ⁻¹' S) x z.2⟩ : ↥S)
    exact Continuous.subtype_mk (p := fun w : ℂ => w ∈ S) (f := fun z : ↥C => p (z : X))
      (hp.continuousOn.comp_continuous continuous_subtype_val
        (fun z => connectedComponentIn_subset (p ⁻¹' S) x z.2))
      (fun z => connectedComponentIn_subset (p ⁻¹' S) x z.2)
  -- the image of the section is closed (Hausdorff), hence a component
  have hclosed : IsClosed (Set.range φC) :=
    isClosed_range_of_continuous_section (f := p') (g := φC) hp'cont hφC_cont
      (fun s => Subtype.ext (hsec s))
  have hopen : IsOpen (Set.range φC) := by
    rw [himg]; exact hopenF.preimage continuous_subtype_val
  have hclopen : IsClopen (Set.range φC) := ⟨hclosed, hopen⟩
  have hsurjφ : Function.Surjective φC := by
    have hrange : Set.range φC = Set.univ :=
      hclopen.eq_univ ⟨φC ⟨p x, hx⟩, ⟨⟨p x, hx⟩, rfl⟩⟩
    intro z
    have : z ∈ Set.range φC := by rw [hrange]; exact trivial
    exact this
  have hinjφ : Function.Injective φC := by
    intro a b hab
    have h1 : p ((φC a : ↥C) : X) = p ((φC b : ↥C) : X) :=
      congrArg (fun z : ↥C => p (z : X)) hab
    rw [show p ((φC a : ↥C) : X) = (a : ℂ) from hsec a,
        show p ((φC b : ↥C) : X) = (b : ℂ) from hsec b] at h1
    exact Subtype.ext h1
  have hright : ∀ s : ↥S, p' (φC s) = s := fun s => Subtype.ext (hsec s)
  have hleft : ∀ z : ↥C, φC (p' z) = z := by
    intro z
    obtain ⟨s, hs⟩ := hsurjφ z
    rw [← hs, hright s]
  exact ⟨{ toFun := p', invFun := φC, left_inv := hleft, right_inv := hright,
           continuous_toFun := hp'cont, continuous_invFun := hφC_cont }, fun z => rfl⟩

end Work.HornCov
