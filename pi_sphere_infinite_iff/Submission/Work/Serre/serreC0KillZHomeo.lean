import Mathlib
import Submission.Work.Serre.serreC0KillHomologySets

/-!
# `serreC0KillZHomeo`: the intersection of the cover is the disjoint union of the shells

For `X = KillX f` the space obtained from `Y` by attaching `(n+2)`-cells along `f`, the cover
`KillU ∪ KillV` of `X` has intersection `KillZ f`, which is the union of the shell pieces
`KillQ f i = cellImg f i (open ball of radius 1/2) ∩ (closed ball of radius 1/4)ᶜ`.

The pieces are pairwise disjoint and each is open (`disjoint_KillQ`, `isOpen_KillQ`), and their
union is `KillZ f` (`KillZ_eq_iUnion_KillQ`).  Consequently `KillZ f`, with the subspace
topology, is canonically homeomorphic to the disjoint union (sigma type) of the pieces.

The general point-set statement is proved first: for a family of pairwise disjoint open sets
`U i` with `Z = ⋃ i, U i`, the "value" map `Σ i, ↥(U i) → Z` is a continuous open bijection,
hence a homeomorphism (`nonempty_homeo_iUnion_sigma`).
-/

open Set
open scoped Topology

namespace Work.Serre

noncomputable section

variable {X : Type*} [TopologicalSpace X] {ι : Type} {U : ι → Set X}

/-- The "value" map from the disjoint union of a family of subsets of a space back into the
space. -/
def sigmaValOfOpenCover (U : ι → Set X) : (Σ i, ↥(U i)) → X := fun p => (p.2 : X)

/-- The value map is continuous. -/
theorem continuous_sigmaValOfOpenCover : Continuous (sigmaValOfOpenCover U) :=
  continuous_sigma fun _ => continuous_subtype_val

/-- **The value map of an open cover by the pieces is an open map.** -/
theorem isOpenMap_sigmaValOfOpenCover (hU : ∀ i, IsOpen (U i)) :
    IsOpenMap (sigmaValOfOpenCover U) := by
  intro s hs
  let mkU : ∀ i, ↥(U i) → (Σ j, ↥(U j)) := fun i a => ⟨i, a⟩
  have hpre : ∀ i, IsOpen ((mkU i) ⁻¹' s) := fun i => by
    simpa only [mkU] using isOpen_sigma_iff.mp hs i
  have hdecomp : s = ⋃ i, (mkU i) '' ((mkU i) ⁻¹' s) := by
    ext p
    constructor
    · intro hp
      refine mem_iUnion.mpr ⟨p.1, ?_⟩
      exact mem_image_of_mem (mkU p.1) hp
    · intro hp
      rw [mem_iUnion] at hp
      obtain ⟨i, q, hq, rfl⟩ := hp
      exact hq
  rw [hdecomp, image_iUnion]
  refine isOpen_iUnion fun i => ?_
  have himg : sigmaValOfOpenCover U '' ((mkU i) '' ((mkU i) ⁻¹' s)) =
      (↑) '' ((mkU i) ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mkU i q, ⟨q, hq, rfl⟩, rfl⟩
  rw [himg]
  exact (hU i).isOpenMap_subtype_val _ (hpre i)

/-- **A space which is the union of pairwise disjoint open pieces is the disjoint union of the
pieces**: if the `U i` are pairwise disjoint open sets and `Z = ⋃ i, U i`, then `Z` is
homeomorphic to `Σ i, ↥(U i)`. -/
theorem nonempty_homeo_iUnion_sigma {Z : Set X} (hU : ∀ i, IsOpen (U i))
    (hZU : Z = ⋃ i, U i) (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    Nonempty (↥Z ≃ₜ (Σ i, ↥(U i))) := by
  have hmem : ∀ p : Σ i, ↥(U i), sigmaValOfOpenCover U p ∈ Z := fun p => by
    rw [hZU]
    exact mem_iUnion.mpr ⟨p.1, p.2.2⟩
  let toFun : (Σ i, ↥(U i)) → ↥Z := fun p => ⟨sigmaValOfOpenCover U p, hmem p⟩
  have hinj : Function.Injective toFun := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hval : (a : X) = (b : X) := congrArg Subtype.val h
    by_cases hij : i = j
    · subst hij
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hval))
    · exact absurd (hval.symm ▸ b.2) (Set.disjoint_left.mp (hd i j hij) a.2)
  have hsurj : Function.Surjective toFun := by
    rintro ⟨z, hz⟩
    rw [hZU] at hz
    rw [mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨⟨i, ⟨z, hi⟩⟩, Subtype.ext rfl⟩
  have hcont : Continuous toFun := continuous_sigmaValOfOpenCover.subtype_mk hmem
  have hopen : IsOpenMap toFun := (isOpenMap_sigmaValOfOpenCover hU).subtype_mk hmem
  exact ⟨((Equiv.ofBijective toFun ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen).symm⟩

/-- **The intersection of the two members of the cover is the disjoint union of the shell
pieces.** -/
theorem serreC0KillZHomeo {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Nonempty (↥(Work.Serre.KillZ f) ≃ₜ (Σ i : ι, ↥(Work.Serre.KillQ f i))) :=
  nonempty_homeo_iUnion_sigma (U := fun i => KillQ f i) (Z := KillZ f) (isOpen_KillQ f)
    (KillZ_eq_iUnion_KillQ f) (fun _ _ hij => disjoint_KillQ f hij)

end

end Work.Serre
