import Mathlib
import Submission.Work.A7F.Defs

namespace Work.A7F

/-- For a bijective monoid homomorphism `f : G →* G'`, the image under `f` of the centralizer
of a set `s` is the centralizer of the image `f '' s`.

The `≤` direction is `Subgroup.map_centralizer_le_centralizer_image` and does not need
injectivity; the reverse direction uses bijectivity. -/
theorem map_centralizer_of_bijective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Bijective f) (s : Set G) :
    (Subgroup.centralizer s).map f = Subgroup.centralizer (f '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s f) ?_
  intro z hz
  obtain ⟨y, rfl⟩ := hf.2 z
  rw [Subgroup.mem_map]
  refine ⟨y, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro a ha
  exact hf.1 (by simpa using hz (f a) ⟨a, ha, rfl⟩)

/-- The centralizers of conjugate elements have the same cardinality: conjugation by `g`
carries the centralizer of `x` isomorphically onto the centralizer of `g * x * g⁻¹`. -/
theorem card_centralizer_conj {G : Type*} [Group G] (x g : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have key : Subgroup.centralizer ({g * x * g⁻¹} : Set G)
      = (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g) := by
    rw [map_centralizer_of_bijective _ (MulAut.conj g).bijective]
    congr 1
    ext z
    simp [MulAut.conj_apply]
  rw [key, Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Work.A7F
