import Mathlib
import Submission.Work.ORDunwoody.Basic

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody GTree

set_option linter.style.haveILetI false

/-- If a group `H` acts on `X` through a surjective homomorphism `π : H →* G` which is
compatible with a `G`-action on `X` (as recorded by `h`), then the `H`-orbit setoid and the
`G`-orbit setoid on `X` coincide.  Consequently finiteness of the `G`-orbit quotient implies
finiteness of the `H`-orbit quotient. -/
theorem finite_orbitQuotient_of_surjective {G H X : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H X] (π : H →* G) (hπ : Function.Surjective π)
    (h : ∀ (a : H) (x : X), a • x = π a • x)
    (hG : Finite (MulAction.orbitRel.Quotient G X)) :
    Finite (MulAction.orbitRel.Quotient H X) := by
  have hrel : MulAction.orbitRel H X = MulAction.orbitRel G X := by
    ext x y
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨π a, by rw [← h a y, ha]⟩
    · rintro ⟨g, hg⟩
      obtain ⟨a, rfl⟩ := hπ g
      exact ⟨a, by rw [h a y, hg]⟩
  exact (congrArg (fun s : Setoid X => Finite (Quotient s)) hrel.symm).mp hG

/-- Pulling back a cocompact tree action along a surjective homomorphism `π : H →* G` (whose
action on the vertex type is the induced one, as recorded by `h`) again gives a cocompact
action: the `H`-orbits of vertices and of oriented edges are exactly the `G`-orbits. -/
theorem pullback_isCocompact {G H : Type*} [Group G] [Group H] {V : Type*}
    [MulAction G V] [MulAction H V] (π : H →* G) (hπ : Function.Surjective π)
    (h : ∀ (a : H) (v : V), a • v = π a • v) (T : GTree G V) (hT : T.IsCocompact) :
    (T.pullback π h).IsCocompact := by
  obtain ⟨hv, he⟩ := hT
  -- The `G`-action on the oriented edges of the pullback, transported from `T`.  Its
  -- underlying function is identical to the `G`-action on `AdjPair T`, which is what makes
  -- the finiteness hypothesis `he` apply verbatim.
  letI gAct : MulAction G (AdjPair (T.pullback π h)) :=
    { smul := fun g p => ⟨g • (p : V × V), T.smul_adj g p.2⟩
      one_smul := fun p => Subtype.ext (one_smul G (p : V × V))
      mul_smul := fun g g' p => Subtype.ext (mul_smul g g' (p : V × V)) }
  -- The `H`-action on oriented edges agrees with the `G`-action through `π`.
  have hcompl : ∀ (a : H) (p : AdjPair (T.pullback π h)), a • p = π a • p := by
    intro a p
    apply Subtype.ext
    show (a • (p : V × V) : V × V) = (π a • (p : V × V) : V × V)
    ext <;> simp [h a]
  exact ⟨finite_orbitQuotient_of_surjective π hπ h hv,
         finite_orbitQuotient_of_surjective π hπ hcompl he⟩

end Work.ORDunwoody.Lemmas
