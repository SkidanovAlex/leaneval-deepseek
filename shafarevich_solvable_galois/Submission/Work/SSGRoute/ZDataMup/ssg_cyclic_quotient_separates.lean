import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-- Any nontrivial element of a finite commutative group is separated by a homomorphism
onto a finite cyclic group (a "cyclic quotient"): there is a finite cyclic group `C` and a
homomorphism `φ : G →* C` with `φ g ≠ 1`.

This is the elementary ingredient used in Shafarevich's theorem to detect nontrivial elements
of finite abelian Galois groups (e.g. via Kummer theory / local data). -/
theorem ssg_cyclic_quotient_separates {G : Type*} [CommGroup G] [Fintype G]
    (g : G) (hg : g ≠ 1) :
    ∃ (C : Type) (_ : CommGroup C) (_ : Fintype C) (_ : IsCyclic C) (φ : G →* C), φ g ≠ 1 := by
  classical
  -- The structure theorem for finite abelian groups: `G` is a product of cyclic groups.
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  -- Since `g ≠ 1`, some coordinate of `e g` is nontrivial.
  have hex : ∃ i : ι, e g i ≠ 1 := by
    by_contra h
    push Not at h
    exact hg ((MulEquiv.map_eq_one_iff e).mp (funext h))
  obtain ⟨i, hi⟩ := hex
  -- That coordinate is a finite cyclic group.
  have hnz : NeZero (n i) := ⟨by have h := hn i; omega⟩
  refine ⟨Multiplicative (ZMod (n i)), inferInstance, inferInstance, inferInstance,
    (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp e.toMonoidHom, ?_⟩
  simpa using hi

end Work.SSGRoute.ZDataMup
