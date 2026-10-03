import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientGroupOrbitV

namespace Work.ORBassSerre.QuotientTree

universe u

/-- The canonical map from `G`-orbits on `X` to `(G ⧸ N)`-orbits on the `N`-orbits of `X`:
the `G`-orbit of `x` is sent to the `(G ⧸ N)`-orbit of the `N`-orbit of `x`.  It is well defined
because `x` and `g • x` have `N`-orbits lying in the same `(G ⧸ N)`-orbit. -/
theorem orbitQuotient_map_compat {G X : Type u} [Group G] [MulAction G X] (N : Subgroup G)
    [N.Normal] {a b : X} (hab : (MulAction.orbitRel G X) a b) :
    (MulAction.orbitRel (G ⧸ N) (MulAction.orbitRel.Quotient N X))
      (Quotient.mk'' a : MulAction.orbitRel.Quotient N X) (Quotient.mk'' b) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab
  obtain ⟨g, hg⟩ := hab
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨QuotientGroup.mk' N g, ?_⟩
  rw [Work.ORBassSerre.quotient_smul_mk, hg]

/-- Finitely many `G`-orbits on `X` give finitely many `(G ⧸ N)`-orbits on the set of `N`-orbits
of `X` (for the induced action of `G ⧸ N`). -/
theorem finite_orbitQuotient_quotient {G X : Type u} [Group G] [MulAction G X] (N : Subgroup G)
    [N.Normal] (h : Finite (MulAction.orbitRel.Quotient G X)) :
    Finite (MulAction.orbitRel.Quotient (G ⧸ N) (MulAction.orbitRel.Quotient N X)) := by
  -- The map `G`-orbit of `x` ↦ `(G ⧸ N)`-orbit of the `N`-orbit of `x` is surjective.
  let f : MulAction.orbitRel.Quotient G X →
      MulAction.orbitRel.Quotient (G ⧸ N) (MulAction.orbitRel.Quotient N X) :=
    Quotient.map (fun x => (Quotient.mk'' x : MulAction.orbitRel.Quotient N X))
      (fun _ _ hab => orbitQuotient_map_compat N hab)
  have hf : ∀ x : X,
      f (Quotient.mk'' x) =
        Quotient.mk'' (Quotient.mk'' x : MulAction.orbitRel.Quotient N X) :=
    fun x => Quotient.map_mk _ _ x
  refine Finite.of_surjective f ?_
  intro y
  refine Quotient.inductionOn y ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk'' x, hf x⟩

end Work.ORBassSerre.QuotientTree
