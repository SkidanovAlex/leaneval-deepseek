import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.LI

/-- A nontrivial free group admits a surjection onto the infinite cyclic group `Multiplicative ℤ`.

Indeed, a free group is free on its basis `IsFreeGroup.Generators H`; if `H` is nontrivial the
basis is nonempty, and sending one basis element to a generator of `Multiplicative ℤ` and all
others to `1` (via the universal property `IsFreeGroup.lift`) is a surjection. -/
theorem nontrivial_isFreeGroup_indicable (H : Type*) [Group H] [IsFreeGroup H] (h : Nontrivial H) :
    ∃ f : H →* Multiplicative ℤ, Function.Surjective f := by
  classical
  have hne : Nonempty (IsFreeGroup.Generators H) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    haveI := hc
    haveI : Unique (FreeGroup (IsFreeGroup.Generators H)) := inferInstance
    haveI : Subsingleton H :=
      Function.Surjective.subsingleton (IsFreeGroup.mulEquiv H).surjective
    obtain ⟨a, b, hab⟩ := h
    exact hab (Subsingleton.elim a b)
  obtain ⟨a⟩ := hne
  refine ⟨IsFreeGroup.lift (fun i => if i = a then Multiplicative.ofAdd (1 : ℤ) else 1), ?_⟩
  intro y
  refine ⟨(IsFreeGroup.of a) ^ (Multiplicative.toAdd y), ?_⟩
  rw [map_zpow, IsFreeGroup.lift_of, if_pos rfl, ← ofAdd_zsmul]
  simpa [zsmul_eq_mul] using ofAdd_toAdd y

theorem isFreeGroup_locallyIndicable (G : Type*) [Group G] [IsFreeGroup G] :
    Group.LocallyIndicable G := by
  intro H _hFG hne
  -- Every subgroup of a free group is free (Nielsen--Schreier).
  haveI : IsFreeGroup H := inferInstance
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  exact nontrivial_isFreeGroup_indicable H ‹Nontrivial H›

end Work.ORLocInd.LI
