import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If `I` is covered by `J` in the lattice of ideals of a commutative ring `A`, then the length
of `A ⧸ I` exceeds that of `A ⧸ J` by exactly one.

The short exact sequence `0 → J/I → A/I → A/J → 0` exhibits `A ⧸ I` as an extension of `A ⧸ J`
by the simple module `J/I` (simple precisely because `I ⋖ J`), and length is additive in short
exact sequences (`Module.length_eq_add_of_exact`). -/
theorem ideal_length_quotient_covBy {A : Type*} [CommRing A] {I J : Ideal A} (h : I ⋖ J) :
    Module.length A (A ⧸ I) = Module.length A (A ⧸ J) + 1 := by
  have hle : I ≤ J := h.le
  -- The natural surjection `A ⧸ I ↠ A ⧸ J`.
  let g : (A ⧸ I) →ₗ[A] (A ⧸ J) :=
    Submodule.mapQ (I : Submodule A A) (J : Submodule A A) (LinearMap.id : A →ₗ[A] A)
      (by simpa using hle)
  -- Its kernel is the image of `J` in `A ⧸ I`, i.e. the submodule `J/I`.
  have hker : LinearMap.ker g
      = Submodule.map (Submodule.mkQ (I : Submodule A A)) (J : Submodule A A) := by
    rw [Submodule.ker_mapQ]
    simp
  have hg_surj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_mapQ]
    simp
  -- `J/I` is a simple module, because `I ⋖ J` leaves no submodule strictly in between.
  have hsimple : IsSimpleModule A
      (Submodule.map (Submodule.mkQ (I : Submodule A A)) (J : Submodule A A)) := by
    rw [isSimpleModule_iff_isAtom]
    -- Transport the atom statement across the order isomorphism between submodules of `A ⧸ I`
    -- and the interval `[I, ⊤]` of ideals.
    rw [← OrderIso.isAtom_iff (Submodule.comapMkQRelIso (I : Submodule A A))
      (Submodule.map (Submodule.mkQ (I : Submodule A A)) (J : Submodule A A))]
    have h1 : (Submodule.comapMkQRelIso (I : Submodule A A))
        (Submodule.map (Submodule.mkQ (I : Submodule A A)) (J : Submodule A A))
        = ⟨(J : Submodule A A), hle⟩ := by
      ext x
      simp [Submodule.comapMkQRelIso, Submodule.comap_map_mkQ, sup_eq_right.mpr hle]
    rw [h1]
    exact Set.Ici.isAtom_iff.mpr h
  -- Length is additive in the short exact sequence `0 → J/I → A/I → A/J → 0`.
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.subtype_injective (LinearMap.ker g)) hg_surj
      (LinearMap.exact_subtype_ker_map g)
  rw [hlen, hker, Module.length_eq_one_iff.mpr hsimple]
  exact add_comm _ _

end Work.BW
