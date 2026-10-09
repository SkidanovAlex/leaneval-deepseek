import Mathlib
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Tame

open scoped Classical Pointwise
open CategoryTheory

/-! ## The unramified quotient `Gal(κ^ur/κ) ≅ Ẑ` is non-trivial

The local structure theory needs a Frobenius element, i.e. an element of `Gal(κ̄/κ)` lying
*outside* the inertia subgroup.  The only group-theoretic input is that the unramified quotient
`Gal(κ^ur/κ)` is `Ẑ` (the profinite completion of `ℤ`), which is non-trivial; the trivial
quotient is not isomorphic to it.

The proof of non-triviality of `Ẑ` is the universal property of the profinite completion
applied to the surjection `ℤ → ℤ/2`: the induced map `Ẑ → ℤ/2` is surjective, so `Ẑ` has two
distinct elements. -/

/-- **`Ẑ` is non-trivial.**  The profinite completion of `ℤ` surjects onto `ℤ/2ℤ` (via the
universal property of the completion applied to the quotient map `ℤ → ℤ/2`), hence it has at
least two elements. -/
theorem nontrivial_zhat : Nontrivial NK.LocalAnabelian.Zhat := by
  -- the quotient map `ℤ → ℤ/2`, as a map of multiplicative groups
  let f : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))
  -- `ℤ/2` as a (discrete) profinite group
  let P : ProfiniteGrp := ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2)))
  -- the induced map `Ẑ → ℤ/2`, which is surjective because `f` is
  let φ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ)) ⟶ P :=
    ProfiniteGrp.ProfiniteCompletion.lift (P := P) (GrpCat.ofHom f)
  have hφ : ∀ a : Multiplicative ℤ,
      φ.hom.toMonoidHom (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ)) a)
        = f a :=
    fun a => CategoryTheory.ConcreteCategory.congr_hom
      (ProfiniteGrp.ProfiniteCompletion.lift_eta (P := P) (f := GrpCat.ofHom f)) a
  refine ⟨ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ))
    (Multiplicative.ofAdd (1 : ℤ)), 1, ?_⟩
  intro hcon
  have h1 : φ.hom.toMonoidHom (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ))
      (Multiplicative.ofAdd (1 : ℤ))) = 1 :=
    (congrArg φ.hom.toMonoidHom hcon).trans (map_one _)
  have h3 : (1 : ZMod 2) = 0 := by
    have h2 : Multiplicative.ofAdd (((1 : ℤ) : ZMod 2)) = (1 : Multiplicative (ZMod 2)) :=
      (hφ _).symm.trans h1
    simp at h2
  exact one_ne_zero h3

/-- **The inertia subgroup is a proper subgroup**, given that the unramified quotient is `Ẑ`:
if every element of `Gal(K'/κ)` lay in the inertia subgroup then the quotient
`Gal(K'/κ)/I` would be trivial, contradicting `Gal(K'/κ)/I ≅ Ẑ` and the non-triviality of `Ẑ`. -/
theorem exists_notMem_inertiaSubgroup_of_unramifiedQuotient
    {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K'] {p : ℕ}
    (h : Nonempty (Gal(K'/κ) ⧸ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p ≃*
      NK.LocalAnabelian.Zhat)) :
    ∃ x : Gal(K'/κ), x ∉ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p := by
  obtain ⟨e⟩ := h
  by_contra hcon
  -- if the inertia subgroup is not proper it is everything, and the quotient collapses
  have htop : NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p = ⊤ :=
    le_antisymm le_top fun x _ => by
      by_contra hx
      exact hcon ⟨x, hx⟩
  have hsub : Subsingleton (Gal(K'/κ) ⧸
      NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  -- transporting along `e` makes `Ẑ` a subsingleton, contradicting its non-triviality
  obtain ⟨x, y, hxy⟩ := nontrivial_zhat.exists_pair_ne
  exact hxy (e.symm.injective (hsub.elim (e.symm x) (e.symm y)))

end NK.LocalStructure.Tame
