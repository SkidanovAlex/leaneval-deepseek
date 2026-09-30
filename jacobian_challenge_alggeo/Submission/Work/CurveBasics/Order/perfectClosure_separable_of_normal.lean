import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Separability over the relative perfect closure of a finite normal extension

If `L / K` is a finite **normal** field extension, then the maximal purely inseparable
subextension `N := perfectClosure K L` is a separable base for `L`: every element of `L` is
separable over `N` (Stacks 030M, 032N).

The proof is the standard one.  Let `G = Gal(L/K)` act on `L` and let `L^G` be its fixed field.
By Artin's theorem (`FixedPoints.isSeparable`) `L / L^G` is separable.  The remaining point is
that `L^G ⊆ N`: if `x ∈ L` is fixed by every `K`-automorphism of `L` then `x` has no conjugate
other than itself in `L`, so `minpoly K x` has exactly one root in `L`, i.e. its separable degree
is one, which means `x ∈ perfectClosure K L` (`mem_perfectClosure_iff_natSepDegree_eq_one`).
The reverse inclusion `N ⊆ L^G` holds because elements of the purely inseparable relative
perfect closure are fixed by all `K`-automorphisms.

This is the statement `Work.CurveBasics.Order.perfectClosure_separable_of_normal`.
-/

set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

universe u v

section Basic

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The fixed field of the full Galois group consists exactly of the elements fixed by all
`K`-algebra automorphisms of `L`. -/
theorem mem_fixedPoints_subfield_iff (x : L) :
    x ∈ FixedPoints.subfield (L ≃ₐ[K] L) L ↔ ∀ σ : L ≃ₐ[K] L, σ x = x := by
  rw [show x ∈ FixedPoints.subfield (L ≃ₐ[K] L) L ↔
      x ∈ MulAction.fixedPoints (L ≃ₐ[K] L) L from Iff.rfl, MulAction.mem_fixedPoints]
  simp [AlgEquiv.smul_def]

/-- Elements of the relative perfect closure `perfectClosure K L` are fixed by every
`K`-algebra automorphism of `L`: the relative perfect closure is purely inseparable over `K`,
so there is at most one `K`-algebra homomorphism out of it. -/
theorem perfectClosure_fixed (x : L) (hx : x ∈ perfectClosure K L) (σ : L ≃ₐ[K] L) :
    σ x = x := by
  haveI : IsPurelyInseparable K ↥(perfectClosure K L) := inferInstance
  have h1 : (σ : L →ₐ[K] L).comp (IsScalarTower.toAlgHom K ↥(perfectClosure K L) L)
      = IsScalarTower.toAlgHom K ↥(perfectClosure K L) L := Subsingleton.elim _ _
  have h2 := congr_arg (fun f => f ⟨x, hx⟩) h1
  simpa using h2

/-- If `L / K` is normal then every element of `L` fixed by all `K`-automorphisms of `L` is
purely inseparable over `K`, hence lies in `perfectClosure K L`. -/
theorem fixedPoints_le_perfectClosure [Normal K L] (x : L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) : x ∈ perfectClosure K L := by
  classical
  rw [mem_perfectClosure_iff_natSepDegree_eq_one,
    Polynomial.natSepDegree_eq_of_splits _ (Normal.splits (inferInstance : Normal K L) x),
    Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  rw [Multiset.mem_toFinset, Polynomial.mem_aroots, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hae⟩
    have hint : IsIntegral K x := Normal.isIntegral (inferInstance : Normal K L) x
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv (isConjRoot_of_aeval_eq_zero hint hae)
    have hthis : y = σ.symm x := by
      have h2 := congr_arg (⇑(σ.symm)) hσ
      simpa using h2
    rw [hthis, hx σ.symm]
  · intro h
    rw [h]
    exact ⟨minpoly.ne_zero (Normal.isIntegral (inferInstance : Normal K L) x),
      minpoly.aeval K x⟩

/-- The fixed field of `Gal(L/K)` is contained in the relative perfect closure of `K` in `L`
whenever `L / K` is normal. -/
theorem fixedPoints_subfield_le_perfectClosure [Normal K L] :
    FixedPoints.subfield (L ≃ₐ[K] L) L ≤ (perfectClosure K L).toSubfield := fun x hx =>
  fixedPoints_le_perfectClosure x ((mem_fixedPoints_subfield_iff x).1 hx)

/-- The relative perfect closure of `K` in `L` is contained in the fixed field of `Gal(L/K)`. -/
theorem perfectClosure_le_fixedPoints_subfield :
    (perfectClosure K L).toSubfield ≤ FixedPoints.subfield (L ≃ₐ[K] L) L := fun x hx =>
  (mem_fixedPoints_subfield_iff x).2 fun σ => perfectClosure_fixed x hx σ

end Basic

/-- If `L / K` is a finite **normal** field extension, then `L` is separable over the relative
perfect closure `N := perfectClosure K L` (the largest purely inseparable subextension of `L / K`).

This is Stacks 030M/032N: for normal `L/K` the maximal separable subextension `M :=
separableClosure K L` and `N` satisfy `L = M ⊔ N`, hence `L / N ≅ M / (M ⊓ N) = M / K` is
separable (`separableClosure_inf_perfectClosure` gives `M ⊓ N = ⊥`).  Equivalently
`separableClosure N L = ⊤`, and one concludes with `eq_separableClosure_iff` /
`separableClosure_le_iff`.

The normality hypothesis cannot be dropped (counterexample: `K = F₂(t)`, `L = K(x,y)` with
`x² + x + t = 0`, `y² = x`, where `perfectClosure K L = K` but `L/K` is not separable). -/
theorem perfectClosure_separable_of_normal {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Normal K L] :
    Algebra.IsSeparable ↥(perfectClosure K L) L := by
  haveI : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  -- Artin's theorem: `L` is separable over the fixed field of the full Galois group.
  have hArtin : Algebra.IsSeparable ↥(FixedPoints.subfield (L ≃ₐ[K] L) L) L :=
    FixedPoints.isSeparable _ L
  have hle := fixedPoints_subfield_le_perfectClosure (K := K) (L := L)
  have hge := perfectClosure_le_fixedPoints_subfield (K := K) (L := L)
  -- The two subfields of `L` are equal, so the base fields are isomorphic over `L`.
  let e : ↥(FixedPoints.subfield (L ≃ₐ[K] L) L) ≃+* ↥((perfectClosure K L).toSubfield) :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      invFun := fun y => ⟨y.1, hge y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl
      map_mul' := fun x y => by ext; rfl
      map_add' := fun x y => by ext; rfl }
  have he : (algebraMap ↥((perfectClosure K L).toSubfield) L).comp
        (e : ↥(FixedPoints.subfield (L ≃ₐ[K] L) L) →+*
          ↥((perfectClosure K L).toSubfield)) =
      (RingHom.id L).comp (algebraMap ↥(FixedPoints.subfield (L ≃ₐ[K] L) L) L) := by
    ext x; rfl
  haveI : Algebra.IsSeparable ↥(FixedPoints.subfield (L ≃ₐ[K] L) L) L := hArtin
  exact Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl L) he

end Work.CurveBasics.Order
