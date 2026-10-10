import Mathlib.GroupTheory.Index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Small vocabulary for the finiteness of `Ext¹_{D_w}(N, K_wˣ)` (`ext_localUnits_finite`)

Nothing here is specific to number fields; these are the two elementary ingredients of the
syzygy argument:

* `nsmulAddHom p M` is "multiplication by `p`" as an additive homomorphism `M →+ M`, so that the
  `p`-torsion `(nsmulAddHom p M).ker` and the subgroup of `p`-th powers `(nsmulAddHom p M).range`
  are both `AddSubgroup`s;
* `finite_of_finite_addSubgroup_of_finite_quotient`: an abelian group with a finite subgroup of
  finite index is finite (used as "an extension of two finite groups is finite").
-/

namespace Work.SSGRoute

noncomputable section

/-- Multiplication by `p` on an additive commutative monoid, as an additive homomorphism. -/
def nsmulAddHom (p : ℕ) (M : Type*) [AddCommMonoid M] : M →+ M where
  toFun m := p • m
  map_zero' := smul_zero p
  map_add' a b := smul_add p a b

@[simp] lemma nsmulAddHom_apply (p : ℕ) {M : Type*} [AddCommMonoid M] (m : M) :
    nsmulAddHom p M m = p • m := rfl

lemma mem_nsmulAddHom_ker (p : ℕ) {M : Type*} [AddCommGroup M] (m : M) :
    m ∈ (nsmulAddHom p M).ker ↔ p • m = 0 := Iff.rfl

/-- **An extension of two finite groups is finite.** -/
theorem finite_of_finite_addSubgroup_of_finite_quotient {M : Type*} [AddCommGroup M]
    (H : AddSubgroup M) (hH : Finite H) (hQ : Finite (M ⧸ H)) : Finite M :=
  (AddSubgroup.finite_iff_finite_and_finiteIndex H).mpr
    ⟨hH, (AddSubgroup.finiteIndex_iff_finite_quotient).mpr hQ⟩

end

end Work.SSGRoute
