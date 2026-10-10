import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `T`-idèles and the `T`-units, as `ℤ[Gal(L/K)]`-modules

Milne's proof of the Herbrand-quotient computation `h(Gal(L/K), C_L) = [L : K]` (*Class Field
Theory*, Theorem 4.3) runs through the `T`-idèles and the `T`-units attached to a finite
`Gal(L/K)`-stable set `T` of places of `L`:

* `𝕀_{L,T}` — the idèles of `L` whose components outside `T` are local units;
* `U(T) = Lˣ ∩ 𝕀_{L,T}` — the `T`-units.

This file defines them inside the vocabulary of the delivered chapter and shows that they carry
the `Gal(L/K)`-action (so that their Tate cohomology is available).  The two classical Herbrand
computations (`h(𝕀_{L,T}) = ∏_{v ∈ S}[L_w : K_v]`, Milne Proposition 2.7, and
`[L:K]·h(U(T)) = ∏_{v ∈ S}[L_w : K_v]`, Milne Proposition 3.1) are *not* proved here; they are
recorded as the data of `herbrandQuotient_of_milneData`
(`Submission/Work/GlobalCFTdeep/Herbrand/Reduction.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The **`T`-idèles** of `L`: the idèles whose components outside `T` are local units. -/
def TIdeles (T : Set (Place L)) : Subgroup (Idele L) where
  carrier := {x | ∀ w : Place L, w ∉ T → x w ∈ Place.localUnits L w}
  one_mem' := fun w _ => one_mem _
  mul_mem' := fun hx hy w hw => by
    rw [Idele.mul_apply]; exact mul_mem (hx w hw) (hy w hw)
  inv_mem' := fun hx w hw => by
    rw [Idele.inv_apply]; exact inv_mem (hx w hw)

@[simp] theorem mem_TIdeles {T : Set (Place L)} {x : Idele L} :
    x ∈ TIdeles T ↔ ∀ w : Place L, w ∉ T → x w ∈ Place.localUnits L w := Iff.rfl

/-- The **`T`-units** of `L`: the elements of `Lˣ` whose principal idèle is a `T`-idèle. -/
def TUnits (T : Set (Place L)) : Subgroup Lˣ := (TIdeles T).comap (Idele.principalIdele L)

@[simp] theorem mem_TUnits {T : Set (Place L)} {a : Lˣ} :
    a ∈ TUnits T ↔ ∀ w : Place L, w ∉ T →
      Units.map (algebraMap L (Place.localField L w)) a ∈ Place.localUnits L w :=
  Iff.rfl

/-- A `G`-stable subgroup of a `G`-group is itself a `G`-group. -/
def stableMulDistribMulAction (G : Type*) [Group G] {M : Type*} [Group M]
    [MulDistribMulAction G M] (H : Subgroup M) (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) :
    MulDistribMulAction G H where
  smul g x := ⟨g • (x : M), hH g x.2⟩
  one_smul x := Subtype.ext (MulAction.one_smul (x : M))
  mul_smul g h x := Subtype.ext (SemigroupAction.mul_smul g h (x : M))
  smul_mul g x y := Subtype.ext (MulDistribMulAction.smul_mul g (x : M) (y : M))
  smul_one g := Subtype.ext (MulDistribMulAction.smul_one g)

/-- The `T`-idèles are stable under `Gal(L/K)` when `T` is. -/
theorem smul_mem_TIdeles {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    {σ : L ≃ₐ[K] L} {x : Idele L} (hx : x ∈ TIdeles T) : σ • x ∈ TIdeles T := by
  intro w hw
  have h1 : σ⁻¹ • w ∉ T := by
    intro h
    exact hw (by simpa using hT (σ := σ) h)
  rw [Idele.smul_apply]
  refine (Place.localRingEquiv_mem_localUnits (σ := σ⁻¹) (v := w)
    (Units.map (Place.localRingEquiv σ⁻¹ w).symm.toMonoidHom (x (σ⁻¹ • w)))).mpr ?_
  have hcoe : Units.map (Place.localRingEquiv σ⁻¹ w).toMonoidHom
      (Units.map (Place.localRingEquiv σ⁻¹ w).symm.toMonoidHom (x (σ⁻¹ • w)))
      = x (σ⁻¹ • w) := by
    ext
    simp
  rw [hcoe]
  exact hx (σ⁻¹ • w) h1

/-- The `T`-idèles as a `ℤ[Gal(L/K)]`-module. -/
def tIdelesRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T) (fun σ x hx => smul_mem_TIdeles hT hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (TIdeles T)

/-- The `T`-units are stable under `Gal(L/K)` when `T` is. -/
theorem smul_mem_TUnits {T : Set (Place L)}
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    {σ : L ≃ₐ[K] L} {a : Lˣ} (ha : a ∈ TUnits T) : σ • a ∈ TUnits T := by
  have ha' : Idele.principalIdele L a ∈ TIdeles T := by rwa [mem_TUnits] at ha
  have h2 : Idele.principalIdele L (σ • a) = σ • Idele.principalIdele L a := by
    rw [Galois.globalCFT_smul_principalIdele]
    exact congrArg (Idele.principalIdele L)
      (rfl : σ • a = Units.map σ.toMulEquiv.toMonoidHom a)
  have h1 : Idele.principalIdele L (σ • a) ∈ TIdeles T := by
    rw [h2]
    exact smul_mem_TIdeles hT ha'
  rw [mem_TUnits]
  exact mem_TIdeles.mp h1

/-- The `T`-units as a `ℤ[Gal(L/K)]`-module. -/
def tUnitsRep (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T) : Rep ℤ (L ≃ₐ[K] L) :=
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TUnits T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TUnits T) (fun σ x hx => smul_mem_TUnits hT hx)
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (TUnits T)

end NK.GlobalCFTdeep
