/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
import Submission.NK.GlobalCFT.LocalField.Topology

/-!
# The idèle group of a number field

For a number field `K` the group of idèles `𝕀 K` is the restricted product of the local
multiplicative groups `K_vˣ` over all places `v` of `K`, with respect to the subgroups `𝒪_vˣ`
of local units (which are all of `K_vˣ` at the archimedean places, so that the product is
restricted only at the nonarchimedean places).  It carries the restricted product topology,
which makes it a topological group.

## Main definitions

* `NK.GlobalCFT.Idele K` (notation `𝕀[K]`): the idèle group.
* `NK.GlobalCFT.Idele.eval`: the projections `𝕀 K →* K_vˣ`.
* `NK.GlobalCFT.Idele.principalIdele`: the diagonal embedding `Kˣ →* 𝕀 K`; its range is
  `NK.GlobalCFT.Idele.principalSubgroup`.
* `NK.GlobalCFT.Idele.integralIdeles`: the idèles which are integral at every finite place.
* `NK.GlobalCFT.Idele.unityIdeles`: the idèles which are `1` at every archimedean place and
  integral at every finite place; these form the group `∏_{v finite} 𝒪_vˣ`.

## Main results

* (delegated) local compactness of `𝕀 K`, the diagonal's image is discrete and closed,
  and `unityIdeles` is compact.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

/-- The **idèle group** of the number field `K`: the restricted product of the local unit groups
`K_vˣ` with respect to the local units `𝒪_vˣ`. -/
def Idele (K : Type*) [Field K] [NumberField K] : Type _ :=
  Πʳ v : Place K, [(Place.localField K v)ˣ, Place.localUnits K v]

/-- `𝕀[K]` is notation for the idèle group of `K`. -/
scoped notation "𝕀[" K "]" => Idele K

namespace Idele

variable {K : Type*} [Field K] [NumberField K]

instance : DFunLike (Idele K) (Place K) (fun v => (Place.localField K v)ˣ) where
  coe a := a.1
  coe_injective _ _ := Subtype.ext

instance : CommGroup (Idele K) :=
  inferInstanceAs (CommGroup (Πʳ v : Place K,
    [(Place.localField K v)ˣ, Place.localUnits K v]))

instance : TopologicalSpace (Idele K) :=
  inferInstanceAs (TopologicalSpace (Πʳ v : Place K,
    [(Place.localField K v)ˣ, Place.localUnits K v]))

instance : IsTopologicalGroup (Idele K) :=
  haveI : Fact (∀ v : Place K, IsOpen (Place.localUnits K v : Set ((Place.localField K v)ˣ))) :=
    inferInstance
  RestrictedProduct.isTopologicalGroup (fun v : Place K => (Place.localField K v)ˣ)

instance (v : Place K) : LocallyCompactSpace ((Place.localField K v)ˣ) :=
  NK.GlobalCFT.LocalField.globalCFT_localFieldUnits_locallyCompactSpace v

instance : LocallyCompactSpace (Idele K) :=
  RestrictedProduct.locallyCompactSpace_of_group (fun v : Place K => (Place.localField K v)ˣ)
    (B := fun v => Place.localUnits K v)
    (NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_eventually (K := K))

instance : T2Space (Idele K) :=
  inferInstanceAs (T2Space (Πʳ v : Place K,
    [(Place.localField K v)ˣ, Place.localUnits K v]))

/-- Two idèles are equal if all their components are equal. -/
@[ext] theorem ext {x y : Idele K} (h : ∀ v, x v = y v) : x = y :=
  Subtype.ext (funext h)

@[simp] theorem mul_apply (x y : Idele K) (v : Place K) : (x * y) v = x v * y v := rfl

@[simp] theorem inv_apply (x : Idele K) (v : Place K) : x⁻¹ v = (x v)⁻¹ := rfl

@[simp] theorem one_apply (v : Place K) : (1 : Idele K) v = 1 := rfl

/-- The projection `𝕀 K →* K_vˣ`. -/
def eval (v : Place K) : Idele K →* (Place.localField K v)ˣ where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem eval_apply (v : Place K) (x : Idele K) : eval v x = x v := rfl

/-- An idèle is determined by its components. -/
theorem eval_injective (x y : Idele K) (h : ∀ v, eval v x = eval v y) : x = y :=
  ext fun v => h v

/-! ### The diagonal embedding -/

/-- The set of finite places at which a unit `k` of `K` does not have valuation `1`.  It is
finite: it is contained in the support of `k` together with the support of `k⁻¹`. -/
theorem finite_setOf_valuation_ne_one (k : Kˣ) :
    {q : HeightOneSpectrum (𝓞 K) | q.valuation K (k : K) ≠ 1}.Finite := by
  refine Set.Finite.subset ((HeightOneSpectrum.Support.finite (R := 𝓞 K) (k : K)).union
    (HeightOneSpectrum.Support.finite (R := 𝓞 K) ((k⁻¹ : Kˣ) : K))) ?_
  intro q hq
  simp only [Set.mem_union, Set.mem_ofPred_eq, HeightOneSpectrum.Support]
  have ha : 0 < q.valuation K (k : K) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff (q.valuation K)).mpr (Units.ne_zero k)
  rcases lt_trichotomy (q.valuation K (k : K)) 1 with h | h | h
  · right
    have hk : ((k⁻¹ : Kˣ) : K) = (k : K)⁻¹ := by simp
    rw [hk, map_inv₀]
    exact (one_lt_inv₀ ha).mpr h
  · exact absurd h hq
  · exact Or.inl h

/-- An element of `Kˣ` is a local unit at all but finitely many places: this is the
eventual condition defining the restricted product, for the diagonal embedding. -/
theorem eventually_localUnits_principal (x : Kˣ) :
    ∀ᶠ v in Filter.cofinite,
      Units.map (algebraMap K (Place.localField K v)) x ∈ Place.localUnits K v := by
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset ((finite_setOf_valuation_ne_one x).image Place.ofFinite) ?_
  intro v hv
  rcases v with _ | q
  · exact absurd Place.mem_localUnits_ofInfinite hv
  · refine ⟨q, ?_, rfl⟩
    intro hq
    exact hv (by
      rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one, Units.coe_map]
      change Valued.v (R := q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap K (q.adicCompletion K) (x : K)) = 1
      rw [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
      exact hq)

set_option maxHeartbeats 1000000 in
/-- The **diagonal embedding** of `Kˣ` into the idèles: the principal idèle `(x)ᵥ`. -/
def principalIdele (K : Type*) [Field K] [NumberField K] : Kˣ →* Idele K where
  toFun x :=
    ⟨fun v => Units.map (algebraMap K (Place.localField K v)) x,
      eventually_localUnits_principal x⟩
  map_one' := by
    apply Subtype.ext
    funext v
    exact map_one _
  map_mul' := by
    intro x y
    apply Subtype.ext
    funext v
    exact map_mul _ _ _

@[simp] theorem principalIdele_apply (x : Kˣ) (v : Place K) :
    principalIdele K x v = Units.map (algebraMap K (Place.localField K v)) x := rfl

/-- The subgroup of principal idèles `Kˣ ⊆ 𝕀 K`. -/
def principalSubgroup (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) :=
  (principalIdele K).range

theorem mem_principalSubgroup {x : Idele K} :
    x ∈ principalSubgroup K ↔ ∃ k : Kˣ, principalIdele K k = x := Iff.rfl

/-! ### Idèles which are integral at the finite places -/

/-- The subgroup of idèles which are units at every finite place (i.e. integral at every
nonarchimedean place). -/
def integralIdeles (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) where
  carrier := {x | ∀ v, Place.IsFinite v → x v ∈ Place.localUnits K v}
  one_mem' := fun v _ => Subgroup.one_mem _
  mul_mem' := fun hx hy v hv => Subgroup.mul_mem _ (hx v hv) (hy v hv)
  inv_mem' := fun hx v hv => Subgroup.inv_mem _ (hx v hv)

theorem mem_integralIdeles {x : Idele K} :
    x ∈ integralIdeles K ↔ ∀ v, Place.IsFinite v → x v ∈ Place.localUnits K v := Iff.rfl

/-- The subgroup of idèles which are `1` at all archimedean places and units at all finite
places: the group `∏_{v finite} 𝒪_vˣ`. -/
def unityIdeles (K : Type*) [Field K] [NumberField K] : Subgroup (Idele K) where
  carrier := {x | (∀ v, Place.IsInfinite v → x v = 1) ∧
    ∀ v, Place.IsFinite v → x v ∈ Place.localUnits K v}
  one_mem' := ⟨fun v _ => rfl, fun v _ => Subgroup.one_mem _⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [mul_apply, hx.1 v hv, hy.1 v hv, one_mul]
    · intro v hv
      rw [mul_apply]
      exact Subgroup.mul_mem _ (hx.2 v hv) (hy.2 v hv)
  inv_mem' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [inv_apply, hx.1 v hv, inv_one]
    · intro v hv
      rw [inv_apply]
      exact Subgroup.inv_mem _ (hx.2 v hv)

theorem mem_unityIdeles {x : Idele K} :
    x ∈ unityIdeles K ↔ (∀ v, Place.IsInfinite v → x v = 1) ∧
      ∀ v, Place.IsFinite v → x v ∈ Place.localUnits K v := Iff.rfl

end Idele

end NK.GlobalCFT
