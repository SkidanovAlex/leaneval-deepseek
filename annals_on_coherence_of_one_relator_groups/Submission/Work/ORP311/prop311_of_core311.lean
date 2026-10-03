/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (the reduction `Core311 ⇒ Prop311`)

# `Core311` implies `Prop311`: `U_N ⊆ U(N)`

`Prop311` is the statement of JZLA20, Proposition 3.11, in the form in which the route
design consumes it: for `N ≤ H ≤ G`, `N` normal in `H`, `t : ↥H` with `H = N ⋊ ⟨t⟩`, every
`n` and every `A : Mₙ(U_N)` over the `∗`-regular closure `U_N = closureCN N` of the image of
`ℂ[↥N]` in `U(G)`,

`1 + A · ι (single t 1)` is a unit of `Mₙ(U(G))`.

`Core311` is the same statement with `A` ranging over the enveloping `U(N) = ((concreteEnvelope G).sub N).V`
instead of only over `U_N`.

The reduction rests on the single structural fact recorded in `Defs.lean`: `U_N` is the
smallest `∗`-regular `∗`-subring of `U(G)` containing the image of `ℂ[↥N]`, while the image
of the envelope inclusion `φ : U(N) ↪ U(G)` is a `∗`-regular `∗`-subring containing that
image; hence `U_N ⊆ im φ`.  Since `φ` is injective we may then lift any matrix `A` over `U_N`
to a matrix `B` over `U(N)` with `B.map φ = A.map (closureCN.subtype N)`, and apply `Core311`
to `B`.

The two ingredients of `U_N ⊆ im φ` are:

* `φ` is `ℂ`-linear — indeed `φ (algebraMap ℂ V c) = ι (single 1 c) = algebraMap ℂ U c`,
  which follows from `ιH_algebraMap`, `ι_algebraMap` and `φ_ι` at the identity of `↥N`;
* the image of `φ` is `∗`-regular, because `φ` restricts to a `∗`-ring isomorphism onto it.

`φ (ιH x) = phiN N x` then holds for all `x : ℂ[↥N]` by `MonoidAlgebra.ringHom_ext`.
-/
import Mathlib
import Submission.Work.ORP311.Defs

set_option autoImplicit false

universe u

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The image of the envelope inclusion `φ : U(N) ↪ U(G)` as a `∗`-subring of `U(G)`. -/
noncomputable def rangeSubring (N : Subgroup G) :
    Work.ORHughesFree.StarSubring (concreteEnvelope G).U where
  toSubring :=
    { carrier := Set.range ((concreteEnvelope G).sub N).φ
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, map_neg _ _⟩ }
  star_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨star v, ((concreteEnvelope G).sub N).φ_star v⟩

/-- The image of the envelope inclusion is `∗`-regular: `φ` is an injective `∗`-ring map from
the `∗`-regular ring `U(N)` onto it, and both the von Neumann regularity and the properness
of the involution transport along such a map. -/
instance instIsStarRegularRange (N : Subgroup G) :
    Work.ORHughesFree.IsStarRegular (rangeSubring (G := G) N) := by
  have hreg : Work.ORHughesFree.IsStarRegular ((concreteEnvelope G).sub N).V :=
    isStarRegular_of_isStarRegularRing ((concreteEnvelope G).sub N).starRegularV
  refine ⟨⟨fun x => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨v, hv⟩ := x.2
    obtain ⟨w, hw⟩ := (inferInstance :
      Work.ORHughesFree.VonNeumannRegularRing ((concreteEnvelope G).sub N).V).exists_mul_inverse v
    refine ⟨⟨((concreteEnvelope G).sub N).φ w, ⟨w, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show x.1 * ((concreteEnvelope G).sub N).φ w * x.1 = x.1
    rw [← hv, ← map_mul, ← map_mul, hw]
  · obtain ⟨v, hv⟩ := x.2
    have hval : star x.1 * x.1 = 0 := congrArg Subtype.val hx
    have h2 : ((concreteEnvelope G).sub N).φ (star v * v) = 0 := by
      rw [map_mul, ((concreteEnvelope G).sub N).φ_star]
      rw [hv]
      exact hval
    have hv0 : star v * v = 0 :=
      ((concreteEnvelope G).sub N).φ_injective (by rw [h2, map_zero])
    have hzero : v = 0 := hreg.proper v hv0
    apply Subtype.ext
    show x.1 = 0
    rw [← hv, hzero, map_zero]

/-- **`φ` is compatible with the structure maps**: `φ (ιH x) = phiN N x` for every
`x : ℂ[↥N]`, i.e. the image of `ℂ[↥N]` in `U(G)` computed through `U(N)` agrees with the
map `phiN N` of the definition of `U_N`.

Both sides are ring homomorphisms `ℂ[↥N] →+* U(G)`; on the group basis this is `φ_ι`, and
on the scalar `single 1 r` it is `ιH_algebraMap` followed by `φ_ι` at the identity
(which says exactly that `φ` is `ℂ`-linear). -/
theorem phiN_eq_comp (N : Subgroup G) :
    phiN N = (((concreteEnvelope G).sub N).φ).comp ((concreteEnvelope G).sub N).ιH := by
  refine MonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
  · simp only [RingHom.comp_apply]
    rw [((concreteEnvelope G).sub N).φ_ι 1 r]
    simp only [phiN, RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    rfl
  · simp only [RingHom.comp_apply]
    rw [((concreteEnvelope G).sub N).φ_ι m 1]
    simp only [phiN, RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    rfl

/-- **`U_N ⊆ U(N)`**: the `∗`-regular closure of the image of `ℂ[↥N]` in `U(G)` is contained
in the image of the envelope inclusion `φ : U(N) ↪ U(G)`. -/
theorem closureCN_subset_range (N : Subgroup G) :
    (closureCN N : Set (concreteEnvelope G).U) ⊆ Set.range ((concreteEnvelope G).sub N).φ := by
  refine closureCN_le (S := rangeSubring (G := G) N) ?_
  rintro y ⟨x, rfl⟩
  exact ⟨((concreteEnvelope G).sub N).ιH x, by simp only [phiN_eq_comp, RingHom.comp_apply]⟩

/-- **JZLA20, Proposition 3.11, in the reduced form `Core311` implies the form `Prop311`.**

Given the `1 + A·t` property for `A` ranging over `U(N)`, the same holds for `A` ranging
over the smaller `∗`-regular closure `U_N`: lift `A` along the injection `U_N → U(N)`
provided by `closureCN_subset_range`, which is compatible with the inclusions into `U(G)`. -/
theorem prop311_of_core311 (G : Type*) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] :
    Work.ORP311.Core311 G → Work.ORP311.Prop311 G := by
  intro hcore H N hNH hN t hext n A
  have hex : ∀ x : closureCNty N,
      ∃ v : ((concreteEnvelope G).sub N).V, ((concreteEnvelope G).sub N).φ v =
        (x : (concreteEnvelope G).U) :=
    fun x => closureCN_subset_range (G := G) N x.2
  choose i hi using hex
  have hB := hcore H N hNH t hext n (A.map i)
  have hmap : (A.map i).map ((concreteEnvelope G).sub N).φ =
      A.map (closureCN.subtype N) := by
    rw [Matrix.map_map]
    ext p q
    simp only [Matrix.map_apply, Function.comp_apply, closureCN.subtype_apply]
    exact hi (A p q)
  rw [hmap] at hB
  exact hB

end Work.ORP311
