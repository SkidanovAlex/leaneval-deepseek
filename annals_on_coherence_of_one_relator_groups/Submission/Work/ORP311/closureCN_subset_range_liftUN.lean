/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JZLA20 Proposition 3.11 in the concrete `U(G)`)

# `U_N ⊆ range (liftUN N)`: the `∗`-regular closure of `ℂ[N]` lies in the image of `U(N)`

For a subgroup `N ≤ G` let

* `phiN N : ℂ[↥N] →+* U(G)` be the composite `ℂ[↥N] → ℂ[G] → U(G)`;
* `closureCN N = U_N` the `∗`-regular closure of the image of `phiN N` in `U(G)`
  (JZLA20, §3.1);
* `liftUN N : U(↥N) →+* U(G)` the inclusion of the algebra of operators affiliated to the
  group von Neumann algebra of `N` into that of `G`, obtained from the diagonal embedding
  `N(N) → N(G)` (`Work.ORVonNeumann.VonNeumannAlgebra.exists_liftU_of_diagHom`) — this is
  `((concreteEnvelope G).sub N).φ` as a function, but the two are *different* `Classical.choice`s
  and hence not definitionally equal.

**Main result.** `U_N ⊆ range (liftUN N)`, i.e. every element of the `∗`-regular closure of
`ℂ[N]` inside `U(G)` is in the image of the inclusion `U(N) ↪ U(G)`.

This is the structural input for the `Core311 ⇒ Prop311` reduction (see
`Submission/Work/ORP311/prop311_of_core311.lean`, whose `closureCN_subset_range` is the exact
analogue for the enveloping inclusion `(concreteEnvelope G).sub N`).  It is proved by the same
two ingredients:

* `liftUN N` is compatible with the structure maps (`liftUN_toU_eq_phiN`), so
  `range (phiN N) ⊆ range (liftUN N)`;
* `range (liftUN N)` is a `∗`-regular `∗`-subring of `U(G)` (`rangeSubringLift`,
  `instIsStarRegularRangeLift`), because `liftUN N` is an injective `∗`-ring homomorphism out
  of the `∗`-regular ring `U(↥N)`.

Then `closureCN_le` (the universal property of the `∗`-regular closure) applies.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs

set_option autoImplicit false

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ## The defining properties of `liftUN N`

`liftUN N` is `(exists_liftU_of_diagHom N ...).choose`, so all of its properties are read off
from `Classical.choose_spec` of that existence statement. -/

/-- The `choose_spec` of `Work.ORVonNeumann.VonNeumannAlgebra.exists_liftU_of_diagHom` as
applied in the definition of `Work.ORP311.P311.liftUN`: the lift is injective, `∗`-preserving,
and compatible with the structure maps `ℂ[↥N] → U(↥N)` and `ℂ[G] → U(G)` on the group basis. -/
theorem liftUN_spec (N : Subgroup G) :
    Function.Injective (P311.liftUN N) ∧
      (∀ v : (Rep.countableGroupVonNeumann (G := ↥N)).affiliated,
        P311.liftUN N (star v) = star (P311.liftUN N v)) ∧
      (∀ (h : ↥N) (c : ℂ),
        P311.liftUN N (VonNeumannAlgebra.toU (Rep.countableGroupVonNeumann (G := ↥N))
          (MonoidAlgebra.single h c)) =
          VonNeumannAlgebra.toU (Rep.countableGroupVonNeumann (G := G))
            (MonoidAlgebra.single (h : G) c)) :=
  let h := (VonNeumannAlgebra.exists_liftU_of_diagHom N (P311.cosetDataN N) (P311.PhiN N)
    (P311.PhiN_spec N).2.1 (P311.PhiN_spec N).2.2.1 (P311.PhiN_spec N).2.2.2).choose_spec
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem liftUN_injective (N : Subgroup G) : Function.Injective (P311.liftUN N) :=
  (liftUN_spec N).1

theorem liftUN_star (N : Subgroup G) :
    ∀ v : (Rep.countableGroupVonNeumann (G := ↥N)).affiliated,
      P311.liftUN N (star v) = star (P311.liftUN N v) :=
  (liftUN_spec N).2.1

/-! ## Compatibility of `liftUN N` with the structure maps -/

/-- **`liftUN N` is compatible with `phiN N`**: composing the structure map
`ℂ[↥N] → U(↥N)` with the lift `U(↥N) → U(G)` gives `phiN N`.

Both sides are ring homomorphisms `ℂ[↥N] →+* U(G)`; on the basis `single h c` this is the
third component of `liftUN_spec`, together with the definition of `phiN N` as the composite
`ℂ[↥N] → ℂ[G] → U(G)`. -/
theorem phiN_eq_comp_liftUN (N : Subgroup G) :
    phiN N = (P311.liftUN N).comp
      (VonNeumannAlgebra.toU (Rep.countableGroupVonNeumann (G := ↥N))) := by
  refine MonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
  · rw [RingHom.comp_apply, (liftUN_spec N).2.2 (1 : ↥N) r]
    simp only [phiN, iota_apply, RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    rfl
  · rw [RingHom.comp_apply, (liftUN_spec N).2.2 m 1]
    simp only [phiN, iota_apply, RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    rfl

/-- The elementwise form of `phiN_eq_comp_liftUN`. -/
theorem liftUN_toU_eq_phiN (N : Subgroup G) (x : MonoidAlgebra ℂ ↥N) :
    P311.liftUN N (VonNeumannAlgebra.toU (Rep.countableGroupVonNeumann (G := ↥N)) x) =
      phiN N x := by
  rw [phiN_eq_comp_liftUN N]
  rfl

/-! ## The image of `liftUN N` is a `∗`-regular `∗`-subring of `U(G)` -/

/-- The image of the lift `liftUN N : U(↥N) → U(G)` as a `∗`-subring of `U(G)`. -/
noncomputable def rangeSubringLift (N : Subgroup G) :
    Work.ORHughesFree.StarSubring (concreteEnvelope G).U where
  toSubring :=
    { carrier := Set.range (P311.liftUN N)
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, map_neg _ _⟩ }
  star_mem' := by rintro _ ⟨v, rfl⟩; exact ⟨star v, liftUN_star N v⟩

/-- The image of `liftUN N` is `∗`-regular: `liftUN N` is an injective `∗`-ring map from the
`∗`-regular ring `U(↥N)` onto it, and both von Neumann regularity and the properness of the
involution transport along such a map. -/
instance instIsStarRegularRangeLift (N : Subgroup G) :
    Work.ORHughesFree.IsStarRegular (rangeSubringLift (G := G) N) := by
  have hreg : Work.ORHughesFree.IsStarRegular
      ((Rep.countableGroupVonNeumann (G := ↥N)).affiliated) :=
    instIsStarRegularConcreteU ↥N
  refine ⟨⟨fun x => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨v, hv⟩ := x.2
    obtain ⟨w, hw⟩ := (inferInstance :
      Work.ORHughesFree.VonNeumannRegularRing
        ((Rep.countableGroupVonNeumann (G := ↥N)).affiliated)).exists_mul_inverse v
    refine ⟨⟨P311.liftUN N w, ⟨w, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show x.1 * P311.liftUN N w * x.1 = x.1
    rw [← hv, ← map_mul, ← map_mul, hw]
  · obtain ⟨v, hv⟩ := x.2
    have hval : star x.1 * x.1 = 0 := congrArg Subtype.val hx
    have h2 : P311.liftUN N (star v * v) = 0 := by
      rw [map_mul, liftUN_star N v, hv]
      exact hval
    have hv0 : star v * v = 0 := liftUN_injective N (by rw [h2, map_zero])
    have hzero : v = 0 := hreg.proper v hv0
    apply Subtype.ext
    show x.1 = 0
    rw [← hv, hzero, map_zero]

/-! ## The main result -/

theorem closureCN_subset_range_liftUN {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G) : (Work.ORP311.closureCN N : Set (Work.ORP311.concreteEnvelope G).U) ⊆ Set.range (Work.ORP311.P311.liftUN N) := by
  refine closureCN_le (S := rangeSubringLift (G := G) N) ?_
  rintro y ⟨x, rfl⟩
  exact ⟨VonNeumannAlgebra.toU (Rep.countableGroupVonNeumann (G := ↥N)) x,
    liftUN_toU_eq_phiN N x⟩

end Work.ORP311
