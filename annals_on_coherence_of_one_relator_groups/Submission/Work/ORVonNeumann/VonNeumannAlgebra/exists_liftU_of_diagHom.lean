/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The lift `U(H) →+* U(G)` induced by a diagonal algebra map `N(H) → N(G)`

Let `G` be a countable group, `H ≤ G` a subgroup, `C : CosetData G H` a right-coset
decomposition of `G` over `H`, and `Φ : N(H) →ₐ[ℂ] N(G)` a `*`-preserving injective
`ℂ`-algebra map which acts on `ℓ²(G)` "cosetwise":

`(Φ b) (C.e q y) = C.e q (b y)`   for all `b : N(H)`, `q : C.Q`, `y : ℓ²(H)`.

Then `Φ` sends non-zero-divisors of `N(H)` to non-zero-divisors of `N(G)`
(`Work.ORVonNeumann.Rep.Phi_mem_nonZeroDivisors`), so the ring homomorphism `f = Φ` followed
by the structure map `N(G) →+* U(G)` maps the Ore set of denominators into the units of
`U(G) = N(G)[(nzd)⁻¹]`.  The universal property of the Ore localisation
(`OreLocalization.universalHom`) therefore produces a ring homomorphism

`φ : U(H) = N(H)[(nzd)⁻¹] →+* U(G)`,

which this file proves to be injective, `*`-preserving, and compatible with the inclusions of
the group algebras `ℂ[H] ↪ U(H)`, `ℂ[G] ↪ U(G)` and with the structure maps
`N(H) → U(H)`, `N(G) → U(G)`.

## Main result

* `Work.ORVonNeumann.VonNeumannAlgebra.exists_liftU_of_diagHom`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Envelope
import Submission.Work.ORVonNeumann.Rep.CosetData
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumann
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumannOre
import Submission.Work.ORVonNeumann.Rep.exists_diagHom
import Submission.Work.ORVonNeumann.Rep.Phi_mem_nonZeroDivisors
import Submission.Work.ORVonNeumann.Ore.star_oreLocalization
import Submission.Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors
import Submission.Work.Rep.Ore.denseRange_of_injective
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.numOf
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.U
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.UStar

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.ORVonNeumann.VonNeumannAlgebra

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The numerator map `numOf D` is the ring homomorphism `numeratorRingHom`. -/
theorem numOf_eq_numeratorRingHom {G : Type*} [Group G] (D : GroupVonNeumannAlgebra G)
    (x : D.N) : numOf D x = OreLocalization.numeratorRingHom x := by
  rw [numOf_apply D x, OreLocalization.numeratorHom_apply (S := nonZeroDivisors D.N),
    OreLocalization.numeratorRingHom_apply]

/-- The numerator map of the Ore localisation, on numerators. -/
theorem numOf_oreDiv {G : Type*} [Group G] (D : GroupVonNeumannAlgebra G) (x : D.N) :
    numOf D x = x /ₒ (1 : nonZeroDivisors D.N) := by
  rw [numOf_apply D x, OreLocalization.numeratorHom_apply]

/-- **The universal lift of an injective ring homomorphism along an Ore localisation is
injective.**  If `f : R →+* T` is injective and `S` is an Ore set of `R` mapped into the units
of `T`, then `OreLocalization.universalHom f fS hf` is injective: on a fraction `r /ₒ s` it is
`↑(fS s)⁻¹ * f r`, which vanishes only if `f r = 0`, hence only if `r = 0`, hence only on the
fraction `0 /ₒ s = 0`. -/
theorem universalHom_injective_aux {R T : Type*} [Ring R] [Ring T] {S : Submonoid R}
    [OreLocalization.OreSet S] (f : R →+* T) (fS : S →* Units T)
    (hf : ∀ s : S, f s = fS s) (hinj : Function.Injective f) :
    Function.Injective (OreLocalization.universalHom f fS hf) := by
  have key : ∀ x : OreLocalization S R, OreLocalization.universalHom f fS hf x = 0 → x = 0 := by
    refine OreLocalization.ind (β := fun x => OreLocalization.universalHom f fS hf x = 0 → x = 0)
      ?_
    intro r s h
    rw [OreLocalization.universalHom_apply] at h
    have h2 : f r = 0 := by
      have h3 : (fS s : Units T) * ((↑(fS s)⁻¹) * f r) = (fS s : Units T) * 0 := by rw [h]
      simpa [mul_assoc] using h3
    have hr : r = 0 := hinj (by rw [h2, map_zero])
    rw [hr]
    exact OreLocalization.zero_oreDiv s
  intro x y hxy
  exact sub_eq_zero.mp (key (x - y) (by rw [map_sub, hxy, sub_self]))

/-- `toU` of a basis vector of the group algebra is `numOf` of the corresponding multiple of
the regular representation. -/
theorem toU_single {G : Type*} [Group G] (D : GroupVonNeumannAlgebra G) (g : G) (c : ℂ) :
    toU D (MonoidAlgebra.single g c) = numOf D (c • D.ρ g) := by
  rw [toU_apply, D.lift_single]
  exact (numOf_eq_numeratorRingHom D (c • D.ρ g)).symm

/-- **The diagonal algebra map sends the left regular representation of `H` to that of
`G`.**  Both operators agree on every coset block `C.e q y`: the one because of the defining
property `hΦform`, the other because left translations and the coset identifications commute
(`Rep.diagOp_apply_e`, `Rep.diagOp_leftRegOp`). -/
theorem Phi_leftRegularHom {H : Subgroup G} (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (h : ↥H) :
    Φ (Rep.leftRegularHom (G := ↥H) h) = Rep.leftRegularHom (G := G) (h : G) := by
  classical
  refine Subtype.ext ?_
  refine Rep.ext_of_eq_on_blocks C (fun q y => ?_)
  rw [hΦform (Rep.leftRegularHom (G := ↥H) h) q y, Rep.leftRegularHom_coe,
    Rep.leftRegularHom_coe, ← Rep.diagOp_apply_e C (Rep.leftRegOp h) q y,
    Rep.diagOp_leftRegOp C h]

section Diag

/-- `Φ` as a ring homomorphism between the commutant carriers of the two models. -/
noncomputable def diagRingHom (H : Subgroup G)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G)) :
    (Rep.countableGroupVonNeumann (G := ↥H)).N →+*
      (Rep.countableGroupVonNeumann (G := G)).N :=
  Φ.toRingHom

/-- `diagRingHom` is the restriction of `Φ`. -/
theorem diagRingHom_apply (H : Subgroup G)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (b : (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagRingHom H Φ b = Φ (b : ↥(groupVonNeumann ↥H)) := rfl

/-- `diagRingHom` is a `*`-map. -/
theorem diagRingHom_star (H : Subgroup G)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (b : (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagRingHom H Φ (star b) = star (diagRingHom H Φ b) :=
  hΦstar (b : ↥(groupVonNeumann ↥H))

/-- `diagRingHom` preserves non-zero-divisors. -/
theorem diagRingHom_mem_nonZeroDivisors (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (s : (Rep.countableGroupVonNeumann (G := ↥H)).N)
    (hs : s ∈ nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagRingHom H Φ s ∈ nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N :=
  Rep.Phi_mem_nonZeroDivisors C Φ hΦstar hΦform hs

/-- The induced map on the non-zero-divisors. -/
noncomputable def diagSub (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    ↥(nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N) →*
      ↥(nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N) :=
  { toFun := fun s =>
      ⟨diagRingHom H Φ (s : (Rep.countableGroupVonNeumann (G := ↥H)).N),
        diagRingHom_mem_nonZeroDivisors H C Φ hΦstar hΦform s s.2⟩
    map_one' := Subtype.ext (map_one (diagRingHom H Φ))
    map_mul' := fun s t => Subtype.ext (map_mul (diagRingHom H Φ)
      (s : (Rep.countableGroupVonNeumann (G := ↥H)).N)
      (t : (Rep.countableGroupVonNeumann (G := ↥H)).N)) }

/-- The composite `N(H) →+* U(G)`. -/
noncomputable def diagULift (H : Subgroup G)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G)) :
    (Rep.countableGroupVonNeumann (G := ↥H)).N →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated :=
  (numOf (Rep.countableGroupVonNeumann (G := G))).comp (diagRingHom H Φ)

/-- The non-zero-divisors of `N(H)`, viewed as units of `U(G)`. -/
noncomputable def diagUnits (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    ↥(nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N) →*
      Units (Rep.countableGroupVonNeumann (G := G)).affiliated :=
  (Ore.numUnitHom (R := (Rep.countableGroupVonNeumann (G := G)).N)
    (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N)).comp
    (diagSub H C Φ hΦstar hΦform)

/-- The defining property of `diagUnits`. -/
theorem diagUnits_spec (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (s : ↥(nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N)) :
    diagULift H Φ (s : (Rep.countableGroupVonNeumann (G := ↥H)).N) =
      ↑(diagUnits H C Φ hΦstar hΦform s) := by
  have h1 : (↑(diagUnits H C Φ hΦstar hΦform s) :
        (Rep.countableGroupVonNeumann (G := G)).affiliated) =
      ((diagSub H C Φ hΦstar hΦform s :
          ↥(nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N)) :
        (Rep.countableGroupVonNeumann (G := G)).N) /ₒ
        (1 : nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N) :=
    Ore.coe_numeratorUnit (s := diagSub H C Φ hΦstar hΦform s)
  rw [h1]
  exact (numOf_oreDiv (Rep.countableGroupVonNeumann (G := G))
    (diagSub H C Φ hΦstar hΦform s)).symm

/-- **The lift `U(H) →+* U(G)` induced by `Φ`.** -/
noncomputable def diagPhi (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    (Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated :=
  OreLocalization.universalHom (diagULift H Φ) (diagUnits H C Φ hΦstar hΦform)
    (diagUnits_spec H C Φ hΦstar hΦform)

/-- The value of `diagPhi` on the structure maps `N(H) → U(H)`, `N(G) → U(G)`. -/
theorem diagPhi_num (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (b : (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagPhi H C Φ hΦstar hΦform (numOf (Rep.countableGroupVonNeumann (G := ↥H)) b) =
      numOf (Rep.countableGroupVonNeumann (G := G)) (diagRingHom H Φ b) :=
  OreLocalization.universalHom_commutes (diagULift H Φ) (diagUnits H C Φ hΦstar hΦform)
    (diagUnits_spec H C Φ hΦstar hΦform)

/-- The `*`-conjugate `x ↦ (ψ (x⋆))⋆` of a ring homomorphism `ψ : U(H) →+* U(G)`. -/
noncomputable def starConj (H : Subgroup G)
    (ψ : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated) :
    (Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated :=
  { toFun := fun x => star (ψ (star x))
    map_one' := by simp
    map_zero' := by simp
    map_add' := by intro x y; simp only [map_add, star_add]
    map_mul' := by intro x y; simp only [map_mul, star_mul] }

/-- The `*`-conjugate of the lift is the lift itself: both are ring homomorphisms out of the
Ore localisation `U(H)` which agree on the numerators, hence on everything. -/
theorem starConj_eq_diagPhi (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    starConj H (diagPhi H C Φ hΦstar hΦform) = diagPhi H C Φ hΦstar hΦform := by
  refine OreLocalization.universalHom_unique (diagULift H Φ) (diagUnits H C Φ hΦstar hΦform)
    (diagUnits_spec H C Φ hΦstar hΦform) _ ?_
  intro r
  show star (diagPhi H C Φ hΦstar hΦform
    (star (OreLocalization.numeratorHom
      (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N) r))) = diagULift H Φ r
  rw [← numOf_apply (Rep.countableGroupVonNeumann (G := ↥H)) r]
  have h1 : star (numOf (Rep.countableGroupVonNeumann (G := ↥H)) r) =
      numOf (Rep.countableGroupVonNeumann (G := ↥H)) (star r) :=
    affiliated_star_numerator (Rep.countableGroupVonNeumann (G := ↥H)) r
  have hcomm : diagPhi H C Φ hΦstar hΦform
      (numOf (Rep.countableGroupVonNeumann (G := ↥H)) (star r)) = diagULift H Φ (star r) :=
    OreLocalization.universalHom_commutes (diagULift H Φ) (diagUnits H C Φ hΦstar hΦform)
      (diagUnits_spec H C Φ hΦstar hΦform)
  have h2 : diagULift H Φ (star r) =
      numOf (Rep.countableGroupVonNeumann (G := G)) (diagRingHom H Φ (star r)) := rfl
  have h3 : star (numOf (Rep.countableGroupVonNeumann (G := G)) (diagRingHom H Φ (star r))) =
      numOf (Rep.countableGroupVonNeumann (G := G)) (star (diagRingHom H Φ (star r))) :=
    affiliated_star_numerator (Rep.countableGroupVonNeumann (G := G)) _
  have h4 : star (diagRingHom H Φ (star r)) = diagRingHom H Φ r := by
    rw [diagRingHom_star H Φ hΦstar r, star_star]
  calc star (diagPhi H C Φ hΦstar hΦform
          (star (numOf (Rep.countableGroupVonNeumann (G := ↥H)) r)))
      = star (diagPhi H C Φ hΦstar hΦform
          (numOf (Rep.countableGroupVonNeumann (G := ↥H)) (star r))) := by rw [h1]
    _ = star (diagULift H Φ (star r)) := by rw [hcomm]
    _ = star (numOf (Rep.countableGroupVonNeumann (G := G)) (diagRingHom H Φ (star r))) := by
          rw [h2]
    _ = numOf (Rep.countableGroupVonNeumann (G := G)) (star (diagRingHom H Φ (star r))) := h3
    _ = numOf (Rep.countableGroupVonNeumann (G := G)) (diagRingHom H Φ r) := by rw [h4]
    _ = diagULift H Φ r := rfl

/-- **The lift is `*`-preserving.** -/
theorem diagPhi_star (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (v : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated) :
    diagPhi H C Φ hΦstar hΦform (star v) =
      star (diagPhi H C Φ hΦstar hΦform v) := by
  have h : starConj H (diagPhi H C Φ hΦstar hΦform) v =
      diagPhi H C Φ hΦstar hΦform v :=
    congrArg (fun (g : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated) => g v)
      (starConj_eq_diagPhi H C Φ hΦstar hΦform)
  have h' : star (diagPhi H C Φ hΦstar hΦform (star v)) =
      diagPhi H C Φ hΦstar hΦform v := h
  calc diagPhi H C Φ hΦstar hΦform (star v)
      = star (star (diagPhi H C Φ hΦstar hΦform (star v))) := (star_star _).symm
    _ = star (diagPhi H C Φ hΦstar hΦform v) := by rw [h']

/-- **The lift is injective.** -/
theorem diagPhi_injective (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (hΦinj : Function.Injective Φ) :
    Function.Injective (diagPhi H C Φ hΦstar hΦform) := by
  have hnum : Function.Injective (numOf (Rep.countableGroupVonNeumann (G := G))) := by
    intro a b hab
    have h1 : Function.Injective (OreLocalization.numeratorRingHom
        (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N)) :=
      OreLocalization.numeratorHom_inj
        (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N) inf_le_left
    exact h1 hab
  have hfinj : Function.Injective (diagULift H Φ) := by
    intro a b hab
    exact hΦinj (hnum hab)
  exact universalHom_injective_aux (diagULift H Φ) (diagUnits H C Φ hΦstar hΦform)
    (diagUnits_spec H C Φ hΦstar hΦform) hfinj

/-- `diagRingHom` is `ℂ`-linear. -/
theorem diagRingHom_smul (H : Subgroup G)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (c : ℂ) (x : (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagRingHom H Φ (c • x) = c • diagRingHom H Φ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  exact Φ.commutes c

/-- The left regular representation of `H`, as an element of the commutant carrier. -/
noncomputable def leftRegH (H : Subgroup G) (h : ↥H) :
    (Rep.countableGroupVonNeumann (G := ↥H)).N :=
  Rep.leftRegularHom (G := ↥H) h

/-- The left regular representation of `G`, as an element of the commutant carrier. -/
noncomputable def leftRegG (g : G) : (Rep.countableGroupVonNeumann (G := G)).N :=
  Rep.leftRegularHom (G := G) g

/-- The lift sends the regular representation of `H` to that of `G`. -/
theorem diagLeftReg (H : Subgroup G) (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q), ∀ y : l2 ↥H,
      (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (h : ↥H) :
    diagRingHom H Φ (leftRegH H h) = leftRegG (h : G) :=
  Phi_leftRegularHom C Φ hΦform h

/-- `toU` on a basis vector of `ℂ[H]`. -/
theorem toU_single_H (H : Subgroup G) (h : ↥H) (c : ℂ) :
    toU (Rep.countableGroupVonNeumann (G := ↥H)) (MonoidAlgebra.single h c) =
      numOf (Rep.countableGroupVonNeumann (G := ↥H)) (c • leftRegH H h) := by
  rw [toU_single (Rep.countableGroupVonNeumann (G := ↥H)) h c]
  rfl

/-- `toU` on a basis vector of `ℂ[G]`. -/
theorem toU_single_G (g : G) (c : ℂ) :
    toU (Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single g c) =
      numOf (Rep.countableGroupVonNeumann (G := G)) (c • leftRegG g) := by
  rw [toU_single (Rep.countableGroupVonNeumann (G := G)) g c]
  rfl

end Diag

theorem exists_liftU_of_diagHom {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) (C : Work.ORVonNeumann.Rep.CosetData G H) (Φ : ↥(Work.ORVonNeumann.groupVonNeumann ↥H) →ₐ[ℂ] ↥(Work.ORVonNeumann.groupVonNeumann G)) (hΦstar : ∀ b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H), Φ (star b) = star (Φ b)) (hΦinj : Function.Injective Φ) (hΦform : ∀ (b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) (q : C.Q), ∀ y : Work.ORVonNeumann.l2 ↥H, (Φ b : Work.ORVonNeumann.boundedEnd G) (C.e q y) = C.e q ((b : Work.ORVonNeumann.boundedEnd ↥H) y)) : ∃ φ : (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+* (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)).affiliated, Function.Injective φ ∧ (∀ v : (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := ↥H)).affiliated, φ (star v) = star (φ v)) ∧ (∀ (h : ↥H) (c : ℂ), φ (Work.ORVonNeumann.VonNeumannAlgebra.toU (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := ↥H)) (MonoidAlgebra.single h c)) = Work.ORVonNeumann.VonNeumannAlgebra.toU (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single (h : G) c)) ∧ (∀ b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H), φ (Work.ORVonNeumann.VonNeumannAlgebra.numOf (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := ↥H)) b) = Work.ORVonNeumann.VonNeumannAlgebra.numOf (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)) (Φ b)) := by
  refine ⟨diagPhi H C Φ hΦstar hΦform, ?_, ?_, ?_, ?_⟩
  · exact diagPhi_injective H C Φ hΦstar hΦform hΦinj
  · intro v
    exact diagPhi_star H C Φ hΦstar hΦform v
  · intro h c
    rw [toU_single_H H h c, toU_single_G (h : G) c]
    have h1 : diagRingHom H Φ (c • leftRegH H h) = c • leftRegG (h : G) := by
      rw [diagRingHom_smul H Φ c (leftRegH H h), diagLeftReg H C Φ hΦform h]
    rw [diagPhi_num H C Φ hΦstar hΦform (c • leftRegH H h), h1]
  · intro b
    exact diagPhi_num H C Φ hΦstar hΦform b

end Work.ORVonNeumann.VonNeumannAlgebra
