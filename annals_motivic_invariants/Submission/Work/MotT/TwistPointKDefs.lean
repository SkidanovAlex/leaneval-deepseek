import Mathlib
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.TransPlace
import Submission.Work.MotT.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared vocabulary for `Work.MotT.twistPointK_coords` (node T4, step 5)

This file collects the definitions and elementary lemmas that the coordinate step of the LAM
argument needs, so that the pieces of the proof can be stated in one common language:

* `plugHomAt E a b h : Coord E →ₐ[L] L` — evaluation of the affine coordinate ring at `(a,b)`;
* `evalAtLoc E a b : ↥(affPlaceAt E a b) →ₐ[L] L` — the residue map / evaluation of functions
  regular at the nonsingular affine point `(a,b)`, with the defining property
  `evalAtLoc (algebraMap (Coord E) _ r) = plugHomAt r`;
* `map_transAlgEquiv_affPlaceAt` — the general translation law for the local rings:
  `map τ_A (𝒪_{Q+A}) = 𝒪_Q`;
* `kleinTw_map` — `kleinTw` commutes with ring homomorphisms.

## Tags

elliptic curve, function field, place, Klein coordinates, Kummer twist
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT

noncomputable section

/-! ## §1 Evaluation at a nonsingular affine point -/

variable {L : Type} [Field L]

/-- Evaluation of the affine coordinate ring at a nonsingular affine point `(a,b)`. -/
noncomputable def plugHomAt (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) : Work.MotC2.Coord E →ₐ[L] L :=
  Work.MotC2.plugHom E a b (by
    simpa [Algebra.algebraMap_self, WeierstrassCurve.map_id] using h.1)

@[simp]
lemma plugHomAt_coordX (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    plugHomAt E a b h (Work.MotC2.coordX E) = a := by
  simp [plugHomAt]

@[simp]
lemma plugHomAt_coordY (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    plugHomAt E a b h (Work.MotC2.coordY E) = b := by
  simp [plugHomAt]

@[simp]
lemma plugHomAt_algebraMap (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) (c : L) :
    plugHomAt E a b h (algebraMap L (Work.MotC2.Coord E) c) = c :=
  (plugHomAt E a b h).commutes c

@[simp]
lemma plugHomAt_algebraMap_K (E : WeierstrassCurve L) (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) {K : Type} [Field K] [Algebra K L]
    (c : K) :
    plugHomAt E a b h (algebraMap K (Work.MotC2.Coord E) c) = algebraMap K L c := by
  rw [IsScalarTower.algebraMap_apply K L (Work.MotC2.Coord E)]
  exact (plugHomAt E a b h).commutes (algebraMap K L c)

/-- The kernel of the evaluation at the nonsingular affine point `(a,b)` is the maximal ideal
`⟨x - a, y - b⟩`. -/
lemma ker_plugHomAt (E : WeierstrassCurve L) [E.IsElliptic] (a b : L)
    (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    RingHom.ker (plugHomAt E a b h).toRingHom = Work.MotC2.affPlaceIdeal E a b := by
  haveI : Work.MotC2.IsNonsingularPoint E a b := ⟨h⟩
  refine (Ideal.IsMaximal.eq_of_le (Work.MotC2.instIsMaximalAffPlaceIdeal E a b) ?_ ?_).symm
  · intro htop
    have h1 : (1 : Work.MotC2.Coord E) ∈ RingHom.ker (plugHomAt E a b h).toRingHom := by
      rw [htop]; trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  · rw [Work.MotC2.affPlaceIdeal, CoordinateRing.XYIdeal, Ideal.span_le]
    rintro x (rfl | rfl)
    · change CoordinateRing.XClass E a ∈ RingHom.ker (plugHomAt E a b h).toRingHom
      rw [RingHom.mem_ker, Work.MotC2.XClass_eq_coordX_sub, map_sub]
      change (plugHomAt E a b h) (Work.MotC2.coordX E) -
        (plugHomAt E a b h) (algebraMap L (Work.MotC2.Coord E) a) = 0
      rw [plugHomAt_coordX, plugHomAt_algebraMap, sub_self]
    · change CoordinateRing.YClass E (Polynomial.C b) ∈
        RingHom.ker (plugHomAt E a b h).toRingHom
      rw [RingHom.mem_ker, Work.MotC2.YClass_eq_coordY_sub, map_sub]
      change (plugHomAt E a b h) (Work.MotC2.coordY E) -
        (plugHomAt E a b h) (algebraMap L (Work.MotC2.Coord E) b) = 0
      rw [plugHomAt_coordY, plugHomAt_algebraMap, sub_self]

/-- **The residue map at a nonsingular affine point**: the evaluation of a function regular at
`(a,b)`, as an `L`-algebra homomorphism from the local ring `↥(affPlaceAt E a b)` to `L`.  It is
constructed as the localization of `plugHomAt` and satisfies
`evalAtLoc (algebraMap (Coord E) _ r) = plugHomAt E a b h r`. -/
noncomputable def evalAtLoc (E : WeierstrassCurve L) [E.IsElliptic] (a b : L)
    [hns : Work.MotC2.IsNonsingularPoint E a b] : ↥(Work.MotC2.affPlaceAt E a b) →ₐ[L] L :=
  let hg : ∀ y : ↥(Work.MotC2.affPlaceIdeal E a b).primeCompl,
      IsUnit ((plugHomAt E a b hns.nonsingular).toRingHom y) := fun y => by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hy : (y : Work.MotC2.Coord E) ∈
        RingHom.ker (plugHomAt E a b hns.nonsingular).toRingHom :=
      RingHom.mem_ker.mpr h0
    rw [ker_plugHomAt E a b hns.nonsingular] at hy
    exact y.2 hy
  { toRingHom := IsLocalization.lift hg
    commutes' := fun c => by
      have h1 : (algebraMap L ↥(Work.MotC2.affPlaceAt E a b)) c =
          (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b))
            ((algebraMap L (Work.MotC2.Coord E)) c) :=
        (Work.MotC2.affPlaceAt_algebraMap_algebraMap E a b c).symm
      rw [h1]
      exact (IsLocalization.lift_eq (M := (Work.MotC2.affPlaceIdeal E a b).primeCompl) hg
        (algebraMap L (Work.MotC2.Coord E) c)).trans
        ((plugHomAt E a b hns.nonsingular).commutes c) }

/-- The defining property of `evalAtLoc`. -/
@[simp]
lemma evalAtLoc_algebraMap (E : WeierstrassCurve L) [E.IsElliptic] (a b : L)
    [hns : Work.MotC2.IsNonsingularPoint E a b] (r : Work.MotC2.Coord E) :
    evalAtLoc E a b (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) r) =
      plugHomAt E a b hns.nonsingular r :=
  IsLocalization.lift_eq _ r

@[simp]
lemma evalAtLoc_algebraMap_L (E : WeierstrassCurve L) [E.IsElliptic] (a b : L)
    [hns : Work.MotC2.IsNonsingularPoint E a b] (c : L) :
    evalAtLoc E a b (algebraMap L ↥(Work.MotC2.affPlaceAt E a b) c) = c :=
  (evalAtLoc E a b).commutes c

/-- Two `L`-algebra homomorphisms out of `↥(affPlaceAt E a b)` agreeing on the image of the
coordinate ring are equal: the local ring is a localization of `Coord E`, so a ring homomorphism
out of it is determined by its restriction to `Coord E`. -/
lemma evalAtLoc_ext (E : WeierstrassCurve L) [E.IsElliptic] (a b : L)
    [hns : Work.MotC2.IsNonsingularPoint E a b]
    {f g : ↥(Work.MotC2.affPlaceAt E a b) →ₐ[L] L}
    (h : ∀ r : Work.MotC2.Coord E,
      f (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) r) =
        g (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E a b) r)) : f = g := by
  have hker : f.toRingHom.comp (algebraMap (Work.MotC2.Coord E)
        ↥(Work.MotC2.affPlaceAt E a b)) =
      g.toRingHom.comp (algebraMap (Work.MotC2.Coord E)
        ↥(Work.MotC2.affPlaceAt E a b)) :=
    RingHom.ext fun r => h r
  have hf : f.toRingHom = g.toRingHom :=
    IsLocalization.ringHom_ext (Work.MotC2.affPlaceIdeal E a b).primeCompl hker
  exact AlgHom.coe_ringHom_injective hf

/-- **The general translation law for the local rings.**  For affine nonsingular points
`Q = (q₁,q₂)` and `Q' = (q₁',q₂')` with `Q + A = Q'`, translation by `A` carries the local ring at
`Q'` onto the local ring at `Q`: `map τ_A (𝒪_{Q'}) = 𝒪_Q`.

This follows from `Work.MotC2.TransPlace` applied at `Q'` (`map τ_{Q'} 𝒪_{Q'} = 𝒪_O`) and at `Q`
(`map τ_{-Q} 𝒪_O = 𝒪_Q`), together with `τ_A = τ_{-Q} * τ_{Q'}`. -/
lemma map_transAlgEquiv_affPlaceAt (E : WeierstrassCurve L) [E.IsElliptic] [DecidableEq L]
    {q₁ q₂ q₁' q₂' : L} (h : WeierstrassCurve.Affine.Nonsingular E q₁ q₂)
    (h' : WeierstrassCurve.Affine.Nonsingular E q₁' q₂') (A : E.toAffine.Point)
    (hA : WeierstrassCurve.Affine.Point.some q₁ q₂ h + A
      = WeierstrassCurve.Affine.Point.some q₁' q₂' h') :
    Subalgebra.map (Work.MotC2.transAlgEquiv E A).toAlgHom
      (Work.MotC2.affPlaceAt E q₁' q₂') = Work.MotC2.affPlaceAt E q₁ q₂ := by
  have hA' : A = -(WeierstrassCurve.Affine.Point.some q₁ q₂ h) +
      WeierstrassCurve.Affine.Point.some q₁' q₂' h' := by
    rw [← hA]; abel
  have h1 : Work.MotC2.transAlgEquiv E A =
      Work.MotC2.transAlgEquiv E (-(WeierstrassCurve.Affine.Point.some q₁ q₂ h)) *
        Work.MotC2.transAlgEquiv E (WeierstrassCurve.Affine.Point.some q₁' q₂' h') := by
    rw [← Work.MotC2.transAlgEquiv_add E (-(WeierstrassCurve.Affine.Point.some q₁ q₂ h))
      (WeierstrassCurve.Affine.Point.some q₁' q₂' h'), hA']
  have hcomp : (Work.MotC2.transAlgEquiv E A).toAlgHom =
      (Work.MotC2.transAlgEquiv E (-(WeierstrassCurve.Affine.Point.some q₁ q₂ h))).toAlgHom.comp
        (Work.MotC2.transAlgEquiv E
          (WeierstrassCurve.Affine.Point.some q₁' q₂' h')).toAlgHom := by
    rw [h1]
    refine AlgHom.ext fun z => ?_
    exact AlgEquiv.mul_apply _ _ z
  rw [hcomp, ← Subalgebra.map_map, (Work.MotC2.TransPlace L E q₁' q₂' h').1]
  exact (Work.MotC2.TransPlace L E q₁ q₂ h).2

/-! ## §2 Small Klein-model lemmas -/

/-- `twMon` commutes with ring homomorphisms (the branch condition is on the indices only). -/
theorem twMon_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : R)
    (y : Fin 5 → R) (i l : Fin 5) :
    f (Work.MotV.twMon h y i l) = Work.MotV.twMon (f h) (fun j => f (y j)) i l := by
  unfold Work.MotV.twMon
  rw [map_mul, map_mul, apply_ite (f : R → S)]
  simp

/-- `kleinTw` commutes with ring homomorphisms (its coefficients are integers). -/
theorem kleinTw_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b h : R)
    (y : Fin 5 → R) (k : Fin 5) :
    f (Work.MotV.kleinTw a b h y k) =
      Work.MotV.kleinTw (f a) (f b) (f h) (fun i => f (y i)) k := by
  fin_cases k <;>
    simp only [Work.MotV.kleinTw, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      twMon_map f] <;>
    first | refl_ring1 | ring

/-- `kleinTw` is unchanged when the arguments are pushed through an injective ring homomorphism. -/
theorem kleinTw_of_map_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (a b h : R) (y : Fin 5 → R) (k : Fin 5)
    (hk : Work.MotV.kleinTw (f a) (f b) (f h) (fun i => f (y i)) k = 0) :
    Work.MotV.kleinTw a b h y k = 0 :=
  hf (by rw [map_zero, kleinTw_map]; exact hk)

end

end Work.MotT
