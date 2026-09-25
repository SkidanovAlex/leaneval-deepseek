/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local action of the decomposition group on `L_wˣ`

This module sets up the local vocabulary needed for
`NK.HassePrinciple.subsingleton_groupCohomology_one_ideleRep`:

* `onePlace w u` — the idèle which is `u` at the place `w` and `1` elsewhere;
* `actVal g w u` — the image of a local unit `u` at `w` under the action of `g`, as a local unit
  at `g • w`, i.e. `u` transported by the canonical isomorphism `L_w ≃+* L_{g w}`;
* `localAut w σ` — for `σ` in the stabiliser `H_w` of `w`, the resulting automorphism of the local
  field `L_w`, and `localAutHom w : H_w →* (L_w ≃+* L_w)` — the faithful action of `H_w` on `L_w`
  by field automorphisms.

The comparison with the action on idèles is `smul_apply_smul_place`: the value of a translate at
the translated place is the image of the original component.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_idele
import Submission.NK.GlobalCFT.Galois.globalCFT_mul_smul_idele
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_principalIdele

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

section Basics

variable {L : Type} [Field L] [NumberField L]

/-- **The idèle with `u` at the place `w` and `1` elsewhere.** -/
noncomputable def onePlace (w : Place L) (u : (Place.localField L w)ˣ) : Idele L := by
  classical
  exact ⟨fun v => if h : v = w then h.symm ▸ u else 1, by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton w) ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    by_contra hne
    exact hv (by rw [dif_neg (by simpa using hne)]; exact Subgroup.one_mem _)⟩

@[simp] theorem onePlace_apply_self (w : Place L) (u : (Place.localField L w)ˣ) :
    onePlace w u w = u := by
  classical
  show (if h : w = w then h.symm ▸ u else 1) = u
  rw [dif_pos rfl]

theorem onePlace_apply_ne {v w : Place L} (h : v ≠ w) (u : (Place.localField L w)ˣ) :
    onePlace w u v = 1 := by
  classical
  show (if h' : v = w then h'.symm ▸ u else 1) = 1
  rw [dif_neg h]

/-- The transport of an element along an equality of places, in the `RingEquiv.cast` form. -/
theorem ringEquiv_cast_apply_eq {a b : Place L} (h : a = b) (x : Place.localField L a) :
    (RingEquiv.cast (R := fun v : Place L => Place.localField L v) h) x = h ▸ x := by
  cases h; rfl

/-- Cancelling a transport along an equality and back. -/
theorem eqRec_symm_eqRec {a b : Place L} (h : a = b) (z : Place.localField L a) :
    (h.symm ▸ (h ▸ z) : Place.localField L a) = z := by cases h; rfl

/-- The coercion of a transported unit is the transport of the coercion. -/
theorem units_val_cast {a b : Place L} (h : a = b) (u : (Place.localField L a)ˣ) :
    (((h ▸ u : (Place.localField L b)ˣ)) : Place.localField L b) =
      (h ▸ (u : Place.localField L a) : Place.localField L b) := by
  cases h; rfl

/-- The transport of a component (a unit) of an idèle along an equality of places. -/
theorem units_transport {a b : Place L} (h : a = b) (y : Idele L) :
    (h ▸ (y a : (Place.localField L a)ˣ)) = (y b : (Place.localField L b)ˣ) := by
  refine Units.ext ?_
  rw [units_val_cast]
  exact NK.GlobalCFT.Galois.globalCFT_cast_dep_apply
    (fun v => ((y v : (Place.localField L v)ˣ) : Place.localField L v)) h

/-- The transport of a component of an idèle along an equality of places. -/
theorem idele_transport {a b : Place L} (h : a = b) (y : Idele L) :
    ((y a : (Place.localField L a)ˣ) : Place.localField L a) =
      (h ▸ ((y b : (Place.localField L b)ˣ) : Place.localField L b) :
        Place.localField L a) := by
  have h2 := NK.GlobalCFT.Galois.globalCFT_cast_dep_apply
    (fun v => ((y v : (Place.localField L v)ˣ) : Place.localField L v)) h
  have h3 := congrArg (fun z => (h.symm ▸ z : Place.localField L a)) h2
  rw [eqRec_symm_eqRec] at h3
  exact h3

end Basics

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The automorphism of the local field `L_w` attached to an element `σ` of the stabiliser of
`w`**: the canonical isomorphism `L_w ≃+* L_{σ w}` transported along `σ • w = w`. -/
noncomputable def localAut (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    Place.localField L w ≃+* Place.localField L w :=
  (Place.localRingEquiv σ.1 w).trans
    (RingEquiv.cast (R := fun v : Place L => Place.localField L v)
      (MulAction.mem_stabilizer_iff.mp σ.2))

theorem localAut_apply (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (x : Place.localField L w) :
    localAut w σ x =
      (RingEquiv.cast (R := fun v : Place L => Place.localField L v)
        (MulAction.mem_stabilizer_iff.mp σ.2)) (Place.localRingEquiv σ.1 w x) :=
  rfl

/-- The local automorphism attached to an element of the stabiliser is compatible with the
embeddings of `L`. -/
theorem localAut_algebraMap (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : L) :
    localAut w σ (algebraMap L (Place.localField L w) x) =
      algebraMap L (Place.localField L w) (σ.1 x) := by
  have h := MulAction.mem_stabilizer_iff.mp σ.2
  rw [localAut_apply, Place.localRingEquiv_algebraMap, ringEquiv_cast_apply_eq]
  exact NK.GlobalCFT.Galois.localField_cast_algebraMap h (σ.1 x)

theorem localAut_continuous (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    Continuous (localAut w σ : Place.localField L w → Place.localField L w) := by
  have h := MulAction.mem_stabilizer_iff.mp σ.2
  rw [show (localAut w σ : Place.localField L w → Place.localField L w) =
      fun y => (RingEquiv.cast (R := fun v : Place L => Place.localField L v) h)
        (Place.localRingEquiv σ.1 w y) from rfl]
  rw [show (fun y : Place.localField L w =>
      (RingEquiv.cast (R := fun v : Place L => Place.localField L v) h)
        (Place.localRingEquiv σ.1 w y))
    = fun y : Place.localField L w => h ▸ (Place.localRingEquiv σ.1 w y) from by
      funext y; rw [ringEquiv_cast_apply_eq]]
  exact NK.GlobalCFT.Galois.continuous_localField_cast h
    (NK.GlobalCFT.Galois.continuous_localRingEquiv σ.1 w)

/-- Two continuous ring automorphisms of a local field agreeing on the image of `L` are equal. -/
theorem localRingEquiv_ext_of_algebraMap {w : Place L} {f g : Place.localField L w ≃+* Place.localField L w}
    (hf : Continuous (f : Place.localField L w → Place.localField L w))
    (hg : Continuous (g : Place.localField L w → Place.localField L w))
    (h : ∀ x : L, f (algebraMap L (Place.localField L w) x) =
      g (algebraMap L (Place.localField L w) x)) : f = g := by
  have hdense : DenseRange (algebraMap L (Place.localField L w)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField w
  have hfun : (f : Place.localField L w → Place.localField L w) = g :=
    DenseRange.equalizer hdense hf hg (funext h)
  exact RingEquiv.ext (congrFun hfun)

/-- Two ring automorphisms of a field which agree on the non-zero elements are equal. -/
theorem ringEquiv_ext_of_units {w : Place L} {f g : Place.localField L w ≃+* Place.localField L w}
    (h : ∀ u : (Place.localField L w)ˣ,
      f (u : Place.localField L w) = g (u : Place.localField L w)) : f = g := by
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · subst hx; simp
  · exact h (Units.mk0 x hx)

/-- **The local automorphisms form a monoid homomorphism** from the stabiliser of `w` to the
automorphism group of the local field `L_w`. -/
noncomputable def localAutHom (w : Place L) :
    MulAction.stabilizer (L ≃ₐ[K] L) w →* (Place.localField L w ≃+* Place.localField L w) where
  toFun := localAut w
  map_one' := by
    refine localRingEquiv_ext_of_algebraMap (localAut_continuous w 1) continuous_id fun x => ?_
    rw [localAut_algebraMap]
    show algebraMap L (Place.localField L w) ((1 : MulAction.stabilizer (L ≃ₐ[K] L) w).1 x)
      = algebraMap L (Place.localField L w) x
    rw [OneMemClass.coe_one, AlgEquiv.one_apply]
  map_mul' σ τ := by
    refine localRingEquiv_ext_of_algebraMap (localAut_continuous w (σ * τ))
      ((localAut_continuous w σ).comp (localAut_continuous w τ)) fun x => ?_
    show (localAut w (σ * τ)) (algebraMap L (Place.localField L w) x) =
      (localAut w σ) ((localAut w τ) (algebraMap L (Place.localField L w) x))
    rw [localAut_algebraMap, localAut_algebraMap, localAut_algebraMap,
      Subgroup.coe_mul, AlgEquiv.mul_apply]

/-- The action of the stabiliser of `w` on `L_w` is faithful. -/
theorem localAutHom_injective (w : Place L) : Function.Injective (localAutHom (K := K) w) := by
  intro σ τ h
  refine Subtype.ext (AlgEquiv.ext fun x => ?_)
  have hx := congrArg (fun (φ : Place.localField L w ≃+* Place.localField L w) =>
      φ (algebraMap L (Place.localField L w) x)) h
  simp only [localAutHom, MonoidHom.coe_mk, OneHom.coe_mk] at hx
  rw [localAut_algebraMap, localAut_algebraMap] at hx
  exact (algebraMap L (Place.localField L w)).injective hx

/-- The composite `L_w → L_{g w} → L_{g⁻¹ (g w)}` of the two local isomorphisms is the transport
along `g⁻¹ • (g • w) = w`. -/
theorem symm_localRingEquiv_trans_eq_cast (g : L ≃ₐ[K] L) (w : Place L)
    (h : g⁻¹ • (g • w) = w) :
    ((Place.localRingEquiv g w).trans (Place.localRingEquiv g⁻¹ (g • w)))
      = RingEquiv.cast (R := fun v : Place L => Place.localField L v) h.symm := by
  refine RingEquiv.ext fun x => ?_
  have hdense : DenseRange (algebraMap L (Place.localField L w)) :=
    NK.GlobalCFT.Galois.denseRange_algebraMap_localField w
  have hcont₁ : Continuous (fun y : Place.localField L w =>
      (Place.localRingEquiv g⁻¹ (g • w)) (Place.localRingEquiv g w y)) :=
    (NK.GlobalCFT.Galois.continuous_localRingEquiv g⁻¹ (g • w)).comp
      (NK.GlobalCFT.Galois.continuous_localRingEquiv g w)
  have hcont₂ : Continuous (fun y : Place.localField L w =>
      (h.symm ▸ y : Place.localField L (g⁻¹ • (g • w)))) :=
    NK.GlobalCFT.Galois.continuous_localField_cast h.symm continuous_id
  have hfun : (fun y : Place.localField L w =>
      (Place.localRingEquiv g⁻¹ (g • w)) (Place.localRingEquiv g w y))
      = fun y : Place.localField L w => (h.symm ▸ y : Place.localField L (g⁻¹ • (g • w))) := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext z
    simp only [Function.comp_apply]
    rw [Place.localRingEquiv_algebraMap, Place.localRingEquiv_algebraMap]
    have hgz : g⁻¹ (g z) = z := by
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [hgz]
    exact (NK.GlobalCFT.Galois.localField_cast_algebraMap h.symm z).symm
  rw [RingEquiv.trans_apply, ringEquiv_cast_apply_eq]
  exact congrFun hfun x

/-- **The inverse of the local isomorphism `L_w ≃+* L_{g w}` followed by the transport is the
local isomorphism `L_w ≃+* L_{g w}`.** -/
theorem symm_localRingEquiv_cast_apply (g : L ≃ₐ[K] L) (w : Place L)
    (h : g⁻¹ • (g • w) = w) (x : Place.localField L w) :
    (Place.localRingEquiv g⁻¹ (g • w)).symm
        ((RingEquiv.cast (R := fun v : Place L => Place.localField L v) h.symm) x) =
      Place.localRingEquiv g w x := by
  have hx : (RingEquiv.cast (R := fun v : Place L => Place.localField L v) h.symm) x =
      (Place.localRingEquiv g⁻¹ (g • w)) (Place.localRingEquiv g w x) := by
    have hpt := congrFun (congrArg (fun (e : Place.localField L w ≃+*
      Place.localField L (g⁻¹ • (g • w))) => (e : Place.localField L w →
        Place.localField L (g⁻¹ • (g • w)))) (symm_localRingEquiv_trans_eq_cast g w h)) x
    rw [RingEquiv.trans_apply] at hpt
    exact hpt.symm
  rw [hx, RingEquiv.symm_apply_apply]

/-- **The image of a local unit under the action of `g`**, as a local unit at `g • w`. -/
noncomputable def actVal (g : L ≃ₐ[K] L) (w : Place L) (u : (Place.localField L w)ˣ) :
    (Place.localField L (g • w))ˣ :=
  Units.map (Place.localRingEquiv g w).toMonoidHom u

@[simp] theorem actVal_one (g : L ≃ₐ[K] L) (w : Place L) : actVal g w 1 = 1 := map_one _

theorem actVal_mul (g : L ≃ₐ[K] L) (w : Place L) (u v : (Place.localField L w)ˣ) :
    actVal g w (u * v) = actVal g w u * actVal g w v := map_mul _ _ _

theorem actVal_inv (g : L ≃ₐ[K] L) (w : Place L) (u : (Place.localField L w)ˣ) :
    actVal g w u⁻¹ = (actVal g w u)⁻¹ := map_inv _ _

theorem actVal_div (g : L ≃ₐ[K] L) (w : Place L) (u v : (Place.localField L w)ˣ) :
    actVal g w (u / v) = actVal g w u / actVal g w v := map_div _ _ _

/-- **Composition law for the action on local components.** -/
theorem actVal_comp (g₁ g₂ : L ≃ₐ[K] L) (w : Place L) (u : (Place.localField L w)ˣ) :
    actVal (g₁ * g₂) w u =
      (mul_smul g₁ g₂ w).symm ▸ actVal g₁ (g₂ • w) (actVal g₂ w u) := by
  refine Units.ext ?_
  rw [units_val_cast]
  simp only [actVal, Units.coe_map]
  show (Place.localRingEquiv (g₁ * g₂) w) ((u : Place.localField L w)) =
    (mul_smul g₁ g₂ w).symm ▸ (Place.localRingEquiv g₁ (g₂ • w))
      ((Place.localRingEquiv g₂ w) ((u : Place.localField L w)))
  exact NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp g₂ g₁ w
    (mul_smul g₁ g₂ w).symm (u : Place.localField L w)

/-- **The action of a stabiliser element on the `w`-component is the local automorphism.** -/
theorem actVal_stabilizer (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (u : (Place.localField L w)ˣ) :
    (MulAction.mem_stabilizer_iff.mp σ.2) ▸ actVal σ.1 w u =
      Units.map (localAut w σ).toMonoidHom u := by
  refine Units.ext ?_
  rw [units_val_cast]
  show (MulAction.mem_stabilizer_iff.mp σ.2) ▸
      ((Place.localRingEquiv σ.1 w) ((u : Place.localField L w)) : Place.localField L (σ.1 • w))
    = (RingEquiv.cast (R := fun v : Place L => Place.localField L v)
        (MulAction.mem_stabilizer_iff.mp σ.2))
      ((Place.localRingEquiv σ.1 w) ((u : Place.localField L w)))
  rw [← ringEquiv_cast_apply_eq]

/-- The action on an idèle at a place depends only on the component at the preimage place. -/
theorem smul_apply_eq_of_eq_at (g : L ≃ₐ[K] L) (w : Place L) {y z : Idele L}
    (h : y (g⁻¹ • w) = z (g⁻¹ • w)) : (g • y) w = (g • z) w := by
  rw [Idele.smul_apply, Idele.smul_apply]
  rw [h]

/-- **The value of a translate at the translated place is the image of the original component.** -/
theorem smul_apply_smul_place (g : L ≃ₐ[K] L) (w : Place L) (y : Idele L) :
    (g • y) (g • w) = actVal g w (y w) := by
  have h : g⁻¹ • (g • w) = w := by rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [smul_apply_eq_of_eq_at g (g • w) (y := y)
    (z := onePlace (g⁻¹ • (g • w)) (y (g⁻¹ • (g • w)))) (by rw [onePlace_apply_self])]
  rw [Idele.smul_apply, onePlace_apply_self]
  refine Units.ext ?_
  rw [Units.coe_map]
  show (Place.localRingEquiv g⁻¹ (g • w)).symm
      ((y (g⁻¹ • (g • w)) : (Place.localField L (g⁻¹ • (g • w)))ˣ) :
        Place.localField L (g⁻¹ • (g • w)))
    = (Place.localRingEquiv g w) ((y w) : Place.localField L w)
  rw [idele_transport h y]
  rw [← ringEquiv_cast_apply_eq]
  exact symm_localRingEquiv_cast_apply g w h ((y w) : Place.localField L w)

/-- **The component of a translate at a stabilised place is the local automorphism applied to the
component**, for an arbitrary idèle. -/
theorem smul_apply_stabilizer (w : Place L) (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (y : Idele L) :
    (σ.1 • y) w = Units.map (localAut w σ).toMonoidHom (y w) := by
  have h : σ.1 • w = w := MulAction.mem_stabilizer_iff.mp σ.2
  have h1 : (h ▸ ((σ.1 • y) (σ.1 • w))) = (h ▸ actVal σ.1 w (y w)) := by
    rw [smul_apply_smul_place]
  rw [← units_transport h (σ.1 • y), h1]
  exact actVal_stabilizer w σ (y w)

end Main

end NK.HassePrinciple