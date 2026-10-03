/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The image of `Φ` restricted to a subgroup lands in the division closure of `K[H]`

For a field `K`, a group `G`, a ring `U` and a ring homomorphism `φ : K[G] →+* U`, and a subgroup
`H ≤ G`, write

* `D_G = divisionClosure (Set.range φ)` for the division closure of `φ(K[G])` in `U`, and
* `D_H = divisionClosure (Set.range (φ ∘ K[H] ↪ K[G]))` for the division closure of `φ(K[H])`.

The universal morphisms `Φ_{G,U} : Rat(Kˣ × G) →+* D_G` and `Φ_{H,U} : Rat(Kˣ × H) →+* D_H`
of [JZLA20, Lemma 4.2] fit into the commutative square

```
Rat(Kˣ × H) --ofSubgroup--> Rat(Kˣ × G)
     |                            |
  Φ_{H,U}                      Φ_{G,U}
     v                            v
    D_H   ---inclDH---------->   D_G
```

because, by the universal property of `Rat(Kˣ × H)`, `Φ_{G,U}` restricted to `Rat(Kˣ × H)` is a
morphism of rational `Kˣ × H`-semirings and the inclusion `D_H ↪ D_G` is compatible with the
rational operations (a unit of `D_G` which lies in `D_H` is already a unit of `D_H`, since the
division closure is closed under inverses that exist in the ambient ring `U`).

Consequently `Φ_{G,U}(ofSubgroup β)` lies in `D_H` for every `β : Rat(Kˣ × H)`: this is the
statement proved here.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.Reduce
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.Section6.imElem_mul
import Submission.Work.ORHughesFree.Section6.ratOpClosure_smul
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_idem
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_mono

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- `D_H`, the division closure of `φ(K[↥H])` in `U`. -/
noncomputable abbrev DHU (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) : Subring U :=
  divisionClosure (Set.range (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype)))

/-- `D_G`, the division closure of `φ(K[G])` in `U`. -/
noncomputable abbrev DGU (φ : MonoidAlgebra K G →+* U) : Subring U :=
  divisionClosure (Set.range φ)

/-- The group-like unit `λ · h` of `K[↥H]`, mapped into `U` by `φ`, lies in `D_H` whenever
`(λ, h)` lies in `unitsTimesSubgroup H`. -/
theorem unitOf_mem_DHU (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (w : ↥(unitsTimesSubgroup (K := K) H)) :
    φ (unitOf (w : Kˣ × G)) ∈ (DHU φ H : Set U) := by
  have hwh : (w : Kˣ × G).2 ∈ H := mem_unitsTimesSubgroup.mp w.2
  refine subset_divisionClosure _ ⟨MonoidAlgebra.single ⟨(w : Kˣ × G).2, hwh⟩ ((w : Kˣ × G).1 : K), ?_⟩
  show φ (MonoidAlgebra.mapDomain H.subtype
      (MonoidAlgebra.single ⟨(w : Kˣ × G).2, hwh⟩ ((w : Kˣ × G).1 : K))) =
    φ (MonoidAlgebra.single ((w : Kˣ × G).2) ((w : Kˣ × G).1 : K))
  rw [MonoidAlgebra.mapDomain_single, Subgroup.subtype_apply]

/-- The image in `D_H` of the group-like unit `λ · h`, for `(λ, h) ∈ unitsTimesSubgroup H`. -/
noncomputable def smulElem (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (w : ↥(unitsTimesSubgroup (K := K) H)) : ↥(DHU φ H) :=
  ⟨φ (unitOf (w : Kˣ × G)), unitOf_mem_DHU φ H w⟩

@[simp] theorem smulElem_coe (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (w : ↥(unitsTimesSubgroup (K := K) H)) :
    ((smulElem φ H w : ↥(DHU φ H)) : U) = φ (unitOf (w : Kˣ × G)) := rfl

@[simp] theorem smulElem_mul (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (u v : ↥(unitsTimesSubgroup (K := K) H)) :
    smulElem φ H (u * v) = smulElem φ H u * smulElem φ H v := by
  apply Subtype.ext
  show φ (unitOf ((u * v : ↥(unitsTimesSubgroup (K := K) H)) : Kˣ × G)) =
    φ (unitOf (u : Kˣ × G)) * φ (unitOf (v : Kˣ × G))
  rw [show ((u * v : ↥(unitsTimesSubgroup (K := K) H)) : Kˣ × G) =
      (u : Kˣ × G) * (v : Kˣ × G) from rfl, unitOf_mul, map_mul]

@[simp] theorem smulElem_one (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    smulElem φ H 1 = 1 := by
  apply Subtype.ext
  show φ (unitOf ((1 : ↥(unitsTimesSubgroup (K := K) H)) : Kˣ × G)) = (1 : U)
  rw [show ((1 : ↥(unitsTimesSubgroup (K := K) H)) : Kˣ × G) = 1 from rfl, unitOf_one, map_one]

/-- `smulElem φ H w` is a unit of `D_H`, with inverse `smulElem φ H w⁻¹`. -/
theorem smulElem_isUnit (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (w : ↥(unitsTimesSubgroup (K := K) H)) :
    IsUnit (smulElem φ H w) ∧
      ∀ h : IsUnit (smulElem φ H w), ↑h.unit⁻¹ = smulElem φ H w⁻¹ := by
  have hright : smulElem φ H w * smulElem φ H w⁻¹ = 1 := by
    rw [← smulElem_mul, mul_inv_cancel, smulElem_one]
  have hleft : smulElem φ H w⁻¹ * smulElem φ H w = 1 := by
    rw [← smulElem_mul, inv_mul_cancel, smulElem_one]
  refine ⟨⟨⟨smulElem φ H w, smulElem φ H w⁻¹, hright, hleft⟩, rfl⟩, ?_⟩
  intro h
  have hw : h.unit = ⟨smulElem φ H w, smulElem φ H w⁻¹, hright, hleft⟩ :=
    Units.ext (IsUnit.unit_spec h)
  exact (congrArg (fun x : (↥(DHU φ H))ˣ => (↑x⁻¹ : ↥(DHU φ H))) hw).trans rfl

/-- The rational `↥(unitsTimesSubgroup H)`-semiring structure on `D_H`: the rational operation is
inversion on the units of `D_H`, and the two actions are multiplication by the images of the
group-like units `φ(λ·h)`, which lie in `D_H`. -/
noncomputable def ratStructSubgroup (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    RationalUSemiring ↥(unitsTimesSubgroup (K := K) H) ↥(DHU φ H) where
  ratOp := ratOpClosure _
  ratOp_zero := ratOpClosure_zero _
  smul w x := smulElem φ H w * x
  smulRight x w := x * smulElem φ H w
  smul_eq_mul u r := Subtype.ext (by simp)
  smulRight_eq_mul r u := Subtype.ext (by simp)
  smul_mul u v := by rw [smulElem_mul]; simp
  smul_one_one := by rw [smulElem_one]; simp
  smulRight_one_one := by rw [smulElem_one]; simp
  smulRight_one u := by simp
  rat_smul u v r := by
    have hu : IsUnit (smulElem φ H u) := (smulElem_isUnit φ H u).1
    have hv : IsUnit (smulElem φ H v) := (smulElem_isUnit φ H v).1
    have key : ratOpClosure (DHU φ H) (smulElem φ H u * r * smulElem φ H v) =
        ↑hv.unit⁻¹ * ratOpClosure (DHU φ H) r * ↑hu.unit⁻¹ :=
      ratOpClosure_smul (DHU φ H) hu hv r
    calc ratOpClosure (DHU φ H) (smulElem φ H u * (r * smulElem φ H v))
        = ratOpClosure (DHU φ H) (smulElem φ H u * r * smulElem φ H v) := by rw [mul_assoc]
      _ = ↑hv.unit⁻¹ * ratOpClosure (DHU φ H) r * ↑hu.unit⁻¹ := key
      _ = (smulElem φ H v⁻¹ * ratOpClosure (DHU φ H) r) * smulElem φ H u⁻¹ := by
            rw [(smulElem_isUnit φ H v).2 hv, (smulElem_isUnit φ H u).2 hu]

/-- The inclusion `D_H ↪ D_G` of the division closures. -/
noncomputable def toDG (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    ↥(DHU φ H) →+* ↥(DGU φ) :=
  Subring.inclusion (DivisionClosure.divisionClosure_mono (by
    rintro y ⟨x, rfl⟩
    exact ⟨MonoidAlgebra.mapDomainRingHom K H.subtype x, rfl⟩))

@[simp] theorem toDG_coe (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (z : ↥(DHU φ H)) :
    ((toDG φ H z : ↥(DGU φ)) : U) = (z : U) :=
  Subring.coe_inclusion _ z

/-- The inclusion `D_H ↪ D_G` is compatible with `ratOpClosure`: for `y ∈ D_H`, inverting `y` as
an element of `D_H` and then including it in `D_G` is the same as inverting `y` as an element of
`D_G`.  This is where the definition of a division closure is used: an element of `D_H` which is
invertible in `D_G` is already invertible in `D_H` (`divisionClosure_inv_mem`). -/
theorem toDG_ratOpClosure (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) (y : ↥(DHU φ H)) :
    toDG φ H (ratOpClosure (DHU φ H) y) = ratOpClosure (DGU φ) (toDG φ H y) := by
  classical
  by_cases hy : IsUnit y
  · have hy' : IsUnit (toDG φ H y) := hy.map (toDG φ H)
    have hlu : ratOpClosure (DHU φ H) y = ↑hy.unit⁻¹ := by
      unfold ratOpClosure; rw [dif_pos hy]
    have hru : ratOpClosure (DGU φ) (toDG φ H y) = ↑hy'.unit⁻¹ := by
      unfold ratOpClosure; rw [dif_pos hy']
    rw [hlu, hru]
    have ha1 : toDG φ H y * toDG φ H (↑hy.unit⁻¹) = 1 := by
      have h : toDG φ H (↑hy.unit) * toDG φ H (↑hy.unit⁻¹) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rwa [IsUnit.unit_spec hy] at h
    have hb1 : ↑hy'.unit⁻¹ * toDG φ H y = 1 := by
      have h := Units.inv_mul hy'.unit
      rwa [IsUnit.unit_spec hy'] at h
    calc toDG φ H (↑hy.unit⁻¹)
        = (↑hy'.unit⁻¹ * toDG φ H y) * toDG φ H (↑hy.unit⁻¹) := by rw [hb1, one_mul]
      _ = ↑hy'.unit⁻¹ * (toDG φ H y * toDG φ H (↑hy.unit⁻¹)) := by rw [mul_assoc]
      _ = ↑hy'.unit⁻¹ * 1 := by rw [ha1]
      _ = ↑hy'.unit⁻¹ := mul_one _
  · have hy0 : ratOpClosure (DHU φ H) y = 0 := by
      unfold ratOpClosure; rw [dif_neg hy]
    rw [hy0, map_zero]
    have hnot : ¬ IsUnit (toDG φ H y) := by
      intro h
      have hyU : (y : U) * ((↑h.unit⁻¹ : ↥(DGU φ)) : U) = 1 := by
        have h1 : toDG φ H y * ↑h.unit⁻¹ = 1 := by
          have h' := Units.mul_inv h.unit
          rwa [IsUnit.unit_spec h] at h'
        have h2 := congrArg (fun z : ↥(DGU φ) => (z : U)) h1
        rw [Subring.coe_mul, Subring.coe_one, toDG_coe] at h2
        exact h2
      have hyU' : ((↑h.unit⁻¹ : ↥(DGU φ)) : U) * (y : U) = 1 := by
        have h1 : ↑h.unit⁻¹ * toDG φ H y = 1 := by
          have h' := Units.inv_mul h.unit
          rwa [IsUnit.unit_spec h] at h'
        have h2 := congrArg (fun z : ↥(DGU φ) => (z : U)) h1
        rw [Subring.coe_mul, Subring.coe_one, toDG_coe] at h2
        exact h2
      have hmem : ((↑h.unit⁻¹ : ↥(DGU φ)) : U) ∈ (DHU φ H : Set U) :=
        DivisionClosure.divisionClosure_inv_mem _ y.2 hyU hyU'
      refine hy ⟨⟨y, ⟨((↑h.unit⁻¹ : ↥(DGU φ)) : U), hmem⟩, ?_, ?_⟩, rfl⟩
      · exact Subtype.ext hyU
      · exact Subtype.ext hyU'
    have hgoal : ratOpClosure (DGU φ) (toDG φ H y) = 0 := by
      unfold ratOpClosure; rw [dif_neg hnot]
    rw [hgoal]

theorem Phi_subgroup_mem {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (β : Work.ORHughesFree.RatU ↥(Work.ORHughesFree.unitsTimesSubgroup (K := K) H)) :
    (((Work.ORHughesFree.Phi φ) (Work.ORHughesFree.RatU.ofSubgroup
        (Work.ORHughesFree.unitsTimesSubgroup (K := K) H) β) : U)) ∈
      (Work.ORHughesFree.divisionClosure
        (Set.range (φ.comp (MonoidAlgebra.mapDomainRingHom K H.subtype))) : Subring U) := by
  let W : Subgroup (Kˣ × G) := unitsTimesSubgroup (K := K) H
  let g : RatU ↥W →+* ↥(DHU φ H) := RatU.lift (↥(DHU φ H)) (ratStructSubgroup φ H)
  have hhom : IsRationalUSemiringHom (RatU.rational)
      (RationalUSemiring.restrict W (ratStruct φ)) ((toDG φ H).comp g) :=
  { map_rat := fun x => by
      change toDG φ H (g (RatU.ratOp x)) =
        (RationalUSemiring.restrict W (ratStruct φ)).ratOp (toDG φ H (g x))
      rw [show g (RatU.ratOp x) = ratOpClosure (DHU φ H) (g x) from
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_rat x]
      rw [toDG_ratOpClosure φ H (g x)]
      change ratOpClosure (DGU φ) (toDG φ H (g x)) =
        (ratStruct φ).ratOp (toDG φ H (g x))
      rw [ratStruct_ratOp]
    map_smul := fun u x => by
      change toDG φ H (g (RatU.smul u x)) =
        (RationalUSemiring.restrict W (ratStruct φ)).smul u (toDG φ H (g x))
      rw [show g (RatU.smul u x) = (ratStructSubgroup φ H).smul u (g x) from
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_smul u x]
      change toDG φ H (smulElem φ H u * g x) =
        (RationalUSemiring.restrict W (ratStruct φ)).smul u (toDG φ H (g x))
      apply Subtype.ext
      simp only [Subring.coe_mul, toDG_coe, RationalUSemiring.restrict_smul, ratStruct_smul,
        smulElem_coe]
    map_smulRight := fun x u => by
      change toDG φ H (g (RatU.smulRight x u)) =
        (RationalUSemiring.restrict W (ratStruct φ)).smulRight (toDG φ H (g x)) u
      rw [show g (RatU.smulRight x u) = (ratStructSubgroup φ H).smulRight (g x) u from
        (RatU.lift_isHom (↥(DHU φ H)) (ratStructSubgroup φ H)).map_smulRight x u]
      change toDG φ H (g x * smulElem φ H u) =
        (RationalUSemiring.restrict W (ratStruct φ)).smulRight (toDG φ H (g x)) u
      apply Subtype.ext
      simp only [Subring.coe_mul, toDG_coe, RationalUSemiring.restrict_smulRight,
        ratStruct_smulRight, smulElem_coe] }
  have heq : (toDG φ H).comp g = (Phi φ).comp (RatU.ofSubgroup W) := by
    rw [RatU.lift_unique (↥(DGU φ)) (RationalUSemiring.restrict W (ratStruct φ)) _ hhom,
      Phi_comp_ofSubgroup φ W]
  have hb : toDG φ H (g β) = (Phi φ) (RatU.ofSubgroup W β) := by
    have h1 := congrFun (congrArg DFunLike.coe heq) β
    simpa using h1
  have h2 : ((Phi φ) (RatU.ofSubgroup W β) : U) = ((g β : ↥(DHU φ H)) : U) := by
    rw [← hb, toDG_coe]
  change ((Phi φ) (RatU.ofSubgroup W β) : U) ∈ (DHU φ H : Subring U)
  rw [h2]
  exact (g β).2

end Work.ORHughesFree.Section6