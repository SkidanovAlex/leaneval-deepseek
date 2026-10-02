import Mathlib
import Submission.Work.RatHurewicz.Cofibre.URetract

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homotopy equivalence `cofibreU ι ≃ E`

`cofibreU ι = {h < 1/2}` is the half-open cone on the fibre glued to `E`.  Because it has no apex
(the cone points of height `1` are excluded), the collapse `[x,t] ↦ ι x` of its cone part is
well defined, and it is a deformation retraction: the homotopy `[x,t] ↦ [x,(1-s)t]` shrinks the
height to `0` without ever leaving `{h < 1/2}`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The restricted quotient map `↥(q ⁻¹' cofibreU ι) → ↥(cofibreU ι)`. -/
def cofibreUQuot (ι : C(F, E)) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι),
      ↥(cofibreU ι)) where
  toFun p := ⟨Quotient.mk'' p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp continuous_subtype_val) _

theorem isQuotientMap_cofibreUQuot (ι : C(F, E)) :
    Topology.IsQuotientMap (cofibreUQuot ι) :=
  (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (cofibreRel ι))).restrictPreimage_isOpen
    (isOpen_cofibreU ι)

/-- The raw retraction is continuous on the preimage of `cofibreU ι`. -/
theorem continuous_uRetractFun (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    Continuous fun a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι) =>
      uRetractFun ι e₀ a.1 := by
  refine continuous_of_sumPiecewise ι (isOpen_coneLtHalfSet (F := F)) (ContinuousMap.id E)
    (coneBaseLtHalf ι) ?_ ?_ (preimage_cofibreU ι)
  · intro e; rfl
  · intro y hy
    show (if h : coneHeight y < cofibreHalf then coneBaseLtHalf ι ⟨y, h⟩ else e₀)
      = coneBaseLtHalf ι ⟨y, hy⟩
    rw [dif_pos (show coneHeight y < cofibreHalf from hy)]

/-- The raw retraction is constant on the fibres of the restricted quotient map. -/
theorem uRetractFun_factors (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    Function.FactorsThrough
      (fun a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι) =>
        uRetractFun ι e₀ a.1)
      (cofibreUQuot ι) := by
  intro a b hab
  have h : (Quotient.mk'' a.1 : cofibre ι) = Quotient.mk'' b.1 := congrArg Subtype.val hab
  exact uRetractFun_eq_of_eqvGen ι e₀ (Quotient.exact h) a.2 b.2

/-- **The retraction `cofibreU ι → E`**: the identity on `E` and the collapse of the half-open cone
onto its base. -/
def cofibreURetract (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) : C(↥(cofibreU ι), E) :=
  Topology.IsQuotientMap.lift (isQuotientMap_cofibreUQuot ι)
    ⟨fun a => uRetractFun ι e₀ a.1, continuous_uRetractFun ι e₀⟩ (uRetractFun_factors ι e₀)

/-- The computation rule of the retraction on a point of `E ⊕ Cone F` in the preimage. -/
theorem cofibreURetract_mk (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E)
    (a : E ⊕ Work.Stems.Cone F) (ha : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι)
      ⁻¹' cofibreU ι) :
    cofibreURetract ι e₀ ⟨Quotient.mk'' a, ha⟩ = uRetractFun ι e₀ a := by
  have h := Topology.IsQuotientMap.lift_comp (isQuotientMap_cofibreUQuot ι)
    ⟨fun a => uRetractFun ι e₀ a.1, continuous_uRetractFun ι e₀⟩ (uRetractFun_factors ι e₀)
  have h2 := congrFun (congrArg (fun k : C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι)
      ⁻¹' cofibreU ι), E) => ⇑k) h) ⟨a, ha⟩
  have hpt : (⟨Quotient.mk'' a, ha⟩ : ↥(cofibreU ι)) = cofibreUQuot ι ⟨a, ha⟩ := Subtype.ext rfl
  rw [hpt]
  exact h2

/-- The inclusion `E → ↥(cofibreU ι)`. -/
def cofibreUIncl (ι : C(F, E)) : C(E, ↥(cofibreU ι)) where
  toFun x := ⟨cofibreIncl ι x, cofibreIncl_mem_cofibreU ι x⟩
  continuous_toFun := Continuous.subtype_mk (cofibreIncl ι).continuous _

@[simp]
theorem cofibreUIncl_apply (ι : C(F, E)) (x : E) :
    (cofibreUIncl ι x : cofibre ι) = cofibreIncl ι x := rfl

/-- The retraction is a section of the inclusion. -/
theorem cofibreURetract_comp_cofibreUIncl (ι : C(F, E)) [Nonempty E] [Nonempty F] (e₀ : E) :
    (cofibreURetract ι e₀).comp (cofibreUIncl ι) = ContinuousMap.id E := by
  ext x
  show cofibreURetract ι e₀ (cofibreUIncl ι x) = x
  have hmem : (Sum.inl x : E ⊕ Work.Stems.Cone F) ∈
      (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreU ι :=
    cofibreIncl_mem_cofibreU ι x
  have hpt : (cofibreUIncl ι x : ↥(cofibreU ι)) = ⟨Quotient.mk'' (Sum.inl x), hmem⟩ :=
    Subtype.ext rfl
  rw [hpt, cofibreURetract_mk ι e₀ (Sum.inl x) hmem]
  rfl

/-- The point `[y, t]` of the cofibre, as an element of `cofibreU ι`, when `t < 1/2`. -/
theorem cofibreInclCone_mem_cofibreU (ι : C(F, E)) (y : Work.Stems.Cone F)
    (hy : coneHeight y < cofibreHalf) : cofibreInclCone ι y ∈ cofibreU ι :=
  (mem_cofibreU_coneIncl_iff ι y).mpr hy

end

end Work.RatHurewicz
