import Mathlib
import Submission.Work.RatHurewicz.Cofibre.ConeContract
import Submission.Work.RatHurewicz.Cofibre.Gluing
import Submission.Work.RatHurewicz.Cofibre.RelClass

/-!
# The contraction of the punctured cone `cofibreV ι`

`cofibreV ι = {z | 0 < cofibreHeight ι z}` is the image of the punctured cone
(`preimage_cofibreV`) and is contractible: push the height to `1` with `coneContractC`,
which keeps the height positive (`coneHeight_concContract_pos`).

This file provides the two ingredients of the descent of that contraction from the preimage
`q ⁻¹' cofibreV ι` to `cofibreV ι`:

* `cofibreVContract_mem` — the raw map takes values in `cofibreV ι` (so it corestricts);
* `cofibreVContractRaw` — the raw map is **continuous**, as a composite
  `(E ⊕ Cone F) × I --sumProdDistrib--> (E × I) ⊕ (Cone F × I) --Sum.elim--> cofibre ι`
  (the two *clopen* summands make the `Sum.elim` legitimate, with no representative extraction).

The remaining step is the descent along the quotient map `q' : ↥(q ⁻¹' cofibreV ι) → ↥(cofibreV ι)`
by `Topology.IsQuotientMap.continuous_lift_prod_right` (the product of a quotient map with the
locally compact `I` is a quotient map), whose well-definedness hypothesis is
`sumElim_const_cone_eq_of_eqvGen` (`Cofibre/RelClass.lean`), together with the two computation
rules `H (v, 0) = v` and `H (v, 1) = b` (both obtained from `IsQuotientMap.lift_comp` plus the
surjectivity of `q'`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The punctured-cone value of the contraction lies in `cofibreV ι`. -/
theorem mem_cofibreV_coneContract (ι : C(F, E)) (s : unitInterval) (y : Work.Stems.Cone F)
    (hy : (0 : unitInterval) < coneHeight y) :
    cofibreInclCone ι (coneContractC (s, y)) ∈ cofibreV ι :=
  (mem_cofibreV_coneIncl_iff ι (coneContractC (s, y))).mpr
    (coneHeight_concContract_pos (F := F) s y hy)

/-- **The raw contraction map takes values in `cofibreV ι`.**  On the `Sum.inl` part the value is
irrelevant: those points have `cofibreHeightFun = 0` and are therefore not in the preimage of
`cofibreV ι`. -/
theorem cofibreVContract_mem (ι : C(F, E)) (x₀ : F) (s : unitInterval)
    (a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι)) :
    Sum.elim (fun _ : E => cofibreInclCone ι (Work.Stems.coneApex x₀))
      (fun y : Work.Stems.Cone F =>
        cofibreInclCone ι (coneContractC (s, y))) a.1 ∈ cofibreV ι := by
  rcases ha : a.1 with e | y
  · exfalso
    have h := a.2
    rw [Set.mem_preimage, ha, mem_cofibreV_iff] at h
    have h0 : cofibreHeight ι (Quotient.mk'' (Sum.inl e)) = 0 := cofibreHeight_incl ι e
    rw [h0] at h
    exact absurd h (not_lt.mpr le_rfl)
  · refine mem_cofibreV_coneContract ι s y ?_
    have h := a.2
    rw [Set.mem_preimage, ha] at h
    exact (mem_cofibreV_coneIncl_iff ι y).mp h

/-- **The raw contraction map is continuous.**  It is the composite of the coordinate map, the
homeomorphism `(E ⊕ Cone F) × I ≃ (E × I) ⊕ (Cone F × I)` and the `Sum.elim` of the two
continuous branches. -/
def cofibreVContractRaw (ι : C(F, E)) (x₀ : F) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) × unitInterval,
      cofibre ι) :=
  ((⟨Sum.elim (fun _ : E × unitInterval => cofibreInclCone ι (Work.Stems.coneApex x₀))
      (fun q : Work.Stems.Cone F × unitInterval =>
        cofibreInclCone ι (coneContractC (q.2, q.1))),
      continuous_const.sumElim ((cofibreInclCone ι).continuous.comp
        (coneContractC.continuous.comp
          (continuous_snd.prodMk continuous_fst)))⟩ :
      C((E × unitInterval) ⊕ (Work.Stems.Cone F × unitInterval), cofibre ι)).comp
    ⟨(⇑(Homeomorph.sumProdDistrib (X := E) (Y := Work.Stems.Cone F) (Z := unitInterval))),
      (Homeomorph.sumProdDistrib (X := E) (Y := Work.Stems.Cone F)
        (Z := unitInterval)).continuous⟩).comp
    ⟨fun p : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) ×
        unitInterval => (p.1.1, p.2),
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

/-- **The computation rule of the raw contraction map**: it *is* the explicit `Sum.elim`, once the
coordinate map and `Homeomorph.sumProdDistrib` are pushed through. -/
theorem cofibreVContractRaw_apply (ι : C(F, E)) (x₀ : F)
    (p : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) × unitInterval) :
    cofibreVContractRaw ι x₀ p =
      Sum.elim (fun _ : E => cofibreInclCone ι (Work.Stems.coneApex x₀))
        (fun y : Work.Stems.Cone F =>
          cofibreInclCone ι (coneContractC (p.2, y))) p.1.1 := by
  show (Sum.elim (fun _ : E × unitInterval => cofibreInclCone ι (Work.Stems.coneApex x₀))
      (fun q : Work.Stems.Cone F × unitInterval =>
        cofibreInclCone ι (coneContractC (q.2, q.1))))
      (⇑(Homeomorph.sumProdDistrib (X := E) (Y := Work.Stems.Cone F) (Z := unitInterval))
        (p.1.1, p.2)) = _
  rcases p.1.1 with e | y
  · first
      | rfl
      | simp only [Homeomorph.sumProdDistrib, Equiv.sumProdDistrib,
          Homeomorph.coe_toHomeomorphOfContinuousOpen, Equiv.coe_fn_symm_mk,
          Sum.elim_inl, Sum.elim_inr, Prod.fst_mk, Prod.snd_mk]
  · first
      | rfl
      | simp only [Homeomorph.sumProdDistrib, Equiv.sumProdDistrib,
          Homeomorph.coe_toHomeomorphOfContinuousOpen, Equiv.coe_fn_symm_mk,
          Sum.elim_inl, Sum.elim_inr, Prod.fst_mk, Prod.snd_mk]

/-- **The raw contraction map, corestricted to `cofibreV ι`.** -/
def cofibreVContractCore (ι : C(F, E)) (x₀ : F) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) × unitInterval,
      ↥(cofibreV ι)) :=
  ⟨fun p => ⟨cofibreVContractRaw ι x₀ p, by
      rw [cofibreVContractRaw_apply]
      exact cofibreVContract_mem ι x₀ p.2 p.1⟩,
    Continuous.subtype_mk (cofibreVContractRaw ι x₀).continuous (fun p => by
      rw [cofibreVContractRaw_apply]
      exact cofibreVContract_mem ι x₀ p.2 p.1)⟩

@[simp]
theorem cofibreVContractCore_apply (ι : C(F, E)) (x₀ : F)
    (p : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) × unitInterval) :
    (cofibreVContractCore ι x₀ p : cofibre ι) = cofibreVContractRaw ι x₀ p := rfl

/-! ## The descent of the contraction along the quotient map -/

/-- The quotient map `↥(q ⁻¹' cofibreV ι) → ↥(cofibreV ι)`, as a continuous map. -/
def cofibreVQuot (ι : C(F, E)) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι), ↥(cofibreV ι)) where
  toFun a := ⟨Quotient.mk'' a.1, a.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp continuous_subtype_val) (fun a => a.2)

theorem isQuotientMap_cofibreVQuot (ι : C(F, E)) :
    Topology.IsQuotientMap (cofibreVQuot ι) :=
  (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (cofibreRel ι))).restrictPreimage_isOpen
    (isOpen_cofibreV ι)

/-- The curried corestricted raw map, as a continuous map into the function space
`C(I, ↥cofibreV ι)` (continuity into the compact-open topology from the uncurried map). -/
def cofibreVContractCurried (ι : C(F, E)) (x₀ : F) :
    C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι),
      C(unitInterval, ↥(cofibreV ι))) where
  toFun a := ⟨fun s => cofibreVContractCore ι x₀ (a, s),
    (cofibreVContractCore ι x₀).continuous.comp (continuous_const.prodMk continuous_id)⟩
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
    (cofibreVContractCore ι x₀).continuous

@[simp]
theorem cofibreVContractCurried_apply (ι : C(F, E)) (x₀ : F)
    (a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι)) (s : unitInterval) :
    (cofibreVContractCurried ι x₀ a) s = cofibreVContractCore ι x₀ (a, s) := rfl

/-- **Well-definedness of the descent**: the curried corestricted raw map is constant on the fibres
of the quotient map `q'`.  For a fixed time `s` this is `sumElim_const_cone_eq_of_eqvGen`. -/
theorem cofibreVContractCurried_factors (ι : C(F, E)) (x₀ : F) :
    Function.FactorsThrough (cofibreVContractCurried ι x₀) (cofibreVQuot ι) := by
  intro a b hab
  have hq : (Quotient.mk'' a.1 : cofibre ι) = Quotient.mk'' b.1 := congrArg Subtype.val hab
  have hrel : Relation.EqvGen (cofibreRel ι) a.1 b.1 := Quotient.eq''.mp hq
  have key : ∀ c : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι),
      (0 : unitInterval) < cofibreHeightFun ι c.1 := by
    intro c
    have h := c.2
    rw [Set.mem_preimage, mem_cofibreV_iff] at h
    rcases hc : c.1 with e | y
    · rw [hc] at h
      simp only [cofibreHeight, cofibreHeightFun, Quotient.lift_mk, Sum.elim_inl] at h
      exact absurd h (not_lt.mpr le_rfl)
    · rw [hc] at h
      simpa only [cofibreHeight, cofibreHeightFun, Quotient.lift_mk, Sum.elim_inr] using h
  ext s
  rw [cofibreVContractCurried_apply, cofibreVContractCurried_apply]
  rw [cofibreVContractCore_apply, cofibreVContractCore_apply,
    cofibreVContractRaw_apply, cofibreVContractRaw_apply]
  exact sumElim_const_cone_eq_of_eqvGen ι (cofibreInclCone ι (Work.Stems.coneApex x₀))
    (fun y : Work.Stems.Cone F => cofibreInclCone ι (coneContractC (s, y)))
    hrel (key a) (key b)

/-- **The descended contraction, in curried form.** -/
def cofibreVContractQuot (ι : C(F, E)) (x₀ : F) :
    C(↥(cofibreV ι), C(unitInterval, ↥(cofibreV ι))) :=
  Topology.IsQuotientMap.lift (isQuotientMap_cofibreVQuot ι) (cofibreVContractCurried ι x₀)
    (cofibreVContractCurried_factors ι x₀)

/-- **The descended contraction** `↥cofibreV ι × I → ↥cofibreV ι`, the uncurrying of
`cofibreVContractQuot`. -/
def cofibreVContract (ι : C(F, E)) (x₀ : F) :
    C(↥(cofibreV ι) × unitInterval, ↥(cofibreV ι)) :=
  (cofibreVContractQuot ι x₀).uncurry

@[simp]
theorem cofibreVContract_apply (ι : C(F, E)) (x₀ : F)
    (v : ↥(cofibreV ι)) (s : unitInterval) :
    cofibreVContract ι x₀ (v, s) = (cofibreVContractQuot ι x₀ v) s := rfl

/-- **Second unit law of the contraction**: `H (v, 1)` is the apex point. -/
theorem cofibreVContract_one (ι : C(F, E)) (x₀ : F) (v : ↥(cofibreV ι)) :
    cofibreVContract ι x₀ (v, 1) =
      ⟨cofibreInclCone ι (Work.Stems.coneApex x₀),
        (mem_cofibreV_coneIncl_iff ι (Work.Stems.coneApex x₀)).mpr (by
          rw [coneHeight_coneApex]
          norm_num)⟩ := by
  obtain ⟨a, ha⟩ := (isQuotientMap_cofibreVQuot ι).surjective v
  subst ha
  have hstep : cofibreVContractQuot ι x₀ (cofibreVQuot ι a) = cofibreVContractCurried ι x₀ a :=
    congrFun (congrArg (fun k : C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
          cofibreV ι), C(unitInterval, ↥(cofibreV ι))) =>
        (⇑k : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) →
          C(unitInterval, ↥(cofibreV ι))))
      (Topology.IsQuotientMap.lift_comp (isQuotientMap_cofibreVQuot ι)
        (cofibreVContractCurried ι x₀) (cofibreVContractCurried_factors ι x₀))) a
  rw [cofibreVContract_apply, hstep, cofibreVContractCurried_apply]
  apply Subtype.ext
  show (cofibreVContractRaw ι x₀ (a, 1) : cofibre ι) = cofibreInclCone ι (Work.Stems.coneApex x₀)
  rw [cofibreVContractRaw_apply]
  rcases hc : a.1 with e | y
  · have h := a.2
    rw [Set.mem_preimage, mem_cofibreV_iff] at h
    rw [hc] at h
    simp only [cofibreHeight, cofibreHeightFun, Quotient.lift_mk, Sum.elim_inl] at h
    exact absurd h (not_lt.mpr le_rfl)
  · change cofibreInclCone ι (coneContractC (1, y)) =
      cofibreInclCone ι (Work.Stems.coneApex x₀)
    rw [coneContractC_one x₀]

/-- **First unit law of the contraction**: `H (v, 0) = v`. -/
theorem cofibreVContract_zero (ι : C(F, E)) (x₀ : F) (v : ↥(cofibreV ι)) :
    cofibreVContract ι x₀ (v, 0) = v := by
  obtain ⟨a, ha⟩ := (isQuotientMap_cofibreVQuot ι).surjective v
  subst ha
  have hstep : cofibreVContractQuot ι x₀ (cofibreVQuot ι a) = cofibreVContractCurried ι x₀ a :=
    congrFun (congrArg (fun k : C(↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
          cofibreV ι), C(unitInterval, ↥(cofibreV ι))) =>
        (⇑k : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' cofibreV ι) →
          C(unitInterval, ↥(cofibreV ι))))
      (Topology.IsQuotientMap.lift_comp (isQuotientMap_cofibreVQuot ι)
        (cofibreVContractCurried ι x₀) (cofibreVContractCurried_factors ι x₀))) a
  rw [cofibreVContract_apply, hstep, cofibreVContractCurried_apply]
  apply Subtype.ext
  show (cofibreVContractRaw ι x₀ (a, 0) : cofibre ι) = Quotient.mk'' a.1
  rw [cofibreVContractRaw_apply]
  rcases hc : a.1 with e | y
  · have h := a.2
    rw [Set.mem_preimage, mem_cofibreV_iff] at h
    rw [hc] at h
    simp only [cofibreHeight, cofibreHeightFun, Quotient.lift_mk, Sum.elim_inl] at h
    exact absurd h (not_lt.mpr le_rfl)
  · change cofibreInclCone ι (coneContractC (0, y)) = Quotient.mk'' (Sum.inr y)
    rw [coneContractC_zero]
    rfl

/-- **The punctured cone `cofibreV ι` is contractible.** -/
theorem exists_contraction_cofibreV {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    [Nonempty F] (ι : C(F, E)) :
    ∃ H : C(↥(cofibreV ι) × unitInterval, ↥(cofibreV ι)),
      (∀ v, H (v, 0) = v) ∧ ∃ b : ↥(cofibreV ι), ∀ v, H (v, 1) = b := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty F)
  exact ⟨cofibreVContract ι x₀, cofibreVContract_zero ι x₀, _, cofibreVContract_one ι x₀⟩

end

end Work.RatHurewicz
