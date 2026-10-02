import Mathlib
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The projectivisation of a complex gluing-data bundle (I): the space

Let `Z` be a complex vector bundle over a topological space `B` in the gluing-data model
(`Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι`) and let `E∖0 ⊆ E` be the complement of
the zero section of its realification (`Work.Thom.zeroComplement`).  This module builds the
**projectivisation** `P(E) = (E∖0)/ℂˣ` of `Z` as the quotient of the punctured total space by the
fibrewise action of the units of `ℂ`:

* `Work.LerayHirsch.smulPunct` — the `ℂˣ`-action `p ↦ ⟨p.proj, c • p.snd⟩` on the punctured total
  space (well defined because `c ≠ 0`), with `smulPunct_one`, `smulPunct_mul`;
* `Work.LerayHirsch.projSetoid` — the orbit relation, so that
  `Work.LerayHirsch.ProjSpace Z = Quotient (projSetoid Z)`;
* `Work.LerayHirsch.mkProj` — the quotient map, `continuous_mkProj`, `surjective_mkProj`,
  `mkProj_eq_iff`;
* `Work.LerayHirsch.projMap Z : C(ProjSpace Z, B)` — the projection, continuous for the quotient
  topology, with `projMap_mkProj` and `surjective_projMap`;
* `Work.LerayHirsch.chartCoord` — the chart coordinates on the punctured total space, and their
  transformation law `chartCoord (c • p) = c • chartCoord p`, which is what makes every
  construction below invariant under the `ℂˣ`-action;
* `Work.LerayHirsch.ProjFibre`, `Work.LerayHirsch.fibreOf`, `Work.LerayHirsch.fibreMap` — **the
  fibre of `P(E)` over `b` is the projectivisation of the model fibre**, i.e. `ℂP^{m-1}`
  (`Work.LerayHirsch.fibreMap_bijective`, `Submission/Work/LerayHirsch/fibreMap_bijective.lean`).

The **tautological line bundle** `ℓ ⊆ π^*E` over `P(E)`, with `ζ = c₁(ℓ)`, is
`Submission/Work/LerayHirsch/TautLine.lean`; the Leray–Hirsch statement is
`Submission/Work/LerayHirsch/LH.lean`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The action of the units of `ℂ` on `E∖0` -/

/-- The **`ℂˣ`-action on the complement of the zero section** of the realification of a complex
gluing-data bundle: `c • p = ⟨p.proj, c • p.snd⟩`.  It is defined on the punctured total space,
hence the scalar must be a *unit* (`c ≠ 0`). -/
def smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) : ↥(zeroComplement (realification Z)) :=
  ⟨⟨p.1.proj, (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩, by
    rw [mem_zeroComplement]
    exact smul_ne_zero (Units.ne_zero c) p.2⟩

@[simp] theorem smulPunct_coe (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    ((smulPunct Z c p : ↥(zeroComplement (realification Z))) : (realification Z).TotalSpace)
      = ⟨p.1.proj, (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ := rfl

@[simp] theorem smulPunct_proj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) : (smulPunct Z c p).1.proj = p.1.proj := rfl

theorem smulPunct_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    (show EuclideanSpace ℂ (Fin m) from (smulPunct Z c p).1.2)
      = (c : ℂ) • (show EuclideanSpace ℂ (Fin m) from p.1.2) := rfl

theorem smulPunct_one (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : smulPunct Z 1 p = p := by
  refine Subtype.ext (Bundle.TotalSpace.ext rfl ?_)
  rw [smulPunct_coe]
  exact heq_of_eq (one_smul ℂ (show EuclideanSpace ℂ (Fin m) from p.1.2))

theorem smulPunct_mul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c d : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    smulPunct Z (c * d) p = smulPunct Z c (smulPunct Z d p) := by
  refine Subtype.ext (Bundle.TotalSpace.ext rfl ?_)
  rw [smulPunct_coe, smulPunct_coe, smulPunct_coe]
  exact heq_of_eq (mul_smul (c : ℂ) (d : ℂ) (show EuclideanSpace ℂ (Fin m) from p.1.2))

/-! ## The projectivisation -/

/-- The relation on `E∖0` whose quotient is the projectivisation of `Z`: two points of the same
fibre which differ by a nonzero scalar. -/
def projRel (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p q : ↥(zeroComplement (realification Z))) : Prop :=
  ∃ c : ℂˣ, smulPunct Z c q = p

theorem projRel_refl (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : projRel Z p p :=
  ⟨1, smulPunct_one Z p⟩

theorem projRel_symm (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {p q : ↥(zeroComplement (realification Z))} (h : projRel Z p q) : projRel Z q p := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c⁻¹, ?_⟩
  have h2 : smulPunct Z (c⁻¹ * c) q = smulPunct Z c⁻¹ (smulPunct Z c q) :=
    smulPunct_mul Z c⁻¹ c q
  rw [inv_mul_cancel, smulPunct_one, hc] at h2
  exact h2.symm

theorem projRel_trans (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {p q r : ↥(zeroComplement (realification Z))} (h₁ : projRel Z p q)
    (h₂ : projRel Z q r) : projRel Z p r := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  refine ⟨c * d, ?_⟩
  rw [smulPunct_mul, hd, hc]

/-- The setoid of the projectivisation: the orbit relation of the `ℂˣ`-action on `E∖0`. -/
def projSetoid (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Setoid ↥(zeroComplement (realification Z)) where
  r := projRel Z
  iseqv := ⟨projRel_refl Z, fun h => projRel_symm Z h, fun h₁ h₂ => projRel_trans Z h₁ h₂⟩

/-- **The projectivisation** `P(E) = (E∖0)/ℂˣ` of a complex gluing-data bundle `Z`. -/
def ProjSpace (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : Type _ :=
  Quotient (projSetoid Z)

instance (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    TopologicalSpace (ProjSpace Z) := instTopologicalSpaceQuotient

/-- The quotient map `E∖0 → P(E)`. -/
def mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : ProjSpace Z :=
  Quotient.mk'' p

theorem continuous_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Continuous (mkProj Z) := continuous_quotient_mk'

theorem surjective_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Function.Surjective (mkProj Z) := Quotient.mk''_surjective

theorem mkProj_eq_iff (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {p q : ↥(zeroComplement (realification Z))} :
    mkProj Z p = mkProj Z q ↔ projRel Z p q := Quotient.eq''

theorem mkProj_eq_iff_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {p q : ↥(zeroComplement (realification Z))} :
    mkProj Z p = mkProj Z q ↔ ∃ c : ℂˣ, p = smulPunct Z c q := by
  rw [mkProj_eq_iff]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩; exact ⟨c, hc.symm⟩

/-- The **projection** `π : P(E) → B`, well defined because the `ℂˣ`-action preserves the base
point, and continuous for the quotient topology. -/
def projMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : C(ProjSpace Z, B) where
  toFun := Quotient.lift (fun p => p.1.proj) (by
    intro p q h
    obtain ⟨c, hc⟩ := h
    rw [← hc]
    rfl)
  continuous_toFun := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    show Continuous (fun p : ↥(zeroComplement (realification Z)) => p.1.proj)
    exact ((bundleProj (realification Z)).comp (subtypeMap (zeroComplement (realification Z)))).continuous

@[simp] theorem projMap_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : projMap Z (mkProj Z p) = p.1.proj := rfl

/-- A nonzero vector of the model fibre exists as soon as the rank is positive. -/
theorem exists_ne_zero_fin (hm : 1 ≤ m) :
    ∃ v : EuclideanSpace ℂ (Fin m), v ≠ 0 := by
  refine ⟨(EuclideanSpace.equiv (Fin m) ℂ).symm
    (Pi.single (⟨0, by omega⟩ : Fin m) 1), ?_⟩
  intro hv
  have h1 : (Pi.single (⟨0, by omega⟩ : Fin m) 1 : Fin m → ℂ) = 0 := by
    have h := congrArg (EuclideanSpace.equiv (Fin m) ℂ) hv
    simpa using h
  have h2 := congrFun h1 (⟨0, by omega⟩ : Fin m)
  exact one_ne_zero h2

/-- The projection is surjective as soon as the rank is positive. -/
theorem surjective_projMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (hm : 1 ≤ m) : Function.Surjective (projMap Z) := by
  intro b
  obtain ⟨v, hv⟩ := exists_ne_zero_fin (m := m) hm
  have hp : (⟨b, v⟩ : (realification Z).TotalSpace) ∈ zeroComplement (realification Z) := by
    rw [mem_zeroComplement]; exact hv
  exact ⟨mkProj Z ⟨(⟨b, v⟩ : (realification Z).TotalSpace), hp⟩, rfl⟩

theorem nonempty_projSpace [Nonempty B] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (hm : 1 ≤ m) : Nonempty (ProjSpace Z) := by
  obtain ⟨b⟩ := ‹Nonempty B›
  obtain ⟨v, hv⟩ := exists_ne_zero_fin (m := m) hm
  have hp : (⟨b, v⟩ : (realification Z).TotalSpace) ∈ zeroComplement (realification Z) := by
    rw [mem_zeroComplement]; exact hv
  exact ⟨mkProj Z ⟨(⟨b, v⟩ : (realification Z).TotalSpace), hp⟩⟩

/-! ## The chart coordinates on the punctured total space

The trivialisation `Z.localTriv i` of `Z`, restricted to the punctured total space of the
realification, gives at each point a vector of the *model* fibre `ℂ^m`.  These are the coordinates
in which the tautological line bundle and its tautological section are written. -/

/-- The **chart coordinates** of a point of the punctured total space: the second component of
`Z.localTriv i`.  (As with `Z.localTriv` itself, this is only meaningful over `Z.baseSet i`, where
the trivialisation is defined.) -/
def chartCoord (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (p : ↥(zeroComplement (realification Z))) : EuclideanSpace ℂ (Fin m) :=
  (Z.localTriv i (p : (realification Z).TotalSpace)).2

theorem chartCoord_def (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z i p
      = (Z.coordChange (Z.indexAt p.1.proj) i p.1.proj)
          (show EuclideanSpace ℂ (Fin m) from p.1.2) := by
  unfold chartCoord
  rw [VectorBundleCore.localTriv_apply]

/-- The chart coordinates are **equivariant** for the `ℂˣ`-action: this is the reason every
construction on `P(E)` below is well defined. -/
theorem chartCoord_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : ι)
    (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z i (smulPunct Z c p) = (c : ℂ) • chartCoord Z i p := by
  rw [chartCoord_def, chartCoord_def]
  rw [smulPunct_proj, smulPunct_snd]
  exact map_smul _ _ _

/-- The chart coordinates of a point over `Z.baseSet i` are nonzero: the realification of a
complex bundle has no zero vectors over the base set of a trivialisation. -/
theorem chartCoord_ne_zero_of_mem_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i : ι) (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj ∈ Z.baseSet i) :
    chartCoord Z i p ≠ 0 := by
  intro h
  have h' : (Z.coordChange (Z.indexAt p.1.proj) i p.1.proj)
      (show EuclideanSpace ℂ (Fin m) from p.1.2) = 0 := by
    rw [← chartCoord_def]; exact h
  have h2 : (Z.coordChange i (Z.indexAt p.1.proj) p.1.proj)
      ((Z.coordChange (Z.indexAt p.1.proj) i p.1.proj)
        (show EuclideanSpace ℂ (Fin m) from p.1.2)) = 0 := by
    rw [h', map_zero]
  rw [Z.coordChange_comp (Z.indexAt p.1.proj) i (Z.indexAt p.1.proj) p.1.proj
    ⟨⟨Z.mem_baseSet_at p.1.proj, hp⟩, Z.mem_baseSet_at p.1.proj⟩] at h2
  have hself : (Z.coordChange (Z.indexAt p.1.proj) (Z.indexAt p.1.proj) p.1.proj)
      (show EuclideanSpace ℂ (Fin m) from p.1.2) = (show EuclideanSpace ℂ (Fin m) from p.1.2) :=
    Z.coordChange_self (Z.indexAt p.1.proj) p.1.proj (Z.mem_baseSet_at p.1.proj) _
  rw [hself] at h2
  exact p.2 h2

/-! ## The fibre of the projectivisation

The fibre of `π : P(E) → B` over `b` is *canonically* the projectivisation of the model fibre: the
punctured fibre over `b` is `{v : ℂ^m // v ≠ 0}` (every point of the total space is a pair), and the
relation is exactly the relation of `ℙ ℂ (EuclideanSpace ℂ (Fin m))`.  In particular the fibre of
`P(E)` is `ℂP^{m-1}`, the object of `Submission/Work/Projective/`. -/

/-- The projectivisation `ℙ ℂ (ℂ^m)` of the *model* fibre carries the quotient topology (the
instance is not registered by Mathlib for `Projectivization`; it is needed to speak of the fibre of
`P(E)` as a topological space). -/
instance instTopologicalSpaceProjectiveEuclidean (m : ℕ) :
    TopologicalSpace (ℙ ℂ (EuclideanSpace ℂ (Fin m))) :=
  instTopologicalSpaceQuotient

/-- The fibre of `P(E)` over `b`, as a subtype. -/
abbrev ProjFibre (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) : Type _ :=
  {x : ProjSpace Z // projMap Z x = b}

/-- A nonzero vector of the model fibre over `b` gives a point of the fibre of `P(E)`. -/
def fibreOf (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) : ProjFibre Z b :=
  have hp : (⟨b, v.1⟩ : (realification Z).TotalSpace) ∈ zeroComplement (realification Z) := by
    rw [mem_zeroComplement]; exact v.2
  ⟨mkProj Z ⟨(⟨b, v.1⟩ : (realification Z).TotalSpace), hp⟩, rfl⟩

theorem fibreOf_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (c : ℂˣ) (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) :
    fibreOf Z b ⟨(c : ℂ) • v.1, smul_ne_zero (Units.ne_zero c) v.2⟩ = fibreOf Z b v := by
  refine Subtype.ext ?_
  rw [fibreOf, fibreOf, mkProj_eq_iff]
  refine ⟨c, ?_⟩
  refine Subtype.ext (Bundle.TotalSpace.ext rfl ?_)
  exact heq_of_eq (by rw [smulPunct_coe])

/-- **Two proportional nonzero vectors give the same point of the fibre** (the general-scalar
form needed by `Projectivization.lift`). -/
theorem fibreOf_eq_of_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (t : ℂ) (v w : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0})
    (h : (v : EuclideanSpace ℂ (Fin m)) = t • (w : EuclideanSpace ℂ (Fin m))) :
    fibreOf Z b v = fibreOf Z b w := by
  have ht : t ≠ 0 := by
    intro ht0
    exact v.2 (by rw [h, ht0, zero_smul])
  have hv : v = ⟨t • (w : EuclideanSpace ℂ (Fin m)), smul_ne_zero ht w.2⟩ := Subtype.ext h
  rw [hv]
  exact fibreOf_smul Z b (Units.mk0 t ht) w

/-- **The map from the projectivisation of the model fibre to the fibre of `π : P(E) → B`**.  It is
a bijection (`Work.LerayHirsch.fibreMap_bijective`), i.e. the fibre of the projectivisation is
`ℂP^{m-1}`. -/
def fibreMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    ℙ ℂ (EuclideanSpace ℂ (Fin m)) → ProjFibre Z b :=
  Projectivization.lift (fun v => fibreOf Z b v) (fun a b' t hat => fibreOf_eq_of_smul Z b t a b' hat)

@[simp] theorem fibreMap_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (v : EuclideanSpace ℂ (Fin m)) (hv : v ≠ 0) :
    fibreMap Z b (Projectivization.mk ℂ v hv) = fibreOf Z b ⟨v, hv⟩ := rfl

end

end Work.LerayHirsch
