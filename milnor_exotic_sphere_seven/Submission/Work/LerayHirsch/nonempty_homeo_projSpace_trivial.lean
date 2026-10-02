import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.fibreMap_bijective
import Submission.Work.Thom.realification_homeo
import Submission.Work.LerayHirsch.exists_punctTrivHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# `P(B × ℂ^m) ≅ B × ℂP^{m-1}`: the projectivisation of the trivial complex bundle

`Work.LerayHirsch.ProjSpace Z` is the projectivisation `(E∖0)/ℂˣ` of a complex gluing-data bundle
`Z` (`Submission/Work/LerayHirsch/Punctum.lean`).  For the **trivial** bundle
`Z = trivialVectorBundleCore ℂ B (ℂ^m) PUnit` the punctured total space is `B × (ℂ^m ∖ 0)` and the
quotient is `B × ℙ ℂ (ℂ^m)`: this module proves that this identification is a homeomorphism.

The statement is the trivial case of Leray–Hirsch — the input `KunnethCP` of
`Submission/Work/LerayHirsch/LH.lean` — so that Künneth for `B × ℂP^{m-1}` can be read off from the
Leray–Hirsch statement for the trivial bundle.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {m : ℕ}

/-! ## The projectivisation map of the model fibre -/

/-- `mkP m` is `Projectivization.mk` on the nonzero vectors of the model fibre `ℂ^m`. -/
def mkP (m : ℕ) : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} → ℙ ℂ (EuclideanSpace ℂ (Fin m)) :=
  fun v => Projectivization.mk ℂ v.1 v.2

theorem mkP_apply (m : ℕ) (v : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) :
    mkP m v = Projectivization.mk ℂ v.1 v.2 := rfl

/-- `mkP m` only depends on the underlying vector. -/
theorem mkP_congr {v w : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}}
    (h : v.1 = w.1) : mkP m v = mkP m w :=
  congrArg (mkP m) (Subtype.ext h)

/-- Two nonzero vectors have the same class iff they differ by a nonzero scalar. -/
theorem mkP_eq_iff {v w : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}} :
    mkP m v = mkP m w ↔ ∃ c : ℂ, c • w.1 = v.1 := by
  rw [mkP_apply, mkP_apply, Projectivization.mk_eq_mk_iff']

theorem continuous_mkP (m : ℕ) : Continuous (mkP m) := continuous_quotient_mk'

theorem surjective_mkP (m : ℕ) : Function.Surjective (mkP m) := Quotient.mk''_surjective

/-- **The projectivisation map of the model fibre is open.**  It is the quotient map for the
continuous `ℂˣ`-action on the nonzero vectors, and the action is by homeomorphisms (scaling by a
unit), so the saturation of an open set is open. -/
theorem isOpenMap_mkP (m : ℕ) : IsOpenMap (mkP m) := by
  intro U hU
  rw [isOpen_coinduced]
  rw [show (@Quotient.mk' {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}
        (projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin m)))) = mkP m from rfl]
  have hpre : (mkP m) ⁻¹' ((mkP m) '' U)
      = ⋃ c : ℂˣ, (fun w : {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
          (⟨(c : ℂ) • w.1, smul_ne_zero (Units.ne_zero c) w.2⟩ :
            {v : EuclideanSpace ℂ (Fin m) // v ≠ 0})) ⁻¹' U := by
    ext w
    simp only [mkP, Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ v.1 w.1 v.2 w.2).mp hvw
      refine ⟨c, ?_⟩
      have hveq : (⟨(c : ℂ) • w.1, smul_ne_zero (Units.ne_zero c) w.2⟩ :
          {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) = v := Subtype.ext hc
      rw [hveq]; exact hv
    · rintro ⟨c, hc⟩
      exact ⟨⟨(c : ℂ) • w.1, smul_ne_zero (Units.ne_zero c) w.2⟩, hc,
        (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr ⟨c, rfl⟩⟩
  rw [hpre]
  refine isOpen_iUnion fun c => ?_
  exact (Continuous.subtype_mk ((continuous_const_smul (c : ℂ)).comp continuous_subtype_val)
    (fun w => smul_ne_zero (Units.ne_zero c) w.2)).isOpen_preimage U hU

/-! ## The class map on the punctured total space -/

/-- The product of a surjective map with the identity is surjective. -/
theorem surjective_prodMap_id {X Y Z : Type*} {f : Y → Z} (hf : Function.Surjective f) :
    Function.Surjective (Prod.map (id : X → X) f) := by
  rintro ⟨x, z⟩
  obtain ⟨y, rfl⟩ := hf z
  exact ⟨(x, y), rfl⟩

/-- The **class of the fibre coordinate**: a punctured vector of the trivial bundle `B × ℂ^m` maps
to its base point together with the class of its fibre coordinate in `ℙ ℂ (ℂ^m)`. -/
def projProd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) :
    ↥(zeroComplement (realification Z)) → B × ℙ ℂ (EuclideanSpace ℂ (Fin m)) :=
  fun p => (p.1.proj, mkP m ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
    (mem_zeroComplement p.1).mp p.2⟩)

/-! ## The main theorem -/

/-- **`P(B × ℂ^m) ≅ B × ℂP^{m-1}`**, the trivial case of Leray–Hirsch. -/
theorem nonempty_homeo_projSpace_trivial_aux (m : ℕ) (B : Type) [TopologicalSpace B] :
    Nonempty (ProjSpace
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) ≃ₜ
      (B × Projectivization ℂ (EuclideanSpace ℂ (Fin m)))) := by
  let Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit :=
    trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit
  have hφexists : ∃ e : ↥(zeroComplement (realification Z)) ≃ₜ
      (B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}),
      ∀ p, (e : ↥(zeroComplement (realification Z)) →
            B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) p
          = (p.1.proj, ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
              (mem_zeroComplement p.1).mp p.2⟩) :=
    exists_punctTrivHomeo m B
  obtain ⟨φ, hφ⟩ := hφexists
  have hcomp : projProd Z = (Prod.map (id : B → B) (mkP m)) ∘
      (φ : ↥(zeroComplement (realification Z)) →
        B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0}) := by
    funext p
    rw [Function.comp_apply, hφ p]
    rfl
  have hcont : Continuous (projProd Z) := by
    refine Continuous.prodMk ?_ ?_
    · exact ((bundleProj (realification Z)).comp
        (subtypeMap (zeroComplement (realification Z)))).continuous
    · have h2 : (fun p : ↥(zeroComplement (realification Z)) =>
          mkP m ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
            (mem_zeroComplement p.1).mp p.2⟩)
          = (fun q : B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
              mkP m ⟨q.2.1, q.2.2⟩) ∘
            (φ : ↥(zeroComplement (realification Z)) → _) := by
        funext p
        rw [Function.comp_apply, hφ p]
      rw [h2]
      exact (continuous_mkP m).comp ((Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_snd) (fun q => q.2.2)).comp φ.continuous)
  have hopen : IsOpenMap (projProd Z) := by
    rw [hcomp]
    exact ((IsOpenMap.id : IsOpenMap (id : B → B)).prodMap (isOpenMap_mkP m)).comp φ.isOpenMap
  have hsurj : Function.Surjective (projProd Z) := by
    rw [hcomp]
    exact (surjective_prodMap_id (surjective_mkP m)).comp φ.surjective
  have hQ : Topology.IsQuotientMap (projProd Z) :=
    hopen.isQuotientMap hcont hsurj
  let F' : ProjSpace Z → B × ℙ ℂ (EuclideanSpace ℂ (Fin m)) :=
    fun x => (projMap Z x, projClass Z x)
  have hF'mk : ∀ p, F' (mkProj Z p) = projProd Z p := by
    intro p
    simp only [F', projProd, mkP, projMap_mkProj, projClass_mkProj]
  have hQ' : Topology.IsQuotientMap F' := by
    refine Topology.IsQuotientMap.of_comp_isQuotientMap (isQuotientMap_quotient_mk') ?_
    change Topology.IsQuotientMap (projProd Z)
    exact hQ
  have hinj : Function.Injective F' := by
    intro x y hxy
    have h1 : projMap Z x = projMap Z y := congrArg Prod.fst hxy
    have h2 : projClass Z x = projClass Z y := congrArg Prod.snd hxy
    have hx : (fibreMap Z (projMap Z x) (projClass Z x)).1 = x :=
      congrArg Subtype.val (fibreMap_projClass Z (projMap Z x) x rfl)
    have hy : (fibreMap Z (projMap Z y) (projClass Z y)).1 = y :=
      congrArg Subtype.val (fibreMap_projClass Z (projMap Z y) y rfl)
    rw [← hx, h1, h2, hy]
  exact ⟨(Equiv.ofBijective F' ⟨hinj, hQ'.surjective⟩).toHomeomorph
    (fun s => hQ'.isCoinducing.isOpen_preimage)⟩

theorem nonempty_homeo_projSpace_trivial (m : ℕ) (B : Type) [TopologicalSpace B] :
    Nonempty (Work.LerayHirsch.ProjSpace
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) ≃ₜ
      (B × Projectivization ℂ (EuclideanSpace ℂ (Fin m)))) :=
  nonempty_homeo_projSpace_trivial_aux m B

end

end Work.LerayHirsch
