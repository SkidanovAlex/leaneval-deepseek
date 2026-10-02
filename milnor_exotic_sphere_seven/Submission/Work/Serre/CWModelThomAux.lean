import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.c2oddRangeTwo
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.zerothHomotopy_fibre_equiv_of_path
import Submission.Work.RatHurewicz.CompressRelToRelPi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary lemmas for the CW-model Thom case

This module collects the small structural lemmas used by the tower induction of
`Submission/Work/Serre/cwModelThomCase.lean`:

* `CWThom.FibreData` — the hypothesis on the fibres of a fibration (the vanishing of the rational
  homology off degree `r` in the range and `H_r ≅ ℚ`), bundled as a predicate of the *fibration*
  (so that it can be transported along base changes and used pointwise);
* the transport of `FibreData` along a homeomorphism of the base (`fibreData_comp_homeo`) and along
  the restriction to the preimage of a subspace (`fibreData_restrictFibre`), together with the two
  fibre homeomorphisms which implement them;
* `fibreData_of_point` — fibre data propagates from one point of a path connected base to all
  points (the same content as `Work.Serre.fibreConditions_of_path`, in the bundled form);
* `isSerreFibration_comp_homeo` — a Serre fibration stays one after composing the base with a
  homeomorphism.

The statements are in the namespace `Work.Serre.CWThom` because `Work.Serre.FibreData` and friends
are the kind of name that other files in this (shared) directory may want; the prefix makes the
intent explicit and avoids clashes.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace CWThom

/-- **The fibre data of a fibration**: the vanishing of the rational homology of every fibre off
degree `r` in the range `≤ N`, and `H_r(fibre;ℚ) ≅ ℚ`. -/
def FibreData (r N : ℕ) {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) : Prop :=
  ∀ γ : Γ, (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      IsZero (ratH (TopCat.of {x : X // q x = γ}) t)) ∧
    Nonempty (ratH (TopCat.of {x : X // q x = γ}) r ≅ ModuleCat.of ℚ ℚ)

/-- **A Serre fibration remains one after postcomposition with a homeomorphism.** -/
theorem isSerreFibration_comp_homeo {Γ Γ' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ']
    (e : Γ ≃ₜ Γ') {X : Type} [TopologicalSpace X] {q : C(X, Γ)}
    (hq : Work.StemsB.IsSerreFibration q) :
    Work.StemsB.IsSerreFibration ((⟨e, e.continuous_toFun⟩ : C(Γ, Γ')).comp q) := by
  intro n f b H
  obtain ⟨g, H', heq⟩ :=
    hq n f ((⟨e.symm, e.symm.continuous_toFun⟩ : C(Γ', Γ)).comp b)
      { toContinuousMap := (⟨e.symm, e.symm.continuous_toFun⟩ : C(Γ', Γ)).comp H.toContinuousMap
        map_zero_left := fun z => by
          show e.symm (H.toContinuousMap (0, z)) = q (f z)
          have h : H.toContinuousMap (0, z) =
            (((⟨e, e.continuous_toFun⟩ : C(Γ, Γ')).comp q).comp f) z := H.map_zero_left z
          rw [h]
          exact e.symm_apply_apply (q (f z))
        map_one_left := fun z => by
          show e.symm (H.toContinuousMap (1, z)) =
            ((⟨e.symm, e.symm.continuous_toFun⟩ : C(Γ', Γ)).comp b) z
          have h : H.toContinuousMap (1, z) = b z := H.map_one_left z
          rw [h]
          rfl }
  refine ⟨g, H', ?_⟩
  ext zt
  show e (q (H'.toContinuousMap zt)) = H.toContinuousMap zt
  have h : q (H'.toContinuousMap zt) =
    (((⟨e.symm, e.symm.continuous_toFun⟩ : C(Γ', Γ)).comp H.toContinuousMap)) zt :=
    ContinuousMap.congr_fun heq zt
  rw [h]
  exact e.apply_symm_apply (H.toContinuousMap zt)

/-- **The fibre homeomorphism of the restriction to a preimage.** -/
def fibreHomeo_restrictFibre {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) (S : Set Γ) (γ : ↥S) :
    {x : ↥(q ⁻¹' S) // restrictFibre q S x = γ} ≃ₜ {y : X // q y = (γ : Γ)} :=
  { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
    invFun := fun y => ⟨⟨y.1, by
      change q y.1 ∈ S
      rw [show q y.1 = (γ : Γ) from y.2]
      exact γ.2⟩, by
      show restrictFibre q S ⟨y.1, _⟩ = γ
      exact Subtype.ext y.2⟩
    left_inv := fun x => Subtype.ext (Subtype.ext rfl)
    right_inv := fun y => Subtype.ext rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val }

/-- **The fibre homeomorphism of a base change along a homeomorphism (fixed total space).** -/
def fibreHomeo_comp_homeo {Γ Γ' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ']
    (e : Γ ≃ₜ Γ') {X : Type} [TopologicalSpace X] (q : C(X, Γ)) (γ' : Γ') :
    {x : X // e (q x) = γ'} ≃ₜ {x : X // q x = e.symm γ'} :=
  { toFun := fun x => ⟨x.1,
      (e.symm_apply_apply (q x.1)).symm.trans (congrArg e.symm x.2)⟩
    invFun := fun x => ⟨x.1,
      (congrArg e x.2).trans (e.apply_symm_apply γ')⟩
    left_inv := fun x => Subtype.ext rfl
    right_inv := fun x => Subtype.ext rfl
    continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
    continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }

/-- **Path connectedness transports along a homeomorphism.** -/
theorem pathConnectedSpace_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : PathConnectedSpace X) : PathConnectedSpace Y :=
  { nonempty := h.nonempty.map e
    joined := fun y₁ y₂ => by
      obtain ⟨p⟩ := h.joined (e.symm y₁) (e.symm y₂)
      exact ⟨{ toContinuousMap :=
                ⟨fun t => e (p t), e.continuous_toFun.comp p.continuous_toFun⟩
               source' := by
                 show e (p 0) = y₁
                 rw [p.source]
                 exact e.apply_symm_apply y₁
               target' := by
                 show e (p 1) = y₂
                 rw [p.target]
                 exact e.apply_symm_apply y₂ }⟩ }

/-- **Fibre data transports along a homeomorphism of the base of a fibration with fixed total
space.** -/
theorem fibreData_comp_homeo {r N : ℕ} {Γ Γ' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ']
    (e : Γ ≃ₜ Γ') {X : Type} [TopologicalSpace X] {q : C(X, Γ)} (hd : FibreData r N q) :
    FibreData r N ((⟨e, e.continuous_toFun⟩ : C(Γ, Γ')).comp q) := by
  intro γ'
  have hfib : {x : X // (⟨e, e.continuous_toFun⟩ : C(Γ, Γ')).comp q x = γ'} ≃ₜ
      {x : X // q x = e.symm γ'} := fibreHomeo_comp_homeo e q γ'
  constructor
  · intro t ht htr htN
    obtain ⟨eHt⟩ := Work.StemsB.c2odd_ratH_iso_of_homeo hfib t
    exact IsZero.of_iso ((hd (e.symm γ')).1 t ht htr htN) eHt
  · obtain ⟨eHr⟩ := Work.StemsB.c2odd_ratH_iso_of_homeo hfib r
    exact ⟨eHr.trans (hd (e.symm γ')).2.some⟩

/-- **Fibre data is unaffected by restricting a fibration to the preimage of a subset.** -/
theorem fibreData_restrictFibre {r N : ℕ} {Γ : Type} [TopologicalSpace Γ] {X : Type}
    [TopologicalSpace X] {q : C(X, Γ)} (hd : FibreData r N q) (S : Set Γ) :
    FibreData r N (restrictFibre q S) := by
  intro γ
  have hfib : {x : ↥(q ⁻¹' S) // restrictFibre q S x = γ} ≃ₜ {y : X // q y = (γ : Γ)} :=
    fibreHomeo_restrictFibre q S γ
  constructor
  · intro t ht htr htN
    obtain ⟨eHt⟩ := Work.StemsB.c2odd_ratH_iso_of_homeo hfib t
    exact IsZero.of_iso ((hd (γ : Γ)).1 t ht htr htN) eHt
  · obtain ⟨eHr⟩ := Work.StemsB.c2odd_ratH_iso_of_homeo hfib r
    exact ⟨eHr.trans (hd (γ : Γ)).2.some⟩

/-- **Fibre data propagates from one point along paths.** -/
theorem fibreData_of_point {r N : ℕ} {Γ : Type} [TopologicalSpace Γ] [PathConnectedSpace Γ]
    {X : Type} [TopologicalSpace X] {q : C(X, Γ)} (hq : Work.StemsB.IsSerreFibration q)
    (γ₀ : Γ)
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → IsZero (ratH (TopCat.of {x : X // q x = γ₀}) t))
    (hgen : Nonempty (ratH (TopCat.of {x : X // q x = γ₀}) r ≅ ModuleCat.of ℚ ℚ)) :
    FibreData r N q := by
  intro γ
  obtain ⟨p⟩ := PathConnectedSpace.joined γ₀ γ
  have h0 : p.toContinuousMap 0 = γ₀ := p.source
  have h1 : p.toContinuousMap 1 = γ := p.target
  constructor
  · intro t ht htr htN
    obtain ⟨e⟩ := Work.Serre.ratH_fibre_iso_of_path q hq p.toContinuousMap t
    rw [h0, h1] at e
    exact IsZero.of_iso (hvan t ht htr htN) e.symm
  · obtain ⟨e⟩ := Work.Serre.ratH_fibre_iso_of_path q hq p.toContinuousMap r
    rw [h0, h1] at e
    exact ⟨e.symm.trans hgen.some⟩


/-- The fibre of `p` over `b`, presented as the preimage of the singleton `{b}`. -/
def fibrePreimageHomeo {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (b : B) : ↥(p ⁻¹' {b}) ≃ₜ Work.StemsB.fibre p b where
  toFun x := ⟨x.1, Set.mem_singleton_iff.mp x.2⟩
  invFun x := ⟨x.1, Set.mem_singleton_iff.mpr x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- **Path connectedness of the fibres of a Serre fibration propagates from one fibre to all of
them.**  The fibre over `γ` is joined to the fibre over `γ₀` by the transport of `π₀` along a path
(`Work.Serre.fibre_zerothHomotopy_equiv_of_path`), and nonemptiness follows from path lifting. -/
theorem pathConnectedSpace_fibre_of_point {Γ : Type} [TopologicalSpace Γ] [PathConnectedSpace Γ]
    {X : Type} [TopologicalSpace X] (q : C(X, Γ)) (hq : Work.StemsB.IsSerreFibration q) (γ₀ : Γ)
    (h : PathConnectedSpace (Work.StemsB.fibre q γ₀)) (γ : Γ) :
    PathConnectedSpace (Work.StemsB.fibre q γ) := by
  classical
  obtain ⟨p⟩ := PathConnectedSpace.joined γ₀ γ
  -- the equivariance of `pi_0` along the path
  obtain ⟨e⟩ := Work.Serre.fibre_zerothHomotopy_equiv_of_path q hq p
  haveI hZ₀ : Subsingleton (ZerothHomotopy ↥(q ⁻¹' {γ₀})) :=
    ((pathConnectedSpace_iff_zerothHomotopy).mp
      (pathConnectedSpace_of_homeo (fibrePreimageHomeo q γ₀).symm h)).2
  haveI hZ : Subsingleton (ZerothHomotopy ↥(q ⁻¹' {γ})) :=
    ⟨fun a b => by
      have h1 : e.symm a = e.symm b := Subsingleton.elim _ _
      calc a = e (e.symm a) := (e.apply_symm_apply a).symm
        _ = e (e.symm b) := by rw [h1]
        _ = b := e.apply_symm_apply b⟩
  -- nonemptiness: lift the path from a point of the fibre over `γ₀`
  obtain ⟨x₀⟩ := h.nonempty
  have hx₀ : q x₀.1 = γ₀ := x₀.2
  have hq0 : q x₀.1 = p 0 := by rw [p.source]; exact hx₀
  obtain ⟨w, hw0, hw⟩ := Work.Serre.exists_liftPath_proj q hq p.toContinuousMap hq0
  have hw1 : q (w 1) = γ := by
    have := congrFun (congrArg DFunLike.coe hw) 1
    simpa [p.target] using this
  haveI : Nonempty ↥(q ⁻¹' {γ}) := ⟨⟨w 1, by simpa using hw1⟩⟩
  haveI hpc' : PathConnectedSpace ↥(q ⁻¹' {γ}) :=
    (pathConnectedSpace_iff_zerothHomotopy).mpr ⟨inferInstance, hZ⟩
  exact pathConnectedSpace_of_homeo (fibrePreimageHomeo q γ) hpc'

end CWThom

end

end Work.Serre
