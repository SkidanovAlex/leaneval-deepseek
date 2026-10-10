import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Guidance from the project lead (the requester):

# cInv_eq_zero_of_pseudoReg  (Part A, feasible, ~400-800 lines on top of cInv_mul)
Paper Lemma 4.3. f = α·γ·α⁻¹ with γ a PartialIso of X' whose source and target contain every coheight-1 point, so exDiv γ = exDiv γ⁻¹ = ∅ and c(γ) = 0.
The general groupoid form of cInv_mul (X → X' → X' → X, which the cInv_mul proof gives for free, stated for varieties) yields c(f) = c(α) + c(γ) + c(α⁻¹). With c(α⁻¹) = −c(α) (apply additivity to α∘α⁻¹ = id; c(id) = 0) we get c(f) = 0.
**Implementation note:** prove cInv_mul in the groupoid generality (X,Y,Z arbitrary 𝕜-varieties, over-𝕜 birational maps) and derive the Cr statement. X' here is an arbitrary variety, possibly non-normal, non-projective, not rational-looking. The combinatorial proof above does not care.
Also needed: γ.toBirationalMap is represented by γ itself (IsIsoAt at source points, by definition), and PartialIso.IsPseudoIso gives "coheight 1 ⇒ in source".
-/

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-! ### Auxiliary facts about `IsOver` for composites of birational maps

`BirationalMap.trans` and `BirationalMap.symm` are plain definitions, so instance search does not
unfold them; the two results below provide the missing instances by hand. -/

/-- A composite of two birational maps over `S` is over `S`. -/
lemma pseudoReg_isOver_trans {S : Scheme.{0}} {X Y Z : Scheme.{0}} [X.Over S] [Y.Over S]
    [Z.Over S] [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]
    (f : X.BirationalMap Y) (g : Y.BirationalMap Z) [f.IsOver S] [g.IsOver S] :
    (f.trans g).IsOver S := by
  change (f.hom.comp g.hom).IsOver S
  infer_instance

/-- A partial isomorphism over `S` gives a birational map over `S`. -/
lemma pseudoReg_isOver_toBirationalMap {S X Y : Scheme.{0}} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] (γ : X.PartialIso Y)
    (hγ : γ.IsOver (X ↘ S) (Y ↘ S)) : γ.toBirationalMap.IsOver S := by
  change γ.toRationalMap.IsOver S
  have h : γ.toPartialMap.IsOver S := by
    simp only [PartialMap.IsOver, Hom.isOver_iff]
    simp only [PartialIso.toPartialMap_hom, PartialIso.toPartialMap_domain, Category.assoc]
    exact hγ
  exact ⟨γ.toPartialMap, h, rfl⟩

/-! ### Pseudo-isomorphisms have vanishing invariant

A pseudo-isomorphism is an isomorphism in codimension one, so it is an isomorphism at every point of
coheight one; in particular its exceptional set is empty and its invariant vanishes. -/

/-- A point of coheight one lies in the source of a pseudo-isomorphism. -/
lemma pseudoReg_mem_source_of_coheight_one {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (γ : X.PartialIso Y) (hγ : γ.IsPseudoIso) {x : X}
    (hx : coheight x = 1) : x ∈ γ.source := by
  by_contra h
  exact absurd (hx ▸ hγ.codim_source x h) (by decide)

/-- A point of coheight one lies in the target of a pseudo-isomorphism. -/
lemma pseudoReg_mem_target_of_coheight_one {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (γ : X.PartialIso Y) (hγ : γ.IsPseudoIso) {y : Y}
    (hy : coheight y = 1) : y ∈ γ.target := by
  by_contra h
  exact absurd (hy ▸ hγ.codim_target y h) (by decide)

/-- A pseudo-isomorphism is an isomorphism at every point of coheight one; it is represented by
itself. -/
lemma pseudoReg_isIsoAt_toBirationalMap {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (γ : X.PartialIso Y) (hγ : γ.IsPseudoIso) {x : X}
    (hx : coheight x = 1) : IsIsoAt γ.toBirationalMap x :=
  ⟨γ, pseudoReg_mem_source_of_coheight_one γ hγ hx, rfl⟩

/-- Likewise for the inverse of a pseudo-isomorphism. -/
lemma pseudoReg_isIsoAt_symm_toBirationalMap {X : Scheme.{0}} [IrreducibleSpace X]
    (γ : X.PartialIso X) (hγ : γ.IsPseudoIso) {x : X} (hx : coheight x = 1) :
    IsIsoAt (γ.toBirationalMap).symm x := by
  refine ⟨γ.symm, ?_, ?_⟩
  · simpa [PartialIso.symm_source] using pseudoReg_mem_target_of_coheight_one γ hγ hx
  · rfl

/-- A pseudo-isomorphism has no exceptional divisors. -/
lemma pseudoReg_exDiv_toBirationalMap_eq_empty {X : Scheme.{0}} [IrreducibleSpace X]
    (γ : X.PartialIso X) (hγ : γ.IsPseudoIso) : exDiv γ.toBirationalMap = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hnx⟩
  exact hnx (pseudoReg_isIsoAt_toBirationalMap γ hγ hx)

/-- The inverse of a pseudo-isomorphism has no exceptional divisors. -/
lemma pseudoReg_exDiv_symm_toBirationalMap_eq_empty {X : Scheme.{0}} [IrreducibleSpace X]
    (γ : X.PartialIso X) (hγ : γ.IsPseudoIso) : exDiv (γ.toBirationalMap).symm = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hnx⟩
  exact hnx (pseudoReg_isIsoAt_symm_toBirationalMap γ hγ hx)

/-- The invariant of a pseudo-isomorphism vanishes (paper: `c(γ) = 0`). -/
lemma pseudoReg_cInv_toBirationalMap (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [IrreducibleSpace X]
    [X.Over (Spec (.of 𝕜))] {W : Scheme.{0}} [W.Over (Spec (.of 𝕜))] (w : W)
    (γ : X.PartialIso X) (hγ : γ.IsPseudoIso) : cInv 𝕜 w γ.toBirationalMap = 0 := by
  simp [cInv, excCount, pseudoReg_exDiv_toBirationalMap_eq_empty γ hγ,
    pseudoReg_exDiv_symm_toBirationalMap_eq_empty γ hγ]

/-! ### The identity and inverse pairs -/

/-- The inverse of any birational map is a two-sided inverse for `trans`. -/
lemma pseudoReg_trans_symm_eq_one {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) : φ.trans φ.symm = 1 := by
  ext
  rw [BirationalMap.trans_hom, BirationalMap.symm_hom, φ.hom_comp_inv_id]
  rfl

/-- The identity birational map has vanishing invariant. -/
lemma pseudoReg_cInv_one (𝕜 : Type) [Field 𝕜] {X : Scheme.{0}} [IrreducibleSpace X]
    [X.Over (Spec (.of 𝕜))] {W : Scheme.{0}} [W.Over (Spec (.of 𝕜))] (w : W) :
    cInv 𝕜 w (1 : X.BirationalMap X) = 0 := by
  have hs : BirationalMap.symm (1 : X.BirationalMap X) = 1 := by
    change (1 : X.BirationalMap X)⁻¹ = 1
    exact inv_one
  rw [cInv, hs, sub_self]

/-! ### Additivity of the invariant in the groupoid of birational maps of varieties

The groupoid form of the paper's Lemma 2.2, `Work.Motivic.cInv_add`, is proved in
`Submission/Work/Motivic/cInv_add.lean` and imported above. -/

/-! ### The main result -/

/-- Pseudo-regularizable Cremona transformations have vanishing invariant. -/
theorem cInv_eq_zero_of_pseudoReg (𝕜 : Type) [Field 𝕜] (n : ℕ) {Z : Scheme.{0}}
    [Z.Over (Spec (.of 𝕜))] (z : Z) (f : Cr 𝕜 n) (hf : f.1.IsPseudoRegularizable 𝕜) :
    cInv 𝕜 z (f : BirationalMap 𝔸(Fin n; Spec (.of 𝕜)) 𝔸(Fin n; Spec (.of 𝕜))) = 0 := by
  obtain ⟨P⟩ := hf
  letI : Variety 𝕜 P.X' := P.variety
  have hα : P.α.IsOver (Spec (.of 𝕜)) := P.isOver_α
  haveI : P.α.IsOver (Spec (.of 𝕜)) := hα
  have hγ0 : P.γ.toBirationalMap.IsOver (Spec (.of 𝕜)) :=
    pseudoReg_isOver_toBirationalMap P.γ P.isOver_γ
  haveI : P.γ.toBirationalMap.IsOver (Spec (.of 𝕜)) := hγ0
  have hαγ : (P.α.trans P.γ.toBirationalMap).IsOver (Spec (.of 𝕜)) :=
    pseudoReg_isOver_trans P.α P.γ.toBirationalMap
  haveI : (P.α.trans P.γ.toBirationalMap).IsOver (Spec (.of 𝕜)) := hαγ
  have hαs : P.α.symm.IsOver (Spec (.of 𝕜)) := by
    change P.α.inv.IsOver (Spec (.of 𝕜))
    infer_instance
  haveI : P.α.symm.IsOver (Spec (.of 𝕜)) := hαs
  -- `c(α) + c(α⁻¹) = 0`, from additivity applied to `α ∘ α⁻¹ = id`.
  have hαα : cInv 𝕜 z P.α + cInv 𝕜 z P.α.symm = 0 := by
    have h := cInv_add (𝕜 := 𝕜) (w := z) (φ := P.α) (ψ := P.α.symm)
    rw [← h, pseudoReg_trans_symm_eq_one]
    exact pseudoReg_cInv_one 𝕜 z
  -- `c(f) = c(α) + c(γ) + c(α⁻¹)`.
  have h1 : cInv 𝕜 z (P.α.trans P.γ.toBirationalMap) =
      cInv 𝕜 z P.α + cInv 𝕜 z P.γ.toBirationalMap :=
    cInv_add (𝕜 := 𝕜) (w := z) (φ := P.α) (ψ := P.γ.toBirationalMap)
  have h2 : cInv 𝕜 z ((P.α.trans P.γ.toBirationalMap).trans P.α.symm) =
      cInv 𝕜 z (P.α.trans P.γ.toBirationalMap) + cInv 𝕜 z P.α.symm :=
    cInv_add (𝕜 := 𝕜) (w := z) (φ := P.α.trans P.γ.toBirationalMap) (ψ := P.α.symm)
  have h3 : cInv 𝕜 z P.γ.toBirationalMap = 0 :=
    pseudoReg_cInv_toBirationalMap 𝕜 z P.γ P.isPseudoIso
  have hmain : cInv 𝕜 z ((P.α.trans P.γ.toBirationalMap).trans P.α.symm) = 0 := by
    rw [h2, h1, h3, add_zero]
    linarith
  have hfe : (f : BirationalMap 𝔸(Fin n; Spec (.of 𝕜)) 𝔸(Fin n; Spec (.of 𝕜))) =
      (P.α.trans P.γ.toBirationalMap).trans P.α.symm := P.cond
  rw [hfe]
  exact hmain

end Work.Motivic
