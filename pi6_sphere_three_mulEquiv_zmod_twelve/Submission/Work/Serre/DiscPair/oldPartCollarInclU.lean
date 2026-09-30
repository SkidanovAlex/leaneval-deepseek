import Mathlib
import Submission.Work.Serre.DiscPair.oldPartDefs
import Submission.Work.Serre.DiscPair.subPairMapQuasiIso
import Submission.Work.Serre.DiscPair.collarDefs
import Submission.Work.Serre.DiscPair.collarHomeoA2
import Submission.Work.Serre.DiscPair.collarSetHomotopyEquiv
import Submission.Work.Serre.Basic

set_option synthInstance.maxHeartbeats 400000


/-!
# The collar of `U` inside the disc-pair pair

The inclusion `oldUBot ↪ oldUU₀` — the bottom copy of the source inside the collar `{λ < 1/2}`,
both cut down to the subspace `U = cylPairU q` — is a rational homology isomorphism: it is a
homotopy equivalence, with homotopy inverse the push-down of the collar (`λ ↦ 0`) obtained by
restricting the collaring homotopy `Aux.cylH` of `subPairMapQuasiIso` to the collar inside `U`.

Recall that `Aux.cylH q : I × ↥(cylU₀A₂ q) → ↥(cylPairA₂ q)` is the push-down of the collar: in
collar coordinates it replaces `λ` by `(1-s) λ` (this is `cylCollar_symm_push` / `cylH_val`
below).  A point of the collar of `U` has coordinates `(x,t)` with `x ∈ A = cylPairA q` and
`t < 1/2`, so both the push-down and the push-down homotopy stay inside `U`, and at `s = 1` the
push-down lands in the bottom copy `range (cylIncl q) = oldUBot q`.
-/

set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-! ## Elementary facts about the collar representation -/

/-- A point `⟦(x,t)⟧` of the mapping cylinder lies in `U` exactly when `x ∈ A`. -/
theorem mem_cylPairU_cylMk_inl (q : C(X, CylZ D Γ ι f)) (x : X) (t : unitInterval) :
    cylMk q (Sum.inl (x, t)) ∈ cylPairU q ↔ x ∈ cylPairA q := Iff.rfl

/-- The collar coordinate of a point of the collar model `cylSet₁`, read through `cylCollar`. -/
theorem cylLam_cylCollar_symm (q : C(X, CylZ D Γ ι f)) (z : ↥(cylSet₁ q)) :
    cylLam q (((Aux.cylCollar q).symm z : ↥(cylU₀A₂ q)) : cyl q) = z.1.2 := by
  obtain ⟨⟨x, t⟩, hmem⟩ := z
  rw [Aux.cylCollar_symm' q x t hmem]
  simp only [cylLam_cylMk_inl]

/-- The collar coordinate of a point of `cylU₀A₂` is the second coordinate of its collar
representative. -/
theorem cylLam_eq_cylCollar (q : C(X, CylZ D Γ ι f)) (y : ↥(cylU₀A₂ q)) :
    cylLam q (y : cyl q) = (Aux.cylCollar q y).1.2 := by
  have h := cylLam_cylCollar_symm q (Aux.cylCollar q y)
  rwa [Homeomorph.symm_apply_apply] at h

/-- **The coordinates of a point of the collar of `U`.**  A point of `cylU₀A₂` lying in `U` is
`⟦(x,t)⟧` with `t < 1/2` and `x ∈ A`, and `Aux.cylPr` is its `x`-coordinate. -/
theorem exists_coord (q : C(X, CylZ D Γ ι f)) (y' : ↥(cylU₀A₂ q))
    (hU : (y' : cyl q) ∈ cylPairU q) :
    ∃ (x : X) (t : unitInterval), (t : ℝ) < 1/2 ∧ x ∈ cylPairA q ∧
      Aux.cylPr q y' = x ∧ (y' : cyl q) = cylMk q (Sum.inl (x, t)) := by
  set z := Aux.cylCollar q y' with hz
  obtain ⟨⟨x, t⟩, hmem⟩ := z
  have hzval : Aux.cylCollar q y' = ⟨(x, t), hmem⟩ := hz.symm
  have hy' : y' = (Aux.cylCollar q).symm ⟨(x, t), hmem⟩ := by
    rw [← hzval, Homeomorph.symm_apply_apply]
  have hcyl : (y' : cyl q) = cylMk q (Sum.inl (x, t)) := by
    rw [hy', Aux.cylCollar_symm' q x t hmem]
  have hx : x ∈ cylPairA q := (mem_cylPairU_cylMk_inl q x t).mp (hcyl ▸ hU)
  have hpr : Aux.cylPr q y' = x := by
    show (Aux.cylCollar q y').1.1 = x
    rw [hzval]
  exact ⟨x, t, hmem.1, hx, hpr, hcyl⟩

/-- The `x`-coordinate `Aux.cylPr` of a point whose class is `⟦(x,t)⟧` is `x`. -/
theorem cylPr_eq_of_eq_cylMk (q : C(X, CylZ D Γ ι f)) (y' : ↥(cylU₀A₂ q)) (x : X)
    (t : unitInterval) (ht : (t : ℝ) < 1/2)
    (hy : (y' : cyl q) = cylMk q (Sum.inl (x, t))) : Aux.cylPr q y' = x := by
  set z := Aux.cylCollar q y' with hz
  obtain ⟨⟨x', t'⟩, hmem⟩ := z
  have hzval : Aux.cylCollar q y' = ⟨(x', t'), hmem⟩ := hz.symm
  have hy' : y' = (Aux.cylCollar q).symm ⟨(x', t'), hmem⟩ := by
    rw [← hzval, Homeomorph.symm_apply_apply]
  have hcyl : (y' : cyl q) = cylMk q (Sum.inl (x', t')) := by
    rw [hy', Aux.cylCollar_symm' q x' t' hmem]
  have htne : t ≠ 1 := by
    intro h; rw [h] at ht; norm_num at ht
  have heq : (Sum.inl (x', t') : (X × unitInterval) ⊕ CylZ D Γ ι f) = Sum.inl (x, t) :=
    (Work.Serre.eqvGen_inl_iff q (p := x) (t := t) htne
      (Quotient.exact (hcyl.symm.trans hy))).mpr rfl
  have h1 : x' = x := congrArg Prod.fst (Sum.inl.inj heq)
  have hpr : (Aux.cylCollar q y').1.1 = x' := by rw [hzval]
  rw [show Aux.cylPr q y' = (Aux.cylCollar q y').1.1 from rfl, hpr, h1]

/-- The `Aux.cylPr` of a point of the collar of `U` lies in `A`. -/
theorem cylPr_mem (q : C(X, CylZ D Γ ι f)) (y' : ↥(cylU₀A₂ q))
    (hU : (y' : cyl q) ∈ cylPairU q) : Aux.cylPr q y' ∈ cylPairA q := by
  obtain ⟨x, t, -, hx, hpr, -⟩ := exists_coord q y' hU
  rwa [hpr]

/-! ## The push-down in the collar model -/

/-- The push-down of the collar model commutes with `cylCollar`. -/
theorem cylCollar_symm_push (q : C(X, CylZ D Γ ι f)) (z : ↥(cylSet₁ q)) (s : unitInterval) :
    ((Aux.cylCollar q).symm (Aux.cylPush q (z, s)) : cyl q) =
      cylMk q (Sum.inl (z.1.1, Work.Serre.unitIntervalMulSub s z.1.2)) := by
  have hval : (Aux.cylPush q (z, s)).1 =
      (z.1.1, Work.Serre.unitIntervalMulSub s z.1.2) := rfl
  have hmem : (z.1.1, Work.Serre.unitIntervalMulSub s z.1.2) ∈ cylSet₁ q :=
    hval ▸ (Aux.cylPush q (z, s)).2
  have hpush : Aux.cylPush q (z, s) = ⟨_, hmem⟩ := Subtype.ext hval
  rw [hpush, Aux.cylCollar_symm' q z.1.1 (Work.Serre.unitIntervalMulSub s z.1.2) hmem]

/-- **The value of the collaring homotopy `Aux.cylH`** in collar coordinates. -/
theorem cylH_val (q : C(X, CylZ D Γ ι f)) (y' : ↥(cylU₀A₂ q)) (s : unitInterval) :
    ((Aux.cylH q (s, y') : ↥(cylPairA₂ q)) : cyl q) =
      cylMk q (Sum.inl ((Aux.cylCollar q y').1.1,
        Work.Serre.unitIntervalMulSub s (Aux.cylCollar q y').1.2)) :=
  cylCollar_symm_push q (Aux.cylCollar q y') s

/-- The collar coordinate of the collaring homotopy: `λ ↦ (1-s) λ`. -/
theorem cylLam_cylH (q : C(X, CylZ D Γ ι f)) (y' : ↥(cylU₀A₂ q)) (s : unitInterval) :
    (cylLam q ((Aux.cylH q (s, y') : ↥(cylPairA₂ q)) : cyl q) : ℝ) =
      (1 - (s : ℝ)) * ((Aux.cylCollar q y').1.2 : ℝ) := by
  rw [cylH_val]
  rfl

/-! ## The collar inside `U` -/

/-- The inclusion of subtypes `oldUU₀ ⊆ cylU₀A₂`. -/
def uuIncl (q : C(X, CylZ D Γ ι f)) : C(↥(oldUU₀ q), ↥(cylU₀A₂ q)) where
  toFun y := ⟨⟨y.1.1, Or.inl y.1.2⟩, y.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk
      (f := fun y : ↥(oldUU₀ q) => (⟨y.1.1, Or.inl y.1.2⟩ : ↥(cylPairA₂ q))) ?_
      (fun y => y.2)
    refine Continuous.subtype_mk
      (f := fun y : ↥(oldUU₀ q) => (y.1.1 : cyl q)) ?_ (fun y => Or.inl y.1.2)
    fun_prop

@[simp] theorem uuIncl_coe (q : C(X, CylZ D Γ ι f)) (y : ↥(oldUU₀ q)) :
    ((uuIncl q y : ↥(cylU₀A₂ q)) : cyl q) = y.1.1 := rfl

@[simp] theorem oldUIncl_coe_cyl (q : C(X, CylZ D Γ ι f)) (z : ↥(oldUBot q)) :
    ((oldUIncl q z : ↥(oldUU₀ q)) : cyl q) = z.1.1 := rfl

/-- The push-down stays in `U`. -/
theorem cylH_mem_U (q : C(X, CylZ D Γ ι f)) (y : ↥(oldUU₀ q)) (s : unitInterval) :
    ((Aux.cylH q (s, uuIncl q y) : ↥(cylPairA₂ q)) : cyl q) ∈ cylPairU q := by
  have hx : (Aux.cylCollar q (uuIncl q y)).1.1 ∈ cylPairA q :=
    cylPr_mem q (uuIncl q y) y.1.2
  rw [cylH_val]
  exact (mem_cylPairU_cylMk_inl q _ _).mpr hx

/-- The push-down stays in the collar. -/
theorem cylH_mem_U₀ (q : C(X, CylZ D Γ ι f)) (y : ↥(oldUU₀ q)) (s : unitInterval) :
    ((Aux.cylH q (s, uuIncl q y) : ↥(cylPairA₂ q)) : cyl q) ∈ cylU₀ q := by
  rw [mem_cylU₀_iff, cylLam_cylH]
  have ht : ((Aux.cylCollar q (uuIncl q y)).1.2 : ℝ) < 1/2 := by
    have h0 : (cylLam q ((uuIncl q y : ↥(cylU₀A₂ q)) : cyl q) : ℝ) < 1/2 := y.2
    rw [cylLam_eq_cylCollar] at h0
    exact h0
  have h0 : (0 : ℝ) ≤ ((Aux.cylCollar q (uuIncl q y)).1.2 : ℝ) :=
    (Aux.cylCollar q (uuIncl q y)).1.2.2.1
  have hs : (1 - (s : ℝ)) ≤ 1 := by linarith [s.2.1]
  calc (1 - (s : ℝ)) * ((Aux.cylCollar q (uuIncl q y)).1.2 : ℝ)
      ≤ 1 * ((Aux.cylCollar q (uuIncl q y)).1.2 : ℝ) := mul_le_mul_of_nonneg_right hs h0
    _ = ((Aux.cylCollar q (uuIncl q y)).1.2 : ℝ) := one_mul _
    _ < 1/2 := ht

/-- At the end of the push-down homotopy the point is in the bottom copy. -/
theorem cylH_one_mem_bot (q : C(X, CylZ D Γ ι f)) (y : ↥(oldUU₀ q)) :
    ((Aux.cylH q (1, uuIncl q y) : ↥(cylPairA₂ q)) : cyl q) ∈ cylPairBot q := by
  rw [Aux.cylH_one]
  exact ⟨Aux.cylPr q (uuIncl q y), by rw [cylInclA₂_coe]⟩

/-- **The push-down `oldUU₀ → oldUBot`** of the collar inside `U` onto the bottom copy. -/
def oldPush (q : C(X, CylZ D Γ ι f)) : C(↥(oldUU₀ q), ↥(oldUBot q)) where
  toFun y :=
    ⟨⟨↑(Aux.cylH q (1, uuIncl q y)), cylH_mem_U q y 1⟩, cylH_one_mem_bot q y⟩
  continuous_toFun := by
    refine Continuous.subtype_mk
      (f := fun y : ↥(oldUU₀ q) =>
        (⟨↑(Aux.cylH q (1, uuIncl q y)), cylH_mem_U q y 1⟩ : ↥(cylPairU q))) ?_
      (fun y => cylH_one_mem_bot q y)
    refine Continuous.subtype_mk
      (f := fun y : ↥(oldUU₀ q) => (↑(Aux.cylH q (1, uuIncl q y)) : cyl q)) ?_
      (fun y => cylH_mem_U q y 1)
    fun_prop

/-- **The push-down homotopy** of the collar inside `U`, from the identity to the composite
`oldUIncl ∘ oldPush`. -/
def oldH (q : C(X, CylZ D Γ ι f)) : C(unitInterval × ↥(oldUU₀ q), ↥(oldUU₀ q)) where
  toFun p :=
    ⟨⟨↑(Aux.cylH q (p.1, uuIncl q p.2)), cylH_mem_U q p.2 p.1⟩,
      cylH_mem_U₀ q p.2 p.1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk
      (f := fun p : unitInterval × ↥(oldUU₀ q) =>
        (⟨↑(Aux.cylH q (p.1, uuIncl q p.2)), cylH_mem_U q p.2 p.1⟩ : ↥(cylPairU q))) ?_
      (fun p => cylH_mem_U₀ q p.2 p.1)
    refine Continuous.subtype_mk
      (f := fun p : unitInterval × ↥(oldUU₀ q) =>
        (↑(Aux.cylH q (p.1, uuIncl q p.2)) : cyl q)) ?_
      (fun p => cylH_mem_U q p.2 p.1)
    fun_prop

theorem oldH_zero (q : C(X, CylZ D Γ ι f)) (y : ↥(oldUU₀ q)) : oldH q (0, y) = y := by
  refine Subtype.ext (Subtype.ext ?_)
  show (↑(Aux.cylH q (0, uuIncl q y)) : cyl q) = y.1.1
  rw [Aux.cylH_zero]
  exact uuIncl_coe q y

theorem oldH_one (q : C(X, CylZ D Γ ι f)) (y : ↥(oldUU₀ q)) :
    oldH q (1, y) = oldUIncl q (oldPush q y) := by
  refine Subtype.ext (Subtype.ext ?_)
  rfl

theorem oldPush_incl (q : C(X, CylZ D Γ ι f)) (z : ↥(oldUBot q)) :
    oldPush q (oldUIncl q z) = z := by
  obtain ⟨x, hx⟩ := z.2
  have hpr : Aux.cylPr q (uuIncl q (oldUIncl q z)) = x :=
    cylPr_eq_of_eq_cylMk q (uuIncl q (oldUIncl q z)) x 0 (by norm_num) (by
      show ((uuIncl q (oldUIncl q z) : ↥(cylU₀A₂ q)) : cyl q) = cylMk q (Sum.inl (x, 0))
      rw [uuIncl_coe]
      exact hx.symm)
  refine Subtype.ext (Subtype.ext ?_)
  show (↑(Aux.cylH q (1, uuIncl q (oldUIncl q z))) : cyl q) = z.1.1
  rw [Aux.cylH_one, cylInclA₂_coe, hpr, ← hx]

end

end Work.Serre.DiscPair

namespace Work.Serre.DiscPair

/-- The inclusion `oldUBot ↪ oldUU₀` of the bottom of the collar into the collar, inside the
sub-space `U = cylPairU q`, is a rational homology isomorphism.  (`oldUBot = {x : ↥(cylPairU q) |
(x : cyl q) ∈ cylPairBot q}`, `oldUU₀ = {x : ↥(cylPairU q) | (x : cyl q) ∈ cylU₀ q}` and `oldUIncl`
is the inclusion; all three are in `Submission.Work.Serre.DiscPair.oldPartDefs`, and
`cylU₀ q = {λ < 1/2}` for the collar coordinate `λ = cylLam q`.) -/
theorem oldPartCollarInclU (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.Serre.DiscPair.CylZ D Γ ι f)) :
    Work.Serre.IsRatHomologyIso
      (Work.Serre.DiscPair.oldUIncl (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) := by
  have hleft : ((oldPush q).comp (oldUIncl q)).Homotopic
      (ContinuousMap.id ↥(oldUBot q)) := by
    have hcomp : (oldPush q).comp (oldUIncl q) = ContinuousMap.id ↥(oldUBot q) :=
      ContinuousMap.ext (fun z => oldPush_incl q z)
    simpa only [hcomp] using
      (show ((ContinuousMap.id ↥(oldUBot q)).Homotopic (ContinuousMap.id ↥(oldUBot q))) from
        ⟨ContinuousMap.Homotopy.refl _⟩)
  have hright : ((oldUIncl q).comp (oldPush q)).Homotopic
      (ContinuousMap.id ↥(oldUU₀ q)) :=
    ⟨ContinuousMap.Homotopy.symm
      { toContinuousMap := oldH q
        map_zero_left := fun y => oldH_zero q y
        map_one_left := fun y => oldH_one q y }⟩
  exact Work.Serre.IsRatHomologyIso.of_homotopyEquiv
    (ContinuousMap.HomotopyEquiv.mk (oldUIncl q) (oldPush q) hleft hright)

end Work.Serre.DiscPair
