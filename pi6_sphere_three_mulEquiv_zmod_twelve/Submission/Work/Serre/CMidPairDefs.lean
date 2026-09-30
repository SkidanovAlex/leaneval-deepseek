import Mathlib
import Submission.Work.Serre.C1Cyl

/-!
# The collar neighbourhood of the "middle" pair `(cyl q, CMid q b)`, for an arbitrary base

`Work.Serre.CMid q b = range (cylIncl q) ∪ (cylRetract q) ⁻¹' {b}` is the "old part" of the mapping
cylinder of `q` at the point `b`: the bottom copy `A = range (cylIncl q)` together with the cone
`P = (cylRetract q) ⁻¹' {b}` on the fibre `F_b = q ⁻¹' {b}`.

This file is the general-base counterpart of `Submission/Work/Serre/DiscPair/collarDefs.lean` (where
the base is `attachCells (D-2) Γ ι f` and the "old part" is `range (attachIncl)`, i.e. `Y' = univ`).
Everything there depends on the old part only through the two properties

* `cylPairA = q ⁻¹' Y'` and `cylPairU = (cylRetract q) ⁻¹' Y'`, `cylPairA₂ = cylPairU ∪ range (cylIncl q)`,

so it generalises verbatim to `Y' = {b}` with an arbitrary base.  We record here the collar
coordinate `λ`, the open sets `U₀ = {λ < 1/2}`, `U₁ = {0 < λ}`, the pieces `U₀A₂`, `U₁A₂`,
`U₀U₁A₂` of `CMid q b`, the collar models `cylSet₁`, `cylSet₂ ⊆ X × I`, and the elementary
identities they satisfy (they are copies of the corresponding statements of `collarDefs.lean`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.CMidPair

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The collar coordinate `λ` -/

/-- The collar coordinate on the presenting disjoint union: `t` on `X × I` and `1` on the base. -/
def cylLamFun (q : C(X, B)) : (X × unitInterval) ⊕ B → unitInterval :=
  Sum.elim (fun z => z.2) (fun _ => 1)

/-- The collar coordinate respects the gluing relation of the mapping cylinder. -/
theorem cylLamFun_rel (q : C(X, B)) :
    ∀ a b, Relation.EqvGen (cylRel q) a b → cylLamFun q a = cylLamFun q b := by
  have hgen : ∀ a b, cylRel q a b → cylLamFun q a = cylLamFun q b := by
    rintro a b ⟨p, rfl, rfl⟩
    rfl
  intro a b hab
  induction hab with
  | rel x y h => exact hgen x y h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The collar coordinate** `λ : cyl q → I`: the quotient lift of `inl (x,t) ↦ t`, `inr b ↦ 1`. -/
def cylLam (q : C(X, B)) : cyl q → unitInterval :=
  Quotient.lift (cylLamFun q) (cylLamFun_rel q)

theorem continuous_cylLam (q : C(X, B)) : Continuous (cylLam q) := by
  have h1 : Continuous (cylLamFun q) := by
    unfold cylLamFun
    exact Continuous.sumElim continuous_snd continuous_const
  rw [cylLam]
  exact h1.quotient_lift (cylLamFun_rel q)

@[simp] theorem cylLam_cylMk (q : C(X, B)) (a : (X × unitInterval) ⊕ B) :
    cylLam q (cylMk q a) = cylLamFun q a := rfl

@[simp] theorem cylLam_cylMk_inl (q : C(X, B)) (x : X) (t : unitInterval) :
    cylLam q (cylMk q (Sum.inl (x, t))) = t := rfl

@[simp] theorem cylLam_cylMk_inr (q : C(X, B)) (b' : B) :
    cylLam q (cylMk q (Sum.inr b')) = 1 := rfl

@[simp] theorem cylLam_cylIncl (q : C(X, B)) (x : X) : cylLam q (cylIncl q x) = 0 := rfl

@[simp] theorem cylLam_cylInr (q : C(X, B)) (b' : B) : cylLam q (cylInr q b') = 1 := rfl

theorem one_ne_zero_unitInterval : (1 : unitInterval) ≠ 0 := by
  intro h
  have h' : ((1 : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ) := congrArg Subtype.val h
  norm_num at h'

/-- **The bottom copy is the zero set of the collar coordinate.** -/
theorem cylLam_eq_zero_iff (q : C(X, B)) (y : cyl q) :
    cylLam q y = 0 ↔ y ∈ Set.range (cylIncl q) := by
  constructor
  · induction y using Quotient.inductionOn with
    | h a =>
      rcases a with ⟨x, t⟩ | b'
      · intro h
        refine ⟨x, ?_⟩
        have ht : t = (0 : unitInterval) := h
        rw [ht]
        rfl
      · intro h
        exact absurd (show (1 : unitInterval) = 0 from h) one_ne_zero_unitInterval
  · rintro ⟨x, rfl⟩
    rfl

/-- The collar coordinate is positive away from the bottom copy. -/
theorem lt_cylLam_of_not_mem (q : C(X, B)) {y : cyl q}
    (hy : y ∉ Set.range (cylIncl q)) : 0 < (cylLam q y : ℝ) :=
  lt_of_le_of_ne (cylLam q y).2.1 (fun h =>
    hy ((cylLam_eq_zero_iff q y).mp (Subtype.ext h.symm)))

/-! ## The sets `U₀ = {λ < 1/2}` and `U₁ = {0 < λ}` -/

def cylU₀ (q : C(X, B)) : Set (cyl q) :=
  cylLam q ⁻¹' {t : unitInterval | (t : ℝ) < 1/2}

def cylU₁ (q : C(X, B)) : Set (cyl q) :=
  cylLam q ⁻¹' {t : unitInterval | 0 < (t : ℝ)}

theorem mem_cylU₀_iff (q : C(X, B)) (y : cyl q) :
    y ∈ cylU₀ q ↔ (cylLam q y : ℝ) < 1/2 := Iff.rfl

theorem mem_cylU₁_iff (q : C(X, B)) (y : cyl q) :
    y ∈ cylU₁ q ↔ 0 < (cylLam q y : ℝ) := Iff.rfl

theorem mem_cylU₁_cylMk_inl_iff (q : C(X, B)) (x : X) (t : unitInterval) :
    cylMk q (Sum.inl (x, t)) ∈ cylU₁ q ↔ 0 < (t : ℝ) := by
  rw [mem_cylU₁_iff, cylLam_cylMk_inl]

theorem mem_cylU₀_cylMk_inl_iff (q : C(X, B)) (x : X) (t : unitInterval) :
    cylMk q (Sum.inl (x, t)) ∈ cylU₀ q ↔ (t : ℝ) < 1/2 := by
  rw [mem_cylU₀_iff, cylLam_cylMk_inl]

theorem isOpen_cylU₀ (q : C(X, B)) : IsOpen (cylU₀ q) :=
  (isOpen_lt continuous_subtype_val continuous_const).preimage (continuous_cylLam q)

theorem isOpen_cylU₁ (q : C(X, B)) : IsOpen (cylU₁ q) :=
  (isOpen_lt continuous_const continuous_subtype_val).preimage (continuous_cylLam q)

/-! ## The interaction of `λ` with the push-up homotopy `cylMove` -/

/-- **The push-up homotopy acts on the collar coordinate by `t ↦ (1-s) t + s`.** -/
theorem cylLam_cylMove (q : C(X, B)) (y : cyl q) (s : unitInterval) :
    cylLam q (cylMove q (y, s)) = unitIntervalLin s (cylLam q y) := by
  induction y using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨x, t⟩ | b'
    · rfl
    · show (1 : unitInterval) = unitIntervalLin s 1
      rw [unitIntervalLin_one_right]

/-- The push-up homotopy does not move the points of the retraction. -/
theorem cylRetract_cylMove (q : C(X, B)) (y : cyl q) (s : unitInterval) :
    cylRetract q (cylMove q (y, s)) = cylRetract q y := by
  induction y using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨x, t⟩ | b' <;> rfl

/-- `(1-s) t + s > 0` for `t > 0`. -/
theorem lt_unitIntervalLin_right (s t : unitInterval) (ht : 0 < (t : ℝ)) :
    0 < (unitIntervalLin s t : ℝ) := by
  have hkey : (unitIntervalLin s t : ℝ) = (t : ℝ) + (s : ℝ) * (1 - (t : ℝ)) := by
    show (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) = (t : ℝ) + (s : ℝ) * (1 - (t : ℝ))
    ring
  rw [hkey]
  nlinarith [ht, s.2.1, t.2.2,
    mul_nonneg s.2.1 (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ))]

/-- The push-up homotopy preserves `U₁ = {0 < λ}`. -/
theorem cylMove_mem_cylU₁ (q : C(X, B)) {y : cyl q} (hy : y ∈ cylU₁ q)
    (s : unitInterval) : cylMove q (y, s) ∈ cylU₁ q := by
  rw [mem_cylU₁_iff] at hy ⊢
  rw [cylLam_cylMove]
  exact lt_unitIntervalLin_right s (cylLam q y) hy

/-! ## The old part and its two pieces -/

/-- The fibre `F_b = q ⁻¹' {b}` over `b`. -/
def cylPairA (q : C(X, B)) (b : B) : Set X := q ⁻¹' ({b} : Set B)

/-- The cone `P = (cylRetract q) ⁻¹' {b}` on the fibre over `b`. -/
def cylPairU (q : C(X, B)) (b : B) : Set (cyl q) := (cylRetract q) ⁻¹' ({b} : Set B)

/-- The bottom copy `A = range (cylIncl q)`. -/
def cylPairBot (q : C(X, B)) : Set (cyl q) := Set.range (cylIncl q)

/-- The old part `A₂ = P ∪ A = CMid q b`. -/
def cylPairA₂ (q : C(X, B)) (b : B) : Set (cyl q) :=
  cylPairBot q ∪ cylPairU q b

/-- The cone inside the old part. -/
def cylPairUinA₂ (q : C(X, B)) (b : B) : Set ↥(cylPairA₂ q b) :=
  {x | (x : cyl q) ∈ cylPairU q b}

/-- `U₀` cut down to `A₂`. -/
def cylU₀A₂ (q : C(X, B)) (b : B) : Set ↥(cylPairA₂ q b) :=
  {x | (x : cyl q) ∈ cylU₀ q}

/-- `U₁` cut down to `A₂`. -/
def cylU₁A₂ (q : C(X, B)) (b : B) : Set ↥(cylPairA₂ q b) :=
  {x | (x : cyl q) ∈ cylU₁ q}

/-- The relative part `(A₂ ∩ U₀) ∩ U₁` of the collar. -/
def cylU₀U₁A₂ (q : C(X, B)) (b : B) : Set ↥(cylU₀A₂ q b) :=
  {y | (y.1 : ↥(cylPairA₂ q b)) ∈ cylU₁A₂ q b}

/-- The collar model of `A₂ ∩ U₀` inside `X × I`: `(X × {0}) ∪ (F_b × (0,1/2))`. -/
def cylSet₁ (q : C(X, B)) (b : B) : Set (X × unitInterval) :=
  {z | (z.2 : ℝ) < 1/2 ∧ (z.2 = 0 ∨ z.1 ∈ cylPairA q b)}

/-- The collar model of `A₂ ∩ U₀ ∩ U₁` inside `X × I`: `F_b × (0,1/2)`. -/
def cylSet₂ (q : C(X, B)) (b : B) : Set (X × unitInterval) :=
  {z | 0 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1/2 ∧ z.1 ∈ cylPairA q b}

/-! ## Elementary identities -/

/-- The push-up homotopy preserves the cone `P = cylPairU q b`. -/
theorem cylMove_mem_cylPairU (q : C(X, B)) (b : B) {y : cyl q}
    (hy : y ∈ cylPairU q b) (s : unitInterval) : cylMove q (y, s) ∈ cylPairU q b := by
  show cylRetract q (cylMove q (y, s)) ∈ ({b} : Set B)
  rw [cylRetract_cylMove]
  exact hy

/-- The retraction of a cylinder point. -/
theorem cylRetract_cylMk_inl (q : C(X, B)) (x : X) (t : unitInterval) :
    cylRetract q (cylMk q (Sum.inl (x, t))) = q x := rfl

/-- `A₂ ∩ U₁ ⊆ P`. -/
theorem cylU₁_inter_cylPairA₂_subset (q : C(X, B)) (b : B) :
    cylU₁ q ∩ cylPairA₂ q b ⊆ cylPairU q b := by
  rintro y ⟨hy1, hyA⟩
  rcases hyA with hyB | hyU
  · exfalso
    have h0 : cylLam q y = 0 := (cylLam_eq_zero_iff q y).mpr hyB
    rw [mem_cylU₁_iff, h0] at hy1
    exact lt_irrefl 0 hy1
  · exact hyU

/-- `A₂ = A ∪ (A₂ ∩ U₁)`. -/
theorem cylPairA₂_eq_cylPairBot_union (q : C(X, B)) (b : B) :
    cylPairA₂ q b = cylPairBot q ∪ (cylPairA₂ q b ∩ cylU₁ q) := by
  ext y
  constructor
  · intro hy
    rcases hy with hyB | hyU
    · exact Or.inl hyB
    · by_cases h : y ∈ cylPairBot q
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr hyU, (mem_cylU₁_iff q y).mpr (lt_cylLam_of_not_mem q h)⟩
  · rintro (hyB | ⟨hyA, -⟩)
    · exact Or.inl hyB
    · exact hyA

/-- `{A₂ ∩ U₀, A₂ ∩ U₁}` covers `A₂`. -/
theorem cylU₀A₂_union_cylU₁A₂ (q : C(X, B)) (b : B) :
    cylU₀A₂ q b ∪ cylU₁A₂ q b = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : (cylLam q (x : cyl q) : ℝ) < 1/2
  · exact Or.inl h
  · refine Or.inr ?_
    show 0 < (cylLam q (x : cyl q) : ℝ)
    linarith

theorem cylU₁A₂_subset_cylPairUinA₂ (q : C(X, B)) (b : B) :
    cylU₁A₂ q b ⊆ cylPairUinA₂ q b :=
  fun x hx => cylU₁_inter_cylPairA₂_subset q b ⟨hx, x.2⟩

theorem cylU₁A₂_mapsTo_cylPairUinA₂ (q : C(X, B)) (b : B) :
    Set.MapsTo (⇑(ContinuousMap.id ↥(cylPairA₂ q b)))
      (cylU₁A₂ q b) (cylPairUinA₂ q b) :=
  fun x hx => cylU₁A₂_subset_cylPairUinA₂ q b hx

/-- Membership of a cylinder point in `A₂` in terms of the coordinates. -/
theorem mem_cylPairA₂_cylMk_inl_iff (q : C(X, B)) (b : B) (x : X) (t : unitInterval)
    (ht : (t : ℝ) < 1/2) :
    cylMk q (Sum.inl (x, t)) ∈ cylPairA₂ q b ↔ t = 0 ∨ x ∈ cylPairA q b := by
  constructor
  · intro hy
    rcases hy with hyB | hyU
    · left
      obtain ⟨x', hx'⟩ := hyB
      have h := congrArg (cylLam q) hx'
      rw [cylLam_cylIncl, cylLam_cylMk_inl] at h
      exact h.symm
    · right
      show q x ∈ ({b} : Set B)
      rw [← cylRetract_cylMk_inl q x t]
      exact hyU
  · rintro (rfl | hxA)
    · exact Or.inl ⟨x, rfl⟩
    · refine Or.inr ?_
      show cylRetract q (cylMk q (Sum.inl (x, t))) ∈ ({b} : Set B)
      rw [cylRetract_cylMk_inl]
      exact hxA

/-- `cylIncl q` viewed as a map into the old part `A₂`. -/
def cylInclA₂ (q : C(X, B)) (b : B) : C(X, ↥(cylPairA₂ q b)) where
  toFun x := ⟨cylIncl q x, Or.inl ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk (f := fun x : X => cylIncl q x)
    ((cylIncl q).continuous) (fun x => Or.inl ⟨x, rfl⟩)

theorem cylInclA₂_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (cylInclA₂ q b) (cylPairA q b) (cylPairUinA₂ q b) := by
  intro x hx
  show cylRetract q (cylIncl q x) ∈ ({b} : Set B)
  exact hx

@[simp] theorem cylInclA₂_coe (q : C(X, B)) (b : B) (x : X) :
    ((cylInclA₂ q b) x : cyl q) = cylIncl q x := rfl

end

end Work.Serre.CMidPair
