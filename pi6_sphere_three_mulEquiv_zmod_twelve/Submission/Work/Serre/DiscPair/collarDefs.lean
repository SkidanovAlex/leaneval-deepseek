import Mathlib
import Submission.Work.Serre.DiscPair.cylPairDefs

/-!
# The collar of the mapping cylinder: the coordinate `λ` and the sets `U₀`, `U₁`

Vocabulary for the disc-pair comparison `Work.Serre.DiscPair.subPairMapQuasiIso`.

For `q : C(X, Z)` with `Z = attachCells (D-2) Γ ι f` we consider the mapping cylinder
`cyl q` (see `Submission/Work/Serre/C1Cyl.lean`) and its **collar coordinate**

`λ : cyl q → I`,  `λ (x,t) = t` on `X × I`,  `λ z = 1` on the target copy,

which is the quotient lift of `((X × I) ⊔ Z) → I`, `inl (x,t) ↦ t`, `inr z ↦ 1` (continuous,
because the gluing relation `(x,1) ~ q x` is respected).  We put

* `U₀ = {λ < 1/2}` and `U₁ = {0 < λ}` (both open in `cyl q`).

With `A₂ = cylPairA₂ q = U ∪ range (cylIncl q)` (where `U = cylPairU q = (cylRetract q)⁻¹ Y'`,
`Y' = cylPairS`, `A₂ = U ∪ cylPairBot q`) the basic facts are

* `range (cylIncl q) = {λ = 0}` (`cylLam_eq_zero_iff`),
* `A₂ ∩ U₁ ⊆ U` (`cylU₁_inter_cylPairA₂_subset`),
* `A₂ = range (cylIncl q) ∪ (A₂ ∩ U₁)`,
* `{A₂ ∩ U₀, A₂ ∩ U₁}` is an open cover of `A₂` (`cylU₀A₂_union_cylU₁A₂`),

and `cylMove q` (the push-up homotopy of the cylinder) preserves `U` and `U₁` with
`λ (cylMove q (y,s)) = (1-s) λ y + s` (`cylLam_cylMove`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

/-- The target `Z = attachCells (D-2) Γ ι f` of the attaching maps. -/
abbrev CylZ (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) : Type :=
  Work.RatHurewicz.attachCells (D-2) Γ ι f

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

theorem one_ne_zero_unitInterval : (1 : unitInterval) ≠ 0 := by
  intro h
  have h' : ((1 : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ) := congrArg Subtype.val h
  norm_num at h'

/-! ## The collar coordinate `λ` -/

/-- The collar coordinate on the presenting disjoint union of the mapping cylinder: `t` on
`X × I` and `1` on the target copy. -/
def cylLamFun (q : C(X, CylZ D Γ ι f)) :
    (X × unitInterval) ⊕ CylZ D Γ ι f → unitInterval :=
  Sum.elim (fun z => z.2) (fun _ => 1)

/-- The collar coordinate function respects the gluing relation of the mapping cylinder. -/
theorem cylLamFun_rel (q : C(X, CylZ D Γ ι f)) :
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

/-- **The collar coordinate** `λ : cyl q → I`, the quotient lift of `inl (x,t) ↦ t`,
`inr z ↦ 1`. -/
def cylLam (q : C(X, CylZ D Γ ι f)) : cyl q → unitInterval :=
  Quotient.lift (cylLamFun q) (cylLamFun_rel q)

/-- The collar coordinate is continuous. -/
theorem continuous_cylLam (q : C(X, CylZ D Γ ι f)) : Continuous (cylLam q) := by
  have h1 : Continuous (cylLamFun q) := by
    unfold cylLamFun
    exact Continuous.sumElim continuous_snd continuous_const
  rw [cylLam]
  exact h1.quotient_lift (cylLamFun_rel q)

@[simp] theorem cylLam_cylMk (q : C(X, CylZ D Γ ι f))
    (a : (X × unitInterval) ⊕ CylZ D Γ ι f) :
    cylLam q (cylMk q a) = cylLamFun q a := rfl

@[simp] theorem cylLam_cylMk_inl (q : C(X, CylZ D Γ ι f)) (x : X) (t : unitInterval) :
    cylLam q (cylMk q (Sum.inl (x, t))) = t := rfl

@[simp] theorem cylLam_cylMk_inr (q : C(X, CylZ D Γ ι f)) (z : CylZ D Γ ι f) :
    cylLam q (cylMk q (Sum.inr z)) = 1 := rfl

@[simp] theorem cylLam_cylIncl (q : C(X, CylZ D Γ ι f)) (x : X) :
    cylLam q (cylIncl q x) = 0 := rfl

@[simp] theorem cylLam_cylInr (q : C(X, CylZ D Γ ι f)) (z : CylZ D Γ ι f) :
    cylLam q (cylInr q z) = 1 := rfl

/-- **The bottom copy is the zero set of the collar coordinate.** -/
theorem cylLam_eq_zero_iff (q : C(X, CylZ D Γ ι f)) (y : cyl q) :
    cylLam q y = 0 ↔ y ∈ Set.range (cylIncl q) := by
  constructor
  · induction y using Quotient.inductionOn with
    | h a =>
      rcases a with ⟨x, t⟩ | z
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
theorem lt_cylLam_of_not_mem (q : C(X, CylZ D Γ ι f)) {y : cyl q}
    (hy : y ∉ Set.range (cylIncl q)) : 0 < (cylLam q y : ℝ) :=
  lt_of_le_of_ne (cylLam q y).2.1 (fun h =>
    hy ((cylLam_eq_zero_iff q y).mp (Subtype.ext h.symm)))

/-! ## The sets `U₀`, `U₁` -/

/-- `U₀ = {λ < 1/2} ⊆ cyl q`. -/
def cylU₀ (q : C(X, CylZ D Γ ι f)) : Set (cyl q) :=
  cylLam q ⁻¹' {t : unitInterval | (t : ℝ) < 1/2}

/-- `U₁ = {0 < λ} ⊆ cyl q`. -/
def cylU₁ (q : C(X, CylZ D Γ ι f)) : Set (cyl q) :=
  cylLam q ⁻¹' {t : unitInterval | 0 < (t : ℝ)}

theorem mem_cylU₀_iff (q : C(X, CylZ D Γ ι f)) (y : cyl q) :
    y ∈ cylU₀ q ↔ (cylLam q y : ℝ) < 1/2 := Iff.rfl

theorem mem_cylU₁_iff (q : C(X, CylZ D Γ ι f)) (y : cyl q) :
    y ∈ cylU₁ q ↔ 0 < (cylLam q y : ℝ) := Iff.rfl

theorem mem_cylU₁_cylMk_inl_iff (q : C(X, CylZ D Γ ι f)) (x : X) (t : unitInterval) :
    cylMk q (Sum.inl (x, t)) ∈ cylU₁ q ↔ 0 < (t : ℝ) := by
  rw [mem_cylU₁_iff, cylLam_cylMk_inl]

theorem mem_cylU₀_cylMk_inl_iff (q : C(X, CylZ D Γ ι f)) (x : X) (t : unitInterval) :
    cylMk q (Sum.inl (x, t)) ∈ cylU₀ q ↔ (t : ℝ) < 1/2 := by
  rw [mem_cylU₀_iff, cylLam_cylMk_inl]

theorem isOpen_cylU₀ (q : C(X, CylZ D Γ ι f)) : IsOpen (cylU₀ q) :=
  (isOpen_lt continuous_subtype_val continuous_const).preimage (continuous_cylLam q)

theorem isOpen_cylU₁ (q : C(X, CylZ D Γ ι f)) : IsOpen (cylU₁ q) :=
  (isOpen_lt continuous_const continuous_subtype_val).preimage (continuous_cylLam q)

/-! ## The interaction of `λ` with the push-up homotopy `cylMove` -/

/-- **The push-up homotopy acts on the collar coordinate by `t ↦ (1-s) t + s`.** -/
theorem cylLam_cylMove (q : C(X, CylZ D Γ ι f)) (y : cyl q) (s : unitInterval) :
    cylLam q (cylMove q (y, s)) = unitIntervalLin s (cylLam q y) := by
  induction y using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨x, t⟩ | z
    · rfl
    · show (1 : unitInterval) = unitIntervalLin s 1
      rw [unitIntervalLin_one_right]

/-- The push-up homotopy does not move the points of the retraction. -/
theorem cylRetract_cylMove (q : C(X, CylZ D Γ ι f)) (y : cyl q) (s : unitInterval) :
    cylRetract q (cylMove q (y, s)) = cylRetract q y := by
  induction y using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨x, t⟩ | z <;> rfl

/-- The push-up homotopy preserves `U = (cylRetract q) ⁻¹' Y'`. -/
theorem cylMove_mem_cylPairU (q : C(X, CylZ D Γ ι f)) {y : cyl q}
    (hy : y ∈ cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) (s : unitInterval) :
    cylMove q (y, s) ∈ cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q := by
  show cylRetract q (cylMove q (y, s)) ∈ cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)
  rw [cylRetract_cylMove]
  exact hy

/-- `(1-s) t + s > 0` for `t > 0`. -/
theorem lt_unitIntervalLin_right (s t : unitInterval) (ht : 0 < (t : ℝ)) :
    0 < (unitIntervalLin s t : ℝ) := by
  have hkey : (unitIntervalLin s t : ℝ) = (t : ℝ) + (s : ℝ) * (1 - (t : ℝ)) := by
    show (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) = (t : ℝ) + (s : ℝ) * (1 - (t : ℝ))
    ring
  rw [hkey]
  nlinarith [ht, s.2.1, t.2.2, mul_nonneg s.2.1 (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ))]

/-- The push-up homotopy preserves `U₁ = {0 < λ}`. -/
theorem cylMove_mem_cylU₁ (q : C(X, CylZ D Γ ι f)) {y : cyl q} (hy : y ∈ cylU₁ q)
    (s : unitInterval) : cylMove q (y, s) ∈ cylU₁ q := by
  rw [mem_cylU₁_iff] at hy ⊢
  rw [cylLam_cylMove]
  exact lt_unitIntervalLin_right s (cylLam q y) hy

/-! ## The two pieces of `A₂` -/

/-- `A₂ ∩ U₁ ⊆ U`. -/
theorem cylU₁_inter_cylPairA₂_subset (q : C(X, CylZ D Γ ι f)) :
    cylU₁ q ∩ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
      ⊆ cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q := by
  rintro y ⟨hy1, hyA⟩
  rcases hyA with hyU | hyB
  · exact hyU
  · exfalso
    have h0 : cylLam q y = 0 := (cylLam_eq_zero_iff q y).mpr hyB
    rw [mem_cylU₁_iff, h0] at hy1
    exact lt_irrefl 0 hy1

/-- `A₂ = range (cylIncl q) ∪ (A₂ ∩ U₁)`. -/
theorem cylPairA₂_eq_cylPairBot_union (q : C(X, CylZ D Γ ι f)) :
    cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
      = cylPairBot (D := D) (Γ := Γ) (ι := ι) q
        ∪ (cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
            ∩ cylU₁ q) := by
  ext y
  constructor
  · intro hy
    rcases hy with hyU | hyB
    · by_cases h : y ∈ cylPairBot (D := D) (Γ := Γ) (ι := ι) q
      · exact Or.inl h
      · refine Or.inr ⟨Or.inl hyU, ?_⟩
        rw [mem_cylU₁_iff]
        exact lt_cylLam_of_not_mem q h
    · exact Or.inl hyB
  · rintro (hyB | ⟨hyA, -⟩)
    · exact Or.inr hyB
    · exact hyA

/-! ## The same sets inside `A₂` -/

/-- `U₀` cut down to `A₂`. -/
def cylU₀A₂ (q : C(X, CylZ D Γ ι f)) :
    Set ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  {x | (x : cyl q) ∈ cylU₀ q}

/-- `U₁` cut down to `A₂`. -/
def cylU₁A₂ (q : C(X, CylZ D Γ ι f)) :
    Set ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  {x | (x : cyl q) ∈ cylU₁ q}

theorem cylU₁A₂_subset_cylPairUinA₂ (q : C(X, CylZ D Γ ι f)) :
    cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
      ⊆ cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q :=
  fun x hx => cylU₁_inter_cylPairA₂_subset q ⟨hx, x.2⟩

theorem cylU₁A₂_mapsTo_cylPairUinA₂ (q : C(X, CylZ D Γ ι f)) :
    Set.MapsTo (⇑(ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
      (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  fun x hx => cylU₁A₂_subset_cylPairUinA₂ q hx

/-- **`{A₂ ∩ U₀, A₂ ∩ U₁}` covers `A₂`.** -/
theorem cylU₀A₂_union_cylU₁A₂ (q : C(X, CylZ D Γ ι f)) :
    cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
      ∪ cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : (cylLam q (x : cyl q) : ℝ) < 1/2
  · exact Or.inl h
  · refine Or.inr ?_
    show 0 < (cylLam q (x : cyl q) : ℝ)
    linarith

/-- The pair subset `(A₂ ∩ U₁)` inside `U₀A₂`: the relative part of the collar. -/
def cylU₀U₁A₂ (q : C(X, CylZ D Γ ι f)) :
    Set ↥(cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  {y | (y.1 : ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
        ∈ cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q}

/-- The collar model of `A₂ ∩ U₀` inside `X × I`: `(X × {0}) ∪ (A × (0,1/2))`. -/
def cylSet₁ (q : C(X, CylZ D Γ ι f)) : Set (X × unitInterval) :=
  {z | (z.2 : ℝ) < 1/2 ∧ (z.2 = 0 ∨ z.1 ∈ cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)}

/-- The collar model of `A₂ ∩ U₀ ∩ U₁` inside `X × I`: `A × (0,1/2)`. -/
def cylSet₂ (q : C(X, CylZ D Γ ι f)) : Set (X × unitInterval) :=
  {z | 0 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1/2
    ∧ z.1 ∈ cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q}

/-- Membership of a cylinder point in `A₂` in terms of the collar coordinates. -/
theorem mem_cylPairA₂_cylMk_inl_iff (q : C(X, CylZ D Γ ι f)) (x : X) (t : unitInterval)
    (ht : (t : ℝ) < 1/2) :
    cylMk q (Sum.inl (x, t)) ∈ cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q
      ↔ t = 0 ∨ x ∈ cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q := by
  constructor
  · intro hy
    rcases hy with hyU | hyB
    · right
      exact hyU
    · left
      have h2 := hyB
      rw [cylPairBot, Set.mem_range] at h2
      obtain ⟨x', hx'⟩ := h2
      have := congrArg (cylLam q) hx'
      rw [cylLam_cylMk_inl, cylLam_cylIncl] at this
      exact this.symm
  · rintro (rfl | hxA)
    · exact Or.inr ⟨x, rfl⟩
    · exact Or.inl hxA

end

end Work.Serre.DiscPair
