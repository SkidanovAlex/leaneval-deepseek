/-
  WilC4 : the vocabulary of the o-minimal monotonicity theorem (`WilC4.mono_real`).

  `mono_real` states: a `∅`-definable functional subset `Y ⊆ ℝ²` (a partial definable function)
  agrees with a monotone function on every interval avoiding a finite exceptional set `B`.
  This is the "R-mono" input of the C4 route (`sources/wilkiesC4route/wilkies_C4_route.md`).

  The proof follows the classical proof of the o-minimal monotonicity theorem: one shows that
  the one-sided germs of the function are eventually on one side of the value at every point
  (Schoutens, *O-minimalism*, Theorem 4.2), that the sets of points with a given germ type have
  finite topological boundary (this is where o-minimality enters), and that on a connected piece
  avoiding those boundaries the germ type is constant, which forces monotonicity.

  This module only fixes the vocabulary: the partial function encoded by `Y` is never materialised,
  all sets are described directly in terms of the relation `Y`.
-/
import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.BndDefs

set_option autoImplicit false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable (Y : Set (Fin 2 → ℝ))

/-- The **domain** of the partial function described by the graph `Y ⊆ ℝ²` (a point `x` with at
least one `y` such that `(x, y) ∈ Y`). -/
def MonoDom : Set ℝ := {x : ℝ | ∃ y : ℝ, ![x, y] ∈ Y}

/-- The set of points at which `Y` is **locally constant**: there are `y` and `ε > 0` with
`(x, y) ∈ Y` and `(z, y) ∈ Y` for every `z ∈ (x - ε, x + ε)`. -/
def MonoW : Set ℝ :=
  {x : ℝ | ∃ y ε : ℝ, 0 < ε ∧ ![x, y] ∈ Y ∧
    ∀ z : ℝ, x - ε < z → z < x + ε → ![z, y] ∈ Y}

/-- Points whose **left germ** lies strictly below the value: for some `ε > 0` and some value `y`
at `a`, every point `z ∈ (a - ε, a)` that lies in the domain has value `< y`. -/
def MonoLm : Set ℝ :=
  {a : ℝ | ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a - ε < z → z < a → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y' < y}

/-- Points whose **left germ** lies strictly above the value. -/
def MonoHm : Set ℝ :=
  {a : ℝ | ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a - ε < z → z < a → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y < y'}

/-- Points whose **right germ** lies strictly below the value. -/
def MonoLp : Set ℝ :=
  {a : ℝ | ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a < z → z < a + ε → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y' < y}

/-- Points whose **right germ** lies strictly above the value. -/
def MonoHp : Set ℝ :=
  {a : ℝ | ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a < z → z < a + ε → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y < y'}

/-- The relation `{(x, w) : f x < f w}` attached to the partial function `Y`.  The fibre at `w`
is the set `{x : f x < f w}`, which is what the germ analysis needs. -/
def MonoLA : Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![v 1, y'] ∈ Y ∧ y < y'}

/-- The relation `{(x, w) : f x > f w}` attached to the partial function `Y`. -/
def MonoHA : Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![v 1, y'] ∈ Y ∧ y' < y}

/-- The fibre of `MonoLA` over `a`, i.e. the set of `x` with value below the value at `a`. -/
def MonoLfib (a : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ MonoLA Y}

/-- The fibre of `MonoHA` over `a`, i.e. the set of `x` with value above the value at `a`. -/
def MonoHfib (a : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ MonoHA Y}

/-- The set of points whose value is below the value at `a` (the "decoded" fibre of `MonoLA`). -/
def MonoLset (a : ℝ) : Set ℝ :=
  {x : ℝ | ∃ y y' : ℝ, ![x, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y < y'}

/-- The set of points whose value is above the value at `a` (the "decoded" fibre of `MonoHA`). -/
def MonoHset (a : ℝ) : Set ℝ :=
  {x : ℝ | ∃ y y' : ℝ, ![x, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y' < y}

/-- `Y` describes a nondecreasing partial function on the open interval `(a, b)`: any two points
of `(a, b)` carrying `Y`-values have them in the same order. -/
def MonoIncOn (a b : ℝ) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : ℝ, a < x₁ → x₁ < x₂ → x₂ < b → ![x₁, y₁] ∈ Y → ![x₂, y₂] ∈ Y → y₁ ≤ y₂

/-- `Y` describes a nonincreasing partial function on the open interval `(a, b)`. -/
def MonoDecOn (a b : ℝ) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : ℝ, a < x₁ → x₁ < x₂ → x₂ < b → ![x₁, y₁] ∈ Y → ![x₂, y₂] ∈ Y → y₂ ≤ y₁

/-- The **exceptional set** of the monotonicity theorem: the topological boundaries (in the sense
of `Work.WilC2.IsBnd`) of the domain, of the locally constant locus, and of the four one-sided
germ types. -/
def MonoBnd : Set ℝ :=
  {x : ℝ | WilC2.IsBnd (MonoDom Y) x} ∪ {x : ℝ | WilC2.IsBnd (MonoW Y) x} ∪
    {x : ℝ | WilC2.IsBnd (MonoLm Y) x} ∪ {x : ℝ | WilC2.IsBnd (MonoHm Y) x} ∪
    {x : ℝ | WilC2.IsBnd (MonoLp Y) x} ∪ {x : ℝ | WilC2.IsBnd (MonoHp Y) x}

/-! ## Unfolding lemmas -/

@[simp] lemma mem_MonoDom {x : ℝ} : x ∈ MonoDom Y ↔ ∃ y : ℝ, ![x, y] ∈ Y := Iff.rfl

@[simp] lemma mem_MonoW {x : ℝ} : x ∈ MonoW Y ↔ ∃ y ε : ℝ, 0 < ε ∧ ![x, y] ∈ Y ∧
    ∀ z : ℝ, x - ε < z → z < x + ε → ![z, y] ∈ Y := Iff.rfl

@[simp] lemma mem_MonoLm {a : ℝ} : a ∈ MonoLm Y ↔ ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a - ε < z → z < a → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y' < y := Iff.rfl

@[simp] lemma mem_MonoHm {a : ℝ} : a ∈ MonoHm Y ↔ ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a - ε < z → z < a → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y < y' := Iff.rfl

@[simp] lemma mem_MonoLp {a : ℝ} : a ∈ MonoLp Y ↔ ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a < z → z < a + ε → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y' < y := Iff.rfl

@[simp] lemma mem_MonoHp {a : ℝ} : a ∈ MonoHp Y ↔ ∃ ε y : ℝ, 0 < ε ∧ ![a, y] ∈ Y ∧
    ∀ z : ℝ, a < z → z < a + ε → ∃ y' : ℝ, ![z, y'] ∈ Y ∧ y < y' := Iff.rfl

lemma mem_MonoLfib {a : ℝ} {v : Fin 1 → ℝ} :
    v ∈ MonoLfib Y a ↔ ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y < y' := Iff.rfl

lemma mem_MonoHfib {a : ℝ} {v : Fin 1 → ℝ} :
    v ∈ MonoHfib Y a ↔ ∃ y y' : ℝ, ![v 0, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y' < y := Iff.rfl

@[simp] lemma mem_MonoLset {a x : ℝ} :
    x ∈ MonoLset Y a ↔ ∃ y y' : ℝ, ![x, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y < y' := Iff.rfl

@[simp] lemma mem_MonoHset {a x : ℝ} :
    x ∈ MonoHset Y a ↔ ∃ y y' : ℝ, ![x, y] ∈ Y ∧ ![a, y'] ∈ Y ∧ y' < y := Iff.rfl

lemma mem_MonoIncOn {a b : ℝ} :
    MonoIncOn Y a b ↔ ∀ x₁ x₂ y₁ y₂ : ℝ, a < x₁ → x₁ < x₂ → x₂ < b →
      ![x₁, y₁] ∈ Y → ![x₂, y₂] ∈ Y → y₁ ≤ y₂ := Iff.rfl

lemma mem_MonoDecOn {a b : ℝ} :
    MonoDecOn Y a b ↔ ∀ x₁ x₂ y₁ y₂ : ℝ, a < x₁ → x₁ < x₂ → x₂ < b →
      ![x₁, y₁] ∈ Y → ![x₂, y₂] ∈ Y → y₂ ≤ y₁ := Iff.rfl

/-! ## Membership in the exceptional set

`MonoBnd Y` is the union of the six boundary sets, so each of the six `IsBnd` predicates implies
membership and conversely. -/

lemma isBnd_dom_mem_MonoBnd {x : ℝ} (h : WilC2.IsBnd (MonoDom Y) x) : x ∈ MonoBnd Y := by
  simp only [MonoBnd, Set.mem_union, Set.mem_setOf_eq]
  tauto

lemma isBnd_W_mem_MonoBnd {x : ℝ} (h : WilC2.IsBnd (MonoW Y) x) : x ∈ MonoBnd Y := by
  simp only [MonoBnd, Set.mem_union, Set.mem_setOf_eq]
  tauto

lemma isBnd_Lm_mem_MonoBnd {x : ℝ} (h : WilC2.IsBnd (MonoLm Y) x) : x ∈ MonoBnd Y := by
  simp only [MonoBnd, Set.mem_union, Set.mem_setOf_eq]
  tauto

lemma isBnd_Hm_mem_MonoBnd {x : ℝ} (h : WilC2.IsBnd (MonoHm Y) x) : x ∈ MonoBnd Y := by
  simp only [MonoBnd, Set.mem_union, Set.mem_setOf_eq]
  tauto

lemma isBnd_Lp_mem_MonoBnd {x : ℝ} (h : WilC2.IsBnd (MonoLp Y) x) : x ∈ MonoBnd Y := by
  simp only [MonoBnd, Set.mem_union, Set.mem_setOf_eq]
  tauto

lemma isBnd_Hp_mem_MonoBnd {x : ℝ} (h : WilC2.IsBnd (MonoHp Y) x) : x ∈ MonoBnd Y := by
  simp only [MonoBnd, Set.mem_union, Set.mem_setOf_eq]
  tauto

end Work.WilC4
