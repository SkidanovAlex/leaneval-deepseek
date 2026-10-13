/-
  WilC4/ParamMonoDefs : the vocabulary of the *parametric* o-minimal monotonicity theorem
  (`Work.WilC4.ulpm_mono_param`).

  `mono_real` treats a single `∅`-definable partial function `Y ⊆ ℝ²`.  Here `Y ⊆ ℝ^{n+2}` is a
  `∅`-definable *family* of partial functions, indexed by `c : Fin n → ℝ`: the fibre over `c` is
  `Pfibre Y c = {(x, y) : (x, y, c) ∈ Y}` (with `x` the first coordinate and `y` the second).

  The target statement produces a `∅`-definable family of exception sets `B ⊆ ℝ^{n+1}`, whose
  fibres are uniformly finite, such that every fibre function is monotone on every interval
  avoiding the corresponding exception set.  The candidate is `PBnd Y`: the parametric version of
  `MonoBnd (Pfibre Y c)`, i.e. the union of the topological boundaries of the parametric domain
  `PDom`, of the locally-constant locus `PW`, and of the four one-sided germ loci
  `PLm, PHm, PLp, PHp`.

  The one non-elementary fact is that `PBnd Y` is `∅`-definable; it is assembled by colleagues
  from the four lemmas
  `paramDom_definable`, `paramW_definable`, `paramGerms_definable`, `paramBnd_definable`.
-/
import Mathlib
import Submission.Work.WilC4.monoDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {n : ℕ}

/-! ## 1. The parametric vocabulary -/

/-- The graph of the partial function obtained from the family `Y ⊆ ℝ^{n+2}` at the parameter
`c : Fin n → ℝ` (the first coordinate of `Y` is the argument, the second the value). -/
def Pfibre (Y : Set (Fin (n + 2) → ℝ)) (c : Fin n → ℝ) : Set (Fin 2 → ℝ) :=
  {v | Fin.cons (v 0) (Fin.cons (v 1) c) ∈ Y}

/-- The fibre of a parametric set `S ⊆ ℝ^{n+1}` at the parameter encoded by `Fin.tail p`
(`p 0` is the argument of the fibre). -/
def Pfib1 (S : Set (Fin (n + 1) → ℝ)) (p : Fin (n + 1) → ℝ) : Set ℝ :=
  {x | Fin.cons x (Fin.tail p) ∈ S}

/-- Parametric domain: `p ∈ PDom Y` iff the fibre function at `Fin.tail p` is defined at `p 0`. -/
def PDom (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ y : ℝ, Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y}

/-- Parametric locally constant locus. -/
def PW (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ y ε : ℝ, 0 < ε ∧ Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
    ∀ z : ℝ, p 0 - ε < z → z < p 0 + ε → Fin.cons z (Fin.cons y (Fin.tail p)) ∈ Y}

/-- Parametric left germ strictly below the value. -/
def PLm (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ ε y : ℝ, 0 < ε ∧ Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
    ∀ z : ℝ, p 0 - ε < z → z < p 0 →
      ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y' < y}

/-- Parametric left germ strictly above the value. -/
def PHm (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ ε y : ℝ, 0 < ε ∧ Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
    ∀ z : ℝ, p 0 - ε < z → z < p 0 →
      ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y < y'}

/-- Parametric right germ strictly below the value. -/
def PLp (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ ε y : ℝ, 0 < ε ∧ Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
    ∀ z : ℝ, p 0 < z → z < p 0 + ε →
      ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y' < y}

/-- Parametric right germ strictly above the value. -/
def PHp (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | ∃ ε y : ℝ, 0 < ε ∧ Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y ∧
    ∀ z : ℝ, p 0 < z → z < p 0 + ε →
      ∃ y' : ℝ, Fin.cons z (Fin.cons y' (Fin.tail p)) ∈ Y ∧ y < y'}

/-- The parametric exceptional set: the union of the boundaries of the six parametric loci. -/
def PBnd (Y : Set (Fin (n + 2) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | WilC2.IsBnd (Pfib1 (PDom Y) p) (p 0)} ∪
  {p | WilC2.IsBnd (Pfib1 (PW Y) p) (p 0)} ∪
  {p | WilC2.IsBnd (Pfib1 (PLm Y) p) (p 0)} ∪
  {p | WilC2.IsBnd (Pfib1 (PHm Y) p) (p 0)} ∪
  {p | WilC2.IsBnd (Pfib1 (PLp Y) p) (p 0)} ∪
  {p | WilC2.IsBnd (Pfib1 (PHp Y) p) (p 0)}

/-! ## 2. The fibre identifications

`PBnd Y` really is the family `c ↦ MonoBnd (Pfibre Y c)`. -/

lemma Pfib1_cons (S : Set (Fin (n + 1) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 S (Fin.cons x c) = {z : ℝ | Fin.cons z c ∈ S} := by
  ext z
  simp [Pfib1]

lemma Pfib1_Dom (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 (PDom Y) (Fin.cons x c) = MonoDom (Pfibre Y c) := by
  ext z; simp [Pfib1, PDom, MonoDom, Pfibre]

lemma Pfib1_W (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 (PW Y) (Fin.cons x c) = MonoW (Pfibre Y c) := by
  ext z; simp [Pfib1, PW, MonoW, Pfibre]

lemma Pfib1_Lm (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 (PLm Y) (Fin.cons x c) = MonoLm (Pfibre Y c) := by
  ext z; simp [Pfib1, PLm, MonoLm, Pfibre]

lemma Pfib1_Hm (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 (PHm Y) (Fin.cons x c) = MonoHm (Pfibre Y c) := by
  ext z; simp [Pfib1, PHm, MonoHm, Pfibre]

lemma Pfib1_Lp (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 (PLp Y) (Fin.cons x c) = MonoLp (Pfibre Y c) := by
  ext z; simp [Pfib1, PLp, MonoLp, Pfibre]

lemma Pfib1_Hp (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Pfib1 (PHp Y) (Fin.cons x c) = MonoHp (Pfibre Y c) := by
  ext z; simp [Pfib1, PHp, MonoHp, Pfibre]

lemma mem_PBnd_iff (Y : Set (Fin (n + 2) → ℝ)) (x : ℝ) (c : Fin n → ℝ) :
    Fin.cons x c ∈ PBnd Y ↔ x ∈ MonoBnd (Pfibre Y c) := by
  simp only [PBnd, MonoBnd, Set.mem_union, Set.mem_setOf_eq, Fin.cons_zero,
    Pfib1_Dom, Pfib1_W, Pfib1_Lm, Pfib1_Hm, Pfib1_Lp, Pfib1_Hp]

variable {Y : Set (Fin (n + 2) → ℝ)}

/-- The fibre relations are functional when the family is. -/
lemma Pfibre_fun
    (hfun : ∀ (c : Fin n → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y') (c : Fin n → ℝ) :
    ∀ x y y' : ℝ, ![x, y] ∈ Pfibre Y c → ![x, y'] ∈ Pfibre Y c → y = y' := by
  intro x y y' hy hy'
  exact hfun c x y y' (by simpa [Pfibre] using hy) (by simpa [Pfibre] using hy')

/-! ## 3. The extended relation

Membership of `(argument, value, parameters)` in `Y` is encoded by a single relation `PExt Y`
on the index type `Fin (n+1) ⊕ Fin 1` (the first summand is the "row" `p`, the second the value).
`PExt_apply` is the only thing one ever needs about it. -/

/-- The index map `Fin (n+2) → Fin (n+1) ⊕ Fin 1` sending `0 ↦ (0, ·)`, `1 ↦ (·, 0)` and
`j+2 ↦ (j+1, ·)`. -/
def Pτ (n : ℕ) : Fin (n + 2) → Fin (n + 1) ⊕ Fin 1 :=
  Fin.cons (Sum.inl 0) (Fin.cons (Sum.inr 0) (fun j : Fin n => Sum.inl (Fin.succ j)))

/-- `(argument, value, parameters) ∈ Y`, indexed by `Fin (n+1) ⊕ Fin 1`. -/
def PExt (Y : Set (Fin (n + 2) → ℝ)) : Set ((Fin (n + 1) ⊕ Fin 1) → ℝ) :=
  (fun w : (Fin (n + 1) ⊕ Fin 1) → ℝ => w ∘ Pτ n) ⁻¹' Y

lemma PExt_apply (p : Fin (n + 1) → ℝ) (y : ℝ) :
    Sum.elim p (fun _ : Fin 1 => y) ∈ PExt Y ↔
      Fin.cons (p 0) (Fin.cons y (Fin.tail p)) ∈ Y := by
  have h : (Sum.elim p (fun _ : Fin 1 => y)) ∘ Pτ n =
      Fin.cons (p 0) (Fin.cons y (Fin.tail p)) := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      induction j using Fin.cases with
      | zero => rfl
      | succ k => rfl
  rw [PExt, Set.mem_preimage, h]

/-! ## 4. `∅`-definable coordinates

Because `LRc` names every real, the coordinate functions are `∅`-definable: the constant term of
the language evaluates to the required real by `rfl`. -/

theorem empty_definable_coord_eq {α : Type} (i : α) (r : ℝ) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc {v : α → ℝ | v i = r} := by
  rw [Set.empty_definable_iff]
  refine ⟨(Term.var i).equal (FirstOrder.Language.Constants.term (LR.con r)), ?_⟩
  ext v
  show (v i = r) ↔ (v i = ((LR.con r : LRc.Constants) : ℝ))
  rw [show ((LR.con r : LRc.Constants) : ℝ) = r from rfl]

end Work.WilC4
