/-
  Area C2 (WilC2): the *definability of the constancy set* of a definable relation.

  If `P` is a `T`-definable relation on `M`, then the set of `y` such that
  * some `x` satisfies `P y x`, and
  * there is `ε > 0` with `P y x → P z x` for every `z ∈ (y - ε, y + ε)`
  is again `T`-definable.  The statement is purely syntactic: the witnessing formula is built
  from the formula defining `P` together with the ring formulas for the order.

  `≤` is not a symbol of `LRc`, but the hypothesis `hsq` ("every nonnegative element is a
  square") makes `x ≤ y ↔ ∃ z, x + z * z = y` (`leF`) correct in every model, so all order
  comparisons — including the ones with the compound terms `y - ε` and `y + ε` — are expressible
  by ring formulas.
-/
import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.SelectDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-! ## 1. The arithmetic lemmas -/

/-- In a linearly ordered field in which every nonnegative element is a square,
`∃ z, a + z * z = b` is exactly `a ≤ b`. -/
theorem exists_add_sq_eq_iff_le {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (a b : M) :
    (∃ z : M, a + z * z = b) ↔ a ≤ b := by
  constructor
  · rintro ⟨z, hz⟩
    nlinarith [mul_self_nonneg z]
  · intro h
    obtain ⟨z, hz⟩ := hsq (b - a) (by linarith)
    exact ⟨z, by linarith⟩

/-- In a linearly ordered field in which every nonnegative element is a square,
`∃ z, z * z = a` is exactly `0 ≤ a`. -/
theorem exists_sq_eq_iff_nonneg {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (a : M) :
    (∃ z : M, z * z = a) ↔ 0 ≤ a := by
  constructor
  · rintro ⟨z, rfl⟩
    exact mul_self_nonneg z
  · intro h
    obtain ⟨z, hz⟩ := hsq a h
    exact ⟨z, hz.symm⟩

/-! ## 2. Ring formulas involving the compound terms `y - ε` and `y + ε` -/

/-- `x 0 - x 1 < x 2`, as a ring formula, i.e. `¬ ∃ z, x 2 + z * z = x 0 + (-x 1)`. -/
def ltSubF : Language.ring.Formula (Fin 3) :=
  ∼((Term.bdEqual
      (Term.var (Sum.inl (2 : Fin 3)) +
        Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
      (Term.var (Sum.inl (0 : Fin 3)) + -Term.var (Sum.inl (1 : Fin 3)))).ex)

/-- `x 2 < x 0 + x 1`, as a ring formula, i.e. `¬ ∃ z, (x 0 + x 1) + z * z = x 2`. -/
def ltAddF : Language.ring.Formula (Fin 3) :=
  ∼((Term.bdEqual
      (Term.var (Sum.inl (0 : Fin 3)) + Term.var (Sum.inl (1 : Fin 3)) +
        Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
      (Term.var (Sum.inl (2 : Fin 3)))).ex)

/-- `x 0 ≤ 0`, as a ring formula, i.e. `∃ z, x 0 + z * z = 0`. -/
def leZeroF : Language.ring.Formula (Fin 1) :=
  (Term.bdEqual
    (Term.var (Sum.inl (0 : Fin 1)) +
      Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
    (0 : Language.ring.Term (Fin 1 ⊕ Fin 1))).ex

/-- `0 < x 0`, as a ring formula: `x 0` is a square and `¬ x 0 ≤ 0`. -/
def posF : Language.ring.Formula (Fin 1) := sqF ⊓ ∼leZeroF

theorem ltSubF_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin 3 → M) :
    ltSubF.Realize v ↔ v 0 - v 1 < v 2 := by
  rw [ltSubF, Formula.Realize, BoundedFormula.realize_not, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul,
    Ring.realize_neg, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  rw [← not_le, sub_eq_add_neg]
  exact not_iff_not.mpr (exists_add_sq_eq_iff_le hsq (v 2) (v 0 + -v 1))

theorem ltAddF_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin 3 → M) :
    ltAddF.Realize v ↔ v 2 < v 0 + v 1 := by
  rw [ltAddF, Formula.Realize, BoundedFormula.realize_not, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  rw [← not_le]
  exact not_iff_not.mpr (exists_add_sq_eq_iff_le hsq (v 0 + v 1) (v 2))

theorem leZeroF_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin 1 → M) :
    leZeroF.Realize v ↔ v 0 ≤ 0 := by
  rw [leZeroF, Formula.Realize, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul,
    Ring.realize_zero, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact exists_add_sq_eq_iff_le hsq (v 0) 0

theorem posF_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (v : Fin 1 → M) :
    posF.Realize v ↔ 0 < v 0 := by
  rw [posF, Formula.realize_inf, Formula.realize_not, sqF_realize,
    exists_sq_eq_iff_nonneg hsq, leZeroF_realize hsq]
  exact lt_iff_le_not_ge.symm

/-! ## 3. The same atoms in `LRc`, in an arbitrary context -/

/-- `a - b < c` in the language `LRc`. -/
def ltSubA {C : Type*} (a b c : C) : LRc.Formula C := liftR ![a, b, c] ltSubF

/-- `c < a + b` in the language `LRc`. -/
def ltAddA {C : Type*} (a b c : C) : LRc.Formula C := liftR ![a, b, c] ltAddF

/-- `0 < a` in the language `LRc`. -/
def posA {C : Type*} (a : C) : LRc.Formula C := liftR (fun _ : Fin 1 => a) posF

theorem ltSubA_realize {C : Type*} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (w : C → M) (a b c : C) : (ltSubA a b c).Realize w ↔ w a - w b < w c := by
  rw [ltSubA, liftR_realize]
  have h : w ∘ ![a, b, c] = ![w a, w b, w c] := by
    funext i; fin_cases i <;> rfl
  rw [h, ltSubF_realize hsq]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem ltAddA_realize {C : Type*} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (w : C → M) (a b c : C) : (ltAddA a b c).Realize w ↔ w c < w a + w b := by
  rw [ltAddA, liftR_realize]
  have h : w ∘ ![a, b, c] = ![w a, w b, w c] := by
    funext i; fin_cases i <;> rfl
  rw [h, ltAddF_realize hsq]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem posA_realize {C : Type*} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (w : C → M) (a : C) : (posA a).Realize w ↔ 0 < w a := by
  rw [posA, liftR_realize]
  have h : w ∘ (fun _ : Fin 1 => a) = fun _ : Fin 1 => w a := rfl
  rw [h, posF_realize hsq]

/-! ## 4. The atoms inside `LRc[[T]]` -/

/-- The `LRc`-formula `F`, viewed in the richer language `LRc[[T]]` in which the parameters
`T` are named by constants. -/
def upT {T : Set M} {α : Type*} (F : LRc.Formula α) : LRc[[T]].Formula α :=
  (LRc.lhomWithConstants T).onFormula F

theorem upT_realize {T : Set M} {α : Type*} (F : LRc.Formula α) (v : α → M) :
    (upT (T := T) F).Realize v ↔ F.Realize v :=
  LHom.realize_onFormula (LRc.lhomWithConstants T) F (v := v)

/-- `a - b < c` in the language `LRc[[T]]`. -/
def ltSubAT {T : Set M} {C : Type*} (a b c : C) : LRc[[T]].Formula C := upT (ltSubA a b c)

/-- `c < a + b` in the language `LRc[[T]]`. -/
def ltAddAT {T : Set M} {C : Type*} (a b c : C) : LRc[[T]].Formula C := upT (ltAddA a b c)

/-- `0 < a` in the language `LRc[[T]]`. -/
def posAT {T : Set M} {C : Type*} (a : C) : LRc[[T]].Formula C := upT (posA a)

theorem ltSubAT_realize {T : Set M} {C : Type*}
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (a b c : C) :
    (ltSubAT (T := T) a b c).Realize w ↔ w a - w b < w c := by
  rw [ltSubAT, upT_realize]
  exact ltSubA_realize hsq w a b c

theorem ltAddAT_realize {T : Set M} {C : Type*}
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (a b c : C) :
    (ltAddAT (T := T) a b c).Realize w ↔ w c < w a + w b := by
  rw [ltAddAT, upT_realize]
  exact ltAddA_realize hsq w a b c

theorem posAT_realize {T : Set M} {C : Type*}
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (a : C) :
    (posAT (T := T) a).Realize w ↔ 0 < w a := by
  rw [posAT, upT_realize]
  exact posA_realize hsq w a

/-! ## 5. The witnessing formula -/

/-- The context `(y, x)` of the first conjunct, resp. `(y, ε)` of the second. -/
abbrev ctxA : Type := Fin 1 ⊕ Fin 1
/-- The context `(y, ε, z)`. -/
abbrev ctxB : Type := ctxA ⊕ Fin 1
/-- The context `(y, ε, z, x)`. -/
abbrev ctxC : Type := ctxB ⊕ Fin 1

/-- The distinguished point `y`. -/
abbrev xA : ctxA := Sum.inl 0
/-- The second slot: the witness of the first conjunct / the `ε` of the second. -/
abbrev wA : ctxA := Sum.inr 0
abbrev xB : ctxB := Sum.inl xA
abbrev eB : ctxB := Sum.inl wA
abbrev zB : ctxB := Sum.inr 0
abbrev xC : ctxC := Sum.inl xB
abbrev zC : ctxC := Sum.inl zB
abbrev yC : ctxC := Sum.inr 0

/-- The body of the first conjunct: `P y x`. -/
def cfBody1 {T : Set M} (φ : LRc[[T]].Formula (Fin 2)) : LRc[[T]].Formula ctxA :=
  Formula.relabel ![xA, wA] φ

/-- The innermost implication: `P y x → P z x`. -/
def cfBody3 {T : Set M} (φ : LRc[[T]].Formula (Fin 2)) : LRc[[T]].Formula ctxC :=
  Formula.relabel ![xC, yC] φ ⟹ Formula.relabel ![zC, yC] φ

/-- `(y - ε < z) → (z < y + ε) → (∀ x, P y x → P z x)`. -/
def cfBody2 {T : Set M} (φ : LRc[[T]].Formula (Fin 2)) : LRc[[T]].Formula ctxB :=
  ltSubAT xB eB zB ⟹ (ltAddAT xB eB zB ⟹ Formula.iAlls (Fin 1) (cfBody3 φ))

/-- `0 < ε ∧ ∀ z, (y - ε < z) → (z < y + ε) → (∀ x, P y x → P z x)`. -/
def cfBody {T : Set M} (φ : LRc[[T]].Formula (Fin 2)) : LRc[[T]].Formula ctxA :=
  posAT wA ⊓ Formula.iAlls (Fin 1) (cfBody2 φ)

/-- **The witnessing formula** for the constancy set of `φ`. -/
def constancyForm {T : Set M} (φ : LRc[[T]].Formula (Fin 2)) :
    LRc[[T]].Formula (Fin 1) :=
  Formula.iExs (Fin 1) (cfBody1 φ) ⊓ Formula.iExs (Fin 1) (cfBody φ)

/-! ## 6. Realisability of the pieces -/

theorem cfBody1_realize {T : Set M} {P : M → M → Prop}
    (φ : LRc[[T]].Formula (Fin 2))
    (hφ : ∀ w : Fin 2 → M, φ.Realize w ↔ P (w 0) (w 1)) (w : ctxA → M) :
    (cfBody1 φ).Realize w ↔ P (w xA) (w wA) := by
  rw [cfBody1, Formula.realize_relabel]
  have h : w ∘ ![xA, wA] = ![w xA, w wA] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  exact hφ ![w xA, w wA]

theorem cfBody3_realize {T : Set M} {P : M → M → Prop}
    (φ : LRc[[T]].Formula (Fin 2))
    (hφ : ∀ w : Fin 2 → M, φ.Realize w ↔ P (w 0) (w 1)) (w : ctxC → M) :
    (cfBody3 φ).Realize w ↔ (P (w xC) (w yC) → P (w zC) (w yC)) := by
  rw [cfBody3, Formula.realize_imp, Formula.realize_relabel, Formula.realize_relabel]
  have h1 : w ∘ ![xC, yC] = ![w xC, w yC] := by
    funext i; fin_cases i <;> rfl
  have h2 : w ∘ ![zC, yC] = ![w zC, w yC] := by
    funext i; fin_cases i <;> rfl
  rw [h1, h2, hφ, hφ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem cfBody2_realize {T : Set M} {P : M → M → Prop}
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : LRc[[T]].Formula (Fin 2))
    (hφ : ∀ w : Fin 2 → M, φ.Realize w ↔ P (w 0) (w 1)) (w : ctxB → M) :
    (cfBody2 φ).Realize w ↔
      (w xB - w eB < w zB →
        (w zB < w xB + w eB → ∀ i : Fin 1 → M, P (w xB) (i 0) → P (w zB) (i 0))) := by
  rw [cfBody2, Formula.realize_imp, Formula.realize_imp, ltSubAT_realize hsq,
    ltAddAT_realize hsq, Formula.realize_iAlls]
  constructor
  · intro h h1 h2 i
    have h3 := h h1 h2 i
    rw [cfBody3_realize φ hφ] at h3
    simp only [Sum.elim_inl, Sum.elim_inr] at h3
    exact h3
  · intro h h1 h2 i
    rw [cfBody3_realize φ hφ]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact h h1 h2 i

theorem cfBody_realize {T : Set M} {P : M → M → Prop}
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : LRc[[T]].Formula (Fin 2))
    (hφ : ∀ w : Fin 2 → M, φ.Realize w ↔ P (w 0) (w 1)) (w : ctxA → M) :
    (cfBody φ).Realize w ↔
      (0 < w wA ∧ ∀ i : Fin 1 → M, (w xA - w wA < i 0 →
        (i 0 < w xA + w wA → ∀ j : Fin 1 → M, P (w xA) (j 0) → P (i 0) (j 0)))) := by
  rw [cfBody, Formula.realize_inf, posAT_realize hsq, Formula.realize_iAlls]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi1 hi2 j hj => ?_⟩
    have h3 := h2 i
    rw [cfBody2_realize hsq φ hφ] at h3
    simp only [Sum.elim_inl, Sum.elim_inr] at h3
    exact h3 hi1 hi2 j hj
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    rw [cfBody2_realize hsq φ hφ]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact h2 i

theorem constancyForm_realize {T : Set M} {P : M → M → Prop}
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : LRc[[T]].Formula (Fin 2))
    (hφ : ∀ w : Fin 2 → M, φ.Realize w ↔ P (w 0) (w 1)) (v : Fin 1 → M) :
    (constancyForm φ).Realize v ↔
      (∃ y : M, P (v 0) y) ∧
      (∃ ε : M, 0 < ε ∧ ∀ z : M, v 0 - ε < z → z < v 0 + ε →
        ∀ y : M, P (v 0) y → P z y) := by
  rw [constancyForm, Formula.realize_inf, Formula.realize_iExs, Formula.realize_iExs]
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨e, he⟩⟩
    rw [cfBody1_realize φ hφ] at hu
    simp only [Sum.elim_inl, Sum.elim_inr] at hu
    rw [cfBody_realize hsq φ hφ] at he
    simp only [Sum.elim_inl, Sum.elim_inr] at he
    exact ⟨⟨u 0, hu⟩, e 0, he.1, fun z hz1 hz2 y hy => he.2 (fun _ => z) hz1 hz2 (fun _ => y) hy⟩
  · rintro ⟨⟨y, hy⟩, ⟨ε, hε1, hε2⟩⟩
    refine ⟨⟨fun _ => y, ?_⟩, ⟨fun _ => ε, ?_⟩⟩
    · rw [cfBody1_realize φ hφ]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact hy
    · rw [cfBody_realize hsq φ hφ]
      refine ⟨hε1, fun i hi1 hi2 j hj => ?_⟩
      exact hε2 (i 0) hi1 hi2 (j 0) hj

/-! ## 7. The main statement -/

/-- The set of "locally constant points" of a `T`-definable relation is `T`-definable: if
`P : M → M → Prop` is `T`-definable, then so is the set of `y` such that
* `P y ·` is nonempty, and
* for some `ε > 0`, every `z ∈ (y - ε, y + ε)` with `P y x` also satisfies `P z x`.

This is a pure syntactic statement about `Set.Definable`: the witnessing `LRc`-formula is built
from the formula defining `P` together with the order, which is `LRc`-definable here because the
component structure hypotheses give `ringToLRc.IsExpansionOn M` and `hsq` makes `leF` correct. -/
theorem definable_constancy_set2 {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    {T : Set M} {P : M → M → Prop}
    (hP : T.Definable WilkiesDesign.CG.LRc {v : Fin 2 → M | P (v 0) (v 1)}) :
    T.Definable WilkiesDesign.CG.LRc {v : Fin 1 → M |
      (∃ y : M, P (v 0) y) ∧
      (∃ ε : M, 0 < ε ∧ ∀ z : M, v 0 - ε < z → z < v 0 + ε → ∀ y : M, P (v 0) y → P z y)} := by
  obtain ⟨φ, hφ⟩ := hP
  have hφ' : ∀ w : Fin 2 → M, φ.Realize w ↔ P (w 0) (w 1) := by
    intro w
    have h : w ∈ ({v : Fin 2 → M | P (v 0) (v 1)} : Set (Fin 2 → M)) ↔
        w ∈ Set.ofPred φ.Realize := by rw [hφ]
    simpa using h.symm
  refine ⟨constancyForm φ, ?_⟩
  ext v
  rw [Set.mem_ofPred_eq]
  exact (constancyForm_realize hsq φ hφ' v).symm

end Work.WilC2
