/-
  Area C2 (WilC2): the *syntactic* side of the definable choice on a fibre.

  `ChoiceCond φ v y` (module `Submission.Work.WilC2.ChoiceDefs`) is the semantic condition
  selecting the point of the leftmost component of the fibre of `φ` at `v` whose rescaling is
  the midpoint of the rescaled leftmost component.  This file builds a parametric `LRc`-formula
  `selectForm φ` realising it, i.e.

    `(selectForm φ).Realize (Sum.elim v (fun _ => y)) ↔ ChoiceCond φ v y`

  in every ordered field model `M` of the right kind in which every nonnegative element is a
  square (the theorem `selectForm_exists` in `Submission.Work.WilC2.selectForm_exists`).

  The relation `≤` is `leF` (`∃ z, x + z*z = y`), so that its realizability is the honest order
  of `M` (given that squares are the nonnegative elements); `0 ≤ y` is written as "`y` is a
  square", which avoids any constant symbol.

  The fibre atoms are `φ` relabelled at the appropriate variable (`fibA`), the rescaling
  relation `RescaleRel` is `rrA`, membership in the leftmost component `LeftComp` is `lcA`, and
  the infimum/supremum conditions `IsInfTZ`/`IsSupTZ` are `infA`/`supA`.  Note that the
  quantifier over the rescaled leftmost component `TZset` is kept in the form
  `∀ y t, y ∈ LeftComp → RescaleRel y t → ...`, which is equivalent to `∀ t ∈ TZset, ...`
  (moving the existential out of the antecedent of an implication, `forall_TZ`).
-/
import Mathlib
import Submission.Work.WilC2.ChoiceDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

variable {n : ℕ}

/-! ## 1. Ring atoms -/

/-- `sqF y` is `∃ z, z * z = y`. -/
def sqF : Language.ring.Formula (Fin 1) :=
  (Term.bdEqual (Term.var (Sum.inr 0) * Term.var (Sum.inr 0)) (Term.var (Sum.inl 0))).ex

/-- `lin₁F t y` is `t + t * y = y` (`t * (1 + y) = y` in a commutative ring). -/
def lin₁F : Language.ring.Formula (Fin 2) :=
  Term.bdEqual (Term.var (Sum.inl 0) + Term.var (Sum.inl 0) * Term.var (Sum.inl 1))
    (Term.var (Sum.inl 1))

/-- `lin₂F t y` is `t - t * y = y` (`t * (1 - y) = y` in a commutative ring). -/
def lin₂F : Language.ring.Formula (Fin 2) :=
  Term.bdEqual (Term.var (Sum.inl 0) + -(Term.var (Sum.inl 0) * Term.var (Sum.inl 1)))
    (Term.var (Sum.inl 1))

/-- `midF t m s` is `t + t = m + s`. -/
def midF : Language.ring.Formula (Fin 3) :=
  Term.bdEqual (Term.var (Sum.inl 0) + Term.var (Sum.inl 0))
    (Term.var (Sum.inl 1) + Term.var (Sum.inl 2))

theorem sqF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : Fin 1 → M) :
    sqF.Realize v ↔ ∃ z : M, z * z = v 0 := by
  rw [sqF, Formula.Realize, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_mul, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr]

theorem lin₁F_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : Fin 2 → M) :
    lin₁F.Realize v ↔ v 0 + v 0 * v 1 = v 1 := by
  rw [lin₁F, Formula.Realize]
  simp only [BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul, Term.realize_var,
    Sum.elim_inl]

theorem lin₂F_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : Fin 2 → M) :
    lin₂F.Realize v ↔ v 0 - v 0 * v 1 = v 1 := by
  rw [lin₂F, Formula.Realize]
  simp only [BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul, Ring.realize_neg,
    Term.realize_var, Sum.elim_inl, sub_eq_add_neg]

theorem midF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : Fin 3 → M) :
    midF.Realize v ↔ v 0 + v 0 = v 1 + v 2 := by
  rw [midF, Formula.Realize]
  simp only [BoundedFormula.realize_bdEqual, Ring.realize_add, Term.realize_var, Sum.elim_inl]

/-! ## 2. The `LRc`-atoms attached to variables of a context -/

/-- `a ≤ b`, as an `LRc`-formula in the context `C`. -/
def leA {C : Type*} (a b : C) : LRc.Formula C := liftR ![a, b] leF

/-- `a < b`, as an `LRc`-formula in the context `C`. -/
def ltA {C : Type*} (a b : C) : LRc.Formula C := leA a b ⊓ ∼(leA b a)

/-- `0 ≤ a`, i.e. "`a` is a square", as an `LRc`-formula in the context `C`. -/
def sqA {C : Type*} (a : C) : LRc.Formula C := liftR (fun _ : Fin 1 => a) sqF

/-- `t + t * y = y`, as an `LRc`-formula in the context `C`. -/
def lin₁A {C : Type*} (t y : C) : LRc.Formula C := liftR ![t, y] lin₁F

/-- `t - t * y = y`, as an `LRc`-formula in the context `C`. -/
def lin₂A {C : Type*} (t y : C) : LRc.Formula C := liftR ![t, y] lin₂F

/-- `t + t = m + s`, as an `LRc`-formula in the context `C`. -/
def midA {C : Type*} (t m s : C) : LRc.Formula C := liftR ![t, m, s] midF

/-- `φ` with its point variable relabelled to `u` and its parameters to `p`. -/
def fibA {C : Type*} (φ : ParamFormula n) (p : Fin n → C) (u : C) : LRc.Formula C :=
  Formula.relabel (Sum.elim p (fun _ : Fin 1 => u)) φ

/-- The leftmost-component condition on the variable `u`, with fresh variables for the witnesses
`z, w` of the convexity clause. -/
def lcA {C : Type*} (φ : ParamFormula n) (p : Fin n → C) (u : C) : LRc.Formula C :=
  fibA φ p u ⊓ Formula.iAlls (Fin 2)
    ((fibA φ (fun i => Sum.inl (p i)) (Sum.inr (0 : Fin 2))).imp
      ((ltA (Sum.inr (0 : Fin 2)) (Sum.inl u)).imp
        (((ltA (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)) ⊓
            ltA (Sum.inr (1 : Fin 2)) (Sum.inl u))).imp
          (fibA φ (fun i => Sum.inl (p i)) (Sum.inr (1 : Fin 2))))))

/-- The rescaling relation `RescaleRel y t`, with `0 ≤ y` written as "`y` is a square". -/
def rrA {C : Type*} (y t : C) : LRc.Formula C :=
  (sqA y ⊓ lin₁A t y) ⊔ ((∼(sqA y)) ⊓ lin₂A t y)

/-- `m` is the infimum of the rescaled leftmost component `TZset`.  The first conjunct says that
`m` is a lower bound, the second that everything below `m` fails to be one. -/
def infA {C : Type*} (φ : ParamFormula n) (p : Fin n → C) (m : C) : LRc.Formula C :=
  Formula.iAlls (Fin 2)
    ((lcA φ (fun i => Sum.inl (p i)) (Sum.inr (0 : Fin 2))).imp
      ((rrA (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2))).imp
        (leA (Sum.inl m) (Sum.inr (1 : Fin 2)))))
  ⊓
  Formula.iAlls (Fin 1)
    ((Formula.iAlls (Fin 2)
        ((lcA φ (fun i => Sum.inl (Sum.inl (p i))) (Sum.inr (0 : Fin 2))).imp
          ((rrA (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2))).imp
            (leA (Sum.inl (Sum.inr (0 : Fin 1))) (Sum.inr (1 : Fin 2)))))).imp
      (leA (Sum.inr (0 : Fin 1)) (Sum.inl m)))

/-- `s` is the supremum of the rescaled leftmost component `TZset`. -/
def supA {C : Type*} (φ : ParamFormula n) (p : Fin n → C) (s : C) : LRc.Formula C :=
  Formula.iAlls (Fin 2)
    ((lcA φ (fun i => Sum.inl (p i)) (Sum.inr (0 : Fin 2))).imp
      ((rrA (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2))).imp
        (leA (Sum.inr (1 : Fin 2)) (Sum.inl s))))
  ⊓
  Formula.iAlls (Fin 1)
    ((Formula.iAlls (Fin 2)
        ((lcA φ (fun i => Sum.inl (Sum.inl (p i))) (Sum.inr (0 : Fin 2))).imp
          ((rrA (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2))).imp
            (leA (Sum.inr (1 : Fin 2)) (Sum.inl (Sum.inr (0 : Fin 1))))))).imp
      (leA (Sum.inl s) (Sum.inr (0 : Fin 1))))

/-- **The selecting formula.**  Its free variables are the `n` parameters and the point; the three
existentially quantified variables are the infimum `m`, the supremum `s` and the rescaled
midpoint `t`. -/
def selectForm (φ : ParamFormula n) : ParamFormula n :=
  Formula.iExs (Fin 3)
    (lcA φ (fun i : Fin n => Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr 0))
      ⊓ (infA φ (fun i : Fin n => Sum.inl (Sum.inl i)) (Sum.inr (0 : Fin 3))
      ⊓ (supA φ (fun i : Fin n => Sum.inl (Sum.inl i)) (Sum.inr (1 : Fin 3))
      ⊓ (rrA (Sum.inl (Sum.inr 0)) (Sum.inr (2 : Fin 3))
      ⊓ midA (Sum.inr (2 : Fin 3)) (Sum.inr (0 : Fin 3)) (Sum.inr (1 : Fin 3))))))

/-! ## 3. Reindexing the `Fin k`-quantifier blocks

`Formula.iAlls (Fin k)` quantifies over `Fin k → M`; these lemmas convert the block into
`k` nested quantifiers over `M`.  Their left-hand sides are *plain* higher-order patterns
(a metavariable applied to a bound variable), which is what makes them usable by `simp`. -/

theorem forall_fin1' {M : Type} (P : (Fin 1 → M) → Prop) :
    (∀ i, P i) ↔ ∀ a, P ![a] :=
  ⟨fun h a => h ![a], fun h i => by
    have hi : ![i 0] = i := by funext k; fin_cases k <;> rfl
    rw [← hi]; exact h (i 0)⟩

theorem forall_fin2' {M : Type} (P : (Fin 2 → M) → Prop) :
    (∀ i, P i) ↔ ∀ a b, P ![a, b] :=
  ⟨fun h a b => h ![a, b], fun h i => by
    have hi : ![i 0, i 1] = i := by funext k; fin_cases k <;> rfl
    rw [← hi]; exact h (i 0) (i 1)⟩

theorem exists_fin2' {M : Type} (P : (Fin 2 → M) → Prop) :
    (∃ i, P i) ↔ ∃ a b, P ![a, b] :=
  ⟨fun h => by
    obtain ⟨i, hi⟩ := h
    have hi' : ![i 0, i 1] = i := by funext k; fin_cases k <;> rfl
    exact ⟨i 0, i 1, by rw [hi']; exact hi⟩,
   fun h => by obtain ⟨a, b, hab⟩ := h; exact ⟨![a, b], hab⟩⟩

theorem exists_fin3' {M : Type} (P : (Fin 3 → M) → Prop) :
    (∃ i, P i) ↔ ∃ a b c, P ![a, b, c] :=
  ⟨fun h => by
    obtain ⟨i, hi⟩ := h
    have hi' : ![i 0, i 1, i 2] = i := by funext k; fin_cases k <;> rfl
    exact ⟨i 0, i 1, i 2, by rw [hi']; exact hi⟩,
   fun h => by obtain ⟨a, b, c, hab⟩ := h; exact ⟨![a, b, c], hab⟩⟩

/-- Membership in `TZset` is an existential over the leftmost component: the existential can be
moved out of the antecedent of an implication. -/
theorem forall_TZ {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [LRc.Structure M] {φ : ParamFormula n} {v : Fin n → M} {P : M → Prop} :
    (∀ t, t ∈ TZset φ v → P t) ↔ ∀ y t, y ∈ LeftComp φ v → RescaleRel y t → P t := by
  rw [TZset]
  exact ⟨fun h y t hy hrt => h t ⟨y, hy, hrt⟩, fun h t ⟨y, hy, hrt⟩ => h y t hy hrt⟩

/-! ## 4. Realizability of the atoms -/

variable {C : Type*} {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]

theorem sqA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (y : C) :
    (sqA y).Realize w ↔ 0 ≤ w y := by
  rw [sqA, liftR_realize]
  have h : w ∘ (fun _ : Fin 1 => y) = fun _ : Fin 1 => w y := rfl
  rw [h, sqF_realize]
  constructor
  · rintro ⟨z, hz⟩; rw [← hz]; exact mul_self_nonneg z
  · intro h; obtain ⟨z, hz⟩ := hsq (w y) h; exact ⟨z, hz.symm⟩

theorem leA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (a b : C) :
    (leA a b).Realize w ↔ w a ≤ w b := by
  rw [leA, liftR_realize]
  have h : w ∘ ![a, b] = ![w a, w b] := by funext k; fin_cases k <;> rfl
  rw [h]
  exact leF_realize_le hsq (w a) (w b)

theorem ltA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (a b : C) :
    (ltA a b).Realize w ↔ w a < w b := by
  rw [ltA, Formula.realize_inf, Formula.realize_not, leA_realize hsq w a b,
    leA_realize hsq w b a]
  exact lt_iff_le_not_ge.symm

theorem lin₁A_realize (w : C → M) (t y : C) :
    (lin₁A t y).Realize w ↔ w t + w t * w y = w y := by
  rw [lin₁A, liftR_realize]
  have h : w ∘ ![t, y] = ![w t, w y] := by funext k; fin_cases k <;> rfl
  rw [h, lin₁F_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem lin₂A_realize (w : C → M) (t y : C) :
    (lin₂A t y).Realize w ↔ w t - w t * w y = w y := by
  rw [lin₂A, liftR_realize]
  have h : w ∘ ![t, y] = ![w t, w y] := by funext k; fin_cases k <;> rfl
  rw [h, lin₂F_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem midA_realize (w : C → M) (t m s : C) :
    (midA t m s).Realize w ↔ w t + w t = w m + w s := by
  rw [midA, liftR_realize]
  have h : w ∘ ![t, m, s] = ![w t, w m, w s] := by funext k; fin_cases k <;> rfl
  rw [h, midF_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem fibA_realize (φ : ParamFormula n) (p : Fin n → C) (u : C) (w : C → M) :
    (fibA φ p u).Realize w ↔ w u ∈ Fib φ (fun i => w (p i)) := by
  rw [fibA, Formula.realize_relabel]
  have h : w ∘ Sum.elim p (fun _ : Fin 1 => u) =
      Sum.elim (fun i => w (p i)) (fun _ => w u) := by
    funext x; rcases x with i | k <;> rfl
  rw [h]
  rfl

theorem lcA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (φ : ParamFormula n)
    (p : Fin n → C) (u : C) (w : C → M) :
    (lcA φ p u).Realize w ↔ w u ∈ LeftComp φ (fun i => w (p i)) := by
  rw [lcA, Formula.realize_inf, fibA_realize, Formula.realize_iAlls, LeftComp, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun z hz hzy w' hzw' hw'y => ?_⟩
    have h3 := h2 ![z, w']
    simp only [Formula.realize_imp, fibA_realize, ltA_realize hsq, Formula.realize_inf,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at h3
    exact h3 hz hzy ⟨hzw', hw'y⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    simp only [Formula.realize_imp, fibA_realize, ltA_realize hsq, Formula.realize_inf,
      Sum.elim_inl, Sum.elim_inr]
    intro hz hzy hboth
    exact h2 (i 0) hz hzy (i 1) hboth.1 hboth.2

theorem rrA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (w : C → M) (y t : C) :
    (rrA y t).Realize w ↔ RescaleRel (w y) (w t) := by
  rw [rrA, Formula.realize_sup, Formula.realize_inf, Formula.realize_inf, Formula.realize_not,
    sqA_realize hsq, lin₁A_realize, lin₂A_realize, RescaleRel]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, by rw [mul_add, mul_one]; exact h2⟩
    · exact Or.inr ⟨not_le.mp h1, by rw [mul_sub, mul_one]; exact h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, by rw [mul_add, mul_one] at h2; exact h2⟩
    · exact Or.inr ⟨not_le.mpr h1, by rw [mul_sub, mul_one] at h2; exact h2⟩

theorem infA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (φ : ParamFormula n)
    (p : Fin n → C) (m : C) (w : C → M) :
    (infA φ p m).Realize w ↔ IsInfTZ φ (fun i => w (p i)) (w m) := by
  have hR : IsInfTZ φ (fun i => w (p i)) (w m) ↔
      ((∀ y t : M, y ∈ LeftComp φ (fun i => w (p i)) → RescaleRel y t → w m ≤ t) ∧
        ∀ m' : M, (∀ y t : M, y ∈ LeftComp φ (fun i => w (p i)) → RescaleRel y t →
          m' ≤ t) → m' ≤ w m) := by
    simp only [IsInfTZ, forall_TZ]
  rw [hR]
  simp only [infA, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    lcA_realize hsq, rrA_realize hsq, leA_realize hsq, Sum.elim_inl, Sum.elim_inr,
    forall_fin1', forall_fin2', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem supA_realize (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (φ : ParamFormula n)
    (p : Fin n → C) (s : C) (w : C → M) :
    (supA φ p s).Realize w ↔ IsSupTZ φ (fun i => w (p i)) (w s) := by
  have hR : IsSupTZ φ (fun i => w (p i)) (w s) ↔
      ((∀ y t : M, y ∈ LeftComp φ (fun i => w (p i)) → RescaleRel y t → t ≤ w s) ∧
        ∀ s' : M, (∀ y t : M, y ∈ LeftComp φ (fun i => w (p i)) → RescaleRel y t →
          t ≤ s') → w s ≤ s') := by
    simp only [IsSupTZ, forall_TZ]
  rw [hR]
  simp only [supA, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    lcA_realize hsq, rrA_realize hsq, leA_realize hsq, Sum.elim_inl, Sum.elim_inr,
    forall_fin1', forall_fin2', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end Work.WilC2
