/-
  WilC4 : `monoDefinable_W` (area C4 of `annals_wilkies_conjecture`).

  `MonoW Y` is the set of points at which the partial function described by `Y ⊆ ℝ²` is
  *locally constant*: some value `y` with `(x, y) ∈ Y` works for a whole neighbourhood of `x`.
  This file shows that it is `∅`-definable in `LRc` as soon as `Y` is.

  Mathematically the statement is pure first-order logic: the definition of `MonoW` is

      x ∈ MonoW Y  ↔  ∃ y ε, 0 < ε ∧ (x, y) ∈ Y ∧ ∀ z, x - ε < z → z < x + ε → (z, y) ∈ Y,

  a formula built out of the definable relation `Y`, the field operations and the order.  The
  only work is the transcription into the language `LRc = (ring ⊕ rexp)[[ℝ]]`, which has symbols
  for `+`, `*`, `-`, `0`, `1` and the restricted exponential (and a constant for every real), but
  **no** symbol for the order.  As in the rest of area C (`Work.WilC2.leF`, `Work.WilC4.posAtom`),
  the order is written *inside the language of rings*:

  * `0 < x` is the ring formula `x ≠ 0 ∧ ∃ w, w * w = x` (`wLtZeroAtom`);
  * `x ≤ y` is the ring formula `∃ w, w * w = y - x` (`wLeAtom`), and `x < y` is
    `x ≤ y ∧ x ≠ y` (`wLtAtom`);
  * `x + y = z` is the ring formula `x + y = z` (`wAddAtom`).

  These formulas mean what they should because in `ℝ` every nonnegative real is a square
  (the hypothesis `hsq`, discharged at the end by `Real.sq_sqrt`).

  `LRc` has no symbol for the *difference* either, so `x - ε` and `x + ε` are handled by
  introducing the two auxiliary variables `a, b`, subject to the (term) equations `a + ε = x`
  and `x + ε = b` -- see `Wbody`.  The quantifier blocks are then stripped in order with
  `Set.Definable.forall_of_finite` (`z`) and `Set.Definable.exists_of_finite` (`y, ε, a, b`).
-/
import Mathlib
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.finite_definable_singleton

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize)

/-! ## 1. The atomic ring formulas -/

/-- The atom `x = 0`. -/
def wZeroAtom : ring.Formula (Fin 1) := Term.equal (Term.var 0) (0 : ring.Term (Fin 1))

/-- The atom `x ≠ 0`. -/
def wNeZeroAtom : ring.Formula (Fin 1) := wZeroAtom.not

/-- The atom `∃ w, w * w = x`, i.e. `0 ≤ x` in a linearly ordered field in which every
nonnegative element is a square. -/
def wPosAtom : ring.Formula (Fin 1) :=
  (Term.bdEqual (Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1) * Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1))
    (Term.var (Sum.inl 0))).ex

/-- The atom `0 < x`, i.e. `x ≠ 0 ∧ ∃ w, w * w = x`. -/
def wLtZeroAtom : ring.Formula (Fin 1) := wPosAtom ⊓ wNeZeroAtom

/-- The atom `x + y = z`. -/
def wAddAtom : ring.Formula (Fin 3) := Term.equal (Term.var 0 + Term.var 1) (Term.var 2)

/-- The atom `x = y`. -/
def wEqAtom : ring.Formula (Fin 2) := Term.equal (Term.var 0) (Term.var 1)

/-- The atom `x ≠ y`. -/
def wNeqAtom : ring.Formula (Fin 2) := wEqAtom.not

/-- The atom `x ≤ y`, i.e. `∃ w, w * w = y - x`. -/
def wLeAtom : ring.Formula (Fin 2) :=
  (Term.bdEqual (Term.var (Sum.inr 0 : Fin 2 ⊕ Fin 1) * Term.var (Sum.inr 0 : Fin 2 ⊕ Fin 1))
    (Term.var (Sum.inl 1) + -(Term.var (Sum.inl 0)))).ex

/-- The atom `x < y`, i.e. `x ≤ y ∧ x ≠ y`. -/
def wLtAtom : ring.Formula (Fin 2) := wLeAtom ⊓ wNeqAtom

/-! ## 2. Realisation of the atoms after substitution of variables -/

section Atoms

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-- The order of an ordered field in which every nonnegative element is a square is a square:
`(∃ z, z * z = u) ↔ 0 ≤ u`. -/
theorem sq_iff_nonneg {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (hsq : ∀ x : R, 0 ≤ x → ∃ z : R, x = z * z) (u : R) :
    (∃ z : R, z * z = u) ↔ 0 ≤ u := by
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact mul_self_nonneg z
  · intro h
    obtain ⟨z, hz⟩ := hsq u h
    exact ⟨z, hz.symm⟩

theorem wZeroAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M) :
    (liftR f wZeroAtom).Realize rw ↔ rw (f 0) = 0 := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0)] := by funext t; fin_cases t <;> rfl
  rw [h]
  simp [wZeroAtom]

theorem wPosAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M) :
    (liftR f wPosAtom).Realize rw ↔ ∃ z : M, z * z = rw (f 0) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0)] := by funext t; fin_cases t <;> rfl
  rw [h]
  rw [wPosAtom, Formula.Realize, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_mul, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_fin_one]

theorem wLtZeroAtom_lift {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR f wLtZeroAtom).Realize rw ↔ 0 < rw (f 0) := by
  rw [show liftR f wLtZeroAtom = (liftR f wPosAtom) ⊓ (liftR f wNeZeroAtom) from rfl,
    Formula.realize_inf, wPosAtom_lift, sq_iff_nonneg hsq]
  rw [show liftR f wNeZeroAtom = (liftR f wZeroAtom).not from rfl, Formula.realize_not,
    wZeroAtom_lift]
  exact ⟨fun h => lt_of_le_of_ne h.1 (fun h0 => h.2 h0.symm), fun h => ⟨h.le, ne_of_gt h⟩⟩

theorem wAddAtom_lift {Ctx : Type} (f : Fin 3 → Ctx) (rw : Ctx → M) :
    (liftR f wAddAtom).Realize rw ↔ rw (f 0) + rw (f 1) = rw (f 2) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1), rw (f 2)] := by funext t; fin_cases t <;> rfl
  rw [h]
  simp [wAddAtom]

theorem wEqAtom_lift {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M) :
    (liftR f wEqAtom).Realize rw ↔ rw (f 0) = rw (f 1) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1)] := by funext t; fin_cases t <;> rfl
  rw [h]
  simp [wEqAtom]

theorem wLeAtom_lift {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR f wLeAtom).Realize rw ↔ rw (f 0) ≤ rw (f 1) := by
  rw [liftR_realize]
  have h : rw ∘ f = ![rw (f 0), rw (f 1)] := by funext t; fin_cases t <;> rfl
  rw [h]
  rw [wLeAtom, Formula.Realize, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_mul, Ring.realize_add,
    Ring.realize_neg, Term.realize_var, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · rintro ⟨z, hz⟩
    nlinarith [mul_self_nonneg z]
  · intro hle
    obtain ⟨z, hz⟩ := hsq (rw (f 1) - rw (f 0)) (by linarith)
    exact ⟨z, by linarith [hz]⟩

theorem wLtAtom_lift {Ctx : Type} (f : Fin 2 → Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR f wLtAtom).Realize rw ↔ rw (f 0) < rw (f 1) := by
  rw [show liftR f wLtAtom = (liftR f wLeAtom) ⊓ (liftR f wNeqAtom) from rfl,
    Formula.realize_inf, wLeAtom_lift _ _ hsq]
  rw [show liftR f wNeqAtom = (liftR f wEqAtom).not from rfl, Formula.realize_not, wEqAtom_lift]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨h.le, ne_of_lt h⟩⟩

/-! ## 3. The definable sets attached to the atoms -/

/-- `0 < v i` is definable without parameters. -/
theorem wLtZero_definable {Ω : Type} (i : Ω) (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (∅ : Set M).Definable LRc {v : Ω → M | 0 < v i} := by
  rw [Set.empty_definable_iff]
  refine ⟨liftR (fun _ : Fin 1 => i) wLtZeroAtom, ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [wLtZeroAtom_lift (fun _ : Fin 1 => i) v hsq]

/-- `v i + v j = v k` is definable without parameters. -/
theorem wAdd_eq_definable {Ω : Type} (i j k : Ω) :
    (∅ : Set M).Definable LRc {v : Ω → M | v i + v j = v k} := by
  rw [Set.empty_definable_iff]
  refine ⟨liftR ![i, j, k] wAddAtom, ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [wAddAtom_lift ![i, j, k] v]
  simp

/-- `v i < v j` is definable without parameters. -/
theorem wLt_definable {Ω : Type} (i j : Ω) (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (∅ : Set M).Definable LRc {v : Ω → M | v i < v j} := by
  rw [Set.empty_definable_iff]
  refine ⟨liftR ![i, j] wLtAtom, ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [wLtAtom_lift ![i, j] v hsq]
  simp

/-- The pullback of a definable `Y ⊆ M²` along two coordinate projections:
`{v | (v i, v j) ∈ Y}` is definable over the same parameters. -/
theorem wPair_definable {A : Set M} {Y : Set (Fin 2 → M)} (hY : A.Definable LRc Y)
    {Ω : Type} (i j : Ω) : A.Definable LRc {v : Ω → M | ![v i, v j] ∈ Y} := by
  have h' : (fun g : Ω → M => g ∘ ![i, j]) ⁻¹' Y = {v : Ω → M | ![v i, v j] ∈ Y} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show v ∘ ![i, j] = ![v i, v j] from by funext t; fin_cases t <;> rfl]
  have h := hY.preimage_comp (f := ![i, j])
  rwa [h'] at h

end Atoms

/-! ## 4. The body, and its quantifier blocks

The free variable is `x`; the existentially quantified block is `y, ε, a, b` (with `a` and `b`
naming `x - ε` and `x + ε`), and the universally quantified block is `z`.  These are the three
blocks of `Wctx = (Fin 1 ⊕ Fin 4) ⊕ Fin 1`, and `Wx`, `Wy`, `We`, `Wa`, `Wb`, `Wz` are the
individual variables. -/

/-- The index type of the body: `x`, then `y, ε, a, b`, then `z`. -/
abbrev Wctx : Type := (Fin 1 ⊕ Fin 4) ⊕ Fin 1

/-- The free variable `x`. -/
def Wx : Wctx := Sum.inl (Sum.inl 0)
/-- The variable `y` (the value). -/
def Wy : Wctx := Sum.inl (Sum.inr 0)
/-- The variable `ε` (the radius). -/
def We : Wctx := Sum.inl (Sum.inr 1)
/-- The variable `a = x - ε` (the left endpoint). -/
def Wa : Wctx := Sum.inl (Sum.inr 2)
/-- The variable `b = x + ε` (the right endpoint). -/
def Wb : Wctx := Sum.inl (Sum.inr 3)
/-- The universally quantified variable `z`. -/
def Wz : Wctx := Sum.inr 0

/-- The body of the definition of `MonoW`, in coordinates:
`0 < ε ∧ a + ε = x ∧ x + ε = b ∧ (x, y) ∈ Y ∧ (a < z → z < b → (z, y) ∈ Y)`. -/
def Wbody {M : Type} [Add M] [Zero M] [LT M] (Y : Set (Fin 2 → M)) : Set (Wctx → M) :=
  {v | 0 < v We ∧ v Wa + v We = v Wx ∧ v Wx + v We = v Wb ∧ ![v Wx, v Wy] ∈ Y ∧
    (v Wa < v Wz → v Wz < v Wb → ![v Wz, v Wy] ∈ Y)}

/-- The body with `z` universally quantified. -/
def Wuniv {M : Type} [Add M] [Zero M] [LT M] (Y : Set (Fin 2 → M)) :
    Set ((Fin 1 ⊕ Fin 4) → M) :=
  {v | ∀ u : Fin 1 → M, Sum.elim v u ∈ Wbody Y}

/-- The body with `y, ε, a, b` existentially quantified: this is the `LRc`-definable set that
turns out to be `MonoW Y`. -/
def Wfin {M : Type} [Add M] [Zero M] [LT M] (Y : Set (Fin 2 → M)) : Set (Fin 1 → M) :=
  {v | ∃ u : Fin 4 → M, Sum.elim v u ∈ Wuniv Y}

section Assembly

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-- The body is definable over the parameters of `Y`. -/
theorem wBody_definable {A : Set M} {Y : Set (Fin 2 → M)} (hY : A.Definable LRc Y)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    A.Definable LRc (Wbody Y) := by
  have h1 : A.Definable LRc {v : Wctx → M | 0 < v We} :=
    (wLtZero_definable (M := M) We hsq).mono (Set.empty_subset A)
  have h2 : A.Definable LRc {v : Wctx → M | v Wa + v We = v Wx} :=
    (wAdd_eq_definable (M := M) Wa We Wx).mono (Set.empty_subset A)
  have h3 : A.Definable LRc {v : Wctx → M | v Wx + v We = v Wb} :=
    (wAdd_eq_definable (M := M) Wx We Wb).mono (Set.empty_subset A)
  have h4 : A.Definable LRc {v : Wctx → M | ![v Wx, v Wy] ∈ Y} := wPair_definable hY Wx Wy
  have h5 : A.Definable LRc {v : Wctx → M | v Wa < v Wz} :=
    (wLt_definable (M := M) Wa Wz hsq).mono (Set.empty_subset A)
  have h6 : A.Definable LRc {v : Wctx → M | v Wz < v Wb} :=
    (wLt_definable (M := M) Wz Wb hsq).mono (Set.empty_subset A)
  have h7 : A.Definable LRc {v : Wctx → M | ![v Wz, v Wy] ∈ Y} := wPair_definable hY Wz Wy
  have h := h1.inter (h2.inter (h3.inter (h4.inter ((h5.inter h6).compl.union h7))))
  convert h using 1
  ext v
  simp only [Wbody, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
  tauto

/-- The universally quantified body is definable over the parameters of `Y`. -/
theorem wUniv_definable {A : Set M} {Y : Set (Fin 2 → M)} (hY : A.Definable LRc Y)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) : A.Definable LRc (Wuniv Y) := by
  have h := (wBody_definable (A := A) hY hsq).forall_of_finite (α := Fin 1 ⊕ Fin 4) (β := Fin 1)
  simpa only [Wuniv] using h

/-- `Wfin Y` is definable over the parameters of `Y`. -/
theorem wFin_definable {A : Set M} {Y : Set (Fin 2 → M)} (hY : A.Definable LRc Y)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) : A.Definable LRc (Wfin Y) := by
  have h := (wUniv_definable (A := A) hY hsq).exists_of_finite (α := Fin 1) (β := Fin 4)
  simpa only [Wfin] using h

end Assembly

/-! ## 5. The arithmetic identification of `Wfin Y` with `MonoW Y` -/

/-- Unfolding of the fourfold existential quantifier of `Wfin`. -/
theorem exists_fin4_iff {M : Type} {Q : (Fin 4 → M) → Prop} :
    (∃ f : Fin 4 → M, Q f) ↔ ∃ a b c d : M, Q ![a, b, c, d] :=
  ⟨fun ⟨f, hf⟩ => ⟨f 0, f 1, f 2, f 3, by
      have hf' : (![f 0, f 1, f 2, f 3] : Fin 4 → M) = f := funext fun i => by
        fin_cases i <;> rfl
      rw [hf']
      exact hf⟩,
   fun ⟨a, b, c, d, h⟩ => ⟨![a, b, c, d], h⟩⟩

/-- Unfolding of the universal quantifier over `Fin 1`. -/
theorem forall_fin1_iff {M : Type} {Q : (Fin 1 → M) → Prop} :
    (∀ f : Fin 1 → M, Q f) ↔ ∀ a : M, Q (fun _ => a) :=
  ⟨fun h a => h (fun _ => a),
   fun h f => by
     have hf : (fun _ : Fin 1 => f 0) = f := funext fun i => by fin_cases i; rfl
     rw [← hf]
     exact h (f 0)⟩

/-- `Wfin Y`, in coordinates. -/
theorem mem_wfin {Y : Set (Fin 2 → ℝ)} {v : Fin 1 → ℝ} :
    v ∈ Wfin Y ↔ ∃ y ε a b : ℝ, 0 < ε ∧ a + ε = v 0 ∧ v 0 + ε = b ∧ ![v 0, y] ∈ Y ∧
      (∀ z : ℝ, a < z → z < b → ![z, y] ∈ Y) := by
  simp only [Wfin, Wuniv, Wbody, Set.mem_ofPred_eq, Wx, Wy, We, Wa, Wb, Wz, Sum.elim_inl,
    Sum.elim_inr, exists_fin4_iff, forall_fin1_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  constructor
  · rintro ⟨a, b, c, d, h⟩
    exact ⟨a, b, c, d, (h 0).1, (h 0).2.1, (h 0).2.2.1, (h 0).2.2.2.1,
      fun z hz1 hz2 => (h z).2.2.2.2 hz1 hz2⟩
  · rintro ⟨y, ε, a, b, h1, h2, h3, h4, h5⟩
    exact ⟨y, ε, a, b, fun z => ⟨h1, h2, h3, h4, h5 z⟩⟩

/-- `Wfin Y` is `MonoW Y`, read on one-point tuples. -/
theorem wfin_real (Y : Set (Fin 2 → ℝ)) :
    {v : Fin 1 → ℝ | v 0 ∈ MonoW Y} = Wfin Y := by
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [mem_wfin, mem_MonoW]
  constructor
  · rintro ⟨y, ε, hε, hY, hall⟩
    exact ⟨y, ε, v 0 - ε, v 0 + ε, hε, by ring, rfl, hY, fun z h1 h2 => hall z h1 h2⟩
  · rintro ⟨y, ε, a, b, hε, h1, h2, hY, hall⟩
    exact ⟨y, ε, hε, hY, fun z hz1 hz2 => hall z (by linarith) (by linarith)⟩

/-! ## 6. The theorem -/

/-- **`MonoW` is definable.**  The locally constant locus of a `∅`-definable partial function
`Y ⊆ ℝ²` is `∅`-definable in `LRc`.  This is the definition of `MonoW` transcribed into the
language: `x ∈ MonoW Y` iff there are `y, ε, a, b` with `0 < ε`, `a + ε = x`, `x + ε = b`,
`(x, y) ∈ Y` and `(z, y) ∈ Y` for all `z ∈ (a, b)`; the order is expressed by squares
(`wLtAtom`, `wLeAtom`) and `ℝ` is linearly ordered, so `a < z ∧ z < b ↔ x - ε < z ∧ z < x + ε`
along `a + ε = x`, `x + ε = b`. -/
theorem monoDefinable_W {Y : Set (Fin 2 → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (MonoW Y) := by
  have hsq : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z := fun x hx => by
    have h2 := Real.sq_sqrt hx
    exact ⟨Real.sqrt x, by
      calc x = (Real.sqrt x) ^ 2 := h2.symm
        _ = Real.sqrt x * Real.sqrt x := by ring⟩
  have h : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Wfin Y) :=
    wFin_definable (A := (∅ : Set ℝ)) hY hsq
  unfold Set.Definable₁
  rw [wfin_real Y]
  exact h

end Work.WilC4
