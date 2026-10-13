/-
  Area C2 (WilC2): the o-minimal model-theoretic transfer behind `C2_models_ominimal`.

  This file fixes the vocabulary.  `ringToLRc` embeds the language of rings in
  `LRc = (ring ⊕ rexp)[[ℝ]]`; `leF` and `btwF` are the ring-formulas expressing `≤` and strict
  betweenness (via "the difference/nonzero product is a square"); `sliceSent K φ` is the sentence
  saying that every fibre of the parametric family `φ : LRc.Formula (Fin n ⊕ Fin 1)` is a union of
  at most `2K+1` convex sets, exhibited by `K` cut points.  `realize_sliceSent` is its semantic
  characterisation.

  Convention: `φ : ParamFormula n = LRc.Formula (Fin n ⊕ Fin 1)`, the first block being the
  parameters and the single variable `Fin 1` the point at which the fibre is taken, i.e. the
  fibre over `p` is `{y | φ.Realize (Sum.elim p (fun _ => y))}`.
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.ModelTheory.Skolem

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-! ## 1. The language of rings inside `LRc` -/

/-- The inclusion of the language of rings in `LRc = (ring ⊕ rexp)[[ℝ]]`. -/
def ringToLRc : Language.ring →ᴸ LRc :=
  (LHom.sumInl : LR →ᴸ LRc).comp (LHom.sumInl : Language.ring →ᴸ LR)

instance instRingToLRcIsExpansionOn (M : Type) [Language.ring.Structure M] [rexpL.Structure M]
    [(constantsOn ℝ).Structure M] : ringToLRc.IsExpansionOn M :=
  ⟨fun {n} f x => by cases f <;> rfl, fun {n} R _ => isEmptyElim R⟩

/-! ## 2. The arithmetic formulas -/

/-- `leF x y` is `∃ z, x + z * z = y`. -/
def leF : Language.ring.Formula (Fin 2) :=
  (Term.bdEqual
      (Term.var (Sum.inl (0 : Fin 2)) +
        Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
      (Term.var (Sum.inl (1 : Fin 2)))).ex

/-- `btwF a b c` is `∃ z w, (a - b) * (b - c) = z * z ∧ w * z = 1`. -/
def btwF : Language.ring.Formula (Fin 3) :=
  ((Term.bdEqual
      ((Term.var (Sum.inl (0 : Fin 3)) + -Term.var (Sum.inl (1 : Fin 3))) *
        (Term.var (Sum.inl (1 : Fin 3)) + -Term.var (Sum.inl (2 : Fin 3))))
      (Term.var (Sum.inr (0 : Fin 2)) * Term.var (Sum.inr (0 : Fin 2)))) ⊓
    (Term.bdEqual
      (Term.var (Sum.inr (1 : Fin 2)) * Term.var (Sum.inr (0 : Fin 2)))
      (1 : Language.ring.Term (Fin 3 ⊕ Fin 2)))).exs

/-- `liftR f F` is the `LRc`-formula obtained from the ring formula `F` by renaming its free
variables along `f`. -/
def liftR {k : ℕ} {α : Type*} (f : Fin k → α) (F : Language.ring.Formula (Fin k)) :
    LRc.Formula α :=
  Formula.relabel f (ringToLRc.onFormula F)

theorem liftR_realize' {k : ℕ} {α : Type*} (f : Fin k → α) (F : Language.ring.Formula (Fin k))
    {M : Type} [LRc.Structure M] (v : α → M) :
    (liftR f F).Realize v ↔ (ringToLRc.onFormula F).Realize (v ∘ f) := by
  rw [liftR, Formula.realize_relabel]

theorem liftR_realize {k : ℕ} {α : Type*} (f : Fin k → α) (F : Language.ring.Formula (Fin k))
    {M : Type} [Language.ring.Structure M] [LRc.Structure M] [ringToLRc.IsExpansionOn M]
    (v : α → M) :
    (liftR f F).Realize v ↔ F.Realize (v ∘ f) := by
  rw [liftR_realize', LHom.realize_onFormula]

/-! ## 3. Semantics of the arithmetic formulas -/

theorem leF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : Fin 2 → M) : leF.Realize v ↔ ∃ z : M, v 0 + z * z = v 1 := by
  rw [leF, Formula.Realize, BoundedFormula.realize_ex]
  simp only [Fin.snoc_zero, BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]

theorem btwF_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (v : Fin 3 → M) :
    btwF.Realize v ↔ ∃ z w : M, (v 0 - v 1) * (v 1 - v 2) = z * z ∧ w * z = 1 := by
  simp only [btwF, BoundedFormula.realize_exs, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, Ring.realize_add, Ring.realize_mul, Ring.realize_neg,
    Ring.realize_one, Term.realize_var, Sum.elim_inl, Sum.elim_inr, sub_eq_add_neg]
  constructor
  · rintro ⟨xs, h1, h2⟩
    exact ⟨xs 0, xs 1, h1, h2⟩
  · rintro ⟨z, w, h1, h2⟩
    exact ⟨![z, w], by simpa using h1, by simpa using h2⟩

theorem leF_realize_le {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (u v : M) :
    leF.Realize ![u, v] ↔ u ≤ v := by
  rw [leF_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨z, hz⟩
    have : 0 ≤ z * z := mul_self_nonneg z
    linarith
  · intro h
    obtain ⟨z, hz⟩ := hsq (v - u) (by linarith)
    exact ⟨z, by linarith⟩

theorem btwF_realize_btw {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (a b c : M) :
    btwF.Realize ![a, b, c] ↔ (a < b ∧ b < c) ∨ (c < b ∧ b < a) := by
  rw [btwF_realize]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, sub_eq_add_neg]
  constructor
  · rintro ⟨z, w, hz, hw⟩
    have hzne : z ≠ 0 := by intro h; rw [h, mul_zero] at hw; exact zero_ne_one hw
    have hpos : 0 < (a + -b) * (b + -c) := by rw [hz]; exact mul_self_pos.mpr hzne
    rcases lt_trichotomy a b with hab | hab | hba
    · rcases lt_trichotomy b c with hbc | hbc | hcb
      · exact Or.inl ⟨hab, hbc⟩
      · exfalso
        rw [hbc, add_neg_cancel, mul_zero] at hpos
        exact absurd hpos (lt_irrefl 0)
      · exfalso; nlinarith [hpos, hab, hcb]
    · exfalso; subst hab; rw [add_neg_cancel, zero_mul] at hpos
      exact absurd hpos (lt_irrefl 0)
    · rcases lt_trichotomy b c with hbc | hbc | hcb
      · exfalso; nlinarith [hpos, hba, hbc]
      · exfalso
        rw [hbc, add_neg_cancel, mul_zero] at hpos
        exact absurd hpos (lt_irrefl 0)
      · exact Or.inr ⟨hcb, hba⟩
  · rintro (⟨hab, hbc⟩ | ⟨hcb, hba⟩)
    · have hpos : 0 < (a + -b) * (b + -c) := by nlinarith
      obtain ⟨z, hz⟩ := hsq _ hpos.le
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, mul_zero] at hz
        rw [hz] at hpos
        exact absurd hpos (lt_irrefl 0)
      exact ⟨z, z⁻¹, hz, inv_mul_cancel₀ hz0⟩
    · have hpos : 0 < (a + -b) * (b + -c) := by nlinarith
      obtain ⟨z, hz⟩ := hsq _ hpos.le
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, mul_zero] at hz
        rw [hz] at hpos
        exact absurd hpos (lt_irrefl 0)
      exact ⟨z, z⁻¹, hz, inv_mul_cancel₀ hz0⟩

/-! ## 4. The cut-point convexity sentence -/

/-- A parametric family: `n` parameters and one point variable. -/
abbrev ParamFormula (n : ℕ) := LRc.Formula (Fin n ⊕ Fin 1)

/-- The variables of the cut-point sentence, arranged so that all four quantifier blocks can be
stripped from the right (outermost quantifier first: parameters, cut points, the triple `(u,w,v)`).
The leading `Empty` block lets `Formula.iAlls (Fin n)` end in a genuine `Sentence`. -/
abbrev QVar (n K : ℕ) := ((Empty ⊕ Fin n) ⊕ Fin K) ⊕ Fin 3

/-- The parameter variables. -/
def paramVar {n K : ℕ} (i : Fin n) : QVar n K := Sum.inl (Sum.inl (Sum.inr i))

/-- The cut-point variables. -/
def cutVar {n K : ℕ} (j : Fin K) : QVar n K := Sum.inl (Sum.inr j)

/-- The `(u,w,v)` variables. -/
def ptVar {n K : ℕ} (k : Fin 3) : QVar n K := Sum.inr k

/-- The assignment function produced by the quantifier blocks: parameters, cut points, triple. -/
def rawV {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) : QVar n K → M :=
  fun b => Sum.elim (Sum.elim (fun b' => Sum.elim v p b') y) q b

theorem rawV_eq {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) :
    rawV v p y q = fun a => Sum.elim (Sum.elim (fun b' => Sum.elim v p b') y) q a := rfl

theorem rawV_paramVar {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) (i : Fin n) : rawV v p y q (paramVar (K := K) i) = p i := by
  simp [rawV, paramVar]

theorem rawV_cutVar {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) (j : Fin K) : rawV v p y q (cutVar (n := n) j) = y j := by
  simp [rawV, cutVar]

theorem rawV_ptVar {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) (k : Fin 3) : rawV v p y q (ptVar (n := n) (K := K) k) = q k := by
  simp [rawV, ptVar]

/-- `φ` with its point variable renamed to `x`. -/
def evalAt {n K : ℕ} (φ : ParamFormula n) (x : QVar n K) : LRc.Formula (QVar n K) :=
  Formula.relabel (Sum.elim (fun i => paramVar (K := K) i) (fun _ => x)) φ

/-- Monotonicity of the cut points. -/
def monoForm {n K : ℕ} : LRc.Formula (QVar n K) :=
  Formula.iInf (fun b : {b : Fin K × Fin K // b.1 ≤ b.2} =>
    liftR ![cutVar (n := n) b.1.1, cutVar (n := n) b.1.2] leF)

/-- The convexity clause: on each of the pieces cut out by the cut points the fibre is convex. -/
def clauseForm {n K : ℕ} (φ : ParamFormula n) : LRc.Formula (QVar n K) :=
  (evalAt φ (ptVar (n := n) 0) ⊓ evalAt φ (ptVar (n := n) 2) ⊓
      liftR ![ptVar (n := n) 0, ptVar (n := n) 1, ptVar (n := n) 2] btwF ⊓
      Formula.iInf (fun j : Fin K => ∼(liftR ![ptVar (n := n) 0, cutVar (n := n) j,
        ptVar (n := n) 2] btwF))) ⟹ evalAt φ (ptVar (n := n) 1)

/-- **The cut-point sentence.** `K` cut points exhibit every fibre of `φ` as a union of at most
`2K+1` convex sets. -/
def sliceSent {n : ℕ} (K : ℕ) (φ : ParamFormula n) : LRc.Sentence :=
  Formula.iAlls (Fin n) (Formula.iExs (Fin K) (Formula.iAlls (Fin 3) (monoForm ⊓ clauseForm φ)))

/-- The assertion realised by `sliceSent`, in terms of the raw assignment `rawV`. -/
def SliceRaw {n : ℕ} (K : ℕ) (φ : ParamFormula n) (M : Type*) [LRc.Structure M] :
    Prop :=
  ∀ (p : Fin n → M), ∃ (y : Fin K → M), ∀ (q : Fin 3 → M),
    (∀ b : {b : Fin K × Fin K // b.1 ≤ b.2},
        (ringToLRc.onFormula leF).Realize (rawV (default : Empty → M) p y q ∘
          ![cutVar (n := n) b.1.1, cutVar (n := n) b.1.2])) ∧
      ((((φ.Realize (rawV (default : Empty → M) p y q ∘
            Sum.elim (fun i => paramVar (K := K) i) (fun _ => ptVar (n := n) 0)) ∧
          φ.Realize (rawV (default : Empty → M) p y q ∘
            Sum.elim (fun i => paramVar (K := K) i) (fun _ => ptVar (n := n) 2))) ∧
        (ringToLRc.onFormula btwF).Realize (rawV (default : Empty → M) p y q ∘
          ![ptVar (n := n) 0, ptVar (n := n) 1, ptVar (n := n) 2])) ∧
        ∀ j : Fin K, ¬(ringToLRc.onFormula btwF).Realize ((rawV (default : Empty → M) p y q) ∘
          ![ptVar (n := n) 0, cutVar (n := n) j, ptVar (n := n) 2])) →
      φ.Realize (rawV (default : Empty → M) p y q ∘
        Sum.elim (fun i => paramVar (K := K) i) (fun _ => ptVar (n := n) 1)))

/-- The semantic content of `sliceSent`, in the `Fin 3`-indexed form matching `SliceRaw`
syntactically. -/
def SliceGoodQ {n : ℕ} (K : ℕ) (φ : ParamFormula n) (M : Type*) [LRc.Structure M]
    [Preorder M] : Prop :=
  ∀ p : Fin n → M, ∃ y : Fin K → M, (∀ i j : Fin K, i ≤ j → y i ≤ y j) ∧
    ∀ q : Fin 3 → M, φ.Realize (Sum.elim p (fun _ => q 0)) →
      φ.Realize (Sum.elim p (fun _ => q 2)) →
      ((q 0 < q 1 ∧ q 1 < q 2) ∨ (q 2 < q 1 ∧ q 1 < q 0)) →
      (∀ j : Fin K, ¬((q 0 < y j ∧ y j < q 2) ∨ (q 2 < y j ∧ y j < q 0))) →
      φ.Realize (Sum.elim p (fun _ => q 1))

/-- The semantic content of `sliceSent K φ`, as used by the model-theoretic arguments. -/
def SliceGood {n : ℕ} (K : ℕ) (φ : ParamFormula n) (M : Type*) [LRc.Structure M] [Preorder M] :
    Prop :=
  ∀ p : Fin n → M, ∃ y : Fin K → M, (∀ i j : Fin K, i ≤ j → y i ≤ y j) ∧
    ∀ u w v : M, φ.Realize (Sum.elim p (fun _ => u)) →
      φ.Realize (Sum.elim p (fun _ => v)) →
      ((u < w ∧ w < v) ∨ (v < w ∧ w < u)) →
      (∀ j : Fin K, ¬((u < y j ∧ y j < v) ∨ (v < y j ∧ y j < u))) →
      φ.Realize (Sum.elim p (fun _ => w))


theorem rawV_comp_param {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) (x : QVar n K) :
    rawV v p y q ∘ (Sum.elim (fun i => paramVar (K := K) i) (fun _ : Fin 1 => x)) =
      Sum.elim p (fun _ => rawV v p y q x) := by
  funext b
  rcases b with i | k
  · simp [Function.comp_apply, rawV_paramVar]
  · simp [Function.comp_apply]

theorem rawV_comp_vec2 {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) (x : Fin 2 → QVar n K) :
    rawV v p y q ∘ x = ![rawV v p y q (x 0), rawV v p y q (x 1)] := by
  funext b
  fin_cases b <;> simp [Function.comp_apply]

theorem rawV_comp_vec3 {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M) (y : Fin K → M)
    (q : Fin 3 → M) (x : Fin 3 → QVar n K) :
    rawV v p y q ∘ x = ![rawV v p y q (x 0), rawV v p y q (x 1), rawV v p y q (x 2)] := by
  funext b
  fin_cases b <;> simp [Function.comp_apply]

theorem rawV_comp_param_pt {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M)
    (y : Fin K → M) (q : Fin 3 → M) (k : Fin 3) :
    rawV v p y q ∘ (Sum.elim (fun i => paramVar (K := K) i) (fun _ : Fin 1 => ptVar (n := n) k)) =
      Sum.elim p (fun _ => q k) := by
  rw [rawV_comp_param]
  simp [rawV_ptVar]

theorem rawV_comp_vec2_cut {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M)
    (y : Fin K → M) (q : Fin 3 → M) (i j : Fin K) :
    rawV v p y q ∘ ![cutVar (n := n) i, cutVar (n := n) j] = ![y i, y j] := by
  rw [rawV_comp_vec2]
  simp [rawV_cutVar]

theorem rawV_comp_vec3_pt {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M)
    (y : Fin K → M) (q : Fin 3 → M) :
    rawV v p y q ∘ ![ptVar (n := n) 0, ptVar (n := n) 1, ptVar (n := n) 2] =
      ![q 0, q 1, q 2] := by
  rw [rawV_comp_vec3]
  simp [rawV_ptVar]

theorem rawV_comp_vec3_cut {M : Type*} {n K : ℕ} (v : Empty → M) (p : Fin n → M)
    (y : Fin K → M) (q : Fin 3 → M) (j : Fin K) :
    rawV v p y q ∘ ![ptVar (n := n) 0, cutVar (n := n) j, ptVar (n := n) 2] =
      ![q 0, y j, q 2] := by
  rw [rawV_comp_vec3]
  simp [rawV_ptVar, rawV_cutVar]

/-! ## 5. The realisation theorem -/

/-- **The semantic characterisation of `sliceSent`.** -/
theorem realize_sliceSent_raw {M : Type} [LRc.Structure M] {n : ℕ} (K : ℕ)
    (φ : ParamFormula n) : M ⊨ sliceSent K φ ↔ SliceRaw K φ M := by
  rw [sliceSent, SliceRaw]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_inf, Formula.realize_imp, Formula.realize_not,
    monoForm, clauseForm, evalAt, liftR_realize', Formula.realize_relabel, rawV_eq]

end Work.WilC2
