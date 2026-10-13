/-
  WilC4/critAux : the definability infrastructure behind `Work.WilC4.crit_def_germ`.

  The sets `PMonoDom, PMonoW, PMonoLm, PMonoHm, PMonoLp, PMonoHp, PMonoLA, PMonoHA`
  (`Submission/Work/WilC4/CritDefs.lean`) are described by first-order formulas built from

  * the membership relation of a `∅`-definable family `Y ⊆ ℝ^{k+2}` (pulled back along a
    reindexing `Fin (k+2) → α ⊕ β`), and
  * comparisons of *ring terms* in the coordinates (`0 < ε`, `p 0 - ε < z`, `y' < y`, …).

  This file provides the two ingredients in a form reusable by the sibling lemmas:

  * `rterm` / `definableFun_rterm` : the realization of a term of the language of rings is a
    `∅`-definable function (`LRc` contains the language of rings, `ringToLRc`), and
  * `definable_lt_fun` / `definable_lt_terms` / `definable_lt_sub` / `definable_lt_add` /
    `definable_lt_const_left` : `{v | f v < g v}` is `∅`-definable for `∅`-definable `f`, `g`;
    this rests on `Work.WilC2.definable_lt` (the order is `LRc`-definable in `ℝ` because every
    nonnegative real is a square) and on `Set.Definable.preimage_map`.

  It also contains the proof of `pw_definable` — the (one) instance of the pattern that needs the
  full "reindex + quantifier block" bookkeeping — so that the sibling lemmas for the germs and for
  `PMonoLA`/`PMonoHA` can be read against it.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC4.paramDom_definable
import Submission.Work.WilC2.bnd_definable_alt

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Ring terms as `∅`-definable functions -/

/-- In `ℝ` every nonnegative element is a square. -/
theorem hsqR (x : ℝ) (hx : 0 ≤ x) : ∃ z : ℝ, x = z * z :=
  ⟨Real.sqrt x, by nlinarith [Real.sq_sqrt hx]⟩

/-- The `LRc`-term attached to a term of the language of rings. -/
noncomputable def rterm {α : Type} (t : Language.ring.Term α) : LRc.Term α :=
  (Language.lhomWithConstants LR ℝ).onTerm
    ((LHom.sumInl : Language.ring →ᴸ LR).onTerm t)

lemma rterm_realize {α : Type} (t : Language.ring.Term α) (v : α → ℝ) :
    Term.realize v (rterm t) = Term.realize v t := by
  rw [rterm, LHom.realize_onTerm, LHom.realize_onTerm]

/-- The realization of a ring term is a `∅`-definable function. -/
lemma definableFun_rterm {α : Type} (t : Language.ring.Term α) :
    (∅ : Set ℝ).DefinableFun LRc (fun v : α → ℝ => Term.realize v t) := by
  have h := Term.definableFun_realize (L := LRc) (M := ℝ) (rterm t)
  convert h using 1
  funext v
  exact (rterm_realize t v).symm

/-! ## 2. Comparisons of `∅`-definable functions -/

/-- `{v | f v < g v}` is `∅`-definable when `f` and `g` are. -/
lemma definable_lt_fun {α : Type} {f g : (α → ℝ) → ℝ}
    (hf : (∅ : Set ℝ).DefinableFun LRc f) (hg : (∅ : Set ℝ).DefinableFun LRc g) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | f v < g v} := by
  have hmap : (∅ : Set ℝ).DefinableMap LRc (fun v : α → ℝ => ![f v, g v]) := by
    intro m
    fin_cases m
    · simpa using hf
    · simpa using hg
  have hlt := Work.WilC2.definable_lt (A := ∅) hsqR (0 : Fin 2) 1
  convert hlt.preimage_map hmap using 1
  ext v
  simp

/-- Comparison of two ring terms. -/
lemma definable_lt_terms {α : Type} (t₁ t₂ : Language.ring.Term α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | Term.realize v t₁ < Term.realize v t₂} :=
  definable_lt_fun (definableFun_rterm t₁) (definableFun_rterm t₂)

/-- `{v | v i - v j < v l}`. -/
lemma definable_lt_sub {α : Type} (i j l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i - v j < v l} := by
  have h := definable_lt_terms (α := α) (Term.var i + -Term.var j) (Term.var l)
  convert h using 1
  ext v
  show v i - v j < v l ↔ Term.realize v (Term.var i + -Term.var j) < Term.realize v (Term.var l)
  simp [sub_eq_add_neg]

/-- `{v | v i < v j + v l}`. -/
lemma definable_lt_add {α : Type} (i j l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i < v j + v l} := by
  have h := definable_lt_terms (α := α) (Term.var i) (Term.var j + Term.var l)
  convert h using 1
  ext v
  show v i < v j + v l ↔ Term.realize v (Term.var i) < Term.realize v (Term.var j + Term.var l)
  simp

/-- `{v | 0 < v l}`. -/
lemma definable_lt_const_left {α : Type} (l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | (0 : ℝ) < v l} := by
  have h := definable_lt_terms (α := α) (0 : Language.ring.Term α) (Term.var l)
  convert h using 1
  ext v
  show (0 : ℝ) < v l ↔ Term.realize v (0 : Language.ring.Term α) < Term.realize v (Term.var l)
  simp

/-- `{v | v l < 0}`. -/
lemma definable_lt_const_right {α : Type} (l : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v l < (0 : ℝ)} := by
  have h := definable_lt_terms (α := α) (Term.var l) (0 : Language.ring.Term α)
  convert h using 1
  ext v
  show v l < (0 : ℝ) ↔ Term.realize v (Term.var l) < Term.realize v (0 : Language.ring.Term α)
  simp

/-! ## 3. The parametric locally constant locus `PW`

`PW Y = {p | ∃ y ε, 0 < ε ∧ (p 0, y, p) ∈ Y ∧ ∀ z, p 0 - ε < z → z < p 0 + ε → (z, y, p) ∈ Y}`.

We put the parameters `p`, the two quantified reals `y, ε` and the bound variable `z` into the
single index type `σ = ((Fin (k+1) ⊕ Fin 2) ⊕ Fin 1)`, and take the set `PS k Y` of tuples whose
`p`-part, `y`-part, `ε`-part and `z`-part satisfy the body of the formula.  It is `∅`-definable,
and `PW Y` is obtained from it by the universal quantification over the `Fin 1` (`z`) block and the
existential quantification over the `Fin 2` (`y, ε`) block. -/

/-- The index type for the `PW` construction: `(parameters) ⊕ (y, ε) ⊕ (z)`. -/
abbrev PSig (k : ℕ) : Type := ((Fin (k+1) ⊕ Fin 2) ⊕ Fin 1)

/-- The coordinate of `p i`, `i : Fin (k+1)`. -/
def pIx {k : ℕ} (i : Fin (k+1)) : PSig k := Sum.inl (Sum.inl i)
/-- The coordinate of `y`. -/
def yIx {k : ℕ} : PSig k := Sum.inl (Sum.inr 0)
/-- The coordinate of `ε`. -/
def eIx {k : ℕ} : PSig k := Sum.inl (Sum.inr 1)
/-- The coordinate of `z`. -/
def zIx {k : ℕ} : PSig k := Sum.inr 0

/-- The reindexing of `Y` used for the membership `(p 0, y, p) ∈ Y`. -/
def t1 (k : ℕ) : Fin (k+2) → PSig k :=
  Fin.cons (pIx (k := k) 0) (Fin.cons (yIx (k := k)) (fun j : Fin k => pIx (k := k) j.succ))

/-- The reindexing of `Y` used for the membership `(z, y, p) ∈ Y`. -/
def t2 (k : ℕ) : Fin (k+2) → PSig k :=
  Fin.cons (zIx (k := k)) (Fin.cons (yIx (k := k)) (fun j : Fin k => pIx (k := k) j.succ))

/-- The body of the `PW` formula, on the big index type. -/
def PS (k : ℕ) (Y : Set (Fin (k+2) → ℝ)) : Set (PSig k → ℝ) :=
  {t | (fun i => t (t1 k i)) ∈ Y ∧ (0 : ℝ) < t (eIx (k := k)) ∧
    (t (pIx (k := k) 0) - t (eIx (k := k)) < t (zIx (k := k)) →
      t (zIx (k := k)) < t (pIx (k := k) 0) + t (eIx (k := k)) →
      (fun i => t (t2 k i)) ∈ Y)}

@[simp] lemma elim_pIx {k : ℕ} (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) (z : Fin 1 → ℝ)
    (i : Fin (k+1)) : (Sum.elim (Sum.elim p u) z) (pIx i) = p i := by simp [pIx]

@[simp] lemma elim_yIx {k : ℕ} (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) (z : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim p u) z) (yIx (k := k)) = u 0 := by simp [yIx]

@[simp] lemma elim_eIx {k : ℕ} (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) (z : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim p u) z) (eIx (k := k)) = u 1 := by simp [eIx]

@[simp] lemma elim_zIx {k : ℕ} (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) (z : Fin 1 → ℝ) :
    (Sum.elim (Sum.elim p u) z) (zIx (k := k)) = z 0 := by simp [zIx]

lemma comp_t1 (k : ℕ) (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) (z : Fin 1 → ℝ) :
    (fun i => (Sum.elim (Sum.elim p u) z) (t1 k i)) =
      Fin.cons (p 0) (Fin.cons (u 0) (Fin.tail p)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

lemma comp_t2 (k : ℕ) (p : Fin (k+1) → ℝ) (u : Fin 2 → ℝ) (z : Fin 1 → ℝ) :
    (fun i => (Sum.elim (Sum.elim p u) z) (t2 k i)) =
      Fin.cons (z 0) (Fin.cons (u 0) (Fin.tail p)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

/-- `PS k Y` is `∅`-definable. -/
theorem PS_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (PS k Y) := by
  have hA1 : (∅ : Set ℝ).Definable LRc
      {t : PSig k → ℝ | (fun i => t (t1 k i)) ∈ Y} := by
    have h := hY.preimage_comp (t1 k)
    convert h using 1
    ext t
    simp [Function.comp_def]
  have hA2 : (∅ : Set ℝ).Definable LRc {t : PSig k → ℝ | (0 : ℝ) < t (eIx (k := k))} :=
    definable_lt_const_left (eIx (k := k))
  have hA3a : (∅ : Set ℝ).Definable LRc
      {t : PSig k → ℝ | t (pIx (k := k) 0) - t (eIx (k := k)) < t (zIx (k := k))} :=
    definable_lt_sub (pIx (k := k) 0) (eIx (k := k)) (zIx (k := k))
  have hA3b : (∅ : Set ℝ).Definable LRc
      {t : PSig k → ℝ | t (zIx (k := k)) < t (pIx (k := k) 0) + t (eIx (k := k))} :=
    definable_lt_add (zIx (k := k)) (pIx (k := k) 0) (eIx (k := k))
  have hA3c : (∅ : Set ℝ).Definable LRc
      {t : PSig k → ℝ | (fun i => t (t2 k i)) ∈ Y} := by
    have h := hY.preimage_comp (t2 k)
    convert h using 1
    ext t
    simp [Function.comp_def]
  have hA3 : (∅ : Set ℝ).Definable LRc
      {t : PSig k → ℝ | t (pIx (k := k) 0) - t (eIx (k := k)) < t (zIx (k := k)) →
        t (zIx (k := k)) < t (pIx (k := k) 0) + t (eIx (k := k)) →
        (fun i => t (t2 k i)) ∈ Y} := by
    have h := (hA3a.compl.union hA3b.compl).union hA3c
    convert h using 1
    ext t
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    tauto
  have h := (hA1.inter hA2).inter hA3
  convert h using 1
  ext t
  simp only [PS, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- The identification of `PW Y` with the quantifier block applied to `PS k Y`. -/
lemma PW_eq (k : ℕ) (Y : Set (Fin (k+2) → ℝ)) :
    PW Y = {p : Fin (k+1) → ℝ | ∃ u : Fin 2 → ℝ, ∀ z : Fin 1 → ℝ,
      Sum.elim (Sum.elim p u) z ∈ PS k Y} := by
  ext p
  simp only [PW, PS, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ε, hε, hmem, hgerm⟩
    refine ⟨![y, ε], fun z => ⟨?_, ?_, ?_⟩⟩
    · rw [comp_t1]
      simpa using hmem
    · simpa using hε
    · intro h1 h2
      have := hgerm (z 0) (by simpa using h1) (by simpa using h2)
      rw [comp_t2]
      simpa using this
  · rintro ⟨u, hu⟩
    refine ⟨u 0, u 1, ?_, ?_, ?_⟩
    · simpa using (hu 0).2.1
    · have h := (hu 0).1
      rw [comp_t1] at h
      simpa using h
    · intro z h1 h2
      have h := (hu (fun _ : Fin 1 => z)).2.2 (by simpa using h1) (by simpa using h2)
      rw [comp_t2] at h
      simpa using h

/-- **`PW Y` is `∅`-definable.** -/
theorem pw_definable {k : ℕ} {Y : Set (Fin (k+2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (PW Y) := by
  have hS := PS_definable (k := k) hY
  have h1 : (∅ : Set ℝ).Definable LRc
      {t : (Fin (k+1) ⊕ Fin 2) → ℝ | ∀ z : Fin 1 → ℝ, Sum.elim t z ∈ PS k Y} :=
    hS.forall_of_finite (α := Fin (k+1) ⊕ Fin 2) (β := Fin 1)
  have h2 : (∅ : Set ℝ).Definable LRc
      {p : Fin (k+1) → ℝ | ∃ u : Fin 2 → ℝ,
        Sum.elim p u ∈ {t : (Fin (k+1) ⊕ Fin 2) → ℝ | ∀ z : Fin 1 → ℝ,
          Sum.elim t z ∈ PS k Y}} :=
    h1.exists_of_finite (α := Fin (k+1)) (β := Fin 2)
  rw [PW_eq k Y]
  exact h2

end Work.WilC4
