/-
  WilC4/badScale_aux : the vocabulary of a **self-contained** proof that the relation
  `{(M, ε) | M ∈ Work.WilC4.BadScale Y B E ε}` is `∅`-definable in `LRc`.

  `BadScale Y B E ε` is

    `{M | 0 < M ∧ ∃ (c : Fin k → ℝ) (x w : ℝ), 0 < x ∧ IsDeepR B c M x ∧ RatW Y c x w ∧
          ∀ ρ ∈ E, 0 < ρ → ε < |w / ρ - 1|}`.

  Reading it as a formula, the free variables are `(M, ε) : ℝ²` and the bound ones are
  `(c, x, w)`, with two inner sub-formulae whose quantified objects are again real numbers
  (`b`, and the quotient `x / (2M)` for the deepness; `ρ`, and the quotient `w / ρ` for the
  failure clause).

  ## Index bookkeeping

  * `BSPar k = Fin k ⊕ Fin 2` carries `(c, x, w)`, so that the outer `∃ (c,x,w)` is the *finite*
    existential quantifier `Set.Definable.exists_of_finite` over the second summand of
    `BSI k = Fin 2 ⊕ BSPar k`; the first summand `Fin 2` carries the free pair `(M, ε)`.
  * `BSD k = BSI k ⊕ Fin 2` is the ambient index of the deepness body (`b` in slot `Sum.inr 0`,
    the quotient `x/(2M)` in slot `Sum.inr 1`);
  * `BSR k = BSI k ⊕ Fin 3` is the ambient index of the ratio body (`y` in `Sum.inr 0`,
    `y'` in `Sum.inr 1`, and the auxiliary `z = 2x` in `Sum.inr 2`);
  * `BSC k = BSI k ⊕ Fin 2` is the ambient index of the failure/cluster body (`ρ` in `Sum.inr 0`,
    the quotient `w/ρ` in `Sum.inr 1`).

  Each body is written with *every* quantified variable free, so that it is a quantifier-free set
  of tuples; the projection lemmas `BSDeep`, `BSRatW`, `BSSpec` then reintroduce the quantifiers
  through `Set.Definable.forall_of_finite` / `Set.Definable.exists_of_finite`.

  ## IMPORTANT (do not import the `DevBdd` vocabulary chain)

  This development is deliberately *self-contained*: it must **not** import
  `Submission.Work.WilC4.DevBddDefs`, `DevBdd_definable`, `DevDeep_definable`,
  `DevRatW_definable`, `DevConc_definable`, `dev_rate` or `dev_rate_devBdd`.  The public index
  abbreviations `dc dx dw dy` of `DevBddDefs` (typed `DevI k → ℝ`) collide with the public
  abbreviations of the same name declared in `Submission.Work.WilC4.DeepThetaGDefs` (typed
  `DRIdx k → ℝ`), and `DeepThetaGDefs` lies in the import closure of `deep_ratio_bdd` /
  `dev_decay_E`; a module importing both chains cannot elaborate.  Modules importing this file
  should therefore import *only* this file (plus `Mathlib`); the `DevBdd` files may of course be
  *read* as a template — the proofs of `DevBdd_definable` are the exact analogues of the lemmas
  requested here, with the index types of `DevBddDefs` replaced by the ones below.

  What is available for the proofs below (all in the import closure of this file):

  * the arithmetic atoms of `Submission/Work/WilC4/DiagDefs.lean`:
    `definable_isDivR`, `definable_eval_eq_LRc`, `definable_le_LRc`, `definable_ne_LRc`,
    `GrSub1`, `GrSub1_definable`, `IsDivR`, `isDivR_iff`, `definable_univ_iff_empty`,
    and in the same closure `GrSub`, `GrSub_definable`, `real_definable_le`,
    `real_definable_lt`, `definable_lt_const`, `definable_eq_add` (from
    `Submission/Work/WilC4/crit_def_bad_aux.lean`);
  * the polynomial division atom `definable_isDivR_poly` copied below (the one of
    `WilC4/CandBody_definable.lean`, under a fresh name) for the occurrence
    `IsDivR (g sx) (2 * g sM) q₁`, whose denominator is not a slot.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.DiagDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

namespace BSAux

variable {k : ℕ}

/-! ## 1. The index types and the slots -/

/-- The block carrying the quantified parameters `(c, x, w)` of `BadScale`. -/
abbrev BSPar (k : ℕ) := Fin k ⊕ Fin 2

/-- The full block `(M, ε, c, x, w)`: the first `Fin 2` carries `(M, ε) = (v 0, v 1)`. -/
abbrev BSI (k : ℕ) := Fin 2 ⊕ BSPar k

/-- The index block of the deepness body: `BSI k` plus `(b, x/(2M))`. -/
abbrev BSD (k : ℕ) := BSI k ⊕ Fin 2

/-- The index block of the ratio body: `BSI k` plus `(y, y', z)` with `z = 2x`. -/
abbrev BSR (k : ℕ) := BSI k ⊕ Fin 3

/-- The index block of the failure body: `BSI k` plus `(ρ, w/ρ)`. -/
abbrev BSC (k : ℕ) := BSI k ⊕ Fin 2

/-- The slot of `M = v 0`. -/
abbrev sM : BSI k := Sum.inl (0 : Fin 2)

/-- The slot of `ε = v 1`. -/
abbrev sEps : BSI k := Sum.inl (1 : Fin 2)

/-- The slot of `c i`. -/
abbrev sc (i : Fin k) : BSI k := Sum.inr (Sum.inl i)

/-- The slot of `x`. -/
abbrev sx : BSI k := Sum.inr (Sum.inr (0 : Fin 2))

/-- The slot of `w`. -/
abbrev sw : BSI k := Sum.inr (Sum.inr (1 : Fin 2))

/-- The parameter slots of `B` read in the `BSD k` context. -/
abbrev bEmb (k : ℕ) : Fin k → BSD k := fun i => Sum.inl (sc i)

/-- The parameter slots of `Y` read in the `BSR k` context (the head is unused by `GrSub`). -/
abbrev yEmb (k : ℕ) : Fin (k+1) → BSR k :=
  Fin.cons (Sum.inr (0 : Fin 3)) (fun i : Fin k => Sum.inl (sc i))

/-! ## 2. The polynomial division atom -/

/-- `IsDivR` with numerator and denominator supplied by polynomials in the free variables, and
the quotient read off from a coordinate (a copy of `CandBodyDefs.definable_isDivR_poly` under a
fresh name, so that the development does not depend on `WilC4/CandBody_definable.lean`). -/
theorem definable_isDivR_poly {σ : Type*} (A B : MvPolynomial σ ℝ) (l : σ) :
    (Set.univ : Set ℝ).Definable LRc
      {u : σ → ℝ | IsDivR ((MvPolynomial.eval u) A) ((MvPolynomial.eval u) B) (u l)} := by
  have h1 : (Set.univ : Set ℝ).Definable LRc
      ({u : σ → ℝ | (MvPolynomial.eval u) B = 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l) = 0}) :=
    (definable_eval_eq_LRc B 0).inter (definable_eval_eq_LRc (MvPolynomial.X l) 0)
  have h2 : (Set.univ : Set ℝ).Definable LRc
      ({u : σ → ℝ | (MvPolynomial.eval u) B ≠ 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l * B - A) = 0}) :=
    (definable_ne_LRc B 0).inter (definable_eval_eq_LRc (MvPolynomial.X l * B - A) 0)
  have h := h1.union h2
  have hset : ({u : σ → ℝ | (MvPolynomial.eval u) B = 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l) = 0} ∪
        ({u : σ → ℝ | (MvPolynomial.eval u) B ≠ 0} ∩
          {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l * B - A) = 0}))
      = {u : σ → ℝ | IsDivR ((MvPolynomial.eval u) A) ((MvPolynomial.eval u) B) (u l)} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, MvPolynomial.eval_X,
      MvPolynomial.eval_mul, MvPolynomial.eval_sub, IsDivR]
    constructor
    · rintro (⟨hb, hq⟩ | ⟨hb, hq⟩)
      · exact Or.inl ⟨hb, hq⟩
      · exact Or.inr ⟨hb, by linarith⟩
    · rintro (⟨hb, hq⟩ | ⟨hb, hq⟩)
      · exact Or.inl ⟨hb, hq⟩
      · exact Or.inr ⟨hb, by linarith⟩
  rw [hset] at h
  exact h

/-- `∅`-definability upgrades to `univ`-definability. -/
lemma univ_of_empty {α : Type*} {s : Set (α → ℝ)}
    (h : (∅ : Set ℝ).Definable LRc s) : (Set.univ : Set ℝ).Definable LRc s :=
  h.mono (Set.empty_subset _)

/-! ## 3. The positivity clause and the three bodies -/

/-- The clause `0 < x` of `BadScale` (the base point of the fibre is positive). -/
def BSPos : Set (BSI k → ℝ) := {g | 0 < g sx}

/-! ## 4. The three bodies -/

/-- The body of the *negation* of the deepness condition, in the `BSD k` context: `b ∈ B`,
`q₁ = x/(2M)`, `q₁ ≤ b ≤ 2 M x`, where `b` is the slot `Sum.inr 0` and `q₁` the slot
`Sum.inr 1`. -/
def BSDeepBody (B : Set (Fin (k+1) → ℝ)) : Set (BSD k → ℝ) :=
  {g | g ∈ GrSub1 B (bEmb k) (Sum.inr (0 : Fin 2)) ∧
       IsDivR (g (Sum.inl (sx : BSI k))) (2 * g (Sum.inl (sM : BSI k)))
         (g (Sum.inr (1 : Fin 2))) ∧
       g (Sum.inr (1 : Fin 2)) ≤ g (Sum.inr (0 : Fin 2)) ∧
       g (Sum.inr (0 : Fin 2)) ≤ 2 * g (Sum.inl (sM : BSI k)) * g (Sum.inl (sx : BSI k))}

/-- `g ∈ BSDeep B` is the deepness condition: the two extra variables are universally quantified. -/
def BSDeep (B : Set (Fin (k+1) → ℝ)) : Set (BSI k → ℝ) :=
  {g | ∀ u : Fin 2 → ℝ, Sum.elim g u ∉ BSDeepBody B}

/-- The body of the doubling-ratio clause `RatW Y c x w` in the `BSR k` context: the values at
`x` and at `z = 2x` are the slots `Sum.inr 0` and `Sum.inr 1`, the argument `2x` is the slot
`Sum.inr 2`. -/
def BSRatWBody (Y : Set (Fin (k+2) → ℝ)) : Set (BSR k → ℝ) :=
  {g | g ∈ GrSub Y (yEmb k) (Sum.inl (sx : BSI k)) (Sum.inr (0 : Fin 3)) ∧
       g ∈ GrSub Y (yEmb k) (Sum.inr (2 : Fin 3)) (Sum.inr (1 : Fin 3)) ∧
       g (Sum.inr (2 : Fin 3)) = 2 * g (Sum.inl (sx : BSI k)) ∧
       g (Sum.inr (0 : Fin 3)) ≠ 0 ∧
       g (Sum.inl (sw : BSI k)) * g (Sum.inr (0 : Fin 3)) = g (Sum.inr (1 : Fin 3))}

/-- `g ∈ BSRatW Y` is the doubling-ratio relation. -/
def BSRatW (Y : Set (Fin (k+2) → ℝ)) : Set (BSI k → ℝ) :=
  {g | ∃ u : Fin 3 → ℝ, Sum.elim g u ∈ BSRatWBody Y}

/-- The body of the *conclusion* clause `∃ ρ ∈ E, 0 < ρ ∧ |w/ρ - 1| ≤ ε`, in the `BSC k`
context: `ρ ∈ E`, `0 < ρ`, `q = w/ρ` and `|q - 1| ≤ ε` (written as the conjunction of the two
linear inequalities `-ε ≤ q - 1` and `q - 1 ≤ ε`), where `ρ` is the slot `Sum.inr 0` and `q` the
slot `Sum.inr 1`.

Note the direction: `BSSpec E` below is the ***complement*** of the projection of this body, so
that `g ∈ BSSpec E` means that the conclusion *fails* for every positive `ρ ∈ E`. -/
def BSConcBody (E : Set ℝ) : Set (BSC k → ℝ) :=
  {g | g (Sum.inr (0 : Fin 2)) ∈ E ∧ 0 < g (Sum.inr (0 : Fin 2)) ∧
       IsDivR (g (Sum.inl (sw : BSI k))) (g (Sum.inr (0 : Fin 2))) (g (Sum.inr (1 : Fin 2))) ∧
       -(g (Sum.inl (sEps : BSI k))) ≤ g (Sum.inr (1 : Fin 2)) - 1 ∧
       g (Sum.inr (1 : Fin 2)) - 1 ≤ g (Sum.inl (sEps : BSI k))}

/-- `g ∈ BSSpec E` is the clause `∀ ρ ∈ E, 0 < ρ → ε < |w/ρ - 1|` (`ε` being the slot
`sEps` and `w` the slot `sw`), with the auxiliary quotient universally quantified as well: it is
the complement of the projection of `BSConcBody E`, which is equivalent to the intended clause
because the quotient `q = w/ρ` is unique as soon as `ρ ≠ 0`. -/
def BSSpec (E : Set ℝ) : Set (BSI k → ℝ) :=
  {g | ∀ u : Fin 2 → ℝ, Sum.elim g u ∉ BSConcBody E}

/-- The inner set of the formula: `0 < x ∧ IsDeepR B c M x ∧ RatW Y c x w ∧` (the failure of
the specification clause), read over the block `BSI k` which carries `(M, ε, c, x, w)` with
`(M, ε)` free.  The outer existential `∃ (c,x,w)` is then the finite projection of `BSInner`
along the block `BSPar k`. -/
def BSInner (Y : Set (Fin (k+2) → ℝ)) (B : Set (Fin (k+1) → ℝ)) (E : Set ℝ) :
    Set (BSI k → ℝ) :=
  BSPos ∩ BSDeep B ∩ BSRatW Y ∩ BSSpec E

end BSAux

end Work.WilC4
