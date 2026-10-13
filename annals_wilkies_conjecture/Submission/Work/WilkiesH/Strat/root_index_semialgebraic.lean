import Mathlib
import Submission.Work.WilkiesH.Tarski.definable_iff_polynomialSignSet
import Submission.Work.WilkiesI.Basic

/-!
# The root-index set of a polynomial family is semialgebraic

Let `P : MvPolynomial (Fin (m+1)) ℝ` and write a point `z : Fin (m+1) → ℝ` as
`z = Fin.snoc w y` with `w = Fin.init z` and `y = z (Fin.last m)`.  Consider the set

`{z | P z = 0 ∧ #{s < y : P (Fin.snoc w s) = 0} = j}`,

i.e. the family `s ↦ P (Fin.snoc w s)` has exactly `j` real roots below the last
coordinate of `z`.  The statement proved here is the equivalent "enumerated" form: the set
of `z` for which there is a strictly increasing `t : Fin j → ℝ` whose range is exactly the
set of roots of `P (Fin.snoc w ·)` below `y`.

This set is definable in the language of rings over `ℝ` (hence semialgebraic) by pure
first-order logic: the outer `∃ t` is a quantifier over the finite product `ℝ^j`, the inner
`∀ s` a quantifier over the single real `ℝ`, and the remaining conditions are polynomial
equalities and inequalities.  No quantifier elimination (Tarski–Seidenberg) is needed.

## Implementation

The ambient space for the "open" formula is `riIdx m j = (Fin (m+1) ⊕ Fin j) ⊕ Fin 1`,
reading off

* `z` on `riZ i = Sum.inl (Sum.inl i)`,
* the enumeration `t` on `riT i = Sum.inl (Sum.inr i)`,
* the universally quantified real `s` on `riS = Sum.inr 0`.

The substitution `Fin.snoc (Fin.init z) (t i)` is presented as an index map
`riSub i : Fin (m+1) → riIdx m j` (and `riSubS` for the `s`-substitution), so that
precomposition with it is `preimage_comp`; the identities `ri_elim_comp_riSub` and
`ri_elim_comp_riSubS` identify it with `Fin.snoc`.  `riGoodSet` is the corresponding
sub-basic definable set; `ri_goodSet_definable` shows it is definable, and
`riW1`/`riW2` eliminate the `∀` and `∃` quantifiers with
`Set.Definable.forall_of_finite` / `exists_of_finite`.
-/

namespace Work.WilkiesH.Strat

open Classical
open FirstOrder FirstOrder.Language

set_option autoImplicit false

/-- Ambient index type: `m + 1` point coordinates, `j` candidate roots, one extra real. -/
abbrev riIdx (m j : ℕ) := (Fin (m + 1) ⊕ Fin j) ⊕ Fin 1

/-- The `i`-th point coordinate. -/
def riZ {m j : ℕ} (i : Fin (m + 1)) : riIdx m j := Sum.inl (Sum.inl i)

/-- The `i`-th candidate root. -/
def riT {m j : ℕ} (i : Fin j) : riIdx m j := Sum.inl (Sum.inr i)

/-- The extra real (the universally quantified `s`). -/
def riS {m j : ℕ} : riIdx m j := Sum.inr 0

/-- The substitution `Fin.snoc (Fin.init z) (t i)` as an index map. -/
def riSub {m j : ℕ} (i : Fin j) : Fin (m + 1) → riIdx m j :=
  Fin.snoc (fun a => Sum.inl (Sum.inl (Fin.castSucc a))) (Sum.inl (Sum.inr i))

/-- The substitution `Fin.snoc (Fin.init z) s` as an index map. -/
def riSubS {m j : ℕ} : Fin (m + 1) → riIdx m j :=
  Fin.snoc (fun a => Sum.inl (Sum.inl (Fin.castSucc a))) (riS (m := m) (j := j))

@[simp] lemma ri_init_apply {m : ℕ} {σ : Type*} (z : Fin (m + 1) → σ) (c : Fin m) :
    Fin.init z c = z c.castSucc := rfl

lemma ri_mem_himp {α : Type*} {s t : Set α} {x : α} : x ∈ s ⇨ t ↔ (x ∈ s → x ∈ t) := by
  rw [himp_eq]
  change x ∈ t ∪ sᶜ ↔ (x ∈ s → x ∈ t)
  rw [Set.mem_union, Set.mem_compl_iff]
  tauto

/-- A finite-order `StrictMono` set is definable. -/
lemma ri_definable_strictMono (j : ℕ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring {t : Fin j → ℝ | StrictMono t} := by
  have h : {t : Fin j → ℝ | StrictMono t}
      = ⋂ a : Fin j, ⋂ b : Fin j, {t : Fin j → ℝ | a < b → t a < t b} := by
    ext t
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro ht p q hpq; exact ht hpq
    · intro ht p q hpq; exact ht p q hpq
  rw [h]
  refine Set.definable_iInter_of_finite fun a => Set.definable_iInter_of_finite fun b => ?_
  by_cases hab : a < b
  · have h2 : {t : Fin j → ℝ | a < b → t a < t b} = {t : Fin j → ℝ | t a < t b} := by
      ext t; simp [hab]
    rw [h2]
    have h3 : {t : Fin j → ℝ | t a < t b}
        = {t : Fin j → ℝ | (MvPolynomial.eval t) (MvPolynomial.X a - MvPolynomial.X b) < 0} := by
      ext t; simp [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_neg]
    rw [h3]
    exact Work.WilkiesI.definable_eval_lt _ 0
  · have h2 : {t : Fin j → ℝ | a < b → t a < t b} = Set.univ := by
      ext t; simp [hab]
    rw [h2]; exact Set.definable_univ

lemma ri_elim_apply_riZ {m j : ℕ} {z : Fin (m + 1) → ℝ} {t : Fin j → ℝ} {u : Fin 1 → ℝ}
    (i : Fin (m + 1)) : Sum.elim (Sum.elim z t) u (riZ i) = z i := by simp [riZ]

lemma ri_elim_apply_riT {m j : ℕ} {z : Fin (m + 1) → ℝ} {t : Fin j → ℝ} {u : Fin 1 → ℝ}
    (i : Fin j) : Sum.elim (Sum.elim z t) u (riT i) = t i := by simp [riT]

lemma ri_elim_apply_riS {m j : ℕ} {z : Fin (m + 1) → ℝ} {t : Fin j → ℝ} {u : Fin 1 → ℝ} :
    Sum.elim (Sum.elim z t) u (riS (m := m) (j := j)) = u 0 := by simp [riS]

lemma ri_elim_comp_riT {m j : ℕ} {z : Fin (m + 1) → ℝ} {t : Fin j → ℝ} {u : Fin 1 → ℝ} :
    Sum.elim (Sum.elim z t) u ∘ riT (m := m) (j := j) = t := by
  funext i; simp [ri_elim_apply_riT]

lemma ri_elim_comp_riSub {m j : ℕ} {z : Fin (m + 1) → ℝ} {t : Fin j → ℝ} {u : Fin 1 → ℝ}
    (i : Fin j) : Sum.elim (Sum.elim z t) u ∘ riSub i = Fin.snoc (Fin.init z) (t i) := by
  funext a
  rcases Fin.eq_castSucc_or_eq_last a with ⟨c, rfl⟩ | rfl
  · simp [riSub]
  · simp [riSub]

lemma ri_elim_comp_riSubS {m j : ℕ} {z : Fin (m + 1) → ℝ} {t : Fin j → ℝ} {u : Fin 1 → ℝ} :
    Sum.elim (Sum.elim z t) u ∘ riSubS (m := m) (j := j) = Fin.snoc (Fin.init z) (u 0) := by
  funext a
  rcases Fin.eq_castSucc_or_eq_last a with ⟨c, rfl⟩ | rfl
  · simp [riSubS]
  · simp [riSubS, riS]

/-- The sub-basic set of tuples `(z, t, s)` satisfying the conjunction of the root conditions:
`StrictMono t`, all `t i < z (Fin.last m)` are roots, and `s` is a root below
`z (Fin.last m)` only if `s` is one of the `t i`. -/
def riGoodSet (j : ℕ) {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) : Set (riIdx m j → ℝ) :=
  {g : riIdx m j → ℝ | StrictMono (g ∘ riT (m := m) (j := j))} ∩
    ((⋂ i : Fin j, {g : riIdx m j → ℝ | g (riT i) < g (riZ (Fin.last m))} ∩
      ((fun g : riIdx m j → ℝ => g ∘ riSub i) ⁻¹'
        {y : Fin (m + 1) → ℝ | MvPolynomial.eval y P = 0})) ∩
     ({g : riIdx m j → ℝ | g (riS (m := m) (j := j)) < g (riZ (Fin.last m))} ⇨
      (((fun g : riIdx m j → ℝ => g ∘ riSubS (m := m) (j := j)) ⁻¹'
          {y : Fin (m + 1) → ℝ | MvPolynomial.eval y P = 0}) ⇨
        (⋃ i : Fin j, {g : riIdx m j → ℝ | g (riS (m := m) (j := j)) = g (riT i)}))))

/-- The `s`-quantifier is eliminated. -/
def riW1 (j : ℕ) {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) :
    Set ((Fin (m + 1) ⊕ Fin j) → ℝ) :=
  {v | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ riGoodSet j P}

/-- The `t`-quantifier is eliminated. -/
def riW2 (j : ℕ) {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) : Set (Fin (m + 1) → ℝ) :=
  {v | ∃ u : Fin j → ℝ, Sum.elim v u ∈ riW1 j P}

lemma ri_goodSet_definable {m j : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring (riGoodSet j P) := by
  simp only [riGoodSet]
  refine Set.Definable.inter ?_ (Set.Definable.inter ?_ ?_)
  · exact (ri_definable_strictMono j).preimage_comp (riT (m := m) (j := j))
  · refine Set.definable_iInter_of_finite fun i => Set.Definable.inter ?_ ?_
    · have h3 : {g : riIdx m j → ℝ | g (riT i) < g (riZ (Fin.last m))}
          = {g : riIdx m j → ℝ | (MvPolynomial.eval g)
              (MvPolynomial.X (riT i) - MvPolynomial.X (riZ (Fin.last m))) < 0} := by
        ext g; simp [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_neg]
      rw [h3]
      exact Work.WilkiesI.definable_eval_lt _ 0
    · exact (Work.WilkiesI.definable_eval_eq P 0).preimage_comp (riSub i)
  · refine Set.Definable.himp ?_ (Set.Definable.himp ?_ ?_)
    · have h3 : {g : riIdx m j → ℝ | g (riS (m := m) (j := j)) < g (riZ (Fin.last m))}
          = {g : riIdx m j → ℝ | (MvPolynomial.eval g)
              (MvPolynomial.X (riS (m := m) (j := j)) - MvPolynomial.X (riZ (Fin.last m))) < 0} := by
        ext g; simp [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_neg]
      rw [h3]
      exact Work.WilkiesI.definable_eval_lt _ 0
    · exact (Work.WilkiesI.definable_eval_eq P 0).preimage_comp (riSubS (m := m) (j := j))
    · refine Set.definable_iUnion_of_finite fun i => ?_
      have h3 : {g : riIdx m j → ℝ | g (riS (m := m) (j := j)) = g (riT i)}
          = {g : riIdx m j → ℝ | (MvPolynomial.eval g)
              (MvPolynomial.X (riS (m := m) (j := j)) - MvPolynomial.X (riT i)) = 0} := by
        ext g; simp [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_eq_zero]
      rw [h3]
      exact Work.WilkiesI.definable_eval_eq _ 0

/-- Membership in `riGoodSet`, in coordinates. -/
lemma ri_mem_goodSet {m j : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ)
    (z : Fin (m + 1) → ℝ) (t : Fin j → ℝ) (u : Fin 1 → ℝ) :
    Sum.elim (Sum.elim z t) u ∈ riGoodSet j P ↔
      StrictMono t ∧
      (∀ i, t i < z (Fin.last m) ∧
        MvPolynomial.eval (Fin.snoc (Fin.init z) (t i)) P = 0) ∧
      (u 0 < z (Fin.last m) →
        MvPolynomial.eval (Fin.snoc (Fin.init z) (u 0)) P = 0 → ∃ i, u 0 = t i) := by
  simp only [riGoodSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_preimage, ri_mem_himp, ri_elim_comp_riT, ri_elim_apply_riT,
    ri_elim_apply_riZ, ri_elim_apply_riS, ri_elim_comp_riSub, ri_elim_comp_riSubS]

theorem root_index_semialgebraic {m j : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) :
    WilkiesConjecture.IsSemialgebraic
      {z : Fin (m + 1) → ℝ |
        MvPolynomial.eval z P = 0 ∧
        (∃ t : Fin j → ℝ, StrictMono t ∧
          (∀ i, t i < z (Fin.last m) ∧
            MvPolynomial.eval (Fin.snoc (Fin.init z) (t i)) P = 0) ∧
          (∀ s : ℝ, s < z (Fin.last m) →
            MvPolynomial.eval (Fin.snoc (Fin.init z) s) P = 0 → ∃ i, s = t i))} := by
  have hW₁ : Set.Definable (Set.univ : Set ℝ) Language.ring (riW1 j P) :=
    (ri_goodSet_definable P).forall_of_finite
  have hW₂ : Set.Definable (Set.univ : Set ℝ) Language.ring (riW2 j P) := hW₁.exists_of_finite
  have hZ : Set.Definable (Set.univ : Set ℝ) Language.ring
      {z : Fin (m + 1) → ℝ | MvPolynomial.eval z P = 0} := Work.WilkiesI.definable_eval_eq P 0
  have hfin : Set.Definable (Set.univ : Set ℝ) Language.ring
      ({z : Fin (m + 1) → ℝ | MvPolynomial.eval z P = 0} ∩ riW2 j P) := hZ.inter hW₂
  have hEq : {z : Fin (m + 1) → ℝ |
        MvPolynomial.eval z P = 0 ∧
        (∃ t : Fin j → ℝ, StrictMono t ∧
          (∀ i, t i < z (Fin.last m) ∧
            MvPolynomial.eval (Fin.snoc (Fin.init z) (t i)) P = 0) ∧
          (∀ s : ℝ, s < z (Fin.last m) →
            MvPolynomial.eval (Fin.snoc (Fin.init z) s) P = 0 → ∃ i, s = t i))}
      = {z : Fin (m + 1) → ℝ | MvPolynomial.eval z P = 0} ∩ riW2 j P := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, riW2, riW1]
    constructor
    · rintro ⟨hzP, t, hmono, hroot, hsurj⟩
      exact ⟨hzP, t, fun u => (ri_mem_goodSet P z t u).mpr
        ⟨hmono, hroot, fun hu hv => hsurj (u 0) hu hv⟩⟩
    · rintro ⟨hzP, t, ht⟩
      refine ⟨hzP, t, ((ri_mem_goodSet P z t (fun _ => 0)).mp (ht (fun _ => 0))).1, ?_, ?_⟩
      · exact ((ri_mem_goodSet P z t (fun _ => 0)).mp (ht (fun _ => 0))).2.1
      · intro s hs hv
        exact ((ri_mem_goodSet P z t (fun _ => s)).mp (ht (fun _ => s))).2.2 hs hv
  rw [WilkiesConjecture.IsSemialgebraic, hEq]
  exact hfin

end Work.WilkiesH.Strat
