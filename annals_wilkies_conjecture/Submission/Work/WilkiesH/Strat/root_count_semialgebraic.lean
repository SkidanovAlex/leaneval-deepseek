import Mathlib
import Submission.Work.WilkiesH.Strat.root_index_semialgebraic
import Submission.Work.WilkiesI.Basic

/-!
# The set of parameters whose fibre has exactly `m` real roots is semialgebraic

Let `P : MvPolynomial (Fin (μ+1)) ℝ` and consider the univariate polynomial
`s ↦ P (Fin.snoc u s)` obtained by fixing `u : Fin μ → ℝ` in the first `μ` variables.
The set

`{u : Fin μ → ℝ | ∃ t : Fin m → ℝ, StrictMono t ∧ (∀ i, P (Fin.snoc u (t i)) = 0) ∧
    (∀ s, P (Fin.snoc u s) = 0 → ∃ i, s = t i)}`

consists of those `u` for which the roots of this fibre are *exactly* the (strictly increasing)
enumeration `t`.  This file proves it is definable in the language of rings over `ℝ` (hence
semialgebraic) again by pure first-order logic: `∃ t` quantifies over the finite product
`ℝ^m`, `∀ s` over a single real, and the remaining conditions are polynomial equalities.

## Implementation

Ambient index type `rcIdx μ m = (Fin μ ⊕ Fin m) ⊕ Fin 1`, reading off

* the parameter `u` on `rcU a = Sum.inl (Sum.inl a)`,
* the enumeration `t` on `rcT i = Sum.inl (Sum.inr i)`,
* the universally quantified real `s` on `rcS = Sum.inr 0`.

The substitution `Fin.snoc u (t i)` is `rcSub i : Fin (μ+1) → rcIdx μ m` (and `rcSubS` for
`Fin.snoc u (s 0)`), so that precomposition with it is `Set.Definable.preimage_comp`; the
identities `rc_elim_comp_rcSub` and `rc_elim_comp_rcSubS` identify it with `Fin.snoc`.
`rcGoodSet` is the sub-basic definable set, `rc_goodSet_definable` shows it is definable, and
`rcW1`/`rcW2` eliminate the `∀`/`∃` quantifiers with
`Set.Definable.forall_of_finite` / `Set.Definable.exists_of_finite`.
-/

namespace Work.WilkiesH.Strat

open Classical
open FirstOrder FirstOrder.Language

set_option autoImplicit false

/-- Ambient index type: `μ` parameter coordinates, `m` candidate roots, one extra real. -/
abbrev rcIdx (μ m : ℕ) := (Fin μ ⊕ Fin m) ⊕ Fin 1

/-- The `a`-th parameter coordinate. -/
def rcU {μ m : ℕ} (a : Fin μ) : rcIdx μ m := Sum.inl (Sum.inl a)

/-- The `i`-th candidate root. -/
def rcT {μ m : ℕ} (i : Fin m) : rcIdx μ m := Sum.inl (Sum.inr i)

/-- The extra real (the universally quantified `s`). -/
def rcS {μ m : ℕ} : rcIdx μ m := Sum.inr 0

/-- The substitution `Fin.snoc u (t i)` as an index map. -/
def rcSub {μ m : ℕ} (i : Fin m) : Fin (μ + 1) → rcIdx μ m :=
  Fin.snoc (fun a : Fin μ => rcU (m := m) a) (rcT i)

/-- The substitution `Fin.snoc u (s 0)` as an index map. -/
def rcSubS {μ m : ℕ} : Fin (μ + 1) → rcIdx μ m :=
  Fin.snoc (fun a : Fin μ => rcU (m := m) a) (rcS (μ := μ) (m := m))

/-- The sub-basic set of tuples `(u, t, s)` satisfying the root conditions: `StrictMono t`,
each `t i` is a root, and `s` is a root only if `s` is one of the `t i`. -/
def rcGoodSet (μ m : ℕ) (P : MvPolynomial (Fin (μ + 1)) ℝ) : Set (rcIdx μ m → ℝ) :=
  {g : rcIdx μ m → ℝ | StrictMono (g ∘ rcT (μ := μ) (m := m))} ∩
    ((⋂ i : Fin m, ((fun g : rcIdx μ m → ℝ => g ∘ rcSub i) ⁻¹'
        {y : Fin (μ + 1) → ℝ | MvPolynomial.eval y P = 0})) ∩
     (((fun g : rcIdx μ m → ℝ => g ∘ rcSubS (μ := μ) (m := m)) ⁻¹'
        {y : Fin (μ + 1) → ℝ | MvPolynomial.eval y P = 0}) ⇨
       (⋃ i : Fin m, {g : rcIdx μ m → ℝ | g (rcS (μ := μ) (m := m)) = g (rcT i)})))

/-- The `s`-quantifier is eliminated. -/
def rcW1 (μ m : ℕ) (P : MvPolynomial (Fin (μ + 1)) ℝ) : Set ((Fin μ ⊕ Fin m) → ℝ) :=
  {v | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ rcGoodSet μ m P}

/-- The `t`-quantifier is eliminated. -/
def rcW2 (μ m : ℕ) (P : MvPolynomial (Fin (μ + 1)) ℝ) : Set (Fin μ → ℝ) :=
  {v | ∃ u : Fin m → ℝ, Sum.elim v u ∈ rcW1 μ m P}

lemma rc_elim_apply_rcT {μ m : ℕ} {u : Fin μ → ℝ} {t : Fin m → ℝ} {s : Fin 1 → ℝ}
    (i : Fin m) : Sum.elim (Sum.elim u t) s (rcT i) = t i := by simp [rcT]

lemma rc_elim_apply_rcS {μ m : ℕ} {u : Fin μ → ℝ} {t : Fin m → ℝ} {s : Fin 1 → ℝ} :
    Sum.elim (Sum.elim u t) s (rcS (μ := μ) (m := m)) = s 0 := by simp [rcS]

lemma rc_elim_comp_rcT {μ m : ℕ} {u : Fin μ → ℝ} {t : Fin m → ℝ} {s : Fin 1 → ℝ} :
    Sum.elim (Sum.elim u t) s ∘ rcT (μ := μ) (m := m) = t := by
  funext i; simp [rc_elim_apply_rcT]

lemma rc_elim_comp_rcSub {μ m : ℕ} {u : Fin μ → ℝ} {t : Fin m → ℝ} {s : Fin 1 → ℝ}
    (i : Fin m) : Sum.elim (Sum.elim u t) s ∘ rcSub i = Fin.snoc u (t i) := by
  funext a
  rcases Fin.eq_castSucc_or_eq_last a with ⟨c, rfl⟩ | rfl
  · simp [rcSub, rcU]
  · simp [rcSub, rcT]

lemma rc_elim_comp_rcSubS {μ m : ℕ} {u : Fin μ → ℝ} {t : Fin m → ℝ} {s : Fin 1 → ℝ} :
    Sum.elim (Sum.elim u t) s ∘ rcSubS (μ := μ) (m := m) = Fin.snoc u (s 0) := by
  funext a
  rcases Fin.eq_castSucc_or_eq_last a with ⟨c, rfl⟩ | rfl
  · simp [rcSubS, rcU]
  · simp [rcSubS, rcS]

lemma rc_goodSet_definable {μ m : ℕ} (P : MvPolynomial (Fin (μ + 1)) ℝ) :
    Set.Definable (Set.univ : Set ℝ) Language.ring (rcGoodSet μ m P) := by
  simp only [rcGoodSet]
  refine Set.Definable.inter ?_ (Set.Definable.inter ?_ ?_)
  · exact (ri_definable_strictMono m).preimage_comp (rcT (μ := μ) (m := m))
  · refine Set.definable_iInter_of_finite fun i => ?_
    exact (Work.WilkiesI.definable_eval_eq P 0).preimage_comp (rcSub i)
  · refine Set.Definable.himp ?_ ?_
    · exact (Work.WilkiesI.definable_eval_eq P 0).preimage_comp (rcSubS (μ := μ) (m := m))
    · refine Set.definable_iUnion_of_finite fun i => ?_
      have h3 : {g : rcIdx μ m → ℝ | g (rcS (μ := μ) (m := m)) = g (rcT i)}
          = {g : rcIdx μ m → ℝ | (MvPolynomial.eval g)
              (MvPolynomial.X (rcS (μ := μ) (m := m)) - MvPolynomial.X (rcT i)) = 0} := by
        ext g; simp [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_eq_zero]
      rw [h3]
      exact Work.WilkiesI.definable_eval_eq _ 0

/-- Membership in `rcGoodSet`, in coordinates. -/
lemma rc_mem_goodSet {μ m : ℕ} (P : MvPolynomial (Fin (μ + 1)) ℝ)
    (u : Fin μ → ℝ) (t : Fin m → ℝ) (s : Fin 1 → ℝ) :
    Sum.elim (Sum.elim u t) s ∈ rcGoodSet μ m P ↔
      StrictMono t ∧
      (∀ i, MvPolynomial.eval (Fin.snoc u (t i)) P = 0) ∧
      (MvPolynomial.eval (Fin.snoc u (s 0)) P = 0 → ∃ i, s 0 = t i) := by
  simp only [rcGoodSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_preimage, ri_mem_himp, rc_elim_comp_rcT, rc_elim_apply_rcS, rc_elim_apply_rcT,
    rc_elim_comp_rcSub, rc_elim_comp_rcSubS]

theorem root_count_semialgebraic {μ : ℕ} (P : MvPolynomial (Fin (μ + 1)) ℝ) (m : ℕ) :
    WilkiesConjecture.IsSemialgebraic
      {u : Fin μ → ℝ | ∃ t : Fin m → ℝ, StrictMono t ∧
        (∀ i, MvPolynomial.eval (Fin.snoc u (t i)) P = 0) ∧
        (∀ s : ℝ, MvPolynomial.eval (Fin.snoc u s) P = 0 → ∃ i, s = t i)} := by
  have hW₁ : Set.Definable (Set.univ : Set ℝ) Language.ring (rcW1 μ m P) :=
    (rc_goodSet_definable (μ := μ) (m := m) P).forall_of_finite
  have hW₂ : Set.Definable (Set.univ : Set ℝ) Language.ring (rcW2 μ m P) :=
    hW₁.exists_of_finite
  have hEq : {u : Fin μ → ℝ | ∃ t : Fin m → ℝ, StrictMono t ∧
        (∀ i, MvPolynomial.eval (Fin.snoc u (t i)) P = 0) ∧
        (∀ s : ℝ, MvPolynomial.eval (Fin.snoc u s) P = 0 → ∃ i, s = t i)}
      = rcW2 μ m P := by
    ext u
    simp only [Set.mem_ofPred_eq, rcW2, rcW1]
    constructor
    · rintro ⟨t, hmono, hroot, hsurj⟩
      exact ⟨t, fun s => (rc_mem_goodSet P u t s).mpr ⟨hmono, hroot, fun h0 => hsurj (s 0) h0⟩⟩
    · rintro ⟨t, ht⟩
      have h0 := (rc_mem_goodSet P u t (fun _ => (0 : ℝ))).mp (ht (fun _ => 0))
      exact ⟨t, h0.1, h0.2.1, fun s hs =>
        ((rc_mem_goodSet P u t (fun _ => s)).mp (ht (fun _ => s))).2.2 hs⟩
  rw [WilkiesConjecture.IsSemialgebraic, hEq]
  exact hW₂

end Work.WilkiesH.Strat
