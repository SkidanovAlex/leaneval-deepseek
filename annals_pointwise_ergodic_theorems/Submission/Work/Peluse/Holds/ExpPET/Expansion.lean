import Mathlib
import Submission.Work.Peluse.Holds.ExpPET.Reindex

/-!
# The multi-slot expansion of the box sum (`ExpansionPETShort`, brick 2)

`Work.Peluse.Holds.ExpansionPETShort` expands the box sum `boxSumPow s (Q(a)) (symIcc N) f` — whose
`(h,h')`-sums run over the *dependent* products `(i : Fin s) → {x // x ∈ Q_i(a)}` with the
direction sets `Q_i(a) = (c·a + b_i)[M₁]` — and reindexes them by the *labels*
`(k,k') ∈ ([1,M₁]^s)²` via `h_i = (c·a + b_i)·k_i`, so that the `a`-dependence of each cube corner
becomes the linear phase `c·a·λ_ω` with the shift `σ_ω` (and `PetLinear.linear_boxnorm_control_paper`
applies).

This file contains the bookkeeping steps of that expansion:

* `piSuccEquiv` / `sum_pi_succ` — peeling the first coordinate off a sum over a dependent product of
  finite types (the `Fin (s+1)`-induction step);
* `prod_reindex_arithIcc` — the *reindexing identity* itself, with the per-slot cardinality
  normalisation, valid **including** the degenerate slots `κ i = 0` (where the per-slot identity is
  the "collapse" of `Reindex.sum_arithIcc_pair'`);
* `boxSumPow_arithIcc_eq` — the resulting statement for the box sum, with the cube term written in
  the `expCube` vocabulary of `ExpPET/Defs.lean` (via `prod_cubeTerm_mul_eq_expCube`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Peluse.Holds.ExpPET

open Work.Peluse

/-- The product decomposition of a dependent function on `Fin (s+1)` into its value at `0` and its
tail. -/
def piSuccEquiv (s : ℕ) (β : Fin (s + 1) → Type*) :
    ((i : Fin (s + 1)) → β i) ≃ β 0 × ((i : Fin s) → β i.succ) :=
  { toFun := fun g => (g 0, fun i => g i.succ)
    invFun := fun p => Fin.cons p.1 p.2
    left_inv := fun g => Fin.cons_self_tail g
    right_inv := fun p => by
      obtain ⟨b, g'⟩ := p
      simp [Fin.cons_zero, Fin.cons_succ] }

@[simp] lemma piSuccEquiv_apply (s : ℕ) (β : Fin (s + 1) → Type*)
    (g : (i : Fin (s + 1)) → β i) :
    piSuccEquiv s β g = (g 0, fun i : Fin s => g i.succ) := rfl

/-- **Peeling the first coordinate** off a sum over a dependent product indexed by `Fin (s+1)`. -/
lemma sum_pi_succ {s : ℕ} {β : Fin (s + 1) → Type*} [∀ i, Fintype (β i)]
    {M : Type*} [AddCommMonoid M] (Ψ : ((i : Fin (s + 1)) → β i) → M) :
    (∑ g : (i : Fin (s + 1)) → β i, Ψ g)
      = ∑ b : β 0, ∑ g' : (i : Fin s) → β i.succ, Ψ (Fin.cons b g') := by
  classical
  rw [Fintype.sum_equiv (piSuccEquiv s β) (fun g => Ψ g) (fun p => Ψ (Fin.cons p.1 p.2)) ?_]
  · rw [Fintype.sum_prod_type]
  · intro g
    rw [piSuccEquiv_apply]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp

/-- The per-slot reindexing identity of `Reindex.sum_arithIcc_pair'`, in the *subtype* form in which
the box sum's `(h,h')`-averages are written (`prodCubeSum` sums over
`(i : Fin s) → {x // x ∈ Q i}` rather than over `Finset`s).  The labels are the subtype of
`Finset.Icc 1 M₁` in `ℕ`, matching the definition of `arithIcc`. -/
lemma sum_subtype_arithIcc_pair (κ : ℤ) {M₁ : ℕ} (hM₁ : 1 ≤ M₁) (φ : ℤ → ℤ → ℂ) :
    (((Work.Peluse.arithIcc κ M₁).card : ℂ))⁻¹ ^ 2
        * ∑ h : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁},
            ∑ h' : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁}, φ h.1 h'.1
      = (((M₁ : ℂ)))⁻¹ ^ 2
        * ∑ k : {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : {n : ℕ // n ∈ Finset.Icc 1 M₁}, φ (κ * ((k.1 : ℕ) : ℤ)) (κ * ((k'.1 : ℕ) : ℤ)) := by
  classical
  have hinner : ∀ z : ℤ,
      (∑ h' : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁}, φ z h'.1)
        = ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ z h' :=
    fun z => (Finset.sum_subtype (Work.Peluse.arithIcc κ M₁) (fun x => Iff.rfl)
      (fun w : ℤ => φ z w)).symm
  have hinnerL : ∀ z : ℤ,
      (∑ k' : {n : ℕ // n ∈ Finset.Icc 1 M₁}, φ z (κ * ((k'.1 : ℕ) : ℤ)))
        = ∑ k' ∈ Finset.Icc 1 M₁, φ z (κ * ((k' : ℕ) : ℤ)) :=
    fun z => (Finset.sum_subtype (Finset.Icc 1 M₁) (fun x => Iff.rfl)
      (fun w : ℕ => φ z (κ * ((w : ℕ) : ℤ)))).symm
  have hL : (∑ h : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁},
        ∑ h' : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁}, φ h.1 h'.1)
      = ∑ h ∈ Work.Peluse.arithIcc κ M₁, ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ h h' := by
    calc (∑ h : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁},
            ∑ h' : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁}, φ h.1 h'.1)
        = ∑ h : {x : ℤ // x ∈ Work.Peluse.arithIcc κ M₁},
            ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ h.1 h' := by
          exact Finset.sum_congr rfl fun h _ => hinner h.1
      _ = ∑ h ∈ Work.Peluse.arithIcc κ M₁, ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ h h' :=
          (Finset.sum_subtype (Work.Peluse.arithIcc κ M₁) (fun x => Iff.rfl)
            (fun z : ℤ => ∑ h' ∈ Work.Peluse.arithIcc κ M₁, φ z h')).symm
  have hR : (∑ k : {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ k' : {n : ℕ // n ∈ Finset.Icc 1 M₁}, φ (κ * ((k.1 : ℕ) : ℤ)) (κ * ((k'.1 : ℕ) : ℤ)))
      = ∑ k ∈ Finset.Icc 1 M₁, ∑ k' ∈ Finset.Icc 1 M₁,
          φ (κ * ((k : ℕ) : ℤ)) (κ * ((k' : ℕ) : ℤ)) := by
    calc (∑ k : {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : {n : ℕ // n ∈ Finset.Icc 1 M₁}, φ (κ * ((k.1 : ℕ) : ℤ)) (κ * ((k'.1 : ℕ) : ℤ)))
        = ∑ k : {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' ∈ Finset.Icc 1 M₁, φ (κ * ((k.1 : ℕ) : ℤ)) (κ * ((k' : ℕ) : ℤ)) := by
          exact Finset.sum_congr rfl fun k _ => hinnerL (κ * ((k.1 : ℕ) : ℤ))
      _ = ∑ k ∈ Finset.Icc 1 M₁, ∑ k' ∈ Finset.Icc 1 M₁,
            φ (κ * ((k : ℕ) : ℤ)) (κ * ((k' : ℕ) : ℤ)) :=
          (Finset.sum_subtype (Finset.Icc 1 M₁) (fun x => Iff.rfl)
            (fun z : ℕ => ∑ k' ∈ Finset.Icc 1 M₁, φ (κ * ((z : ℕ) : ℤ)) (κ * ((k' : ℕ) : ℤ)))).symm
  rw [hL, hR]
  exact sum_arithIcc_pair' κ hM₁ φ


/-! ## The reindexing induction: statement, helpers, and the `s = 0` case

The reindexing identity of `ExpansionPETShort` is proved by induction on `s` (see the module
docstring and `NOTES_ExpansionPETShort_ROUTE.md` §6): the step peels coordinate `0` off both the
`h`- and the `h'`-sum with `sum_pi_succ`, applies the induction hypothesis to the tail, and closes the
peeled slot with `sum_subtype_arithIcc_pair`.  This block records the statement (`ReindexStmt`), the
three helpers the step needs, and discharges the `s = 0` case (both sums then run over inhabited
subsingletons). -/

/-- A sum over an inhabited subsingleton. -/
lemma sum_subsingleton_aux {α : Type*} [Fintype α] [Subsingleton α] [Nonempty α] {M : Type*}
    [AddCommMonoid M] (f : α → M) : ∑ a : α, f a = f (Classical.arbitrary α) := by
  classical
  have h : (Finset.univ : Finset α) = {Classical.arbitrary α} := by
    ext a
    simp [Subsingleton.elim a (Classical.arbitrary α)]
  rw [h, Finset.sum_singleton]

/-- Two sums over inhabited subsingletons agree as soon as their summands agree pointwise. -/
lemma sum_subsingleton_eq_aux {α γ : Type*} [Fintype α] [Subsingleton α] [Nonempty α]
    [Fintype γ] [Subsingleton γ] [Nonempty γ] {M : Type*} [AddCommMonoid M]
    (f : α → M) (g : γ → M) (h : ∀ a b, f a = g b) : ∑ a : α, f a = ∑ b : γ, g b := by
  rw [sum_subsingleton_aux f, sum_subsingleton_aux g]
  exact h _ _

/-- The coercion identity for `Fin.cons` on a dependent product of subtypes of `ℤ`: this is what
turns the summand after a peel into the shape of the induction hypothesis. -/
lemma cons_coe_aux {n : ℕ} {Q : Fin (n + 1) → Finset ℤ}
    (b : {x : ℤ // x ∈ Q 0}) (g : (i : Fin n) → {x : ℤ // x ∈ Q i.succ}) :
    (fun i : Fin (n + 1) =>
        ((Fin.cons (α := fun j => {x : ℤ // x ∈ Q j}) b g) i).1)
      = Fin.cons b.1 (fun i : Fin n => (g i).1) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp

/-- The reindexing statement of `ExpansionPETShort` at level `s`. -/
def ReindexStmt (s M₁ : ℕ) : Prop :=
  ∀ (κ : Fin s → ℤ) (Φ : ((i : Fin s) → ℤ) → ((i : Fin s) → ℤ) → ℂ),
    (∏ i : Fin s, (((Work.Peluse.arithIcc (κ i) M₁).card : ℂ))⁻¹) ^ 2
        * ∑ h : (i : Fin s) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
            ∑ h' : (i : Fin s) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
              Φ (fun i => (h i).1) (fun i => (h' i).1)
      = (∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
        * ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              Φ (fun i => κ i * ((k i).1 : ℤ)) (fun i => κ i * ((k' i).1 : ℤ))

/-- The `s = 0` case of the reindexing: both sums run over inhabited subsingletons, and both
cardinality products are `1`. -/
lemma reindexStmt_zero (M₁ : ℕ) : ReindexStmt 0 M₁ := by
  intro κ Φ
  haveI h1 : Subsingleton ((i : Fin 0) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁}) :=
    ⟨fun a b => funext fun i => i.elim0⟩
  haveI h2 : Nonempty ((i : Fin 0) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁}) :=
    ⟨fun i => i.elim0⟩
  haveI h3 : Subsingleton ((i : Fin 0) → {n : ℕ // n ∈ Finset.Icc 1 M₁}) :=
    ⟨fun a b => funext fun i => i.elim0⟩
  haveI h4 : Nonempty ((i : Fin 0) → {n : ℕ // n ∈ Finset.Icc 1 M₁}) := ⟨fun i => i.elim0⟩
  have hp : (∏ i : Fin 0, (((Work.Peluse.arithIcc (κ i) M₁).card : ℂ))⁻¹) = 1 := by simp
  have hq : (∏ i : Fin 0, (((M₁ : ℂ))⁻¹)) = 1 := by simp
  rw [hp, hq, one_pow, one_mul, one_mul]
  refine sum_subsingleton_eq_aux _ _ fun h k => sum_subsingleton_eq_aux _ _ fun h' k' => ?_
  have hb : (fun i : Fin 0 => (h i).1) = (fun i : Fin 0 => κ i * ((k i).1 : ℤ)) := by
    funext i
    exact i.elim0
  have hc : (fun i : Fin 0 => (h' i).1) = (fun i : Fin 0 => κ i * ((k' i).1 : ℤ)) := by
    funext i
    exact i.elim0
  rw [hb, hc]



/-- **Peeling coordinate `0` off both sums** of a double sum over a dependent product: the outer sum
becomes `(b, g)` (first coordinate and tail) and the inner sum `(b', g')`.  This is the first clause
of the step of the reindexing induction; the order of the sums is the one the two peels produce
(`b, g, b', g'`), and `sum_swap_aux` reorders it when the induction hypothesis needs `(b,b')` outside
and `(g,g')` inside. -/
lemma sum_pi_succ_double {n : ℕ} {Q : Fin (n + 1) → Finset ℤ}
    (Ψ : ((i : Fin (n + 1)) → ℤ) → ((i : Fin (n + 1)) → ℤ) → ℂ) :
    (∑ h : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
        ∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
          Ψ (fun i => (h i).1) (fun i => (h' i).1))
      = ∑ b : {x : ℤ // x ∈ Q 0}, ∑ g : (i : Fin n) → {x : ℤ // x ∈ Q i.succ},
          ∑ b' : {x : ℤ // x ∈ Q 0}, ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Q i.succ},
            Ψ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Q j}) b g) i).1)
              (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Q j}) b' g') i).1) := by
  rw [sum_pi_succ (β := fun i : Fin (n + 1) => {x : ℤ // x ∈ Q i})
    (Ψ := fun h => ∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
      Ψ (fun i => (h i).1) (fun i => (h' i).1))]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  exact sum_pi_succ (β := fun i : Fin (n + 1) => {x : ℤ // x ∈ Q i})
    (Ψ := fun h' => Ψ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Q j}) b g) i).1)
      (fun i => (h' i).1))

/-- Interchanging the two summations of a double sum (a named wrapper of `Finset.sum_comm`, for use
inside `Finset.sum_congr`). -/
lemma sum_swap_aux {α β : Type*} [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M]
    (F : α → β → M) : (∑ a : α, ∑ b : β, F a b) = ∑ b : β, ∑ a : α, F a b :=
  Finset.sum_comm


/-- The label-side `Fin.cons` coercion identity (needed for the last clause of the step): the label
function `j ↦ κ j · (Fin.cons k₀ k j)` is the `Fin.cons` of its values at `0` and on the tail. -/
lemma cons_coe_label_aux {n : ℕ} (κ : Fin (n + 1) → ℤ) {M₁ : ℕ}
    (k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁})
    (k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁}) :
    (fun j : Fin (n + 1) =>
        κ j * ((Fin.cons (α := fun _ : Fin (n + 1) => {m : ℕ // m ∈ Finset.Icc 1 M₁}) k₀ k) j).1)
      = Fin.cons (κ 0 * (((k₀.1 : ℕ)) : ℤ))
          (fun i : Fin n => κ i.succ * (((k i).1 : ℕ) : ℤ)) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp
  · intro i
    simp

/-- A scalar distributes over a *double* sum: two applications of `Finset.mul_sum`, stopping at the
second level.  It is recorded separately from `Finset.mul_sum` because in the uses below the inner
summand is itself a sum, and the *shape* of the resulting expression matters. -/
lemma mul_sum_sum_eq2 {α β : Type*} [Fintype α] [Fintype β] {R : Type*} [CommSemiring R]
    (k : R) (F : α → β → R) :
    k * (∑ a : α, ∑ b : β, F a b) = ∑ a : α, ∑ b : β, k * F a b := by
  simp only [Finset.mul_sum]

/-- **The step of the reindexing induction**: `ReindexStmt n M₁` implies `ReindexStmt (n+1) M₁`.

The proof peels coordinate `0` off both the `h`- and the `h'`-sum (`sum_pi_succ_double`), swaps the
two middle sums (`sum_swap_aux`) so that the tail sums are innermost, applies the induction hypothesis
slot-in-the-tail (`cons_coe_aux` turns the peeled `Fin.cons`-summand into the shape the hypothesis
expects), and finally collapses the peeled slot with `sum_subtype_arithIcc_pair` — whose label side is
turned back into a `Fin.cons` by `cons_coe_label_aux` and `sum_pi_succ` in reverse. -/
theorem reindexStmt_succ {n M₁ : ℕ} (hM₁ : 1 ≤ M₁) (ih : ReindexStmt n M₁) :
    ReindexStmt (n + 1) M₁ := by
  intro κ Φ
  have hA : (∏ i : Fin (n + 1), (((Work.Peluse.arithIcc (κ i) M₁).card : ℂ))⁻¹) ^ 2
      = (((Work.Peluse.arithIcc (κ 0) M₁).card : ℂ))⁻¹ ^ 2
          * (∏ i : Fin n, (((Work.Peluse.arithIcc (κ i.succ) M₁).card : ℂ))⁻¹) ^ 2 := by
    rw [Fin.prod_univ_succ, mul_pow]
  have hB : (∏ i : Fin (n + 1), (((M₁ : ℂ))⁻¹)) ^ 2
      = (((M₁ : ℂ)))⁻¹ ^ 2 * (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2 := by
    rw [Fin.prod_univ_succ, mul_pow]
  have hpeel : (∑ h : (i : Fin (n + 1)) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
        ∑ h' : (i : Fin (n + 1)) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
          Φ (fun i => (h i).1) (fun i => (h' i).1))
      = ∑ b : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
          ∑ b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
            ∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
              ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
                  (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1) := by
    rw [sum_pi_succ_double (Q := fun j => Work.Peluse.arithIcc (κ j) M₁) (Ψ := Φ)]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact sum_swap_aux (F := fun (g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁})
        (b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁}) =>
          ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
            Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
              (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1))
  rw [hA, hB, hpeel]
  rw [mul_assoc]
  -- push the constant `(∏_{i:Fin n} c_{i.succ})²` inside the two outer sums
  have h1 : (∏ i : Fin n, (((Work.Peluse.arithIcc (κ i.succ) M₁).card : ℂ))⁻¹) ^ 2
        * (∑ b : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
            ∑ b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
              ∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                  Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
                    (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1))
      = ∑ b : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
          ∑ b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
            (∏ i : Fin n, (((Work.Peluse.arithIcc (κ i.succ) M₁).card : ℂ))⁻¹) ^ 2
              * (∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                  ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                    Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
                      (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1)) :=
    mul_sum_sum_eq2 _ (fun b b' =>
      ∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
        ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
          Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
            (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1))
  rw [h1]
  -- apply the induction hypothesis to each `(b,b')`-bracket
  have h2 : (∑ b : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
          ∑ b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
            (∏ i : Fin n, (((Work.Peluse.arithIcc (κ i.succ) M₁).card : ℂ))⁻¹) ^ 2
              * (∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                  ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
                    Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
                      (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1)))
      = ∑ b : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
          ∑ b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
            (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2
              * (∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                    Φ (Fin.cons b.1 (fun i => κ i.succ * ((k i).1 : ℤ)))
                      (Fin.cons b'.1 (fun i => κ i.succ * ((k' i).1 : ℤ)))) := by
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    have hcc : (∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
          ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
            Φ (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b g) i).1)
              (fun i => ((Fin.cons (α := fun j => {x : ℤ // x ∈ Work.Peluse.arithIcc (κ j) M₁}) b' g') i).1))
        = ∑ g : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
            ∑ g' : (i : Fin n) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i.succ) M₁},
              Φ (Fin.cons b.1 (fun i => (g i).1)) (Fin.cons b'.1 (fun i => (g' i).1)) := by
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => ?_
      rw [cons_coe_aux (Q := fun j => Work.Peluse.arithIcc (κ j) M₁) b g,
        cons_coe_aux (Q := fun j => Work.Peluse.arithIcc (κ j) M₁) b' g']
    rw [hcc]
    exact ih (fun i => κ i.succ) (fun a a' => Φ (Fin.cons b.1 a) (Fin.cons b'.1 a'))
  rw [h2]
  -- collapse the peeled slot `0` with the per-slot reindexing identity
  have h3 : (((Work.Peluse.arithIcc (κ 0) M₁).card : ℂ))⁻¹ ^ 2
        * (∑ b : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
            ∑ b' : {x : ℤ // x ∈ Work.Peluse.arithIcc (κ 0) M₁},
              (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2
                * (∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                    ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                      Φ (Fin.cons b.1 (fun i => κ i.succ * ((k i).1 : ℤ)))
                        (Fin.cons b'.1 (fun i => κ i.succ * ((k' i).1 : ℤ)))))
      = (((M₁ : ℂ)))⁻¹ ^ 2
        * (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2
                * (∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                    ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                      Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                        (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))) :=
    sum_subtype_arithIcc_pair (κ 0) hM₁ (fun z z' =>
      (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2
        * (∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              Φ (Fin.cons z (fun i => κ i.succ * ((k i).1 : ℤ)))
                (Fin.cons z' (fun i => κ i.succ * ((k' i).1 : ℤ)))))
  rw [h3]
  -- pull the constant back out of the two label sums
  have h4 : (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
          ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2
              * (∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                    Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                      (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ)))))
      = (∏ i : Fin n, (((M₁ : ℂ))⁻¹)) ^ 2
        * (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                    (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ)))) :=
    by simp only [Finset.mul_sum]
  rw [h4]
  -- reassemble the label vectors
  have h5 : (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
          ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                  (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))
      = (∑ K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
          ∑ K' : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            Φ (fun i => κ i * ((K i).1 : ℤ)) (fun i => κ i * ((K' i).1 : ℤ))) := by
    have e1 : (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
          ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                  (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))
        = (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
                ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                    (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ)))) := by
      refine Finset.sum_congr rfl fun k₀ _ => ?_
      exact (sum_swap_aux (F := fun (k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁})
          (k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁}) =>
            ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))).symm
    have e2 : (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
                ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                    (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))
        = (∑ K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                Φ (fun i => κ i * ((K i).1 : ℤ))
                  (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ)))) := by
      have hkey : ∀ (k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁})
          (k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁})
          (k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁})
          (k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁}),
          Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
            (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ)))
          = Φ (fun i => κ i * (((Fin.cons (α := fun _ : Fin (n + 1) => {m : ℕ // m ∈ Finset.Icc 1 M₁})
                k₀ k) i).1 : ℤ))
            (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))) := by
        intro k₀ k k₀' k'
        rw [cons_coe_label_aux κ k₀ k]
      rw [show (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                    Φ (Fin.cons (κ 0 * ((k₀.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k i).1 : ℤ)))
                      (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))
          = (∑ k₀ : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
                  ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                    Φ (fun i => κ i * (((Fin.cons (α := fun _ : Fin (n + 1) =>
                          {m : ℕ // m ∈ Finset.Icc 1 M₁}) k₀ k) i).1 : ℤ))
                      (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ)))) from
            Finset.sum_congr rfl fun k₀ _ => Finset.sum_congr rfl fun k _ =>
              Finset.sum_congr rfl fun k₀' _ => Finset.sum_congr rfl fun k' _ => hkey k₀ k k₀' k']
      rw [← sum_pi_succ (β := fun _ : Fin (n + 1) => {m : ℕ // m ∈ Finset.Icc 1 M₁})
        (Ψ := fun K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁} =>
          ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              Φ (fun i => κ i * ((K i).1 : ℤ))
                (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))]
    have e3 : (∑ K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                Φ (fun i => κ i * ((K i).1 : ℤ))
                  (Fin.cons (κ 0 * ((k₀'.1 : ℕ) : ℤ)) (fun i => κ i.succ * ((k' i).1 : ℤ))))
        = (∑ K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                Φ (fun i => κ i * ((K i).1 : ℤ))
                  (fun i => κ i * (((Fin.cons (α := fun _ : Fin (n + 1) =>
                        {m : ℕ // m ∈ Finset.Icc 1 M₁}) k₀' k') i).1 : ℤ))) := by
      refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun k₀' _ =>
        Finset.sum_congr rfl fun k' _ => ?_
      rw [← cons_coe_label_aux κ k₀' k']
    have e4 : (∑ K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ k₀' : {m : ℕ // m ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin n) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
                Φ (fun i => κ i * ((K i).1 : ℤ))
                  (fun i => κ i * (((Fin.cons (α := fun _ : Fin (n + 1) =>
                        {m : ℕ // m ∈ Finset.Icc 1 M₁}) k₀' k') i).1 : ℤ)))
        = (∑ K : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
            ∑ K' : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁},
              Φ (fun i => κ i * ((K i).1 : ℤ)) (fun i => κ i * ((K' i).1 : ℤ))) := by
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [← sum_pi_succ (β := fun _ : Fin (n + 1) => {m : ℕ // m ∈ Finset.Icc 1 M₁})
        (Ψ := fun K' : (i : Fin (n + 1)) → {m : ℕ // m ∈ Finset.Icc 1 M₁} =>
          Φ (fun i => κ i * ((K i).1 : ℤ)) (fun i => κ i * ((K' i).1 : ℤ)))]
    exact e1.trans (e2.trans (e3.trans e4))
  rw [h5]
  rw [mul_assoc]

/-- The reindexing identity of `ExpansionPETShort` at every level, by induction on `s`. -/
theorem prod_reindex_arithIcc (s M₁ : ℕ) (hM₁ : 1 ≤ M₁) : ReindexStmt s M₁ := by
  induction s with
  | zero => exact reindexStmt_zero M₁
  | succ n ih => exact reindexStmt_succ hM₁ ih

/-- **The expanded box sum** at the arithmetic-progression direction sets `κ_i[M₁]`: reindexing the
`(h,h')`-average by the labels (`prod_reindex_arithIcc`), the cube term becomes the `expCube` of
`ExpPET/Defs.lean` (`prod_cubeTerm_mul_eq_expCube`).  The cardinality normalisation
`(∏_i |κ_i[M₁]|⁻¹)²` is thereby replaced by `(∏_i M₁⁻¹)²` — valid **including** the degenerate
slots `κ_i = 0`. -/
theorem boxSumPow_arithIcc_eq {s M₁ : ℕ} (hM₁ : 1 ≤ M₁) (κ : Fin s → ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow s (fun i : Fin s => Work.Peluse.arithIcc (κ i) M₁) S f
      = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
          * (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                ∑' x : ℤ, expCube κ (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)) := by
  have hre := prod_reindex_arithIcc s M₁ hM₁ κ
    (fun u u' => ∑' x : ℤ, ∏ ω : Fin s → Bool,
      (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift u u' ω)))
  have hK : (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑' x : ℤ, ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
            (f (x + Work.Peluse.cornerShift (fun i => κ i * ((k i).1 : ℤ))
              (fun i => κ i * ((k' i).1 : ℤ)) ω)))
      = (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑' x : ℤ, expCube κ (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    exact tsum_congr fun x =>
      prod_cubeTerm_mul_eq_expCube κ (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x
  have hreassoc : ((S.card : ℂ))⁻¹
        * (∏ i : Fin s, (((Work.Peluse.arithIcc (κ i) M₁).card : ℂ))⁻¹)
        * (∏ i : Fin s, (((Work.Peluse.arithIcc (κ i) M₁).card : ℂ))⁻¹)
        * (∑ h : (i : Fin s) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
            ∑ h' : (i : Fin s) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
              ∑' x : ℤ, ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
                (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((Work.Peluse.arithIcc (κ i) M₁).card : ℂ))⁻¹) ^ 2
        * (∑ h : (i : Fin s) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
            ∑ h' : (i : Fin s) → {x : ℤ // x ∈ Work.Peluse.arithIcc (κ i) M₁},
              ∑' x : ℤ, ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
                (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))) := by
    ring
  show Work.Peluse.prodCubeSum s (fun i : Fin s => Work.Peluse.arithIcc (κ i) M₁) S (fun _ => f)
      = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
          * (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                ∑' x : ℤ, expCube κ (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x))
  rw [Work.Peluse.prodCubeSum_eq, hreassoc, hre, hK]

end Work.Peluse.Holds.ExpPET
