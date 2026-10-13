/-
  WilG5 — area G5 (from the F-lemma to the algebraic lemma).

  Ω-calculus foundation: monotonicity of the format/degree indices, the projection `projN`
  (forget the last `k` coordinates), the two coordinate lifts `liftFirst` (a set on the
  *first* coordinates) and `liftLast` (a set on the *last* coordinates), the polynomial
  relation sets recording coordinate identifications, and the small supply of Ω-sets used
  everywhere below (`univ`, `∅`, half-spaces, the open cube, points).

  Conventions (fixed here and used by every module above):
    * an ambient space is written `Fin (p + q) → ℝ`; the first `p` coordinates are read by
      `Fin.castAdd q` and the last `q` by `Fin.natAdd p`;
    * `projN k A = {x | ∃ y : Fin k → ℝ, Fin.append x y ∈ A}` (forget the last `k` coords);
    * `liftFirst k A = {z | (fun i => z (Fin.castAdd k i)) ∈ A}` (A on the first coords);
    * `liftLast k A = {z | (fun i => z (lidx k i)) ∈ A}` with `lidx k i = ⟨k + i.val⟩`
      (A on the last coords of `Fin (n + k)`; the type expression keeps the size `n` of `A`
      first — the shape produced by the `prod_left` axiom);
    * `coordPre ι A = {x | x ∘ ι ∈ A}`, `coordImage ι A = {u | ∃ x ∈ A, x ∘ ι = u}`; these
      are *defined* here, their membership lemmas live in `Work.WilG5.Reindex`.

  Note on a statement that had to be repaired.  The "keep the last `k` coordinates"
  operation `lastN k A = {u | ∃ x : Fin n → ℝ, Fin.append x u ∈ A}` does NOT satisfy the
  naive recursion `lastN (k+1) A = {u | Fin.init u ∈ lastN k (projLast A)}`: `projLast`
  forgets which value the last coordinate took.  Counterexample (recorded so that nobody
  re-proves it): `n = 0`, `k = 1`, `A = {(0,1)} ⊆ ℝ²` gives left-hand side `{(0,1)}`,
  right-hand side `{(0,c) | c ∈ ℝ}`.  The correct route (module `Reindex`) is: `liftLast`
  (proved here) + the *balanced* reindexing
  `{x : Fin M | x ∘ σ ∈ A} = projN M (liftLast M A ∩ relSetSwap σ)` + transports of index
  types along explicit arithmetic equalities.
-/
import Submission.Work.Wilkies.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 0. Degree bookkeeping for `MvPolynomial` (crude `≤`-bounds only) -/

theorem td_sub_le {σ : Type*} {R : Type*} [CommRing R] (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree := by
  rw [sub_eq_add_neg]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  rw [MvPolynomial.totalDegree_neg]

theorem td_mul_le {σ : Type*} {R : Type*} [CommSemiring R] (a b : MvPolynomial σ R) :
    (a * b).totalDegree ≤ a.totalDegree + b.totalDegree :=
  MvPolynomial.totalDegree_mul a b

theorem td_X_le {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R] (s : σ) :
    (MvPolynomial.X s : MvPolynomial σ R).totalDegree ≤ 1 :=
  le_of_eq (MvPolynomial.totalDegree_X s)

theorem td_C_le {σ : Type*} {R : Type*} [CommSemiring R] (r : R) :
    (MvPolynomial.C r : MvPolynomial σ R).totalDegree ≤ 0 :=
  le_of_eq (MvPolynomial.totalDegree_C r)

theorem td_X_sub_C_le {N : ℕ} (i : Fin (N + 1)) (c : ℝ) :
    (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin (N + 1)) ℝ).totalDegree ≤ 1 := by
  refine le_trans (td_sub_le _ _) ?_
  exact max_le (td_X_le i) (le_trans (td_C_le c) (Nat.zero_le 1))

theorem td_sq_le {N : ℕ} {p : MvPolynomial (Fin N) ℝ} (hp : p.totalDegree ≤ 1) :
    (p * p).totalDegree ≤ 2 := by
  refine le_trans (td_mul_le _ _) ?_
  simpa using add_le_add hp hp

/-! ## 1. Monotonicity in the format and degree indices -/

theorem mem_monoF {F D n : ℕ} {X : Set (Fin n → ℝ)} (h : X ∈ S.Ω F D n) (c : ℕ) :
    X ∈ S.Ω (F + c) D n := by
  induction c with
  | zero => simpa using h
  | succ c ih => exact S.mono_F ih

theorem mem_monoD {F D n : ℕ} {X : Set (Fin n → ℝ)} (h : X ∈ S.Ω F D n) (c : ℕ) :
    X ∈ S.Ω F (D + c) n := by
  induction c with
  | zero => simpa using h
  | succ c ih => exact S.mono_D ih

theorem mem_mono {F D n : ℕ} {X : Set (Fin n → ℝ)} (h : X ∈ S.Ω F D n)
    (F' D' : ℕ) (hF : F ≤ F') (hD : D ≤ D') : X ∈ S.Ω F' D' n := by
  have h1 : X ∈ S.Ω (F + (F' - F)) (D + (D' - D)) n :=
    mem_monoD (mem_monoF h (F' - F)) (D' - D)
  rwa [Nat.add_sub_cancel' hF, Nat.add_sub_cancel' hD] at h1

/-! ## 2. The two trivial Ω-sets -/

theorem univ_mem {n : ℕ} : (Set.univ : Set (Fin n → ℝ)) ∈ S.Ω (n + 4) 4 n := by
  have h := S.hyp n (0 : MvPolynomial (Fin n) ℝ)
  have he : {x : Fin n → ℝ | MvPolynomial.eval x (0 : MvPolynomial (Fin n) ℝ) = 0} = Set.univ := by
    ext x; simp
  rw [he, MvPolynomial.totalDegree_zero] at h
  exact mem_mono h (n + 4) 4 (by omega) (by omega)

theorem empty_mem {n : ℕ} : (∅ : Set (Fin n → ℝ)) ∈ S.Ω (n + 6) 4 n := by
  have h := S.compl (univ_mem (S := S) (n := n))
  simpa using mem_mono h (n + 6) 4 (by omega) (by omega)

/-! ## 3. Projections -/

/-- Forget the last `k` coordinates. -/
def projN {n : ℕ} (k : ℕ) (A : Set (Fin (n + k) → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ y : Fin k → ℝ, Fin.append x y ∈ A}

/-- Keep only the last `k` coordinates.  (Membership lemma deferred: see the header.) -/
def lastN {n : ℕ} (k : ℕ) (A : Set (Fin (n + k) → ℝ)) : Set (Fin k → ℝ) :=
  {u | ∃ x : Fin n → ℝ, Fin.append x u ∈ A}

theorem projN_mem {n : ℕ} : ∀ (k F D : ℕ) {A : Set (Fin (n + k) → ℝ)},
    A ∈ S.Ω F D (n + k) → projN k A ∈ S.Ω (F + k) D n := by
  intro k
  induction k with
  | zero =>
    intro F D A h
    have heq : projN 0 A = A := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have h2 : Fin.append x y = x := by
          funext i
          conv_lhs => rw [show i = Fin.castAdd 0 i from Fin.ext rfl]
          rw [Fin.append_left]
        rwa [h2] at hy
      · intro hx
        refine ⟨Fin.elim0, ?_⟩
        have h2 : Fin.append x (Fin.elim0 : Fin 0 → ℝ) = x := by
          funext i
          conv_lhs => rw [show i = Fin.castAdd 0 i from Fin.ext rfl]
          rw [Fin.append_left]
        rwa [h2]
    rw [heq]
    exact mem_mono h _ _ (by omega) (by omega)
  | succ k ih =>
    intro F D A h
    have h' : projLast A ∈ S.Ω (F + 1) D (n + k) := S.proj h
    have hih := ih (F + 1) D (A := projLast A) h'
    have heq : projN (k + 1) A = projN k (projLast A) := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨Fin.init y, ?_⟩
        change ∃ t : ℝ, Fin.snoc (Fin.append x (Fin.init y)) t ∈ A
        refine ⟨y (Fin.last k), ?_⟩
        rw [← Fin.append_snoc]
        rwa [Fin.snoc_init_self y]
      · rintro ⟨y, t, hy⟩
        exact ⟨Fin.snoc y t, by rw [Fin.append_snoc]; exact hy⟩
    rw [heq]
    exact mem_mono hih _ _ (by omega) (by omega)

/-! ## 4. Lifts of a set to the first / last coordinates -/

/-- `A` placed on the first `m` coordinates of `Fin (m+k) → ℝ`. -/
def liftFirst {m : ℕ} (k : ℕ) (A : Set (Fin m → ℝ)) : Set (Fin (m + k) → ℝ) :=
  {z | (fun i : Fin m => z (Fin.castAdd k i)) ∈ A}

/-- The `i`-th of the last `n` coordinates of `Fin (n + k)`, as an index of `Fin (n+k)`. -/
def lidx {n : ℕ} (k : ℕ) (i : Fin n) : Fin (n + k) := ⟨k + i.val, by omega⟩

/-- `A` placed on the last `n` coordinates of `Fin (n + k) → ℝ`.  Note the type expression:
the size `n` of `A` comes first, matching what iterating `SOMin.prod_left` produces. -/
def liftLast {n : ℕ} (k : ℕ) (A : Set (Fin n → ℝ)) : Set (Fin (n + k) → ℝ) :=
  {z | (fun i : Fin n => z (lidx k i)) ∈ A}

theorem liftFirst_mem {m : ℕ} : ∀ (k F D : ℕ) {A : Set (Fin m → ℝ)},
    A ∈ S.Ω F D m → liftFirst k A ∈ S.Ω (F + k) D (m + k) := by
  intro k
  induction k with
  | zero =>
    intro F D A h
    have heq : liftFirst 0 A = A := by
      ext z
      simp only [liftFirst, Set.mem_ofPred_eq]
      have hz : (fun i : Fin m => z (Fin.castAdd 0 i)) = z := by
        funext i; exact congrArg z (Fin.ext rfl)
      rw [hz]
    rw [heq]
    exact mem_mono h _ _ (by omega) (by omega)
  | succ k ih =>
    intro F D A h
    have heq : liftFirst (k + 1) A =
        {z : Fin (m + k + 1) → ℝ | Fin.init z ∈ liftFirst k A} := by
      ext z
      change (fun i : Fin m => z (Fin.castAdd (k + 1) i)) ∈ A ↔
        (fun i : Fin m => Fin.init z (Fin.castAdd k i)) ∈ A
      have hfun : (fun i : Fin m => z (Fin.castAdd (k + 1) i)) =
          (fun i : Fin m => Fin.init z (Fin.castAdd k i)) := by
        funext i
        show z (Fin.castAdd (k + 1) i) = Fin.init z (Fin.castAdd k i)
        rw [show Fin.init z (Fin.castAdd k i) = z ((Fin.castAdd k i).castSucc) from rfl,
          show Fin.castAdd (k + 1) i = (Fin.castAdd k i).castSucc from Fin.ext rfl]
      rw [hfun]
    rw [heq]
    exact mem_mono (S.prod_right (ih F D h)) (F + (k + 1)) D (by omega) (by omega)

theorem liftLast_mem {n : ℕ} : ∀ (k F D : ℕ) {A : Set (Fin n → ℝ)},
    A ∈ S.Ω F D n → liftLast k A ∈ S.Ω (F + k) D (n + k) := by
  intro k
  induction k with
  | zero =>
    intro F D A h
    have heq : liftLast 0 A = A := by
      ext z
      simp only [liftLast, Set.mem_ofPred_eq]
      have hz : (fun i : Fin n => z (lidx 0 i)) = z := by
        funext i; exact congrArg z (Fin.ext (by simp [lidx]))
      rw [hz]
    rw [heq]
    exact mem_mono h _ _ (by omega) (by omega)
  | succ k ih =>
    intro F D A h
    have heq : liftLast (k + 1) A =
        {z : Fin (n + k + 1) → ℝ | Fin.tail z ∈ liftLast k A} := by
      ext z
      change (fun i : Fin n => z (lidx (k + 1) i)) ∈ A ↔
        (fun i : Fin n => Fin.tail z (lidx k i)) ∈ A
      have hfun : (fun i : Fin n => z (lidx (k + 1) i)) =
          (fun i : Fin n => Fin.tail z (lidx k i)) := by
        funext i
        show z (lidx (k + 1) i) = Fin.tail z (lidx k i)
        rw [show Fin.tail z (lidx k i) = z ((lidx k i).succ) from rfl,
          show lidx (k + 1) i = (lidx k i).succ from Fin.ext (by simp [lidx]; omega)]
      rw [hfun]
    rw [heq]
    exact mem_mono (S.prod_left (ih F D h)) (F + (k + 1)) D (by omega) (by omega)

/-! ## 5. Relation sets (coordinate identifications) -/

/-- In `Fin (p + q) → ℝ`: the first `p` coordinates form `u`, the last `q` coordinates form
`x`, and `u j = x (σ j)`. -/
def relSet {p q : ℕ} (σ : Fin p → Fin q) : Set (Fin (p + q) → ℝ) :=
  {z | ∀ j : Fin p, z (Fin.castAdd q j) = z (Fin.natAdd p (σ j))}

/-- In `Fin (q + p) → ℝ`: the first `q` coordinates form `x`, the last `p` form `u`, and
`u j = x (σ j)`. -/
def relSetSwap {p q : ℕ} (σ : Fin p → Fin q) : Set (Fin (q + p) → ℝ) :=
  {z | ∀ j : Fin p, z (Fin.natAdd q j) = z (Fin.castAdd p (σ j))}

theorem relSet_mem {p q : ℕ} (σ : Fin p → Fin q) :
    relSet σ ∈ S.Ω (4 * (p + q) + 8) (2 * p + 4) (p + q) := by
  have hsingle : ∀ j : Fin p,
      {z : Fin (p + q) → ℝ | z (Fin.castAdd q j) = z (Fin.natAdd p (σ j))} ∈
        S.Ω (p + q) 1 (p + q) := by
    intro j
    have hdeg : ((MvPolynomial.X (Fin.castAdd q j) -
        MvPolynomial.X (Fin.natAdd p (σ j)) : MvPolynomial (Fin (p + q)) ℝ)).totalDegree ≤ 1 :=
      le_trans (td_sub_le _ _) (max_le (td_X_le _) (td_X_le _))
    have heq : {z : Fin (p + q) → ℝ | z (Fin.castAdd q j) = z (Fin.natAdd p (σ j))} =
        {x : Fin (p + q) → ℝ | MvPolynomial.eval x (MvPolynomial.X (Fin.castAdd q j) -
          MvPolynomial.X (Fin.natAdd p (σ j)) : MvPolynomial (Fin (p + q)) ℝ) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact mem_mono (S.hyp (p + q) (MvPolynomial.X (Fin.castAdd q j) -
      MvPolynomial.X (Fin.natAdd p (σ j)) : MvPolynomial (Fin (p + q)) ℝ)) (p + q) 1
      (le_refl _) hdeg
  have hmem : (⋂ j : Fin p,
      {z : Fin (p + q) → ℝ | z (Fin.castAdd q j) = z (Fin.natAdd p (σ j))}) ∈
      S.Ω (p + q + 1) (∑ _ : Fin p, 1) (p + q) :=
    S.inter (fun _ => 1) (fun j =>
      {z : Fin (p + q) → ℝ | z (Fin.castAdd q j) = z (Fin.natAdd p (σ j))})
      (fun j => hsingle j)
  have hsum : (∑ _ : Fin p, 1) = p := by simp
  rw [hsum] at hmem
  have heq : relSet σ = ⋂ j : Fin p,
      {z : Fin (p + q) → ℝ | z (Fin.castAdd q j) = z (Fin.natAdd p (σ j))} := by
    ext z; simp [relSet]
  rw [heq]
  exact mem_mono hmem (4 * (p + q) + 8) (2 * p + 4) (by omega) (by omega)

theorem relSetSwap_mem {p q : ℕ} (σ : Fin p → Fin q) :
    relSetSwap σ ∈ S.Ω (4 * (p + q) + 8) (2 * p + 4) (q + p) := by
  have hsingle : ∀ j : Fin p,
      {z : Fin (q + p) → ℝ | z (Fin.natAdd q j) = z (Fin.castAdd p (σ j))} ∈
        S.Ω (q + p) 1 (q + p) := by
    intro j
    have hdeg : ((MvPolynomial.X (Fin.natAdd q j) -
        MvPolynomial.X (Fin.castAdd p (σ j)) : MvPolynomial (Fin (q + p)) ℝ)).totalDegree ≤ 1 :=
      le_trans (td_sub_le _ _) (max_le (td_X_le _) (td_X_le _))
    have heq : {z : Fin (q + p) → ℝ | z (Fin.natAdd q j) = z (Fin.castAdd p (σ j))} =
        {x : Fin (q + p) → ℝ | MvPolynomial.eval x (MvPolynomial.X (Fin.natAdd q j) -
          MvPolynomial.X (Fin.castAdd p (σ j)) : MvPolynomial (Fin (q + p)) ℝ) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact mem_mono (S.hyp (q + p) (MvPolynomial.X (Fin.natAdd q j) -
      MvPolynomial.X (Fin.castAdd p (σ j)) : MvPolynomial (Fin (q + p)) ℝ)) (q + p) 1
      (le_refl _) hdeg
  have hmem : (⋂ j : Fin p,
      {z : Fin (q + p) → ℝ | z (Fin.natAdd q j) = z (Fin.castAdd p (σ j))}) ∈
      S.Ω (q + p + 1) (∑ _ : Fin p, 1) (q + p) :=
    S.inter (fun _ => 1) (fun j =>
      {z : Fin (q + p) → ℝ | z (Fin.natAdd q j) = z (Fin.castAdd p (σ j))})
      (fun j => hsingle j)
  have hsum : (∑ _ : Fin p, 1) = p := by simp
  rw [hsum] at hmem
  have heq : relSetSwap σ = ⋂ j : Fin p,
      {z : Fin (q + p) → ℝ | z (Fin.natAdd q j) = z (Fin.castAdd p (σ j))} := by
    ext z; simp [relSetSwap]
  rw [heq]
  exact mem_mono hmem (4 * (p + q) + 8) (2 * p + 4) (by omega) (by omega)

/-! ## 6. Reindexing (definitions; membership lemmas in `Work.WilG5.Reindex`) -/

/-- `coordPre ι A = {x | x ∘ ι ∈ A}`. -/
def coordPre {m N : ℕ} (ι : Fin m → Fin N) (A : Set (Fin m → ℝ)) : Set (Fin N → ℝ) :=
  {x | x ∘ ι ∈ A}

/-- `coordImage ι A = {u | ∃ x ∈ A, x ∘ ι = u}`. -/
def coordImage {m N : ℕ} (ι : Fin m → Fin N) (A : Set (Fin N → ℝ)) : Set (Fin m → ℝ) :=
  {u | ∃ x ∈ A, x ∘ ι = u}

/-! ## 7. Elementary Ω-sets: half-spaces, the open cube, points -/

/-- `{x : c ≤ x i}`: complete the square. -/
theorem leSet_mem {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | c ≤ x i} ∈ S.Ω (4 * n + 16) 4 n := by
  have hdeg : (((MvPolynomial.X (Fin.castAdd 1 i) - MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℝ) -
      MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)))).totalDegree ≤ 2 := by
    refine le_trans (td_sub_le _ _) ?_
    refine max_le ?_ ?_
    · exact le_trans (td_X_sub_C_le (Fin.castAdd 1 i) c) (Nat.le_succ 1)
    · exact td_sq_le (td_X_le (Fin.natAdd n (0 : Fin 1)))
  have hmem : {z : Fin (n + 1) → ℝ |
      MvPolynomial.eval z ((MvPolynomial.X (Fin.castAdd 1 i) - MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = 0} ∈ S.Ω (n + 1) 2 (n + 1) :=
    mem_mono (S.hyp (n + 1) ((MvPolynomial.X (Fin.castAdd 1 i) - MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℝ) -
      MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)))) (n + 1) 2 (le_refl _) hdeg
  have hproj : projLast {z : Fin (n + 1) → ℝ |
      MvPolynomial.eval z ((MvPolynomial.X (Fin.castAdd 1 i) - MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = 0} ∈ S.Ω (n + 2) 2 n :=
    S.proj hmem
  have heq : projLast {z : Fin (n + 1) → ℝ |
      MvPolynomial.eval z ((MvPolynomial.X (Fin.castAdd 1 i) - MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = 0} = {x : Fin n → ℝ | c ≤ x i} := by
    ext x
    have key : ∀ t : ℝ, MvPolynomial.eval (Fin.snoc x t) ((MvPolynomial.X (Fin.castAdd 1 i) -
        MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = (x i - c) - t * t := by
      intro t
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X]
      rw [show Fin.castAdd 1 i = Fin.castSucc i from Fin.ext rfl,
        show (Fin.natAdd n (0 : Fin 1)) = Fin.last n from Fin.ext rfl,
        Fin.snoc_castSucc, Fin.snoc_last]
    constructor
    · rintro ⟨t, ht⟩
      simp only [Set.mem_ofPred_eq] at ht
      rw [key t] at ht
      change c ≤ x i
      nlinarith [sq_nonneg t]
    · intro hx
      refine ⟨Real.sqrt (x i - c), ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [key (Real.sqrt (x i - c))]
      have hsq : Real.sqrt (x i - c) * Real.sqrt (x i - c) = x i - c := by
        rw [← sq, Real.sq_sqrt (sub_nonneg.mpr hx)]
      rw [hsq]; ring
  rw [← heq]
  exact mem_mono hproj (4 * n + 16) 4 (by omega) (by omega)

/-- `{x : x i ≤ c}`: complete the square on the other side. -/
theorem geSet_mem {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i ≤ c} ∈ S.Ω (4 * n + 16) 4 n := by
  have hdeg : (((MvPolynomial.C c - MvPolynomial.X (Fin.castAdd 1 i) : MvPolynomial (Fin (n + 1)) ℝ) -
      MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)))).totalDegree ≤ 2 := by
    refine le_trans (td_sub_le _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (td_sub_le _ _) ?_
      exact max_le (le_trans (td_C_le c) (Nat.zero_le 2)) (le_trans (td_X_le _) (Nat.le_succ 1))
    · exact td_sq_le (td_X_le (Fin.natAdd n (0 : Fin 1)))
  have hmem : {z : Fin (n + 1) → ℝ |
      MvPolynomial.eval z ((MvPolynomial.C c - MvPolynomial.X (Fin.castAdd 1 i) : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = 0} ∈ S.Ω (n + 1) 2 (n + 1) :=
    mem_mono (S.hyp (n + 1) ((MvPolynomial.C c - MvPolynomial.X (Fin.castAdd 1 i) : MvPolynomial (Fin (n + 1)) ℝ) -
      MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)))) (n + 1) 2 (le_refl _) hdeg
  have hproj : projLast {z : Fin (n + 1) → ℝ |
      MvPolynomial.eval z ((MvPolynomial.C c - MvPolynomial.X (Fin.castAdd 1 i) : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = 0} ∈ S.Ω (n + 2) 2 n :=
    S.proj hmem
  have heq : projLast {z : Fin (n + 1) → ℝ |
      MvPolynomial.eval z ((MvPolynomial.C c - MvPolynomial.X (Fin.castAdd 1 i) : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = 0} = {x : Fin n → ℝ | x i ≤ c} := by
    ext x
    have key : ∀ t : ℝ, MvPolynomial.eval (Fin.snoc x t) ((MvPolynomial.C c -
        MvPolynomial.X (Fin.castAdd 1 i) : MvPolynomial (Fin (n + 1)) ℝ) -
        MvPolynomial.X (Fin.natAdd n (0 : Fin 1)) *
          MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) = (c - x i) - t * t := by
      intro t
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X]
      rw [show Fin.castAdd 1 i = Fin.castSucc i from Fin.ext rfl,
        show (Fin.natAdd n (0 : Fin 1)) = Fin.last n from Fin.ext rfl,
        Fin.snoc_castSucc, Fin.snoc_last]
    constructor
    · rintro ⟨t, ht⟩
      simp only [Set.mem_ofPred_eq] at ht
      rw [key t] at ht
      change x i ≤ c
      nlinarith [sq_nonneg t]
    · intro hx
      refine ⟨Real.sqrt (c - x i), ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [key (Real.sqrt (c - x i))]
      have hsq : Real.sqrt (c - x i) * Real.sqrt (c - x i) = c - x i := by
        rw [← sq, Real.sq_sqrt (sub_nonneg.mpr hx)]
      rw [hsq]; ring
  rw [← heq]
  exact mem_mono hproj (4 * n + 16) 4 (by omega) (by omega)

theorem ltSet_mem {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | c < x i} ∈ S.Ω (4 * n + 20) 8 n := by
  have h := S.compl (geSet_mem (S := S) i c)
  have he : {x : Fin n → ℝ | x i ≤ c}ᶜ = {x : Fin n → ℝ | c < x i} := by
    ext x; simp [not_le]
  rw [he] at h
  exact mem_mono h (4 * n + 20) 8 (by omega) (by omega)

theorem gtSet_mem {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i < c} ∈ S.Ω (4 * n + 20) 8 n := by
  have h := S.compl (leSet_mem (S := S) i c)
  have he : {x : Fin n → ℝ | c ≤ x i}ᶜ = {x : Fin n → ℝ | x i < c} := by
    ext x; simp [not_le]
  rw [he] at h
  exact mem_mono h (4 * n + 20) 8 (by omega) (by omega)

/-- The open unit cube. -/
theorem openCube_mem {n : ℕ} :
    openCube n ∈ S.Ω (4 * n + 24) (16 * n + 16) n := by
  have hsingle : ∀ i : Fin n, {x : Fin n → ℝ | x i ∈ Set.Ioo (0 : ℝ) 1} ∈
      S.Ω (4 * n + 20 + 1) 16 n := by
    intro i
    have h1 : {x : Fin n → ℝ | 0 < x i} ∈ S.Ω (4 * n + 20) 8 n := ltSet_mem (S := S) i 0
    have h2 : {x : Fin n → ℝ | x i < 1} ∈ S.Ω (4 * n + 20) 8 n := gtSet_mem (S := S) i 1
    have h := S.inter (fun _ : Fin 2 => 8)
      (fun j : Fin 2 => if j = 0 then {x : Fin n → ℝ | 0 < x i} else {x : Fin n → ℝ | x i < 1})
      (by intro j
          fin_cases j
          · simpa using h1
          · simpa using h2)
    rw [show (∑ _ : Fin 2, 8) = 16 from by simp] at h
    have he : (⋂ j : Fin 2, if j = 0 then {x : Fin n → ℝ | 0 < x i}
        else {x : Fin n → ℝ | x i < 1}) = {x : Fin n → ℝ | x i ∈ Set.Ioo (0 : ℝ) 1} := by
      ext x; simp [Fin.forall_fin_two, Set.mem_Ioo]
    rw [he] at h
    exact h
  have h := S.inter (fun _ : Fin n => 16)
    (fun i => {x : Fin n → ℝ | x i ∈ Set.Ioo (0 : ℝ) 1}) (fun i => hsingle i)
  have hsum : (∑ _ : Fin n, 16) = 16 * n := by
    simp [Finset.sum_const, mul_comm]
  rw [hsum] at h
  have he : (⋂ i : Fin n, {x : Fin n → ℝ | x i ∈ Set.Ioo (0 : ℝ) 1}) = openCube n := by
    ext x; simp [openCube]
  rw [he] at h
  exact mem_mono h (4 * n + 24) (16 * n + 16) (by omega) (by omega)

theorem singleton_mem {n : ℕ} (p : Fin n → ℝ) :
    ({p} : Set (Fin n → ℝ)) ∈ S.Ω (4 * n + 20) (4 * n + 4) n := by
  have hsingle : ∀ i : Fin n, {x : Fin n → ℝ | x i = p i} ∈ S.Ω (4 * n + 16) 4 n := by
    intro i
    have hdeg : ((MvPolynomial.X i - MvPolynomial.C (p i) : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 :=
      le_trans (td_sub_le _ _) (max_le (td_X_le _) (le_trans (td_C_le _) (Nat.zero_le 1)))
    have heq : {x : Fin n → ℝ | x i = p i} =
        {x : Fin n → ℝ | MvPolynomial.eval x (MvPolynomial.X i -
          MvPolynomial.C (p i) : MvPolynomial (Fin n) ℝ) = 0} := by
      ext z
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact mem_mono (S.hyp n (MvPolynomial.X i - MvPolynomial.C (p i) : MvPolynomial (Fin n) ℝ))
      (4 * n + 16) 4 (by omega) (by omega)
  have h := S.inter (fun _ : Fin n => 4)
    (fun i => {x : Fin n → ℝ | x i = p i}) (fun i => hsingle i)
  have hsum : (∑ _ : Fin n, 4) = 4 * n := by
    simp [Finset.sum_const, mul_comm]
  rw [hsum] at h
  have he : (⋂ i : Fin n, {x : Fin n → ℝ | x i = p i}) = {p} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [he] at h
  exact mem_mono h (4 * n + 20) (4 * n + 4) (by omega) (by omega)

end Work.WilG5
