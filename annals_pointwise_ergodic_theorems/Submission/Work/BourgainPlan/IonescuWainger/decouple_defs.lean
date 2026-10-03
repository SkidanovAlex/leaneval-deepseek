import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_hilbert

/-!
# Definitions for the probabilistic decoupling of the hypersystem Khintchine inequality

Tao (arXiv:2008.05066, proof of Theorem `sys-ortho`(ii)) decouples a hypersystem
`(f_A)_{A ∈ C(S,≤k)}` by averaging over the `k^{|S|}` colourings `c : S → {1,…,k}` and iterating
the system form on the `k` colour classes.  This file implements that machinery.

For a colouring `c` of `S` into `k` classes, the *transversal* tuples `σ : Fin k → S` (with
`c (σ j) = j`) index a choice of one element from each colour class; the level-`i` sum `lvl i τ`
(for a partial tuple `τ : Fin i → S`) is the sum of `f (tupleSet σ)` over all transversal tuples
extending `τ`.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset Filter
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X] {α : Type*} [DecidableEq α]

/-- Appending a last coordinate to a tuple with a constant index type. -/
def snocConst {β : Type*} {n : ℕ} (τ : Fin n → β) (a : β) : Fin (n + 1) → β :=
  Fin.snoc (α := fun _ => β) τ a

@[simp] theorem snocConst_castSucc {β : Type*} {n : ℕ} (τ : Fin n → β) (a : β) (j : Fin n) :
    snocConst τ a (Fin.castSucc j) = τ j := by
  simpa [snocConst] using Fin.snoc_castSucc (α := fun _ => β) a τ j

@[simp] theorem snocConst_last {β : Type*} {n : ℕ} (τ : Fin n → β) (a : β) :
    snocConst τ a (Fin.last n) = a := by
  simpa [snocConst] using Fin.snoc_last (α := fun _ => β) a τ

theorem castLE_castSucc {i k : ℕ} (hi : i ≤ k) (hi' : i + 1 ≤ k) (j : Fin i) :
    Fin.castLE hi' (Fin.castSucc j) = Fin.castLE hi j := Fin.ext rfl

theorem castLE_last' {i k : ℕ} (hi' : i + 1 ≤ k) :
    Fin.castLE hi' (Fin.last i) = (⟨i, by omega⟩ : Fin k) := Fin.ext rfl

/-- The `Finset α` underlying a tuple of elements of `S`. -/
def tupleSet (S : Finset α) {k : ℕ} (σ : Fin k → S) : Finset α :=
  Finset.univ.image fun j => (σ j).1

/-- The transversal tuples of a colouring: the tuple `σ` meets the `j`-th colour class at
position `j`. -/
def transversalTuples (S : Finset α) (k : ℕ) (c : S → Fin k) : Finset (Fin k → S) :=
  Finset.univ.filter fun σ => ∀ j, c (σ j) = j

/-- The level-`i` partial sum of the decoupling: sum `f (tupleSet σ)` over the transversal tuples
`σ` whose first `i` coordinates are `τ`. -/
def lvl (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (τ : Fin i → S) : X → ℂ :=
  fun x => ∑ σ ∈ (transversalTuples S k c).filter
    (fun σ => ∀ j : Fin i, σ (Fin.castLE hi j) = τ j), f (tupleSet S σ) x

theorem tupleSet_subset (S : Finset α) {k : ℕ} (σ : Fin k → S) : tupleSet S σ ⊆ S := by
  intro a ha
  simp only [tupleSet, mem_image, mem_univ, true_and] at ha
  obtain ⟨j, rfl⟩ := ha
  exact (σ j).2

theorem tupleSet_card_le (S : Finset α) {k : ℕ} (σ : Fin k → S) :
    (tupleSet S σ).card ≤ k := by
  calc (tupleSet S σ).card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

theorem lvl_aemeasurable (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (τ : Fin i → S) (μ : Measure X)
    (hm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ) :
    AEMeasurable (lvl S k c i hi f τ) μ := by
  classical
  refine Finset.aemeasurable_fun_sum _ (fun σ hσ => ?_)
  exact hm _ (tupleSet_subset S σ) (tupleSet_card_le S σ)

/-- The level recursion: summing the level-`i+1` partial sums over the `i`-th coordinate gives the
level-`i` partial sum. -/
theorem lvl_step (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi : i ≤ k)
    (hi' : i + 1 ≤ k) (f : Finset α → X → ℂ) (τ : Fin i → S) (x : X) :
    ∑ a : S, lvl S k c (i + 1) hi' f (snocConst τ a) x = lvl S k c i hi f τ x := by
  classical
  have key : ∀ a : S,
      (transversalTuples S k c).filter
          (fun σ => ∀ j : Fin (i + 1), σ (Fin.castLE hi' j) = snocConst τ a j)
        = ((transversalTuples S k c).filter
            (fun σ => ∀ j : Fin i, σ (Fin.castLE hi j) = τ j)).filter
          (fun σ => σ (Fin.castLE hi' (Fin.last i)) = a) := by
    intro a
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro σ _
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · have h1 := h (Fin.castSucc j)
        rw [snocConst_castSucc, castLE_castSucc hi hi' j] at h1
        exact h1
      · have h1 := h (Fin.last i)
        rwa [snocConst_last] at h1
    · rintro ⟨h1, h2⟩ j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [snocConst_last]
        exact h2
      · rw [snocConst_castSucc, castLE_castSucc hi hi' j']
        exact h1 j'
  calc ∑ a : S, lvl S k c (i + 1) hi' f (snocConst τ a) x
      = ∑ a : S, ∑ σ ∈ ((transversalTuples S k c).filter
            (fun σ => ∀ j : Fin i, σ (Fin.castLE hi j) = τ j)),
          (if σ (Fin.castLE hi' (Fin.last i)) = a then f (tupleSet S σ) x else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [lvl, key a, Finset.sum_filter]
    _ = ∑ σ ∈ ((transversalTuples S k c).filter
            (fun σ => ∀ j : Fin i, σ (Fin.castLE hi j) = τ j)),
          ∑ a : S, (if σ (Fin.castLE hi' (Fin.last i)) = a then f (tupleSet S σ) x else 0) :=
        Finset.sum_comm
    _ = ∑ σ ∈ ((transversalTuples S k c).filter
            (fun σ => ∀ j : Fin i, σ (Fin.castLE hi j) = τ j)), f (tupleSet S σ) x := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    _ = lvl S k c i hi f τ x := by rw [lvl]

/-- Reindexing a sum over `Fin (i+1) → S` as a sum over the last coordinate and the initial tuple. -/
theorem sum_snoc {M : Type*} [AddCommMonoid M] (S : Finset α) (i : ℕ)
    (F : (Fin (i + 1) → S) → M) :
    ∑ σ : Fin (i + 1) → S, F σ = ∑ a : S, ∑ τ : Fin i → S, F (snocConst τ a) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (i + 1) => S)) F, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro τ _
  congr 1

/-- The `EuclideanSpace`-valued family of level-`i+1` partial sums indexed by the `i`-th coordinate:
the `a`-th member is the vector of partial sums extending the partial tuple `τ` by `a`. -/
noncomputable def hvec (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (a : S) : X → EuclideanSpace ℂ (Fin i → S) :=
  fun x => WithLp.toLp 2 (fun τ => lvl S k c (i + 1) hi' f (snocConst τ a) x)

/-- Summing the level-`i+1` vectors over the `i`-th coordinate gives the vector of level-`i`
partial sums. -/
theorem hvec_sum (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi : i ≤ k) (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (x : X) :
    (∑ a : S, hvec S k c i hi' f a x)
      = WithLp.toLp 2 (fun τ : Fin i → S => lvl S k c i hi f τ x) := by
  rw [WithLp.ext_iff]
  rw [WithLp.ofLp_sum, WithLp.ofLp_toLp]
  funext τ
  rw [Finset.sum_apply]
  exact lvl_step S k c hi hi' f τ x

/-- The squared norm of the level-`i` vector is the level-`i` square function. -/
theorem norm_sq_sum_hvec (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi : i ≤ k)
    (hi' : i + 1 ≤ k) (f : Finset α → X → ℂ) (x : X) :
    ‖∑ a : S, hvec S k c i hi' f a x‖ ^ 2 = ∑ τ : Fin i → S, ‖lvl S k c i hi f τ x‖ ^ 2 := by
  rw [hvec_sum, EuclideanSpace.norm_sq_eq]

/-- The sum of the squared norms of the level-`i+1` vectors is the level-`i+1` square function. -/
theorem sum_norm_sq_hvec (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (x : X) :
    ∑ a : S, ‖hvec S k c i hi' f a x‖ ^ 2
      = ∑ σ : Fin (i + 1) → S, ‖lvl S k c (i + 1) hi' f σ x‖ ^ 2 := by
  have h1 : ∀ a : S, ‖hvec S k c i hi' f a x‖ ^ 2
      = ∑ τ : Fin i → S, ‖lvl S k c (i + 1) hi' f (snocConst τ a) x‖ ^ 2 := by
    intro a
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => h1 a), sum_snoc S i (fun σ => ‖lvl S k c (i + 1) hi' f σ x‖ ^ 2)]

/-- The level-`i` square function (in `ℝ≥0∞`). -/
noncomputable def sqf (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (x : X) : ℝ≥0∞ :=
  ∑ τ : Fin i → S, ‖lvl S k c i hi f τ x‖ₑ ^ (2 : ℝ)

/-- The squared norm of a level-`i+1` vector is the sum of the squared norms of its coordinates. -/
theorem enorm_sq_hvec (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (a : S) (x : X) :
    ‖hvec S k c i hi' f a x‖ₑ ^ (2 : ℝ)
      = ∑ τ : Fin i → S, ‖lvl S k c (i + 1) hi' f (snocConst τ a) x‖ₑ ^ (2 : ℝ) := by
  rw [← ofReal_norm (hvec S k c i hi' f a x),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
    EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun τ _ => pow_nonneg (norm_nonneg _) 2)]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← ofReal_norm (lvl S k c (i + 1) hi' f (snocConst τ a) x),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  rfl

/-- Summing the squared norms of the level-`i+1` vectors over the last coordinate gives the
level-`i+1` square function. -/
theorem sum_enorm_sq_hvec (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (x : X) :
    ∑ a : S, ‖hvec S k c i hi' f a x‖ₑ ^ (2 : ℝ) = sqf S k c (i + 1) hi' f x := by
  rw [Finset.sum_congr rfl (fun a _ => enorm_sq_hvec S k c hi' f a x), sqf]
  exact (sum_snoc S i (fun σ => ‖lvl S k c (i + 1) hi' f σ x‖ₑ ^ (2 : ℝ))).symm

/-- The squared norm of the level-`i` vector (in `ℝ≥0∞`) is the level-`i` square function. -/
theorem enorm_sq_sum_hvec (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi : i ≤ k)
    (hi' : i + 1 ≤ k) (f : Finset α → X → ℂ) (x : X) :
    ‖∑ a : S, hvec S k c i hi' f a x‖ₑ ^ (2 : ℝ) = sqf S k c i hi f x := by
  rw [← ofReal_norm (∑ a : S, hvec S k c i hi' f a x),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  rw [Real.rpow_two, norm_sq_sum_hvec S k c hi hi' f x, sqf,
    ENNReal.ofReal_sum_of_nonneg (fun τ _ => pow_nonneg (norm_nonneg _) 2)]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← ofReal_norm (lvl S k c i hi f τ x),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- The fibre of the level-`i` partial sum: the transversal tuples whose first `i` coordinates are
`η`. -/
def fib (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k) (η : Fin i → S) :
    Finset (Fin k → S) :=
  (transversalTuples S k c).filter (fun σ => ∀ j : Fin i, σ (Fin.castLE hi j) = η j)

theorem lvl_eq_sum_fib (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (η : Fin i → S) (x : X) :
    lvl S k c i hi f η x = ∑ σ ∈ fib S k c i hi η, f (tupleSet S σ) x := rfl

theorem mem_fib {S : Finset α} {k : ℕ} {c : S → Fin k} {i : ℕ} {hi : i ≤ k} {η : Fin i → S}
    {σ : Fin k → S} :
    σ ∈ fib S k c i hi η ↔ σ ∈ transversalTuples S k c ∧ ∀ j : Fin i, σ (Fin.castLE hi j) = η j :=
  Finset.mem_filter

/-- The `i`-th coordinate of a transversal tuple in the fibre of `η` is the last coordinate of
`η`. -/
theorem coord_fib (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi : i < k) (hi' : i + 1 ≤ k)
    {η : Fin (i + 1) → S} {σ : Fin k → S} (hσ : σ ∈ fib S k c (i + 1) hi' η) :
    σ ⟨i, hi⟩ = η (Fin.last i) := by
  have h := (mem_fib.mp hσ).2 (Fin.last i)
  rwa [castLE_last'] at h


/-- The total mass of the transversal tuples. -/
noncomputable def Vmass (S : Finset α) (k : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ)
    (x : X) : ℝ :=
  ∑ ρ ∈ transversalTuples S k c, ‖f (tupleSet S ρ) x‖

/-- The level-`i` square function as a (real) number. -/
noncomputable def sqfR (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (x : X) : ℝ :=
  ∑ τ : Fin i → S, ‖lvl S k c i hi f τ x‖ ^ 2

/-- The `ℝ≥0∞`-valued level-`i` square function is the real one, coerced. -/
theorem sqf_eq_ofReal (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (x : X) :
    sqf S k c i hi f x = ENNReal.ofReal (sqfR S k c i hi f x) := by
  rw [sqf, sqfR, ENNReal.ofReal_sum_of_nonneg (fun τ _ => pow_nonneg (norm_nonneg _) 2)]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← ofReal_norm (lvl S k c i hi f τ x),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- The level-`i` partial sums are dominated by the total mass of the transversal tuples. -/
theorem norm_lvl_le (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (τ : Fin i → S) (x : X) :
    ‖lvl S k c i hi f τ x‖ ≤ Vmass S k c f x := by
  rw [lvl_eq_sum_fib]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ρ _ _ => norm_nonneg _))

/-- The level-`i` square function is bounded by a constant times the square of the total mass of
the transversal tuples. -/
theorem sqfR_le (S : Finset α) (k : ℕ) (c : S → Fin k) (i : ℕ) (hi : i ≤ k)
    (f : Finset α → X → ℂ) (x : X) :
    sqfR S k c i hi f x ≤ ((Finset.univ : Finset (Fin i → S)).card : ℝ) * Vmass S k c f x ^ 2 := by
  rw [sqfR]
  calc ∑ τ : Fin i → S, ‖lvl S k c i hi f τ x‖ ^ 2
      ≤ ∑ _τ : Fin i → S, Vmass S k c f x ^ 2 := by
        apply Finset.sum_le_sum
        intro τ _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lvl_le S k c i hi f τ x) 2
    _ = ((Finset.univ : Finset (Fin i → S)).card : ℝ) * Vmass S k c f x ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Power means for finite sums of nonnegative reals with natural exponent. -/
theorem sum_pow_le_card_mul {β : Type*} (s : Finset β) (u : β → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ s, u i) ^ n ≤ (s.card : ℝ) ^ (n - 1) * ∑ i ∈ s, u i ^ n := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := s) (f := u)
    (p := (n : ℝ)) (by exact_mod_cast hn) hu
  simpa only [Real.rpow_natCast, show ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) by
    push_cast [Nat.cast_sub hn]; ring] using h



/-- The level square functions only depend on the level, not on the proof of `i ≤ k`. -/
theorem sqf_congr {S : Finset α} {k : ℕ} {c : S → Fin k} {f : Finset α → X → ℂ} {i i' : ℕ}
    (h : i = i') (hi : i ≤ k) (hi' : i' ≤ k) :
    sqf S k c i hi f = sqf S k c i' hi' f := by
  subst h
  rfl

end Work.BourgainPlan.IonescuWainger
