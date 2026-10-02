import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.ChernProduct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Graded series, the convolution product, and the associativity of the Whitney formula

The Chern classes of a complex gluing-data bundle `Z` of rank `m` form a *series*
`Work.LerayHirsch.chernSeries Z : (i : ℕ) → Coh ℤ (2*i) B`, `i ↦ c_i(Z)`.  The right-hand side of
the Whitney sum formula in degree `k`,

  `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)`,

is the `k`-th coefficient of the **convolution** `Work.LerayHirsch.convSeries x y` of the two series
(`i ↦ c_i(E)`, `j ↦ c_j(F)`), and the Whitney formula is the statement that `Z ↦ chernSeries Z` is
multiplicative for this convolution.

This module contains the algebra that makes that statement usable:

* the casts (`Work.Thom.cohTransport`) commute with the graded product
  (`cupH'_cast_left`, `cupH'_cast_right`), and the graded product `Work.Whitney.cupChern` is
  additive in each variable and **associative** (`cupChern_assoc`);
* the convolution `convSeries`, its defining equation, additivity, and its reconciliation with the
  explicit `Work.Whitney.chernProductSum` of `Submission/Work/Whitney/ChernProduct.lean`;
* **`convSeries_assoc`**: the convolution is associative.  This is the algebraic core of the
  induction that proves the Whitney formula: it is what allows one to reassociate the split
  `π^*E ≅ ℓ ⊕ Q` with a second summand.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Casts -/

/-- The `Eq.rec`-cast of a cohomology class is `Work.Thom.cohTransport`. -/
theorem eqRec_eq_cohTransport {n n' : ℕ} (h : n = n') (x : Coh ℤ n B) :
    (h ▸ x) = cohTransport h x := by
  cases h; rfl

/-- The transport `Work.Thom.cohTransport` only depends on the two degrees. -/
theorem cohTransport_eq_of_eq {n n' : ℕ} (h h' : n = n') :
    cohTransport h = (cohTransport h' : Coh ℤ n B → Coh ℤ n' B) := by
  rw [Subsingleton.elim h h']

theorem cohTransport_congr_proof {n n' : ℕ} {x : Coh ℤ n B} (h h' : n = n') :
    cohTransport h x = cohTransport h' x := by
  rw [Subsingleton.elim h h']

/-- **The cup product is associative, with the degree cast `(n + m) + k = n + (m + k)` on the
left**: the `Work.Cohomology.cupH'_assoc` in the direction in which it is used in a rewritten
convolution. -/
theorem cupH'_assoc_symm {a b c : ℕ} (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B)
    (z : Coh ℤ (2 * c) B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a + 2 * b) (2 * c)
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) x y) z
      = (Nat.add_assoc (2 * a) (2 * b) (2 * c)).symm ▸
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b + 2 * c) x
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * c) y z)) := by
  have h := Work.Cohomology.cupH'_assoc ℤ (Work.Whitney.ssB B) (2 * a) (2 * b) (2 * c) x y z
  rw [← h]
  exact (Work.Cohomology.eqRec_symm_eqRec_self3
    (M := fun k => (Work.Cohomology.SSetCochainComplex ℤ (Work.Whitney.ssB B)).homology k) _ _).symm

/-- **The degree cast commutes with the cup product in the first variable.** -/
theorem cupH'_cast_left {n n' m : ℕ} (h : n = n') (x : Coh ℤ n B) (y : Coh ℤ m B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n' m (cohTransport h x) y
      = cohTransport (by rw [h] : n + m = n' + m)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n m x y) := by
  cases h
  rw [cohTransport_rfl]
  congr 1

/-- **The degree cast commutes with the cup product in the second variable.** -/
theorem cupH'_cast_right {n m m' : ℕ} (h : m = m') (x : Coh ℤ n B) (y : Coh ℤ m B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n m' x (cohTransport h y)
      = cohTransport (by rw [h] : n + m = n + m')
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) n m x y) := by
  cases h
  rw [cohTransport_rfl]
  congr 1

/-! ## Triangular re-indexings of finite sums

Two elementary combinatorial lemmas about sums over the triangle `{(i,j) | i + j ≤ k}`.  They are
the bookkeeping that makes the convolution of series associative. -/

/-- A sum over `range (k+1)` with the guard `i + j ≤ k` in the inner variable is a sum over
`range (k+1-i)`. -/
theorem sum_range_sum_range_ite {M : Type*} [AddCommMonoid M] (i k : ℕ) (f : ℕ → M) :
    (∑ j ∈ Finset.range (k + 1), if i + j ≤ k then f j else 0)
      = ∑ j ∈ Finset.range (k + 1 - i), f j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun j _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A sum over `range (k+1-i)` is the guarded sum over `range (k+1)`, conversely. -/
theorem sum_range_eq_sum_range_ite {M : Type*} [AddCommMonoid M] (i k : ℕ) (f : ℕ → M) :
    (∑ j ∈ Finset.range (k + 1 - i), f j)
      = ∑ j ∈ Finset.range (k + 1), if i + j ≤ k then f j else 0 :=
  (sum_range_sum_range_ite i k f).symm

/-- **Triangular re-indexing**: the double sum over the triangle `{(a,b) | a + b ≤ k}` written with
the sum of the two indices as the outer variable is the same as the double sum written with the
first index as the outer variable. -/
theorem sum_range_triangle {M : Type*} [AddCommMonoid M] (G : ℕ → ℕ → M) :
    ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (i + 1), G a (i - a))
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - i), G i j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hL : (∑ i ∈ Finset.range (k + 1 + 1), ∑ a ∈ Finset.range (i + 1), G a (i - a))
        = (∑ i ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (i + 1), G a (i - a))
          + ∑ a ∈ Finset.range (k + 1 + 1), G a (k + 1 - a) := by
      rw [Finset.sum_range_succ]
    have hR : (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1 - i), G i j)
        = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - i), G i j)
          + ∑ a ∈ Finset.range (k + 1 + 1), G a (k + 1 - a) := by
      rw [Finset.sum_range_succ]
      have hinner : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1 - i), G i j)
          = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 - i), G i j)
            + ∑ a ∈ Finset.range (k + 1), G a (k + 1 - a) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
        rw [show k + 1 + 1 - i = (k + 1 - i) + 1 by omega, Finset.sum_range_succ]
      rw [hinner]
      have htail : (∑ j ∈ Finset.range (k + 1 + 1 - (k + 1)), G (k + 1) j) = G (k + 1) 0 := by
        rw [Nat.add_sub_cancel_left, Finset.sum_range_one]
      rw [htail]
      have hlast : (∑ a ∈ Finset.range (k + 1 + 1), G a (k + 1 - a))
          = (∑ a ∈ Finset.range (k + 1), G a (k + 1 - a)) + G (k + 1) 0 := by
        rw [Finset.sum_range_succ, Nat.sub_self]
      rw [hlast]
      abel
    rw [hL, ih, hR]

/-! ## The Chern series of a bundle, and the convolution of two series -/

/-- **The Chern series of a complex bundle** of rank `m`: the family `i ↦ c_i(Z)` of its Chern
classes, of degree `2*i`. -/
noncomputable def chernSeries {m : ℕ} {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) : (i : ℕ) → Coh ℤ (2 * i) B :=
  fun i => chernClass m i Z

/-- **One summand of the convolution**: `x_i ⌣ y_{k-i}`, extended by `0` when `i > k`. -/
noncomputable def convTerm (x y : (i : ℕ) → Coh ℤ (2 * i) B) (k i : ℕ) : Coh ℤ (2 * k) B :=
  if _h : i ≤ k then
    cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
      (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
        (x i) (y (k - i)))
  else 0

/-- The defining equation of `convTerm` when `i ≤ k`. -/
theorem convTerm_pos {x y : (i : ℕ) → Coh ℤ (2 * i) B} {k i : ℕ} (h : i ≤ k) :
    convTerm x y k i
      = cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
            (x i) (y (k - i))) := by
  rw [convTerm, dif_pos h]

/-- The defining equation of `convTerm` when `¬ i ≤ k`. -/
theorem convTerm_neg {x y : (i : ℕ) → Coh ℤ (2 * i) B} {k i : ℕ} (h : ¬ i ≤ k) :
    convTerm x y k i = 0 := by
  rw [convTerm, dif_neg h]

/-- The graded product is zero when its first argument is. -/
theorem cupChern_zero_left (a b : ℕ) (y : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern a b (0 : Coh ℤ (2 * a) B) y = 0 := by
  rw [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_left]
  exact map_zero (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm)

/-- **The convolution of two series**: the `k`-th coefficient of the graded product of
`x` and `y`, an element of `H^{2k}(B;ℤ)`.  This is the right-hand side of the Whitney sum formula
in degree `k`. -/
noncomputable def convSeries (x y : (i : ℕ) → Coh ℤ (2 * i) B) (k : ℕ) : Coh ℤ (2 * k) B :=
  ∑ i ∈ Finset.range (k + 1), convTerm x y k i

/-- **One summand of the triple convolution**: `x_i ⌣ (y_j ⌣ z_{k-i-j})`, extended by `0` when
`i + j > k`. -/
noncomputable def conv3Term (x y z : (i : ℕ) → Coh ℤ (2 * i) B) (k i j : ℕ) : Coh ℤ (2 * k) B :=
  if _h : i + j ≤ k then
    cohTransport (by omega : 2 * i + (2 * j + 2 * (k - i - j)) = 2 * k)
      (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * j + 2 * (k - i - j)) (x i)
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * j) (2 * (k - i - j)) (y j)
          (z (k - i - j))))
  else 0

/-- The defining equation of `conv3Term` when `i + j ≤ k`. -/
theorem conv3Term_pos {x y z : (i : ℕ) → Coh ℤ (2 * i) B} {k i j : ℕ} (h : i + j ≤ k) :
    conv3Term x y z k i j
      = cohTransport (by omega : 2 * i + (2 * j + 2 * (k - i - j)) = 2 * k)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * j + 2 * (k - i - j)) (x i)
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * j) (2 * (k - i - j)) (y j)
              (z (k - i - j)))) := by
  rw [conv3Term, dif_pos h]

/-- The defining equation of `conv3Term` when `¬ i + j ≤ k`. -/
theorem conv3Term_neg {x y z : (i : ℕ) → Coh ℤ (2 * i) B} {k i j : ℕ} (h : ¬ i + j ≤ k) :
    conv3Term x y z k i j = 0 := by
  rw [conv3Term, dif_neg h]

/-- **The triple convolution**: the `k`-th coefficient of `x ⌣ y ⌣ z`, i.e. the sum of
`x_i ⌣ (y_j ⌣ z_{k-i-j})` over all `i + j ≤ k`. -/
noncomputable def conv3 (x y z : (i : ℕ) → Coh ℤ (2 * i) B) (k : ℕ) : Coh ℤ (2 * k) B :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), conv3Term x y z k i j

/-- **The right-hand side of the Whitney sum formula is the convolution of the two Chern series**:
`Work.Whitney.chernProductSum Z₁ Z₂ k = convSeries (chernSeries Z₁) (chernSeries Z₂) k`. -/
theorem chernProductSum_eq_convSeries {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ) :
    Work.Whitney.chernProductSum Z₁ Z₂ k
      = convSeries (chernSeries Z₁) (chernSeries Z₂) k := by
  unfold Work.Whitney.chernProductSum convSeries convTerm chernSeries
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h : i ≤ k
  · rw [dif_pos h, dif_pos h, Work.Whitney.chernSummand_def, Work.Whitney.cupChern_def,
      Work.Whitney.cohTransport_trans]
  · rw [dif_neg h, dif_neg h]

/-! ## Extending a sum by vanishing terms -/

/-- A sum over `range n` of a function vanishing from `n` on is the sum over `range N` for any
`N ≥ n`. -/
theorem sum_range_extend {M : Type*} [AddCommMonoid M] {f : ℕ → M} {n N : ℕ} (hn : n ≤ N)
    (hf : ∀ j, n ≤ j → f j = 0) :
    (∑ j ∈ Finset.range n, f j) = ∑ j ∈ Finset.range N, f j := by
  rw [← Finset.sum_range_add_sum_Ico f hn]
  rw [Finset.sum_eq_zero (fun j hj => hf j (Finset.mem_Ico.mp hj).1), add_zero]

/-- **The degree-`E` and degree-`E'` forms of the triple product agree**, for `E = E'`: the
transport of the constant family `z` and of the two degrees is the only change. -/
theorem cupH'_tree_cast {a b : ℕ} {E E' : ℕ} (h : E = E')
    (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) (z : (t : ℕ) → Coh ℤ (2 * t) B) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b + 2 * E) x
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * E) y (z E))
      = ((congrArg (fun t => 2 * a + (2 * b + 2 * t)) h).symm) ▸
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * a) (2 * b + 2 * E') x
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * b) (2 * E') y (z E'))) := by
  cases h
  rfl

/-- **The first factor of the associativity of the convolution.**  The `i`-th summand of
`convSeries x (convSeries y z)` is the sum over `j` of the summands of the triple convolution. -/
theorem convTerm_convSeries_right (x y z : (i : ℕ) → Coh ℤ (2 * i) B) (k i : ℕ) :
    convTerm x (convSeries y z) k i
      = ∑ j ∈ Finset.range (k + 1), conv3Term x y z k i j := by
  by_cases hik : i ≤ k
  · rw [convTerm_pos hik]
    have hsum : convSeries y z (k - i) = ∑ j ∈ Finset.range (k + 1), convTerm y z (k - i) j := by
      show (∑ j ∈ Finset.range (k - i + 1), convTerm y z (k - i) j) = _
      exact sum_range_extend (f := fun j => convTerm y z (k - i) j)
        (by omega : k - i + 1 ≤ k + 1) (fun j hj => convTerm_neg (by omega))
    rw [hsum]
    have h1 : Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i)
          (∑ j ∈ Finset.range (k + 1), convTerm y z (k - i) j)
        = ∑ j ∈ Finset.range (k + 1),
            Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i)
              (convTerm y z (k - i) j) :=
      map_sum (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i))
        (fun j => convTerm y z (k - i) j) (Finset.range (k + 1))
    rw [h1]
    have h2 : cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
          (∑ j ∈ Finset.range (k + 1),
            Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i)
              (convTerm y z (k - i) j))
        = ∑ j ∈ Finset.range (k + 1),
            cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
              (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i)
                (convTerm y z (k - i) j)) :=
      map_sum (Work.Thom.cohTransportLM (by omega : 2 * i + 2 * (k - i) = 2 * k))
        (fun j => Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i)
          (convTerm y z (k - i) j)) (Finset.range (k + 1))
    rw [h2]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : i + j ≤ k
    · have hterm : cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)) (x i)
            (convTerm y z (k - i) j)) = conv3Term x y z k i j := by
        rw [convTerm_pos (by omega : j ≤ k - i),
          cupH'_cast_right (n := 2 * i) (m := 2 * j + 2 * (k - i - j)) (m' := 2 * (k - i))
            (h := (by omega : 2 * j + 2 * (k - i - j) = 2 * (k - i))),
          Work.Whitney.cohTransport_trans, conv3Term_pos hij]
      rw [hterm]
    · rw [convTerm_neg (by omega : ¬ j ≤ k - i), map_zero, conv3Term_neg hij]
      exact map_zero (Work.Thom.cohTransportLM (by omega : 2 * i + 2 * (k - i) = 2 * k))
  · rw [convTerm_neg hik]
    exact (Finset.sum_eq_zero fun j hj => conv3Term_neg (by
      have := Finset.mem_range.mp hj; omega)).symm

/-- **The second factor of the associativity of the convolution.**  The `i`-th summand of
`convSeries (convSeries x y) z` is the sum over `a ≤ i` of the triple convolution summands with the
roles of `x` and `y` interchanged. -/
theorem convTerm_convSeries_left (x y z : (i : ℕ) → Coh ℤ (2 * i) B) (k i : ℕ) :
    convTerm (convSeries x y) z k i
      = ∑ a ∈ Finset.range (i + 1), conv3Term x y z k a (i - a) := by
  by_cases hik : i ≤ k
  · rw [convTerm_pos hik]
    have hsum : convSeries x y i = ∑ a ∈ Finset.range (i + 1), convTerm x y i a := rfl
    rw [hsum]
    have h1a : Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
          (∑ a ∈ Finset.range (i + 1), convTerm x y i a)
        = ∑ a ∈ Finset.range (i + 1),
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
              (convTerm x y i a)) :=
      map_sum (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i)))
        (fun a => convTerm x y i a) (Finset.range (i + 1))
    rw [h1a, LinearMap.sum_apply]
    have h2 : cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
          (∑ a ∈ Finset.range (i + 1),
            (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
              (convTerm x y i a)) (z (k - i)))
        = ∑ a ∈ Finset.range (i + 1),
            cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
              ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
                (convTerm x y i a)) (z (k - i))) :=
      map_sum (Work.Thom.cohTransportLM (by omega : 2 * i + 2 * (k - i) = 2 * k))
        (fun a => (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
          (convTerm x y i a)) (z (k - i))) (Finset.range (i + 1))
    rw [h2]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hai : a ≤ i := by have := Finset.mem_range.mp ha; omega
    have hterm : cohTransport (by omega : 2 * i + 2 * (k - i) = 2 * k)
          ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
            (convTerm x y i a)) (z (k - i))) = conv3Term x y z k a (i - a) := by
      rw [convTerm_pos hai,
        cupH'_cast_left (n := 2 * a + 2 * (i - a)) (n' := 2 * i) (m := 2 * (k - i))
          (h := (by omega : 2 * a + 2 * (i - a) = 2 * i)),
        Work.Whitney.cohTransport_trans,
        cupH'_assoc_symm (a := a) (b := i - a) (c := k - i) (x a) (y (i - a)) (z (k - i)),
        eqRec_eq_cohTransport (B := B), Work.Whitney.cohTransport_trans,
        conv3Term_pos (by omega : a + (i - a) ≤ k),
        cupH'_tree_cast (a := a) (b := i - a) (E := k - i) (E' := k - a - (i - a))
          (by omega : k - i = k - a - (i - a)) (x a) (y (i - a)) z,
        eqRec_eq_cohTransport (B := B), Work.Whitney.cohTransport_trans]
    rw [hterm]
  · rw [convTerm_neg hik]
    exact (Finset.sum_eq_zero fun a ha => conv3Term_neg (by
      have := Finset.mem_range.mp ha; omega)).symm

/-- **The convolution of series is associative.**  This is the algebraic core of the induction that
proves the Whitney sum formula. -/
theorem convSeries_assoc (x y z : (i : ℕ) → Coh ℤ (2 * i) B) (k : ℕ) :
    convSeries (convSeries x y) z k = convSeries x (convSeries y z) k := by
  have hA : convSeries x (convSeries y z) k
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), conv3Term x y z k i j := by
    show (∑ i ∈ Finset.range (k + 1), convTerm x (convSeries y z) k i) = _
    exact Finset.sum_congr rfl fun i _ => convTerm_convSeries_right x y z k i
  have hB : convSeries (convSeries x y) z k
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), conv3Term x y z k i j := by
    rw [show convSeries (convSeries x y) z k
        = ∑ i ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (i + 1), conv3Term x y z k a (i - a) from
      Finset.sum_congr rfl fun i _ => convTerm_convSeries_left x y z k i]
    rw [sum_range_triangle (fun a b => conv3Term x y z k a b)]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact sum_range_extend (f := fun j => conv3Term x y z k i j)
      (by have := Finset.mem_range.mp hi; omega : k + 1 - i ≤ k + 1)
      (fun j hj => conv3Term_neg (by omega))
  rw [hA, hB]

end

end Work.LerayHirsch
