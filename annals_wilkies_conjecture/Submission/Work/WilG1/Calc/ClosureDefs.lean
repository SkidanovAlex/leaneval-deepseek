/-
  WilG1 / Calc / ClosureDefs.

  The objects used by `Work.WilG1.Calc.closure_mem`: the topological closure of an `Ω`-set is an
  `Ω`-set, with explicit format and degree bounds.

  ## The construction

  Fix `X ⊆ ℝⁿ`.  Write `Σ(x,y) = Σ_{j} (y_j - x_j)^2`.  The closure criterion used below is

    `x ∈ closure X ↔ ∀ r ≠ 0, ∃ y ∈ X, Σ(x,y) ≤ r^2`,

  so, since `∃ s, Σ(x,y) + s^2 = r^2 ⟺ Σ(x,y) ≤ r^2` over `ℝ`,

    `(closure X)ᶜ = {x | ∃ r ≠ 0, ¬ ∃ y s, y ∈ X ∧ Σ(x,y) + s^2 = r^2}`.

  The set on the right is a projection of the `Ω`-set

    `bigJ X = cylSet X ∩ hypSet n  ⊆  ℝ^{n + (n+1) + 1}`

  whose coordinates are laid out as `(x | r | y | s)`: the first `n` coordinates are `x`, the
  `n`-th is `r`, the next `n` are `y` and the last one is `s` (so the pair `(x,r)` — the block
  that survives the projection — comes first).  `cylSet X` is the cylinder `y ∈ X`
  (`liftLast` followed by `SOMin.prod_right`), and `hypSet n` is the zero set of the polynomial
  `bigP n = Σ_j (X_{y_j} - X_{x_j})^2 + X_s^2 - X_r^2`, whose total degree is `2`.

  `finalC X ⊆ ℝ^{n+1}` is `{r ≠ 0} ∩ (projN (n+1) (bigJ X))ᶜ`, and

    `projLast (finalC X) = (closure X)ᶜ`

  (proved in `Work.WilG1.Calc.ClosureMain`).
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Calc

open WilkiesDesign WilkiesConjecture

/-! ## 1. The index layout of the big space `ℝ^{n + (n+1) + 1}`

The big space is `Fin (n + (n+1) + 1) → ℝ`, split as the *first* block `(x | r)` of size `n+1`
and the *last* block `(y | s)` of size `n+1`, so that `projN (n+1)` keeps `(x,r)`. -/

/-- The index of the `j`-th `x`-coordinate. -/
def bxIdx {n : ℕ} (j : Fin n) : Fin (n + (n + 1) + 1) := ⟨j.val, by omega⟩

/-- The index of the `r`-coordinate. -/
def brIdx (n : ℕ) : Fin (n + (n + 1) + 1) := ⟨n, by omega⟩

/-- The index of the `j`-th `y`-coordinate. -/
def byIdx {n : ℕ} (j : Fin n) : Fin (n + (n + 1) + 1) := ⟨n + 1 + j.val, by omega⟩

/-- The index of the `s`-coordinate. -/
def bsIdx (n : ℕ) : Fin (n + (n + 1) + 1) := ⟨n + (n + 1), by omega⟩

/-- The polynomial `Σ_j (y_j - x_j)^2 + s^2 - r^2` on the big space. -/
def bigP (n : ℕ) : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ :=
  (∑ j : Fin n, (MvPolynomial.X (byIdx j) - MvPolynomial.X (bxIdx j)) ^ 2)
    + (MvPolynomial.X (bsIdx n)) ^ 2 - (MvPolynomial.X (brIdx n)) ^ 2

/-! ## 2. The three sets -/

/-- The cylinder over `X`: the `y`-block of the big space lies in `X`.  Built as
`liftLast (n+1) X` (which puts `X` on the last `n` coordinates of `Fin (n + (n+1))`, leaving the
first `n+1` free) followed by the addition of the dummy `s`-coordinate. -/
def cylSet {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + (n + 1) + 1) → ℝ) :=
  {z | Fin.init z ∈ WilG5.liftLast (n + 1) X}

/-- The hypersurface `bigP n = 0`. -/
def hypSet (n : ℕ) : Set (Fin (n + (n + 1) + 1) → ℝ) :=
  {z | MvPolynomial.eval z (bigP n) = 0}

/-- The big set: `y ∈ X` and `Σ_j (y_j-x_j)^2 + s^2 = r^2`. -/
def bigJ {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + (n + 1) + 1) → ℝ) :=
  cylSet X ∩ hypSet n

/-- The arithmetic identity turning the big space into `(ℝ^{n+1}) × (ℝ^{n+1})`. -/
theorem bigSpace_eq (n : ℕ) : n + (n + 1) + 1 = (n + 1) + (n + 1) := by omega

/-- The final set in `ℝ^{n+1}`: `r ≠ 0` and no `(y,s)` in the big set above `(x,r)`. -/
def finalC {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {v : Fin (n + 1) → ℝ | v (Fin.last n) ≠ 0} ∩
    (WilG5.projN (n + 1) ((bigSpace_eq n) ▸ bigJ X))ᶜ

/-! ## 3. Degree bookkeeping for `bigP` -/

/-- Total degree of a finite sum is bounded by the maximum of the total degrees. -/
theorem td_sum_le {σ : Type*} {R : Type*} [CommSemiring R] {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial σ R) {C : ℕ} (hf : ∀ i ∈ s, (f i).totalDegree ≤ C) :
    (∑ i ∈ s, f i).totalDegree ≤ C := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    refine le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (hf a (Finset.mem_insert_self a s)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

/-- `(p - q)^2` has total degree at most `2` when `p` and `q` have total degree at most `1`. -/
theorem td_sq_sub_le {σ : Type*} {R : Type*} [CommRing R] {p q : MvPolynomial σ R}
    (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1) : ((p - q) ^ 2).totalDegree ≤ 2 := by
  rw [pow_two]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have h : (p - q).totalDegree ≤ 1 :=
    le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hp hq)
  omega

theorem bigP_totalDegree_le (n : ℕ) : (bigP n).totalDegree ≤ 2 := by
  have hsum : (∑ j : Fin n, (MvPolynomial.X (byIdx j) - MvPolynomial.X (bxIdx j)) ^ 2
      : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ).totalDegree ≤ 2 := by
    refine td_sum_le Finset.univ _ ?_
    intro j _
    exact td_sq_sub_le (le_of_eq (MvPolynomial.totalDegree_X _))
      (le_of_eq (MvPolynomial.totalDegree_X _))
  have hs : ((MvPolynomial.X (bsIdx n)) ^ 2 : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ).totalDegree ≤ 2 := by
    have h1 := MvPolynomial.totalDegree_mul (MvPolynomial.X (bsIdx n))
      (MvPolynomial.X (bsIdx n) : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ)
    rw [← pow_two] at h1
    have h2 : (MvPolynomial.X (bsIdx n) : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ).totalDegree = 1 :=
      MvPolynomial.totalDegree_X _
    omega
  have hr : ((MvPolynomial.X (brIdx n)) ^ 2 : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ).totalDegree ≤ 2 := by
    have h1 := MvPolynomial.totalDegree_mul (MvPolynomial.X (brIdx n))
      (MvPolynomial.X (brIdx n) : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ)
    rw [← pow_two] at h1
    have h2 : (MvPolynomial.X (brIdx n) : MvPolynomial (Fin (n + (n + 1) + 1)) ℝ).totalDegree = 1 :=
      MvPolynomial.totalDegree_X _
    omega
  unfold bigP
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ hr)
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le hsum hs)

/-! ## 4. Membership: the cylinder and the hypersurface -/

theorem cylSet_mem {S : SOMin} {n a D : ℕ} {b : Polynomial ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a (b.eval D) n) :
    cylSet X ∈ S.Ω (a + n + 2) (b.eval D) (n + (n + 1) + 1) := by
  have h1 : WilG5.liftLast (n + 1) X ∈ S.Ω (a + (n + 1)) (b.eval D) (n + (n + 1)) :=
    WilG5.liftLast_mem (S := S) (n + 1) a (b.eval D) hX
  have h2 : {z : Fin (n + (n + 1) + 1) → ℝ | Fin.init z ∈ WilG5.liftLast (n + 1) X} ∈
      S.Ω ((a + (n + 1)) + 1) (b.eval D) (n + (n + 1) + 1) := S.prod_right h1
  exact WilG5.mem_mono h2 (a + n + 2) (b.eval D) (by omega) le_rfl

theorem hypSet_mem {S : SOMin} (n : ℕ) :
    hypSet n ∈ S.Ω (n + (n + 1) + 1) 2 (n + (n + 1) + 1) :=
  WilG5.mem_mono (S.hyp (n + (n + 1) + 1) (bigP n)) _ 2 le_rfl (bigP_totalDegree_le n)

/-- Membership in the cylinder, in coordinates: the block of `z` at positions `n+1,…,2n` is a
point of `X`. -/
theorem mem_cylSet_iff {n : ℕ} {X : Set (Fin n → ℝ)} {z : Fin (n + (n + 1) + 1) → ℝ} :
    z ∈ cylSet X ↔ (fun j : Fin n => z (byIdx j)) ∈ X := by
  rw [cylSet, Set.mem_ofPred_eq, WilG5.liftLast, Set.mem_ofPred_eq]
  have hfun : (fun j : Fin n => Fin.init z (WilG5.lidx (n + 1) j)) =
      (fun j : Fin n => z (byIdx j)) := by
    funext j
    show z (Fin.castSucc (WilG5.lidx (n + 1) j)) = z (byIdx j)
    congr 1
  rw [hfun]

/-- Membership in the hypersurface, in coordinates. -/
theorem mem_hypSet_iff {n : ℕ} {z : Fin (n + (n + 1) + 1) → ℝ} :
    z ∈ hypSet n ↔
      (∑ j : Fin n, (z (byIdx j) - z (bxIdx j)) ^ 2) + z (bsIdx n) ^ 2 - z (brIdx n) ^ 2 = 0 := by
  rw [hypSet, Set.mem_ofPred_eq, bigP]
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_sum,
    MvPolynomial.eval_pow, MvPolynomial.eval_X]

end Work.WilG1.Calc
