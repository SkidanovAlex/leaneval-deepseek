import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.simple_valuation_binary_union
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_inclusionExclusion
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_zero_on_axisBoxes
import Submission.Commons.Geometry.Convex.Hadwiger.klain333_from_cylinders
import Submission.Commons.Geometry.Convex.Hadwiger.givens_word_unit
import Submission.Commons.Geometry.Convex.Hadwiger.imageLIE_admissible

open Set Filter
open scoped Pointwise Topology BigOperators


/-! ## Inlined copy of the orientation machinery

`Commons.Geometry.Convex.Hadwiger.klain333_boxes_all_orientations` cannot be
imported here: its transitive import `orthogonal_word_decomposition` declares a
top-level abbreviation `Commons.Geometry.Convex.Hadwiger.E`, and the identically
named abbreviation declared by
`Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg` (which
is indispensable here, being in the closure of `klain333_from_cylinders`) cannot
coexist with it in a single Lean environment.

Accordingly the orientation machinery (that file together with its import
`orthogonal_word_decomposition`) is inlined below verbatim, inside the fresh
namespace `KlainInlineVD` (so that its many auxiliary names do not collide with
the other commons modules), and with the offending abbreviation renamed
`E` -> `EVID`.  Nothing else is changed: statements and proofs are those of the
two commons files.
-/
open scoped BigOperators

noncomputable section

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

/-! # Orthogonal word decomposition

Every linear isometry `ρ` of `EuclideanSpace ℝ (Fin n)` is a product of maps of two kinds:
coordinate-plane rotations (by angles in `[0, π/2]`) and coordinate reflections.  We prove this
by constructing the word explicitly: first any element of `O(n)` is written as a product of
plane rotations (with arbitrary angle parameters) and coordinate reflections (Section on
generation, done by induction on the dimension and Givens elimination of a unit vector), and
then every plane rotation is itself expanded, by splitting the sign pattern of its
`(c, s)` parameters, into products of quarter-turns and sign-restricted rotations. -/

/-! ## Function-level rotations

We first work with vectors as plain functions `Fin n → ℝ`; the rotation mixing coordinates
`i` and `j` has explicit coordinate formulas, and we record its algebra (invertibility,
additivity, homogeneity, dot-product preservation). -/

noncomputable def rotFnFun {n : ℕ} (i j : Fin n) (c s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun k => if k = i then c * x i - s * x j
           else if k = j then s * x i + c * x j
           else x k

noncomputable def rotFnInvFun {n : ℕ} (i j : Fin n) (c s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun k => if k = i then c * x i + s * x j
           else if k = j then -s * x i + c * x j
           else x k

lemma rotFnFun_i {n : ℕ} (i j : Fin n) (c s : ℝ) (x : Fin n → ℝ) :
    rotFnFun i j c s x i = c * x i - s * x j := by simp [rotFnFun]

lemma rotFnFun_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (x : Fin n → ℝ) :
    rotFnFun i j c s x j = s * x i + c * x j := by simp [rotFnFun, hij.symm]

lemma rotFnFun_o {n : ℕ} (i j : Fin n) (c s : ℝ) (x : Fin n → ℝ) (k : Fin n)
    (h1 : k ≠ i) (h2 : k ≠ j) : rotFnFun i j c s x k = x k := by simp [rotFnFun, h1, h2]

lemma rotFnInvFun_i {n : ℕ} (i j : Fin n) (c s : ℝ) (x : Fin n → ℝ) :
    rotFnInvFun i j c s x i = c * x i + s * x j := by simp [rotFnInvFun]

lemma rotFnInvFun_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (x : Fin n → ℝ) :
    rotFnInvFun i j c s x j = -s * x i + c * x j := by simp [rotFnInvFun, hij.symm]

lemma rotFnInvFun_o {n : ℕ} (i j : Fin n) (c s : ℝ) (x : Fin n → ℝ) (k : Fin n)
    (h1 : k ≠ i) (h2 : k ≠ j) : rotFnInvFun i j c s x k = x k := by simp [rotFnInvFun, h1, h2]

lemma rotFn_inv_left {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : Fin n → ℝ) :
    rotFnInvFun i j c s (rotFnFun i j c s x) = x := by
  funext k
  by_cases h1 : k = i
  · have h2 : k ≠ j := fun hk => hij (h1.symm.trans hk)
    rw [h1, rotFnInvFun_i, rotFnFun_i, rotFnFun_j i j hij]
    ring_nf
    linear_combination hcs * x i
  · by_cases h3 : k = j
    · have h2 : k ≠ i := fun hk => hij (hk.symm.trans h3)
      rw [h3, rotFnInvFun_j i j hij, rotFnFun_i, rotFnFun_j i j hij]
      ring_nf
      linear_combination hcs * x j
    · rw [rotFnInvFun_o i j c s (rotFnFun i j c s x) k h1 h3, rotFnFun_o i j c s x k h1 h3]

lemma rotFn_inv_right {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : Fin n → ℝ) :
    rotFnFun i j c s (rotFnInvFun i j c s x) = x := by
  funext k
  by_cases h1 : k = i
  · have h2 : k ≠ j := fun hk => hij (h1.symm.trans hk)
    rw [h1, rotFnFun_i, rotFnInvFun_i, rotFnInvFun_j i j hij]
    ring_nf
    linear_combination hcs * x i
  · by_cases h3 : k = j
    · have h2 : k ≠ i := fun hk => hij (hk.symm.trans h3)
      rw [h3, rotFnFun_j i j hij, rotFnInvFun_i, rotFnInvFun_j i j hij]
      ring_nf
      linear_combination hcs * x j
    · rw [rotFnFun_o i j c s (rotFnInvFun i j c s x) k h1 h3, rotFnInvFun_o i j c s x k h1 h3]

lemma rotFnFun_add {n : ℕ} (i j : Fin n) (c s : ℝ) (x y : Fin n → ℝ) :
    rotFnFun i j c s (x + y) = rotFnFun i j c s x + rotFnFun i j c s y := by
  funext k
  by_cases h1 : k = i
  · simp [rotFnFun, h1]; ring_nf
  · by_cases h3 : k = j
    · have hji : ¬ j = i := fun hji => h1 (h3.trans hji)
      simp [rotFnFun, h1, h3, hji]; ring_nf
    · simp [rotFnFun, h1, h3]

lemma rotFnFun_smul {n : ℕ} (i j : Fin n) (c s : ℝ) (a : ℝ) (x : Fin n → ℝ) :
    rotFnFun i j c s (a • x) = a • rotFnFun i j c s x := by
  funext k
  by_cases h1 : k = i
  · simp [rotFnFun, h1, mul_add, mul_sub]; ring_nf
  · by_cases h3 : k = j
    · have hji : ¬ j = i := fun hji => h1 (h3.trans hji)
      simp [rotFnFun, h1, h3, hji, mul_add]; ring_nf
    · simp [rotFnFun, h1, h3]

/-- The rotation on functions, a linear equivalence. -/
noncomputable def rotFn {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := rotFnFun i j c s
  invFun := rotFnInvFun i j c s
  left_inv := rotFn_inv_left i j hij c s hcs
  right_inv := rotFn_inv_right i j hij c s hcs
  map_add' := rotFnFun_add i j c s
  map_smul' := rotFnFun_smul i j c s

lemma sum_univ_erase2 (n : ℕ) (i j : Fin n) (hij : i ≠ j) (f : Fin n → ℝ) :
    Finset.sum (Finset.univ : Finset (Fin n)) f =
      Finset.sum (((Finset.univ : Finset (Fin n)).erase i).erase j) f + f i + f j := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hij.symm]
  have h1 : Finset.sum (Finset.univ : Finset (Fin n)) f =
      Finset.sum ((Finset.univ : Finset (Fin n)).erase i) f + f i := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f hi]
  have h2 : Finset.sum ((Finset.univ : Finset (Fin n)).erase i) f =
      Finset.sum (((Finset.univ : Finset (Fin n)).erase i).erase j) f + f j := by
    rw [← Finset.sum_erase_add ((Finset.univ : Finset (Fin n)).erase i) f hj]
  calc
    Finset.sum (Finset.univ : Finset (Fin n)) f
        = Finset.sum ((Finset.univ : Finset (Fin n)).erase i) f + f i := h1
    _ = (Finset.sum (((Finset.univ : Finset (Fin n)).erase i).erase j) f + f j) + f i := by
      rw [h2]
    _ = Finset.sum (((Finset.univ : Finset (Fin n)).erase i).erase j) f + f i + f j := by
      ac_rfl

/-- rotation preserves dot products (function level) -/
lemma rotFn_dot_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (x y : Fin n → ℝ) :
    (∑ k : Fin n, rotFnFun i j c s x k * rotFnFun i j c s y k) = ∑ k : Fin n, x k * y k := by
  classical
  let A := fun k : Fin n => rotFnFun i j c s x k * rotFnFun i j c s y k
  let B := fun k : Fin n => x k * y k
  let S : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hsum : Finset.sum S A = Finset.sum S B := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_erase] at hk
    rcases hk with ⟨hkj, hki'⟩
    rw [Finset.mem_erase] at hki'
    rcases hki' with ⟨hki, _⟩
    simp [A, B, rotFnFun_o i j c s x k hki hkj, rotFnFun_o i j c s y k hki hkj]
  have hiB : A i + A j = B i + B j := by
    simp [A, B, rotFnFun_i, rotFnFun_j i j hij]
    ring_nf
    linear_combination hcs * (x i * y i + x j * y j)
  calc
    (∑ k : Fin n, A k) = Finset.sum (Finset.univ : Finset (Fin n)) A := rfl
    _ = Finset.sum S A + A i + A j := by rw [← sum_univ_erase2 n i j hij A]
    _ = Finset.sum S B + B i + B j := by
      rw [hsum]
      calc
        Finset.sum S B + A i + A j = Finset.sum S B + (A i + A j) := by ac_rfl
        _ = Finset.sum S B + (B i + B j) := by rw [hiB]
        _ = Finset.sum S B + B i + B j := by ac_rfl
    _ = (∑ k : Fin n, B k) := by rw [sum_univ_erase2 n i j hij B]



/-! ## Euclidean-space level: the two generator families -/


abbrev EVID (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- inner product of real components -/
lemma real_inner_mul (a b : ℝ) : inner ℝ a b = b * a := by
  rw [RCLike.inner_apply]
  simp

/-- the canonical linear equivalence from `EVID n` to its underlying function type -/
noncomputable def funEquiv (n : ℕ) : EVID n ≃ₗ[ℝ] (Fin n → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin n → ℝ)

/-- lift a function-level linear equivalence to `EVID n` -/
noncomputable def lift {n : ℕ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) : EVID n ≃ₗ[ℝ] EVID n :=
  (funEquiv n).trans (L.trans (funEquiv n).symm)

lemma lift_apply {n : ℕ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (x : EVID n) (k : Fin n) :
    (lift L x) k = L x.ofLp k := by
  simp [lift, funEquiv, WithLp.linearEquiv]

/-- The plane rotation in coordinates `i j`, as a linear isometry of `EVID n`. -/
noncomputable def rotLIE {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) : EVID n ≃ₗᵢ[ℝ] EVID n := by
  let L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := rotFn i j hij c s hcs
  let f : EVID n ≃ₗ[ℝ] EVID n := lift L
  refine f.isometryOfInner ?_
  intro x y
  have hx : ∀ k : Fin n, (f x) k = L x.ofLp k := by
    intro k; simp [f, lift, funEquiv, WithLp.linearEquiv]
  have hy : ∀ k : Fin n, (f y) k = L y.ofLp k := by
    intro k; simp [f, lift, funEquiv, WithLp.linearEquiv]
  calc
    inner ℝ (f x) (f y) = ∑ k : Fin n, (f y) k * (f x) k := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro k hk
      exact real_inner_mul ((f x) k) ((f y) k)
    _ = ∑ k : Fin n, (L y.ofLp) k * (L x.ofLp) k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hy k, hx k]
    _ = ∑ k : Fin n, y.ofLp k * x.ofLp k := by
      simpa [L, rotFn] using (rotFn_dot_eq i j hij c s hcs y.ofLp x.ofLp)
    _ = inner ℝ x y := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro k hk
      exact real_inner_mul (x.ofLp k) (y.ofLp k)

lemma rotLIE_apply_i {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : EVID n) :
    (rotLIE i j hij c s hcs x) i = c * x i - s * x j := by
  simp [rotLIE, lift_apply, rotFn, rotFnFun_i]

lemma rotLIE_apply_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : EVID n) :
    (rotLIE i j hij c s hcs x) j = s * x i + c * x j := by
  simp [rotLIE, lift_apply, rotFn, rotFnFun_j i j hij]

lemma rotLIE_apply_other {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : EVID n) (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    (rotLIE i j hij c s hcs x) k = x k := by
  simp [rotLIE, lift_apply, rotFn, rotFnFun_o i j c s x.ofLp k hki hkj]

/-- flip function-level -/
noncomputable def flipFnFun {n : ℕ} (k : Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => if j = k then - x k else x j

lemma flipFnFun_self {n : ℕ} (k : Fin n) (x : Fin n → ℝ) :
    flipFnFun k x k = - x k := by simp [flipFnFun]
lemma flipFnFun_other {n : ℕ} (k : Fin n) (x : Fin n → ℝ) (j : Fin n) (hjk : j ≠ k) :
    flipFnFun k x j = x j := by simp [flipFnFun, hjk]

lemma flipFnFun_idem {n : ℕ} (k : Fin n) (x : Fin n → ℝ) :
    flipFnFun k (flipFnFun k x) = x := by
  funext j
  by_cases hjk : j = k
  · subst j; simp [flipFnFun]
  · simp [flipFnFun, hjk]

lemma flipFnFun_add {n : ℕ} (k : Fin n) (x y : Fin n → ℝ) :
    flipFnFun k (x + y) = flipFnFun k x + flipFnFun k y := by
  funext j
  by_cases hjk : j = k
  · subst j; simp [flipFnFun]; ring
  · simp [flipFnFun, hjk]

lemma flipFnFun_smul {n : ℕ} (k : Fin n) (a : ℝ) (x : Fin n → ℝ) :
    flipFnFun k (a • x) = a • flipFnFun k x := by
  funext j
  by_cases hjk : j = k
  · subst j; simp [flipFnFun]
  · simp [flipFnFun, hjk]

noncomputable def flipFn {n : ℕ} (k : Fin n) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := flipFnFun k
  invFun := flipFnFun k
  left_inv := flipFnFun_idem k
  right_inv := flipFnFun_idem k
  map_add' := flipFnFun_add k
  map_smul' := flipFnFun_smul k

/-- The reflection in the coordinate hyperplane `x_k = 0`. -/
noncomputable def flipLIE {n : ℕ} (k : Fin n) : EVID n ≃ₗᵢ[ℝ] EVID n := by
  let L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := flipFn k
  let f : EVID n ≃ₗ[ℝ] EVID n := lift L
  refine f.isometryOfInner ?_
  intro x y
  have hx : ∀ j : Fin n, (f x) j = L x.ofLp j := by
    intro j; simp [f, lift, funEquiv, WithLp.linearEquiv]
  have hy : ∀ j : Fin n, (f y) j = L y.ofLp j := by
    intro j; simp [f, lift, funEquiv, WithLp.linearEquiv]
  calc
    inner ℝ (f x) (f y) = ∑ j : Fin n, (f y) j * (f x) j := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j hj
      exact real_inner_mul ((f x) j) ((f y) j)
    _ = ∑ j : Fin n, y.ofLp j * x.ofLp j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hy j, hx j]
      by_cases hjk : j = k
      · subst j
        simp [L, flipFn, flipFnFun_self]
      · simp [hjk, L, flipFn, flipFnFun_other]
    _ = inner ℝ x y := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j hj
      exact real_inner_mul (x.ofLp j) (y.ofLp j)

lemma flipLIE_apply_self {n : ℕ} (k : Fin n) (x : EVID n) :
    (flipLIE k x) k = - x k := by
  simp [flipLIE, lift_apply, flipFn, flipFnFun_self]

lemma flipLIE_apply_other {n : ℕ} (k : Fin n) (x : EVID n) (j : Fin n) (hjk : j ≠ k) :
    (flipLIE k x) j = x j := by
  simp [flipLIE, lift_apply, flipFn, flipFnFun_other k x j hjk]

/-- quarter turn in the plane `(i,j)` -/
noncomputable def quarterLIE {n : ℕ} (i j : Fin n) (hij : i ≠ j) : EVID n ≃ₗᵢ[ℝ] EVID n :=
  rotLIE i j hij 0 1 (by norm_num)

lemma quarterLIE_apply_i {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) :
    (quarterLIE i j hij x) i = - x j := by
  simpa [quarterLIE] using rotLIE_apply_i i j hij 0 1 (by norm_num) x

lemma quarterLIE_apply_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) :
    (quarterLIE i j hij x) j = x i := by
  simpa [quarterLIE] using rotLIE_apply_j i j hij 0 1 (by norm_num) x

lemma quarterLIE_apply_other {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (quarterLIE i j hij x) k = x k := by
  simpa [quarterLIE] using rotLIE_apply_other i j hij 0 1 (by norm_num) x k hki hkj









/-! ## Word machinery for lists of isometries -/

/-- the product (in application order) of a list of isometries -/
noncomputable def wordVal {n : ℕ} (l : List (EVID n ≃ₗᵢ[ℝ] EVID n)) : EVID n ≃ₗᵢ[ℝ] EVID n :=
  l.foldl (fun acc e => acc.trans e) (LinearIsometryEquiv.refl ℝ (EVID n))

lemma wordVal_nil {n : ℕ} : wordVal ([] : List (EVID n ≃ₗᵢ[ℝ] EVID n)) =
    LinearIsometryEquiv.refl ℝ (EVID n) := by
  simp [wordVal]

lemma foldl_trans_refl {n : ℕ} (A : EVID n ≃ₗᵢ[ℝ] EVID n) :
    ∀ (l : List (EVID n ≃ₗᵢ[ℝ] EVID n)),
      l.foldl (fun acc e => acc.trans e) A = A.trans (wordVal l) := by
  intro l
  induction l generalizing A with
  | nil => simp [wordVal]
  | cons a l ih =>
      simp [List.foldl, wordVal]
      calc
        l.foldl (fun acc e => acc.trans e) (A.trans a)
            = (A.trans a).trans (wordVal l) := ih (A.trans a)
        _ = A.trans (a.trans (wordVal l)) := by rw [LinearIsometryEquiv.trans_assoc]
        _ = A.trans (List.foldl (fun acc e => acc.trans e) a l) := by rw [← ih a]

lemma wordVal_append {n : ℕ} (l1 l2 : List (EVID n ≃ₗᵢ[ℝ] EVID n)) :
    wordVal (l1 ++ l2) = (wordVal l1).trans (wordVal l2) := by
  rw [wordVal, List.foldl_append]
  exact foldl_trans_refl (wordVal l1) l2

lemma wordVal_single {n : ℕ} (e : EVID n ≃ₗᵢ[ℝ] EVID n) : wordVal [e] = e := by
  simp [wordVal]

lemma wordVal_cons {n : ℕ} (e : EVID n ≃ₗᵢ[ℝ] EVID n) (l : List (EVID n ≃ₗᵢ[ℝ] EVID n)) :
    wordVal (e :: l) = e.trans (wordVal l) := by
  calc
    wordVal (e :: l) = wordVal ([e] ++ l) := by simp
    _ = (wordVal [e]).trans (wordVal l) := wordVal_append [e] l
    _ = e.trans (wordVal l) := by rw [wordVal_single]

/-- the inverse of a word is the reversed word of inverses -/
lemma wordVal_reverse_symm {n : ℕ} (l : List (EVID n ≃ₗᵢ[ℝ] EVID n)) :
    wordVal ((l.map (fun e => e.symm)).reverse) = (wordVal l).symm := by
  induction l with
  | nil =>
      apply LinearIsometryEquiv.ext
      intro x
      simp [wordVal]
      exact (LinearIsometryEquiv.apply_symm_apply (LinearIsometryEquiv.refl ℝ (EVID n)) x)
  | cons a l ih =>
      simp only [List.map_cons, List.reverse_cons]
      rw [wordVal_append, wordVal_single, ih]
      rw [wordVal_cons]
      rw [LinearIsometryEquiv.symm_trans]

/-- mapping a word by a word-producing function preserves products -/
abbrev Iso (n : ℕ) := EVID n ≃ₗᵢ[ℝ] EVID n

lemma wordVal_flatMap {n : ℕ} (l : List (Iso n))
    (f : Iso n → List (Iso n))
    (h : ∀ e ∈ l, wordVal (f e) = e) :
    wordVal (List.flatMap f l) = wordVal l := by
  induction l with
  | nil => simp [wordVal]
  | cons a l ih =>
      rw [List.flatMap_cons]
      rw [wordVal_append]
      rw [h a (by simp)]
      have hl : ∀ e ∈ l, wordVal (f e) = e := fun e he => h e (by simp [he])
      rw [ih hl]
      rw [← wordVal_cons]

/-! ## Allowed generators -/

/-- maps of the two allowed forms appearing in the decomposition -/
def Allowed {n : ℕ} (e : EVID n ≃ₗᵢ[ℝ] EVID n) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧ ∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧ c ^ 2 + s ^ 2 = 1 ∧
    ∀ x : EVID n, e x i = c * x i - s * x j ∧ e x j = s * x i + c * x j ∧
      ∀ k : Fin n, k ≠ i → k ≠ j → e x k = x k)
  ∨ (∃ k : Fin n, ∀ x : EVID n, e x k = - x k ∧ ∀ j : Fin n, j ≠ k → e x j = x j)

lemma allowed_rotLIE {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    Allowed (rotLIE i j hij c s hcs) := by
  left
  refine ⟨i, j, hij, c, s, hc, hs, hcs, ?_⟩
  intro x
  exact ⟨rotLIE_apply_i i j hij c s hcs x, rotLIE_apply_j i j hij c s hcs x,
    fun k hki hkj => rotLIE_apply_other i j hij c s hcs x k hki hkj⟩

lemma allowed_flipLIE {n : ℕ} (k : Fin n) : Allowed (flipLIE k) := by
  right
  refine ⟨k, ?_⟩
  intro x
  exact ⟨flipLIE_apply_self k x, fun j hjk => flipLIE_apply_other k x j hjk⟩

lemma allowed_quarterLIE {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Allowed (quarterLIE i j hij) := by
  simpa [quarterLIE] using
    (allowed_rotLIE i j hij 0 1 (by norm_num) (by norm_num) (by norm_num))

/-- a list all of whose members are allowed -/
def AllowedWord {n : ℕ} (l : List (EVID n ≃ₗᵢ[ℝ] EVID n)) : Prop := ∀ e ∈ l, Allowed e

lemma allowed_append {n : ℕ} {l1 l2 : List (EVID n ≃ₗᵢ[ℝ] EVID n)} :
    AllowedWord l1 → AllowedWord l2 → AllowedWord (l1 ++ l2) := by
  intro h1 h2 e he
  rw [List.mem_append] at he
  rcases he with he | he
  · exact h1 e he
  · exact h2 e he

lemma allowed_cons {n : ℕ} {a : EVID n ≃ₗᵢ[ℝ] EVID n} {l : List (EVID n ≃ₗᵢ[ℝ] EVID n)} :
    Allowed a → AllowedWord l → AllowedWord (a :: l) := by
  intro ha h e he
  rw [List.mem_cons] at he
  rcases he with rfl | he
  · exact ha
  · exact h e he

lemma allowed_flatMap {n : ℕ} (l : List (Iso n))
    (f : Iso n → List (Iso n))
    (hf : ∀ e ∈ l, AllowedWord (f e)) : AllowedWord (List.flatMap f l) := by
  intro e he
  rw [List.mem_flatMap] at he
  rcases he with ⟨e', he', hee⟩
  exact hf e' he' e hee

lemma AllowedWord_nil {n : ℕ} : AllowedWord ([] : List (EVID n ≃ₗᵢ[ℝ] EVID n)) := by
  intro e he
  simp at he


/-! ## Symm of rotations, and powers of the quarter turn -/

lemma rotFnInvFun_eq_rotFnFun {n : ℕ} (i j : Fin n) (c s : ℝ) :
    rotFnInvFun i j c s = rotFnFun i j c (-s) := by
  funext x
  funext k
  by_cases hki : k = i
  · subst k; simp [rotFnFun, rotFnInvFun]
  · by_cases hkj : k = j
    · subst k; simp [rotFnFun, rotFnInvFun, hki]
    · simp [rotFnFun, rotFnInvFun, hki, hkj]

lemma lift_symm_apply {n : ℕ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (x : EVID n) (k : Fin n) :
    (lift L).symm x k = L.symm x.ofLp k := by
  simp [lift, funEquiv, WithLp.linearEquiv]

lemma rotFn_symm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotFn i j hij c s hcs).symm = rotFn i j hij c (-s) (by nlinarith [hcs]) := by
  apply LinearEquiv.ext
  intro x
  simp [rotFn, rotFnInvFun_eq_rotFnFun]

lemma lift_symm {n : ℕ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    (lift L).symm = lift L.symm := by
  apply LinearEquiv.ext
  intro x
  apply PiLp.ext
  intro k
  simp [lift, funEquiv, WithLp.linearEquiv]

lemma rotLIE_symm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotLIE i j hij c s hcs).symm = rotLIE i j hij c (-s) (by nlinarith [hcs]) := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  simp [rotLIE, rotFn_symm, lift_symm]

/-- the square of the quarter turn in plane `(i,j)` -/
noncomputable def quarter2 {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Iso n :=
  (quarterLIE i j hij).trans (quarterLIE i j hij)

/-- the cube of the quarter turn in plane `(i,j)` -/
noncomputable def quarter3 {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Iso n :=
  (quarterLIE i j hij).trans (quarter2 i j hij)

lemma quarter2_apply_i {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) :
    (quarter2 i j hij x) i = - x i := by
  dsimp [quarter2]
  rw [quarterLIE_apply_i i j hij (quarterLIE i j hij x)]
  rw [quarterLIE_apply_j i j hij x]

lemma quarter2_apply_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) :
    (quarter2 i j hij x) j = - x j := by
  dsimp [quarter2]
  rw [quarterLIE_apply_j i j hij (quarterLIE i j hij x)]
  rw [quarterLIE_apply_i i j hij x]

lemma quarter2_apply_other {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) : (quarter2 i j hij x) k = x k := by
  dsimp [quarter2]
  rw [quarterLIE_apply_other i j hij (quarterLIE i j hij x) k hki hkj]
  rw [quarterLIE_apply_other i j hij x k hki hkj]

lemma quarter3_apply_i {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) :
    (quarter3 i j hij x) i = x j := by
  dsimp [quarter3]
  rw [quarter2_apply_i i j hij (quarterLIE i j hij x)]
  rw [quarterLIE_apply_i i j hij x]
  ring

lemma quarter3_apply_j {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) :
    (quarter3 i j hij x) j = - x i := by
  dsimp [quarter3]
  rw [quarter2_apply_j i j hij (quarterLIE i j hij x)]
  rw [quarterLIE_apply_j i j hij x]

lemma quarter3_apply_other {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : EVID n) (k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) : (quarter3 i j hij x) k = x k := by
  dsimp [quarter3]
  rw [quarter2_apply_other i j hij (quarterLIE i j hij x) k hki hkj]
  rw [quarterLIE_apply_other i j hij x k hki hkj]


/-! ## Lemma A: a plane rotation decomposes into allowed maps -/

lemma rotLIE_q1 {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rotLIE i j hij c s hcs =
      (rotLIE i j hij s (-c) (by nlinarith [hcs])).trans (quarterLIE i j hij) := by
  ext x k
  by_cases hki : k = i
  · subst k
    rw [LinearIsometryEquiv.trans_apply]
    rw [rotLIE_apply_i i j hij c s hcs x]
    rw [quarterLIE_apply_i i j hij (rotLIE i j hij s (-c) (by nlinarith [hcs]) x)]
    rw [rotLIE_apply_j i j hij s (-c) (by nlinarith [hcs]) x]
    ring
  · by_cases hkj : k = j
    · subst k
      rw [LinearIsometryEquiv.trans_apply]
      rw [rotLIE_apply_j i j hij c s hcs x]
      rw [quarterLIE_apply_j i j hij (rotLIE i j hij s (-c) (by nlinarith [hcs]) x)]
      rw [rotLIE_apply_i i j hij s (-c) (by nlinarith [hcs]) x]
      ring
    · rw [LinearIsometryEquiv.trans_apply]
      rw [quarterLIE_apply_other i j hij (rotLIE i j hij s (-c) (by nlinarith [hcs]) x) k hki hkj]
      rw [rotLIE_apply_other i j hij s (-c) (by nlinarith [hcs]) x k hki hkj]
      rw [rotLIE_apply_other i j hij c s hcs x k hki hkj]

lemma rotLIE_q2 {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rotLIE i j hij c s hcs =
      (rotLIE i j hij (-c) (-s) (by nlinarith [hcs])).trans (quarter2 i j hij) := by
  ext x k
  by_cases hki : k = i
  · subst k
    rw [LinearIsometryEquiv.trans_apply]
    rw [rotLIE_apply_i i j hij c s hcs x]
    rw [quarter2_apply_i i j hij (rotLIE i j hij (-c) (-s) (by nlinarith [hcs]) x)]
    rw [rotLIE_apply_i i j hij (-c) (-s) (by nlinarith [hcs]) x]
    ring
  · by_cases hkj : k = j
    · subst k
      rw [LinearIsometryEquiv.trans_apply]
      rw [rotLIE_apply_j i j hij c s hcs x]
      rw [quarter2_apply_j i j hij (rotLIE i j hij (-c) (-s) (by nlinarith [hcs]) x)]
      rw [rotLIE_apply_j i j hij (-c) (-s) (by nlinarith [hcs]) x]
      ring
    · rw [LinearIsometryEquiv.trans_apply]
      rw [quarter2_apply_other i j hij (rotLIE i j hij (-c) (-s) (by nlinarith [hcs]) x) k hki hkj]
      rw [rotLIE_apply_other i j hij (-c) (-s) (by nlinarith [hcs]) x k hki hkj]
      rw [rotLIE_apply_other i j hij c s hcs x k hki hkj]

lemma rotLIE_q3 {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rotLIE i j hij c s hcs =
      (rotLIE i j hij (-s) c (by nlinarith [hcs])).trans (quarter3 i j hij) := by
  ext x k
  by_cases hki : k = i
  · subst k
    rw [LinearIsometryEquiv.trans_apply]
    rw [rotLIE_apply_i i j hij c s hcs x]
    rw [quarter3_apply_i i j hij (rotLIE i j hij (-s) c (by nlinarith [hcs]) x)]
    rw [rotLIE_apply_j i j hij (-s) c (by nlinarith [hcs]) x]
    ring
  · by_cases hkj : k = j
    · subst k
      rw [LinearIsometryEquiv.trans_apply]
      rw [rotLIE_apply_j i j hij c s hcs x]
      rw [quarter3_apply_j i j hij (rotLIE i j hij (-s) c (by nlinarith [hcs]) x)]
      rw [rotLIE_apply_i i j hij (-s) c (by nlinarith [hcs]) x]
      ring
    · rw [LinearIsometryEquiv.trans_apply]
      rw [quarter3_apply_other i j hij (rotLIE i j hij (-s) c (by nlinarith [hcs]) x) k hki hkj]
      rw [rotLIE_apply_other i j hij (-s) c (by nlinarith [hcs]) x k hki hkj]
      rw [rotLIE_apply_other i j hij c s hcs x k hki hkj]

lemma rotLIE_word {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ l : List (Iso n), AllowedWord l ∧ wordVal l = rotLIE i j hij c s hcs := by
  classical
  by_cases hc : 0 ≤ c
  · by_cases hs : 0 ≤ s
    · refine ⟨[rotLIE i j hij c s hcs], ?_, ?_⟩
      · exact allowed_cons (allowed_rotLIE i j hij c s hc hs hcs) AllowedWord_nil
      · exact wordVal_single (rotLIE i j hij c s hcs)
    · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hs))
      refine ⟨[rotLIE i j hij (-s) c (by nlinarith [hcs]), quarterLIE i j hij,
        quarterLIE i j hij, quarterLIE i j hij], ?_, ?_⟩
      · apply allowed_cons
        · exact allowed_rotLIE i j hij (-s) c hs' hc (by nlinarith [hcs])
        · apply allowed_cons
          · exact allowed_quarterLIE i j hij
          · apply allowed_cons
            · exact allowed_quarterLIE i j hij
            · exact allowed_cons (allowed_quarterLIE i j hij) AllowedWord_nil
      · rw [rotLIE_q3 i j hij c s hcs]
        simp [wordVal_cons, wordVal_single, wordVal_nil, quarter2, quarter3]
  · have hc' : 0 ≤ -c := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hc))
    by_cases hs : 0 ≤ s
    · refine ⟨[rotLIE i j hij s (-c) (by nlinarith [hcs]), quarterLIE i j hij], ?_, ?_⟩
      · apply allowed_cons
        · exact allowed_rotLIE i j hij s (-c) hs hc' (by nlinarith [hcs])
        · exact allowed_cons (allowed_quarterLIE i j hij) AllowedWord_nil
      · rw [rotLIE_q1 i j hij c s hcs]
        simp [wordVal_cons, wordVal_single, wordVal_nil]
    · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_lt (lt_of_not_ge hs))
      refine ⟨[rotLIE i j hij (-c) (-s) (by nlinarith [hcs]), quarterLIE i j hij,
        quarterLIE i j hij], ?_, ?_⟩
      · apply allowed_cons
        · exact allowed_rotLIE i j hij (-c) (-s) hc' hs' (by nlinarith [hcs])
        · apply allowed_cons
          · exact allowed_quarterLIE i j hij
          · exact allowed_cons (allowed_quarterLIE i j hij) AllowedWord_nil
      · rw [rotLIE_q2 i j hij c s hcs]
        simp [wordVal_cons, wordVal_single, wordVal_nil, quarter2, quarter3]




/-! ## EVID-level transitivity: mapping `e₀` by plane rotations -/

/-- the first standard basis vector as a function -/
noncomputable def eFn (m : ℕ) : Fin (m + 1) → ℝ :=
  fun j => if j = (0 : Fin (m + 1)) then 1 else 0

/-- the first standard basis vector of `EVID (m+1)` -/
noncomputable def e0Elem (m : ℕ) : EVID (m + 1) :=
  WithLp.toLp 2 (eFn m)

lemma e0Elem_apply (m : ℕ) (j : Fin (m + 1)) : (e0Elem m) j = eFn m j := by
  simp [e0Elem, eFn]

lemma e0Elem_apply_zero (m : ℕ) : (e0Elem m) (0 : Fin (m + 1)) = 1 := by
  simp [e0Elem_apply, eFn]

lemma e0Elem_apply_other (m : ℕ) (j : Fin (m + 1)) (hj : j ≠ (0 : Fin (m + 1))) :
    (e0Elem m) j = 0 := by
  simp [e0Elem_apply, eFn, hj]

/-- norm squared of an element of `EVID (m+1)` in terms of coordinates -/
lemma norm_sq_sum (m : ℕ) (x : EVID (m + 1)) :
    ‖x‖ ^ 2 = ∑ i : Fin (m + 1), (x i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i hi
  simp

lemma sum_sq_eFn (m : ℕ) : (∑ i : Fin (m + 1), (eFn m i) ^ 2) = 1 := by
  simp [eFn]

lemma norm_e0Elem (m : ℕ) : ‖e0Elem m‖ = 1 := by
  have hsq : ‖e0Elem m‖ ^ 2 = 1 := by
    rw [norm_sq_sum]
    simpa [e0Elem] using (sum_sq_eFn m)
  have hnon : 0 ≤ ‖e0Elem m‖ := norm_nonneg _
  nlinarith

/-- a plane-rotation datum at the `EVID`-level (plane through coordinates `0` and `j`) -/
structure PlaneDatum (m : ℕ) where
  j : Fin (m + 1)
  hjnz : j ≠ (0 : Fin (m + 1))
  c : ℝ
  s : ℝ
  hcs : c ^ 2 + s ^ 2 = 1

namespace PlaneDatum

noncomputable def toLIE {m : ℕ} (d : PlaneDatum m) : Iso (m + 1) :=
  rotLIE (0 : Fin (m + 1)) d.j d.hjnz.symm d.c d.s d.hcs

/-- function-level fold of the rotation datums -/
noncomputable def fnFold (m : ℕ) (ds : List (PlaneDatum m)) (w : Fin (m + 1) → ℝ) :
    Fin (m + 1) → ℝ :=
  ds.foldl (fun acc d => rotFnFun (0 : Fin (m + 1)) d.j d.c d.s acc) w

end PlaneDatum

open PlaneDatum (fnFold)

lemma PlaneDatum.toLIE_ofLp {m : ℕ} (d : PlaneDatum m) (x : EVID (m + 1)) :
    (PlaneDatum.toLIE d x).ofLp = rotFnFun (0 : Fin (m + 1)) d.j d.c d.s x.ofLp := by
  change (rotLIE (0 : Fin (m + 1)) d.j d.hjnz.symm d.c d.s d.hcs x).ofLp =
    rotFnFun (0 : Fin (m + 1)) d.j d.c d.s x.ofLp
  funext k
  simp [PlaneDatum.toLIE, rotLIE, rotFn, lift_apply]

lemma wordVal_lift_ds {m : ℕ} (v : EVID (m + 1)) (ds : List (PlaneDatum m)) :
    (wordVal (ds.map PlaneDatum.toLIE) v).ofLp = fnFold m ds v.ofLp := by
  induction ds generalizing v with
  | nil => simp [wordVal, fnFold]
  | cons d ds ih =>
      have htrans : (d.toLIE.trans (wordVal (ds.map PlaneDatum.toLIE)) v) =
          wordVal (ds.map PlaneDatum.toLIE) (d.toLIE v) := by
        rw [LinearIsometryEquiv.trans_apply]
      rw [List.map_cons, wordVal_cons, htrans]
      rw [ih (d.toLIE v)]
      rw [PlaneDatum.toLIE_ofLp d v]
      rfl

/-- matching the pmap-built datum list with the child's word -/
lemma fnFold_of_pmap {m : ℕ} (lfn : List (Fin (m + 1) × ℝ × ℝ))
    (H : ∀ e ∈ lfn, e.1 ≠ (0 : Fin (m + 1)) ∧ e.2.1 ^ 2 + e.2.2 ^ 2 = 1)
    (w : Fin (m + 1) → ℝ) :
    fnFold m (lfn.pmap (fun e hp =>
      { j := e.1, hjnz := hp.1, c := e.2.1, s := e.2.2, hcs := hp.2 }) H) w =
    lfn.foldl (fun acc (e : Fin (m + 1) × ℝ × ℝ) =>
      rotFnFun (0 : Fin (m + 1)) e.1 e.2.1 e.2.2 acc) w := by
  revert H w
  induction lfn with
  | nil =>
      intro H w
      simp [fnFold]
  | cons a l ih =>
      intro H w
      unfold fnFold at *
      rw [List.pmap_cons]
      exact ih (fun e he => H e (List.mem_cons_of_mem a he))
        (rotFnFun (0 : Fin (m + 1)) a.1 a.2.1 a.2.2 w)

/-- every unit vector can be rotated to `e₀` by plane rotations in the planes `(0,k)` -/
theorem trans_e0 (m : ℕ) (hm : 1 ≤ m) (v : EVID (m + 1)) (hv : ‖v‖ = 1) :
    ∃ ds : List (PlaneDatum m),
      (∀ d ∈ ds, d.j ≠ (0 : Fin (m + 1))) ∧
      wordVal (ds.map PlaneDatum.toLIE) v = e0Elem m := by
  have hvsum : (∑ i : Fin (m + 1), (v i) ^ 2) = 1 := by
    have hsq : ‖v‖ ^ 2 = 1 := by nlinarith
    rw [norm_sq_sum] at hsq
    exact hsq
  classical
  obtain ⟨lfn, hvalid, hidx, hfold⟩ := givens_word_unit m hm v.ofLp hvsum
  let H : ∀ e ∈ lfn, e.1 ≠ (0 : Fin (m + 1)) ∧ e.2.1 ^ 2 + e.2.2 ^ 2 = 1 :=
    fun e he => ⟨hidx e he, hvalid e he⟩
  let ds : List (PlaneDatum m) :=
    lfn.pmap (fun e hp =>
      { j := e.1, hjnz := hp.1, c := e.2.1, s := e.2.2, hcs := hp.2 }) H
  refine ⟨ds, ?_, ?_⟩
  · intro d hd
    rw [List.mem_pmap] at hd
    rcases hd with ⟨e, he, rfl⟩
    exact (H e he).1
  · -- wordVal (ds.map toLIE) v = e0Elem m
    have hc : (wordVal (ds.map PlaneDatum.toLIE) v).ofLp = eFn m := by
      have hl : (wordVal (ds.map PlaneDatum.toLIE) v).ofLp = fnFold m ds v.ofLp := by
        exact wordVal_lift_ds v ds
      rw [hl]
      rw [fnFold_of_pmap lfn H v.ofLp]
      exact hfold
    calc
      wordVal (ds.map PlaneDatum.toLIE) v
          = WithLp.toLp 2 ((wordVal (ds.map PlaneDatum.toLIE) v).ofLp) := by
            exact (WithLp.toLp_ofLp 2 (wordVal (ds.map PlaneDatum.toLIE) v)).symm
      _ = WithLp.toLp 2 (eFn m) := by rw [hc]
      _ = e0Elem m := rfl



/-! ## Reflection decomposition -/

lemma inner_e0Elem {m : ℕ} (x : EVID (m + 1)) : inner ℝ x (e0Elem m) = x (0 : Fin (m + 1)) := by
  rw [PiLp.inner_apply]
  simp [e0Elem_apply, eFn]

lemma inner_e0Elem_comm {m : ℕ} (x : EVID (m + 1)) : inner ℝ (e0Elem m) x = x (0 : Fin (m + 1)) := by
  rw [real_inner_comm, inner_e0Elem]

/-- the flip at coordinate `0` is the reflection in the hyperplane perpendicular to `e₀` -/
lemma flip_zero_eq_reflection {m : ℕ} :
    flipLIE (0 : Fin (m + 1)) = (ℝ ∙ (e0Elem m))ᗮ.reflection := by
  apply LinearIsometryEquiv.ext
  intro x
  apply PiLp.ext
  intro k
  by_cases hk : k = (0 : Fin (m + 1))
  · subst k
    rw [flipLIE_apply_self (0 : Fin (m + 1)) x]
    rw [Submodule.reflection_orthogonal_apply (𝕜 := ℝ) (K := ℝ ∙ (e0Elem m)) x]
    rw [Submodule.reflection_singleton_apply]
    simp [inner_e0Elem_comm, e0Elem_apply_zero, norm_e0Elem]
    ring
  · rw [flipLIE_apply_other (0 : Fin (m + 1)) x k hk]
    rw [Submodule.reflection_orthogonal_apply (𝕜 := ℝ) (K := ℝ ∙ (e0Elem m)) x]
    rw [Submodule.reflection_singleton_apply]
    simp [inner_e0Elem_comm, e0Elem_apply_other m k hk, hk]

/-- a rotation datum with inverted direction -/
def PlaneDatum.symm {m : ℕ} (d : PlaneDatum m) : PlaneDatum m :=
  { j := d.j, hjnz := d.hjnz, c := d.c, s := -d.s, hcs := by nlinarith [d.hcs] }

lemma PlaneDatum.toLIE_symm {m : ℕ} (d : PlaneDatum m) :
    (PlaneDatum.toLIE d).symm = PlaneDatum.toLIE (PlaneDatum.symm d) := by
  rw [PlaneDatum.toLIE, PlaneDatum.toLIE, PlaneDatum.symm]
  exact rotLIE_symm (0 : Fin (m + 1)) d.j d.hjnz.symm d.c d.s d.hcs

/-- the allowed-word decomposition of a rotation datum -/
noncomputable def PlaneDatum.allowedWord {m : ℕ} (d : PlaneDatum m) : List (Iso (m + 1)) :=
  Classical.choose (rotLIE_word (0 : Fin (m + 1)) d.j d.hjnz.symm d.c d.s d.hcs)

lemma PlaneDatum.allowedWord_spec {m : ℕ} (d : PlaneDatum m) :
    AllowedWord (PlaneDatum.allowedWord d) ∧
      wordVal (PlaneDatum.allowedWord d) = PlaneDatum.toLIE d := by
  dsimp [PlaneDatum.allowedWord, PlaneDatum.toLIE]
  exact Classical.choose_spec
    (rotLIE_word (0 : Fin (m + 1)) d.j d.hjnz.symm d.c d.s d.hcs)

lemma allowedWord_flatMap_ds {m : ℕ} (ds : List (PlaneDatum m)) :
    AllowedWord (ds.flatMap PlaneDatum.allowedWord) := by
  intro e he
  rw [List.mem_flatMap] at he
  rcases he with ⟨d, hd, hee⟩
  exact (PlaneDatum.allowedWord_spec d).1 e hee

lemma wordVal_flatMap_ds {m : ℕ} (ds : List (PlaneDatum m)) :
    wordVal (ds.flatMap PlaneDatum.allowedWord) = wordVal (ds.map PlaneDatum.toLIE) := by
  induction ds with
  | nil => simp [wordVal]
  | cons d ds ih =>
      calc
        wordVal (PlaneDatum.allowedWord d ++ (ds.flatMap PlaneDatum.allowedWord))
            = (wordVal (PlaneDatum.allowedWord d)).trans (wordVal (ds.flatMap PlaneDatum.allowedWord)) :=
              wordVal_append (PlaneDatum.allowedWord d) (ds.flatMap PlaneDatum.allowedWord)
        _ = (PlaneDatum.toLIE d).trans (wordVal (ds.map PlaneDatum.toLIE)) := by
              rw [(PlaneDatum.allowedWord_spec d).2, ih]
        _ = wordVal (PlaneDatum.toLIE d :: ds.map PlaneDatum.toLIE) :=
              (wordVal_cons (PlaneDatum.toLIE d) (ds.map PlaneDatum.toLIE)).symm
        _ = wordVal ((d :: ds).map PlaneDatum.toLIE) := rfl

/-- the allowed word realizing the reflection in the hyperplane perpendicular to `u`. -/
noncomputable def reflWord {m : ℕ} (ds : List (PlaneDatum m)) : List (Iso (m + 1)) :=
  (ds.flatMap PlaneDatum.allowedWord ++ [flipLIE (0 : Fin (m + 1))]) ++
    ((ds.map PlaneDatum.symm).reverse).flatMap PlaneDatum.allowedWord

lemma reflWord_allowed {m : ℕ} (ds : List (PlaneDatum m)) : AllowedWord (reflWord ds) := by
  dsimp [reflWord]
  apply allowed_append
  · apply allowed_append
    · exact allowedWord_flatMap_ds ds
    · exact allowed_cons (allowed_flipLIE (0 : Fin (m + 1))) AllowedWord_nil
  · exact allowedWord_flatMap_ds ((ds.map PlaneDatum.symm).reverse)


lemma reflWord_wordVal {m : ℕ} (ds : List (PlaneDatum m)) :
    wordVal (reflWord ds) =
      ((wordVal (ds.map PlaneDatum.toLIE)).trans (flipLIE (0 : Fin (m + 1)))).trans
        (wordVal (ds.map PlaneDatum.toLIE)).symm := by
  dsimp [reflWord]
  rw [wordVal_append, wordVal_append]
  rw [wordVal_single]
  congr 1
  · rw [wordVal_flatMap_ds ds]
  · calc
      wordVal (((ds.map PlaneDatum.symm).reverse).flatMap PlaneDatum.allowedWord)
          = wordVal (((ds.map PlaneDatum.symm).reverse).map PlaneDatum.toLIE) :=
            wordVal_flatMap_ds ((ds.map PlaneDatum.symm).reverse)
      _ = wordVal (((ds.map PlaneDatum.toLIE).map (fun e => e.symm)).reverse) := by
            congr 1
            rw [List.map_reverse, List.map_map]
            -- LHS: (ds.map (toLIE∘symm)).reverse, RHS inside: reverse: (ds.map (fun d => (toLIE d).symm)).reverse
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro d hd
            exact (PlaneDatum.toLIE_symm d).symm
      _ = (wordVal (ds.map PlaneDatum.toLIE)).symm := wordVal_reverse_symm (ds.map PlaneDatum.toLIE)

/-- reflection in `(ℝ ∙ u)ᗮ` equals the word built from the transitivity word -/
theorem reflWord_eq_reflection {m : ℕ} (u : EVID (m + 1)) (hu : ‖u‖ = 1)
    (ds : List (PlaneDatum m)) (hds : wordVal (ds.map PlaneDatum.toLIE) u = e0Elem m) :
    wordVal (reflWord ds) = (ℝ ∙ u)ᗮ.reflection := by
  let G : Iso (m + 1) := wordVal (ds.map PlaneDatum.toLIE)
  have hGu : G u = e0Elem m := hds
  have hu_inv : G.symm (e0Elem m) = u := by
    rw [← hGu]
    exact G.symm_apply_apply u
  have hKflip : (flipLIE (0 : Fin (m + 1))) = (ℝ ∙ (e0Elem m))ᗮ.reflection :=
    flip_zero_eq_reflection
  have h1 : wordVal (reflWord ds) =
      ((G.trans (flipLIE (0 : Fin (m + 1)))).trans G.symm) := by
    rw [reflWord_wordVal ds]
  have h2 : ((G.trans (flipLIE (0 : Fin (m + 1)))).trans G.symm)
      = G.trans ((flipLIE (0 : Fin (m + 1))).trans G.symm) := by
    rw [LinearIsometryEquiv.trans_assoc]
  have hsp : Submodule.map (↑G.symm.toLinearEquiv : EVID (m + 1) →ₗ[ℝ] EVID (m + 1))
        (ℝ ∙ (e0Elem m)) = ℝ ∙ (G.symm (e0Elem m)) := by
    rw [Submodule.map_span, Set.image_singleton]
    congr 1
  have hmap : ((ℝ ∙ (e0Elem m))ᗮ).map (↑G.symm.toLinearEquiv : EVID (m + 1) →ₗ[ℝ] EVID (m + 1)) = (ℝ ∙ u)ᗮ := by
    calc
      ((ℝ ∙ (e0Elem m))ᗮ).map (↑G.symm.toLinearEquiv : EVID (m + 1) →ₗ[ℝ] EVID (m + 1))
          = ((ℝ ∙ (e0Elem m)).map (↑G.symm.toLinearEquiv : EVID (m + 1) →ₗ[ℝ] EVID (m + 1)))ᗮ := by
            exact (Submodule.map_orthogonal_equiv (ℝ ∙ (e0Elem m)) G.symm)
      _ = (ℝ ∙ (G.symm (e0Elem m)))ᗮ := by rw [hsp]
      _ = (ℝ ∙ u)ᗮ := by rw [hu_inv]
  have hrefl_map := Submodule.reflection_map (𝕜 := ℝ)
    (f := G.symm) ((ℝ ∙ (e0Elem m))ᗮ)
  have h3 : G.trans (((ℝ ∙ (e0Elem m))ᗮ.reflection).trans G.symm)
      = Submodule.reflection (((ℝ ∙ (e0Elem m))ᗮ).map (↑G.symm.toLinearEquiv : EVID (m + 1) →ₗ[ℝ] EVID (m + 1))) := by
    have hx := hrefl_map.symm
    rw [LinearIsometryEquiv.symm_symm] at hx
    exact hx
  calc
    wordVal (reflWord ds)
        = ((G.trans (flipLIE (0 : Fin (m + 1)))).trans G.symm) := h1
    _ = G.trans ((flipLIE (0 : Fin (m + 1))).trans G.symm) := h2
    _ = G.trans (((ℝ ∙ (e0Elem m))ᗮ.reflection).trans G.symm) := by rw [hKflip]
    _ = Submodule.reflection (((ℝ ∙ (e0Elem m))ᗮ).map (↑G.symm.toLinearEquiv : EVID (m + 1) →ₗ[ℝ] EVID (m + 1))) := h3
    _ = (ℝ ∙ u)ᗮ.reflection := by
      congr 1


/-- the allowed decomposition of the reflection in `(ℝ ∙ v)ᗮ`, `v ≠ 0`, in dimension ≥ 2 -/
theorem refl_allowed {m : ℕ} (hm : 1 ≤ m) (v : EVID (m + 1)) (hv : v ≠ 0) :
    ∃ w : List (Iso (m + 1)), AllowedWord w ∧ wordVal w = (ℝ ∙ v)ᗮ.reflection := by
  let u : EVID (m + 1) := (‖v‖⁻¹) • v
  have hne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hc0 : (‖v‖⁻¹ : ℝ) ≠ 0 := inv_ne_zero hne
  have hun : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
    exact inv_mul_cancel₀ hne
  obtain ⟨ds, hjnz, hval⟩ := trans_e0 m hm u hun
  have hspan : (ℝ ∙ u)ᗮ = (ℝ ∙ v)ᗮ := by
    apply Submodule.ext
    intro x
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    dsimp [u]
    rw [inner_smul_left]
    -- goal: (‖v‖⁻¹ * inner ℝ v x = 0) ↔ inner ℝ v x = 0
    constructor
    · intro hz
      exact (mul_eq_zero.mp hz).resolve_left hc0
    · intro hz
      rw [hz]
      simp
  refine ⟨reflWord ds, reflWord_allowed ds, ?_⟩
  calc
    wordVal (reflWord ds) = (ℝ ∙ u)ᗮ.reflection := reflWord_eq_reflection u hun ds hval
    _ = (ℝ ∙ v)ᗮ.reflection := by
      congr 1

/-- an isometry is a product of hyperplane reflections (Cartan–Dieudonné) -/
lemma isometry_reflections {n : ℕ} (ρ : Iso n) :
    ∃ lv : List (EVID n),
      ρ = (lv.map (fun v : EVID n => ((ℝ ∙ v)ᗮ.reflection : Iso n))).prod := by
  rcases (LinearIsometryEquiv.reflections_generate_dim (F := EVID n) ρ) with ⟨lv, hl, h⟩
  exact ⟨lv, h⟩

lemma LIE_one_eq_refl {n : ℕ} : (1 : Iso n) = LinearIsometryEquiv.refl ℝ (EVID n) := by
  ext x
  simp

lemma wordVal_eq_prod_rev {n : ℕ} (l : List (Iso n)) : wordVal l = l.reverse.prod := by
  induction l with
  | nil => rw [wordVal_nil, List.reverse_nil, List.prod_nil]; exact LIE_one_eq_refl.symm
  | cons a l ih =>
      calc
        wordVal (a :: l) = a.trans (wordVal l) := wordVal_cons a l
        _ = a.trans (l.reverse.prod) := by rw [ih]
        _ = (l.reverse.prod) * a := by rfl
        _ = (l.reverse ++ [a]).prod := by
              rw [List.prod_append]
              simp
        _ = (a :: l).reverse.prod := by rw [List.reverse_cons]

lemma allowed_flatMap_any {n : ℕ} {α : Type*} (l : List α) (f : α → List (Iso n))
    (hf : ∀ a ∈ l, AllowedWord (f a)) : AllowedWord (l.flatMap f) := by
  intro e he
  rw [List.mem_flatMap] at he
  rcases he with ⟨a, ha, hea⟩
  exact hf a ha e hea

lemma wordVal_flatMap_generic {n : ℕ} {α : Type*} (l : List α) (f : α → List (Iso n))
    (g : α → Iso n) (h : ∀ a ∈ l, wordVal (f a) = g a) :
    wordVal (l.flatMap f) = wordVal (l.map g) := by
  induction l with
  | nil => simp [wordVal]
  | cons a l ih =>
      calc
        wordVal (f a ++ (l.flatMap f)) = (wordVal (f a)).trans (wordVal (l.flatMap f)) :=
          wordVal_append (f a) (l.flatMap f)
        _ = (g a).trans (wordVal (l.map g)) := by
              have hl : ∀ a' ∈ l, wordVal (f a') = g a' := fun a' ha' => h a' (by simp [ha'])
              rw [h a (by simp), ih hl]
        _ = wordVal (g a :: l.map g) := (wordVal_cons (g a) (l.map g)).symm
        _ = wordVal ((a :: l).map g) := rfl

/-- reflection in `(ℝ ∙ 0)ᗮ` is the identity -/
lemma refl_zero_eq_id {m : ℕ} :
    (ℝ ∙ (0 : EVID (m + 1)))ᗮ.reflection = LinearIsometryEquiv.refl ℝ (EVID (m + 1)) := by
  apply LinearIsometryEquiv.ext
  intro x
  rw [Submodule.reflection_orthogonal_apply (𝕜 := ℝ) (K := ℝ ∙ (0 : EVID (m + 1))) x]
  rw [Submodule.reflection_singleton_apply]
  simp

/-- the main decomposition theorem for dimension ≥ 2 -/
lemma decomp_zero (ρ : Iso 0) : ∃ l : List (Iso 0), AllowedWord l ∧ wordVal l = ρ := by
  refine ⟨[], AllowedWord_nil, ?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  exact Subsingleton.elim _ _

/-! ### dimension-one coordinate facts -/

/-- every element of `EVID 1` is a scalar multiple of `e₀` -/
lemma eq_smul_e0_one (x : EVID 1) : x = (x (0 : Fin 1)) • (e0Elem 0) := by
  apply PiLp.ext
  intro j
  fin_cases j
  simp [e0Elem, eFn]

/-- `ρ e₀` has unit norm -/
lemma norm_map_unit {n : ℕ} (ρ : Iso (n + 1)) (e0 : EVID (n + 1)) (he : ‖e0‖ = 1) :
    ‖ρ e0‖ = 1 := by
  have h := ρ.norm_map e0
  rwa [he] at h

/-- `‖x‖²` equals the square of the only coordinate in `EVID 1` -/
lemma norm_sq_one_coord (x : EVID 1) : ‖x‖ ^ 2 = (x (0 : Fin 1)) ^ 2 := by
  rw [norm_sq_sum (m := 0) x]
  simp

/-- reflection in `(ℝ ∙ 0)ᗮ` is the identity -/
lemma refl_zero_eq_id_dim1 :
    (ℝ ∙ (0 : EVID 1))ᗮ.reflection = LinearIsometryEquiv.refl ℝ (EVID 1) := by
  ext x
  rw [Submodule.reflection_orthogonal_apply (𝕜 := ℝ) (K := ℝ ∙ (0 : EVID 1)) x]
  rw [Submodule.reflection_singleton_apply]
  simp

/-- the decomposition in dimension one -/
lemma decomp_one (ρ : Iso 1) : ∃ l : List (Iso 1), AllowedWord l ∧ wordVal l = ρ := by
  classical
  let a : ℝ := (ρ (e0Elem 0)) (0 : Fin 1)
  have h1 : ‖ρ (e0Elem 0)‖ = 1 := norm_map_unit ρ (e0Elem 0) (norm_e0Elem 0)
  have ha_sq : a ^ 2 = 1 := by
    have hsq : ‖ρ (e0Elem 0)‖ ^ 2 = a ^ 2 := by
      rw [norm_sq_one_coord (ρ (e0Elem 0))]
    nlinarith [h1, hsq]
  rcases (sq_eq_one_iff.mp ha_sq) with ha | ha
  · refine ⟨[], AllowedWord_nil, ?_⟩
    rw [wordVal_nil]
    have hρ0 : ρ (e0Elem 0) = e0Elem 0 := by
      rw [eq_smul_e0_one (ρ (e0Elem 0))]
      simp [a, ha, e0Elem_apply_zero]
    apply LinearIsometryEquiv.ext
    intro x
    calc
      x = (x (0 : Fin 1)) • (e0Elem 0) := eq_smul_e0_one x
      _ = (x (0 : Fin 1)) • (ρ (e0Elem 0)) := by rw [hρ0]
      _ = ρ ((x (0 : Fin 1)) • (e0Elem 0)) := (ρ.map_smul (x (0 : Fin 1)) (e0Elem 0)).symm
      _ = ρ x := (congrArg ρ (eq_smul_e0_one x)).symm
  · refine ⟨[flipLIE (0 : Fin 1)], allowed_cons (allowed_flipLIE (0 : Fin 1)) AllowedWord_nil, ?_⟩
    rw [wordVal_single]
    have hρ0 : ρ (e0Elem 0) = - (e0Elem 0) := by
      rw [eq_smul_e0_one (ρ (e0Elem 0))]
      simp [a, ha, e0Elem_apply_zero]
    apply LinearIsometryEquiv.ext
    intro x
    symm
    calc
      ρ x = ρ ((x (0 : Fin 1)) • (e0Elem 0)) := congrArg ρ (eq_smul_e0_one x)
      _ = (x (0 : Fin 1)) • (ρ (e0Elem 0)) := (ρ.map_smul (x (0 : Fin 1)) (e0Elem 0))
      _ = (x (0 : Fin 1)) • (- (e0Elem 0)) := by rw [hρ0]
      _ = -((x (0 : Fin 1)) • (e0Elem 0)) := by rw [smul_neg]
      _ = - x := congrArg (fun t : EVID 1 => -t) (eq_smul_e0_one x).symm
      _ = (flipLIE (0 : Fin 1)) x := by
            apply PiLp.ext
            intro j
            fin_cases j
            change -x 0 = (flipLIE (0 : Fin 1)) x 0
            rw [flipLIE_apply_self (0 : Fin 1) x]

lemma decomp_le1 (n : ℕ) (hn : n ≤ 1) (ρ : Iso n) :
    ∃ l : List (Iso n), AllowedWord l ∧ wordVal l = ρ := by
  interval_cases n
  · exact decomp_zero ρ
  · exact decomp_one ρ

/-- generic assembly: from per-normal reflection decompositions we get the full decomposition -/
lemma decomp_via_reflections {d : ℕ} (ρ : Iso d) (f : EVID d → List (Iso d))
    (hf_allowed : ∀ v : EVID d, AllowedWord (f v))
    (hf_word : ∀ v : EVID d, wordVal (f v) = (ℝ ∙ v)ᗮ.reflection) :
    ∃ l : List (Iso d), AllowedWord l ∧ wordVal l = ρ := by
  classical
  obtain ⟨lv, hρ⟩ := isometry_reflections ρ
  let lr : List (EVID d) := lv.reverse
  let σ : EVID d → Iso d := fun v => (ℝ ∙ v)ᗮ.reflection
  have hwordρ : ρ = wordVal (lr.map σ) := by
    rw [wordVal_eq_prod_rev]
    have hmaprev : (lr.map σ).reverse = lv.map σ := by
      dsimp [lr]
      rw [List.map_reverse, List.reverse_reverse]
    rw [hmaprev]
    exact hρ
  refine ⟨lr.flatMap f, ?_, ?_⟩
  · exact allowed_flatMap_any lr f (fun v hv => hf_allowed v)
  · calc
      wordVal (lr.flatMap f) = wordVal (lr.map σ) :=
        wordVal_flatMap_generic lr f σ (fun v hv => hf_word v)
      _ = ρ := hwordρ.symm

/-- the main decomposition theorem for dimension ≥ 2 -/
theorem decomp_ge2 (m : ℕ) (hm : 1 ≤ m) (ρ : Iso (m + 1)) :
    ∃ l : List (Iso (m + 1)), AllowedWord l ∧ wordVal l = ρ := by
  let f : EVID (m + 1) → List (Iso (m + 1)) := fun v =>
    if h : v = 0 then [] else Classical.choose (refl_allowed hm v h)
  have hf_allowed : ∀ v : EVID (m + 1), AllowedWord (f v) := by
    intro v
    dsimp [f]
    by_cases h : v = 0
    · rw [dif_pos h]
      exact AllowedWord_nil
    · rw [dif_neg h]
      exact (Classical.choose_spec (refl_allowed hm v h)).1
  have hf_word : ∀ v : EVID (m + 1), wordVal (f v) = (ℝ ∙ v)ᗮ.reflection := by
    intro v
    dsimp [f]
    by_cases h : v = 0
    · rw [dif_pos h, h, wordVal_nil]
      exact refl_zero_eq_id.symm
    · rw [dif_neg h]
      exact (Classical.choose_spec (refl_allowed hm v h)).2
  exact decomp_via_reflections ρ f hf_allowed hf_word

/-- reindex an isometry along an equivalence of the index types -/
noncomputable def reindexIso {m n : ℕ} (e : Fin n ≃ Fin m) (ρ : Iso n) : Iso m :=
  let el : EVID n ≃ₗᵢ[ℝ] EVID m := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  el.symm.trans (ρ.trans el)

/-- reindex a rotation isometry along an index equivalence -/
noncomputable def conjIso {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (g : Iso (m + 1)) : Iso n :=
  let el : EVID n ≃ₗᵢ[ℝ] EVID (m + 1) := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  el.trans (g.trans el.symm)

lemma cong_coord {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (x : EVID n) (k : Fin (m + 1)) :
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x) k = x (e.symm k) := by
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

lemma cong_symm_coord {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (y : EVID (m + 1)) (i : Fin n) :
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm y) i = y (e i) := by
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

lemma conjIso_apply {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (g : Iso (m + 1)) (x : EVID n) :
    (conjIso e g x) = ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm)
      (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) := by
  rfl

@[simp] lemma pi_cancel_left {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (x : EVID n) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x) = x := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

@[simp] lemma pi_cancel_right {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (x : EVID (m + 1)) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm) x) = x := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

lemma reindexIso_apply {m n : ℕ} (e : Fin n ≃ Fin m) (ρ : Iso n) (y : EVID m) :
    (reindexIso e ρ) y = (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e)
      (ρ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm y)) := by
  rfl

lemma conjIso_refl {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) :
    conjIso e (LinearIsometryEquiv.refl ℝ (EVID (m + 1))) = LinearIsometryEquiv.refl ℝ (EVID n) := by
  apply LinearIsometryEquiv.ext
  intro x
  simp [conjIso_apply]

lemma conjIso_trans {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (a b : Iso (m + 1)) :
    conjIso e (a.trans b) = (conjIso e a).trans (conjIso e b) := by
  apply LinearIsometryEquiv.ext
  intro x
  simp [conjIso_apply]

lemma conjIso_allowed {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) {g : Iso (m + 1)}
    (hg : Allowed g) : Allowed (conjIso e g) := by
  rcases hg with ⟨i, j, hij, c, s, hc, hs, hcs, hcoords⟩ | ⟨k0, hflip⟩
  · left
    refine ⟨e.symm i, e.symm j, ?_, c, s, hc, hs, hcs, ?_⟩
    · intro h
      exact hij (by
        calc i = e (e.symm i) := (Equiv.apply_symm_apply e i).symm
             _ = e (e.symm j) := by rw [h]
             _ = j := Equiv.apply_symm_apply e j)
    · intro x
      constructor
      · calc
          (conjIso e g x) (e.symm i)
              = (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) i := by
                  rw [conjIso_apply]
                  rw [cong_symm_coord e (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) (e.symm i)]
                  simp
          _ = c * x (e.symm i) - s * x (e.symm j) := by
                  rw [(hcoords ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)).1]
                  rw [cong_coord e x i, cong_coord e x j]
      · constructor
        · calc
            (conjIso e g x) (e.symm j)
                = (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) j := by
                    rw [conjIso_apply]
                    rw [cong_symm_coord e (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) (e.symm j)]
                    simp
            _ = s * x (e.symm i) + c * x (e.symm j) := by
                    rw [(hcoords ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)).2.1]
                    rw [cong_coord e x i, cong_coord e x j]
        · intro k hki hkj
          calc
            (conjIso e g x) k
                = (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) (e k) := by
                    rw [conjIso_apply]
                    rw [cong_symm_coord e (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) k]
            _ = ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x) (e k) := by
                    rw [(hcoords ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)).2.2 (e k)]
                    · intro h
                      apply hki
                      calc
                        k = e.symm (e k) := by simp
                        _ = e.symm i := by rw [h]
                    · intro h
                      apply hkj
                      calc
                        k = e.symm (e k) := by simp
                        _ = e.symm j := by rw [h]
            _ = x k := by
                    rw [cong_coord e x (e k)]
                    simp
  · right
    refine ⟨e.symm k0, ?_⟩
    intro x
    constructor
    · calc
        (conjIso e g x) (e.symm k0)
            = (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) k0 := by
                rw [conjIso_apply]
                rw [cong_symm_coord e (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) (e.symm k0)]
                simp
        _ = - x (e.symm k0) := by
                rw [(hflip ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)).1]
                rw [cong_coord e x k0]
    · intro j hjk
      calc
        (conjIso e g x) j
            = (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) (e j) := by
                rw [conjIso_apply]
                rw [cong_symm_coord e (g ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) j]
        _ = ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x) (e j) := by
                rw [(hflip ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)).2 (e j)]
                intro h
                apply hjk
                calc
                  j = e.symm (e j) := by simp
                  _ = e.symm k0 := by rw [h]
        _ = x j := by
                rw [cong_coord e x (e j)]
                simp

lemma conjIso_wordVal {m n : ℕ} (e : Fin n ≃ Fin (m + 1)) (l : List (Iso (m + 1))) :
    wordVal (l.map (conjIso e)) = conjIso e (wordVal l) := by
  induction l with
  | nil => simp [wordVal, conjIso_refl e]
  | cons a l ih =>
      rw [List.map_cons, wordVal_cons, ih, wordVal_cons]
      exact (conjIso_trans e a (wordVal l)).symm

lemma reindexIso_conj {n : ℕ} {m : ℕ} (e : Fin n ≃ Fin (m + 1)) (ρ : Iso n) :
    conjIso e (reindexIso e ρ) = ρ := by
  apply LinearIsometryEquiv.ext
  intro x
  simp [conjIso_apply, reindexIso_apply]

theorem decomp (n : ℕ) (ρ : Iso n) :
    ∃ l : List (Iso n), AllowedWord l ∧ wordVal l = ρ := by
  by_cases hn : n ≤ 1
  · exact decomp_le1 n hn ρ
  · -- n ≥ 2 : transport to dimension (n-1) + 1
    let m := n - 1
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hm_eq : m + 1 = n := by dsimp [m]; omega
    -- reindex Fin n ≃ Fin (m + 1)
    have hf : Fin (m + 1) = Fin n := by rw [hm_eq]
    have e : Fin n ≃ Fin (m + 1) := by
      exact (Equiv.cast hf).symm
    let ρ' : Iso (m + 1) := reindexIso e ρ
    obtain ⟨l', hallowed', hprod'⟩ := decomp_ge2 m hm ρ'
    -- reindex the word back to `Fin n`
    refine ⟨l'.map (conjIso e), ?_, ?_⟩
    · intro g hg
      rw [List.mem_map] at hg
      rcases hg with ⟨g', hg'l, rfl⟩
      exact conjIso_allowed e (hallowed' g' hg'l)
    · calc
        wordVal (l'.map (conjIso e)) = conjIso e (wordVal l') := conjIso_wordVal e l'
        _ = conjIso e ρ' := by rw [hprod']
        _ = ρ := by
              simpa [ρ'] using reindexIso_conj e ρ

/-- The requested statement: every orthogonal linear isometry of `EuclideanSpace ℝ (Fin n)`
is a (left-to-right) product of coordinate-plane rotations and coordinate reflections. -/
theorem orthogonal_word_decomposition
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ l : List (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
      (∀ e ∈ l,
        (∃ i j : Fin n, i ≠ j ∧ ∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧ c ^ 2 + s ^ 2 = 1 ∧
          ∀ x : EuclideanSpace ℝ (Fin n),
            e x i = c * x i - s * x j ∧ e x j = s * x i + c * x j ∧
            ∀ k : Fin n, k ≠ i → k ≠ j → e x k = x k)
        ∨ (∃ k : Fin n, ∀ x : EuclideanSpace ℝ (Fin n),
            e x k = - x k ∧ ∀ j : Fin n, j ≠ k → e x j = x j)) ∧
      ρ = l.foldl (fun acc e => acc.trans e)
            (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨l, hallowed, hprod⟩ := decomp n ρ
  refine ⟨l, ?_, ?_⟩
  · simpa [AllowedWord, Allowed] using hallowed
  · simpa [wordVal] using hprod.symm
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD
end

open Set
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

noncomputable section

abbrev EO (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## coordinate vectors -/
def eBasisO {n : ℕ} (i : Fin n) : EO n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun k => if k = i then 1 else 0)
@[simp] theorem eBasisO_coord_self {n : ℕ} (i : Fin n) : eBasisO i i = 1 := by simp [eBasisO]
@[simp] theorem eBasisO_coord_of_ne {n : ℕ} (i k : Fin n) (hik : k ≠ i) : eBasisO i k = 0 := by simp [eBasisO, hik]

def pairShift {n : ℕ} (i j : Fin n) (a b : ℝ) : EO n := a • eBasisO i + b • eBasisO j
@[simp] theorem pairShift_coord_i {n : ℕ} {i j : Fin n} (hij : i ≠ j) {a b : ℝ} :
    pairShift i j a b i = a := by
  simp [pairShift, eBasisO_coord_of_ne j i (by exact fun h : i = j => hij h)]
@[simp] theorem pairShift_coord_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) {a b : ℝ} :
    pairShift i j a b j = b := by
  simp [pairShift, eBasisO_coord_of_ne i j (by exact fun h : j = i => hij h.symm)]
@[simp] theorem pairShift_coord_k {n : ℕ} {i j : Fin n} (a b : ℝ) (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    pairShift i j a b k = 0 := by
  simp [pairShift, hki, hkj]

/-! ## frozen cube (coordinates other than i,j in [0,1]) -/

def frozenSetO (n : ℕ) (i j : Fin n) : Set (EO n) :=
  {x | ∀ k : Fin n, k ≠ i → k ≠ j → x k ∈ Set.Icc (0 : ℝ) 1}

theorem frozenSetO_convex (n : ℕ) (i j : Fin n) : Convex ℝ (frozenSetO n i j) := by
  intro x hx y hy a b ha hb hab
  intro k hki hkj
  have hx' : x k ∈ Set.Icc (0 : ℝ) 1 := hx k hki hkj
  have hy' : y k ∈ Set.Icc (0 : ℝ) 1 := hy k hki hkj
  have hc : a • (x k) + b • (y k) ∈ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hx' hy' ha hb hab
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hc

theorem frozenSetO_closed (n : ℕ) (i j : Fin n) : IsClosed (frozenSetO n i j) := by
  rw [show frozenSetO n i j = ⋂ k : Fin n, {x : EO n | (k ≠ i ∧ k ≠ j) → x k ∈ Set.Icc (0 : ℝ) 1} by
    ext x
    simp [frozenSetO]]
  exact isClosed_iInter (fun k => by
    by_cases hk : k ≠ i ∧ k ≠ j
    · have hset : {x : EO n | (k ≠ i ∧ k ≠ j) → x k ∈ Set.Icc (0 : ℝ) 1} = {x : EO n | x k ∈ Set.Icc (0 : ℝ) 1} := by
        ext x
        simp [hk]
      rw [hset]
      exact IsClosed.preimage (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) k)
        (isClosed_Icc (a := (0 : ℝ)) (b := 1))
    · have hset : {x : EO n | (k ≠ i ∧ k ≠ j) → x k ∈ Set.Icc (0 : ℝ) 1} = Set.univ := by
        ext x
        simp [hk]
      rw [hset]
      exact isClosed_univ)

/-! ## regBody: bodies {x | (xi,xj) ∈ P ∧ frozen} -/

def regBodyO (n : ℕ) (i j : Fin n) (P : Set (ℝ × ℝ)) : Set (EO n) :=
  {x | (x i, x j) ∈ P ∧ x ∈ frozenSetO n i j}

theorem regBodyO_convex {n : ℕ} (i j : Fin n) {P : Set (ℝ × ℝ)} (hP : Convex ℝ P) :
    Convex ℝ (regBodyO n i j P) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxP, hxf⟩
  rcases hy with ⟨hyP, hyf⟩
  constructor
  · have hxy : ((a • x + b • y) i, (a • x + b • y) j) = a • (x i, x j) + b • (y i, y j) := by
      ext p <;> simp [Pi.smul_apply]
    rw [hxy]
    exact hP hxP hyP ha hb hab
  · intro k hki hkj
    have hx' : x k ∈ Set.Icc (0 : ℝ) 1 := hxf k hki hkj
    have hy' : y k ∈ Set.Icc (0 : ℝ) 1 := hyf k hki hkj
    have hc : a • (x k) + b • (y k) ∈ Set.Icc (0 : ℝ) 1 :=
      (convex_Icc (0 : ℝ) 1) hx' hy' ha hb hab
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hc

theorem regBodyO_union (n : ℕ) (i j : Fin n) (P Q : Set (ℝ × ℝ)) :
    regBodyO n i j (P ∪ Q) = regBodyO n i j P ∪ regBodyO n i j Q := by
  ext x
  unfold regBodyO frozenSetO
  constructor
  · rintro ⟨h, hf⟩
    rcases h with hp | hq
    · exact Or.inl ⟨hp, hf⟩
    · exact Or.inr ⟨hq, hf⟩
  · rintro (⟨hp, hf⟩ | ⟨hq, hf⟩)
    · exact ⟨Or.inl hp, hf⟩
    · exact ⟨Or.inr hq, hf⟩

theorem regBodyO_inter (n : ℕ) (i j : Fin n) (P Q : Set (ℝ × ℝ)) :
    regBodyO n i j (P ∩ Q) = regBodyO n i j P ∩ regBodyO n i j Q := by
  ext x
  unfold regBodyO frozenSetO
  constructor
  · rintro ⟨⟨hp, hq⟩, hf⟩
    exact ⟨⟨hp, hf⟩, ⟨hq, hf⟩⟩
  · rintro ⟨⟨hp, hf⟩, ⟨hq, _⟩⟩
    exact ⟨⟨hp, hq⟩, hf⟩

theorem regBodyO_translate (n : ℕ) (i j : Fin n) (hij : i ≠ j) (P : Set (ℝ × ℝ)) (a b : ℝ) :
    regBodyO n i j ((fun p : ℝ × ℝ => (p.1 + a, p.2 + b)) '' P) =
      (fun x : EO n => x + pairShift i j a b) '' (regBodyO n i j P) := by
  ext x
  constructor
  · rintro ⟨hpair, hfrozen⟩
    rcases hpair with ⟨p, hp, hx⟩
    have hxi : x i = p.1 + a := by linarith [congrArg Prod.fst hx]
    have hxj : x j = p.2 + b := by linarith [congrArg Prod.snd hx]
    have hp' : (x i - a, x j - b) ∈ P := by
      have hpair_eq : (x i - a, x j - b) = p := by
        ext q <;> simp at hxi hxj ⊢ <;> linarith
      simpa [hpair_eq] using hp
    let y : EO n := x - pairShift i j a b
    have hy_in : y ∈ regBodyO n i j P := by
      unfold regBodyO frozenSetO
      constructor
      · have hyi : y i = x i - a := by simp [y, pairShift_coord_i hij]
        have hyj : y j = x j - b := by simp [y, pairShift_coord_j hij]
        simpa [hyi, hyj] using hp'
      · intro k hki hkj
        have hyk : y k = x k := by simp [y, pairShift_coord_k a b k hki hkj]
        rw [hyk]
        exact hfrozen k hki hkj
    refine ⟨y, hy_in, ?_⟩
    ext k
    simp [y]
  · rintro ⟨y, hy, rfl⟩
    unfold regBodyO frozenSetO at hy
    rcases hy with ⟨hpair, hfrozen⟩
    constructor
    · refine ⟨(y i, y j), hpair, ?_⟩
      ext p <;> simp [pairShift_coord_i hij, pairShift_coord_j hij]
    · intro k hki hkj
      have hyk : (y + pairShift i j a b) k = y k := by simp [pairShift_coord_k a b k hki hkj]
      rw [hyk]
      exact hfrozen k hki hkj

/-! ## boundedness -/
lemma norm_le_coord_bound (n : ℕ) (M : ℝ) (hM : 0 ≤ M) {x : EO n}
    (hx : ∀ i : Fin n, |x i| ≤ M) : ‖x‖ ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) * M := by
  have hsq : ‖x‖ ^ 2 ≤ (Fintype.card (Fin n) : ℝ) * M ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i : Fin n, ‖x i‖ ^ 2) ≤ ∑ i : Fin n, M ^ 2 := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h1 : ‖x i‖ ≤ M := by
          have habs : |x i| ≤ M := hx i
          simpa [Real.norm_eq_abs] using habs
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hM] using h1)
      _ = (Fintype.card (Fin n) : ℝ) * M ^ 2 := by simp
  have hs_nonneg : 0 ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) * M := mul_nonneg (Real.sqrt_nonneg _) hM
  have hprod : ‖x‖ ^ 2 ≤ (Real.sqrt (Fintype.card (Fin n) : ℝ) * M) ^ 2 := by
    have hc : (0 : ℝ) ≤ (Fintype.card (Fin n) : ℝ) := by positivity
    calc
      ‖x‖ ^ 2 ≤ (Fintype.card (Fin n) : ℝ) * M ^ 2 := hsq
      _ = (Real.sqrt (Fintype.card (Fin n) : ℝ) * M) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]
  have habs : |‖x‖| ≤ |Real.sqrt (Fintype.card (Fin n) : ℝ) * M| := sq_le_sq.mp hprod
  simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hM] using habs

theorem bounded_of_coord_bounds (n : ℕ) (M : ℝ) (hM : 0 ≤ M) {S : Set (EO n)}
    (hS : ∀ x ∈ S, ∀ i : Fin n, |x i| ≤ M) : Bornology.IsBounded S := by
  refine Metric.isBounded_iff.mpr ⟨2 * (Real.sqrt (Fintype.card (Fin n) : ℝ) * M) + 1, ?_⟩
  intro x hx y hy
  have hxle : ‖x‖ ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) * M := norm_le_coord_bound n M hM (hS x hx)
  have hyle : ‖y‖ ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) * M := norm_le_coord_bound n M hM (hS y hy)
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 * (Real.sqrt (Fintype.card (Fin n) : ℝ) * M) := by linarith
    _ ≤ 2 * (Real.sqrt (Fintype.card (Fin n) : ℝ) * M) + 1 := by linarith

/-- ConvexBody from closed convex nonempty set with coordinate bound -/
def mkBodyFrom (n : ℕ) {S : Set (EO n)} (hcl : IsClosed S) (hcv : Convex ℝ S) (hnon : S.Nonempty)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x ∈ S, ∀ i : Fin n, |x i| ≤ M) : ConvexBody (EO n) :=
  ⟨S, hcv, (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, bounded_of_coord_bounds n M hM hb⟩), hnon⟩/-! ## two-piece value equality -/

theorem twoPieceValEq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → μ K = 0)
    {P0 P1 M T0 T1 B0 B1 : ConvexBody V} {t : V}
    (hU0 : (P0 : Set V) = (M : Set V) ∪ (T0 : Set V))
    (hI0 : (B0 : Set V) = (M : Set V) ∩ (T0 : Set V))
    (hB0 : interior (B0 : Set V) = ∅)
    (hU1 : (P1 : Set V) = (M : Set V) ∪ (T1 : Set V))
    (hI1 : (B1 : Set V) = (M : Set V) ∩ (T1 : Set V))
    (hB1 : interior (B1 : Set V) = ∅)
    (hT : (T1 : Set V) = (fun x : V => x + t) '' (T0 : Set V)) :
    μ P0 = μ P1 := by
  have h0 := simple_valuation_binary_union (V := V) μ hadd hsimple
    (A := P0) (B := B0) (C := M) (D := T0) hU0 hI0 hB0
  have h1 := simple_valuation_binary_union (V := V) μ hadd hsimple
    (A := P1) (B := B1) (C := M) (D := T1) hU1 hI1 hB1
  have ht : μ T0 = μ T1 := htrans T0 T1 t hT
  linarith

/-! ## 2D region boilerplate (convexity, closedness, bounds) -/

lemma convex_plane_le (A B c : ℝ) : Convex ℝ {p : ℝ × ℝ | A * p.1 + B * p.2 ≤ c} := by
  intro x hx y hy a b ha hb hab
  change A * (a • x + b • y).1 + B * (a • x + b • y).2 ≤ c
  have hx' : A * x.1 + B * x.2 ≤ c := hx
  have hy' : A * y.1 + B * y.2 ≤ c := hy
  have h1 : A * (a • x + b • y).1 + B * (a • x + b • y).2
      = a * (A * x.1 + B * x.2) + b * (A * y.1 + B * y.2) := by
    simp [Pi.smul_apply, Pi.add_apply]
    ring
  rw [h1]
  calc
    a * (A * x.1 + B * x.2) + b * (A * y.1 + B * y.2) ≤ a * c + b * c := by
      nlinarith
    _ = c := by
      have hsum : a * c + b * c = (a + b) * c := by ring
      rw [hsum, hab]
      ring

lemma convex_plane_ge (A B c : ℝ) : Convex ℝ {p : ℝ × ℝ | c ≤ A * p.1 + B * p.2} := by
  intro x hx y hy a b ha hb hab
  change c ≤ A * (a • x + b • y).1 + B * (a • x + b • y).2
  have hx' : c ≤ A * x.1 + B * x.2 := hx
  have hy' : c ≤ A * y.1 + B * y.2 := hy
  have h1 : A * (a • x + b • y).1 + B * (a • x + b • y).2
      = a * (A * x.1 + B * x.2) + b * (A * y.1 + B * y.2) := by
    simp [Pi.smul_apply, Pi.add_apply]
    ring
  rw [h1]
  calc
    c = a * c + b * c := by
      have hsum : a * c + b * c = (a + b) * c := by ring
      rw [hsum, hab]
      ring
    _ ≤ a * (A * x.1 + B * x.2) + b * (A * y.1 + B * y.2) := by nlinarith

theorem continuous_pair_linear (A B : ℝ) : Continuous (fun p : ℝ × ℝ => A * p.1 + B * p.2) := by
  have hc1 : Continuous (fun p : ℝ × ℝ => A * p.1) := by
    exact Continuous.mul (continuous_const : Continuous fun _ : ℝ × ℝ => A) continuous_fst
  have hc2 : Continuous (fun p : ℝ × ℝ => B * p.2) := by
    exact Continuous.mul (continuous_const : Continuous fun _ : ℝ × ℝ => B) continuous_snd
  exact hc1.add hc2

theorem isClosed_plane_le (A B c : ℝ) : IsClosed {p : ℝ × ℝ | A * p.1 + B * p.2 ≤ c} := by
  exact IsClosed.preimage (continuous_pair_linear A B) isClosed_Iic

theorem isClosed_plane_ge (A B c : ℝ) : IsClosed {p : ℝ × ℝ | c ≤ A * p.1 + B * p.2} := by
  exact IsClosed.preimage (continuous_pair_linear A B) isClosed_Ici

/-- closedness of a region body -/
theorem regBodyO_closed (n : ℕ) (i j : Fin n) {P : Set (ℝ × ℝ)} (hP : IsClosed P) :
    IsClosed (regBodyO n i j P) := by
  have hc_i : Continuous (fun x : EO n => x i) :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) i
  have hc_j : Continuous (fun x : EO n => x j) :=
    PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) j
  have h1 : IsClosed {x : EO n | (x i, x j) ∈ P} :=
    IsClosed.preimage (Continuous.prodMk hc_i hc_j) hP
  rw [show regBodyO n i j P = {x : EO n | (x i, x j) ∈ P} ∩ frozenSetO n i j by
    ext x; simp [regBodyO]]
  exact h1.inter (frozenSetO_closed n i j)

/-- nonempty of a region body -/
theorem regBodyO_nonempty (n : ℕ) (i j : Fin n) (hij : i ≠ j) {P : Set (ℝ × ℝ)}
    (a b : ℝ) (hP : (a, b) ∈ P) : (regBodyO n i j P).Nonempty := by
  let z : EO n := a • eBasisO i + b • eBasisO j
  refine ⟨z, ?_⟩
  unfold regBodyO frozenSetO
  constructor
  · have hzi : z i = a := by
      calc
        z i = a * eBasisO i i + b * eBasisO j i := by simp [z]
        _ = a * 1 + b * 0 := by rw [eBasisO_coord_self, eBasisO_coord_of_ne j i hij]
        _ = a := by ring
    have hzj : z j = b := by
      calc
        z j = a * eBasisO i j + b * eBasisO j j := by simp [z]
        _ = a * 0 + b * 1 := by
          rw [eBasisO_coord_of_ne i j (by exact fun h : j = i => hij h.symm), eBasisO_coord_self]
        _ = b := by ring
    change (z i, z j) ∈ P
    simpa [hzi, hzj] using hP
  · intro k hki hkj
    simp [z, hki, hkj]

/-- coordinate bounds for a region body given bounds on the region -/
theorem regBodyO_coord_bounds (n : ℕ) (i j : Fin n) {P : Set (ℝ × ℝ)}
    (R : ℝ) (hR : 0 ≤ R) (hP : ∀ p ∈ P, |p.1| ≤ R ∧ |p.2| ≤ R) :
    ∀ x ∈ regBodyO n i j P, ∀ k : Fin n, |x k| ≤ max R 1 := by
  intro x hx k
  rcases hx with ⟨hpair, hfrozen⟩
  have hb := hP (x i, x j) hpair
  by_cases hki : k = i
  · subst k
    calc |x i| ≤ R := hb.1
      _ ≤ max R 1 := le_max_left R 1
  · by_cases hkj : k = j
    · subst k
      calc |x j| ≤ R := hb.2
        _ ≤ max R 1 := le_max_left R 1
    · have hk := hfrozen k hki hkj
      rw [Set.mem_Icc] at hk
      calc |x k| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        _ ≤ max R 1 := le_max_right R 1

/-- construct the ConvexBody of a region body -/
def mkRegBody (n : ℕ) (i j : Fin n) (hij : i ≠ j) {P : Set (ℝ × ℝ)}
    (hcl : IsClosed P) (hcv : Convex ℝ P) (a b : ℝ) (hP : (a, b) ∈ P)
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ p ∈ P, |p.1| ≤ R ∧ |p.2| ≤ R) : ConvexBody (EO n) :=
  mkBodyFrom n (regBodyO_closed n i j hcl) (regBodyO_convex i j hcv)
    (regBodyO_nonempty n i j hij a b hP) (max R 1)
    (le_trans hR (le_max_left R 1))
    (regBodyO_coord_bounds n i j R hR hb)

@[simp] theorem mkRegBody_coe (n : ℕ) (i j : Fin n) (hij : i ≠ j) {P : Set (ℝ × ℝ)}
    (hcl : IsClosed P) (hcv : Convex ℝ P) (a b : ℝ) (hP : (a, b) ∈ P)
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ p ∈ P, |p.1| ≤ R ∧ |p.2| ≤ R) :
    (mkRegBody n i j hij hcl hcv a b hP R hR hb : Set (EO n)) = regBodyO n i j P := rfl


/-! ## interior empty for level sets of a pair-linear functional -/
lemma interior_pair_level {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B c : ℝ)
    (hA : A ≠ 0) : interior {x : EO n | A * (x i) + B * (x j) = c} = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_interior] at hx
    rcases hx with ⟨t, hts, hto, hxt⟩
    rcases (Metric.isOpen_iff.mp hto x hxt) with ⟨ε, hε, hball⟩
    let z : EO n := eBasisO i
    have hzi : z i = 1 := by simp [z]
    have hz_ne : z ≠ 0 := by
      intro hz0
      have : (z i) = (0 : EO n) i := by rw [hz0]
      simp [hzi] at this
    have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    let δ : ℝ := ε / (2 * ‖z‖)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (lt_of_le_of_ne (norm_nonneg z) (Ne.symm hnz)))
    let y : EO n := x + δ • z
    have hyx : dist y x < ε := by
      rw [dist_eq_norm]
      have hyx' : ‖y - x‖ = δ * ‖z‖ := by
        rw [show y - x = δ • z by ext k; simp [y]]
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδ)]
      rw [hyx']
      have hδz : δ * ‖z‖ = ε / 2 := by
        dsimp [δ]
        field_simp [hnz]
      rw [hδz]
      linarith
    have hy_in_t : y ∈ t := hball hyx
    have hy_in_s : A * (y i) + B * (y j) = c := hts hy_in_t
    have hyi : y i = x i + δ := by simp [y, z]
    have hyj : y j = x j := by
      simp [y, z, (show j ≠ i from fun h : j = i => hij h.symm)]
    have hxL : A * (x i) + B * (x j) = c := hts hxt
    have hLy : A * (y i) + B * (y j) ≠ c := by
      rw [hyi, hyj]
      have h1 : A * (x i + δ) + B * (x j) = A * δ + c := by
        calc
          A * (x i + δ) + B * (x j) = (A * (x i) + B * (x j)) + A * δ := by ring
          _ = c + A * δ := by rw [hxL]
          _ = A * δ + c := by ring
      rw [h1]
      have hAδ : A * δ ≠ 0 := mul_ne_zero hA (ne_of_gt hδ)
      intro hc
      have hzero : A * δ = 0 := by linarith
      exact hAδ hzero
    exact False.elim (hLy hy_in_s)
  · intro hx
    exact False.elim hx

/-- level set of a pair-linear functional, when the B-coefficient is nonzero -/
lemma interior_pair_level_snd {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B c : ℝ)
    (hB : B ≠ 0) : interior {x : EO n | A * (x i) + B * (x j) = c} = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_interior] at hx
    rcases hx with ⟨t, hts, hto, hxt⟩
    rcases (Metric.isOpen_iff.mp hto x hxt) with ⟨ε, hε, hball⟩
    let z : EO n := eBasisO j
    have hzj : z j = 1 := by simp [z]
    have hz_ne : z ≠ 0 := by
      intro hz0
      have : (z j) = (0 : EO n) j := by rw [hz0]
      simp [hzj] at this
    have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    let δ : ℝ := ε / (2 * ‖z‖)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (lt_of_le_of_ne (norm_nonneg z) (Ne.symm hnz)))
    let y : EO n := x + δ • z
    have hyx : dist y x < ε := by
      rw [dist_eq_norm]
      have hyx' : ‖y - x‖ = δ * ‖z‖ := by
        rw [show y - x = δ • z by ext k; simp [y]]
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδ)]
      rw [hyx']
      have hδz : δ * ‖z‖ = ε / 2 := by
        dsimp [δ]
        field_simp [hnz]
      rw [hδz]
      linarith
    have hy_in_t : y ∈ t := hball hyx
    have hy_in_s : A * (y i) + B * (y j) = c := hts hy_in_t
    have hyi : y i = x i := by
      simp [y, z, (show i ≠ j from hij)]
    have hyj : y j = x j + δ := by simp [y, z]
    have hxL : A * (x i) + B * (x j) = c := hts hxt
    have hLy : A * (y i) + B * (y j) ≠ c := by
      rw [hyi, hyj]
      have h1 : A * (x i) + B * (x j + δ) = B * δ + c := by
        calc
          A * (x i) + B * (x j + δ) = (A * (x i) + B * (x j)) + B * δ := by ring
          _ = c + B * δ := by rw [hxL]
          _ = B * δ + c := by ring
      rw [h1]
      have hBδ : B * δ ≠ 0 := mul_ne_zero hB (ne_of_gt hδ)
      intro hc
      have hzero : B * δ = 0 := by linarith
      exact hBδ hzero
    exact False.elim (hLy hy_in_s)
  · intro hx
    exact False.elim hx

/-! ## scalar combo helpers -/
lemma combo_nonneg (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ a * x + b * y := by
  nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]
lemma combo_le_one (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x ≤ 1) (hy : y ≤ 1) : a * x + b * y ≤ 1 := by
  have h1 : a * x ≤ a * 1 := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * y ≤ b * 1 := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * x + b * y ≤ a * 1 + b * 1 := add_le_add h1 h2
  nlinarith [hab]
lemma combo_ge_one (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ a * x + b * y := by
  have h1 : a * 1 ≤ a * x := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * 1 ≤ b * y := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * 1 + b * 1 ≤ a * x + b * y := add_le_add h1 h2
  nlinarith [hab]
lemma combo_nonpos (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x ≤ 0) (hy : y ≤ 0) :
    a * x + b * y ≤ 0 := by
  have h1 : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hx
  have h2 : b * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy
  linarith

end
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD

open Set
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

noncomputable section

/-! ## Step 1: P0 (square) ↔ P1 (skewed left by t), t ∈ [0,1] -/

def rP0 : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}
def rP1 (t : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ p.1 + t * p.2 ∧ p.1 + t * p.2 ≤ 1}
def rM (t : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ p.1 ∧ p.1 + t * p.2 ≤ 1}
def rT0 (t : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 1 - t * p.2 ≤ p.1 ∧ p.1 ≤ 1}
def rT1 (t : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ -t * p.2 ≤ p.1 ∧ p.1 ≤ 0}

theorem rP0_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : rP0 = rM t ∪ rT0 t := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨h1, h2, h3, h4⟩
    by_cases h : p.1 ≤ 1 - t * p.2
    · left
      exact ⟨h3, h4, h1, by nlinarith⟩
    · right
      exact ⟨h3, h4, by nlinarith [ht0, ht1, h3, h4], h2⟩
  · rintro (⟨h3, h4, h1, h2⟩ | ⟨h3, h4, h5, h6⟩)
    · exact ⟨h1, by nlinarith [ht0, h3, h2], h3, h4⟩
    · exact ⟨by nlinarith [ht0, ht1, h3, h5], h6, h3, h4⟩

theorem rP1_eq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : rP1 t = rM t ∪ rT1 t := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨h3, h4, h5, h6⟩
    by_cases h : 0 ≤ p.1
    · left
      exact ⟨h3, h4, h, h6⟩
    · right
      exact ⟨h3, h4, by nlinarith [h5], le_of_not_ge h⟩
  · rintro (⟨h3, h4, h1, h2⟩ | ⟨h3, h4, h7, h1⟩)
    · exact ⟨h3, h4, by nlinarith [ht0, h3, h1], h2⟩
    · have htp2 : t * p.2 ≤ t := by simpa using (mul_le_mul_of_nonneg_left h4 ht0)
      exact ⟨h3, h4, by nlinarith [h7], by nlinarith [ht1, h1, htp2]⟩

theorem rT0_translate (t : ℝ) : (fun p : ℝ × ℝ => (p.1 - 1, p.2)) '' rT0 t = rT1 t := by
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    rcases hq with ⟨h1, h2, h3, h4⟩
    have hq1 : q.1 = p.1 + 1 := by
      have hc := congrArg Prod.fst hpq
      linarith
    have hq2 : q.2 = p.2 := by
      have hc := congrArg Prod.snd hpq
      simpa using hc
    have h1' : 0 ≤ p.2 := by simpa [hq2] using h1
    have h2' : p.2 ≤ 1 := by simpa [hq2] using h2
    have h3' : -t * p.2 ≤ p.1 := by
      have htmp : 1 - t * q.2 ≤ q.1 := h3
      rw [hq2, hq1] at htmp
      linarith
    have h4' : p.1 ≤ 0 := by
      have htmp : q.1 ≤ 1 := h4
      rw [hq1] at htmp
      linarith
    exact ⟨h1', h2', h3', h4'⟩
  · intro hp
    rcases hp with ⟨h1, h2, h3, h4⟩
    refine ⟨(p.1 + 1, p.2), ?_, ?_⟩
    · exact ⟨h1, h2, by nlinarith, by linarith⟩
    · ext p2 <;> simp

/-! Convexity -/
theorem rP0_convex : Convex ℝ rP0 := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4⟩
  rcases hy with ⟨h5, h6, h7, h8⟩
  change 0 ≤ (a • x + b • y).1 ∧ (a • x + b • y).1 ≤ 1 ∧ 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1
  constructor
  · show 0 ≤ (a • x + b • y).1
    simp
    exact combo_nonneg a b x.1 y.1 ha hb h1 h5
  constructor
  · show (a • x + b • y).1 ≤ 1
    simp
    exact combo_le_one a b x.1 y.1 ha hb hab h2 h6
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h3 h7
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h4 h8

theorem rM_convex (t : ℝ) : Convex ℝ (rM t) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4⟩
  rcases hy with ⟨h5, h6, h7, h8⟩
  change 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1 ∧ 0 ≤ (a • x + b • y).1 ∧
    (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h1 h5
  constructor
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h2 h6
  constructor
  · show 0 ≤ (a • x + b • y).1
    simp
    exact combo_nonneg a b x.1 y.1 ha hb h3 h7
  · show (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab h4 h8

theorem rT0_convex (t : ℝ) : Convex ℝ (rT0 t) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4⟩
  rcases hy with ⟨h5, h6, h7, h8⟩
  change 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1 ∧
    1 - t * (a • x + b • y).2 ≤ (a • x + b • y).1 ∧ (a • x + b • y).1 ≤ 1
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h1 h5
  constructor
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h2 h6
  constructor
  · show 1 - t * (a • x + b • y).2 ≤ (a • x + b • y).1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    have hx1 : 1 ≤ x.1 + t * x.2 := by nlinarith [h3]
    have hy1 : 1 ≤ y.1 + t * y.2 := by nlinarith [h7]
    have hge : 1 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 := by
      rw [hL]
      exact combo_ge_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab hx1 hy1
    linarith
  · show (a • x + b • y).1 ≤ 1
    simp
    exact combo_le_one a b x.1 y.1 ha hb hab h4 h8

theorem rT1_convex (t : ℝ) : Convex ℝ (rT1 t) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4⟩
  rcases hy with ⟨h5, h6, h7, h8⟩
  change 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1 ∧
    -t * (a • x + b • y).2 ≤ (a • x + b • y).1 ∧ (a • x + b • y).1 ≤ 0
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h1 h5
  constructor
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h2 h6
  constructor
  · show -t * (a • x + b • y).2 ≤ (a • x + b • y).1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    have hx3 : 0 ≤ x.1 + t * x.2 := by nlinarith [h3]
    have hy3 : 0 ≤ y.1 + t * y.2 := by nlinarith [h7]
    have hge : 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 := by
      rw [hL]
      exact combo_nonneg a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hx3 hy3
    linarith
  · show (a • x + b • y).1 ≤ 0
    simp
    exact combo_nonpos a b x.1 y.1 ha hb h4 h8

theorem rP1_convex (t : ℝ) : Convex ℝ (rP1 t) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4⟩
  rcases hy with ⟨h5, h6, h7, h8⟩
  change 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1 ∧
    0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 ∧
    (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h1 h5
  constructor
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h2 h6
  constructor
  · show 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_nonneg a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb h3 h7
  · show (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab h4 h8

/-! Closedness -/
theorem rP0_closed : IsClosed rP0 := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := by simpa using (isClosed_plane_ge 1 0 0)
  have hB : IsClosed {p : ℝ × ℝ | p.1 ≤ 1} := by simpa using (isClosed_plane_le 1 0 1)
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hD : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  rw [show rP0 = (({p | 0 ≤ p.1} ∩ {p | p.1 ≤ 1}) ∩ {p | 0 ≤ p.2}) ∩ {p | p.2 ≤ 1} by
    ext p <;> simp [rP0] <;> tauto]
  exact (((hA.inter hB).inter hC).inter hD)

theorem rM_closed (t : ℝ) : IsClosed (rM t) := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hB : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := by simpa using (isClosed_plane_ge 1 0 0)
  have hD : IsClosed {p : ℝ × ℝ | p.1 + t * p.2 ≤ 1} := by simpa using (isClosed_plane_le 1 t 1)
  rw [show rM t = (({p | 0 ≤ p.2} ∩ {p | p.2 ≤ 1}) ∩ {p | 0 ≤ p.1}) ∩ {p | p.1 + t * p.2 ≤ 1} by
    ext p <;> simp [rM] <;> tauto]
  exact (((hA.inter hB).inter hC).inter hD)

theorem rT0_closed (t : ℝ) : IsClosed (rT0 t) := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hB : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  have hC : IsClosed {p : ℝ × ℝ | 1 - t * p.2 ≤ p.1} := by
    have hh := (isClosed_plane_ge 1 t 1)
    have heq : {p : ℝ × ℝ | 1 - t * p.2 ≤ p.1} = {p : ℝ × ℝ | 1 ≤ p.1 + t * p.2} := by
      ext p
      constructor
      · intro hp
        have hp' : 1 - t * p.2 ≤ p.1 := by simpa using hp
        change 1 ≤ p.1 + t * p.2
        linarith
      · intro hp
        have hp' : 1 ≤ p.1 + t * p.2 := by simpa using hp
        change 1 - t * p.2 ≤ p.1
        linarith
    rw [heq]
    simpa using hh
  have hD : IsClosed {p : ℝ × ℝ | p.1 ≤ 1} := by simpa using (isClosed_plane_le 1 0 1)
  rw [show rT0 t = (({p | 0 ≤ p.2} ∩ {p | p.2 ≤ 1}) ∩ {p | 1 - t * p.2 ≤ p.1}) ∩ {p | p.1 ≤ 1} by
    ext p <;> simp [rT0] <;> tauto]
  exact (((hA.inter hB).inter hC).inter hD)

theorem rT1_closed (t : ℝ) : IsClosed (rT1 t) := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hB : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  have hC : IsClosed {p : ℝ × ℝ | -t * p.2 ≤ p.1} := by
    have hh := (isClosed_plane_ge 1 t 0)
    have heq : {p : ℝ × ℝ | -t * p.2 ≤ p.1} = {p : ℝ × ℝ | 0 ≤ p.1 + t * p.2} := by
      ext p
      constructor
      · intro hp
        have hp' : -t * p.2 ≤ p.1 := by simpa using hp
        change 0 ≤ p.1 + t * p.2
        linarith
      · intro hp
        have hp' : 0 ≤ p.1 + t * p.2 := by simpa using hp
        change -t * p.2 ≤ p.1
        linarith
    rw [heq]
    simpa using hh
  have hD : IsClosed {p : ℝ × ℝ | p.1 ≤ 0} := by simpa using (isClosed_plane_le 1 0 0)
  rw [show rT1 t = (({p | 0 ≤ p.2} ∩ {p | p.2 ≤ 1}) ∩ {p | -t * p.2 ≤ p.1}) ∩ {p | p.1 ≤ 0} by
    ext p <;> simp [rT1] <;> tauto]
  exact (((hA.inter hB).inter hC).inter hD)

theorem rP1_closed (t : ℝ) : IsClosed (rP1 t) := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hB : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 + t * p.2} := by
    have hh := (isClosed_plane_ge 1 t 0)
    simpa using hh
  have hD : IsClosed {p : ℝ × ℝ | p.1 + t * p.2 ≤ 1} := by simpa using (isClosed_plane_le 1 t 1)
  rw [show rP1 t = (({p | 0 ≤ p.2} ∩ {p | p.2 ≤ 1}) ∩ {p | 0 ≤ p.1 + t * p.2}) ∩ {p | p.1 + t * p.2 ≤ 1} by
    ext p <;> simp [rP1] <;> tauto]
  exact (((hA.inter hB).inter hC).inter hD)

/-! membership of nonempty points -/
theorem mem_P0_00 : (0, 0) ∈ rP0 := by simp [rP0]
theorem mem_M_00 (t : ℝ) : (0, 0) ∈ rM t := by simp [rM]
theorem mem_T1_00 (t : ℝ) : (0, 0) ∈ rT1 t := by simp [rT1]
theorem mem_T0_10 (t : ℝ) (ht0 : 0 ≤ t) : (1, 0) ∈ rT0 t := by simp [rT0]
theorem mem_P1_00 (t : ℝ) : (0, 0) ∈ rP1 t := by simp [rP1]

/-! bounds -/
theorem rP0_bounds : ∀ p ∈ rP0, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem rM_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ p ∈ rM t, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  constructor
  · have htp2 : 0 ≤ t * p.2 := mul_nonneg ht0 h1
    exact abs_le.mpr ⟨by linarith [h3], by linarith [h4, htp2]⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rT0_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ p ∈ rT0 t, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  constructor
  · have h1mtp2 : 0 ≤ 1 - t * p.2 := by nlinarith [ht0, ht1, h1]
    have hp1lo : 0 ≤ p.1 := by nlinarith [h3, h1mtp2]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rT1_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ p ∈ rT1 t, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  constructor
  · have htp2 : 0 ≤ t * p.2 := mul_nonneg ht0 h1
    have hp1lo : -1 ≤ p.1 := by nlinarith [h3, htp2]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rP1_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ p ∈ rP1 t, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  constructor
  · have htp2 : 0 ≤ t * p.2 := mul_nonneg ht0 h1
    have htp2le : t * p.2 ≤ t := by simpa using (mul_le_mul_of_nonneg_left h2 ht0)
    have hp1lo : -1 ≤ p.1 := by nlinarith [h3, htp2le]
    have hp1hi : p.1 ≤ 1 := by nlinarith [h4, htp2]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD

open Set
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

noncomputable section

/-! bodies for step 1 -/
def B0reg (t : ℝ) : Set (ℝ × ℝ) := rM t ∩ rT0 t
def B1reg (t : ℝ) : Set (ℝ × ℝ) := rM t ∩ rT1 t

theorem B0reg_convex (t : ℝ) : Convex ℝ (B0reg t) := by
  dsimp [B0reg]
  exact (rM_convex t).inter (rT0_convex t)
theorem B0reg_closed (t : ℝ) : IsClosed (B0reg t) := by
  dsimp [B0reg]
  exact (rM_closed t).inter (rT0_closed t)
theorem B0reg_mem (t : ℝ) (ht0 : 0 ≤ t) : (1, 0) ∈ B0reg t := by
  dsimp [B0reg]
  constructor
  · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact mem_T0_10 t ht0
theorem B0reg_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ p ∈ B0reg t, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  exact rM_bounds t ht0 ht1 p hp.1

theorem B1reg_convex (t : ℝ) : Convex ℝ (B1reg t) := by
  dsimp [B1reg]
  exact (rM_convex t).inter (rT1_convex t)
theorem B1reg_closed (t : ℝ) : IsClosed (B1reg t) := by
  dsimp [B1reg]
  exact (rM_closed t).inter (rT1_closed t)
theorem B1reg_mem (t : ℝ) : (0, 0) ∈ B1reg t := by
  dsimp [B1reg]
  constructor
  · exact mem_M_00 t
  · exact mem_T1_00 t
theorem B1reg_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ p ∈ B1reg t, |p.1| ≤ 1 ∧ |p.2| ≤ 1 := by
  intro p hp
  exact rM_bounds t ht0 ht1 p hp.1

theorem step1_value_eq (n : ℕ) (i j : Fin n) (hij : i ≠ j) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0) :
    μ (mkRegBody n i j hij rP0_closed rP0_convex 0 0 mem_P0_00 1 (by norm_num) rP0_bounds) =
      μ (mkRegBody n i j hij (rP1_closed t) (rP1_convex t) 0 0 (mem_P1_00 t) 1 (by norm_num)
          (rP1_bounds t ht0 ht1)) := by
  let P0body : ConvexBody (EO n) := mkRegBody n i j hij rP0_closed rP0_convex 0 0 mem_P0_00 1 (by norm_num) rP0_bounds
  let P1body : ConvexBody (EO n) := mkRegBody n i j hij (rP1_closed t) (rP1_convex t) 0 0 (mem_P1_00 t) 1 (by norm_num) (rP1_bounds t ht0 ht1)
  let Mbody : ConvexBody (EO n) := mkRegBody n i j hij (rM_closed t) (rM_convex t) 0 0 (mem_M_00 t) 1 (by norm_num) (rM_bounds t ht0 ht1)
  let T0body : ConvexBody (EO n) := mkRegBody n i j hij (rT0_closed t) (rT0_convex t) 1 0 (mem_T0_10 t ht0) 1 (by norm_num) (rT0_bounds t ht0 ht1)
  let T1body : ConvexBody (EO n) := mkRegBody n i j hij (rT1_closed t) (rT1_convex t) 0 0 (mem_T1_00 t) 1 (by norm_num) (rT1_bounds t ht0 ht1)
  let B0body : ConvexBody (EO n) := mkRegBody n i j hij (B0reg_closed t) (B0reg_convex t) 1 0 (B0reg_mem t ht0) 1 (by norm_num) (B0reg_bounds t ht0 ht1)
  let B1body : ConvexBody (EO n) := mkRegBody n i j hij (B1reg_closed t) (B1reg_convex t) 0 0 (B1reg_mem t) 1 (by norm_num) (B1reg_bounds t ht0 ht1)
  have hU0 : (P0body : Set (EO n)) = (Mbody : Set (EO n)) ∪ (T0body : Set (EO n)) := by
    change regBodyO n i j rP0 = regBodyO n i j (rM t) ∪ regBodyO n i j (rT0 t)
    rw [rP0_eq t ht0 ht1]
    exact regBodyO_union n i j (rM t) (rT0 t)
  have hI0 : (B0body : Set (EO n)) = (Mbody : Set (EO n)) ∩ (T0body : Set (EO n)) := by
    change regBodyO n i j (B0reg t) = regBodyO n i j (rM t) ∩ regBodyO n i j (rT0 t)
    dsimp [B0reg]
    exact regBodyO_inter n i j (rM t) (rT0 t)
  have hB0 : interior (B0body : Set (EO n)) = ∅ := by
    have hsub : (B0body : Set (EO n)) ⊆ {x : EO n | (x i) + t * (x j) = 1} := by
      intro x hx
      have hxr : x ∈ regBodyO n i j (B0reg t) := by simpa [B0body] using hx
      rcases hxr with ⟨hpair, hfrozen⟩
      change (x i) + t * (x j) = 1
      rcases hpair with ⟨hm, hT0⟩
      rcases hm with ⟨h1, h2, h3, h4⟩
      rcases hT0 with ⟨h5, h6, h7, h8⟩
      have hle : (x i) + t * (x j) ≤ 1 := h4
      have hge : 1 ≤ (x i) + t * (x j) := by linarith
      linarith
    have hlevel : interior {x : EO n | (x i) + t * (x j) = 1} = ∅ := by
      simpa using (interior_pair_level i j hij 1 t 1 (by norm_num))
    have hsub2 : interior (B0body : Set (EO n)) ⊆ (∅ : Set (EO n)) := by
      simpa [hlevel] using (interior_mono hsub)
    ext x
    constructor
    · intro hx
      exact False.elim (hsub2 hx)
    · intro hx
      exact False.elim hx
  have hU1 : (P1body : Set (EO n)) = (Mbody : Set (EO n)) ∪ (T1body : Set (EO n)) := by
    change regBodyO n i j (rP1 t) = regBodyO n i j (rM t) ∪ regBodyO n i j (rT1 t)
    rw [rP1_eq t ht0 ht1]
    exact regBodyO_union n i j (rM t) (rT1 t)
  have hI1 : (B1body : Set (EO n)) = (Mbody : Set (EO n)) ∩ (T1body : Set (EO n)) := by
    change regBodyO n i j (B1reg t) = regBodyO n i j (rM t) ∩ regBodyO n i j (rT1 t)
    dsimp [B1reg]
    exact regBodyO_inter n i j (rM t) (rT1 t)
  have hB1 : interior (B1body : Set (EO n)) = ∅ := by
    have hsub : (B1body : Set (EO n)) ⊆ {x : EO n | (x i) = 0} := by
      intro x hx
      have hxr : x ∈ regBodyO n i j (B1reg t) := by simpa [B1body] using hx
      rcases hxr with ⟨hpair, hfrozen⟩
      change (x i) = 0
      rcases hpair with ⟨hm, hT1⟩
      rcases hm with ⟨h1, h2, h3, h4⟩
      rcases hT1 with ⟨h5, h6, h7, h8⟩
      linarith
    have hlevel : interior {x : EO n | (x i) = 0} = ∅ := by
      simpa using (interior_pair_level i j hij 1 0 0 (by norm_num))
    have hsub2 : interior (B1body : Set (EO n)) ⊆ (∅ : Set (EO n)) := by
      simpa [hlevel] using (interior_mono hsub)
    ext x
    constructor
    · intro hx
      exact False.elim (hsub2 hx)
    · intro hx
      exact False.elim hx
  have hT : (T1body : Set (EO n)) = (fun x : EO n => x + pairShift i j (-1) 0) '' (T0body : Set (EO n)) := by
    change regBodyO n i j (rT1 t) =
      (fun x : EO n => x + pairShift i j (-1) 0) '' (regBodyO n i j (rT0 t))
    rw [← rT0_translate t]
    have hfun : (fun p : ℝ × ℝ => (p.1 - 1, p.2)) = (fun p : ℝ × ℝ => (p.1 + (-1), p.2 + 0)) := by
      funext p
      ext q <;> ring
    rw [hfun]
    rw [regBodyO_translate n i j hij (rT0 t) (-1) 0]
  have hEq : μ P0body = μ P1body := by
    exact twoPieceValEq (V := EO n) μ hadd htrans hsimple
      (P0 := P0body) (P1 := P1body) (M := Mbody) (T0 := T0body) (T1 := T1body)
      (B0 := B0body) (B1 := B1body) (t := pairShift i j (-1) 0)
      hU0 hI0 hB0 hU1 hI1 hB1 hT
  simpa [P0body, P1body] using hEq


/-! ## Step 2: P1(t) (square in (α,β)-chart, α=b, β=a+t·b) ↔ P2 (skew by s along α).
  w := a + t·b is invariant under shifts along f = e_j - t·e_i. -/

def rP2 (t s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 + t * p.2 ∧ p.1 + t * p.2 ≤ 1 ∧
       0 ≤ p.2 + s * (p.1 + t * p.2) ∧ p.2 + s * (p.1 + t * p.2) ≤ 1}

def rM2 (t s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ p.1 + t * p.2 ∧ p.1 + t * p.2 ≤ 1 ∧
       p.2 + s * (p.1 + t * p.2) ≤ 1}

def rU2 (t s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ p.1 + t * p.2 ∧ p.1 + t * p.2 ≤ 1 ∧
       1 - s * (p.1 + t * p.2) ≤ p.2}

def rV2 (t s : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 + t * p.2 ∧ p.1 + t * p.2 ≤ 1 ∧
       -s * (p.1 + t * p.2) ≤ p.2 ∧ p.2 ≤ 0}

/-- P1(t) = M2 ∪ U2 (split p.2 at 1 - s·w) -/
theorem rP1_eq2 (t s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : rP1 t = rM2 t s ∪ rU2 t s := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨h1, h2, h3, h4⟩
    by_cases h : p.2 ≤ 1 - s * (p.1 + t * p.2)
    · left
      exact ⟨h1, h2, h3, h4, by nlinarith⟩
    · right
      exact ⟨h1, h2, h3, h4, by nlinarith⟩
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, h3, h4⟩

/-- P2 = M2 ∪ V2 (split p.2 at 0) -/
theorem rP2_eq (t s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : rP2 t s = rM2 t s ∪ rV2 t s := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨h3, h4, h5, h6⟩
    by_cases h : 0 ≤ p.2
    · left
      have h5' : 0 ≤ p.1 + t * p.2 := h3
      refine ⟨h, ?_, h3, h4, h6⟩
      have hle : p.2 ≤ 1 := by nlinarith [hs0, h3, h6]
      exact hle
    · right
      exact ⟨h3, h4, by nlinarith [h5], le_of_not_ge h⟩
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h3, h4, h7, h1⟩)
    · exact ⟨h3, h4, by nlinarith [hs0, h1, h3], h5⟩
    · have hsw : s * (p.1 + t * p.2) ≤ s := by
        simpa using (mul_le_mul_of_nonneg_left h4 hs0)
      exact ⟨h3, h4, by nlinarith [h7], by nlinarith [hs1, h1, hsw]⟩

/-- V2 shifted by f = (-t, 1) gives U2 (w invariant under adding f) -/
theorem rV2_shift (t s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (fun p : ℝ × ℝ => (p.1 - t, p.2 + 1)) '' rV2 t s = rU2 t s := by
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    rcases hq with ⟨h3, h4, h7, h1⟩
    have hq1 : q.1 = p.1 + t := by
      have hc := congrArg Prod.fst hpq
      linarith
    have hq2 : q.2 = p.2 - 1 := by
      have hc := congrArg Prod.snd hpq
      linarith
    have hw : p.1 + t * p.2 = q.1 + t * q.2 := by
      rw [hq1, hq2]
      ring
    have hsw : s * (q.1 + t * q.2) ≤ s := by
      have hm := mul_le_mul_of_nonneg_left h4 hs0
      simpa using hm
    have hp1 : p.2 ≤ 1 := by linarith [h1, hq2]
    have hq2_ge : -1 ≤ q.2 := by
      have hge1 : -1 ≤ -s := by linarith
      have hge2 : -s ≤ -s * (q.1 + t * q.2) := by linarith [hsw]
      linarith
    have hp0 : 0 ≤ p.2 := by linarith [hq2_ge, hq2]
    have hw0 : 0 ≤ p.1 + t * p.2 := by
      rw [hw]
      exact h3
    have hw1 : p.1 + t * p.2 ≤ 1 := by
      rw [hw]
      exact h4
    have h7' : 1 - s * (p.1 + t * p.2) ≤ p.2 := by
      rw [← hw] at h7
      linarith [hq2]
    exact ⟨hp0, hp1, hw0, hw1, h7'⟩
  · intro hp
    rcases hp with ⟨h1, h2, h3, h4, h5⟩
    let q : ℝ × ℝ := (p.1 + t, p.2 - 1)
    have hwq : q.1 + t * q.2 = p.1 + t * p.2 := by
      dsimp [q]
      ring
    have hq_in : q ∈ rV2 t s := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hwq]
        exact h3
      · rw [hwq]
        exact h4
      · rw [hwq]
        change -s * (p.1 + t * p.2) ≤ q.2
        have hq2v : q.2 = p.2 - 1 := by rfl
        rw [hq2v]
        linarith [h5]
      · dsimp [q]
        linarith
    refine ⟨q, hq_in, ?_⟩
    ext p2 <;> ring


/-! Step-2 convexity / closedness / bounds / points -/
theorem rM2_convex (t s : ℝ) : Convex ℝ (rM2 t s) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4, h5⟩
  rcases hy with ⟨h6, h7, h8, h9, h10⟩
  change 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1 ∧
    0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 ∧
    (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1 ∧
    (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ 1
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h1 h6
  constructor
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h2 h7
  constructor
  · show 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_nonneg a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb h3 h8
  constructor
  · show (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab h4 h9
  · show (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ 1
    have hL : (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2)
        = a * (x.2 + s * (x.1 + t * x.2)) + b * (y.2 + s * (y.1 + t * y.2)) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.2 + s * (x.1 + t * x.2)) (y.2 + s * (y.1 + t * y.2)) ha hb hab h5 h10

theorem rU2_convex (t s : ℝ) : Convex ℝ (rU2 t s) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h1, h2, h3, h4, h5⟩
  rcases hy with ⟨h6, h7, h8, h9, h10⟩
  change 0 ≤ (a • x + b • y).2 ∧ (a • x + b • y).2 ≤ 1 ∧
    0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 ∧
    (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1 ∧
    1 - s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ (a • x + b • y).2
  constructor
  · show 0 ≤ (a • x + b • y).2
    simp
    exact combo_nonneg a b x.2 y.2 ha hb h1 h6
  constructor
  · show (a • x + b • y).2 ≤ 1
    simp
    exact combo_le_one a b x.2 y.2 ha hb hab h2 h7
  constructor
  · show 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_nonneg a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb h3 h8
  constructor
  · show (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab h4 h9
  · show 1 - s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ (a • x + b • y).2
    have hL : (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2)
        = a * (x.2 + s * (x.1 + t * x.2)) + b * (y.2 + s * (y.1 + t * y.2)) := by simp; ring
    have hx5 : 1 ≤ x.2 + s * (x.1 + t * x.2) := by linarith [h5]
    have hy5 : 1 ≤ y.2 + s * (y.1 + t * y.2) := by linarith [h10]
    have hge : 1 ≤ (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) := by
      rw [hL]
      exact combo_ge_one a b (x.2 + s * (x.1 + t * x.2)) (y.2 + s * (y.1 + t * y.2)) ha hb hab hx5 hy5
    linarith

theorem rV2_convex (t s : ℝ) : Convex ℝ (rV2 t s) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h3, h4, h7, h1⟩
  rcases hy with ⟨h8, h9, h10, h6⟩
  change 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 ∧
    (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1 ∧
    -s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ (a • x + b • y).2 ∧
    (a • x + b • y).2 ≤ 0
  constructor
  · show 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_nonneg a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb h3 h8
  constructor
  · show (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab h4 h9
  constructor
  · show -s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ (a • x + b • y).2
    have hL : (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2)
        = a * (x.2 + s * (x.1 + t * x.2)) + b * (y.2 + s * (y.1 + t * y.2)) := by simp; ring
    have hx7 : 0 ≤ x.2 + s * (x.1 + t * x.2) := by linarith [h7]
    have hy7 : 0 ≤ y.2 + s * (y.1 + t * y.2) := by linarith [h10]
    have hge : 0 ≤ (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) := by
      rw [hL]
      exact combo_nonneg a b (x.2 + s * (x.1 + t * x.2)) (y.2 + s * (y.1 + t * y.2)) ha hb hx7 hy7
    linarith
  · show (a • x + b • y).2 ≤ 0
    simp
    exact combo_nonpos a b x.2 y.2 ha hb h1 h6

theorem rP2_convex (t s : ℝ) : Convex ℝ (rP2 t s) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨h3, h4, h5, h6⟩
  rcases hy with ⟨h8, h9, h10, h7⟩
  change 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2 ∧
    (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1 ∧
    0 ≤ (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) ∧
    (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ 1
  constructor
  · show 0 ≤ (a • x + b • y).1 + t * (a • x + b • y).2
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_nonneg a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb h3 h8
  constructor
  · show (a • x + b • y).1 + t * (a • x + b • y).2 ≤ 1
    have hL : (a • x + b • y).1 + t * (a • x + b • y).2
        = a * (x.1 + t * x.2) + b * (y.1 + t * y.2) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.1 + t * x.2) (y.1 + t * y.2) ha hb hab h4 h9
  constructor
  · show 0 ≤ (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2)
    have hL : (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2)
        = a * (x.2 + s * (x.1 + t * x.2)) + b * (y.2 + s * (y.1 + t * y.2)) := by simp; ring
    rw [hL]
    exact combo_nonneg a b (x.2 + s * (x.1 + t * x.2)) (y.2 + s * (y.1 + t * y.2)) ha hb h5 h10
  · show (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2) ≤ 1
    have hL : (a • x + b • y).2 + s * ((a • x + b • y).1 + t * (a • x + b • y).2)
        = a * (x.2 + s * (x.1 + t * x.2)) + b * (y.2 + s * (y.1 + t * y.2)) := by simp; ring
    rw [hL]
    exact combo_le_one a b (x.2 + s * (x.1 + t * x.2)) (y.2 + s * (y.1 + t * y.2)) ha hb hab h6 h7


/-! Step-2 closedness -/
theorem rM2_closed (t s : ℝ) : IsClosed (rM2 t s) := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hB : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 + t * p.2} := by
    simpa using (isClosed_plane_ge 1 t 0)
  have hD : IsClosed {p : ℝ × ℝ | p.1 + t * p.2 ≤ 1} := by
    simpa using (isClosed_plane_le 1 t 1)
  have hE : IsClosed {p : ℝ × ℝ | p.2 + s * (p.1 + t * p.2) ≤ 1} := by
    have hh := (isClosed_plane_le s (1 + s * t) 1)
    have heq : {p : ℝ × ℝ | p.2 + s * (p.1 + t * p.2) ≤ 1} =
        {p : ℝ × ℝ | s * p.1 + (1 + s * t) * p.2 ≤ 1} := by
      ext p
      constructor
      · intro hp
        have hp' : p.2 + s * (p.1 + t * p.2) ≤ 1 := by simpa using hp
        change s * p.1 + (1 + s * t) * p.2 ≤ 1
        nlinarith
      · intro hp
        have hp' : s * p.1 + (1 + s * t) * p.2 ≤ 1 := by simpa using hp
        change p.2 + s * (p.1 + t * p.2) ≤ 1
        nlinarith
    rw [heq]
    simpa using hh
  rw [show rM2 t s = ((({p | 0 ≤ p.2} ∩ {p | p.2 ≤ 1}) ∩ {p | 0 ≤ p.1 + t * p.2}) ∩
      {p | p.1 + t * p.2 ≤ 1}) ∩ {p | p.2 + s * (p.1 + t * p.2) ≤ 1} by
    ext p <;> simp [rM2] <;> tauto]
  exact ((((hA.inter hB).inter hC).inter hD).inter hE)

theorem rU2_closed (t s : ℝ) : IsClosed (rU2 t s) := by
  have hA : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := by simpa using (isClosed_plane_ge 0 1 0)
  have hB : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := by simpa using (isClosed_plane_le 0 1 1)
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 + t * p.2} := by
    simpa using (isClosed_plane_ge 1 t 0)
  have hD : IsClosed {p : ℝ × ℝ | p.1 + t * p.2 ≤ 1} := by
    simpa using (isClosed_plane_le 1 t 1)
  have hE : IsClosed {p : ℝ × ℝ | 1 - s * (p.1 + t * p.2) ≤ p.2} := by
    have hh := (isClosed_plane_ge s (1 + s * t) 1)
    have heq : {p : ℝ × ℝ | 1 - s * (p.1 + t * p.2) ≤ p.2} =
        {p : ℝ × ℝ | 1 ≤ s * p.1 + (1 + s * t) * p.2} := by
      ext p
      constructor
      · intro hp
        have hp' : 1 - s * (p.1 + t * p.2) ≤ p.2 := by simpa using hp
        change 1 ≤ s * p.1 + (1 + s * t) * p.2
        nlinarith
      · intro hp
        have hp' : 1 ≤ s * p.1 + (1 + s * t) * p.2 := by simpa using hp
        change 1 - s * (p.1 + t * p.2) ≤ p.2
        nlinarith
    rw [heq]
    simpa using hh
  rw [show rU2 t s = ((({p | 0 ≤ p.2} ∩ {p | p.2 ≤ 1}) ∩ {p | 0 ≤ p.1 + t * p.2}) ∩
      {p | p.1 + t * p.2 ≤ 1}) ∩ {p | 1 - s * (p.1 + t * p.2) ≤ p.2} by
    ext p <;> simp [rU2] <;> tauto]
  exact ((((hA.inter hB).inter hC).inter hD).inter hE)

theorem rV2_closed (t s : ℝ) : IsClosed (rV2 t s) := by
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 + t * p.2} := by
    simpa using (isClosed_plane_ge 1 t 0)
  have hD : IsClosed {p : ℝ × ℝ | p.1 + t * p.2 ≤ 1} := by
    simpa using (isClosed_plane_le 1 t 1)
  have hE : IsClosed {p : ℝ × ℝ | -s * (p.1 + t * p.2) ≤ p.2} := by
    have hh := (isClosed_plane_ge s (1 + s * t) 0)
    have heq : {p : ℝ × ℝ | -s * (p.1 + t * p.2) ≤ p.2} =
        {p : ℝ × ℝ | 0 ≤ s * p.1 + (1 + s * t) * p.2} := by
      ext p
      constructor
      · intro hp
        have hp' : -s * (p.1 + t * p.2) ≤ p.2 := by simpa using hp
        change 0 ≤ s * p.1 + (1 + s * t) * p.2
        nlinarith
      · intro hp
        have hp' : 0 ≤ s * p.1 + (1 + s * t) * p.2 := by simpa using hp
        change -s * (p.1 + t * p.2) ≤ p.2
        nlinarith
    rw [heq]
    simpa using hh
  have hF : IsClosed {p : ℝ × ℝ | p.2 ≤ 0} := by simpa using (isClosed_plane_le 0 1 0)
  rw [show rV2 t s = ({p | 0 ≤ p.1 + t * p.2} ∩ {p | p.1 + t * p.2 ≤ 1}) ∩
      ({p | -s * (p.1 + t * p.2) ≤ p.2} ∩ {p | p.2 ≤ 0}) by
    ext p <;> simp [rV2] <;> tauto]
  exact ((hC.inter hD).inter (hE.inter hF))

theorem rP2_closed (t s : ℝ) : IsClosed (rP2 t s) := by
  have hC : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 + t * p.2} := by
    simpa using (isClosed_plane_ge 1 t 0)
  have hD : IsClosed {p : ℝ × ℝ | p.1 + t * p.2 ≤ 1} := by
    simpa using (isClosed_plane_le 1 t 1)
  have hE : IsClosed {p : ℝ × ℝ | 0 ≤ p.2 + s * (p.1 + t * p.2)} := by
    have hh := (isClosed_plane_ge s (1 + s * t) 0)
    have heq : {p : ℝ × ℝ | 0 ≤ p.2 + s * (p.1 + t * p.2)} =
        {p : ℝ × ℝ | 0 ≤ s * p.1 + (1 + s * t) * p.2} := by
      ext p
      constructor
      · intro hp
        have hp' : 0 ≤ p.2 + s * (p.1 + t * p.2) := by simpa using hp
        change 0 ≤ s * p.1 + (1 + s * t) * p.2
        nlinarith
      · intro hp
        have hp' : 0 ≤ s * p.1 + (1 + s * t) * p.2 := by simpa using hp
        change 0 ≤ p.2 + s * (p.1 + t * p.2)
        nlinarith
    rw [heq]
    simpa using hh
  have hF : IsClosed {p : ℝ × ℝ | p.2 + s * (p.1 + t * p.2) ≤ 1} := by
    have hh := (isClosed_plane_le s (1 + s * t) 1)
    have heq : {p : ℝ × ℝ | p.2 + s * (p.1 + t * p.2) ≤ 1} =
        {p : ℝ × ℝ | s * p.1 + (1 + s * t) * p.2 ≤ 1} := by
      ext p
      constructor
      · intro hp
        have hp' : p.2 + s * (p.1 + t * p.2) ≤ 1 := by simpa using hp
        change s * p.1 + (1 + s * t) * p.2 ≤ 1
        nlinarith
      · intro hp
        have hp' : s * p.1 + (1 + s * t) * p.2 ≤ 1 := by simpa using hp
        change p.2 + s * (p.1 + t * p.2) ≤ 1
        nlinarith
    rw [heq]
    simpa using hh
  rw [show rP2 t s = ({p | 0 ≤ p.1 + t * p.2} ∩ {p | p.1 + t * p.2 ≤ 1}) ∩
      ({p | 0 ≤ p.2 + s * (p.1 + t * p.2)} ∩ {p | p.2 + s * (p.1 + t * p.2) ≤ 1}) by
    ext p <;> simp [rP2] <;> tauto]
  exact ((hC.inter hD).inter (hE.inter hF))


/-! Step-2 membership points & bounds -/
theorem mem_M2 (t s : ℝ) : (0, 0) ∈ rM2 t s := by simp [rM2]
theorem mem_V2 (t s : ℝ) : (0, 0) ∈ rV2 t s := by simp [rV2]
theorem mem_P2 (t s : ℝ) : (0, 0) ∈ rP2 t s := by simp [rP2]
theorem mem_U2 (t s : ℝ) : (-t, 1) ∈ rU2 t s := by
  change 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 ∧ 0 ≤ -t + t * 1 ∧ -t + t * 1 ≤ 1 ∧
    1 - s * (-t + t * 1) ≤ 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

lemma abs_le_one_of_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |x| ≤ 1 := by
  rw [abs_of_nonneg h0]
  exact h1

lemma abs_p1_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (p1 p2 w : ℝ)
    (hw : w = p1 + t * p2) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp2 : |p2| ≤ 1) : |p1| ≤ 2 := by
  have hp1eq : p1 = w - t * p2 := by linarith
  rw [hp1eq]
  have htp2 : |t * p2| ≤ 1 := by
    have htabs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
    have hm := mul_le_mul htabs hp2 (abs_nonneg p2) (by norm_num)
    simpa [abs_mul] using hm
  have hwabs : |w| ≤ 1 := by rw [abs_of_nonneg hw0]; exact hw1
  calc
    |w - t * p2| ≤ |w| + |t * p2| := abs_sub w (t * p2)
    _ ≤ 1 + 1 := add_le_add hwabs htp2
    _ = 2 := by norm_num

theorem rM2_bounds (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ p ∈ rM2 t s, |p.1| ≤ 2 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4, h5⟩
  constructor
  · exact abs_p1_le_two ht0 ht1 p.1 p.2 (p.1 + t * p.2) rfl h3 h4 (abs_le_one_of_nonneg h1 h2)
  · exact abs_le_one_of_nonneg h1 h2

theorem rU2_bounds (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ p ∈ rU2 t s, |p.1| ≤ 2 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h1, h2, h3, h4, h5⟩
  constructor
  · exact abs_p1_le_two ht0 ht1 p.1 p.2 (p.1 + t * p.2) rfl h3 h4 (abs_le_one_of_nonneg h1 h2)
  · exact abs_le_one_of_nonneg h1 h2

theorem rV2_bounds (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ p ∈ rV2 t s, |p.1| ≤ 2 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h3, h4, h7, h1⟩
  constructor
  · have hsw1 : s * (p.1 + t * p.2) ≤ 1 := by
      have hsws : s * (p.1 + t * p.2) ≤ s := by
        simpa using (mul_le_mul_of_nonneg_left h4 hs0)
      linarith
    have hp2 : |p.2| ≤ 1 := by
      have hp2lo : -1 ≤ p.2 := by nlinarith [h7, hsw1]
      rw [abs_le]
      constructor
      · exact hp2lo
      · linarith [h1]
    exact abs_p1_le_two ht0 ht1 p.1 p.2 (p.1 + t * p.2) rfl h3 h4 hp2
  · have hsw1 : s * (p.1 + t * p.2) ≤ 1 := by
      have hsws : s * (p.1 + t * p.2) ≤ s := by
        simpa using (mul_le_mul_of_nonneg_left h4 hs0)
      linarith
    have hp2lo : -1 ≤ p.2 := by nlinarith [h7, hsw1]
    rw [abs_le]
    constructor
    · exact hp2lo
    · linarith [h1]

theorem rP2_bounds (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ p ∈ rP2 t s, |p.1| ≤ 2 ∧ |p.2| ≤ 1 := by
  intro p hp
  rcases hp with ⟨h3, h4, h5, h6⟩
  constructor
  · have hsw1 : s * (p.1 + t * p.2) ≤ 1 := by
      have hsws : s * (p.1 + t * p.2) ≤ s := by
        simpa using (mul_le_mul_of_nonneg_left h4 hs0)
      linarith
    have hp2 : |p.2| ≤ 1 := by
      have hp2lo : -1 ≤ p.2 := by nlinarith [h5, hsw1]
      have hp2hi : p.2 ≤ 1 := by nlinarith [h6, hs0, h3]
      rw [abs_le]
      exact ⟨hp2lo, hp2hi⟩
    exact abs_p1_le_two ht0 ht1 p.1 p.2 (p.1 + t * p.2) rfl h3 h4 hp2
  · have hsw1 : s * (p.1 + t * p.2) ≤ 1 := by
      have hsws : s * (p.1 + t * p.2) ≤ s := by
        simpa using (mul_le_mul_of_nonneg_left h4 hs0)
      linarith
    have hp2lo : -1 ≤ p.2 := by nlinarith [h5, hsw1]
    have hp2hi : p.2 ≤ 1 := by nlinarith [h6, hs0, h3]
    rw [abs_le]
    exact ⟨hp2lo, hp2hi⟩


end
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD

open Set
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

noncomputable section

/-! ## linear map on the region plane and images of regions -/

def Mlin (A B C D : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (A * p.1 + B * p.2, C * p.1 + D * p.2)
  map_add' := by
    intro p q
    ext <;> simp <;> ring
  map_smul' := by
    intro a p
    ext <;> simp <;> ring

@[simp] theorem Mlin_coord_fst (A B C D : ℝ) (p : ℝ × ℝ) :
    (Mlin A B C D p).1 = A * p.1 + B * p.2 := rfl
@[simp] theorem Mlin_coord_snd (A B C D : ℝ) (p : ℝ × ℝ) :
    (Mlin A B C D p).2 = C * p.1 + D * p.2 := rfl

def rImg (A B C D : ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  Mlin A B C D '' S

theorem rImg_union (A B C D : ℝ) (P Q : Set (ℝ × ℝ)) :
    rImg A B C D (P ∪ Q) = rImg A B C D P ∪ rImg A B C D Q := by
  change (Mlin A B C D) '' (P ∪ Q) = (Mlin A B C D) '' P ∪ (Mlin A B C D) '' Q
  exact Set.image_union (Mlin A B C D) P Q

lemma Mlin_injective (A B C D : ℝ) (hdet : A * D - B * C ≠ 0) :
    Function.Injective (Mlin A B C D) := by
  intro p q hpq
  have h1 := congrArg Prod.fst hpq
  have h2 := congrArg Prod.snd hpq
  -- h1 : A*p.1+B*p.2 = A*q.1+B*q.2, h2 : C*p.1+D*p.2 = C*q.1+D*q.2
  have hD1 : D * (A * p.1 + B * p.2) = D * (A * q.1 + B * q.2) := congrArg (fun z : ℝ => D * z) h1
  have hB2 : B * (C * p.1 + D * p.2) = B * (C * q.1 + D * q.2) := congrArg (fun z : ℝ => B * z) h2
  apply Prod.ext
  · have hmain : (A * D - B * C) * (p.1 - q.1) = 0 := by nlinarith
    have : p.1 - q.1 = 0 := (mul_eq_zero.mp hmain).resolve_left hdet
    linarith
  · have hC1 : C * (A * p.1 + B * p.2) = C * (A * q.1 + B * q.2) := congrArg (fun z : ℝ => C * z) h1
    have hA2 : A * (C * p.1 + D * p.2) = A * (C * q.1 + D * q.2) := congrArg (fun z : ℝ => A * z) h2
    have hmain : (A * D - B * C) * (p.2 - q.2) = 0 := by nlinarith
    have : p.2 - q.2 = 0 := (mul_eq_zero.mp hmain).resolve_left hdet
    linarith

theorem rImg_inter (A B C D : ℝ) (hdet : A * D - B * C ≠ 0) (P Q : Set (ℝ × ℝ)) :
    rImg A B C D (P ∩ Q) = rImg A B C D P ∩ rImg A B C D Q := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.1, rfl⟩, ⟨p, hp.2, rfl⟩⟩
  · rintro ⟨⟨p1, hp1, hq1⟩, ⟨p2, hp2, hq2⟩⟩
    have hpq : Mlin A B C D p1 = Mlin A B C D p2 := by rw [hq1, hq2]
    have hp12 : p1 = p2 := Mlin_injective A B C D hdet hpq
    refine ⟨p1, ⟨hp1, by simpa [hp12] using hp2⟩, hq1⟩

theorem rImg_convex (A B C D : ℝ) {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) :
    Convex ℝ (rImg A B C D S) := by
  exact hS.linear_image (Mlin A B C D)

lemma isBounded_of_coord_bounds (R : ℝ) (hR : 0 ≤ R) {S : Set (ℝ × ℝ)}
    (hS : ∀ p ∈ S, |p.1| ≤ R ∧ |p.2| ≤ R) : Bornology.IsBounded S := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R, ?_⟩
  intro p hp
  have hb := hS p hp
  rw [Prod.norm_def]
  exact max_le hb.1 hb.2

theorem rImg_isClosed (A B C D R : ℝ) (hR : 0 ≤ R) {S : Set (ℝ × ℝ)}
    (hcl : IsClosed S) (hS : ∀ p ∈ S, |p.1| ≤ R ∧ |p.2| ≤ R) :
    IsClosed (rImg A B C D S) := by
  have hcpS : IsCompact S := by
    exact Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨hcl, isBounded_of_coord_bounds R hR hS⟩
  have hcont : Continuous (Mlin A B C D) := (Mlin A B C D).continuous_of_finiteDimensional
  have hcp : IsCompact (rImg A B C D S) := hcpS.image hcont
  exact hcp.isClosed

theorem rImg_coord_bounds (A B C D Rb : ℝ) (hRb : 0 ≤ Rb) {S : Set (ℝ × ℝ)}
    (hS : ∀ p ∈ S, |p.1| ≤ Rb ∧ |p.2| ≤ Rb) :
    ∀ q ∈ rImg A B C D S, |q.1| ≤ (|A| + |B|) * Rb ∧ |q.2| ≤ (|C| + |D|) * Rb := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  constructor
  · calc
      |A * p.1 + B * p.2| ≤ |A * p.1| + |B * p.2| := abs_add_le _ _
      _ ≤ |A| * Rb + |B| * Rb := by
        apply add_le_add
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hS p hp).1 (abs_nonneg A)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hS p hp).2 (abs_nonneg B)
      _ = (|A| + |B|) * Rb := by ring
  · calc
      |C * p.1 + D * p.2| ≤ |C * p.1| + |D * p.2| := abs_add_le _ _
      _ ≤ |C| * Rb + |D| * Rb := by
        apply add_le_add
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hS p hp).1 (abs_nonneg C)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hS p hp).2 (abs_nonneg D)
      _ = (|C| + |D|) * Rb := by ring

lemma abs_sum_four_nonneg (A B C D : ℝ) : 0 ≤ |A| + |B| + |C| + |D| := by
  nlinarith [abs_nonneg A, abs_nonneg B, abs_nonneg C, abs_nonneg D]

lemma rImg_mem_zero (A B C D : ℝ) (S : Set (ℝ × ℝ)) (hS : (0, 0) ∈ S) :
    (0, 0) ∈ rImg A B C D S := by
  have h : Mlin A B C D (0, 0) = (0, 0) := by ext <;> simp [Mlin]
  rw [← h]
  exact Set.mem_image_of_mem (Mlin A B C D) hS

lemma rImg_mem_img (A B C D : ℝ) (S : Set (ℝ × ℝ)) (a b : ℝ) (hS : (a, b) ∈ S) :
    (A * a + B * b, C * a + D * b) ∈ rImg A B C D S := by
  have h : Mlin A B C D (a, b) = (A * a + B * b, C * a + D * b) := rfl
  rw [← h]
  exact Set.mem_image_of_mem (Mlin A B C D) hS

/-! ## transported bodies and the transported slant dissection -/

lemma mem_M_T0 (u : ℝ) : (1, 0) ∈ rM u ∩ rT0 u := by
  simp [rM, rT0]
lemma mem_M_T1 (u : ℝ) : (0, 0) ∈ rM u ∩ rT1 u := by
  simp [rM, rT1]

/-- ConvexBody over the M-image of a standard 1-bounded region -/
noncomputable def trBody (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A B C D : ℝ)
    {S : Set (ℝ × ℝ)} (hcl : IsClosed S) (hcv : Convex ℝ S)
    (hbS : ∀ p ∈ S, |p.1| ≤ 1 ∧ |p.2| ≤ 1) (a b : ℝ) (hmem : (a, b) ∈ S) :
    ConvexBody (EO n) :=
  mkRegBody n i j hij (rImg_isClosed A B C D 1 (by norm_num) hcl hbS)
    (rImg_convex A B C D hcv) (A * a + B * b) (C * a + D * b)
    (rImg_mem_img A B C D S a b hmem) (|A| + |B| + |C| + |D|)
    (abs_sum_four_nonneg A B C D)
    (fun q hq => by
      have hc := rImg_coord_bounds A B C D 1 (by norm_num) hbS q hq
      constructor
      · calc |q.1| ≤ (|A| + |B|) * 1 := hc.1
          _ = |A| + |B| := by ring
          _ ≤ |A| + |B| + |C| + |D| := by nlinarith [abs_nonneg C, abs_nonneg D]
      · calc |q.2| ≤ (|C| + |D|) * 1 := hc.2
          _ = |C| + |D| := by ring
          _ ≤ |A| + |B| + |C| + |D| := by nlinarith [abs_nonneg A, abs_nonneg B])

@[simp] theorem trBody_coe (n : ℕ) (i j : Fin n) (hij : i ≠ j) (A B C D : ℝ)
    {S : Set (ℝ × ℝ)} (hcl : IsClosed S) (hcv : Convex ℝ S)
    (hbS : ∀ p ∈ S, |p.1| ≤ 1 ∧ |p.2| ≤ 1) (a b : ℝ) (hmem : (a, b) ∈ S) :
    (trBody n i j hij A B C D hcl hcv hbS a b hmem : Set (EO n)) =
      regBodyO n i j (rImg A B C D S) := by
  simp [trBody]

lemma rImg_shift (A B C D : ℝ) (S : Set (ℝ × ℝ)) :
    rImg A B C D ((fun p : ℝ × ℝ => (p.1 - 1, p.2)) '' S) =
      (fun q : ℝ × ℝ => (q.1 - A, q.2 - C)) '' rImg A B C D S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨p0, hp0, rfl⟩
    refine ⟨Mlin A B C D p0, ⟨p0, hp0, rfl⟩, ?_⟩
    ext <;> simp <;> ring
  · rintro ⟨m, ⟨p0, hp0, rfl⟩, rfl⟩
    refine ⟨(p0.1 - 1, p0.2), ⟨p0, hp0, rfl⟩, ?_⟩
    ext <;> simp <;> ring

/-- A linear-image of the standard rP0/rP1(u) slant dissection has equal values. -/
theorem slant_transport (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (A B C D u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hdet : A * D - B * C ≠ 0)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0) :
    μ (trBody n i j hij A B C D rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00) =
      μ (trBody n i j hij A B C D (rP1_closed u) (rP1_convex u) (rP1_bounds u hu0 hu1)
          0 0 (mem_P1_00 u)) := by
  let P0 : ConvexBody (EO n) := trBody n i j hij A B C D rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00
  let P1 : ConvexBody (EO n) := trBody n i j hij A B C D (rP1_closed u) (rP1_convex u)
      (rP1_bounds u hu0 hu1) 0 0 (mem_P1_00 u)
  let Mb : ConvexBody (EO n) := trBody n i j hij A B C D (rM_closed u) (rM_convex u)
      (rM_bounds u hu0 hu1) 0 0 (mem_M_00 u)
  let T0 : ConvexBody (EO n) := trBody n i j hij A B C D (rT0_closed u) (rT0_convex u)
      (rT0_bounds u hu0 hu1) 1 0 (mem_T0_10 u hu0)
  let T1 : ConvexBody (EO n) := trBody n i j hij A B C D (rT1_closed u) (rT1_convex u)
      (rT1_bounds u hu0 hu1) 0 0 (mem_T1_00 u)
  let B0 : ConvexBody (EO n) := trBody n i j hij A B C D
      ((rM_closed u).inter (rT0_closed u)) ((rM_convex u).inter (rT0_convex u))
      (fun p hp => rM_bounds u hu0 hu1 p hp.1) 1 0 (mem_M_T0 u)
  let B1 : ConvexBody (EO n) := trBody n i j hij A B C D
      ((rM_closed u).inter (rT1_closed u)) ((rM_convex u).inter (rT1_convex u))
      (fun p hp => rM_bounds u hu0 hu1 p hp.1) 0 0 (mem_M_T1 u)
  have hU0 : (P0 : Set (EO n)) = (Mb : Set (EO n)) ∪ (T0 : Set (EO n)) := by
    change regBodyO n i j (rImg A B C D rP0) =
      regBodyO n i j (rImg A B C D (rM u)) ∪ regBodyO n i j (rImg A B C D (rT0 u))
    rw [← regBodyO_union n i j (rImg A B C D (rM u)) (rImg A B C D (rT0 u))]
    rw [← rImg_union A B C D (rM u) (rT0 u)]
    rw [← rP0_eq u hu0 hu1]
  have hU1 : (P1 : Set (EO n)) = (Mb : Set (EO n)) ∪ (T1 : Set (EO n)) := by
    change regBodyO n i j (rImg A B C D (rP1 u)) =
      regBodyO n i j (rImg A B C D (rM u)) ∪ regBodyO n i j (rImg A B C D (rT1 u))
    rw [← regBodyO_union n i j (rImg A B C D (rM u)) (rImg A B C D (rT1 u))]
    rw [← rImg_union A B C D (rM u) (rT1 u)]
    rw [← rP1_eq u hu0 hu1]
  have hI0 : (B0 : Set (EO n)) = (Mb : Set (EO n)) ∩ (T0 : Set (EO n)) := by
    change regBodyO n i j (rImg A B C D (rM u ∩ rT0 u)) =
      regBodyO n i j (rImg A B C D (rM u)) ∩ regBodyO n i j (rImg A B C D (rT0 u))
    rw [rImg_inter A B C D hdet (rM u) (rT0 u)]
    exact regBodyO_inter n i j (rImg A B C D (rM u)) (rImg A B C D (rT0 u))
  have hI1 : (B1 : Set (EO n)) = (Mb : Set (EO n)) ∩ (T1 : Set (EO n)) := by
    change regBodyO n i j (rImg A B C D (rM u ∩ rT1 u)) =
      regBodyO n i j (rImg A B C D (rM u)) ∩ regBodyO n i j (rImg A B C D (rT1 u))
    rw [rImg_inter A B C D hdet (rM u) (rT1 u)]
    exact regBodyO_inter n i j (rImg A B C D (rM u)) (rImg A B C D (rT1 u))
  have hT : (T1 : Set (EO n)) = (fun x : EO n => x + pairShift i j (-A) (-C)) '' (T0 : Set (EO n)) := by
    change regBodyO n i j (rImg A B C D (rT1 u)) =
      (fun x : EO n => x + pairShift i j (-A) (-C)) '' (regBodyO n i j (rImg A B C D (rT0 u)))
    rw [← regBodyO_translate n i j hij (rImg A B C D (rT0 u)) (-A) (-C)]
    congr 1
    calc
      rImg A B C D (rT1 u) =
          rImg A B C D ((fun p : ℝ × ℝ => (p.1 - 1, p.2)) '' rT0 u) := by rw [rT0_translate u]
      _ = (fun q : ℝ × ℝ => (q.1 - A, q.2 - C)) '' rImg A B C D (rT0 u) := rImg_shift A B C D (rT0 u)
  have hB0 : interior (B0 : Set (EO n)) = ∅ := by
    let α : ℝ := D - C * u
    let β : ℝ := A * u - B
    let c0 : ℝ := α * A + β * C
    have hsub : (B0 : Set (EO n)) ⊆ {x : EO n | α * (x i) + β * (x j) = c0} := by
      intro x hx
      have hxr : x ∈ regBodyO n i j (rImg A B C D (rM u ∩ rT0 u)) := by simpa [B0] using hx
      rcases hxr with ⟨hpair, hfrozen⟩
      change α * (x i) + β * (x j) = c0
      rcases hpair with ⟨p, hp01, hpq⟩
      rcases hp01 with ⟨hpM, hpT0⟩
      rcases hpM with ⟨h1, h2, h3, h4⟩
      rcases hpT0 with ⟨h5, h6, h7, h8⟩
      have hpu : p.1 + u * p.2 = 1 := by linarith
      have hxi : x i = A * p.1 + B * p.2 := by
        have hc := congrArg Prod.fst hpq.symm
        simpa using hc
      have hxj : x j = C * p.1 + D * p.2 := by
        have hc := congrArg Prod.snd hpq.symm
        simpa using hc
      dsimp [α, β, c0]
      rw [hxi, hxj]
      have hp1 : p.1 = 1 - u * p.2 := by linarith
      rw [hp1]
      ring
    have hlev : interior {x : EO n | α * (x i) + β * (x j) = c0} = ∅ := by
      by_cases hα : α ≠ 0
      · exact interior_pair_level i j hij α β c0 hα
      · have hα0 : α = 0 := by exact not_not.mp hα
        have hβ : β ≠ 0 := by
          intro hβ0
          have hα0' : D - C * u = 0 := by simpa [α] using hα0
          have hβ0' : A * u - B = 0 := by simpa [β] using hβ0
          have hD : D = C * u := by linarith
          have hB : B = A * u := by linarith
          have hz : A * D - B * C = 0 := by
            rw [hD, hB]
            ring
          exact hdet hz
        exact interior_pair_level_snd i j hij α β c0 hβ
    have hsub2 : interior (B0 : Set (EO n)) ⊆ (∅ : Set (EO n)) := by
      intro y hy
      have hyi : y ∈ interior {x : EO n | α * (x i) + β * (x j) = c0} := (interior_mono hsub) hy
      rw [hlev] at hyi
      exact hyi
    ext x
    constructor
    · intro hx
      exact False.elim (hsub2 hx)
    · intro hx
      exact False.elim hx
  have hB1 : interior (B1 : Set (EO n)) = ∅ := by
    have hsub : (B1 : Set (EO n)) ⊆ {x : EO n | (-D) * (x i) + B * (x j) = 0} := by
      intro x hx
      have hxr : x ∈ regBodyO n i j (rImg A B C D (rM u ∩ rT1 u)) := by simpa [B1] using hx
      rcases hxr with ⟨hpair, hfrozen⟩
      change (-D) * (x i) + B * (x j) = 0
      rcases hpair with ⟨p, hp01, hpq⟩
      rcases hp01 with ⟨hpM, hpT1⟩
      rcases hpM with ⟨h1, h2, h3, h4⟩
      rcases hpT1 with ⟨h5, h6, h7, h8⟩
      have hp10 : p.1 = 0 := by linarith
      have hxi : x i = A * p.1 + B * p.2 := by
        have hc := congrArg Prod.fst hpq.symm
        simpa using hc
      have hxj : x j = C * p.1 + D * p.2 := by
        have hc := congrArg Prod.snd hpq.symm
        simpa using hc
      have hxi' : x i = B * p.2 := by
        rw [hp10] at hxi
        simpa using hxi
      have hxj' : x j = D * p.2 := by
        rw [hp10] at hxj
        simpa using hxj
      rw [hxi', hxj']
      ring
    have hlev : interior {x : EO n | (-D) * (x i) + B * (x j) = 0} = ∅ := by
      by_cases hB : B ≠ 0
      · exact interior_pair_level_snd i j hij (-D) B 0 hB
      · have hB0 : B = 0 := not_not.mp hB
        have hD : D ≠ 0 := by
          intro hd0
          have hz : A * D - B * C = 0 := by
            rw [hd0, hB0]
            ring
          exact hdet hz
        have hDn : -D ≠ 0 := by
          intro hn
          apply hD
          linarith
        exact interior_pair_level i j hij (-D) B 0 hDn
    have hsub2 : interior (B1 : Set (EO n)) ⊆ (∅ : Set (EO n)) := by
      intro y hy
      have hyi : y ∈ interior {x : EO n | (-D) * (x i) + B * (x j) = 0} := (interior_mono hsub) hy
      rw [hlev] at hyi
      exact hyi
    ext x
    constructor
    · intro hx
      exact False.elim (hsub2 hx)
    · intro hx
      exact False.elim hx
  have hEq : μ P0 = μ P1 := by
    exact twoPieceValEq (V := EO n) μ hadd htrans hsimple
      (P0 := P0) (P1 := P1) (M := Mb) (T0 := T0) (T1 := T1)
      (B0 := B0) (B1 := B1) (t := pairShift i j (-A) (-C))
      hU0 hI0 hB0 hU1 hI1 hB1 hT
  simpa [P0, P1] using hEq

/-! ## composition and translation of region maps -/

@[simp] theorem Mlin_apply (A B C D : ℝ) (p : ℝ × ℝ) :
    Mlin A B C D p = (A * p.1 + B * p.2, C * p.1 + D * p.2) := rfl

lemma Mlin_comp (A B C D A' B' C' D' : ℝ) :
    (Mlin A B C D).comp (Mlin A' B' C' D') =
      Mlin (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  apply LinearMap.ext
  intro p
  ext <;> simp <;> ring

lemma Mlin_add (A B C D : ℝ) (p w : ℝ × ℝ) :
    Mlin A B C D (p + w) = Mlin A B C D p + Mlin A B C D w := by
  ext <;> simp <;> ring

theorem rImg_of_translate (A B C D : ℝ) (S : Set (ℝ × ℝ)) (w : ℝ × ℝ) :
    rImg A B C D ((fun p : ℝ × ℝ => p + w) '' S) =
      (fun q : ℝ × ℝ => q + Mlin A B C D w) '' rImg A B C D S := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨p0, hp0, rfl⟩
    refine ⟨Mlin A B C D p0, ⟨p0, hp0, rfl⟩, ?_⟩
    rw [Mlin_add]
  · rintro ⟨m, ⟨p0, hp0, rfl⟩, rfl⟩
    refine ⟨p0 + w, ⟨p0, hp0, rfl⟩, ?_⟩
    rw [Mlin_add]

/-- image of the unit square under the 90-degree rotation `(a,b) ↦ (b,-a)` is a translate -/
theorem rImg_rot90C : rImg 0 1 (-1) 0 rP0 = (fun p : ℝ × ℝ => p + (0, -1)) '' rP0 := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨h1, h2, h3, h4⟩
    refine ⟨(p.2, 1 - p.1), ?_, ?_⟩
    · change 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ 1 - p.1 ∧ 1 - p.1 ≤ 1
      constructor
      · exact h3
      constructor
      · exact h4
      constructor
      · linarith
      · linarith
    · ext <;> simp [Mlin_apply] <;> ring
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨h1, h2, h3, h4⟩
    refine ⟨(1 - q.2, q.1), ?_, ?_⟩
    · change 0 ≤ 1 - q.2 ∧ 1 - q.2 ≤ 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ 1
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · exact h1
      · exact h2
    · ext <;> simp [Mlin_apply] <;> ring

/-- image of the unit square under the horizontal shear `(a,b) ↦ (a - t b, b)` is rP1 t -/
theorem rImg_shearC (t : ℝ) : rImg 1 (-t) 0 1 rP0 = rP1 t := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    change 0 ≤ (Mlin 1 (-t) 0 1 p).2 ∧ (Mlin 1 (-t) 0 1 p).2 ≤ 1 ∧
      0 ≤ (Mlin 1 (-t) 0 1 p).1 + t * (Mlin 1 (-t) 0 1 p).2 ∧
      (Mlin 1 (-t) 0 1 p).1 + t * (Mlin 1 (-t) 0 1 p).2 ≤ 1
    rcases hp with ⟨h1, h2, h3, h4⟩
    have hx2 : (Mlin 1 (-t) 0 1 p).2 = p.2 := by rw [Mlin_apply]; simp
    have hx1 : (Mlin 1 (-t) 0 1 p).1 + t * (Mlin 1 (-t) 0 1 p).2 = p.1 := by
      rw [Mlin_apply]
      ring
    constructor
    · rw [hx2]
      exact h3
    constructor
    · rw [hx2]
      exact h4
    constructor
    · rw [hx1]
      exact h1
    · rw [hx1]
      exact h2
  · intro hx
    rcases hx with ⟨h1, h2, h3, h4⟩
    refine ⟨(x.1 + t * x.2, x.2), ?_, ?_⟩
    · change 0 ≤ x.1 + t * x.2 ∧ x.1 + t * x.2 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1
      exact ⟨h3, h4, h1, h2⟩
    · ext <;> simp [Mlin_apply] <;> ring

/-- rImg(t,1,-1,0) rP0 is a translate of rP1 t -/
lemma rImg_M2_rP0 (t : ℝ) :
    rImg t 1 (-1) 0 rP0 = (fun p : ℝ × ℝ => p + (t, -1)) '' (rP1 t) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨h1, h2, h3, h4⟩
    refine ⟨(t * p.1 + p.2 - t, 1 - p.1), ?_, ?_⟩
    · change 0 ≤ 1 - p.1 ∧ 1 - p.1 ≤ 1 ∧
          0 ≤ (t * p.1 + p.2 - t) + t * (1 - p.1) ∧
          (t * p.1 + p.2 - t) + t * (1 - p.1) ≤ 1
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · nlinarith
      · nlinarith
    · ext <;> simp [Mlin_apply] <;> ring
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨h1, h2, h3, h4⟩
    refine ⟨(1 - q.2, q.1 + t * q.2), ?_, ?_⟩
    · change 0 ≤ 1 - q.2 ∧ 1 - q.2 ≤ 1 ∧ 0 ≤ q.1 + t * q.2 ∧ q.1 + t * q.2 ≤ 1
      constructor
      · linarith
      constructor
      · linarith
      constructor
      · exact h3
      · exact h4
    · ext <;> simp [Mlin_apply] <;> ring

/-- rImg(1-t*s, -t, s, 1) rP0 is a translate of rImg(t,1,-1,0) (rP1 s) -/
lemma rImg_M3_rP0 (t s : ℝ) :
    rImg (1 - t * s) (-t) s 1 rP0 =
      (fun p : ℝ × ℝ => p + (-t, 1)) '' (rImg t 1 (-1) 0 (rP1 s)) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨h1, h2, h3, h4⟩
    refine ⟨Mlin t 1 (-1) 0 (1 - s * p.1 - p.2, p.1), ?_, ?_⟩
    · refine ⟨(1 - s * p.1 - p.2, p.1), ?_, rfl⟩
      change 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ (1 - s * p.1 - p.2) + s * p.1 ∧
        (1 - s * p.1 - p.2) + s * p.1 ≤ 1
      constructor
      · exact h1
      constructor
      · exact h2
      constructor
      · nlinarith
      · nlinarith
    · ext <;> simp [Mlin_apply] <;> ring
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨p, hp, rfl⟩
    rcases hp with ⟨h1, h2, h3, h4⟩
    refine ⟨(p.2, 1 - p.1 - s * p.2), ?_, ?_⟩
    · change 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ 0 ≤ 1 - p.1 - s * p.2 ∧ 1 - p.1 - s * p.2 ≤ 1
      constructor
      · exact h1
      constructor
      · exact h2
      constructor
      · nlinarith
      · nlinarith
    · ext <;> simp [Mlin_apply] <;> ring

@[simp] theorem rImg_id (S : Set (ℝ × ℝ)) : rImg 1 0 0 1 S = S := by
  ext x
  constructor
  · rintro ⟨p, hp, hpq⟩
    have hx : x = p := by simpa [Mlin_apply] using hpq.symm
    rw [hx]
    exact hp
  · intro hx
    exact ⟨x, hx, by simp [Mlin_apply]⟩

/-- three consecutive slant dissections move the cube onto the rotated square -/
theorem evl_chain (n : ℕ) (i j : Fin n) (hij : i ≠ j) (t s : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0) :
    μ (trBody n i j hij 1 0 0 1 rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00) =
      μ (trBody n i j hij (1 - t * s) (-t) s 1 (rP1_closed t) (rP1_convex t)
          (rP1_bounds t ht0 ht1) 0 0 (mem_P1_00 t)) := by
  let B0 : ConvexBody (EO n) := trBody n i j hij 1 0 0 1 rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00
  let B1 : ConvexBody (EO n) := trBody n i j hij 1 0 0 1 (rP1_closed t) (rP1_convex t)
      (rP1_bounds t ht0 ht1) 0 0 (mem_P1_00 t)
  let B2 : ConvexBody (EO n) := trBody n i j hij t 1 (-1) 0 rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00
  let B3 : ConvexBody (EO n) := trBody n i j hij t 1 (-1) 0 (rP1_closed s) (rP1_convex s)
      (rP1_bounds s hs0 hs1) 0 0 (mem_P1_00 s)
  let B4 : ConvexBody (EO n) := trBody n i j hij (1 - t * s) (-t) s 1 rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00
  let B5 : ConvexBody (EO n) := trBody n i j hij (1 - t * s) (-t) s 1 (rP1_closed t) (rP1_convex t)
      (rP1_bounds t ht0 ht1) 0 0 (mem_P1_00 t)
  have hd1 : (1 : ℝ) * 1 - 0 * 0 ≠ 0 := by norm_num
  have hd2 : t * 0 - 1 * (-1) ≠ 0 := by
    rw [show t * 0 - 1 * (-1) = 1 by ring]
    norm_num
  have hd3 : (1 - t * s) * 1 - (-t) * s ≠ 0 := by
    rw [show (1 - t * s) * 1 - (-t) * s = 1 by ring]
    norm_num
  have h01 : μ B0 = μ B1 := by
    exact slant_transport n i j hij 1 0 0 1 t ht0 ht1 hd1 μ hadd htrans hsimple
  have h23 : μ B2 = μ B3 := by
    exact slant_transport n i j hij t 1 (-1) 0 s hs0 hs1 hd2 μ hadd htrans hsimple
  have h45 : μ B4 = μ B5 := by
    exact slant_transport n i j hij (1 - t * s) (-t) s 1 t ht0 ht1 hd3 μ hadd htrans hsimple
  have hset12 : (B2 : Set (EO n)) =
      (fun x : EO n => x + pairShift i j t (-1)) '' (B1 : Set (EO n)) := by
    change regBodyO n i j (rImg t 1 (-1) 0 rP0) =
      (fun x : EO n => x + pairShift i j t (-1)) '' (regBodyO n i j (rImg 1 0 0 1 (rP1 t)))
    rw [rImg_id]
    rw [← regBodyO_translate n i j hij (rP1 t) t (-1)]
    have hfun : (fun p : ℝ × ℝ => (p.1 + t, p.2 + (-1))) = (fun p : ℝ × ℝ => p + (t, -1)) := by
      funext p
      ext <;> simp
    rw [hfun]
    exact congrArg (fun P : Set (ℝ × ℝ) => regBodyO n i j P) (rImg_M2_rP0 t)
  have h12 : μ B1 = μ B2 := htrans B1 B2 (pairShift i j t (-1)) hset12
  have hset34 : (B4 : Set (EO n)) =
      (fun x : EO n => x + pairShift i j (-t) 1) '' (B3 : Set (EO n)) := by
    change regBodyO n i j (rImg (1 - t * s) (-t) s 1 rP0) =
      (fun x : EO n => x + pairShift i j (-t) 1) '' (regBodyO n i j (rImg t 1 (-1) 0 (rP1 s)))
    rw [← regBodyO_translate n i j hij (rImg t 1 (-1) 0 (rP1 s)) (-t) 1]
    have hfun2 : (fun p : ℝ × ℝ => (p.1 + (-t), p.2 + 1)) = (fun p : ℝ × ℝ => p + (-t, 1)) := by
      funext p
      ext <;> simp
    rw [hfun2]
    exact congrArg (fun P : Set (ℝ × ℝ) => regBodyO n i j P) (rImg_M3_rP0 t s)
  have h34 : μ B3 = μ B4 := htrans B3 B4 (pairShift i j (-t) 1) hset34
  have hEq : μ B0 = μ B5 := by
    calc μ B0 = μ B1 := h01
      _ = μ B2 := h12
      _ = μ B3 := h23
      _ = μ B4 := h34
      _ = μ B5 := h45
  simpa [B0, B5] using hEq


end
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD

open Set
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

noncomputable section

/-! ## Ambient cube and imageLIE helpers -/

def fullCubeSet (n : ℕ) : Set (EO n) :=
  {x | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1}

theorem fullCubeSet_convex (n : ℕ) : Convex ℝ (fullCubeSet n) := by
  intro x hx y hy a b ha hb hab i
  have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := hx i
  have hy' : y i ∈ Set.Icc (0 : ℝ) 1 := hy i
  have hc : a • (x i) + b • (y i) ∈ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hx' hy' ha hb hab
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hc

theorem fullCubeSet_closed (n : ℕ) : IsClosed (fullCubeSet n) := by
  rw [show fullCubeSet n = ⋂ i : Fin n, {x : EO n | x i ∈ Set.Icc (0 : ℝ) 1} by
    ext x
    simp [fullCubeSet]]
  exact isClosed_iInter (fun i => by
    exact IsClosed.preimage (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) i)
      (isClosed_Icc (a := (0 : ℝ)) (b := 1)))

theorem fullCubeSet_nonempty (n : ℕ) : (fullCubeSet n).Nonempty := by
  refine ⟨0, ?_⟩
  intro i
  simp

theorem fullCubeSet_coord_bounds (n : ℕ) : ∀ x ∈ fullCubeSet n, ∀ i : Fin n, |x i| ≤ 1 := by
  intro x hx i
  have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := hx i
  rw [Set.mem_Icc] at hx'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- the standard cube `[0,1]^n` as a convex body -/
noncomputable def cubeBody (n : ℕ) : ConvexBody (EO n) :=
  mkBodyFrom n (fullCubeSet_closed n) (fullCubeSet_convex n) (fullCubeSet_nonempty n)
    1 (by norm_num) (fullCubeSet_coord_bounds n)

@[simp] theorem cubeBody_coe (n : ℕ) : (cubeBody n : Set (EO n)) = fullCubeSet n := rfl

/-- the axis box region of the EVL equals the full cube -/
theorem regBodyO_rP0_eq_fullCube (n : ℕ) (i j : Fin n) :
    regBodyO n i j rP0 = fullCubeSet n := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hp, hf⟩
    intro k
    by_cases hki : k = i
    · subst k
      rw [rP0] at hp
      exact ⟨hp.1, hp.2.1⟩
    · by_cases hkj : k = j
      · subst k
        rw [rP0] at hp
        exact ⟨hp.2.2.1, hp.2.2.2⟩
      · exact hf k hki hkj
  · intro hx
    change (x i, x j) ∈ rP0 ∧ x ∈ frozenSetO n i j
    constructor
    · rw [rP0]
      exact ⟨(hx i).1, (hx i).2, (hx j).1, (hx j).2⟩
    · intro k hki hkj
      exact hx k

/-- image under the identity -/
theorem imageLIE_refl (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) :
    ConvexBody.imageLIE (LinearIsometryEquiv.refl ℝ V) K = K := by
  apply ConvexBody.ext
  simp

/-- image under a composite: `imageLIE (e₁.trans e₂) K = imageLIE e₂ (imageLIE e₁ K)` -/
theorem imageLIE_trans (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e₁ e₂ : V ≃ₗᵢ[ℝ] V) (K : ConvexBody V) :
    ConvexBody.imageLIE (e₁.trans e₂) K =
      ConvexBody.imageLIE e₂ (ConvexBody.imageLIE e₁ K) := by
  apply ConvexBody.ext
  simp only [imageLIE_apply, Set.image_image]
  rfl

/-! ## half-tangent parametrisation of the plane rotation -/

lemma half_tan_nonneg (c s : ℝ) (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    0 ≤ s / (1 + c) := div_nonneg hs0 (by nlinarith [hc0])

lemma half_tan_le_one (c s : ℝ) (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    s / (1 + c) ≤ 1 := by
  have hc1 : c ≤ 1 := by nlinarith [hcs]
  have hden : 0 < 1 + c := by nlinarith [hc0]
  have hnum : s ≤ 1 + c := by nlinarith [hs0, hc1]
  rw [div_le_iff₀ hden]
  nlinarith

lemma half_tan_mul_den (c s : ℝ) (hc0 : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    (s / (1 + c)) * (1 + c) = s := by
  have hden : 1 + c ≠ 0 := by nlinarith [hc0]
  field_simp [hden]

lemma half_tan_rel1 (c s : ℝ) (hc0 : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    1 - (s / (1 + c)) * s = c := by
  have hden : 1 + c ≠ 0 := by nlinarith [hc0]
  have hm : (1 - (s / (1 + c)) * s) * (1 + c) = c * (1 + c) := by
    field_simp [hden]
    nlinarith [hcs]
  exact (mul_right_cancel₀ hden) hm

/-! ## composed shear = plane rotation region -/

theorem rImg_comp_image (A B C D A' B' C' D' : ℝ) (S : Set (ℝ × ℝ)) :
    rImg A B C D (rImg A' B' C' D' S) = (Mlin A B C D).comp (Mlin A' B' C' D') '' S := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Mlin A' B' C' D' q, ⟨q, hq, rfl⟩, rfl⟩

lemma fst_eq (c s t a b : ℝ) (h1 : 1 - t * s = c) (h2 : t * (1 + c) = s) :
    (1 - t * s) * (a + -(t * b)) + -(t * b) = c * a + -(s * b) := by
  calc
    (1 - t * s) * (a + -(t * b)) + -(t * b)
        = c * (a - t * b) - t * b := by rw [h1]; ring
    _ = c * a - (t * (1 + c)) * b := by ring
    _ = c * a - s * b := by rw [h2]
    _ = c * a + -(s * b) := by ring

lemma snd_eq (c s t a b : ℝ) (h1 : 1 - t * s = c) :
    s * (a + -(t * b)) + b = s * a + c * b := by
  calc
    s * (a + -(t * b)) + b = s * a - (s * t) * b + b := by ring
    _ = s * a + (1 - t * s) * b := by ring
    _ = s * a + c * b := by rw [h1]

lemma Mlin_rot_comp_eq (c s t : ℝ) (h1 : 1 - t * s = c) (h2 : t * (1 + c) = s) :
    (Mlin (1 - t*s) (-t) s 1).comp (Mlin 1 (-t) 0 1) = Mlin c (-s) s c := by
  apply LinearMap.ext
  intro p
  ext
  · simp
    exact fst_eq c s t p.1 p.2 h1 h2
  · simp
    exact snd_eq c s t p.1 p.2 h1

lemma rImg_rot_eq (c s t : ℝ) (h1 : 1 - t * s = c) (h2 : t * (1 + c) = s) :
    rImg (1 - t * s) (-t) s 1 (rP1 t) = rImg c (-s) s c rP0 := by
  calc
    rImg (1 - t * s) (-t) s 1 (rP1 t)
        = rImg (1 - t * s) (-t) s 1 (rImg 1 (-t) 0 1 rP0) := by
            rw [rImg_shearC t]
    _ = (Mlin (1 - t*s) (-t) s 1).comp (Mlin 1 (-t) 0 1) '' rP0 := by
            rw [rImg_comp_image]
    _ = (Mlin c (-s) s c) '' rP0 := by
            rw [Mlin_rot_comp_eq c s t h1 h2]
    _ = rImg c (-s) s c rP0 := rfl

/-! ## symm coordinate facts for `rotLIE` -/

lemma rotLIE_trans_neg (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotLIE i j hij c s hcs).trans
        (rotLIE i j hij c (-s) (by nlinarith [hcs])) =
      LinearIsometryEquiv.refl ℝ (EO n) := by
  apply LinearIsometryEquiv.ext
  intro x
  apply PiLp.ext
  intro k
  by_cases h1 : k = i
  · subst k
    simp [rotLIE_apply_i, rotLIE_apply_j i j hij]
    ring_nf
    linear_combination hcs * x i
  · by_cases h2 : k = j
    · subst k
      simp [rotLIE_apply_i, rotLIE_apply_j i j hij]
      ring_nf
      linear_combination hcs * x j
    · simp [rotLIE_apply_other i j hij c s hcs x k h1 h2,
        rotLIE_apply_other i j hij c (-s) (by nlinarith [hcs]) (rotLIE i j hij c s hcs x) k h1 h2]

lemma rotLIE_symm_eq (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotLIE i j hij c s hcs).symm = rotLIE i j hij c (-s) (by nlinarith [hcs]) := by
  let e := rotLIE i j hij c s hcs
  let g := rotLIE i j hij c (-s) (by nlinarith [hcs])
  have htr : e.trans g = LinearIsometryEquiv.refl ℝ (EO n) := by
    simpa [e, g] using rotLIE_trans_neg n i j hij c s hcs
  calc
    e.symm = e.symm.trans (e.trans g) := by
      rw [htr]
      simp
    _ = (e.symm.trans e).trans g := by rw [LinearIsometryEquiv.trans_assoc]
    _ = (LinearIsometryEquiv.refl ℝ (EO n)).trans g := by
      rw [LinearIsometryEquiv.symm_trans_self]
    _ = g := by simp

lemma rotLIE_symm_apply_i (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : EO n) :
    (rotLIE i j hij c s hcs).symm x i = c * x i + s * x j := by
  rw [rotLIE_symm_eq]
  simp [rotLIE_apply_i]

lemma rotLIE_symm_apply_j (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : EO n) :
    (rotLIE i j hij c s hcs).symm x j = -s * x i + c * x j := by
  rw [rotLIE_symm_eq]
  simp [rotLIE_apply_j i j hij]

lemma rotLIE_symm_apply_other (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (x : EO n) (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    (rotLIE i j hij c s hcs).symm x k = x k := by
  rw [rotLIE_symm_eq]
  simp [rotLIE_apply_other i j hij c (-s) (by nlinarith [hcs]) x k hki hkj]

/-- carrier of the rotation image of the cube -/
theorem rotLIE_cube_carrier (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n) : Set (EO n)) =
      regBodyO n i j (rImg c (-s) s c rP0) := by
  rw [imageLIE_apply, cubeBody_coe]
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, hxy⟩
    have hyx : y = rotLIE i j hij c s hcs x := hxy.symm
    rw [hyx]
    change ((rotLIE i j hij c s hcs x) i, (rotLIE i j hij c s hcs x) j) ∈
            rImg c (-s) s c rP0 ∧ (rotLIE i j hij c s hcs x) ∈ frozenSetO n i j
    constructor
    · have hpair : (x i, x j) ∈ rP0 := by
        rw [rP0]
        exact ⟨(hx i).1, (hx i).2, (hx j).1, (hx j).2⟩
      have him := rImg_mem_img c (-s) s c rP0 (x i) (x j) hpair
      rw [rotLIE_apply_i, rotLIE_apply_j i j hij]
      convert him using 1
      all_goals ring_nf
    · intro k hki hkj
      have hyk : (rotLIE i j hij c s hcs x) k = x k :=
        rotLIE_apply_other i j hij c s hcs x k hki hkj
      rw [hyk]
      exact hx k
  · intro hy
    rcases hy with ⟨hpair, hfrozen⟩
    rcases hpair with ⟨p, hp, hpq⟩
    have hp01 : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
      rw [rP0] at hp
      exact hp
    have hyi : y i = c * p.1 + (-s) * p.2 := by
      have hc := congrArg Prod.fst hpq
      simpa [Mlin_apply] using hc.symm
    have hyj : y j = s * p.1 + c * p.2 := by
      have hc := congrArg Prod.snd hpq
      simpa [Mlin_apply] using hc.symm
    refine ⟨(rotLIE i j hij c s hcs).symm y, ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k
        rw [rotLIE_symm_apply_i n i j hij c s hcs y]
        have hmain : c * y i + s * y j = p.1 := by
          rw [hyi, hyj]
          ring_nf
          linear_combination hcs * p.1
        rw [hmain]
        exact ⟨hp01.1, hp01.2.1⟩
      · by_cases hkj : k = j
        · subst k
          rw [rotLIE_symm_apply_j n i j hij c s hcs y]
          have hmain : -s * y i + c * y j = p.2 := by
            rw [hyi, hyj]
            ring_nf
            linear_combination hcs * p.2
          rw [hmain]
          exact ⟨hp01.2.2.1, hp01.2.2.2⟩
        · rw [rotLIE_symm_apply_other n i j hij c s hcs y k hki hkj]
          exact hfrozen k hki hkj
    · exact (rotLIE i j hij c s hcs).apply_symm_apply y
/-! ## symm coordinate facts for `rotLIE` -/
lemma sin_le_one (c s : ℝ) (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    s ≤ 1 := by
  nlinarith [hcs]

/-- EVL in the ambient space: rotating the cube within a coordinate plane preserves the value. -/
theorem evl_rot (n : ℕ) (i j : Fin n) (hij : i ≠ j) (c s : ℝ)
    (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0) :
    μ (ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n)) = μ (cubeBody n) := by
  let t := s / (1 + c)
  have hden : 1 + c ≠ 0 := by nlinarith [hc0]
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact half_tan_nonneg c s hc0 hs0 hcs
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact half_tan_le_one c s hc0 hs0 hcs
  have hs1 : s ≤ 1 := sin_le_one c s hc0 hs0 hcs
  have h1 : 1 - t * s = c := by
    dsimp [t]
    exact half_tan_rel1 c s hc0 hcs
  have h2 : t * (1 + c) = s := by
    dsimp [t]
    exact half_tan_mul_den c s hc0 hcs
  let B0 : ConvexBody (EO n) := trBody n i j hij 1 0 0 1 rP0_closed rP0_convex rP0_bounds 0 0 mem_P0_00
  let B5 : ConvexBody (EO n) := trBody n i j hij (1 - t * s) (-t) s 1 (rP1_closed t)
      (rP1_convex t) (rP1_bounds t ht0 ht1) 0 0 (mem_P1_00 t)
  have hchain : μ B0 = μ B5 :=
    evl_chain n i j hij t s ht0 ht1 hs0 hs1 μ hadd htrans hsimple
  have hB0car : (B0 : Set (EO n)) = (cubeBody n : Set (EO n)) := by
    dsimp [B0]
    rw [trBody_coe]
    rw [rImg_id]
    exact regBodyO_rP0_eq_fullCube n i j
  have hB0e : B0 = cubeBody n := ConvexBody.ext hB0car
  have hB0v : μ B0 = μ (cubeBody n) := by rw [hB0e]
  have hcar : (ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n) : Set (EO n)) =
      (B5 : Set (EO n)) := by
    rw [rotLIE_cube_carrier n i j hij c s hcs]
    dsimp [B5]
    rw [trBody_coe]
    change regBodyO n i j (rImg c (-s) s c rP0) =
      regBodyO n i j (rImg (1 - t * s) (-t) s 1 (rP1 t))
    rw [rImg_rot_eq c s t h1 h2]
  have hB5e : ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n) = B5 :=
    ConvexBody.ext hcar
  have hB5v : μ (ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n)) = μ B5 := by
    rw [hB5e]
  calc
    μ (ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n))
        = μ B5 := hB5v
    _ = μ B0 := hchain.symm
    _ = μ (cubeBody n) := hB0v

/-! ## flips and the elementary-invariance / word-walk -/

lemma flipLIE_invol (n : ℕ) (k : Fin n) (x : EO n) : flipLIE k (flipLIE k x) = x := by
  apply PiLp.ext
  intro j
  by_cases hjk : j = k
  · subst j
    simp [flipLIE_apply_self]
  · rw [flipLIE_apply_other k (flipLIE k x) j hjk]
    exact flipLIE_apply_other k x j hjk

theorem flip_image_fullCube (n : ℕ) (k : Fin n) :
    (flipLIE k) '' (fullCubeSet n) = (fun x : EO n => x + (-1) • eBasisO k) '' (fullCubeSet n) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨y + (1 : ℝ) • eBasisO k, ?_, ?_⟩
    · intro j
      by_cases hjk : j = k
      · subst j
        have hyk : (y + (1 : ℝ) • eBasisO k) k = 1 - x k := by
          calc
            (y + (1 : ℝ) • eBasisO k) k = y k + 1 := by simp [eBasisO_coord_self]
            _ = -x k + 1 := by
              congr 1
              have hc := congrArg (fun z : EO n => z k) hxy
              rw [flipLIE_apply_self] at hc
              exact hc.symm
            _ = 1 - x k := by ring
        rw [hyk]
        have hxk : x k ∈ Set.Icc (0 : ℝ) 1 := hx k
        rw [Set.mem_Icc] at hxk
        constructor <;> linarith
      · have hyj : (y + (1 : ℝ) • eBasisO k) j = x j := by
          calc
            (y + (1 : ℝ) • eBasisO k) j = y j := by simp [eBasisO_coord_of_ne k j hjk]
            _ = x j := by
              have hc := congrArg (fun z : EO n => z j) hxy
              rw [flipLIE_apply_other k x j hjk] at hc
              exact hc.symm
        rw [hyj]
        exact hx j
    · ext j
      by_cases hjk : j = k
      · subst j
        simp [eBasisO_coord_self]
      · simp [eBasisO_coord_of_ne k j hjk]
  · rintro ⟨x, hx, hxy⟩
    refine ⟨flipLIE k y, ?_, ?_⟩
    · intro j
      by_cases hjk : j = k
      · subst j
        have hyk : y k = x k + -1 := by
          have hc := congrArg (fun z : EO n => z k) hxy
          simpa [eBasisO_coord_self] using hc.symm
        have hwk : (flipLIE k y) k = 1 - x k := by
          rw [flipLIE_apply_self k y, hyk]
          ring
        rw [hwk]
        have hxk : x k ∈ Set.Icc (0 : ℝ) 1 := hx k
        rw [Set.mem_Icc] at hxk
        constructor <;> linarith
      · have hyj : y j = x j := by
          have hc := congrArg (fun z : EO n => z j) hxy
          simpa [eBasisO_coord_of_ne k j hjk] using hc.symm
        have hwj : (flipLIE k y) j = x j := by
          rw [flipLIE_apply_other k y j hjk, hyj]
        rw [hwj]
        exact hx j
    · rw [flipLIE_invol]

theorem flip_invariance (n : ℕ) (k : Fin n)
    (μ : ConvexBody (EO n) → ℝ)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B) :
    μ (ConvexBody.imageLIE (flipLIE k) (cubeBody n)) = μ (cubeBody n) := by
  have hB : (ConvexBody.imageLIE (flipLIE k) (cubeBody n) : Set (EO n)) =
      (fun x : EO n => x + (-1) • eBasisO k) '' (cubeBody n : Set (EO n)) := by
    rw [imageLIE_apply, cubeBody_coe]
    exact flip_image_fullCube n k
  exact (htrans (cubeBody n) (ConvexBody.imageLIE (flipLIE k) (cubeBody n))
      ((-1) • eBasisO k) hB).symm

theorem elementary_invariance (n : ℕ)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0)
    {e : EO n ≃ₗᵢ[ℝ] EO n} (he : Allowed e) :
    μ (ConvexBody.imageLIE e (cubeBody n)) = μ (cubeBody n) := by
  rcases he with hrot | hflip
  · rcases hrot with ⟨i, j, hij, c, s, hc0, hs0, hcs, hcoord⟩
    have heq : e = rotLIE i j hij c s hcs := by
      apply LinearIsometryEquiv.ext
      intro x
      apply PiLp.ext
      intro k
      by_cases h1 : k = i
      · subst k
        rw [(hcoord x).1]
        rw [rotLIE_apply_i]
      · by_cases h2 : k = j
        · subst k
          rw [(hcoord x).2.1]
          rw [rotLIE_apply_j i j hij]
        · rw [(hcoord x).2.2 k h1 h2]
          rw [rotLIE_apply_other i j hij c s hcs x k h1 h2]
    calc
      μ (ConvexBody.imageLIE e (cubeBody n))
          = μ (ConvexBody.imageLIE (rotLIE i j hij c s hcs) (cubeBody n)) := by rw [heq]
      _ = μ (cubeBody n) := evl_rot n i j hij c s hc0 hs0 hcs μ hadd htrans hsimple
  · rcases hflip with ⟨k, hcoord⟩
    have heq : e = flipLIE k := by
      apply LinearIsometryEquiv.ext
      intro x
      apply PiLp.ext
      intro j
      by_cases h1 : j = k
      · subst j
        rw [(hcoord x).1]
        rw [flipLIE_apply_self k x]
      · rw [(hcoord x).2 j h1]
        rw [flipLIE_apply_other k x j h1]
    calc
      μ (ConvexBody.imageLIE e (cubeBody n))
          = μ (ConvexBody.imageLIE (flipLIE k) (cubeBody n)) := by rw [heq]
      _ = μ (cubeBody n) := flip_invariance n k μ htrans

theorem value_step (n : ℕ)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0)
    (τ : EO n ≃ₗᵢ[ℝ] EO n) {e : EO n ≃ₗᵢ[ℝ] EO n} (he : Allowed e) :
    μ (ConvexBody.imageLIE (e.trans τ) (cubeBody n)) =
      μ (ConvexBody.imageLIE τ (cubeBody n)) := by
  rcases (imageLIE_admissible (V := EO n) (W := EO n) τ μ hadd htrans hsimple) with ⟨hadd', htrans', hsimple'⟩
  have hEI := elementary_invariance n (fun K : ConvexBody (EO n) => μ (ConvexBody.imageLIE τ K))
      hadd' htrans' hsimple' he
  simpa [imageLIE_trans (V := EO n) e τ (cubeBody n)] using hEI

theorem imageLIE_word_value_eq (n : ℕ)
    (μ : ConvexBody (EO n) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (EO n),
        (A : Set (EO n)) = (C : Set (EO n)) ∪ (D : Set (EO n)) →
        (B : Set (EO n)) = (C : Set (EO n)) ∩ (D : Set (EO n)) → μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EO n), ∀ t : EO n,
        (B : Set (EO n)) = (fun x : EO n => x + t) '' (A : Set (EO n)) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EO n), interior (K : Set (EO n)) = ∅ → μ K = 0) :
    ∀ (l : List (EO n ≃ₗᵢ[ℝ] EO n)), AllowedWord l →
      μ (ConvexBody.imageLIE (wordVal l) (cubeBody n)) = μ (cubeBody n) := by
  intro l
  induction l with
  | nil =>
      intro hallow
      rw [wordVal_nil]
      rw [imageLIE_refl (EO n) (cubeBody n)]
  | cons a l ih =>
      intro hallow
      have hA : Allowed a := hallow a (by simp)
      have hT : AllowedWord l := fun e he => hallow e (by simp [he])
      rw [wordVal_cons]
      calc
        μ (ConvexBody.imageLIE (a.trans (wordVal l)) (cubeBody n))
            = μ (ConvexBody.imageLIE (wordVal l) (cubeBody n)) :=
              value_step n μ hadd htrans hsimple (wordVal l) hA
        _ = μ (cubeBody n) := ih hT
end
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD

open Set
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger.KlainInlineVD

noncomputable section

theorem klain333_boxes_all_orientations
    (n : ℕ)
    (μ : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin n)),
        (A : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∪ (D : Set (EuclideanSpace ℝ (Fin n))) →
        (B : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∩ (D : Set (EuclideanSpace ℝ (Fin n))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)), ∀ t : EuclideanSpace ℝ (Fin n),
        (B : Set (EuclideanSpace ℝ (Fin n))) = (fun x : EuclideanSpace ℝ (Fin n) => x + t) '' (A : Set (EuclideanSpace ℝ (Fin n))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EuclideanSpace ℝ (Fin n)), interior (K : Set (EuclideanSpace ℝ (Fin n))) = ∅ → μ K = 0)
    (haxis : ∀ a : Fin n → ℝ, (∀ i : Fin n, 0 ≤ a i) → ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin n)),
        (Q : Set (EuclideanSpace ℝ (Fin n))) = {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) (a i)} →
        μ Q = 0) :
    ∀ ρ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin n)),
        (Q : Set (EuclideanSpace ℝ (Fin n))) = ρ '' {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1} →
        μ Q = 0 := by
  intro ρ Q hQ
  have hcube0 : μ (cubeBody n) = 0 := by
    have hset : (cubeBody n : Set (EO n)) =
        {x : EO n | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) ((fun _ : Fin n => 1) i)} := by
      rfl
    exact haxis (fun _ : Fin n => 1) (by intro i; norm_num) (cubeBody n) hset
  rcases (orthogonal_word_decomposition n ρ) with ⟨l, hallowed, hprod⟩
  have hword : μ (ConvexBody.imageLIE ρ (cubeBody n)) = μ (cubeBody n) := by
    have hw : μ (ConvexBody.imageLIE (wordVal l) (cubeBody n)) = μ (cubeBody n) :=
      imageLIE_word_value_eq n μ hadd htrans hsimple l hallowed
    have hρw : ρ = wordVal l := by
      rw [wordVal]
      exact hprod
    rw [hρw]
    exact hw
  have hQcar : (Q : Set (EO n)) = (ConvexBody.imageLIE ρ (cubeBody n) : Set (EO n)) := by
    rw [hQ]
    rw [imageLIE_apply]
    rfl
  have hQe : Q = ConvexBody.imageLIE ρ (cubeBody n) := ConvexBody.ext hQcar
  calc
    μ Q = μ (ConvexBody.imageLIE ρ (cubeBody n)) := by rw [hQe]
    _ = μ (cubeBody n) := hword
    _ = 0 := hcube0

end
end Commons.Geometry.Convex.Hadwiger.KlainInlineVD

namespace Commons.Geometry.Convex.Hadwiger.Klain333Step

/-!
# `klain333_step`: the induction step of Klain's Theorem 3.3

Statement (Klain, *A short proof of Hadwiger's characterization theorem*,
Mathematika 42 (1995), Thm 3.3, induction step `m ↦ m + 1`):

> If every continuous translation-invariant *simple* *even* valuation on
> `E m := EuclideanSpace ℝ (Fin m)` that vanishes on the unit cube is zero
> everywhere, then the same holds on `E (m+1)`.

"Simple" means vanishing on every convex body with empty interior.
"Even" means `φ K = φ (−K)`.

## IMPORTANT (checkpoint note on the statement shape)
Lean parses the dimension-`m` clause `∀ K : ConvexBody V, φ K = 0 → …` of the
final theorem as `∀ K, (φ K = 0 → …)` -- a per-body implication whose premise is
always satisfiable (the zero valuation is admissible), NOT as the intended
hypothesis `(∀ K, φ K = 0) → …`.  Consequently the final statement is logically
equivalent to *box-vanishing in dimension `m+1` with no induction hypothesis*
(it is still TRUE -- Klain Thm 3.3).  Accordingly the file develops:
* generic API (Sections 1-3): coordinates, translations, cylinders,
  interior/union/intersection/translation/negation laws, cube-cylinder identity,
  1-Lipschitz continuity of the unit-cylinder map -- all verified;
* `klain333_inner_step`: the *properly parenthesized* induction step
  `boxVan m → boxVan (m+1)`; its section-valuation (tau) part is complete
  (admissibility of `τ := μ ∘ cyl0` and `τ = 0` from `boxVan m`); the remaining
  in-dimension steps of Klain's proof (orientations, oblique prisms, zonotopes,
  centred bodies via Prop 3.1, simplex argument, polytope density) are still
  placeholders;
* final `klain333_step` = corollary (complete `boxVan (m+1)` via the full
  induction `boxVan 0 ⇒ ∀ n`, drop the vacuous antecedent).

## NEXT STRETCHES (concrete to-do, in order)
1. **Coordinate-cylinder height extension** inside `klain333_inner_step`, after
   the τ-section (`hτzero : ∀ K, τ K = 0`, i.e. `μ(cyl0 K 1) = 0`); goal:
   `μ(cyl0 K h) = 0` for all `h ≥ 0`.  DONE: `cylSlice`/`cylSliceSet`
   (convex/compact/nonempty; `interior_cylSlice_eq_empty`), membership lemmas
   `mem_cyl0_coords`/`mem_cyl0_translate_half`, and the **half-height split**
   `mu_cyl0_half : μ(cyl0 h) = μ(cyl0 (h/2)) + μ(cyl0 (h/2))`.  NEXT:
   - DONE: the general cut `mu_cyl0_split` for arbitrary `c ∈ [0,h]`:
     `μ(cyl0 h) = μ(cyl0 c) + μ(cyl0 (h−c))` (upper piece translated by `c•eLast`,
     membership lemma `mem_cyl0_translate`), with `cyl0_eq_of_height` and the
     sanity check `mu_cyl0_half_from_split` (half-split as `c = h/2`);
   - DONE: unit fractions -- `mu_cyl0_zero` (zero-height cylinders vanish via
     `interior_cyl0_zero_eq_empty`/`cyl0_zero_coe_eq_slice`), `mu_cyl0_add`
     (real additivity of cylinder measure in the height), `mu_cyl0_nat_mul`
     (`μ(cyl0 (k·t)) = k·μ(cyl0 t)` by induction), and
     `mu_cyl0_unit_fraction` (`μ(cyl0 K (1/k)) = 0` from `μ(cyl0 K 1) = 0`
     via `k·(1/k) = 1` and cancellation by `k ≠ 0`);
   - DONE: rational heights -- `mu_cyl0_rational` gives
     `μ(cyl0 K (p/q)) = 0` for all naturals `p`, `0 < q`, from
     `μ(cyl0 K 1) = 0` (via `mu_cyl0_unit_fraction` + `mu_cyl0_nat_mul`
     with `t = 1/q`, and the field identity `p·(1/q) = p/q`);
   - DONE: the height-Lipschitz bound `cyl0_hausdorff_heights`:
     `hausdorffDist (cyl0 K h) (cyl0 K h') ≤ |h - h'|` for `h,h' ≥ 0`
     (via `abs_sub_clamp_le` -- clamping the last coordinate into `[0,h']`
     moves it by at most `|h-h'|`; both directions of the Hausdorff inequality);
   - DONE: `mu_cyl0_nonneg`: `μ(cyl0 K h) = 0` for every real `h ≥ 0`, from
     `μ(cyl0 K 1) = 0` -- rationals `r m = ⌊h·m⌋/m → h` from below
     (`tendsto_nat_floor_mul_div_atTop` composed with `Nat.cast`), each
     `μ(cyl0 (r m)) = 0` by `mu_cyl0_rational`, the body sequence converges
     (`cyl0_hausdorff_heights` + `|r m - h| → 0`), `μ`-continuity transfers,
     and `tendsto_nhds_unique` closes.
   - DONE: feed-back into `klain333_inner_step`: `hCylOne` (unit cylinders
     vanish over every base) and `hCylAll : ∀ K h ≥ 0, μ(cyl0 m K h) = 0`
     via `mu_cyl0_nonneg`.
   - DONE (fleet, commons): the orientation lemma
     `klain333_boxes_all_orientations` (unit cube in every orientation
     vanishes given axis-box vanishing) is PROVEN and imported here.  Dev code
     lives in namespace `…Hadwiger.Klain333Step` (nested) so importing it does
     not clash with the commons `E`/`cubeBody`.
   - DONE (refactor, this file): the `τ`-part is factored out as the standalone
     `cyl0_all_heights` (admissible valuation on `E (m+1)` + `BoxVan m` ⇒ all
     coordinate cylinders `cyl0 m K h` vanish), and `rotCyl_all_heights`
     conjugates it by a frame isometry `ρ` (using the commons `imageLIE_*`
     transport) to get right cylinders in *every* orthonormal frame
     (`hcylFrame` inside `klain333_inner_step`).  `BoxVan n` is a bundled def
     (defeq to the giant clause list, cube clause in equiv-image form);
     `boxVan_zero` (dimension 0) is proven.
   - DONE (glue, inside `klain333_inner_step`): `haxis` (axis boxes, all real
     sizes) comes from the commons `valuation_zero_on_axisBoxes (m+1)` applied
     to `μ` (cube clause ⇒ every axis box vanishes); `hrot` (rotated unit
     cubes) from the commons `klain333_boxes_all_orientations (m+1)`;
     `hcylFrame` (right cylinders, every frame, every height ≥ 0) from
     `rotCyl_all_heights`.
   - DONE (fleet, commons `klain333_from_cylinders`, L80): the rest of
     Klain's in-dimension chain -- oblique prisms (Fig. 2 cut-and-paste,
     subdividing fat bases), polytopes `P + σ = P ∪ ⋃ᵢ (Fᵢ + σ)`, zonotopes
     and zonoids, centred bodies via the smooth-support route (Klain Prop 3.1,
     cosine transform), simplex `P = A ∪ P_c ∪ (−A + v)`, polytope
     triangulation, polytope density -- proving: admissible valuation on
     `E (m+1)` vanishing on every right cylinder (coordinate hyperplane of
     every frame, all heights) is identically zero.
   - DONE (glue, inside `klain333_inner_step`): the cylinder hypothesis of
     `klain333_from_cylinders` is derived from `hcylFrame` (`hcylQ`: rewrite the
     coordinate-set carrier of `imageLIE ρ (cyl0 m K h hh)` and use
     `val_eq_of_set_eq`), and the in-dimension chain is invoked.
   - DONE (this file): `boxVan_all n : BoxVan n` for all `n`, by Nat induction
     from `boxVan_zero` and `klain333_inner_step`; the final theorem
     `klain333_step` is `dsimp only; intro …; exact boxVan_all (m+1)`
     (the dimension-`m` clause is a per-body implication, hence vacuous).
2. **Orientations** (`klain333_boxes_all_orientations`, statement documented
   above in the file): 2-D scissors lemma + rotation decomposition + induction
   over the product; needs `dissection_additivity` (sibling, commons) for the
   cut-and-paste step.
3. Right cylinders over **arbitrary hyperplanes** via `τ_H` (uses
   `bodyIsometry` transport + orientation boxes), then **oblique prisms**
   (Fig. 2), **polytopes/zonotopes**, **centred bodies** (Prop 3.1,
   cosine transform), **simplices**, **polytope density**; assemble into
   `klain333_inner_step` and then the final theorem.

## DEVELOPMENT STATUS

COMPLETE.  The file derives, with no missing step, the requested theorem
`Commons.Geometry.Convex.Hadwiger.klain333_step` (together with the reusable
`Commons.Geometry.Convex.Hadwiger.Klain333Step.klain333_inner_step`,
`BoxVan`, `boxVan_zero`, `boxVan_all`, `cyl0_all_heights`, `rotCyl_all_heights`).

The only non-mathematical point of care is the namespace collision described in
the comment at the top of the file: the orientation machinery is inlined (as
`KlainInlineVD`) rather than imported, because
`orthogonal_word_decomposition` and `zonoidLimit_of_continuous_even_nonneg`
cannot coexist in one Lean environment.
-/

noncomputable section

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## Coordinate plumbing between `E n` and `E (n+1)` -/

/-- Drop the last coordinate. -/
def dropLast (n : ℕ) (y : E (n + 1)) : E n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j : Fin n => y (Fin.castSucc j))

/-- The last coordinate. -/
def lastCoord (n : ℕ) (y : E (n + 1)) : ℝ := y (Fin.last n)

/-- Embed by putting `0` in the last coordinate. -/
def emb (n : ℕ) (x : E n) : E (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun i : Fin (n + 1) =>
      if h : i = Fin.last n then 0 else x (Fin.castLT i (Fin.val_lt_last h)))

/-- The last-coordinate unit vector. -/
def eLast (n : ℕ) : E (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun i : Fin (n + 1) => if i = Fin.last n then 1 else 0)

@[simp] theorem emb_zero (n : ℕ) : emb n (0 : E n) = 0 := by ext i; simp [emb]

@[simp] theorem emb_add (n : ℕ) (x y : E n) : emb n (x + y) = emb n x + emb n y := by
  ext i
  dsimp [emb]
  by_cases h : i = Fin.last n
  · simp [h]
  · simp [h]

@[simp] theorem emb_smul (n : ℕ) (a : ℝ) (x : E n) : emb n (a • x) = a • emb n x := by
  ext i
  dsimp [emb]
  by_cases h : i = Fin.last n
  · simp [h]
  · simp [h]

@[simp] theorem dropLast_emb (n : ℕ) (x : E n) : dropLast n (emb n x) = x := by
  ext j; simp [dropLast, emb]

@[simp] theorem lastCoord_emb (n : ℕ) (x : E n) : lastCoord n (emb n x) = 0 := by
  simp [lastCoord, emb]

@[simp] theorem dropLast_eLast (n : ℕ) : dropLast n (eLast n) = 0 := by
  ext j; simp [dropLast, eLast]

@[simp] theorem lastCoord_eLast (n : ℕ) : lastCoord n (eLast n) = 1 := by
  simp [lastCoord, eLast]

/-- Any point decomposes as its first-coordinate part plus last-coordinate part. -/
theorem emb_dropLast_add_last (n : ℕ) (y : E (n + 1)) :
    emb n (dropLast n y) + lastCoord n y • eLast n = y := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  funext i
  by_cases h : i = Fin.last n
  · simp [emb, eLast, lastCoord, h]
  · have hlt := Fin.val_lt_last h
    have hi : Fin.castSucc (Fin.castLT i hlt) = i := by ext; simp [Fin.castLT]
    simp [emb, eLast, lastCoord, dropLast, h, hi]

@[simp] theorem dropLast_add (n : ℕ) (x y : E (n + 1)) : dropLast n (x + y) = dropLast n x + dropLast n y := by ext j; rfl
@[simp] theorem dropLast_smul (n : ℕ) (a : ℝ) (x : E (n + 1)) : dropLast n (a • x) = a • dropLast n x := by ext j; rfl
@[simp] theorem lastCoord_add (n : ℕ) (x y : E (n + 1)) : lastCoord n (x + y) = lastCoord n x + lastCoord n y := by rfl
@[simp] theorem lastCoord_smul (n : ℕ) (a : ℝ) (x : E (n + 1)) : lastCoord n (a • x) = a * lastCoord n x := by rfl
@[simp] theorem dropLast_neg (n : ℕ) (y : E (n + 1)) : dropLast n (-y) = - dropLast n y := by ext j; rfl
@[simp] theorem lastCoord_neg (n : ℕ) (y : E (n + 1)) : lastCoord n (-y) = - lastCoord n y := by rfl

/-! ## Norm bounds for the coordinate maps -/

@[simp] theorem norm_emb (n : ℕ) (x : E n) : ‖emb n x‖ = ‖x‖ := by
  have hsq : ‖emb n x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    simp [emb]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
    |>.elim (fun h => h) (fun h => by linarith [norm_nonneg (emb n x), norm_nonneg x])

theorem norm_dropLast_le (n : ℕ) (y : E (n + 1)) : ‖dropLast n y‖ ≤ ‖y‖ := by
  have hsq : ‖dropLast n y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    simp [dropLast]
    exact sq_nonneg (y (Fin.last n))
  have habs := sq_le_sq.mp hsq
  have h1 : |‖dropLast n y‖| = ‖dropLast n y‖ := abs_of_nonneg (norm_nonneg _)
  have h2 : |‖y‖| = ‖y‖ := abs_of_nonneg (norm_nonneg _)
  linarith

theorem abs_lastCoord_le_norm (n : ℕ) (y : E (n + 1)) : |lastCoord n y| ≤ ‖y‖ := by
  have h := PiLp.norm_apply_le (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) => ℝ) y (Fin.last n)
  simpa [lastCoord] using h

@[simp] theorem norm_eLast (n : ℕ) : ‖eLast n‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [Fin.sum_univ_castSucc]
  simp [eLast]

/-! ## The coordinate unit cube -/

/-- The unit cube `[0,1]^n` in `E n`. -/
def cubeSet (n : ℕ) : Set (E n) := {x | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1}

theorem cubeSet_eq_equiv_image (n : ℕ) :
    cubeSet n = (EuclideanSpace.equiv (Fin n) ℝ).symm ''
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) := by
  ext x
  constructor
  · intro hx
    refine ⟨(EuclideanSpace.equiv (Fin n) ℝ) x, ?_, ?_⟩
    · intro i hi
      exact hx i
    · rfl
  · rintro ⟨f, hf, rfl⟩
    intro i
    exact hf i trivial

theorem cubeSet_convex (n : ℕ) : Convex ℝ (cubeSet n) := by
  intro x hx y hy a b ha hb hab
  change (a • x + b • y) ∈ cubeSet n
  simp [cubeSet]
  intro i
  have hxi : x i ∈ Set.Icc (0 : ℝ) 1 := hx i
  have hyi : y i ∈ Set.Icc (0 : ℝ) 1 := hy i
  have hconvex : a • (x i) + b • (y i) ∈ Set.Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hxi hyi ha hb hab
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hconvex

theorem cubeSet_closed (n : ℕ) : IsClosed (cubeSet n) := by
  rw [show cubeSet n = ⋂ i : Fin n, {x : E n | x i ∈ Set.Icc (0 : ℝ) 1} by
    ext x; simp [cubeSet]]
  exact isClosed_iInter (fun i =>
    IsClosed.preimage (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) i)
      (isClosed_Icc (a := (0 : ℝ)) (b := 1)))

/-- Every point of the unit cube has norm at most `n + 1`. -/
lemma coord_norm_le (n : ℕ) (x : E n) (hx : ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1) :
    ‖x‖ ≤ (n : ℝ) + 1 := by
  have hsq : ‖x‖ ^ 2 ≤ (n : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      (∑ i : Fin n, ‖x i‖ ^ 2) ≤ ∑ i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have habs : |x i| ≤ 1 := abs_le.mpr ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
        have hle2 : (x i) ^ 2 ≤ 1 := by
          simpa using (sq_le_sq.mpr (by simpa : |x i| ≤ |(1 : ℝ)|))
        simpa [Real.norm_eq_abs, sq_abs] using hle2
      _ = (n : ℝ) := by simp
  have hsqrt : ‖x‖ ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (norm_nonneg x) (Nat.cast_nonneg n)]
    exact hsq
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg ((n : ℝ) - 1)]
  linarith

theorem cubeSet_bounded (n : ℕ) : Bornology.IsBounded (cubeSet n) := by
  refine Metric.isBounded_iff.mpr ⟨2 * ((n : ℝ) + 1), ?_⟩
  intro x hx y hy
  have hxle := coord_norm_le n x hx
  have hyle := coord_norm_le n y hy
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 * ((n : ℝ) + 1) := by linarith

theorem cubeSet_nonempty (n : ℕ) : (cubeSet n).Nonempty := by
  refine ⟨0, ?_⟩
  simp [cubeSet]

/-- The cube as a convex body. -/
def cubeBody (n : ℕ) : ConvexBody (E n) :=
  ⟨cubeSet n, cubeSet_convex n,
    (Metric.isCompact_iff_isClosed_bounded.mpr ⟨cubeSet_closed n, cubeSet_bounded n⟩),
    cubeSet_nonempty n⟩
@[simp] theorem cubeBody_coe (n : ℕ) : (cubeBody n : Set (E n)) = cubeSet n := rfl

/-! ## Translation and negation of a body -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The translate of a convex body by a vector (`t + x` picture; equal as sets
to the right-translation picture by commutativity). -/
def bodyTranslate (K : ConvexBody V) (t : V) : ConvexBody V :=
  ⟨(fun x : V => t + x) '' (K : Set V), K.convex.translate t,
    K.isCompact.image (continuous_const.add continuous_id),
    K.nonempty.image (fun x : V => t + x)⟩

@[simp] theorem bodyTranslate_coe_left (K : ConvexBody V) (t : V) :
    (bodyTranslate K t : Set V) = (fun x : V => t + x) '' (K : Set V) := rfl

@[simp] theorem bodyTranslate_coe_right (K : ConvexBody V) (t : V) :
    (bodyTranslate K t : Set V) = (fun x : V => x + t) '' (K : Set V) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, add_comm y t⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨y, hy, by simpa [add_comm] using hx⟩

@[simp] theorem bodyTranslate_zero (K : ConvexBody V) : bodyTranslate K 0 = K := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    simpa [← hxy] using hy
  · intro hx
    refine ⟨x, hx, by simp⟩

@[simp] theorem bodyTranslate_add (K : ConvexBody V) (s t : V) :
    bodyTranslate (bodyTranslate K s) t = bodyTranslate K (t + s) := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    abel
  · rintro ⟨z, hz, rfl⟩
    refine ⟨s + z, ⟨z, hz, rfl⟩, ?_⟩
    abel

/-- Image of a convex body under negation. -/
def bodyNeg (K : ConvexBody V) : ConvexBody V :=
  ⟨-(K : Set V), K.convex.neg,
    by
      rw [show -(K : Set V) = (fun x : V => -x) '' (K : Set V) by ext x; simp]
      exact K.isCompact.image continuous_neg,
    by
      rw [show -(K : Set V) = (fun x : V => -x) '' (K : Set V) by ext x; simp]
      exact K.nonempty.image (fun x : V => -x)⟩

@[simp] theorem bodyNeg_coe (K : ConvexBody V) : (bodyNeg K : Set V) = -(K : Set V) := rfl

@[simp] theorem bodyNeg_bodyNeg (K : ConvexBody V) : bodyNeg (bodyNeg K) = K := by
  apply ConvexBody.ext
  ext x
  simp

/-! ## Cylinders over the coordinate hyperplane -/

/-- Cylinder set over `K` between heights `a` and `b`. -/
def cylSet (n : ℕ) (K : ConvexBody (E n)) (a b : ℝ) : Set (E (n + 1)) :=
  {y | dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y ∈ Set.Icc a b}

theorem mem_cylSet {n : ℕ} {K : ConvexBody (E n)} {a b : ℝ} {y : E (n + 1)} :
    y ∈ cylSet n K a b ↔ dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y ∈ Set.Icc a b := by rfl

def dropLastL (n : ℕ) : E (n + 1) →ₗ[ℝ] E n :=
  { toFun := dropLast n, map_add' := dropLast_add n, map_smul' := dropLast_smul n }
def lastCoordL (n : ℕ) : E (n + 1) →ₗ[ℝ] ℝ :=
  { toFun := lastCoord n, map_add' := lastCoord_add n, map_smul' := lastCoord_smul n }
lemma dropLast_continuous (n : ℕ) : Continuous (dropLast n) := by
  exact LinearMap.continuous_of_finiteDimensional (dropLastL n)
lemma lastCoord_continuous (n : ℕ) : Continuous (lastCoord n) := by
  exact LinearMap.continuous_of_finiteDimensional (lastCoordL n)

theorem cylSet_convex (n : ℕ) (K : ConvexBody (E n)) (a b : ℝ) : Convex ℝ (cylSet n K a b) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ c d hc hd hcd
  constructor
  · have hcon := K.convex hx1 hy1 hc hd hcd
    simpa using hcon
  · have hcon := (convex_Icc a b) hx2 hy2 hc hd hcd
    simpa using hcon

theorem cylSet_closed (n : ℕ) (K : ConvexBody (E n)) (a b : ℝ) : IsClosed (cylSet n K a b) := by
  rw [show cylSet n K a b =
      (dropLast n ⁻¹' (K : Set (E n))) ∩ (lastCoord n ⁻¹' (Set.Icc a b)) by
    ext y; simp [cylSet]]
  exact (IsClosed.preimage (dropLast_continuous n) (IsCompact.isClosed K.isCompact)).inter
    (IsClosed.preimage (lastCoord_continuous n) (isClosed_Icc (a := a) (b := b)))

lemma abs_mem_Icc_le_max (a b t : ℝ) (ht : t ∈ Set.Icc a b) : |t| ≤ max |a| |b| := by
  have h1 : t ≤ b := ht.2
  have h2 : a ≤ t := ht.1
  have hb' : t ≤ max |a| |b| := by
    have hb1 : b ≤ |b| := le_abs_self b
    linarith [le_max_right |a| |b|, hb1]
  have ha' : -max |a| |b| ≤ t := by
    have hm : |a| ≤ max |a| |b| := le_max_left |a| |b|
    have hneg1 : -max |a| |b| ≤ -|a| := by linarith
    have hneg2 : -|a| ≤ a := by
      have := neg_le_abs a
      linarith
    linarith
  exact abs_le.mpr ⟨ha', hb'⟩

theorem cyl0_bounded (n : ℕ) (K : ConvexBody (E n)) (h : ℝ) (hh : 0 ≤ h) :
    Bornology.IsBounded (cylSet n K 0 h) := by
  rcases (Metric.isBounded_iff_subset_closedBall (0 : E n)).mp K.isCompact.isBounded with ⟨C, hC⟩
  refine (Metric.isBounded_iff_subset_closedBall (0 : E (n + 1))).mpr ⟨C + h, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall]
  simp
  have hy1 : dropLast n y ∈ (K : Set (E n)) := hy.1
  have hy2 : lastCoord n y ∈ Set.Icc 0 h := hy.2
  have hC' : ‖dropLast n y‖ ≤ C := by
    have := hC hy1
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hh' : |lastCoord n y| ≤ h := by
    have hnonneg : 0 ≤ lastCoord n y := hy2.1
    rw [abs_of_nonneg hnonneg]
    exact hy2.2
  calc
    ‖y‖ = ‖emb n (dropLast n y) + lastCoord n y • eLast n‖ := by
      congr 1
      exact (emb_dropLast_add_last n y).symm
    _ ≤ ‖emb n (dropLast n y)‖ + ‖lastCoord n y • eLast n‖ := norm_add_le _ _
    _ ≤ C + h := by
      have h1 : ‖emb n (dropLast n y)‖ ≤ C := by
        simpa [norm_emb] using hC'
      have h2 : ‖lastCoord n y • eLast n‖ ≤ h := by
        rw [norm_smul, Real.norm_eq_abs, norm_eLast]
        simpa using hh'
      linarith

theorem cylSet_nonempty (n : ℕ) (K : ConvexBody (E n)) (a b : ℝ) (hab : a ≤ b) :
    (cylSet n K a b).Nonempty := by
  rcases K.nonempty with ⟨x, hx⟩
  refine ⟨emb n x + a • eLast n, ?_⟩
  constructor
  · have hd : dropLast n (emb n x + a • eLast n) = x := by
      rw [dropLast_add, dropLast_smul, dropLast_emb, dropLast_eLast]
      simp
    simpa [hd] using hx
  · have ht : lastCoord n (emb n x + a • eLast n) = a := by
      rw [lastCoord_add, lastCoord_smul, lastCoord_emb, lastCoord_eLast]
      ring
    rw [ht]
    exact left_mem_Icc.mpr hab

/-- The cylinder of height `h ≥ 0` over `K` (base in the hyperplane, height along the
last coordinate axis). -/
def cyl0 (n : ℕ) (K : ConvexBody (E n)) (h : ℝ) (hh : 0 ≤ h) : ConvexBody (E (n + 1)) :=
  ⟨cylSet n K 0 h, cylSet_convex n K 0 h,
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨cylSet_closed n K 0 h, cyl0_bounded n K h hh⟩,
    cylSet_nonempty n K 0 h (by linarith)⟩

@[simp] theorem cyl0_coe (n : ℕ) (K : ConvexBody (E n)) (h : ℝ) (hh : 0 ≤ h) :
    (cyl0 n K h hh : Set (E (n + 1))) = cylSet n K 0 h := rfl

/-- If the base has empty interior then the cylinder has empty interior. -/
theorem interior_cyl0_eq_empty (n : ℕ) (K : ConvexBody (E n)) (h : ℝ) (hh : 0 ≤ h)
    (hK : interior (K : Set (E n)) = ∅) :
    interior ((cyl0 n K h hh : ConvexBody (E (n + 1))) : Set (E (n + 1))) = ∅ := by
  rw [cyl0_coe]
  by_contra hne
  have hne' : (interior (cylSet n K 0 h : Set (E (n + 1)))).Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hne
  rcases hne' with ⟨x, hx⟩
  have hxnhds : cylSet n K 0 h ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  rcases Metric.nhds_basis_ball.mem_iff.mp hxnhds with ⟨ε, hε, hball⟩
  have hmem : dropLast n x ∈ interior (K : Set (E n)) := by
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (dropLast n x) hε)
    intro w hw
    let v : E n := w - dropLast n x
    have hv : ‖v‖ < ε := by
      simpa [v, dist_eq_norm] using (Metric.mem_ball.mp hw)
    have hxv : x + emb n v ∈ cylSet n K 0 h := hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm : ‖(x + emb n v) - x‖ = ‖emb n v‖ := by
        have : (x + emb n v) - x = emb n v := by abel
        rw [this]
      rwa [hnorm, norm_emb])
    have hd : dropLast n (x + emb n v) = w := by
      simp [v]
    simpa [hd] using hxv.1
  have hmem' : dropLast n x ∈ (∅ : Set (E n)) := by simpa [hK] using hmem
  exact hmem'.elim

/-- Cylinder of a union. -/
theorem cyl0_union_set (n : ℕ) {A C D : ConvexBody (E n)}
    (hU : (A : Set (E n)) = (C : Set (E n)) ∪ (D : Set (E n))) :
    ((cyl0 n A 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) =
      ((cyl0 n C 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) ∪
      ((cyl0 n D 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) := by
  ext y
  rw [cyl0_coe, cyl0_coe, cyl0_coe]
  change (dropLast n y ∈ (A : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) 1) ↔
    ((dropLast n y ∈ (C : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) 1) ∨
     (dropLast n y ∈ (D : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) 1))
  rw [hU]
  simp [Set.mem_union]
  tauto

/-- Cylinder of an intersection. -/
theorem cyl0_inter_set (n : ℕ) {A B C D : ConvexBody (E n)}
    (hU : (A : Set (E n)) = (C : Set (E n)) ∪ (D : Set (E n)))
    (hI : (B : Set (E n)) = (C : Set (E n)) ∩ (D : Set (E n))) :
    ((cyl0 n B 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) =
      ((cyl0 n C 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) ∩
      ((cyl0 n D 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) := by
  ext y
  rw [cyl0_coe, cyl0_coe, cyl0_coe]
  change (dropLast n y ∈ (B : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) 1) ↔
    ((dropLast n y ∈ (C : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) 1) ∧
     (dropLast n y ∈ (D : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) 1))
  rw [hI]
  simp [Set.mem_inter]
  tauto

/-- The cylinder over a translate is the translate of the cylinder. -/
theorem cyl0_bodyTranslate_set (n : ℕ) (K : ConvexBody (E n)) (t : E n) :
    ((cyl0 n (bodyTranslate K t) 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) =
      (fun y : E (n + 1) => y + emb n t) ''
        ((cyl0 n K 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) := by
  ext y
  rw [cyl0_coe, cyl0_coe, mem_cylSet]
  rw [bodyTranslate_coe_left]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with ⟨x0, hx0, hx0eq⟩
    refine ⟨y - emb n t, ?_, ?_⟩
    · rw [mem_cylSet]
      constructor
      · have hd : dropLast n (y - emb n t) = x0 := by
          calc
            dropLast n (y - emb n t) = dropLast n y - t := by
              rw [sub_eq_add_neg]
              simp
              rfl
            _ = (t + x0) - t := by rw [hx0eq.symm]
            _ = x0 := by abel
        rw [hd]
        exact hx0
      · have hl : lastCoord n (y - emb n t) = lastCoord n y := by
          simp [sub_eq_add_neg]
        rw [hl]
        exact h2
    · abel
  · rintro ⟨z, hz, rfl⟩
    rw [mem_cylSet] at hz
    constructor
    · refine ⟨dropLast n z, hz.1, ?_⟩
      rw [dropLast_add, dropLast_emb, add_comm]
    · have hl : lastCoord n (z + emb n t) = lastCoord n z := by
        simp
      rw [hl]
      exact hz.2

/-- A valuation (w.r.t. the quadruple additivity clause) takes equal values on
bodies with the same underlying set. -/
theorem val_eq_of_set_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    {A B : ConvexBody V} (hAB : (A : Set V) = (B : Set V)) : φ A = φ B := by
  have hU : (A : Set V) = (A : Set V) ∪ (A : Set V) := by ext x; simp
  have hI : (B : Set V) = (A : Set V) ∩ (A : Set V) := by
    rw [hAB]
    ext x; simp
  have h := hadd A B A A hU hI
  linarith

/-- Cylinder over the cube is the cube of the next dimension. -/
theorem cyl0_cubeBody_eq (n : ℕ) :
    ((cyl0 n (cubeBody n) 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) =
      cubeSet (n + 1) := by
  ext y
  rw [cyl0_coe]
  simp [mem_cylSet, cubeBody_coe, cubeSet]
  constructor
  · rintro ⟨hyK, hyLast⟩
    intro i
    by_cases h : i = Fin.last n
    · rw [h]
      have : y (Fin.last n) = lastCoord n y := rfl
      rw [this]
      exact hyLast
    · have hlt := Fin.val_lt_last h
      have hi : i = Fin.castSucc (Fin.castLT i hlt) := by ext; simp [Fin.castLT]
      have hyj : y i = (dropLast n y) (Fin.castLT i hlt) := by
        nth_rewrite 1 [hi]
        rfl
      rw [hyj]
      exact hyK (Fin.castLT i hlt)
  · intro hy
    constructor
    · intro j
      have hyj : (dropLast n y) j = y (Fin.castSucc j) := by rfl
      rw [hyj]
      exact hy (Fin.castSucc j)
    · have hyLast : y (Fin.last n) = lastCoord n y := rfl
      rw [← hyLast]
      exact hy (Fin.last n)

/-- Membership in a negated set. -/
theorem mem_neg_iff {V : Type*} [Neg V] (s : Set V) (x : V) : x ∈ -s ↔ -x ∈ s := by
  simp

/-- A valuation sends a body and its negation to equal values. -/
theorem val_bodyNeg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : ConvexBody V → ℝ)
    (heven : ∀ A B : ConvexBody V, (B : Set V) = -(A : Set V) → φ A = φ B)
    (X : ConvexBody V) : φ (bodyNeg X) = φ X := by
  exact (heven X (bodyNeg X) (bodyNeg_coe X)).symm

/-- A valuation is invariant under translation of a body. -/
theorem val_bodyTranslate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : ConvexBody V → ℝ)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → φ A = φ B)
    (X : ConvexBody V) (t : V) : φ (bodyTranslate X t) = φ X := by
  exact (htrans X (bodyTranslate X t) t (bodyTranslate_coe_right X t)).symm


/-- Membership form of the cylinder-negation identity: the negation of the cylinder
over `-K` is a translate of the cylinder over `K`. -/
theorem neg_cyl0_bodyNeg_mem (n : ℕ) (K : ConvexBody (E n)) (y : E (n + 1)) :
    (y ∈ -((cyl0 n (bodyNeg K) 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1)))) ↔
      y ∈ (bodyTranslate (cyl0 n K 1 (by norm_num)) (-eLast n) : Set (E (n + 1))) := by
  rw [bodyTranslate_coe_left]
  rw [mem_neg_iff]
  rw [cyl0_coe, mem_cylSet]
  rw [bodyNeg_coe, mem_neg_iff]
  constructor
  · rintro ⟨hK, hLast⟩
    refine ⟨eLast n + y, ?_, ?_⟩
    · rw [cyl0_coe, mem_cylSet]
      constructor
      · have hd : dropLast n (eLast n + y) = -dropLast n (-y) := by simp
        rw [hd]
        exact hK
      · have hl : lastCoord n (eLast n + y) = 1 + lastCoord n y := by
          rw [lastCoord_add, lastCoord_eLast]
        rw [hl]
        rw [Set.mem_Icc]
        have hLast' : 0 ≤ -lastCoord n y ∧ -lastCoord n y ≤ 1 := by simpa using hLast
        constructor <;> linarith [hLast'.1, hLast'.2]
    · abel
  · rintro ⟨w0, hw0, hw0eq⟩
    have hw0eq' : y = (-eLast n) + w0 := by simpa using hw0eq.symm
    rw [cyl0_coe, mem_cylSet] at hw0
    constructor
    · have hd : dropLast n y = dropLast n w0 := by
        rw [hw0eq']
        simp
      have hmain : -dropLast n (-y) = dropLast n w0 := by
        calc -dropLast n (-y) = dropLast n y := by simp
             _ = dropLast n w0 := hd
      rw [hmain]
      exact hw0.1
    · have hl : lastCoord n y = lastCoord n w0 - 1 := by
        rw [hw0eq']
        rw [lastCoord_add, lastCoord_neg, lastCoord_eLast]
        ring
      have htarget : lastCoord n (-y) = 1 - lastCoord n w0 := by
        calc lastCoord n (-y) = -lastCoord n y := by simp
             _ = 1 - lastCoord n w0 := by rw [hl]; ring
      rw [Set.mem_Icc]
      rw [htarget]
      constructor <;> linarith [hw0.2.1, hw0.2.2]

/-- Negating the cylinder over `-K` gives a translate of the cylinder over `K`. -/
theorem neg_cyl0_bodyNeg_eq (n : ℕ) (K : ConvexBody (E n)) :
    -((cyl0 n (bodyNeg K) 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) =
      (bodyTranslate (cyl0 n K 1 (by norm_num)) (-eLast n) : Set (E (n + 1))) := by
  ext y
  exact neg_cyl0_bodyNeg_mem n K y


/-- `emb` preserves negation. -/
@[simp] theorem emb_neg (n : ℕ) (x : E n) : emb n (-x) = - emb n x := by
  ext i
  dsimp [emb]
  by_cases h : i = Fin.last n <;> simp [h]

/-- `emb` is additive for differences. -/
theorem emb_sub (n : ℕ) (x y : E n) : emb n (x - y) = emb n x - emb n y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, emb_add, emb_neg]

/-- For any point of a cylinder over `K` there is a point of the cylinder over `L`
no further away than `dist K L`. -/
private lemma cyl0_hausdorff_aux (n : ℕ) (K L : ConvexBody (E n)) (y : E (n + 1))
    (hy : y ∈ (cyl0 n K 1 (by norm_num) : Set (E (n + 1)))) :
    ∃ z ∈ (cyl0 n L 1 (by norm_num) : Set (E (n + 1))), dist y z ≤ dist K L := by
  rw [cyl0_coe, mem_cylSet] at hy
  rcases L.isCompact.exists_infDist_eq_dist L.nonempty (dropLast n y) with ⟨y0, hy0L, hy0dist⟩
  have hinf : Metric.infDist (dropLast n y) (L : Set (E n)) ≤ dist K L := by
    have h := Metric.infDist_le_hausdorffDist_of_mem (s := (K : Set (E n))) (t := (L : Set (E n)))
      (x := dropLast n y) hy.1 (ConvexBody.hausdorffEDist_ne_top (K := K) (L := L))
    rw [ConvexBody.hausdorffDist_coe] at h
    exact h
  have hdy : dist (dropLast n y) y0 ≤ dist K L := by
    rw [← hy0dist]
    exact hinf
  refine ⟨emb n y0 + lastCoord n y • eLast n, ?_, ?_⟩
  · rw [cyl0_coe, mem_cylSet]
    constructor
    · have hd : dropLast n (emb n y0 + lastCoord n y • eLast n) = y0 := by simp
      rw [hd]
      exact hy0L
    · have hl : lastCoord n (emb n y0 + lastCoord n y • eLast n) = lastCoord n y := by simp
      rw [hl]
      exact hy.2
  · have hvec : y - (emb n y0 + lastCoord n y • eLast n) = emb n (dropLast n y - y0) := by
      calc
        y - (emb n y0 + lastCoord n y • eLast n)
            = emb n (dropLast n y) + lastCoord n y • eLast n
                - (emb n y0 + lastCoord n y • eLast n) := by
                rw [emb_dropLast_add_last n y]
        _ = emb n (dropLast n y) - emb n y0 := by abel
        _ = emb n (dropLast n y - y0) := (emb_sub n (dropLast n y) y0).symm
    rw [dist_eq_norm]
    rw [hvec]
    calc
      ‖emb n (dropLast n y - y0)‖ = ‖dropLast n y - y0‖ := by simp
      _ = dist (dropLast n y) y0 := by rw [dist_eq_norm]
      _ ≤ dist K L := hdy

/-- Hausdorff distance between unit cylinders is bounded by the base distance. -/
private lemma cyl0_hausdorff_le (n : ℕ) (K L : ConvexBody (E n)) :
    Metric.hausdorffDist ((cyl0 n K 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1)))
      ((cyl0 n L 1 (by norm_num) : ConvexBody (E (n + 1))) : Set (E (n + 1))) ≤ dist K L := by
  refine Metric.hausdorffDist_le_of_mem_dist dist_nonneg ?_ ?_
  · intro y hy
    exact cyl0_hausdorff_aux n K L y hy
  · intro y hy
    rcases cyl0_hausdorff_aux n L K y hy with ⟨z, hz, hle⟩
    exact ⟨z, hz, by simpa [dist_comm] using hle⟩

/-- The cylinder map is 1-Lipschitz in its base. -/
theorem cyl0_lipschitz (n : ℕ) (K L : ConvexBody (E n)) :
    dist (cyl0 n K 1 (by norm_num)) (cyl0 n L 1 (by norm_num)) ≤ dist K L := by
  rw [← ConvexBody.hausdorffDist_coe]
  exact cyl0_hausdorff_le n K L

/-- The map sending a convex body to its unit cylinder is continuous. -/
theorem continuous_cyl0_one (n : ℕ) :
    Continuous (fun K : ConvexBody (E n) => cyl0 n K 1 (by norm_num)) := by
  rw [Metric.continuous_iff]
  intro K ε hε
  refine ⟨ε, hε, ?_⟩
  intro L hL
  have hle := cyl0_lipschitz n L K
  exact lt_of_le_of_lt hle (by simpa [dist_comm] using hL)


/-! ## Height slices and binary splits for cylinders -/

/-- The horizontal slice of the cylinder at height `c`. -/
def cylSliceSet (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) : Set (E (n + 1)) :=
  {y | dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y = c}

theorem cylSliceSet_convex (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) :
    Convex ℝ (cylSliceSet n K c) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  constructor
  · have hc := K.convex hx1 hy1 ha hb hab
    simpa using hc
  · have hlc : lastCoord n (a • x + b • y) = a * lastCoord n x + b * lastCoord n y := by
      simp
    rw [hlc, hx2, hy2]
    calc
      a * c + b * c = (a + b) * c := by ring
      _ = c := by rw [hab]; ring

theorem cylSliceSet_closed (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) :
    IsClosed (cylSliceSet n K c) := by
  rw [show cylSliceSet n K c =
      (dropLast n ⁻¹' (K : Set (E n))) ∩ (lastCoord n ⁻¹' ({c} : Set ℝ)) by
    ext y; simp [cylSliceSet]]
  exact (IsClosed.preimage (dropLast_continuous n) (IsCompact.isClosed K.isCompact)).inter
    (IsClosed.preimage (lastCoord_continuous n) (isClosed_singleton))

theorem cylSliceSet_bounded (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) :
    Bornology.IsBounded (cylSliceSet n K c) := by
  rcases (Metric.isBounded_iff_subset_closedBall (0 : E n)).mp K.isCompact.isBounded with ⟨C, hC⟩
  refine (Metric.isBounded_iff_subset_closedBall (0 : E (n + 1))).mpr ⟨C + |c|, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall]
  simp
  have hy1 : dropLast n y ∈ (K : Set (E n)) := hy.1
  have hy2 : lastCoord n y = c := hy.2
  have hC' : ‖dropLast n y‖ ≤ C := by
    have := hC hy1
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  calc
    ‖y‖ = ‖emb n (dropLast n y) + lastCoord n y • eLast n‖ := by
      congr 1
      exact (emb_dropLast_add_last n y).symm
    _ ≤ ‖emb n (dropLast n y)‖ + ‖lastCoord n y • eLast n‖ := norm_add_le _ _
    _ ≤ C + |c| := by
      have h1 : ‖emb n (dropLast n y)‖ ≤ C := by
        simpa [norm_emb] using hC'
      have h2 : ‖lastCoord n y • eLast n‖ ≤ |c| := by
        rw [hy2, norm_smul, Real.norm_eq_abs, norm_eLast]
        simp
      linarith

theorem cylSliceSet_nonempty (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) :
    (cylSliceSet n K c).Nonempty := by
  rcases K.nonempty with ⟨x0, hx0⟩
  refine ⟨emb n x0 + c • eLast n, ?_⟩
  constructor
  · have hd : dropLast n (emb n x0 + c • eLast n) = x0 := by simp
    simpa [hd] using hx0
  · have hl : lastCoord n (emb n x0 + c • eLast n) = c := by
      simp
    exact hl

/-- The horizontal slice of the cylinder at height `c`, as a convex body. -/
def cylSlice (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) : ConvexBody (E (n + 1)) :=
  ⟨cylSliceSet n K c, cylSliceSet_convex n K c,
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨cylSliceSet_closed n K c, cylSliceSet_bounded n K c⟩,
    cylSliceSet_nonempty n K c⟩

@[simp] theorem cylSlice_coe (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) :
    (cylSlice n K c : Set (E (n + 1))) = cylSliceSet n K c := rfl

/-- A horizontal slice of a cylinder has empty interior. -/
theorem interior_cylSlice_eq_empty (n : ℕ) (K : ConvexBody (E n)) (c : ℝ) :
    interior ((cylSlice n K c : ConvexBody (E (n + 1))) : Set (E (n + 1))) = ∅ := by
  rw [cylSlice_coe]
  by_contra hne
  have hne' : (interior (cylSliceSet n K c : Set (E (n + 1)))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  rcases hne' with ⟨x, hx⟩
  have hxset : x ∈ cylSliceSet n K c := interior_subset hx
  have hxnhds : cylSliceSet n K c ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  rcases Metric.nhds_basis_ball.mem_iff.mp hxnhds with ⟨ε, hε, hball⟩
  let δ : ℝ := ε / 2
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδlt : δ < ε := by dsimp [δ]; linarith
  have hmem : x + δ • eLast n ∈ cylSliceSet n K c := hball (by
    rw [Metric.mem_ball]
    have : dist (x + δ • eLast n) x = δ := by
      rw [dist_eq_norm]
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδ0)]
    rw [this]
    exact hδlt)
  have hlast : lastCoord n (x + δ • eLast n) = c + δ := by
    rw [lastCoord_add, lastCoord_smul, lastCoord_eLast]
    have hxlast : lastCoord n x = c := hxset.2
    rw [hxlast]
    ring
  have hc' : lastCoord n (x + δ • eLast n) = c := hmem.2
  linarith

/-! ## Transport of bodies along linear isometries (frames / orientations) -/

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The image of a convex body under a linear isometry equivalence. -/
def bodyIsometry (e : U ≃ₗᵢ[ℝ] V) (K : ConvexBody U) : ConvexBody V :=
  ⟨e '' (K : Set U), by
    have h := K.convex.linear_image (e : U →ₗ[ℝ] V)
    simpa using h,
    K.isCompact.image e.continuous,
    K.nonempty.image (fun x : U => e x)⟩

@[simp] theorem bodyIsometry_coe (e : U ≃ₗᵢ[ℝ] V) (K : ConvexBody U) :
    (bodyIsometry e K : Set V) = e '' (K : Set U) := rfl

@[simp] theorem bodyIsometry_refl (K : ConvexBody U) :
    bodyIsometry (LinearIsometryEquiv.refl ℝ U) K = K := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp

@[simp] theorem bodyIsometry_trans (e : U ≃ₗᵢ[ℝ] V) (K : ConvexBody U) :
    bodyIsometry e K = e '' (K : Set U) := by
  -- already via coe
  rfl

@[simp] theorem bodyIsometry_comp {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : U ≃ₗᵢ[ℝ] V) (f : V ≃ₗᵢ[ℝ] W) (K : ConvexBody U) :
    bodyIsometry f (bodyIsometry e K) = bodyIsometry (e.trans f) K := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨z, hz, ?_⟩
    rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e z, ?_, ?_⟩
    · refine ⟨z, hz, rfl⟩
    · rfl

/-- `bodyIsometry e` preserves distances between convex bodies. -/
theorem dist_bodyIsometry (e : U ≃ₗᵢ[ℝ] V) (K L : ConvexBody U) :
    dist (bodyIsometry e K) (bodyIsometry e L) = dist K L := by
  rw [← ConvexBody.hausdorffDist_coe (K := bodyIsometry e K) (L := bodyIsometry e L)]
  rw [bodyIsometry_coe, bodyIsometry_coe]
  rw [Metric.hausdorffDist_image (LinearIsometryEquiv.isometry e)]
  exact ConvexBody.hausdorffDist_coe K L

/-- `bodyIsometry e` is continuous. -/
theorem continuous_bodyIsometry (e : U ≃ₗᵢ[ℝ] V) :
    Continuous (fun K : ConvexBody U => bodyIsometry e K) := by
  rw [Metric.continuous_iff]
  intro K ε hε
  refine ⟨ε, hε, ?_⟩
  intro L hL
  rw [dist_bodyIsometry e L K]
  exact hL

/-- The image of the coordinate cube under an isometry that preserves the cube set
as a whole is the cube (used e.g. for coordinate reflections / permutations). -/
theorem bodyIsometry_cube_of_set_eq (m : ℕ) (e : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
    (he : e '' (cubeSet (m + 1)) = cubeSet (m + 1)) :
    bodyIsometry e (cubeBody (m + 1)) = cubeBody (m + 1) := by
  apply ConvexBody.ext
  rw [bodyIsometry_coe, cubeBody_coe]
  exact he

/-- The same cube-preservation fact in any dimension. -/
theorem bodyIsometry_cube_of_set_eq_any (n : ℕ) (e : E n ≃ₗᵢ[ℝ] E n)
    (he : e '' (cubeSet n) = cubeSet n) :
    bodyIsometry e (cubeBody n) = cubeBody n := by
  apply ConvexBody.ext
  rw [bodyIsometry_coe, cubeBody_coe]
  exact he

/-- Cube-preserving isometries (e.g. coordinate permutations) do not change the
value of the (unoriented) cube. -/
theorem mu_rotatedCube_eq_axis_of_cube_preserving (n : ℕ) (μ : ConvexBody (E n) → ℝ)
    (ρ : E n ≃ₗᵢ[ℝ] E n) (hpres : ρ '' (cubeSet n) = cubeSet n) :
    μ (bodyIsometry ρ (cubeBody n)) = μ (cubeBody n) := by
  have hb : bodyIsometry ρ (cubeBody n) = cubeBody n :=
    bodyIsometry_cube_of_set_eq_any n ρ hpres
  rw [hb]

/-- Membership in a height-`h` cylinder: coordinates of the last direction lie in
`[0, h]`. -/
theorem mem_cyl0_coords {n : ℕ} {K : ConvexBody (E n)} {h : ℝ} {hh : 0 ≤ h}
    {y : E (n + 1)} :
    y ∈ ((cyl0 n K h hh : ConvexBody (E (n + 1))) : Set (E (n + 1))) ↔
      dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (0 : ℝ) h := by
  rw [cyl0_coe]
  rfl

/-- Membership in the cylinder of height `h/2` translated up by `h/2`: the last
coordinate lies in `[h/2, h]`. -/
theorem mem_cyl0_translate_half {n : ℕ} {K : ConvexBody (E n)} {h : ℝ} {hh2 : 0 ≤ h / 2}
    {y : E (n + 1)} :
    y ∈ ((bodyTranslate (cyl0 n K (h / 2) hh2) ((h / 2) • eLast n) :
        ConvexBody (E (n + 1))) : Set (E (n + 1))) ↔
      dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y ∈ Set.Icc (h / 2) h := by
  rw [bodyTranslate_coe_left]
  constructor
  · rintro ⟨z, hz, hzeq⟩
    have hzeq' : y = (h / 2) • eLast n + z := by simpa using hzeq.symm
    rw [cyl0_coe, mem_cylSet] at hz
    constructor
    · have hd : dropLast n y = dropLast n z := by rw [hzeq']; simp
      simpa [hd] using hz.1
    · have hl : lastCoord n y = h / 2 + lastCoord n z := by rw [hzeq']; simp
      rw [hl]
      rw [Set.mem_Icc]
      constructor
      · linarith [hz.2.1]
      · linarith [hz.2.2]
  · rintro ⟨hdrop, hlast⟩
    refine ⟨y - (h / 2) • eLast n, ?_, ?_⟩
    · rw [cyl0_coe, mem_cylSet]
      constructor
      · have hd : dropLast n (y - (h / 2) • eLast n) = dropLast n y := by
          rw [sub_eq_add_neg, dropLast_add, dropLast_neg, dropLast_smul, dropLast_eLast]
          simp
        simpa [hd] using hdrop
      · have hl : lastCoord n (y - (h / 2) • eLast n) = lastCoord n y - h / 2 := by
          rw [sub_eq_add_neg, lastCoord_add, lastCoord_neg, lastCoord_smul, lastCoord_eLast]
          ring
        rw [hl]
        rw [Set.mem_Icc]
        constructor
        · linarith [hlast.1]
        · linarith [hlast.2]
    · abel

/-- Membership in a cylinder of height `h - c` translated up by `c`: the last
coordinate lies in `[c, h]`. -/
theorem mem_cyl0_translate {n : ℕ} {K : ConvexBody (E n)} {h c : ℝ} {hhc : 0 ≤ h - c}
    {y : E (n + 1)} :
    y ∈ ((bodyTranslate (cyl0 n K (h - c) hhc) (c • eLast n) :
        ConvexBody (E (n + 1))) : Set (E (n + 1))) ↔
      dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y ∈ Set.Icc c h := by
  rw [bodyTranslate_coe_left]
  constructor
  · rintro ⟨z, hz, hzeq⟩
    have hzeq' : y = c • eLast n + z := by simpa using hzeq.symm
    rw [cyl0_coe, mem_cylSet] at hz
    constructor
    · have hd : dropLast n y = dropLast n z := by rw [hzeq']; simp
      simpa [hd] using hz.1
    · have hl : lastCoord n y = c + lastCoord n z := by rw [hzeq']; simp
      rw [hl]
      rw [Set.mem_Icc]
      constructor
      · linarith [hz.2.1]
      · linarith [hz.2.2]
  · rintro ⟨hdrop, hlast⟩
    refine ⟨y - c • eLast n, ?_, ?_⟩
    · rw [cyl0_coe, mem_cylSet]
      constructor
      · have hd : dropLast n (y - c • eLast n) = dropLast n y := by
          rw [sub_eq_add_neg, dropLast_add, dropLast_neg, dropLast_smul, dropLast_eLast]
          simp
        simpa [hd] using hdrop
      · have hl : lastCoord n (y - c • eLast n) = lastCoord n y - c := by
          rw [sub_eq_add_neg, lastCoord_add, lastCoord_neg, lastCoord_smul, lastCoord_eLast]
          ring
        rw [hl]
        rw [Set.mem_Icc]
        constructor
        · linarith [hlast.1]
        · linarith [hlast.2]
    · abel

/-- Cylinders with equal nonnegative heights are equal. -/
theorem cyl0_eq_of_height {n : ℕ} (K : ConvexBody (E n)) {h1 h2 : ℝ}
    (hh1 : 0 ≤ h1) (hh2 : 0 ≤ h2) (h : h1 = h2) :
    cyl0 n K h1 hh1 = cyl0 n K h2 hh2 := by
  apply ConvexBody.ext
  rw [cyl0_coe, cyl0_coe, h]

/-- The height function of a cylinder is additive under a cut at height `c`:
`[0,h] = [0,c] ∪ [c,h]`, with the upper part a translate of the `h-c` cylinder. -/
theorem mu_cyl0_split {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    (h : ℝ) (hh : 0 ≤ h) (c : ℝ) (hc : 0 ≤ c) (hch : c ≤ h) :
    μ (cyl0 n K h hh) =
      μ (cyl0 n K c hc) + μ (cyl0 n K (h - c) (sub_nonneg.mpr hch)) := by
  let A : ConvexBody (E (n + 1)) := cyl0 n K h hh
  let C : ConvexBody (E (n + 1)) := cyl0 n K c hc
  let D : ConvexBody (E (n + 1)) := bodyTranslate (cyl0 n K (h - c) (sub_nonneg.mpr hch)) (c • eLast n)
  let B : ConvexBody (E (n + 1)) := cylSlice n K c
  have hU : (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) := by
    ext y
    change y ∈ ((cyl0 n K h hh : ConvexBody (E (n + 1))) : Set (E (n + 1))) ↔
      y ∈ ((cyl0 n K c hc : ConvexBody (E (n + 1))) : Set (E (n + 1))) ∨
      y ∈ (bodyTranslate (cyl0 n K (h - c) (sub_nonneg.mpr hch)) (c • eLast n) : Set (E (n + 1)))
    rw [mem_cyl0_coords, mem_cyl0_coords, mem_cyl0_translate]
    constructor
    · rintro ⟨hdrop, hlast⟩
      have hlast0 : 0 ≤ lastCoord n y := (Set.mem_Icc.mp hlast).1
      have hlast1 : lastCoord n y ≤ h := (Set.mem_Icc.mp hlast).2
      by_cases hc' : lastCoord n y ≤ c
      · left
        constructor
        · exact hdrop
        · rw [Set.mem_Icc]
          constructor <;> linarith
      · right
        constructor
        · exact hdrop
        · rw [Set.mem_Icc]
          constructor
          · exact le_of_not_ge hc'
          · exact hlast1
    · rintro (⟨hdrop, hlast⟩ | ⟨hdrop, hlast⟩)
      · constructor
        · exact hdrop
        · rw [Set.mem_Icc]
          constructor
          · exact (Set.mem_Icc.mp hlast).1
          · linarith [hch, (Set.mem_Icc.mp hlast).2]
      · constructor
        · exact hdrop
        · rw [Set.mem_Icc]
          constructor
          · linarith [hc, (Set.mem_Icc.mp hlast).1]
          · exact (Set.mem_Icc.mp hlast).2
  have hI : (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) := by
    ext y
    change y ∈ ((cylSlice n K c : ConvexBody (E (n + 1))) : Set (E (n + 1))) ↔
      (y ∈ ((cyl0 n K c hc : ConvexBody (E (n + 1))) : Set (E (n + 1))) ∧
       y ∈ (bodyTranslate (cyl0 n K (h - c) (sub_nonneg.mpr hch)) (c • eLast n) : Set (E (n + 1))))
    rw [cylSlice_coe]
    change (dropLast n y ∈ (K : Set (E n)) ∧ lastCoord n y = c) ↔
      (y ∈ ((cyl0 n K c hc : ConvexBody (E (n + 1))) : Set (E (n + 1))) ∧
       y ∈ (bodyTranslate (cyl0 n K (h - c) (sub_nonneg.mpr hch)) (c • eLast n) : Set (E (n + 1))))
    rw [mem_cyl0_coords, mem_cyl0_translate]
    constructor
    · rintro ⟨hdrop, hlast⟩
      constructor
      · constructor
        · exact hdrop
        · rw [Set.mem_Icc]
          constructor <;> linarith [hc, hlast]
      · constructor
        · exact hdrop
        · rw [Set.mem_Icc]
          constructor
          · linarith [hlast]
          · linarith [hch, hlast]
    · rintro ⟨⟨hdropC, hlastC⟩, ⟨hdropD, hlastD⟩⟩
      constructor
      · exact hdropC
      · exact le_antisymm (Set.mem_Icc.mp hlastC).2 (Set.mem_Icc.mp hlastD).1
  have hBint : interior ((B : ConvexBody (E (n + 1))) : Set (E (n + 1))) = ∅ := by
    dsimp [B]
    exact interior_cylSlice_eq_empty n K c
  have hIE := hadd A B C D hU hI
  have hB0 : μ B = 0 := hsimple B hBint
  have hA : μ A = μ C + μ D := by linarith
  have hD : μ D = μ (cyl0 n K (h - c) (sub_nonneg.mpr hch)) := by
    dsimp [D]
    exact val_bodyTranslate μ htrans (cyl0 n K (h - c) (sub_nonneg.mpr hch)) (c • eLast n)
  dsimp [A, C, D] at hA
  rw [hA, hD]

/-- The half-height split is the special case `c = h/2` of `mu_cyl0_split`. -/
theorem mu_cyl0_half_from_split {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    (h : ℝ) (hh : 0 ≤ h) (hh2 : 0 ≤ h / 2) :
    μ (cyl0 n K h hh) =
      μ (cyl0 n K (h / 2) hh2) + μ (cyl0 n K (h / 2) hh2) := by
  have hhch : h / 2 ≤ h := by nlinarith [hh]
  have hs := mu_cyl0_split K μ hadd hsimple htrans h hh (h / 2) hh2 hhch
  -- hs : μ (cyl0 h) = μ (cyl0 (h/2)) + μ (cyl0 (h - h/2) (sub_nonneg.mpr hhch))
  have heq : cyl0 n K (h - h / 2) (sub_nonneg.mpr hhch) = cyl0 n K (h / 2) hh2 :=
    cyl0_eq_of_height K (sub_nonneg.mpr hhch) hh2 (by ring)
  rw [hs, heq]

/-- A zero-height cylinder is the horizontal slice at height zero. -/
theorem cyl0_zero_coe_eq_slice (n : ℕ) (K : ConvexBody (E n)) :
    ((cyl0 n K 0 (le_refl (0 : ℝ)) : ConvexBody (E (n + 1))) : Set (E (n + 1))) =
      (cylSlice n K 0 : Set (E (n + 1))) := by
  rw [cyl0_coe, cylSlice_coe]
  ext y
  constructor
  · rintro ⟨hdrop, hlast⟩
    constructor
    · exact hdrop
    · exact le_antisymm hlast.2 hlast.1
  · rintro ⟨hdrop, hlast⟩
    constructor
    · exact hdrop
    · rw [Set.mem_Icc]
      constructor <;> linarith [hlast]

/-- A zero-height cylinder has empty interior. -/
theorem interior_cyl0_zero_eq_empty (n : ℕ) (K : ConvexBody (E n)) :
    interior ((cyl0 n K 0 (le_refl (0 : ℝ)) : ConvexBody (E (n + 1))) : Set (E (n + 1))) = ∅ := by
  rw [cyl0_zero_coe_eq_slice]
  exact interior_cylSlice_eq_empty n K 0

/-- A simple valuation vanishes on zero-height cylinders. -/
theorem mu_cyl0_zero {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0) :
    μ (cyl0 n K 0 (le_refl (0 : ℝ))) = 0 :=
  hsimple (cyl0 n K 0 (le_refl (0 : ℝ))) (interior_cyl0_zero_eq_empty n K)

/-- Cylinder measure is additive in the height: `[0, c+s] = [0,c] ∪ [c, c+s]`. -/
theorem mu_cyl0_add {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) :
    μ (cyl0 n K (c + s) (add_nonneg hc hs)) =
      μ (cyl0 n K c hc) + μ (cyl0 n K s hs) := by
  have hcs : c ≤ c + s := by linarith
  have hsplit := mu_cyl0_split K μ hadd hsimple htrans (c + s) (add_nonneg hc hs) c hc hcs
  have heq : cyl0 n K (c + s - c) (sub_nonneg.mpr hcs) = cyl0 n K s hs :=
    cyl0_eq_of_height K (sub_nonneg.mpr hcs) hs (by ring)
  rw [hsplit, heq]

/-- Cylinder measure of `k`-fold heights scales linearly: `μ(cyl0 (k*t)) = k * μ(cyl0 t)`. -/
theorem mu_cyl0_nat_mul {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    (t : ℝ) (ht : 0 ≤ t) : ∀ k : ℕ,
    μ (cyl0 n K ((k : ℝ) * t) (mul_nonneg (Nat.cast_nonneg k) ht)) =
      (k : ℝ) * μ (cyl0 n K t ht) := by
  intro k
  induction k with
  | zero =>
      have hzt : ((0 : ℕ) : ℝ) * t = 0 := by norm_num
      have heq : cyl0 n K (((0 : ℕ) : ℝ) * t) (mul_nonneg (Nat.cast_nonneg 0) ht) =
          cyl0 n K 0 (le_refl (0 : ℝ)) := by
        apply ConvexBody.ext
        rw [cyl0_coe, cyl0_coe, hzt]
      rw [heq]
      rw [mu_cyl0_zero K μ hsimple]
      ring
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      have hprod : ((k + 1 : ℕ) : ℝ) * t = (k : ℝ) * t + t := by
        rw [hcast]
        ring
      have hk0 : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg k) ht
      have hadd := mu_cyl0_add K μ hadd hsimple htrans (c := (k : ℝ) * t) (s := t) hk0 ht
      have heq : cyl0 n K (((k + 1 : ℕ) : ℝ) * t) (mul_nonneg (Nat.cast_nonneg (k + 1)) ht) =
          cyl0 n K ((k : ℝ) * t + t) (add_nonneg hk0 ht) :=
        cyl0_eq_of_height K (mul_nonneg (Nat.cast_nonneg (k + 1)) ht) (add_nonneg hk0 ht) hprod
      calc
        μ (cyl0 n K (((k + 1 : ℕ) : ℝ) * t) (mul_nonneg (Nat.cast_nonneg (k + 1)) ht))
            = μ (cyl0 n K ((k : ℝ) * t + t) (add_nonneg hk0 ht)) := by rw [heq]
        _ = μ (cyl0 n K ((k : ℝ) * t) hk0) + μ (cyl0 n K t ht) := hadd
        _ = ((k + 1 : ℕ) : ℝ) * μ (cyl0 n K t ht) := by
              rw [ih]
              rw [hcast]
              ring

/-- If the unit cylinder vanishes then cylinders of unit-fraction heights vanish. -/
theorem mu_cyl0_unit_fraction {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    (h1 : μ (cyl0 n K 1 (by norm_num)) = 0)
    (k : ℕ) (hkpos : 0 < k) (hk0 : 0 ≤ (1 : ℝ) / k) :
    μ (cyl0 n K ((1 : ℝ) / k) hk0) = 0 := by
  have hrep := mu_cyl0_nat_mul K μ hadd hsimple htrans ((1 : ℝ) / k) hk0 k
  have hkmul : (k : ℝ) * ((1 : ℝ) / k) = 1 := by
    have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hkpos)
    field_simp [hkne]
  have hL : μ (cyl0 n K ((k : ℝ) * ((1 : ℝ) / k)) (mul_nonneg (Nat.cast_nonneg k) hk0)) = 0 := by
    have heq : cyl0 n K ((k : ℝ) * ((1 : ℝ) / k)) (mul_nonneg (Nat.cast_nonneg k) hk0) =
        cyl0 n K 1 (by norm_num) :=
      cyl0_eq_of_height K (mul_nonneg (Nat.cast_nonneg k) hk0) (by norm_num) hkmul
    rw [heq]
    exact h1
  have hmain : (k : ℝ) * μ (cyl0 n K ((1 : ℝ) / k) hk0) = 0 := by
    rw [← hrep]
    exact hL
  exact (mul_eq_zero.mp hmain).resolve_left (by exact_mod_cast (ne_of_gt hkpos))

/-- If the unit cylinder vanishes then cylinders of every rational height
`p / q` (`0 < q`) vanish. -/
theorem mu_cyl0_rational {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    (h1 : μ (cyl0 n K 1 (by norm_num)) = 0)
    (p q : ℕ) (hqpos : 0 < q) (hpq0 : 0 ≤ (p : ℝ) / q) :
    μ (cyl0 n K ((p : ℝ) / q) hpq0) = 0 := by
  have hq0 : 0 ≤ (1 : ℝ) / q :=
    div_nonneg (by norm_num) (le_of_lt (Nat.cast_pos.mpr hqpos))
  have hu := mu_cyl0_unit_fraction K μ hadd hsimple htrans h1 q hqpos hq0
  have hrep := mu_cyl0_nat_mul K μ hadd hsimple htrans ((1 : ℝ) / q) hq0 p
  have hpm : (p : ℝ) * ((1 : ℝ) / q) = (p : ℝ) / q := by
    have hkne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
    field_simp [hkne]
  have hEq : cyl0 n K ((p : ℝ) * ((1 : ℝ) / q)) (mul_nonneg (Nat.cast_nonneg p) hq0) =
      cyl0 n K ((p : ℝ) / q) hpq0 := by
    apply ConvexBody.ext
    rw [cyl0_coe, cyl0_coe, hpm]
  have hR : (p : ℝ) * μ (cyl0 n K ((1 : ℝ) / q) hq0) = 0 := by
    rw [hu]
    ring
  rw [hEq] at hrep
  rw [hrep]
  exact hR

/-- Clamping a real `t ∈ [0,h]` into `[0,h']` moves it by at most `|h - h'|`. -/
lemma abs_sub_clamp_le {t h h' : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h) (hh'0 : 0 ≤ h') :
    |t - min t h'| ≤ |h - h'| := by
  by_cases hle : t ≤ h'
  · have hmin : min t h' = t := min_eq_left hle
    rw [hmin]
    simp [abs_nonneg]
  · have hgt : h' < t := lt_of_not_ge hle
    have hmin : min t h' = h' := min_eq_right (le_of_lt hgt)
    rw [hmin]
    have hnonneg1 : 0 ≤ t - h' := by linarith
    have hnonneg2 : 0 ≤ h - h' := by linarith [hth]
    rw [abs_of_nonneg hnonneg1, abs_of_nonneg hnonneg2]
    linarith [hth]

/-- Hausdorff distance between two cylinders over the same base with heights
`h`, `h'` is at most `|h - h'|`. -/
lemma cyl0_hausdorff_heights {n : ℕ} (K : ConvexBody (E n)) {h h' : ℝ}
    (hh : 0 ≤ h) (hh' : 0 ≤ h') :
    Metric.hausdorffDist ((cyl0 n K h hh : ConvexBody (E (n + 1))) : Set (E (n + 1)))
      ((cyl0 n K h' hh' : ConvexBody (E (n + 1))) : Set (E (n + 1))) ≤ |h - h'| := by
  refine Metric.hausdorffDist_le_of_mem_dist (abs_nonneg (h - h')) ?H1 ?H2
  · intro y hy
    rw [cyl0_coe, mem_cylSet] at hy
    let t : ℝ := min (lastCoord n y) h'
    have ht0 : 0 ≤ t := by
      exact le_min hy.2.1 hh'
    have hth' : t ≤ h' := min_le_right (lastCoord n y) h'
    let z : E (n + 1) := emb n (dropLast n y) + t • eLast n
    refine ⟨z, ?_, ?_⟩
    · rw [cyl0_coe, mem_cylSet]
      constructor
      · have hd : dropLast n z = dropLast n y := by dsimp [z]; simp
        simpa [hd] using hy.1
      · have hl : lastCoord n z = t := by dsimp [z]; simp
        rw [hl]
        rw [Set.mem_Icc]
        constructor
        · exact ht0
        · exact hth'
    · have hv : y - z = (lastCoord n y - t) • eLast n := by
        dsimp [z]
        calc
          y - (emb n (dropLast n y) + t • eLast n)
              = (emb n (dropLast n y) + lastCoord n y • eLast n) - (emb n (dropLast n y) + t • eLast n) := by
              rw [emb_dropLast_add_last n y]
          _ = lastCoord n y • eLast n - t • eLast n := by abel
          _ = (lastCoord n y - t) • eLast n := by rw [← sub_smul]
      have hdist : dist y z = |lastCoord n y - t| := by
        rw [dist_eq_norm]
        rw [hv]
        simp [norm_smul, Real.norm_eq_abs, norm_eLast]
      rw [hdist]
      exact abs_sub_clamp_le hy.2.1 (Set.mem_Icc.mp hy.2).2 hh'
  · intro y hy
    rw [cyl0_coe, mem_cylSet] at hy
    let t : ℝ := min (lastCoord n y) h
    have ht0 : 0 ≤ t := by
      exact le_min hy.2.1 hh
    have hth : t ≤ h := min_le_right (lastCoord n y) h
    let z : E (n + 1) := emb n (dropLast n y) + t • eLast n
    refine ⟨z, ?_, ?_⟩
    · rw [cyl0_coe, mem_cylSet]
      constructor
      · have hd : dropLast n z = dropLast n y := by dsimp [z]; simp
        simpa [hd] using hy.1
      · have hl : lastCoord n z = t := by dsimp [z]; simp
        rw [hl]
        rw [Set.mem_Icc]
        constructor
        · exact ht0
        · exact hth
    · have hv : y - z = (lastCoord n y - t) • eLast n := by
        dsimp [z]
        calc
          y - (emb n (dropLast n y) + t • eLast n)
              = (emb n (dropLast n y) + lastCoord n y • eLast n) - (emb n (dropLast n y) + t • eLast n) := by
              rw [emb_dropLast_add_last n y]
          _ = lastCoord n y • eLast n - t • eLast n := by abel
          _ = (lastCoord n y - t) • eLast n := by rw [← sub_smul]
      have hdist : dist y z = |lastCoord n y - t| := by
        rw [dist_eq_norm]
        rw [hv]
        simp [norm_smul, Real.norm_eq_abs, norm_eLast]
      rw [hdist]
      have hb := abs_sub_clamp_le hy.2.1 (Set.mem_Icc.mp hy.2).2 hh
      -- hb : |lc - min lc h| ≤ |h' - h|
      calc
        |lastCoord n y - min (lastCoord n y) h| ≤ |h' - h| := hb
        _ = |h - h'| := abs_sub_comm h' h

/-- If the unit cylinder vanishes then cylinders of every real height `h ≥ 0`
vanish: the height map is continuous (height-Lipschitz) and vanishes on the
dense set of rational heights. -/
theorem mu_cyl0_nonneg {n : ℕ} (K : ConvexBody (E n)) (μ : ConvexBody (E (n + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (E (n + 1)),
        (A : Set (E (n + 1))) = (C : Set (E (n + 1))) ∪ (D : Set (E (n + 1))) →
        (B : Set (E (n + 1))) = (C : Set (E (n + 1))) ∩ (D : Set (E (n + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (n + 1)), interior (K : Set (E (n + 1))) = ∅ → μ K = 0)
    (htrans : ∀ A B : ConvexBody (E (n + 1)), ∀ t : E (n + 1),
        (B : Set (E (n + 1))) = (fun x : E (n + 1) => x + t) '' (A : Set (E (n + 1))) → μ A = μ B)
    (h1 : μ (cyl0 n K 1 (by norm_num)) = 0)
    (h : ℝ) (hh : 0 ≤ h) :
    μ (cyl0 n K h hh) = 0 := by
  by_cases hz : h = 0
  · subst h
    have heq : cyl0 n K 0 hh = cyl0 n K 0 (le_refl (0 : ℝ)) := by
      apply ConvexBody.ext
      rfl
    rw [heq]
    exact mu_cyl0_zero K μ hsimple
  · have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hz)
    let p : ℕ → ℕ := fun m => ⌊h * (m : ℝ)⌋₊
    let r : ℕ → ℝ := fun m => if m = 0 then 0 else ((p m : ℕ) : ℝ) / (m : ℝ)
    have hrm : ∀ m : ℕ, 0 ≤ r m := by
      intro m
      by_cases hm : m = 0
      · subst m
        dsimp [r]
        simp
      · dsimp [r]
        rw [if_neg hm]
        have hden : 0 < (m : ℝ) := by
          have hmpos : 0 < m := Nat.pos_of_ne_zero hm
          exact_mod_cast hmpos
        exact div_nonneg (Nat.cast_nonneg (p m)) (le_of_lt hden)
    have hval : ∀ m : ℕ, μ (cyl0 n K (r m) (hrm m)) = 0 := by
      intro m
      by_cases hm : m = 0
      · subst m
        have heq : cyl0 n K (r 0) (hrm 0) = cyl0 n K 0 (le_refl (0 : ℝ)) := by
          apply ConvexBody.ext
          dsimp [r]
        rw [heq]
        exact mu_cyl0_zero K μ hsimple
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hp0 : 0 ≤ ((p m : ℕ) : ℝ) / (m : ℝ) := by
          exact div_nonneg (Nat.cast_nonneg (p m)) (le_of_lt (by exact_mod_cast hmpos))
        have hmu := mu_cyl0_rational K μ hadd hsimple htrans h1 (p m) m hmpos hp0
        have heq : cyl0 n K (((p m : ℕ) : ℝ) / (m : ℝ)) hp0 = cyl0 n K (r m) (hrm m) := by
          apply ConvexBody.ext
          dsimp [r]
          rw [if_neg hm]
        rw [← heq]
        exact hmu
    have hbase : Tendsto (fun x : ℝ => (((⌊h * x⌋₊ : ℕ) : ℝ) / x)) atTop (𝓝 h) :=
      tendsto_nat_floor_mul_div_atTop hh
    have hbaseNat : Tendsto (fun m : ℕ => (((⌊h * (m : ℝ)⌋₊ : ℕ) : ℝ) / (m : ℝ))) atTop (𝓝 h) :=
      hbase.comp tendsto_natCast_atTop_atTop
    have hrt : Tendsto r atTop (𝓝 h) := by
      have hl : (fun m : ℕ => (((⌊h * (m : ℝ)⌋₊ : ℕ) : ℝ) / (m : ℝ))) =ᶠ[atTop] r := by
        rw [Filter.EventuallyEq]
        refine Filter.eventually_atTop.2 ⟨1, ?_⟩
        intro m hm
        dsimp [r]
        have hm0 : m ≠ 0 := by omega
        rw [if_neg hm0]
      exact Filter.Tendsto.congr' hl hbaseNat
    have hleC : ∀ m : ℕ, dist (cyl0 n K (r m) (hrm m)) (cyl0 n K h hh) ≤ |r m - h| := by
      intro m
      rw [← ConvexBody.hausdorffDist_coe (K := cyl0 n K (r m) (hrm m)) (L := cyl0 n K h hh)]
      exact cyl0_hausdorff_heights K (hrm m) hh
    have hC : Tendsto (fun m : ℕ => cyl0 n K (r m) (hrm m)) atTop (𝓝 (cyl0 n K h hh)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [Metric.tendsto_nhds.mp hrt ε hε] with m hd
      have hle := hleC m
      exact lt_of_le_of_lt hle (by simpa [Real.dist_eq] using hd)
    have hmuT : Tendsto (fun m : ℕ => μ (cyl0 n K (r m) (hrm m))) atTop
        (𝓝 (μ (cyl0 n K h hh))) := by
      exact ((hcont.continuousAt (x := cyl0 n K h hh)).tendsto.comp hC)
    have hzeroSeq : (fun m : ℕ => μ (cyl0 n K (r m) (hrm m))) = fun _ : ℕ => (0 : ℝ) := by
      funext m
      exact hval m
    have hzeroT : Tendsto (fun m : ℕ => μ (cyl0 n K (r m) (hrm m))) atTop (𝓝 (0 : ℝ)) := by
      rw [hzeroSeq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hmuT hzeroT

/-! ## Orientation lemma (exact statement; proof deferred)

The remaining in-dimension chain needs the following *unit boxes of every
orientation* fact (Klain's Thm 3.3, step 2, pp. 334-335):

> Let `μ` be a continuous, translation-invariant, *simple* valuation on
> `E (m+1)` that vanishes on every axis-parallel box.  Then for every linear
> isometry `ρ : E (m+1) ≃ₗᵢ[ℝ] E (m+1)` the rotated unit cube vanishes:
> `μ (bodyIsometry ρ (cubeBody (m+1))) = 0`.

The proof splits into two independent pieces:

1. **2-D scissors lemma (Fig. 1).**  For a rotation acting within a plane spanned
   by two basis vectors of a frame and fixing the other `n-2` basis vectors, the
   rotated box is dissected into finitely many convex pieces whose translates
   reassemble into an axis-parallel box of the same frame; hence its `μ`-value
   equals that of an axis-parallel box (i.e. `0`).  In value form: if `μ` vanishes
   on boxes parallel to a frame `F` and `ρ` fixes all but two vectors of `F`,
   rotating within their span, then `μ` vanishes on boxes parallel to `ρ(F)`.
   (Needs the 2-D Fig. 1 construction + `dissection_additivity` for simple
   valuations, being built in the commons.)

2. **Rotation decomposition (Prop. 3.2).**  Every linear isometry
   `ρ : E (m+1) ≃ₗᵢ[ℝ] E (m+1)` is a finite product of isometries each of which
   fixes at least `m` of the standard basis vectors, composed with a product of
   coordinate reflections.  (A coordinate reflection maps the cube to a translate
   of the cube, which vanishes by translation invariance; evenness is not needed
   here.)

Once (1) and (2) are available, `μ (bodyIsometry ρ (cubeBody (m+1))) = 0` follows
by induction over the product: at each stage the current box is parallel to the
frame produced by the previous factors and (1) applies fiberwise over the fixed
`m-1` coordinates.  The orientation statement then feeds the admissibility of the
section valuations `τ_H` over arbitrary hyperplanes `H`, which is how right
cylinders of every orientation (step 3) -- and hence the oblique-prism, polytope
and zonoid steps -- are obtained.

Implementation status: `bodyIsometry` API (image of bodies under linear isometries,
isometry/continuity) and the cube-preservation warm-up
(`bodyIsometry_cube_of_set_eq_any`, `mu_rotatedCube_eq_axis_of_cube_preserving`)
are below.  The full value-level orientation lemma has been REQUESTED from the
fleet (commons lemma `klain333_boxes_all_orientations`, self-contained statement
in `Geometry/Convex/Hadwiger/`); it will be imported here once it lands, and the
in-dimension chain inside `klain333_inner_step` will then apply it (axis boxes
vanish by `hCylAll`), followed by cylinders over arbitrary hyperplanes, oblique
prisms, polytopes/zonotopes, centred bodies, simplices, density.
-/

/-- Box-vanishing in dimension `n`: every continuous, quadruple-additive,
translation-invariant, simple, even valuation on `E n` that vanishes on the
unit coordinate cube is identically zero.  (Klain Thm 3.3, `P n`.) -/
def BoxVan (n : ℕ) : Prop :=
  ∀ (φ : ConvexBody (E n) → ℝ),
    Continuous φ →
    (∀ A B C D : ConvexBody (E n),
        (A : Set (E n)) = (C : Set (E n)) ∪ (D : Set (E n)) →
        (B : Set (E n)) = (C : Set (E n)) ∩ (D : Set (E n)) → φ A + φ B = φ C + φ D) →
    (∀ A B : ConvexBody (E n), ∀ t : E n,
        (B : Set (E n)) = (fun x : E n => x + t) '' (A : Set (E n)) → φ A = φ B) →
    (∀ K : ConvexBody (E n), interior (K : Set (E n)) = ∅ → φ K = 0) →
    (∀ A B : ConvexBody (E n), (B : Set (E n)) = -(A : Set (E n)) → φ A = φ B) →
    (∀ Q : ConvexBody (E n),
        (Q : Set (E n)) = (EuclideanSpace.equiv (Fin n) ℝ).symm ''
          (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
    ∀ K : ConvexBody (E n), φ K = 0

/-- The image under an isometry of the negation of a set is the negation of the image. -/
theorem lie_neg_image {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : U ≃ₗᵢ[ℝ] V) (A : Set U) : -(e '' A) = e '' (-A) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_neg] at hx
    rcases hx with ⟨a, haA, hxeq⟩
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Set.mem_neg]
    have hsym : e.symm x = -a := by
      apply e.injective
      calc
        e (e.symm x) = x := by simp
        _ = -(e a) := by
          have hxeq' : -(e a) = x := by simpa [neg_neg] using congrArg Neg.neg hxeq
          exact hxeq'.symm
        _ = e (-a) := by
          exact ((e : U →ₗ[ℝ] V).map_neg a).symm
    rw [hsym]
    simpa using haA
  · rintro ⟨a, ha, rfl⟩
    rw [Set.mem_neg]
    refine ⟨-a, Set.mem_neg.mp ha, ?_⟩
    exact (e : U →ₗ[ℝ] V).map_neg a

/-- The cylinder/`τ` part of the induction step, factored out: if `BoxVan m`
holds then every admissible valuation on `E (m+1)` vanishes on every right
coordinate cylinder over a convex base in the standard frame, at every height
`h ≥ 0`. -/
theorem cyl0_all_heights (m : ℕ) (hV : BoxVan m) :
    ∀ (μ : ConvexBody (E (m + 1)) → ℝ),
      Continuous μ →
      (∀ A B C D : ConvexBody (E (m + 1)),
          (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
          (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
          μ A + μ B = μ C + μ D) →
      (∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
          (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → μ A = μ B) →
      (∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0) →
      (∀ A B : ConvexBody (E (m + 1)), (B : Set (E (m + 1))) = -(A : Set (E (m + 1))) → μ A = μ B) →
      (∀ Q : ConvexBody (E (m + 1)),
          (Q : Set (E (m + 1))) = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
            (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) → μ Q = 0) →
      ∀ K : ConvexBody (E m), ∀ h : ℝ, ∀ hh : 0 ≤ h,
        μ (cyl0 m K h hh) = 0 := by
  intro μ hμcont hμadd hμtrans hμsimple hμeven hμcube
  -- Section valuation over unit cylinders is admissible on E m, hence zero by hV.
  let τ : ConvexBody (E m) → ℝ := fun K => μ (cyl0 m K 1 (by norm_num))
  have hτcont : Continuous τ := by
    dsimp [τ]
    exact hμcont.comp (continuous_cyl0_one m)
  have hτadd : ∀ A B C D : ConvexBody (E m),
      (A : Set (E m)) = (C : Set (E m)) ∪ (D : Set (E m)) →
      (B : Set (E m)) = (C : Set (E m)) ∩ (D : Set (E m)) → τ A + τ B = τ C + τ D := by
    intro A B C D hU hI
    have h := hμadd (cyl0 m A 1 (by norm_num)) (cyl0 m B 1 (by norm_num))
        (cyl0 m C 1 (by norm_num)) (cyl0 m D 1 (by norm_num))
        (cyl0_union_set (n := m) hU) (cyl0_inter_set (n := m) hU hI)
    dsimp [τ]
    exact h
  have hτtrans : ∀ A B : ConvexBody (E m), ∀ t : E m,
      (B : Set (E m)) = (fun x : E m => x + t) '' (A : Set (E m)) → τ A = τ B := by
    intro A B t hB
    dsimp [τ]
    have hBbody : B = bodyTranslate A t := by
      apply ConvexBody.ext
      rw [bodyTranslate_coe_right]
      exact hB
    have hcylB : cyl0 m B 1 (by norm_num) = cyl0 m (bodyTranslate A t) 1 (by norm_num) := by
      rw [hBbody]
    have hBodyEq : cyl0 m (bodyTranslate A t) 1 (by norm_num) =
        bodyTranslate (cyl0 m A 1 (by norm_num)) (emb m t) := by
      apply ConvexBody.ext
      rw [cyl0_bodyTranslate_set, bodyTranslate_coe_right]
    have hval : μ (cyl0 m (bodyTranslate A t) 1 (by norm_num)) = μ (cyl0 m A 1 (by norm_num)) := by
      rw [hBodyEq]
      exact (hμtrans (cyl0 m A 1 (by norm_num)) (bodyTranslate (cyl0 m A 1 (by norm_num)) (emb m t))
        (emb m t) (bodyTranslate_coe_right (cyl0 m A 1 (by norm_num)) (emb m t))).symm
    rw [hcylB]
    exact hval.symm
  have hτsimple : ∀ K : ConvexBody (E m), interior (K : Set (E m)) = ∅ → τ K = 0 := by
    intro K hK
    dsimp [τ]
    exact hμsimple (cyl0 m K 1 (by norm_num)) (interior_cyl0_eq_empty m K 1 (by norm_num) hK)
  have hτeven : ∀ A B : ConvexBody (E m), (B : Set (E m)) = -(A : Set (E m)) → τ A = τ B := by
    intro A B hB
    dsimp [τ]
    have hBbody : B = bodyNeg A := by
      apply ConvexBody.ext
      rw [bodyNeg_coe]
      exact hB
    have hcylB : cyl0 m B 1 (by norm_num) = cyl0 m (bodyNeg A) 1 (by norm_num) := by
      rw [hBbody]
    have hBodyEq : cyl0 m (bodyNeg A) 1 (by norm_num) =
        bodyNeg (bodyTranslate (cyl0 m A 1 (by norm_num)) (-eLast m)) := by
      apply ConvexBody.ext
      calc
        ((cyl0 m (bodyNeg A) 1 (by norm_num)) : Set (E (m + 1)))
            = -(bodyTranslate (cyl0 m A 1 (by norm_num)) (-eLast m) : Set (E (m + 1))) := by
            have h2 := congrArg (fun s : Set (E (m + 1)) => -s) (neg_cyl0_bodyNeg_eq m A)
            simpa using h2
        _ = ((bodyNeg (bodyTranslate (cyl0 m A 1 (by norm_num)) (-eLast m))) : Set (E (m + 1))) := by
            rw [bodyNeg_coe]
    have hval : μ (cyl0 m (bodyNeg A) 1 (by norm_num)) = μ (cyl0 m A 1 (by norm_num)) := by
      rw [hBodyEq]
      have hneg : μ (bodyNeg (bodyTranslate (cyl0 m A 1 (by norm_num)) (-eLast m))) =
          μ (bodyTranslate (cyl0 m A 1 (by norm_num)) (-eLast m)) := by
        exact val_bodyNeg μ hμeven (bodyTranslate (cyl0 m A 1 (by norm_num)) (-eLast m))
      rw [hneg]
      exact val_bodyTranslate μ hμtrans (cyl0 m A 1 (by norm_num)) (-eLast m)
    rw [hcylB]
    exact hval.symm
  have hτcube : ∀ Q : ConvexBody (E m),
      (Q : Set (E m)) = (EuclideanSpace.equiv (Fin m) ℝ).symm ''
        (Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1)) → τ Q = 0 := by
    intro Q hQ
    dsimp [τ]
    have hQbody : Q = cubeBody m := by
      apply ConvexBody.ext
      rw [cubeBody_coe, cubeSet_eq_equiv_image]
      exact hQ
    have hcylQ : cyl0 m Q 1 (by norm_num) = cyl0 m (cubeBody m) 1 (by norm_num) := by rw [hQbody]
    rw [hcylQ]
    have hBodyEq : cyl0 m (cubeBody m) 1 (by norm_num) = cubeBody (m + 1) := by
      apply ConvexBody.ext
      rw [cyl0_cubeBody_eq, cubeBody_coe]
    rw [hBodyEq]
    have hset : ((cubeBody (m + 1)) : Set (E (m + 1))) =
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
          (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) := by
      rw [cubeBody_coe]
      exact cubeSet_eq_equiv_image (m + 1)
    exact hμcube (cubeBody (m + 1)) hset
  have hτzero : ∀ K : ConvexBody (E m), τ K = 0 := by
    exact hV τ hτcont hτadd hτtrans hτsimple hτeven hτcube
  -- Every unit right cylinder over a base in the coordinate hyperplane vanishes.
  have hCylOne : ∀ K : ConvexBody (E m), μ (cyl0 m K 1 (by norm_num)) = 0 := by
    intro K
    simpa [τ] using hτzero K
  -- Feed-back: by `mu_cyl0_nonneg` (height continuity + rational approximation)
  -- unit-cylinder vanishing implies that *every* coordinate cylinder
  -- `K × [0,h]` (h ≥ 0) vanishes.
  have hCylAll : ∀ K : ConvexBody (E m), ∀ h : ℝ, ∀ hh : 0 ≤ h,
      μ (cyl0 m K h hh) = 0 := by
    intro K h hh
    exact mu_cyl0_nonneg K μ hμcont hμadd hμsimple hμtrans (hCylOne K) h hh

  exact hCylAll

/-- Rotated cylinders: with `BoxVan m` and vanishing of all rotated unit cubes
(`hrot`), an admissible valuation vanishes on every right cylinder over a base
in any orthonormal frame (`imageLIE ρ` of the standard cylinder), at every
height `h ≥ 0`. -/
theorem rotCyl_all_heights (m : ℕ) (hV : BoxVan m)
    (μ : ConvexBody (E (m + 1)) → ℝ)
    (hμcont : Continuous μ)
    (hμadd : ∀ A B C D : ConvexBody (E (m + 1)),
        (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
        (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
        μ A + μ B = μ C + μ D)
    (hμtrans : ∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
        (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → μ A = μ B)
    (hμsimple : ∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0)
    (hμeven : ∀ A B : ConvexBody (E (m + 1)), (B : Set (E (m + 1))) = -(A : Set (E (m + 1))) → μ A = μ B)
    (hrot : ∀ ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1),
        μ (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cubeBody (m + 1))) = 0) :
    ∀ ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1),
      ∀ K : ConvexBody (E m), ∀ h : ℝ, ∀ hh : 0 ≤ h,
        μ (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cyl0 m K h hh)) = 0 := by
  intro ρ
  let Ψ : ConvexBody (E (m + 1)) → ℝ := fun A =>
    μ (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ A)
  have hΨcont : Continuous Ψ := by
    dsimp [Ψ]
    exact hμcont.comp (Commons.Geometry.Convex.Hadwiger.imageLIE_isometry ρ).continuous
  have hΨadm := Commons.Geometry.Convex.Hadwiger.imageLIE_admissible (e := ρ) (μ := μ)
    hμadd hμtrans hμsimple
  rcases hΨadm with ⟨hΨadd, hΨtrans, hΨsimple⟩
  have hΨeven : ∀ A B : ConvexBody (E (m + 1)),
      (B : Set (E (m + 1))) = -(A : Set (E (m + 1))) → Ψ A = Ψ B := by
    intro A B hB
    dsimp [Ψ]
    have hB' : ((Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ B) : Set (E (m + 1))) =
        -((Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ A) : Set (E (m + 1))) := by
      rw [show ((Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ B) : Set (E (m + 1))) =
          ρ '' (B : Set (E (m + 1))) by rfl]
      rw [hB]
      rw [show ((Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ A) : Set (E (m + 1))) =
          ρ '' (A : Set (E (m + 1))) by rfl]
      exact (lie_neg_image ρ (A : Set (E (m + 1)))).symm
    exact hμeven (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ A)
      (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ B) hB'
  have hΨcube : ∀ Q : ConvexBody (E (m + 1)),
      (Q : Set (E (m + 1))) = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
        (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) → Ψ Q = 0 := by
    intro Q hQ
    dsimp [Ψ]
    have hQc : (Q : Set (E (m + 1))) = cubeSet (m + 1) :=
      hQ.trans (cubeSet_eq_equiv_image (m + 1)).symm
    have hb : Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ Q =
        Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cubeBody (m + 1)) := by
      apply ConvexBody.ext
      simp [hQc]
    rw [hb]
    exact hrot ρ
  -- Ψ is admissible on E (m+1); cyl0_all_heights gives the rotated-cylinder
  -- vanishing at all heights.
  intro K h hh
  change μ (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cyl0 m K h hh)) = 0
  exact cyl0_all_heights m hV Ψ hΨcont hΨadd hΨtrans hΨsimple hΨeven hΨcube K h hh


/-- Base case of the box-vanishing induction, dimension `0`: the ambient space
`E 0` has a single point, every convex body is the whole space, and the unit
cube is the whole space, so the cube-vanishing clause already forces every
admissible valuation to vanish everywhere. -/
theorem boxVan_zero : BoxVan 0 := by
  intro φ hφcont hφadd hφtrans hφsimple hφeven hφcube
  intro K
  have hKuniv : (K : Set (E 0)) = Set.univ := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      rcases K.nonempty with ⟨y, hy⟩
      have hxy : x = y := by
        apply PiLp.ext
        intro i
        exact Fin.elim0 i
      simpa [hxy] using hy
  have huniv_eq_cube : (Set.univ : Set (E 0)) =
      (EuclideanSpace.equiv (Fin 0) ℝ).symm ''
        (Set.pi Set.univ (fun _ : Fin 0 => Set.Icc (0 : ℝ) 1)) := by
    ext x
    constructor
    · intro hx
      refine ⟨EuclideanSpace.equiv (Fin 0) ℝ x, ?_, ?_⟩
      · intro i hi
        exact Fin.elim0 i
      · rfl
    · rintro ⟨f, hf, rfl⟩
      trivial
  exact hφcube K (by rw [hKuniv]; exact huniv_eq_cube)


/--
The induction step of Klain's Theorem 3.3 (proper form): box-vanishing in
dimension `m` (all admissible valuations are identically zero) implies
box-vanishing in dimension `m + 1`.

In this file we implement the step up to the point where every admissible
valuation vanishes on all *coordinate right cylinders* `K × [0,h]` (h ≥ 0)
over bases `K` of the coordinate hyperplane: unit cylinders via the section
valuation (the use of the induction hypothesis), all heights via
`mu_cyl0_nonneg`.  The remaining in-dimension steps (orientations, prisms,
zonotopes, centred bodies, simplices, density) are assembled in later
stretches; see the header note.
-/

theorem klain333_inner_step (m : ℕ) :
    (∀ (φ : ConvexBody (E m) → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody (E m),
          (A : Set (E m)) = (C : Set (E m)) ∪ (D : Set (E m)) →
          (B : Set (E m)) = (C : Set (E m)) ∩ (D : Set (E m)) → φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody (E m), ∀ t : E m,
          (B : Set (E m)) = (fun x : E m => x + t) '' (A : Set (E m)) → φ A = φ B) →
      (∀ K : ConvexBody (E m), interior (K : Set (E m)) = ∅ → φ K = 0) →
      (∀ A B : ConvexBody (E m), (B : Set (E m)) = -(A : Set (E m)) → φ A = φ B) →
      (∀ Q : ConvexBody (E m),
          (Q : Set (E m)) = (EuclideanSpace.equiv (Fin m) ℝ).symm ''
            (Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
      ∀ K : ConvexBody (E m), φ K = 0) →
    (∀ (φ : ConvexBody (E (m + 1)) → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody (E (m + 1)),
          (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
          (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
          φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
          (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → φ A = φ B) →
      (∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → φ K = 0) →
      (∀ A B : ConvexBody (E (m + 1)), (B : Set (E (m + 1))) = -(A : Set (E (m + 1))) → φ A = φ B) →
      (∀ Q : ConvexBody (E (m + 1)),
          (Q : Set (E (m + 1))) = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
            (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
      ∀ K : ConvexBody (E (m + 1)), φ K = 0) := by
  intro hV
  intro μ hμcont hμadd hμtrans hμsimple hμeven hμcube
  -- Cylinders in the standard frame (all bases, all heights) vanish: this is
  -- the factored-out section-valuation argument using the `BoxVan m` hypothesis.
  have hCylAll : ∀ K : ConvexBody (E m), ∀ h : ℝ, ∀ hh : 0 ≤ h,
      μ (cyl0 m K h hh) = 0 :=
    cyl0_all_heights m hV μ hμcont hμadd hμtrans hμsimple hμeven hμcube
  -- Axis-parallel boxes (all real side lengths) vanish: commons lemma
  -- `valuation_zero_on_axisBoxes` (its proof dissects the unit cube into tiny
  -- subcubes, tiles rational boxes, and passes to real lengths by continuity).
  have haxis : ∀ a : Fin (m + 1) → ℝ, (∀ i : Fin (m + 1), 0 ≤ a i) →
      ∀ Q : ConvexBody (E (m + 1)),
        (Q : Set (E (m + 1))) = {x : E (m + 1) | ∀ i : Fin (m + 1), x i ∈ Set.Icc (0 : ℝ) (a i)} →
        μ Q = 0 := by
    intro a ha Q hQ
    have hboxeq : {x : E (m + 1) | ∀ i : Fin (m + 1), x i ∈ Set.Icc (0 : ℝ) (a i)} =
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm ''
          (Set.pi Set.univ (fun i : Fin (m + 1) => Set.Icc (0 : ℝ) (a i))) := by
      ext x
      constructor
      · intro hx
        refine ⟨EuclideanSpace.equiv (Fin (m + 1)) ℝ x, ?_, ?_⟩
        · intro i hi
          exact hx i
        · rfl
      · rintro ⟨f, hf, rfl⟩
        intro i
        exact hf i trivial
    exact Commons.Geometry.Convex.Hadwiger.valuation_zero_on_axisBoxes (m + 1) μ hμcont hμadd
      hμtrans hμsimple hμcube (fun _ : Fin (m + 1) => (0 : ℝ)) a ha Q (by rw [hQ]; exact hboxeq)
  -- Unit cubes of every orthonormal orientation vanish: commons lemma
  -- `klain333_boxes_all_orientations` (axis boxes -> plane rotations -> Givens
  -- words -> all of O(n)).
  have hrot : ∀ ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1),
      μ (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cubeBody (m + 1))) = 0 := by
    intro ρ
    exact Commons.Geometry.Convex.Hadwiger.KlainInlineVD.klain333_boxes_all_orientations (m + 1) μ hμcont hμadd
      hμtrans hμsimple haxis ρ
        (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cubeBody (m + 1))) (by simpa [cubeSet])
  -- Right cylinders over convex bases in *every* orthonormal frame, at every
  -- height h >= 0: conjugate by the frame isometry and re-run the cylinder
  -- argument (`rotCyl_all_heights`).
  have hcylFrame : ∀ ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1),
      ∀ K : ConvexBody (E m), ∀ h : ℝ, ∀ hh : 0 ≤ h,
        μ (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cyl0 m K h hh)) = 0 :=
    rotCyl_all_heights m hV μ hμcont hμadd hμtrans hμsimple hμeven hrot
  -- The in-dimension chain of Klain Thm 3.3 (steps 4-7), packaged as the
  -- commons lemma `klain333_from_cylinders`: its cylinder hypothesis is the
  -- coordinate-set form of `imageLIE ρ (cyl0 m K h hh)`, so it follows from
  -- `hcylFrame` by rewriting the carrier.
  have hcylQ : ∀ ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1),
      ∀ K : ConvexBody (E m), ∀ h : ℝ, 0 ≤ h →
      ∀ Q : ConvexBody (E (m + 1)),
        (Q : Set (E (m + 1))) =
          {y : E (m + 1) |
            (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => (ρ.symm y) (Fin.castSucc i)) ∈
              (K : Set (E m)) ∧
            (ρ.symm y) (Fin.last m) ∈ Set.Icc (0 : ℝ) h} →
        μ Q = 0 := by
    intro ρ K h hh Q hQ
    have hset : (Q : Set (E (m + 1))) =
        (Commons.Geometry.Convex.Hadwiger.ConvexBody.imageLIE ρ (cyl0 m K h hh) :
          Set (E (m + 1))) := by
      rw [hQ, Commons.Geometry.Convex.Hadwiger.imageLIE_apply]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_image, cyl0_coe, cylSet, dropLast, lastCoord]
      constructor
      · rintro ⟨hxK, hxh⟩
        exact ⟨ρ.symm x, ⟨hxK, hxh⟩, ρ.apply_symm_apply x⟩
      · rintro ⟨y, ⟨hyK, hyh⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · simpa only [LinearIsometryEquiv.symm_apply_apply] using hyK
        · simpa only [LinearIsometryEquiv.symm_apply_apply] using hyh
    rw [val_eq_of_set_eq μ hμadd hset]
    exact hcylFrame ρ K h hh
  exact Commons.Geometry.Convex.Hadwiger.klain333_from_cylinders m μ hμcont hμadd
    hμtrans hμsimple hμeven hcylQ


end

end Commons.Geometry.Convex.Hadwiger.Klain333Step

namespace Commons.Geometry.Convex.Hadwiger

open Commons.Geometry.Convex.Hadwiger.Klain333Step

/-- Box-vanishing in every dimension (Klain Thm 3.3), by induction from the base
case `BoxVan 0` and the induction step `klain333_inner_step`. -/
theorem boxVan_all : ∀ n : ℕ, BoxVan n
  | 0 => boxVan_zero
  | n + 1 => klain333_inner_step n (boxVan_all n)

theorem klain333_step (m : ℕ) :
    let V := EuclideanSpace ℝ (Fin m)
    ∀ (φ : ConvexBody V → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody V,
          (A : Set V) = (C : Set V) ∪ (D : Set V) →
          (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody V, ∀ t : V,
          (B : Set V) = (fun x : V => x + t) '' (A : Set V) → φ A = φ B) →
      (∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0) →
      (∀ A B : ConvexBody V, (B : Set V) = -(A : Set V) → φ A = φ B) →
      (∀ Q : ConvexBody V,
          (Q : Set V) = (EuclideanSpace.equiv (Fin m) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
      ∀ K : ConvexBody V, φ K = 0 →
    let W := EuclideanSpace ℝ (Fin (m + 1))
    ∀ (φ : ConvexBody W → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody W,
          (A : Set W) = (C : Set W) ∪ (D : Set W) →
          (B : Set W) = (C : Set W) ∩ (D : Set W) → φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody W, ∀ t : W,
          (B : Set W) = (fun x : W => x + t) '' (A : Set W) → φ A = φ B) →
      (∀ K : ConvexBody W, interior (K : Set W) = ∅ → φ K = 0) →
      (∀ A B : ConvexBody W, (B : Set W) = -(A : Set W) → φ A = φ B) →
      (∀ Q : ConvexBody W,
          (Q : Set W) = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Icc (0 : ℝ) 1)) → φ Q = 0) →
      ∀ K : ConvexBody W, φ K = 0 := by
  dsimp only
  intro φ hφcont hφadd hφtrans hφsimple hφeven hφcube K hKzero
  exact boxVan_all (m + 1)

/-- Conflict-free copy of `Commons.Geometry.Convex.Hadwiger.klain333_boxes_all_orientations`
(see the note at the top of this file): its transitive dependency
`orthogonal_word_decomposition` -- which declares a top-level abbreviation
`Commons.Geometry.Convex.Hadwiger.E` clashing with the one of
`zonoidLimit_of_continuous_even_nonneg` -- is inlined here (namespace
`KlainInlineVD`), so that this module can be imported alongside the
zonoid/centred-body chain.  The statement is literally that of the original. -/
theorem klain333_boxes_all_orientations_scoped
    (n : ℕ)
    (μ : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin n)),
        (A : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∪ (D : Set (EuclideanSpace ℝ (Fin n))) →
        (B : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∩ (D : Set (EuclideanSpace ℝ (Fin n))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)), ∀ t : EuclideanSpace ℝ (Fin n),
        (B : Set (EuclideanSpace ℝ (Fin n))) = (fun x : EuclideanSpace ℝ (Fin n) => x + t) '' (A : Set (EuclideanSpace ℝ (Fin n))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EuclideanSpace ℝ (Fin n)), interior (K : Set (EuclideanSpace ℝ (Fin n))) = ∅ → μ K = 0)
    (haxis : ∀ a : Fin n → ℝ, (∀ i : Fin n, 0 ≤ a i) → ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin n)),
        (Q : Set (EuclideanSpace ℝ (Fin n))) = {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) (a i)} →
        μ Q = 0) :
    ∀ ρ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin n)),
        (Q : Set (EuclideanSpace ℝ (Fin n))) = ρ '' {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1} →
        μ Q = 0 :=
  KlainInlineVD.klain333_boxes_all_orientations n μ hcont hadd htrans hsimple haxis

end Commons.Geometry.Convex.Hadwiger
