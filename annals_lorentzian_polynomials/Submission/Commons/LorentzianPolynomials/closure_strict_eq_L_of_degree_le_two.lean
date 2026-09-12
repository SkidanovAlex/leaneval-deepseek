import Mathlib
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_P_eq_nonneg
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq_challenge
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LinearAlgebra.Matrix.closure_strict_lorentzian_quadratic
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

/-! Algebraic and topological structure on `H n d`, needed below. -/

instance instAddCommGroupH (n d : ℕ) : AddCommGroup (H n d) := by
  dsimp [H]
  exact (homogeneousSubmodule (Fin n) ℝ d).addCommGroup

instance instModuleH (n d : ℕ) : Module ℝ (H n d) := by
  dsimp [H]
  exact (homogeneousSubmodule (Fin n) ℝ d).module

instance instIsModuleTopologyH (n d : ℕ) : IsModuleTopology ℝ (H n d) := by
  constructor
  change moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d) = moduleTopology ℝ (H n d)
  dsimp [H]

instance instContinuousAddH (n d : ℕ) : ContinuousAdd (H n d) :=
  IsModuleTopology.toContinuousAdd ℝ (H n d)

instance instIsTopologicalAddGroupH (n d : ℕ) : IsTopologicalAddGroup (H n d) :=
  IsModuleTopology.topologicalAddGroup ℝ (H n d)

/-! Monomial combinatorics for degree two monomials. -/

/-- `weight 1 m = ∑ m i`. -/
lemma weight_one_eq_sum' {n : ℕ} (m : Fin n →₀ ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) m = ∑ i : Fin n, m i := by
  simpa using (Finsupp.weight_eq_sum (w := (1 : Fin n → ℕ)) (f := m))

/-- A monomial of degree two is either a square or a product of two distinct variables. -/
lemma weight_two_decompose {n : ℕ} {m : Fin n →₀ ℕ}
    (hm : Finsupp.weight (1 : Fin n → ℕ) m = 2) :
    (∃ i : Fin n, m = Finsupp.single i 2) ∨
      ∃ (i j : Fin n), i ≠ j ∧ m = Finsupp.single i 1 + Finsupp.single j 1 := by
  classical
  have hsum : (∑ i : Fin n, m i) = 2 := by
    rw [← weight_one_eq_sum' m]
    exact hm
  by_cases hbig : ∃ i : Fin n, 2 ≤ m i
  · rcases hbig with ⟨i, hi⟩
    left
    refine ⟨i, ?_⟩
    apply Finsupp.ext
    intro k
    by_cases hik : k = i
    · subst k
      rw [Finsupp.single_eq_same]
      have hle : m i ≤ 2 := by
        have h2 : m i ≤ ∑ j : Fin n, m j := by
          exact Finset.single_le_sum (fun x hx => Nat.zero_le (m x)) (Finset.mem_univ i)
        omega
      omega
    · rw [Finsupp.single_eq_of_ne hik]
      by_contra hk0
      have hkpos : 0 < m k := Nat.pos_of_ne_zero hk0
      have hge : m i + m k ≤ ∑ j : Fin n, m j := by
        have h2 : m k ≤ ∑ j ∈ (Finset.univ.erase i), m j := by
          exact Finset.single_le_sum (fun x hx => Nat.zero_le (m x)) (by simp [hik])
        rw [← Finset.add_sum_erase Finset.univ (fun j : Fin n => m j) (Finset.mem_univ i)]
        omega
      omega
  · right
    have hall : ∀ i : Fin n, m i ≤ 1 := by
      intro i
      by_contra h
      have h2 : 2 ≤ m i := by omega
      exact hbig ⟨i, h2⟩
    have hsumsup : (∑ i ∈ m.support, m i) = 2 := by
      have hsub : m.support ⊆ Finset.univ := by intro k hk; simp
      have hs : (∑ i ∈ m.support, m i) = (∑ i : Fin n, m i) := by
        refine Finset.sum_subset hsub ?_
        intro k hk hknot
        exact Finsupp.notMem_support_iff.mp hknot
      rw [hs, hsum]
    have hsumones : (∑ i ∈ m.support, (1 : ℕ)) = 2 := by
      have heq : (∑ i ∈ m.support, m i) = ∑ i ∈ m.support, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : 0 < m k := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk)
        have hkle : m k ≤ 1 := hall k
        omega
      rw [← heq]
      exact hsumsup
    have hcard : m.support.card = 2 := by
      rw [Finset.card_eq_sum_ones]
      exact hsumones
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcard
    refine ⟨a, b, hab, ?_⟩
    apply Finsupp.ext
    intro k
    by_cases hka : k = a
    · subst k
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hab]
      have hpos : 0 < m a := Nat.pos_of_ne_zero (by
        have : a ∈ ({a, b} : Finset (Fin n)) := by simp
        have : a ∈ m.support := by simpa [hs] using this
        exact Finsupp.mem_support_iff.mp this)
      have hle : m a ≤ 1 := hall a
      omega
    · by_cases hkb : k = b
      · subst k
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hab), Finsupp.single_eq_same]
        have hpos : 0 < m b := Nat.pos_of_ne_zero (by
          have : b ∈ ({a, b} : Finset (Fin n)) := by simp
          have : b ∈ m.support := by simpa [hs] using this
          exact Finsupp.mem_support_iff.mp this)
        have hle : m b ≤ 1 := hall b
        omega
      · have hmem : k ∉ m.support := by
          intro hk
          have : k ∈ ({a, b} : Finset (Fin n)) := by simpa [hs] using hk
          simp [hka, hkb] at this
        have hk0 : m k = 0 := Finsupp.notMem_support_iff.mp hmem
        rw [hk0]
        simp [hka, hkb]

/-- `e_i + e_j = 2 e_k` iff `i = j = k`. -/
lemma single_add_single_eq_single_two_iff {n : ℕ} (i j k : Fin n) :
    Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single k 2 ↔ i = k ∧ j = k := by
  constructor
  · intro h
    have hik : i = k := by
      by_contra hik
      have hc := congrArg (fun f : Fin n →₀ ℕ => f i) h
      rw [Finsupp.add_apply] at hc
      rw [Finsupp.single_eq_same] at hc
      rw [Finsupp.single_eq_of_ne hik] at hc
      omega
    refine ⟨hik, ?_⟩
    by_contra hjk
    have hc := congrArg (fun f : Fin n →₀ ℕ => f j) h
    by_cases hij : i = j
    · exact hjk (Eq.trans (Eq.symm hij) hik)
    · rw [Finsupp.add_apply] at hc
      rw [Finsupp.single_eq_of_ne (Ne.symm hij)] at hc
      rw [Finsupp.single_eq_same] at hc
      rw [← hik] at hc
      rw [Finsupp.single_eq_of_ne (Ne.symm hij)] at hc
      omega
  · rintro ⟨hik, hjk⟩
    rw [hik, hjk]
    ext x
    by_cases h : x = k
    · subst x
      simp
    · simp [h]

/-- `2 e_k = e_k + e_k`. -/
lemma single_one_add_single_one {n : ℕ} (k : Fin n) :
    Finsupp.single k 1 + Finsupp.single k 1 = Finsupp.single k 2 := by
  ext x
  by_cases h : x = k
  · subst x
    simp
  · simp [h]

/-- `e_i + e_j` equals `e_{i'} + e_{j'}` exactly for the two pairings of `{i,j}`. -/
lemma single_add_single_eq_iff {n : ℕ} (i j i' j' : Fin n) (hij : i ≠ j) :
    Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single i' 1 + Finsupp.single j' 1 ↔
      (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) := by
  constructor
  · intro h
    by_cases hi'i : i' = i
    · left
      refine ⟨hi'i, ?_⟩
      by_cases hj'j : j' = j
      · exact hj'j
      · have hcj := congrArg (fun f : Fin n →₀ ℕ => f j) h
        simp [Finsupp.add_apply, hij, hi'i, hj'j] at hcj
    · right
      have hj'i : j' = i := by
        by_contra hj'i
        have hci := congrArg (fun f : Fin n →₀ ℕ => f i) h
        simp [Finsupp.add_apply, hij, hi'i, hj'i] at hci
      refine ⟨?_, hj'i⟩
      by_contra hi'j
      have hcj := congrArg (fun f : Fin n →₀ ℕ => f j) h
      simp [Finsupp.add_apply, hij, hj'i, hi'j] at hcj
  · rintro (⟨hi', hj'⟩ | ⟨hi', hj'⟩)
    · rw [hi', hj']
    · rw [hi', hj']
      rw [add_comm]

/-- The diagonal double sum that computes the coefficient of a square. -/
lemma sq_double_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
        A i j * (if Finsupp.single k 2 = Finsupp.single i 1 + Finsupp.single j 1 then (1 : ℝ) else 0))
      = A k k := by
  classical
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single k]
    · simp [single_one_add_single_one]
    · intro j hj hjk
      have hne : ¬ (Finsupp.single k 1 + Finsupp.single j 1 = Finsupp.single k 2) := by
        intro hh
        exact hjk ((single_add_single_eq_single_two_iff k j k).mp hh).2
      have hne' : ¬ (Finsupp.single k 2 = Finsupp.single k 1 + Finsupp.single j 1) := fun h => hne h.symm
      simp [hne']
    · intro hk
      exact False.elim (hk (Finset.mem_univ k))
  · intro i hi hik
    apply Finset.sum_eq_zero
    intro j hj
    have hne : ¬ (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single k 2) := by
      intro hh
      exact hik ((single_add_single_eq_single_two_iff i j k).mp hh).1
    have hne' : ¬ (Finsupp.single k 2 = Finsupp.single i 1 + Finsupp.single j 1) := fun h => hne h.symm
    simp [hne']
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

/-- The off-diagonal double sum that computes the coefficient of a cross term. -/
lemma cross_double_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∑ i' : Fin n, ∑ j' : Fin n,
        A i' j' * (if Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single i' 1 + Finsupp.single j' 1 then (1 : ℝ) else 0))
      = A i j + A j i := by
  classical
  let f : Fin n → ℝ := fun i' => ∑ j' : Fin n,
        A i' j' * (if Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single i' 1 + Finsupp.single j' 1 then (1 : ℝ) else 0)
  have hfi : f i = A i j := by
    dsimp [f]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' hj' hj'j
      have hne : ¬ (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single i 1 + Finsupp.single j' 1) := by
        intro hh
        rcases (single_add_single_eq_iff i j i j' hij).mp hh with h | h
        · exact hj'j h.2
        · exact hij h.1
      simp [hne]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  have hfj : f j = A j i := by
    dsimp [f]
    rw [Finset.sum_eq_single i]
    · simp [add_comm]
    · intro j' hj' hj'i
      have hne : ¬ (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single j 1 + Finsupp.single j' 1) := by
        intro hh
        rcases (single_add_single_eq_iff i j j j' hij).mp hh with h | h
        · exfalso
          exact hij h.1.symm
        · exact hj'i h.2
      simp [hne]
    · intro hj
      exact False.elim (hj (Finset.mem_univ i))
  have hzero : ∀ i' : Fin n, i' ∉ ({i, j} : Finset (Fin n)) → f i' = 0 := by
    intro i' hi'
    dsimp [f]
    apply Finset.sum_eq_zero
    intro j' hj'
    have hne : ¬ (Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single i' 1 + Finsupp.single j' 1) := by
      intro hh
      rcases (single_add_single_eq_iff i j i' j' hij).mp hh with h | h
      · exact hi' (by simp [h.1])
      · exact hi' (by simp [h.1])
    simp [hne]
  calc
    (∑ i' : Fin n, ∑ j' : Fin n,
        A i' j' * (if Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single i' 1 + Finsupp.single j' 1 then (1 : ℝ) else 0))
        = ∑ i' : Fin n, f i' := by rfl
    _ = f i + f j := by
        have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := by intro x hx; simp
        have hs := Finset.sum_subset hsub (by intro x hx hx0; exact hzero x hx0)
        rw [← hs]
        rw [Finset.sum_pair hij]
    _ = A i j + A j i := by rw [hfi, hfj]

/-- coefficient of a monomial in a product `X_i * X_j`. -/
lemma coeff_X_mul_X {n : ℕ} (m : Fin n →₀ ℕ) (i j : Fin n) :
    MvPolynomial.coeff m (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) ℝ) =
      if m = Finsupp.single i 1 + Finsupp.single j 1 then (1 : ℝ) else 0 := by
  classical
  rw [MvPolynomial.X, MvPolynomial.X]
  rw [monomial_mul]
  rw [MvPolynomial.coeff_monomial]
  by_cases h : m = Finsupp.single i 1 + Finsupp.single j 1
  · simp [h]
  · have h' : ¬ (Finsupp.single i 1 + Finsupp.single j 1) = m := by
      intro hh; exact h hh.symm
    simp [h, h']

/-! The dictionary between degree-two homogeneous polynomials and matrices. -/

/-- monomial `X_i * X_j` as an element of the space of degree-2 homogeneous polynomials -/
def quadricMonomial (n : ℕ) (i j : Fin n) : H n 2 where
  val := MvPolynomial.X i * MvPolynomial.X j
  property := by
    rw [mem_homogeneousSubmodule]
    exact (isHomogeneous_X (σ := Fin n) (R := ℝ) i).mul (isHomogeneous_X (σ := Fin n) (R := ℝ) j)

/-- The degree-two homogeneous polynomial with Hessian `(A + Aᵀ)/2`. -/
def quadricOfMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : H n 2 :=
  (1 / 2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n, (A i j) • quadricMonomial n i j)

/-- coefficient functional on the degree-`d` space -/
def coeffH (n d : ℕ) (m : Fin n →₀ ℕ) : H n d →ₗ[ℝ] ℝ where
  toFun := fun x => MvPolynomial.coeff m x.1
  map_add' := by
    intro x y
    show MvPolynomial.coeff m (x.1 + y.1) = MvPolynomial.coeff m x.1 + MvPolynomial.coeff m y.1
    rw [MvPolynomial.coeff_add]
  map_smul' := by
    intro r x
    show MvPolynomial.coeff m (r • x.1) = r * MvPolynomial.coeff m x.1
    rw [MvPolynomial.coeff_smul, smul_eq_mul]

lemma coeffH_apply (n d : ℕ) (m : Fin n →₀ ℕ) (x : H n d) :
    coeffH n d m x = MvPolynomial.coeff m x.1 := rfl

lemma coeffH_quadricMonomial (n : ℕ) (m : Fin n →₀ ℕ) (i j : Fin n) :
    coeffH n 2 m (quadricMonomial n i j) =
      if m = Finsupp.single i 1 + Finsupp.single j 1 then (1 : ℝ) else 0 := by
  classical
  rw [coeffH_apply]
  exact coeff_X_mul_X m i j

/-- coefficient of `quadricOfMatrix A` at `m` -/
lemma quadricOfMatrix_coeff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (quadricOfMatrix n A).1 = (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
      A i j * (if m = Finsupp.single i 1 + Finsupp.single j 1 then (1 : ℝ) else 0) := by
  classical
  rw [← coeffH_apply]
  unfold quadricOfMatrix
  rw [map_smul]
  rw [map_sum]
  apply congrArg (fun x : ℝ => (1 / 2 : ℝ) • x)
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, coeffH_quadricMonomial]
  simp [smul_eq_mul]

/-- coefficient of a square monomial -/
lemma quadricOfMatrix_coeff_sq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    MvPolynomial.coeff (Finsupp.single k 2) (quadricOfMatrix n A).1 = (1 / 2 : ℝ) * A k k := by
  classical
  rw [quadricOfMatrix_coeff]
  congr 1
  exact sq_double_sum A k

/-- coefficient of a cross monomial -/
lemma quadricOfMatrix_coeff_cross (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) (quadricOfMatrix n A).1 =
      (1 / 2 : ℝ) * (A i j + A j i) := by
  classical
  rw [quadricOfMatrix_coeff]
  congr 1
  exact cross_double_sum A i j hij

/-- `quadricOfMatrix` depends continuously on the matrix. -/
lemma continuous_quadricOfMatrix (n : ℕ) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => quadricOfMatrix n A) := by
  classical
  unfold quadricOfMatrix
  fun_prop

/-- Hessian of the matrix quadratic. -/
lemma hessian_quadricOfMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (quadricOfMatrix n A).hessian = (1 / 2 : ℝ) • (A + A.transpose) := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    rw [H.hessian]
    rw [if_pos rfl]
    rw [quadricOfMatrix_coeff_sq n A i]
    rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
    ring
  · rw [H.hessian]
    rw [if_neg h]
    rw [quadricOfMatrix_coeff_cross n A h]
    rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
    ring

/-- Hessian of the matrix quadratic, for symmetric `A`. -/
lemma hessian_quadricOfMatrix_symm (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (quadricOfMatrix n A).hessian = A := by
  rw [hessian_quadricOfMatrix]
  ext i j
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hsymm : A j i = A i j := (Matrix.IsSymm.ext_iff.mp hA) i j
  rw [hsymm]
  ring

/-- `weight 1 (single i b) = b`. -/
lemma weight_one_single {n : ℕ} (i : Fin n) (b : ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single i b) = b := by
  rw [Finsupp.weight_single]
  simp

/-- `weight 1 (e_i + e_j) = 2`. -/
lemma weight_one_single_add {n : ℕ} (i j : Fin n) :
    Finsupp.weight (1 : Fin n → ℕ) (Finsupp.single i 1 + Finsupp.single j 1) = 2 := by
  rw [map_add (Finsupp.weight (1 : Fin n → ℕ)), weight_one_single, weight_one_single]

/-- Coefficients of `quadricOfMatrix` vanish away from degree two. -/
lemma quadricOfMatrix_coeff_zero_of_weight_ne_two (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n →₀ ℕ) (hm : Finsupp.weight (1 : Fin n → ℕ) m ≠ 2) :
    MvPolynomial.coeff m (quadricOfMatrix n A).1 = 0 := by
  classical
  rw [quadricOfMatrix_coeff]
  have hzero : (∑ i : Fin n, ∑ j : Fin n,
      A i j * (if m = Finsupp.single i 1 + Finsupp.single j 1 then (1 : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hne : ¬ (m = Finsupp.single i 1 + Finsupp.single j 1) := by
      intro h
      apply hm
      rw [h]
      exact weight_one_single_add i j
    simp [hne]
  rw [hzero]
  ring

/-- Coefficients of a homogeneous degree-two polynomial vanish away from degree two. -/
lemma coeff_homogeneous_zero_of_weight_ne_two {n : ℕ} (f : H n 2)
    (m : Fin n →₀ ℕ) (hm : Finsupp.weight (1 : Fin n → ℕ) m ≠ 2) :
    MvPolynomial.coeff m f.1 = 0 := by
  have hh : f.1.IsWeightedHomogeneous (1 : Fin n → ℕ) 2 := by
    simpa [MvPolynomial.IsHomogeneous] using f.2
  exact MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero hh m hm

/-- Hessian diagonal entries in terms of coefficients. -/
lemma hessian_apply_sq (n : ℕ) (f : H n 2) (k : Fin n) :
    f.hessian k k = 2 * MvPolynomial.coeff (Finsupp.single k 2) f.1 := by
  rw [H.hessian]
  rw [if_pos rfl]

/-- Hessian off-diagonal entries in terms of coefficients. -/
lemma hessian_apply_cross (n : ℕ) (f : H n 2) {i j : Fin n} (hij : i ≠ j) :
    f.hessian i j = MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) f.1 := by
  rw [H.hessian]
  rw [if_neg hij]

/-- The Hessian of a homogeneous quadratic is symmetric. -/
lemma hessian_symm (n : ℕ) (f : H n 2) : (f.hessian).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm h
    rw [hessian_apply_cross n f h]
    rw [hessian_apply_cross n f hji]
    congr 1
    exact add_comm (Finsupp.single j 1) (Finsupp.single i 1)

/-- `quadricOfMatrix (hessian f) = f`; every homogeneous quadratic is the matrix quadratic of
its Hessian. -/
lemma quadricOfMatrix_hessian (n : ℕ) (f : H n 2) : quadricOfMatrix n f.hessian = f := by
  classical
  apply Subtype.ext
  ext m
  by_cases hm : Finsupp.weight (1 : Fin n → ℕ) m = 2
  · rcases weight_two_decompose hm with ⟨k, rfl⟩ | ⟨i, j, hij, rfl⟩
    · rw [quadricOfMatrix_coeff_sq]
      rw [hessian_apply_sq]
      ring
    · rw [quadricOfMatrix_coeff_cross n _ hij]
      rw [hessian_apply_cross n f hij]
      rw [hessian_apply_cross n f (Ne.symm hij)]
      have hcd : MvPolynomial.coeff (Finsupp.single j 1 + Finsupp.single i 1) f.1 =
          MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) f.1 := by
        congr 1
        exact add_comm (Finsupp.single j 1) (Finsupp.single i 1)
      rw [hcd]
      ring
  · rw [quadricOfMatrix_coeff_zero_of_weight_ne_two n f.hessian m hm]
    rw [coeff_homogeneous_zero_of_weight_ne_two f m hm]

/-- Positive coefficients iff positive Hessian entries (for a homogeneous quadratic). -/
lemma mem_P_iff_hessian_pos (n : ℕ) (f : H n 2) : f ∈ P n 2 ↔ ∀ i j : Fin n, 0 < f.hessian i j := by
  classical
  constructor
  · intro hf i j
    by_cases h : i = j
    · subst j
      rw [hessian_apply_sq n f i]
      have hc : 0 < MvPolynomial.coeff (Finsupp.single i 2) f.1 := hf (Finsupp.single i 2) (weight_one_single i 2)
      positivity
    · rw [hessian_apply_cross n f h]
      exact hf (Finsupp.single i 1 + Finsupp.single j 1) (weight_one_single_add i j)
  · intro hf m hm
    rcases weight_two_decompose hm with ⟨k, rfl⟩ | ⟨i, j, hij, rfl⟩
    · have hsq := hessian_apply_sq n f k
      have hpos : 0 < f.hessian k k := hf k k
      rw [hsq] at hpos
      nlinarith
    · rw [← hessian_apply_cross n f hij]
      exact hf i j

/-- The matrix quadratic of a strictly positive matrix lies in `P`. -/
lemma quadricOfMatrix_mem_P_of_pos (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j : Fin n, 0 < B i j) :
    quadricOfMatrix n B ∈ P n 2 := by
  rw [mem_P_iff_hessian_pos]
  intro i j
  rw [hessian_quadricOfMatrix]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  have hpos : 0 < B i j + B j i := add_pos (hB i j) (hB j i)
  positivity

/-- Strictly Lorentzian matrices produce strictly Lorentzian quadratics. -/
lemma quadricOfMatrix_mem_Ŀ_of_strict (n : ℕ) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsSymm) (hpos : ∀ i j : Fin n, 0 < B i j) (hunit : IsUnit B)
    (hcard : (B.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1) :
    quadricOfMatrix n B ∈ Ŀ n 2 := by
  classical
  simp [Ŀ]
  constructor
  · exact quadricOfMatrix_mem_P_of_pos n B hpos
  · constructor
    · rw [hessian_quadricOfMatrix_symm n B hB]
      exact hunit
    · rw [hessian_quadricOfMatrix_symm n B hB]
      exact hcard

/-- Strict Lorentzian matrix set. -/
def strictQuadM (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ (∀ i j : Fin n, 0 < A i j) ∧ IsUnit A ∧
    (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1}

/-- Stable Lorentzian matrix set. -/
def stableQuadM (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ (∀ i j : Fin n, 0 ≤ A i j) ∧
    (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1}

/-- The closure theorem for matrices. -/
lemma closure_strictQuadM_eq_stableQuadM (n : ℕ) (hn : 0 < n) :
    closure (strictQuadM n) = stableQuadM n := by
  classical
  simpa [strictQuadM, stableQuadM] using Commons.LinearAlgebra.Matrix.closure_strict_lorentzian_quadratic n hn

lemma hessian_nonneg_of_coeff_nonneg (n : ℕ) (f : H n 2)
    (hcoeff : ∀ m : Fin n →₀ ℕ, 0 ≤ MvPolynomial.coeff m f.1) :
    ∀ i j : Fin n, 0 ≤ f.hessian i j := by
  intro i j
  by_cases h : i = j
  · subst j
    rw [hessian_apply_sq]
    nlinarith [hcoeff (Finsupp.single i 2)]
  · rw [hessian_apply_cross n f h]
    exact hcoeff (Finsupp.single i 1 + Finsupp.single j 1)

/-- a member of S has its Hessian in the stable matrix set -/
lemma hessian_mem_stableQuadM_of_mem_S (n : ℕ) (f : H n 2) (hf : f ∈ S n 2) :
    f.hessian ∈ stableQuadM n := by
  classical
  rcases hf with ⟨hfst, hcoeff⟩
  have hnn : ∀ i j : Fin n, 0 ≤ f.hessian i j := hessian_nonneg_of_coeff_nonneg n f hcoeff
  have hsymm : f.hessian.IsSymm := hessian_symm n f
  -- stability branch:
  have hleft : f.hessian = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        (∑ i : Fin n, ∑ j : Fin n, f.hessian i j * (z i : ℂ) * (z j : ℂ)) ≠ 0 := by
    rcases hfst with hz | hstable
    · left
      ext i j
      by_cases h : i = j
      · subst j
        rw [hessian_apply_sq]
        rw [hz]
        simp
      · rw [hessian_apply_cross n f h]
        rw [hz]
        simp
    · right
      intro z
      by_contra hz0
      have hsum : (∑ i : Fin n, ∑ j : Fin n, f.hessian i j * (z i : ℂ) * (z j : ℂ)) = 0 := hz0
      have hq := hessian_aeval_eq_challenge n f (fun i : Fin n => (z i : ℂ))
      have hzero2 : 2 * MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) f.1 = 0 := by
        rw [hq]
        exact hsum
      have haeval0 : MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) f.1 = 0 := by
        exact (mul_eq_zero.mp hzero2).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
      have hst := hstable z
      -- hst : aeval (((↑) : ℍ → ℂ) ∘ z) f.1 ≠ 0
      have haeval0' : MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) f.1 = 0 := by
        simpa [Function.comp_def] using haeval0
      exact hst haeval0'
  have hcard : (f.hessian.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 := by
    exact (Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one f.hessian hsymm hnn).mp hleft
  exact ⟨hsymm, hnn, hcard⟩

/-- every member of S is approximated by strictly Lorentzian quadratics -/
lemma mem_closure_Ŀ_of_mem_S (n : ℕ) (hn : 0 < n) (f : H n 2) (hf : f ∈ S n 2) :
    f ∈ closure (Ŀ n 2) := by
  classical
  let A := f.hessian
  have hA : A ∈ stableQuadM n := by
    simpa [A] using hessian_mem_stableQuadM_of_mem_S n f hf
  have hAcl : A ∈ closure (strictQuadM n) := by
    rw [closure_strictQuadM_eq_stableQuadM n hn]
    exact hA
  have hcont : Continuous (fun B : Matrix (Fin n) (Fin n) ℝ => quadricOfMatrix n B) :=
    continuous_quadricOfMatrix n
  have himg : (fun B : Matrix (Fin n) (Fin n) ℝ => quadricOfMatrix n B) '' closure (strictQuadM n)
      ⊆ closure ((fun B : Matrix (Fin n) (Fin n) ℝ => quadricOfMatrix n B) '' strictQuadM n) :=
    image_closure_subset_closure_image hcont
  have hmem1 : quadricOfMatrix n A ∈ closure ((fun B : Matrix (Fin n) (Fin n) ℝ => quadricOfMatrix n B) '' strictQuadM n) := by
    exact himg ⟨A, hAcl, rfl⟩
  have hsub : (fun B : Matrix (Fin n) (Fin n) ℝ => quadricOfMatrix n B) '' strictQuadM n ⊆ Ŀ n 2 := by
    rintro g ⟨B, hB, rfl⟩
    rcases hB with ⟨hBsymm, hBpos, hBunit, hBcard⟩
    exact quadricOfMatrix_mem_Ŀ_of_strict n hBsymm hBpos hBunit hBcard
  have hmem2 : quadricOfMatrix n A ∈ closure (Ŀ n 2) := closure_mono hsub hmem1
  have hfeq : f = quadricOfMatrix n A := by
    simpa [A] using (quadricOfMatrix_hessian n f).symm
  rwa [hfeq]

/-- Strictly Lorentzian quadratics are dense in the stable quadratics (degree two case of
Theorem 2.25). -/
theorem closure_strict_eq_L_of_degree_le_two (n : ℕ) (hn : 0 < n) :
    closure (Ŀ n 2) = L n 2 := by
  classical
  change closure (Ŀ n 2) = S n 2
  apply subset_antisymm
  · exact (S_closed n 2).closure_subset_iff.mpr (strict_subset_L n 2 hn)
  · intro f hf
    exact mem_closure_Ŀ_of_mem_S n hn f hf

end

end Commons.LorentzianPolynomials
