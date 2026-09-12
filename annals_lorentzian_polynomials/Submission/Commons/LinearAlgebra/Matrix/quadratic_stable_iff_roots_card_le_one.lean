import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

open Matrix Polynomial UpperHalfPlane
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

def quadReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * (x i * y j)

def quadComplex {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * (z i) * (z j)

-- lemmas copied/shortened from previous temp files:
lemma quadReal_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    quadReal A x y = x ⬝ᵥ A *ᵥ y := by
  classical
  dsimp [quadReal, dotProduct, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma quadReal_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x y : Fin n → ℝ) :
    quadReal A x y = quadReal A y x := by
  classical
  dsimp [quadReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hA.apply i j]
  ring

lemma inner_toEuclideanLin_eq_quadReal_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    inner ℝ (A.toEuclideanLin (WithLp.toLp 2 x)) (WithLp.toLp 2 y) = quadReal A y x := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.toLpLin_apply, quadReal_mulVec]

lemma inner_toEuclideanLin_eq_quadReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x y : Fin n → ℝ) :
    inner ℝ (A.toEuclideanLin (WithLp.toLp 2 x)) (WithLp.toLp 2 y) = quadReal A x y := by
  rw [inner_toEuclideanLin_eq_quadReal_symm]
  exact quadReal_symm A hA y x

lemma inner_eigen_sum {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (u v : E) :
    inner ℝ (T u) v = ∑ i : Fin n,
      (LinearMap.IsSymmetric.eigenvalues hT hn i) *
        (((LinearMap.IsSymmetric.eigenvectorBasis hT hn).repr u).ofLp i *
          ((LinearMap.IsSymmetric.eigenvectorBasis hT hn).repr v).ofLp i) := by
  classical
  let b : OrthonormalBasis (Fin n) ℝ E := (LinearMap.IsSymmetric.eigenvectorBasis hT hn)
  change inner ℝ (T u) v = ∑ i : Fin n,
      (LinearMap.IsSymmetric.eigenvalues hT hn i) *
        (((b.repr u).ofLp i) * ((b.repr v).ofLp i))
  rw [← b.repr.inner_map_map (T u) v]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag := LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply hT hn u i
  dsimp [b] at hdiag ⊢
  rw [hdiag]
  ring

lemma quadReal_eq_eigen_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x y : Fin n → ℝ) :
    quadReal A x y = ∑ i : Fin n,
      (LinearMap.IsSymmetric.eigenvalues
        (T := A.toEuclideanLin)
        (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
        (by simp [finrank_euclideanSpace]) i) *
        ((((LinearMap.IsSymmetric.eigenvectorBasis
          (T := A.toEuclideanLin)
          (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
          (by simp [finrank_euclideanSpace])).repr (WithLp.toLp 2 x)).ofLp i) *
          (((LinearMap.IsSymmetric.eigenvectorBasis
          (T := A.toEuclideanLin)
          (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
          (by simp [finrank_euclideanSpace])).repr (WithLp.toLp 2 y)).ofLp i)) := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (Matrix.isHermitian_iff_isSymm).2 hA
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  change quadReal A x y = ∑ i : Fin n,
      (LinearMap.IsSymmetric.eigenvalues hT hn i) *
        ((((LinearMap.IsSymmetric.eigenvectorBasis hT hn).repr (WithLp.toLp 2 x)).ofLp i) *
          (((LinearMap.IsSymmetric.eigenvectorBasis hT hn).repr (WithLp.toLp 2 y)).ofLp i))
  rw [← inner_toEuclideanLin_eq_quadReal A hA x y]
  exact inner_eigen_sum T hT hn (WithLp.toLp 2 x) (WithLp.toLp 2 y)

lemma quadComplex_eq_quadReal_sub_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) :
    quadComplex A z =
      (((quadReal A (fun i => (z i).re) (fun i => (z i).re) -
        quadReal A (fun i => (z i).im) (fun i => (z i).im) : ℝ) : ℂ)
      + Complex.I * ((quadReal A (fun i => (z i).re) (fun i => (z i).im) +
        quadReal A (fun i => (z i).im) (fun i => (z i).re) : ℝ) : ℂ)) := by
  classical
  dsimp [quadComplex]
  apply Complex.ext
  · simp [quadReal, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring_nf
  · simp [quadReal, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    simp_rw [Finset.sum_add_distrib]
    ring_nf

lemma quadComplex_eq_zero_of_re_im {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ)
    (hre : quadReal A x x - quadReal A y y = 0)
    (him : quadReal A x y + quadReal A y x = 0) :
    quadComplex A (fun i => (x i : ℂ) + Complex.I * (y i : ℂ)) = 0 := by
  classical
  have hdecomp := quadComplex_eq_quadReal_sub_add A (fun i => (x i : ℂ) + Complex.I * (y i : ℂ))
  have hre' : quadReal A (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).re) (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).re)
      - quadReal A (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).im) (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).im) = 0 := by
    simpa using hre
  have him' : quadReal A (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).re) (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).im)
      + quadReal A (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).im) (fun i => ((x i : ℂ) + Complex.I * (y i : ℂ)).re) = 0 := by
    simpa using him
  rw [hdecomp, hre', him']
  simp

lemma quad_pos_of_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ A i j) (hAne : A ≠ 0) {y : Fin n → ℝ} (hy : ∀ i, 0 < y i) :
    0 < ∑ i : Fin n, ∑ j : Fin n, A i j * (y i * y j) := by
  classical
  have hnot : ¬ ∀ i j, A i j = 0 := by
    intro h
    apply hAne
    ext i j
    exact h i j
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  obtain ⟨j, hj⟩ := not_forall.mp hi
  have hAij_pos : 0 < A i j := lt_of_le_of_ne' (hnn i j) hj
  have hyij_pos : 0 < y i * y j := mul_pos (hy i) (hy j)
  have hterm_pos : 0 < A i j * (y i * y j) := mul_pos hAij_pos hyij_pos
  have hinner_nonneg : ∀ k : Fin n, 0 ≤ ∑ j : Fin n, A k j * (y k * y j) := by
    intro k
    apply Finset.sum_nonneg
    intro l hl
    exact mul_nonneg (hnn k l) (mul_pos (hy k) (hy l)).le
  have hinner_pos_i : 0 < ∑ j : Fin n, A i j * (y i * y j) := by
    refine Finset.sum_pos' (fun k hk => mul_nonneg (hnn i k) (mul_pos (hy i) (hy k)).le) ?_
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simpa using hterm_pos
  refine Finset.sum_pos' (fun k hk => hinner_nonneg k) ?_
  exact ⟨i, Finset.mem_univ i, hinner_pos_i⟩

lemma charpoly_positive_roots_card_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
      (Finset.univ.filter (fun i : Fin n => 0 <
        (LinearMap.IsSymmetric.eigenvalues
          (T := A.toEuclideanLin)
          (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
          (by simp [finrank_euclideanSpace]) i))).card := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (Matrix.isHermitian_iff_isSymm).2 hA
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  have hchar : T.charpoly = A.charpoly := by
    dsimp [T]
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_eq_toLin, Matrix.charpoly_toLin]
  have hroots := LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues (T := T) hT hn
  calc
    (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card
        = (T.charpoly.roots.filter (fun r : ℝ => 0 < r)).card := by rw [hchar]
    _ = (Finset.univ.filter (fun i : Fin n => 0 < hT.eigenvalues hn i)).card := by
        rw [hroots]
        rw [Multiset.filter_map, Multiset.card_map]
        change (Multiset.filter ((fun r : ℝ => 0 < r) ∘ hT.eigenvalues hn) Finset.univ.val).card =
          (Finset.univ.filter (fun i : Fin n => 0 < hT.eigenvalues hn i)).val.card
        rw [Finset.filter_val]
        rfl

noncomputable def symmEigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) : Fin n → ℝ :=
  LinearMap.IsSymmetric.eigenvalues
    (T := A.toEuclideanLin)
    (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
    (by simp [finrank_euclideanSpace])

noncomputable def symmBasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.IsSymmetric.eigenvectorBasis
    (T := A.toEuclideanLin)
    (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
    (by simp [finrank_euclideanSpace])

noncomputable def symmYCoord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (i : Fin n) : ℝ :=
  ((symmBasis A hA).repr (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)))).ofLp i

lemma quadReal_eq_eigen_sum' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x y : Fin n → ℝ) :
    quadReal A x y = ∑ i : Fin n,
      (symmEigenvalues A hA i) *
        ((((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i) *
          (((symmBasis A hA).repr (WithLp.toLp 2 y)).ofLp i)) := by
  simpa [symmEigenvalues, symmBasis] using quadReal_eq_eigen_sum A hA x y

lemma quadReal_of_eigen_coord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (a : Fin n → ℝ) :
    ∃ x : Fin n → ℝ,
      quadReal A x (fun _ : Fin n => (1 : ℝ)) =
        ∑ i : Fin n, (symmEigenvalues A hA i) * (a i * symmYCoord A hA i) ∧
      quadReal A x x = ∑ i : Fin n, (symmEigenvalues A hA i) * (a i * a i) := by
  classical
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := symmBasis A hA
  let ey : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))
  let ex : EuclideanSpace ℝ (Fin n) := b.repr.symm (WithLp.toLp 2 a)
  let x : Fin n → ℝ := fun i => ex.ofLp i
  refine ⟨x, ?_, ?_⟩
  · have hq := quadReal_eq_eigen_sum' A hA x (fun _ : Fin n => (1 : ℝ))
    have htoLp : WithLp.toLp 2 x = ex := by
      apply (WithLp.ext_iff (p := 2)).mpr
      funext i
      simp [x, ex]
    have hcoord_x : ∀ i : Fin n, ((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i = a i := by
      intro i
      rw [htoLp]
      simp [b, ex]
    have hcoord_y : ∀ i : Fin n,
        ((symmBasis A hA).repr (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)))).ofLp i =
          symmYCoord A hA i := by
      intro i
      rfl
    simpa [hcoord_x, hcoord_y] using hq
  · have hq := quadReal_eq_eigen_sum' A hA x x
    have htoLp : WithLp.toLp 2 x = ex := by
      apply (WithLp.ext_iff (p := 2)).mpr
      funext i
      simp [x, ex]
    have hcoord_x : ∀ i : Fin n, ((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i = a i := by
      intro i
      rw [htoLp]
      simp [b, ex]
    simpa [hcoord_x] using hq

lemma sum_two_update_mul {n : ℕ} {p q : Fin n} (hpq : p ≠ q) (ap aq : ℝ)
    (g : Fin n → ℝ) :
    (∑ i : Fin n, (Function.update (Function.update (0 : Fin n → ℝ) p ap) q aq) i * g i)
      = ap * g p + aq * g q := by
  classical
  let a : Fin n → ℝ := Function.update (Function.update (0 : Fin n → ℝ) p ap) q aq
  change (∑ i : Fin n, a i * g i) = ap * g p + aq * g q
  have hq : a q = aq := by simp [a]
  have hp : a p = ap := by simp [a, hpq]
  have htail : ∀ i : Fin n, i ≠ p → i ≠ q → a i = 0 := by
    intro i hip hiq
    simp [a, hip, hiq]
  let t : Finset (Fin n) := Finset.univ.erase q
  have hsum1 : (∑ i : Fin n, a i * g i) = a q * g q + ∑ i ∈ t, a i * g i := by
    rw [← Finset.add_sum_erase Finset.univ (fun i => a i * g i) (Finset.mem_univ q)]
  have hsum2 : (∑ i ∈ t, a i * g i) = a p * g p + ∑ i ∈ t.erase p, a i * g i := by
    have hp_mem : p ∈ t := by simp [t, hpq]
    rw [← Finset.add_sum_erase t (fun i => a i * g i) hp_mem]
  have htail_sum : (∑ i ∈ t.erase p, a i * g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiq : i ≠ q := by
      have : i ∈ t := Finset.mem_of_mem_erase hi
      simpa [t] using this
    have hip : i ≠ p := (Finset.mem_erase.mp hi).1
    rw [htail i hip hiq]
    simp
  rw [hsum1, hsum2, htail_sum, hq, hp]
  ring

lemma two_pos_sq {lam_p lam_q bp bq : ℝ} (hlam_p : 0 < lam_p) (hlam_q : 0 < lam_q)
    (hnot : bp ≠ 0 ∨ bq ≠ 0) :
    0 < lam_p * (lam_q * bq) ^ 2 + lam_q * (lam_p * bp) ^ 2 := by
  have h1 : 0 ≤ lam_p * (lam_q * bq) ^ 2 := mul_nonneg hlam_p.le (sq_nonneg _)
  have h2 : 0 ≤ lam_q * (lam_p * bp) ^ 2 := mul_nonneg hlam_q.le (sq_nonneg _)
  have hsum_nonneg : 0 ≤ lam_p * (lam_q * bq) ^ 2 + lam_q * (lam_p * bp) ^ 2 := add_nonneg h1 h2
  have hsum_ne : lam_p * (lam_q * bq) ^ 2 + lam_q * (lam_p * bp) ^ 2 ≠ 0 := by
    intro h
    have hterm1 : lam_p * (lam_q * bq) ^ 2 = 0 := by nlinarith [h1, h2]
    have hterm2 : lam_q * (lam_p * bp) ^ 2 = 0 := by nlinarith [h1, h2]
    have hbq : bq = 0 := by
      have hsq : (lam_q * bq) ^ 2 = 0 := (mul_eq_zero.mp hterm1).resolve_left (ne_of_gt hlam_p)
      have hmul : lam_q * bq = 0 := sq_eq_zero_iff.mp hsq
      exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hlam_q)
    have hbp : bp = 0 := by
      have hsq : (lam_p * bp) ^ 2 = 0 := (mul_eq_zero.mp hterm2).resolve_left (ne_of_gt hlam_q)
      have hmul : lam_p * bp = 0 := sq_eq_zero_iff.mp hsq
      exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hlam_p)
    rcases hnot with hbp_ne | hbq_ne
    · exact hbp_ne hbp
    · exact hbq_ne hbq
  exact lt_of_le_of_ne' hsum_nonneg hsum_ne

lemma exists_coord_cross_zero_of_two_pos {n : ℕ} (lam b : Fin n → ℝ)
    (hcard : 2 ≤ (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card) :
    ∃ a : Fin n → ℝ,
      (∑ i : Fin n, lam i * (a i * b i)) = 0 ∧
      0 < ∑ i : Fin n, lam i * (a i * a i) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => 0 < lam i)
  have h1 : 1 < s.card := by dsimp [s]; omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
  have hp_pos : 0 < lam p := by
    have := (Finset.mem_filter.mp hp).2
    simpa [s] using this
  have hq_pos : 0 < lam q := by
    have := (Finset.mem_filter.mp hq).2
    simpa [s] using this
  by_cases hboth : b p = 0 ∧ b q = 0
  · let a : Fin n → ℝ := Function.update (Function.update (0 : Fin n → ℝ) p 1) q 0
    refine ⟨a, ?_, ?_⟩
    · have hsum := sum_two_update_mul hpq 1 0 (fun i => lam i * b i)
      have hrewrite : (∑ i : Fin n, lam i * (a i * b i)) =
          ∑ i : Fin n, a i * (lam i * b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hrewrite]
      have hsum' : (∑ i : Fin n, a i * (lam i * b i)) = lam p * b p := by
        simpa [a, hpq, hboth.1, hboth.2] using hsum
      rw [hsum', hboth.1]
      simp
    · have hsum := sum_two_update_mul hpq 1 0 (fun i => lam i * a i)
      have hrewrite : (∑ i : Fin n, lam i * (a i * a i)) =
          ∑ i : Fin n, a i * (lam i * a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hrewrite]
      have hsum' : (∑ i : Fin n, a i * (lam i * a i)) = lam p := by
        simpa [a, hpq] using hsum
      rw [hsum']
      exact hp_pos
  · let ap : ℝ := lam q * b q
    let aq : ℝ := - lam p * b p
    let a : Fin n → ℝ := Function.update (Function.update (0 : Fin n → ℝ) p ap) q aq
    refine ⟨a, ?_, ?_⟩
    · have hsum := sum_two_update_mul hpq ap aq (fun i => lam i * b i)
      have hrewrite : (∑ i : Fin n, lam i * (a i * b i)) =
          ∑ i : Fin n, a i * (lam i * b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hrewrite]
      have hsum' : (∑ i : Fin n, a i * (lam i * b i)) =
          ap * (lam p * b p) + aq * (lam q * b q) := by
        simpa [a, hpq] using hsum
      rw [hsum']
      dsimp [ap, aq]
      ring
    · have hsum := sum_two_update_mul hpq ap aq (fun i => lam i * a i)
      have hrewrite : (∑ i : Fin n, lam i * (a i * a i)) =
          ∑ i : Fin n, a i * (lam i * a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hrewrite]
      have hsum' : (∑ i : Fin n, a i * (lam i * a i)) =
          ap * (lam p * ap) + aq * (lam q * aq) := by
        simpa [a, hpq] using hsum
      rw [hsum']
      have hnot : b p ≠ 0 ∨ b q ≠ 0 := by
        by_contra h
        apply hboth
        exact ⟨not_not.mp (not_or.mp h).1, not_not.mp (not_or.mp h).2⟩
      have hpos := two_pos_sq hp_pos hq_pos hnot
      dsimp [ap, aq]
      nlinarith [hpos]

lemma scale_coord_cross_zero {n : ℕ} (lam a b : Fin n → ℝ)
    (hcross : (∑ i : Fin n, lam i * (a i * b i)) = 0)
    (hpos : 0 < ∑ i : Fin n, lam i * (a i * a i))
    (hypos : 0 < ∑ i : Fin n, lam i * (b i * b i)) :
    ∃ a' : Fin n → ℝ,
      (∑ i : Fin n, lam i * (a' i * b i)) = 0 ∧
      (∑ i : Fin n, lam i * (a' i * a' i)) = ∑ i : Fin n, lam i * (b i * b i) := by
  classical
  let Sa : ℝ := ∑ i : Fin n, lam i * (a i * a i)
  let Sb : ℝ := ∑ i : Fin n, lam i * (b i * b i)
  have hSa_pos : 0 < Sa := by simpa [Sa] using hpos
  have hSb_pos : 0 < Sb := by simpa [Sb] using hypos
  let c : ℝ := Real.sqrt (Sb / Sa)
  refine ⟨fun i => c * a i, ?_, ?_⟩
  · have hsum_mul : (∑ i : Fin n, lam i * ((c * a i) * b i)) =
        c * ∑ i : Fin n, lam i * (a i * b i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum_mul, hcross]
    simp
  · have hsum_sq : (∑ i : Fin n, lam i * ((c * a i) * (c * a i))) =
        c ^ 2 * Sa := by
      dsimp [Sa]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hc_sq : c ^ 2 = Sb / Sa := by
      dsimp [c]
      exact Real.sq_sqrt (div_nonneg hSb_pos.le hSa_pos.le)
    calc
      (∑ i : Fin n, lam i * ((c * a i) * (c * a i))) = c ^ 2 * Sa := hsum_sq
      _ = Sb := by
          rw [hc_sq]
          field_simp [ne_of_gt hSa_pos]

lemma exists_upper_half_plane_zero_of_two_pos_roots {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hcard : 2 ≤ (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card) :
    ∃ z : Fin n → UpperHalfPlane,
      (∑ i : Fin n, ∑ j : Fin n, A i j * (z i : ℂ) * (z j : ℂ)) = 0 := by
  classical
  have hcard_lam : 2 ≤ (Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i)).card := by
    have hroot := charpoly_positive_roots_card_eq A hA
    rw [hroot] at hcard
    dsimp [symmEigenvalues]
    exact hcard
  have hAne : A ≠ 0 := by
    intro hA0
    have hzero : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 0 := by
      rw [hA0]
      simp [Matrix.charpoly_zero]
    omega
  let y0 : Fin n → ℝ := fun _ => 1
  have hy0 : ∀ i : Fin n, 0 < y0 i := by intro i; dsimp [y0]; norm_num
  have hy_quad_pos : 0 < quadReal A y0 y0 := by
    dsimp [quadReal]
    exact quad_pos_of_nonneg A hnn hAne hy0
  have hq_y := quadReal_eq_eigen_sum' A hA y0 y0
  have hycoordpos : 0 < ∑ i : Fin n, symmEigenvalues A hA i * (symmYCoord A hA i * symmYCoord A hA i) := by
    simpa [hq_y, symmYCoord, y0] using hy_quad_pos
  obtain ⟨a, hcross, hpos⟩ := exists_coord_cross_zero_of_two_pos (symmEigenvalues A hA) (symmYCoord A hA) hcard_lam
  obtain ⟨a', hcross', hsq'⟩ := scale_coord_cross_zero (symmEigenvalues A hA) a (symmYCoord A hA) hcross hpos hycoordpos
  obtain ⟨x, hx_cross, hx_sq⟩ := quadReal_of_eigen_coord A hA a'
  have hx_cross0 : quadReal A x y0 = 0 := by
    rw [hx_cross, hcross']
  have hx_sq_eq : quadReal A x x = quadReal A y0 y0 := by
    rw [hx_sq, hsq']
    exact (quadReal_eq_eigen_sum' A hA y0 y0).symm
  let z : Fin n → UpperHalfPlane := fun i =>
    { coe := (x i : ℂ) + Complex.I * (y0 i : ℂ)
      coe_im_pos := by
        dsimp [y0]
        simp }
  refine ⟨z, ?_⟩
  change quadComplex A (fun i => (z i : ℂ)) = 0
  apply quadComplex_eq_zero_of_re_im A x y0
  · linarith [hx_sq_eq]
  · have hyx : quadReal A y0 x = 0 := by
      rw [quadReal_symm A hA y0 x, hx_cross0]
    linarith

lemma quadComplex_eq_zero_parts {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) (hQ : quadComplex A z = 0) :
    quadReal A (fun i => (z i).re) (fun i => (z i).re) -
        quadReal A (fun i => (z i).im) (fun i => (z i).im) = 0 ∧
    quadReal A (fun i => (z i).re) (fun i => (z i).im) +
        quadReal A (fun i => (z i).im) (fun i => (z i).re) = 0 := by
  rw [quadComplex_eq_quadReal_sub_add] at hQ
  constructor
  · have hre := congrArg Complex.re hQ
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] at hre
    exact_mod_cast hre
  · have him := congrArg Complex.im hQ
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im] at him
    exact_mod_cast him

lemma two_pos_of_quad {n : ℕ} (lam c d : Fin n → ℝ)
    (hcpos : 0 < ∑ i : Fin n, lam i * (c i * c i))
    (hd : (∑ i : Fin n, lam i * (d i * d i)) = ∑ i : Fin n, lam i * (c i * c i))
    (hcd : (∑ i : Fin n, lam i * (c i * d i)) = 0) :
    2 ≤ (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card := by
  classical
  by_contra h
  have hle : (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card ≤ 1 := by omega
  let s : Finset (Fin n) := Finset.univ.filter (fun i => 0 < lam i)
  have hcard0or1 : s.card = 0 ∨ s.card = 1 := by
    dsimp [s] at hle ⊢
    omega
  rcases hcard0or1 with h0 | h1
  · have hs_empty : s = ∅ := Finset.card_eq_zero.mp h0
    have hnonpos : ∀ i : Fin n, lam i ≤ 0 := by
      intro i
      have hi : i ∉ s := by simp [s, hs_empty]
      have hi' : ¬ 0 < lam i := by simpa [s] using hi
      exact le_of_not_gt hi'
    have hsum_nonpos : (∑ i : Fin n, lam i * (c i * c i)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact mul_nonpos_of_nonpos_of_nonneg (hnonpos i) (mul_self_nonneg (c i))
    linarith
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ s := by simp [hp]
    have hlam_p_pos : 0 < lam p := by
      have := (Finset.mem_filter.mp hp_mem).2
      simpa [s] using this
    have htail_nonpos : ∀ i : Fin n, i ≠ p → lam i ≤ 0 := by
      intro i hi
      have hi_not : i ∉ s := by
        intro his
        have : i ∈ ({p} : Finset (Fin n)) := by simpa [hp] using his
        have : i = p := by simpa using this
        exact hi this
      have hi' : ¬ 0 < lam i := by simpa [s] using hi_not
      exact le_of_not_gt hi'
    let neglam : Fin n → ℝ := fun i => - lam i
    have hneglam_nonneg : ∀ i, i ≠ p → 0 ≤ neglam i := by
      intro i hi
      dsimp [neglam]
      linarith [htail_nonpos i hi]
    let f : Fin n → ℝ := fun i => neglam i * (c i * c i)
    let g : Fin n → ℝ := fun i => neglam i * (d i * d i)
    let r : Fin n → ℝ := fun i => neglam i * (c i * d i)
    let t : Finset (Fin n) := Finset.univ.erase p
    have htail_c : (∑ i ∈ t, lam i * (c i * c i)) = - ∑ i ∈ t, f i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≠ p := by simpa [t] using hi
      dsimp [f, neglam]
      ring
    have htail_d : (∑ i ∈ t, lam i * (d i * d i)) = - ∑ i ∈ t, g i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≠ p := by simpa [t] using hi
      dsimp [g, neglam]
      ring
    have htail_cd : (∑ i ∈ t, lam i * (c i * d i)) = - ∑ i ∈ t, r i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≠ p := by simpa [t] using hi
      dsimp [r, neglam]
      ring
    have hsum_c : (∑ i : Fin n, lam i * (c i * c i)) = lam p * (c p * c p) - ∑ i ∈ t, f i := by
      calc
        (∑ i : Fin n, lam i * (c i * c i))
            = lam p * (c p * c p) + ∑ i ∈ t, lam i * (c i * c i) := by
              rw [← Finset.add_sum_erase Finset.univ (fun i => lam i * (c i * c i)) (Finset.mem_univ p)]
        _ = lam p * (c p * c p) - ∑ i ∈ t, f i := by
              rw [htail_c]
              ring
    have hsum_d : (∑ i : Fin n, lam i * (d i * d i)) = lam p * (d p * d p) - ∑ i ∈ t, g i := by
      calc
        (∑ i : Fin n, lam i * (d i * d i))
            = lam p * (d p * d p) + ∑ i ∈ t, lam i * (d i * d i) := by
              rw [← Finset.add_sum_erase Finset.univ (fun i => lam i * (d i * d i)) (Finset.mem_univ p)]
        _ = lam p * (d p * d p) - ∑ i ∈ t, g i := by
              rw [htail_d]
              ring
    have hsum_cd : (∑ i : Fin n, lam i * (c i * d i)) = lam p * (c p * d p) - ∑ i ∈ t, r i := by
      calc
        (∑ i : Fin n, lam i * (c i * d i))
            = lam p * (c p * d p) + ∑ i ∈ t, lam i * (c i * d i) := by
              rw [← Finset.add_sum_erase Finset.univ (fun i => lam i * (c i * d i)) (Finset.mem_univ p)]
        _ = lam p * (c p * d p) - ∑ i ∈ t, r i := by
              rw [htail_cd]
              ring
    have hf_nonneg : ∀ i ∈ t, 0 ≤ f i := by
      intro i hi
      have hi' : i ≠ p := by simpa [t] using hi
      dsimp [f, neglam]
      exact mul_nonneg (hneglam_nonneg i hi') (mul_self_nonneg (c i))
    have hg_nonneg : ∀ i ∈ t, 0 ≤ g i := by
      intro i hi
      have hi' : i ≠ p := by simpa [t] using hi
      dsimp [g, neglam]
      exact mul_nonneg (hneglam_nonneg i hi') (mul_self_nonneg (d i))
    have hsq : ∀ i ∈ t, r i ^ 2 ≤ f i * g i := by
      intro i hi
      dsimp [r, f, g, neglam]
      ring_nf
      exact le_rfl
    have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t hf_nonneg hg_nonneg hsq
    have hCpos_lt : lam p * (c p * c p) > ∑ i ∈ t, f i := by
      have hcpos' := hcpos
      rw [hsum_c] at hcpos'
      linarith
    have hDpos_lt : lam p * (d p * d p) > ∑ i ∈ t, g i := by
      have hmain : lam p * (d p * d p) - ∑ i ∈ t, g i = ∑ i : Fin n, lam i * (c i * c i) := by
        rw [← hsum_d, hd]
      have : 0 < lam p * (d p * d p) - ∑ i ∈ t, g i := by
        rw [hmain]; exact hcpos
      linarith
    have hmul_lt : (∑ i ∈ t, f i) * (∑ i ∈ t, g i) < (lam p * (c p * c p)) * (lam p * (d p * d p)) := by
      have h1 : 0 ≤ ∑ i ∈ t, f i := by
        apply Finset.sum_nonneg; intro i hi; exact hf_nonneg i hi
      have h2 : 0 ≤ ∑ i ∈ t, g i := by
        apply Finset.sum_nonneg; intro i hi; exact hg_nonneg i hi
      nlinarith [hCpos_lt, hDpos_lt, h1, h2]
    have hcd_p : lam p * (c p * d p) = ∑ i ∈ t, r i := by
      have hcd' := hcd
      rw [hsum_cd] at hcd'
      linarith
    have hsq_cd : (lam p * (c p * d p)) ^ 2 ≤ (∑ i ∈ t, f i) * (∑ i ∈ t, g i) := by
      rw [hcd_p]
      exact hcauchy
    have hsq_cd_eq : (lam p * (c p * d p)) ^ 2 = (lam p * (c p * c p)) * (lam p * (d p * d p)) := by
      ring
    rw [hsq_cd_eq] at hsq_cd
    linarith

lemma no_upper_half_plane_zero_of_positive_roots_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hroot : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1) :
    A = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      (∑ i : Fin n, ∑ j : Fin n, A i j * (z i : ℂ) * (z j : ℂ)) ≠ 0 := by
  classical
  by_cases hA0 : A = 0
  · left; exact hA0
  · right
    intro z hz
    let w : Fin n → ℂ := fun i => (z i : ℂ)
    have hz' : quadComplex A w = 0 := by simpa [quadComplex, w] using hz
    let xr : Fin n → ℝ := fun i => (w i).re
    let xi : Fin n → ℝ := fun i => (w i).im
    have hparts := quadComplex_eq_zero_parts A w hz'
    have hxx_sub : quadReal A xr xr - quadReal A xi xi = 0 := by simpa [xr, xi] using hparts.1
    have hcross_sum : quadReal A xr xi + quadReal A xi xr = 0 := by simpa [xr, xi] using hparts.2
    have hxx_eq : quadReal A xr xr = quadReal A xi xi := by linarith
    have hcross : quadReal A xr xi = 0 := by
      have hs := quadReal_symm A hA xr xi
      linarith
    have hxi_pos : ∀ i : Fin n, 0 < xi i := by
      intro i
      dsimp [xi, w]
      simpa [UpperHalfPlane.coe_im] using UpperHalfPlane.im_pos (z i)
    have hy_quad_pos : 0 < quadReal A xi xi := by
      dsimp [quadReal]
      exact quad_pos_of_nonneg A hnn hA0 hxi_pos
    have hxx_pos : 0 < quadReal A xr xr := by
      rw [hxx_eq]
      exact hy_quad_pos
    let lam : Fin n → ℝ := symmEigenvalues A hA
    let cx : Fin n → ℝ := fun i => ((symmBasis A hA).repr (WithLp.toLp 2 xr)).ofLp i
    let cy : Fin n → ℝ := fun i => ((symmBasis A hA).repr (WithLp.toLp 2 xi)).ofLp i
    have hq_xx : quadReal A xr xr = ∑ i : Fin n, lam i * (cx i * cx i) := by
      have := quadReal_eq_eigen_sum' A hA xr xr
      simpa [lam, cx] using this
    have hq_xi : quadReal A xr xi = ∑ i : Fin n, lam i * (cx i * cy i) := by
      have := quadReal_eq_eigen_sum' A hA xr xi
      simpa [lam, cx, cy] using this
    have hq_ii : quadReal A xi xi = ∑ i : Fin n, lam i * (cy i * cy i) := by
      have := quadReal_eq_eigen_sum' A hA xi xi
      simpa [lam, cx, cy] using this
    have hcpos : 0 < ∑ i : Fin n, lam i * (cx i * cx i) := by
      rw [← hq_xx]
      exact hxx_pos
    have hd : (∑ i : Fin n, lam i * (cy i * cy i)) = ∑ i : Fin n, lam i * (cx i * cx i) := by
      rw [← hq_ii, ← hq_xx]
      exact hxx_eq.symm
    have hcd : (∑ i : Fin n, lam i * (cx i * cy i)) = 0 := by
      rw [← hq_xi]
      exact hcross
    have htwo := two_pos_of_quad lam cx cy hcpos hd hcd
    have hroot_eq := charpoly_positive_roots_card_eq A hA
    have hroot2 : 2 ≤ (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card := by
      rw [hroot_eq]
      simpa [lam, symmEigenvalues] using htwo
    omega

theorem quadratic_stable_iff_roots_card_le_one
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) :
  (A = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      (∑ i : Fin n, ∑ j : Fin n, A i j * (z i : ℂ) * (z j : ℂ)) ≠ 0) ↔
    (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1 := by
  constructor
  · intro hleft
    by_contra hroot
    have hcard : 2 ≤ (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card := by omega
    obtain ⟨z, hz⟩ := exists_upper_half_plane_zero_of_two_pos_roots A hA hnn hcard
    rcases hleft with hA0 | hstable
    · have hzero : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 0 := by
        rw [hA0]
        simp [Matrix.charpoly_zero]
      omega
    · exact (hstable z) hz
  · intro hroot
    exact no_upper_half_plane_zero_of_positive_roots_le_one A hA hnn hroot

end Commons.LinearAlgebra.Matrix