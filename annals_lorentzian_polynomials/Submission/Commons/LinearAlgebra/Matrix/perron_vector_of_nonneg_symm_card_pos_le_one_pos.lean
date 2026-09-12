import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one

namespace Commons.LinearAlgebra.Matrix

open Matrix Polynomial Set
open scoped BigOperators

set_option hygiene false in
syntax "∃" "λ" ":" term "," term : term
set_option hygiene false in
macro_rules
  | `(∃ λ : $t:term, $p:term) => `(∃ lam : $t, $p)

set_option hygiene false in
syntax "λ" : term
set_option hygiene false in
macro_rules
  | `(λ) => `(lam)

set_option hygiene false in
syntax "λ" "•" term:75 : term
set_option hygiene false in
macro_rules
  | `(λ • $x:term) => `(lam • $x)

noncomputable section

def evec {n : ℕ} (i : Fin n) : Fin n → ℝ := fun k => if k = i then 1 else 0

lemma quadReal_eq_sum_mul_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadReal A x x = ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  classical
  dsimp [quadReal]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma quadReal_add_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    quadReal A (x + y) z = quadReal A x z + quadReal A y z := by
  classical
  rw [quadReal_mulVec, quadReal_mulVec, quadReal_mulVec]
  simp [dotProduct, Finset.sum_add_distrib, add_mul]

lemma quadReal_add_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    quadReal A x (y + z) = quadReal A x y + quadReal A x z := by
  classical
  rw [quadReal_mulVec, quadReal_mulVec, quadReal_mulVec]
  simp [Matrix.mulVec_add, dotProduct, Finset.sum_add_distrib, mul_add]

lemma quadReal_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    quadReal A (evec i) (evec i) = A i i := by
  classical
  dsimp [quadReal, evec]
  simp

lemma quadReal_single_off {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    quadReal A (evec i) (evec j) = A i j := by
  classical
  dsimp [quadReal, evec]
  simp

lemma max_eigenvalue_ge_eigenvalue {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (i : Fin n) :
    symmEigenvalues A hA i ≤ symmEigenvalues A hA ⟨0, hn⟩ := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (Matrix.isHermitian_iff_isSymm).2 hA
  let hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  have hle : (⟨0, hn⟩ : Fin n) ≤ i := by
    rw [Fin.le_def]
    simp
  have hanti := LinearMap.IsSymmetric.eigenvalues_antitone (T := T) hT hfin
  dsimp [symmEigenvalues]
  exact hanti hle

lemma sum_sq_repr_eq_norm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x : Fin n → ℝ) :
    ∑ i : Fin n, (((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i) ^ 2 =
      ∑ i : Fin n, x i ^ 2 := by
  classical
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hnorm : ‖(symmBasis A hA).repr y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [LinearIsometryEquiv.norm_map]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hnorm
  simpa [y, Real.norm_eq_abs, sq_abs] using hnorm

lemma quadReal_le_max_eigenvalue_mul_norm_sq {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x : Fin n → ℝ) :
    quadReal A x x ≤ (symmEigenvalues A hA ⟨0, hn⟩) * ∑ i : Fin n, x i ^ 2 := by
  classical
  let lam : Fin n → ℝ := symmEigenvalues A hA
  let c : Fin n → ℝ := fun i => ((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i
  have hquad := quadReal_eq_eigen_sum' A hA x x
  have hcsq := sum_sq_repr_eq_norm_sq A hA x
  have hle : ∀ i : Fin n, lam i * (c i * c i) ≤ lam ⟨0, hn⟩ * (c i * c i) := by
    intro i
    have hlam := max_eigenvalue_ge_eigenvalue hn A hA i
    have hsq : 0 ≤ c i * c i := mul_self_nonneg _
    exact mul_le_mul_of_nonneg_right hlam hsq
  have hsum_le : (∑ i : Fin n, lam i * (c i * c i)) ≤ ∑ i : Fin n, lam ⟨0, hn⟩ * (c i * c i) := by
    exact Finset.sum_le_sum (fun i hi => hle i)
  calc
    quadReal A x x = ∑ i : Fin n, lam i * (c i * c i) := by
      simpa [lam, c] using hquad
    _ ≤ ∑ i : Fin n, lam ⟨0, hn⟩ * (c i * c i) := hsum_le
    _ = lam ⟨0, hn⟩ * ∑ i : Fin n, c i * c i := by
      rw [Finset.mul_sum]
    _ = lam ⟨0, hn⟩ * ∑ i : Fin n, x i ^ 2 := by
      have hcsq' : ∑ i : Fin n, c i * c i = ∑ i : Fin n, x i ^ 2 := by
        simpa [c, pow_two] using hcsq
      rw [hcsq']

lemma max_eigenvalue_pos_of_nonneg_symm_ne_zero {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hAne : A ≠ 0) :
    0 < symmEigenvalues A hA ⟨0, hn⟩ := by
  classical
  let x : Fin n → ℝ := fun _ => 1
  have hquad_pos : 0 < quadReal A x x := by
    dsimp [quadReal, x]
    exact quad_pos_of_nonneg A hnn hAne (y := fun _ : Fin n => (1 : ℝ)) (by intro i; simpa using Real.zero_lt_one)
  have hle := quadReal_le_max_eigenvalue_mul_norm_sq hn A hA x
  have hnorm : (∑ i : Fin n, x i ^ 2) = n := by
    simp [x]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul_pos : 0 < (symmEigenvalues A hA ⟨0, hn⟩) * (n : ℝ) := by
    rw [← hnorm]
    exact lt_of_lt_of_le hquad_pos hle
  exact (mul_pos_iff_of_pos_right hnpos).mp hmul_pos

lemma symmBasis_mulVec_apply {n : ℕ} (_hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (i j : Fin n) :
    (A.mulVec ((symmBasis A hA i).ofLp)) j = symmEigenvalues A hA i * (symmBasis A hA i).ofLp j := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (Matrix.isHermitian_iff_isSymm).2 hA
  let hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  have h := LinearMap.IsSymmetric.apply_eigenvectorBasis (T := T) hT hfin i
  have hcoords := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp j) h
  dsimp [symmBasis, symmEigenvalues] at hcoords ⊢
  rw [Matrix.toEuclideanLin_apply] at hcoords
  simpa [smul_eq_mul, mul_comm] using hcoords

lemma abs_mulVec_eigenvector_le_mulVec_abs {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hpos : 0 < symmEigenvalues A hA ⟨0, hn⟩) :
    ∀ i : Fin n,
      symmEigenvalues A hA ⟨0, hn⟩ * |(symmBasis A hA ⟨0, hn⟩).ofLp i| ≤
        (A.mulVec (fun k => |(symmBasis A hA ⟨0, hn⟩).ofLp k|)) i := by
  classical
  let lam : ℝ := symmEigenvalues A hA ⟨0, hn⟩
  let v : EuclideanSpace ℝ (Fin n) := symmBasis A hA ⟨0, hn⟩
  let w : Fin n → ℝ := fun k => |v.ofLp k|
  have hlam_nonneg : 0 ≤ lam := le_of_lt hpos
  intro i
  have heigen := symmBasis_mulVec_apply hn A hA ⟨0, hn⟩ i
  have hmainEq : lam * |v.ofLp i| = |∑ j : Fin n, A i j * v.ofLp j| := by
    calc
      lam * |v.ofLp i| = |lam| * |v.ofLp i| := by rw [abs_of_nonneg hlam_nonneg]
      _ = |lam * v.ofLp i| := by rw [abs_mul]
      _ = |∑ j : Fin n, A i j * v.ofLp j| := by
        rw [← heigen]
        rw [Matrix.mulVec_apply_eq_sum]
  have hsum_le : |∑ j : Fin n, A i j * v.ofLp j| ≤ ∑ j : Fin n, |A i j * v.ofLp j| := by
    exact Finset.abs_sum_le_sum_abs (fun j => A i j * v.ofLp j) Finset.univ
  have hsum_eq : (∑ j : Fin n, |A i j * v.ofLp j|) = (A.mulVec w) i := by
    rw [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_mul, abs_of_nonneg (hnn i j)]
  calc
    lam * |v.ofLp i| ≤ |∑ j : Fin n, A i j * v.ofLp j| := le_of_eq hmainEq
    _ ≤ ∑ j : Fin n, |A i j * v.ofLp j| := hsum_le
    _ = (A.mulVec w) i := hsum_eq

lemma eigen_of_quad_eq_max {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (w : Fin n → ℝ)
    (hquad : quadReal A w w = (symmEigenvalues A hA ⟨0, hn⟩) * ∑ i : Fin n, w i ^ 2) :
    A.mulVec w = (symmEigenvalues A hA ⟨0, hn⟩) • w := by
  classical
  let lam : ℝ := symmEigenvalues A hA ⟨0, hn⟩
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := symmBasis A hA
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 w
  let c : Fin n → ℝ := fun i => (b.repr y).ofLp i
  have hquad_eig := quadReal_eq_eigen_sum' A hA w w
  have hcsq := sum_sq_repr_eq_norm_sq A hA w
  have hcsq' : (∑ i : Fin n, c i * c i) = ∑ i : Fin n, w i ^ 2 := by
    simpa [c, b, y, pow_two] using hcsq
  have hsum0 : (∑ i : Fin n, (lam - symmEigenvalues A hA i) * (c i * c i)) = 0 := by
    have h1 : (∑ i : Fin n, symmEigenvalues A hA i * (c i * c i)) = lam * ∑ i : Fin n, w i ^ 2 := by
      calc
        (∑ i : Fin n, symmEigenvalues A hA i * (c i * c i)) = quadReal A w w := by
          simpa [c, b, y] using hquad_eig.symm
        _ = lam * ∑ i : Fin n, w i ^ 2 := by simpa [lam] using hquad
    calc
      (∑ i : Fin n, (lam - symmEigenvalues A hA i) * (c i * c i))
          = lam * (∑ i : Fin n, c i * c i) - ∑ i : Fin n, symmEigenvalues A hA i * (c i * c i) := by
            calc
              (∑ i : Fin n, (lam - symmEigenvalues A hA i) * (c i * c i))
                  = ∑ i : Fin n, (lam * (c i * c i) - symmEigenvalues A hA i * (c i * c i)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [sub_mul]
              _ = (∑ i : Fin n, lam * (c i * c i)) - ∑ i : Fin n, symmEigenvalues A hA i * (c i * c i) := by
                    rw [Finset.sum_sub_distrib]
              _ = lam * (∑ i : Fin n, c i * c i) - ∑ i : Fin n, symmEigenvalues A hA i * (c i * c i) := by
                    rw [Finset.mul_sum]
      _ = lam * (∑ i : Fin n, w i ^ 2) - ∑ i : Fin n, symmEigenvalues A hA i * (c i * c i) := by
            rw [hcsq']
      _ = 0 := by
            rw [h1]
            ring
  have hnonneg : ∀ i : Fin n, 0 ≤ (lam - symmEigenvalues A hA i) * (c i * c i) := by
    intro i
    have hle : symmEigenvalues A hA i ≤ lam := max_eigenvalue_ge_eigenvalue hn A hA i
    have hsq : 0 ≤ c i * c i := mul_self_nonneg _
    exact mul_nonneg (sub_nonneg.mpr hle) hsq
  have hterm0 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i : Fin n => (lam - symmEigenvalues A hA i) * (c i * c i))
      (fun i hi => hnonneg i)).mp hsum0
  have hcoord : ∀ i : Fin n, symmEigenvalues A hA i * c i = lam * c i := by
    intro i
    have hterm : (lam - symmEigenvalues A hA i) * (c i * c i) = 0 := hterm0 i (Finset.mem_univ i)
    by_cases hlam_eq : lam = symmEigenvalues A hA i
    · rw [← hlam_eq]
    · have hdiff_ne : lam - symmEigenvalues A hA i ≠ 0 := by
        intro h
        apply hlam_eq
        linarith
      have hcsq0 : c i * c i = 0 := (mul_eq_zero.mp hterm).resolve_left hdiff_ne
      have hc0 : c i = 0 := mul_self_eq_zero.mp hcsq0
      simp [hc0]
  have hTy : (b.repr (A.toEuclideanLin y)).ofLp = fun i => symmEigenvalues A hA i * c i := by
    funext i
    have h := LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply
      (T := A.toEuclideanLin)
      (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
      (by simp [finrank_euclideanSpace]) y i
    dsimp [b, symmBasis, symmEigenvalues, c, y] at h ⊢
    simpa [Matrix.toEuclideanLin_apply] using h
  have hrepr : b.repr (A.toEuclideanLin y) = b.repr ((lam : ℝ) • y) := by
    apply (WithLp.ext_iff (p := 2)).mpr
    funext i
    calc
      (b.repr (A.toEuclideanLin y)).ofLp i = symmEigenvalues A hA i * c i := by
        exact congr_fun hTy i
      _ = lam * c i := hcoord i
      _ = (b.repr ((lam : ℝ) • y)).ofLp i := by
        rw [map_smul]
        simp [c, b, y]
  have hinj := b.repr.injective hrepr
  have : A.toEuclideanLin y = (lam : ℝ) • y := hinj
  have hcoords := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp) this
  dsimp [y, b] at hcoords
  simpa [lam] using hcoords

lemma positive_eigenvalues_singleton {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hcard : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (hpos : 0 < symmEigenvalues A hA ⟨0, hn⟩) :
    Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i) = {⟨0, hn⟩} := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (Matrix.isHermitian_iff_isSymm).2 hA
  let hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => 0 < LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin i)
  have hcard_lam : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = s.card := by
    have h := charpoly_positive_roots_card_eq A hA
    dsimp [T, hT, hfin, s] at h ⊢
    exact h
  have hle : s.card ≤ 1 := by
    rw [← hcard_lam]
    exact hcard
  have hpos' : 0 < LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin ⟨0, hn⟩ := by
    simpa [T, hT, hfin, symmEigenvalues] using hpos
  have hmem : ⟨0, hn⟩ ∈ s := by
    dsimp [s]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos'⟩
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, ?_⟩
  intro x hx
  exact (Finset.card_le_one_iff.mp hle hmem hx).symm

lemma finrank_eigenspace_max_eq_one {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hcard : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (hpos : 0 < symmEigenvalues A hA ⟨0, hn⟩) :
    Module.finrank ℝ (Module.End.eigenspace (A.toEuclideanLin) (symmEigenvalues A hA ⟨0, hn⟩)) = 1 := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let hT : T.IsSymmetric := by
    dsimp [T]
    rw [Matrix.isSymmetric_toEuclideanLin_iff]
    exact (Matrix.isHermitian_iff_isSymm).2 hA
  let hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp [finrank_euclideanSpace]
  let lam : ℝ := symmEigenvalues A hA ⟨0, hn⟩
  have hpos' : 0 < LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin ⟨0, hn⟩ := by
    simpa [T, hT, hfin, symmEigenvalues] using hpos
  have hfil_singleton :
      Finset.univ.filter (fun i : Fin n => LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin i = lam) = {⟨0, hn⟩} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · have h0 : LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin ⟨0, hn⟩ = lam := by
        dsimp [lam, T, hT, hfin, symmEigenvalues]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
    · intro i hi
      have hiP : LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin i = lam := (Finset.mem_filter.mp hi).2
      have hpos_i : 0 < LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin i := by
        rw [hiP]
        dsimp [lam, T, hT, hfin, symmEigenvalues]
        exact hpos
      have hs := positive_eigenvalues_singleton hn A hA hcard hpos
      have hi_mem : i ∈ Finset.univ.filter (fun k : Fin n => 0 < symmEigenvalues A hA k) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          dsimp [T, hT, hfin, symmEigenvalues]
          exact hpos_i⟩
      rw [hs] at hi_mem
      simpa using hi_mem
  have hcard_fil : (Finset.univ.filter (fun i : Fin n => LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin i = lam)).card =
      Module.finrank ℝ (Module.End.eigenspace T lam) := by
    exact LinearMap.IsSymmetric.card_filter_eigenvalues_eq (T := T) hT hfin lam
  calc
    Module.finrank ℝ (Module.End.eigenspace (A.toEuclideanLin) (symmEigenvalues A hA ⟨0, hn⟩))
        = Module.finrank ℝ (Module.End.eigenspace T lam) := by rfl
    _ = (Finset.univ.filter (fun i : Fin n => LinearMap.IsSymmetric.eigenvalues (T := T) hT hfin i = lam)).card := by
        rw [hcard_fil]
    _ = 1 := by rw [hfil_singleton]; simp

lemma norm_abs_basis_eq_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (i : Fin n) :
    ‖WithLp.toLp 2 (fun k : Fin n => |(symmBasis A hA i).ofLp k|)‖ = 1 := by
  classical
  let v : EuclideanSpace ℝ (Fin n) := symmBasis A hA i
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k => |v.ofLp k|)
  have hnorm_v : ‖v‖ = 1 := (symmBasis A hA).norm_eq_one i
  have hsq_v : ‖v‖ ^ 2 = 1 := by simp [hnorm_v]
  have hsq_w : ‖w‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ k : Fin n, |v.ofLp k| ^ 2 = 1
    calc
      (∑ k : Fin n, |v.ofLp k| ^ 2) = ∑ k : Fin n, v.ofLp k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [sq_abs]
      _ = ‖v‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
      _ = 1 := hsq_v
  have hnorm_nonneg : 0 ≤ ‖w‖ := norm_nonneg _
  rcases sq_eq_one_iff.mp hsq_w with h | h
  · exact h
  · nlinarith

lemma scalar_of_eigenspace_dim_one {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (_hpos : 0 < symmEigenvalues A hA ⟨0, hn⟩)
    (hw_eigen : A.mulVec (fun i => |(symmBasis A hA ⟨0, hn⟩).ofLp i|) =
      (symmEigenvalues A hA ⟨0, hn⟩) • (fun i => |(symmBasis A hA ⟨0, hn⟩).ofLp i|))
    (hdim : Module.finrank ℝ (Module.End.eigenspace (A.toEuclideanLin) (symmEigenvalues A hA ⟨0, hn⟩)) = 1) :
    ∃ c : ℝ, c ≠ 0 ∧
      (fun i : Fin n => |(symmBasis A hA ⟨0, hn⟩).ofLp i|) =
        c • (symmBasis A hA ⟨0, hn⟩).ofLp := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := A.toEuclideanLin
  let lam : ℝ := symmEigenvalues A hA ⟨0, hn⟩
  let E : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Module.End.eigenspace T lam
  let vE : EuclideanSpace ℝ (Fin n) := symmBasis A hA ⟨0, hn⟩
  let wf : Fin n → ℝ := fun i => |vE.ofLp i|
  let wE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 wf
  have hv_ne : vE ≠ 0 := by
    dsimp [vE]
    exact (symmBasis A hA).toBasis.ne_zero ⟨0, hn⟩
  have hw_ne : wE ≠ 0 := by
    intro hw0
    have hnorm1 : ‖wE‖ = 1 := by
      simpa [wE, wf, vE] using norm_abs_basis_eq_one A hA ⟨0, hn⟩
    have hnorm0 : ‖wE‖ = 0 := by simp [hw0]
    linarith
  have hv_mem : vE ∈ E := by
    dsimp [E, T, vE, lam]
    rw [Module.End.mem_eigenspace_iff]
    have h := LinearMap.IsSymmetric.apply_eigenvectorBasis
      (T := A.toEuclideanLin)
      (by rw [Matrix.isSymmetric_toEuclideanLin_iff]; exact (Matrix.isHermitian_iff_isSymm).2 hA)
      (by simp [finrank_euclideanSpace]) ⟨0, hn⟩
    dsimp [symmBasis, symmEigenvalues] at h ⊢
    simpa using h
  have hw_eigen' : T wE = lam • wE := by
    dsimp [T, wE, wf, vE]
    rw [hw_eigen]
    dsimp [lam]
  have hw_mem : wE ∈ E := by
    dsimp [E, T, lam]
    rw [Module.End.mem_eigenspace_iff]
    exact hw_eigen'
  let v_sub : E := ⟨vE, hv_mem⟩
  let w_sub : E := ⟨wE, hw_mem⟩
  have hv_sub_ne : v_sub ≠ 0 := by
    intro h
    apply hv_ne
    exact congrArg Subtype.val h
  have hdimE : Module.finrank ℝ E = 1 := by
    dsimp [E, T, lam]
    simpa [T, lam] using hdim
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℝ) (V := E) v_sub hv_sub_ne).mp hdimE w_sub
  have hc_ambient := congrArg (fun z : E => (z : EuclideanSpace ℝ (Fin n))) hc
  have hc_coords := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp) hc_ambient
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hw0 : wE = 0 := by
      rw [hc0] at hc_ambient
      simpa [w_sub, v_sub] using hc_ambient.symm
    exact hw_ne hw0
  refine ⟨c, hc_ne, ?_⟩
  dsimp [wf, vE] at hc_coords ⊢
  simpa [Pi.smul_def] using hc_coords.symm

lemma coeff_zero_of_orthogonal_of_scalar {n : ℕ} (v u : Fin n → ℝ) (x : Fin n → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hu : u = c • v) (hx : (∑ i : Fin n, u i * x i) = 0) :
    (∑ i : Fin n, v i * x i) = 0 := by
  classical
  have hsum : c * (∑ i : Fin n, v i * x i) = 0 := by
    calc
      c * (∑ i : Fin n, v i * x i) = ∑ i : Fin n, c * (v i * x i) := by rw [Finset.mul_sum]
      _ = ∑ i : Fin n, (c * v i) * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i : Fin n, u i * x i := by
        rw [hu]
        simp [Pi.smul_def]
      _ = 0 := hx
  exact (mul_eq_zero.mp hsum).resolve_left hc

lemma quad_nonpos_of_orthogonal {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hcard : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (u : Fin n → ℝ)
    (hu_abs : u = fun i => |(symmBasis A hA ⟨0, hn⟩).ofLp i|)
    (hu_eigen : A.mulVec u = (symmEigenvalues A hA ⟨0, hn⟩) • u)
    (hpos : 0 < symmEigenvalues A hA ⟨0, hn⟩)
    (x : Fin n → ℝ) (hx : (∑ i : Fin n, u i * x i) = 0) :
    quadReal A x x ≤ 0 := by
  classical
  let vf : Fin n → ℝ := (symmBasis A hA ⟨0, hn⟩).ofLp
  let wf : Fin n → ℝ := fun i => |(symmBasis A hA ⟨0, hn⟩).ofLp i|
  have hw_eigen : A.mulVec wf = (symmEigenvalues A hA ⟨0, hn⟩) • wf := by
    simpa [wf, hu_abs] using hu_eigen
  have hdim := finrank_eigenspace_max_eq_one hn A hA hcard hpos
  obtain ⟨c, hc_ne, hc_scalar⟩ := scalar_of_eigenspace_dim_one hn A hA hpos hw_eigen hdim
  have hu_scalar : u = c • vf := by
    rw [hu_abs]
    exact hc_scalar
  have hx_v : (∑ i : Fin n, vf i * x i) = 0 := by
    apply coeff_zero_of_orthogonal_of_scalar vf u x c hc_ne hu_scalar hx
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := symmBasis A hA
  let cvec : Fin n → ℝ := fun i => (b.repr (WithLp.toLp 2 x)).ofLp i
  have hcoeff0 : cvec ⟨0, hn⟩ = 0 := by
    dsimp [cvec, b]
    rw [OrthonormalBasis.repr_apply_apply]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct, vf, mul_comm] using hx_v
  have hnonpos_each : ∀ i : Fin n, symmEigenvalues A hA i * (cvec i * cvec i) ≤ 0 := by
    intro i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      rw [hcoeff0]
      simp
    · have hpos_singleton := positive_eigenvalues_singleton hn A hA hcard hpos
      have hi_not_pos : ¬ 0 < symmEigenvalues A hA i := by
        intro hposi
        have hi_mem : i ∈ Finset.univ.filter (fun k : Fin n => 0 < symmEigenvalues A hA k) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hposi⟩
        rw [hpos_singleton] at hi_mem
        exact hi (by simpa using hi_mem)
      have hle : symmEigenvalues A hA i ≤ 0 := le_of_not_gt hi_not_pos
      exact mul_nonpos_of_nonpos_of_nonneg hle (mul_self_nonneg _)
  have hsum_nonpos : (∑ i : Fin n, symmEigenvalues A hA i * (cvec i * cvec i)) ≤ 0 := by
    exact Finset.sum_nonpos (fun i hi => hnonpos_each i)
  have hquad_eig := quadReal_eq_eigen_sum' A hA x x
  calc
    quadReal A x x = ∑ i : Fin n, symmEigenvalues A hA i * (cvec i * cvec i) := by
      simpa [cvec, b] using hquad_eig
    _ ≤ 0 := hsum_nonpos

lemma support_of_perron {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (u : Fin n → ℝ) (hu_nonneg : ∀ i, 0 ≤ u i)
    (hu_norm : (∑ i : Fin n, u i * u i) = 1)
    (hpos_lam : 0 < symmEigenvalues A hA ⟨0, hn⟩)
    (hu_eigen : A.mulVec u = (symmEigenvalues A hA ⟨0, hn⟩) • u)
    (hquad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
      (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0) :
    ∀ i j : Fin n, (u i = 0 ∨ u j = 0) → A i j = 0 := by
  classical
  let lam : ℝ := symmEigenvalues A hA ⟨0, hn⟩
  have hquad_quad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
      quadReal A x x ≤ 0 := by
    intro x hx
    rw [quadReal_eq_sum_mul_left]
    exact hquad x hx
  have both_zero : ∀ p q : Fin n, u p = 0 → u q = 0 → A p q = 0 := by
    intro p q hp hq
    have hpq_nonneg : 0 ≤ A p q := hnn p q
    have hpp0 : A p p = 0 := by
      have horth : (∑ k : Fin n, u k * evec p k) = 0 := by
        simp [evec, hp]
      have hqp := hquad_quad (evec p) horth
      have hq_eq : quadReal A (evec p) (evec p) = A p p := quadReal_single A p
      nlinarith [hq_eq, hqp, hnn p p]
    have hqq0 : A q q = 0 := by
      have horth : (∑ k : Fin n, u k * evec q k) = 0 := by
        simp [evec, hq]
      have hqp := hquad_quad (evec q) horth
      have hq_eq : quadReal A (evec q) (evec q) = A q q := quadReal_single A q
      nlinarith [hq_eq, hqp, hnn q q]
    have horth_sum : (∑ k : Fin n, u k * (evec p + evec q) k) = 0 := by
      have hsum_p : (∑ k : Fin n, u k * evec p k) = u p := by simp [evec]
      have hsum_q : (∑ k : Fin n, u k * evec q k) = u q := by simp [evec]
      calc
        (∑ k : Fin n, u k * (evec p + evec q) k)
            = (∑ k : Fin n, u k * evec p k) + ∑ k : Fin n, u k * evec q k := by
              simp [Finset.sum_add_distrib, mul_add]
        _ = u p + u q := by rw [hsum_p, hsum_q]
        _ = 0 := by rw [hp, hq]; simp
    have hqp := hquad_quad (evec p + evec q) horth_sum
    have hq_eq : quadReal A (evec p + evec q) (evec p + evec q) =
        A p p + A p q + A q p + A q q := by
      rw [quadReal_add_left, quadReal_add_right, quadReal_add_right]
      rw [quadReal_single, quadReal_single_off, quadReal_single_off, quadReal_single]
      ring
    have hsymm : A q p = A p q := hA.apply p q
    have hpq_le : A p q ≤ 0 := by nlinarith [hqp, hq_eq, hpp0, hqq0, hsymm, hpq_nonneg]
    exact le_antisymm hpq_le hpq_nonneg
  have elim_row : ∀ p q : Fin n, u p = 0 → 0 < u q → A p q = 0 := by
    intro p q hp hqpos
    have hpq_nonneg : 0 ≤ A p q := hnn p q
    by_contra hpq_ne
    have hpq_pos : 0 < A p q := lt_of_le_of_ne' hpq_nonneg hpq_ne
    have hterm_pos : 0 < A p q * u q := mul_pos hpq_pos hqpos
    have hsum_nonneg : ∀ k : Fin n, 0 ≤ A p k * u k := by
      intro k
      exact mul_nonneg (hnn p k) (hu_nonneg k)
    have hterm_le : A p q * u q ≤ ∑ k : Fin n, A p k * u k := by
      exact Finset.single_le_sum (fun k hk => hsum_nonneg k) (Finset.mem_univ q)
    have hsum_pos : 0 < ∑ k : Fin n, A p k * u k := lt_of_lt_of_le hterm_pos hterm_le
    have hmulvec : (A.mulVec u) p = lam * u p := by
      rw [hu_eigen]
      rfl
    have hsum_eq_zero : (∑ k : Fin n, A p k * u k) = 0 := by
      rw [← Matrix.mulVec_apply_eq_sum]
      rw [hmulvec, hp]
      simp
    linarith
  intro i j hij
  rcases hij with hui | huj
  · by_cases huj0 : u j = 0
    · exact both_zero i j hui huj0
    · exact elim_row i j hui (lt_of_le_of_ne' (hu_nonneg j) huj0)
  · by_cases hui0 : u i = 0
    · exact both_zero i j hui0 huj
    · have hji : A j i = 0 := elim_row j i huj (lt_of_le_of_ne' (hu_nonneg i) hui0)
      simpa [hA.apply j i] using hji

theorem perron_vector_of_nonneg_symm_card_pos_le_one_pos {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hcard : (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1) :
    ∃ u : Fin n → ℝ, ∃ λ : ℝ,
      (∀ i, 0 ≤ u i) ∧ (∑ i, u i * u i) = 1 ∧ 0 ≤ λ ∧
      A.mulVec u = λ • u ∧
      (∀ x : Fin n → ℝ, (∑ i, u i * x i) = 0 →
        (∑ i, ∑ j, x i * A i j * x j) ≤ 0) ∧
      (∀ i j, (u i = 0 ∨ u j = 0) → A i j = 0) := by
  classical
  by_cases hA0 : A = 0
  · let u : Fin n → ℝ := evec ⟨0, hn⟩
    refine ⟨u, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      dsimp [u, evec]
      split <;> norm_num
    · dsimp [u, evec]
      simp
    · norm_num
    · dsimp [u]
      simp [hA0]
    · intro x hx
      simp [hA0]
    · intro i j hij
      simp [hA0]
  · let lam : ℝ := symmEigenvalues A hA ⟨0, hn⟩
    have hpos_symm : 0 < symmEigenvalues A hA ⟨0, hn⟩ :=
      max_eigenvalue_pos_of_nonneg_symm_ne_zero hn A hA hnn hA0
    have hpos_lam : 0 < lam := by simpa [lam] using hpos_symm
    let vf : Fin n → ℝ := (symmBasis A hA ⟨0, hn⟩).ofLp
    let u : Fin n → ℝ := fun i => |vf i|
    have hu_eigen : A.mulVec u = lam • u := by
      have hrow := abs_mulVec_eigenvector_le_mulVec_abs hn A hA hnn hpos_symm
      have hnorm : (∑ i : Fin n, u i ^ 2) = 1 := by
        have hnorm1 : ‖WithLp.toLp 2 (fun k : Fin n => |vf k|)‖ = 1 := by
          dsimp [vf]
          exact norm_abs_basis_eq_one A hA ⟨0, hn⟩
        have hnorm_sq : ‖WithLp.toLp 2 (fun k : Fin n => |vf k|)‖ ^ 2 = 1 := by simp [hnorm1]
        rw [EuclideanSpace.real_norm_sq_eq] at hnorm_sq
        dsimp [u, vf] at hnorm_sq ⊢
        simpa [pow_two] using hnorm_sq
      have hquad_lower : lam * (∑ i : Fin n, u i ^ 2) ≤ quadReal A u u := by
        have hrow' : ∀ i : Fin n, lam * u i ≤ (A.mulVec u) i := by
          intro i
          simpa [u, vf, lam] using hrow i
        have hsum_le : (∑ i : Fin n, (lam * u i) * u i) ≤ ∑ i : Fin n, (A.mulVec u) i * u i := by
          exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hrow' i) (abs_nonneg _))
        have hleft : (∑ i : Fin n, (lam * u i) * u i) = lam * (∑ i : Fin n, u i ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        have hright : (∑ i : Fin n, (A.mulVec u) i * u i) = quadReal A u u := by
          rw [quadReal_mulVec, dotProduct]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        linarith
      have hquad_upper := quadReal_le_max_eigenvalue_mul_norm_sq hn A hA u
      have hquad_eq : quadReal A u u = lam * (∑ i : Fin n, u i ^ 2) := by
        have hquad_upper' : quadReal A u u ≤ lam * (∑ i : Fin n, u i ^ 2) := by
          simpa [lam] using hquad_upper
        linarith [hquad_lower, hquad_upper']
      have hnorm_prod : (∑ i : Fin n, u i * u i) = ∑ i : Fin n, u i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hquad_eq' : quadReal A u u = lam * (∑ i : Fin n, u i * u i) := by
        rw [hquad_eq, hnorm_prod]
      exact eigen_of_quad_eq_max hn A hA u (by simpa [lam] using hquad_eq)
    have hu_nonneg : ∀ i, 0 ≤ u i := by intro i; dsimp [u, vf]; exact abs_nonneg _
    have hu_norm : (∑ i : Fin n, u i * u i) = 1 := by
      have hnorm1 : ‖WithLp.toLp 2 (fun k : Fin n => |vf k|)‖ = 1 := by
        dsimp [vf]
        exact norm_abs_basis_eq_one A hA ⟨0, hn⟩
      have hnorm_sq : ‖WithLp.toLp 2 (fun k : Fin n => |vf k|)‖ ^ 2 = 1 := by simp [hnorm1]
      rw [EuclideanSpace.real_norm_sq_eq] at hnorm_sq
      dsimp [u, vf] at hnorm_sq ⊢
      simpa [pow_two] using hnorm_sq
    have hu_abs : u = fun i => |(symmBasis A hA ⟨0, hn⟩).ofLp i| := by
      dsimp [u, vf]
    have hquad_cond : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
        (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0 := by
      intro x hx
      have hq := quad_nonpos_of_orthogonal hn A hA hcard u hu_abs hu_eigen hpos_symm x hx
      rw [← quadReal_eq_sum_mul_left A x]
      exact hq
    have hsupport : ∀ i j : Fin n, (u i = 0 ∨ u j = 0) → A i j = 0 := by
      exact support_of_perron hn A hA hnn u hu_nonneg hu_norm hpos_symm hu_eigen hquad_cond
    refine ⟨u, lam, hu_nonneg, hu_norm, le_of_lt hpos_lam, hu_eigen, hquad_cond, hsupport⟩

end

end Commons.LinearAlgebra.Matrix