import Mathlib
import Submission.Commons.Algebra.MvPolynomial.harmonic_part_axisInvariant
import Submission.Commons.Algebra.MvPolynomial.axisInv_homogeneous_structure
import Submission.Commons.Algebra.MvPolynomial.zonal_pole_value_ne_zero

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace Commons.Algebra.MvPolynomial

/-- The linear form attached to a basis vector is `X i`. -/
lemma sum_C_single_X {n : ℕ} (i : Fin n) :
    (∑ j : Fin n,
        (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) *
          (MvPolynomial.X j)) = MvPolynomial.X i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [PiLp.single_apply]
    simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The `i = 0` case: zonal radial structure. -/
theorem zonal_radial_zero {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZ : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hR : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hdec : (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k =
        Z + (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    ∃ P : Polynomial ℝ, ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z =
        Polynomial.eval ((θ : EuclideanSpace ℝ (Fin n)) (0 : Fin n)) P := by
  classical
  have hIZ := harmonic_part_axisInvariant (n := n) (k := k) Z R hZ hlapZ hR hdec
  rcases axisInv_homogeneous_structure (n := n) (k := k) hn2 Z hZ hIZ with ⟨c, hc⟩
  refine ⟨∑ j : Fin (k / 2 + 1),
      Polynomial.C (c j) * Polynomial.X ^ (k - 2 * (j : ℕ)) *
        (1 - Polynomial.X ^ 2) ^ (j : ℕ), ?_⟩
  intro θ
  let g : Fin n → ℝ := fun j => (θ : EuclideanSpace ℝ (Fin n)) j
  let S : MvPolynomial (Fin n) ℝ :=
    ∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (MvPolynomial.X (i : Fin n))^2
  have hcS : Z = ∑ j : Fin (k/2+1),
      (c j) • ((MvPolynomial.X (0:Fin n))^(k - 2*(j:ℕ)) * S^(j:ℕ)) := hc
  have hnorm : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have h := Metric.mem_sphere.mp θ.2
    simpa [dist_eq_norm] using h
  have hsumsq : (∑ i : Fin n, ((θ : EuclideanSpace ℝ (Fin n)) i)^2) = 1 := by
    have h1 : ‖(θ : EuclideanSpace ℝ (Fin n))‖^2 = ∑ i, ((θ : EuclideanSpace ℝ (Fin n)) i)^2 := by
      rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
    rw [← h1, hnorm]; norm_num
  have hS : MvPolynomial.eval g S = 1 - (g (0:Fin n))^2 := by
    have hS1 : MvPolynomial.eval g S =
        ∑ i : {i : Fin n // i ≠ (0:Fin n)}, (g (i:Fin n))^2 := by
      dsimp [S]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_pow, MvPolynomial.eval_X]
    have hS2 : (∑ i : {i : Fin n // i ≠ (0:Fin n)}, (g (i:Fin n))^2) =
        ∑ i ∈ (Finset.univ.erase (0:Fin n)), (g i)^2 :=
      (Finset.sum_subtype (s := Finset.univ.erase (0:Fin n))
        (fun x => by simp [Finset.mem_erase]) (fun i : Fin n => (g i)^2)).symm
    have hS3 : (∑ i ∈ (Finset.univ.erase (0:Fin n)), (g i)^2) = 1 - (g (0:Fin n))^2 := by
      have h := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) (fun i => (g i)^2)
        (Finset.mem_univ (0:Fin n))
      rw [hsumsq] at h
      linarith
    rw [hS1, hS2, hS3]
  have hevalZ : MvPolynomial.eval g Z =
      ∑ j : Fin (k/2+1), (c j) * (g (0:Fin n))^(k - 2*(j:ℕ)) * (1 - (g (0:Fin n))^2)^(j:ℕ) := by
    rw [hcS, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_mul, map_pow, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X, hS]
    ring
  rw [hevalZ, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  ring

/-- **Zonal radial theorem.** A homogeneous harmonic polynomial `Z` of degree `k` whose
difference from `Xᵢ^k` is divisible by `∑ Xⱼ²` restricts, on the unit sphere, to a
polynomial in the single coordinate `θᵢ`. -/
theorem zonal_radial
    {n : ℕ} {k : ℕ} (i : Fin n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hdec : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) * (MvPolynomial.X j)) ^ k) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    ∃ P : Polynomial ℝ, ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z =
        Polynomial.eval ((θ : EuclideanSpace ℝ (Fin n)) i) P := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact i.elim0
  haveI : NeZero n := ⟨hn0⟩
  by_cases hn2 : 2 ≤ n
  · -- main case: reduce to the axis-0 statement by swapping coordinates
    let τ : Equiv.Perm (Fin n) := Equiv.swap (0 : Fin n) i
    have hτ0 : τ (0:Fin n) = i := by show (Equiv.swap (0:Fin n) i) (0:Fin n) = i; rw [Equiv.swap_apply_left]
    have hτi : τ i = (0:Fin n) := by show (Equiv.swap (0:Fin n) i) i = (0:Fin n); rw [Equiv.swap_apply_right]
    have hττ : ∀ j : Fin n, τ (τ j) = j := by
      intro j
      show (Equiv.swap (0:Fin n) i) ((Equiv.swap (0:Fin n) i) j) = j
      simp only [Equiv.swap_apply_def]
      by_cases h1 : j = (0:Fin n)
      · subst h1; simp
      · by_cases h2 : j = i
        · subst h2; simp
        · simp [h1, h2]
    let Z' : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ τ Z
    let R' : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ τ R
    have hZ' : Z' ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
      dsimp [Z']; exact rename_mem_homogeneous τ Z hZmem
    have hlapZ' : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z')) = 0 := by
      dsimp [Z']
      rw [rename_lap τ Z, hlapZ, map_zero]
    have hR' : R' ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) := by
      dsimp [R']; exact rename_mem_homogeneous τ R hRmem
    have hdec2 : (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)^k =
        Z + (∑ j : Fin n, (MvPolynomial.X j)^2) * R := by
      have h := hdec
      rw [sum_C_single_X i] at h
      exact h
    have hdec' : (MvPolynomial.X (0:Fin n) : MvPolynomial (Fin n) ℝ)^k =
        Z' + (∑ j : Fin n, (MvPolynomial.X j)^2) * R' := by
      have h := congrArg (MvPolynomial.renameEquiv ℝ τ) hdec2
      simp only [map_pow, map_add, map_mul] at h
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hτi,
        rename_X2 n τ] at h
      exact h
    rcases zonal_radial_zero hn2 Z' R' hZ' hlapZ' hR' hdec' with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    intro θ
    have hnorm : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      have h := Metric.mem_sphere.mp θ.2
      simpa [dist_eq_norm] using h
    let θ' : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) (τ j))
    have hθ'coe : ∀ j : Fin n, (θ' : EuclideanSpace ℝ (Fin n)) j =
        (θ : EuclideanSpace ℝ (Fin n)) (τ j) := by
      intro j; simp only [θ']
    have hθ'norm : ‖θ'‖ = 1 := by
      have h1 : ‖θ'‖^2 = ∑ j : Fin n, ((θ : EuclideanSpace ℝ (Fin n)) (τ j))^2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hθ'coe, Real.norm_eq_abs, sq_abs]
      have h2 : ‖(θ : EuclideanSpace ℝ (Fin n))‖^2 =
          ∑ j : Fin n, ((θ : EuclideanSpace ℝ (Fin n)) j)^2 := by
        rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
      have h3 : (∑ j : Fin n, ((θ : EuclideanSpace ℝ (Fin n)) (τ j))^2) =
          ∑ j : Fin n, ((θ : EuclideanSpace ℝ (Fin n)) j)^2 :=
        Equiv.sum_comp τ (fun j => ((θ : EuclideanSpace ℝ (Fin n)) j)^2)
      have hsq : ‖θ'‖^2 = 1 := by rw [h1, h3, ← h2, hnorm]; norm_num
      nlinarith [hsq, norm_nonneg θ']
    have hθ'sphere : θ' ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm]
      simpa using hθ'norm
    have hkey := hP ⟨θ', hθ'sphere⟩
    have hθ'0 : (θ' : EuclideanSpace ℝ (Fin n)) (0:Fin n) =
        (θ : EuclideanSpace ℝ (Fin n)) i := by
      rw [hθ'coe, hτ0]
    have hconv : MvPolynomial.eval (fun j : Fin n => (θ' : EuclideanSpace ℝ (Fin n)) j) Z'
        = MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z := by
      have hv : (fun j : Fin n => (θ' : EuclideanSpace ℝ (Fin n)) j) =
          (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) (τ j)) := by
        funext j; exact hθ'coe j
      rw [hv]
      have hZ'e : Z' = MvPolynomial.rename (⇑τ) Z := by
        show MvPolynomial.renameEquiv ℝ τ Z = MvPolynomial.rename (⇑τ) Z
        rw [MvPolynomial.renameEquiv_apply]
      rw [hZ'e, MvPolynomial.eval_rename]
      have hfe : ((fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) (τ j)) ∘ τ) =
          (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) := by
        funext j; rw [Function.comp_apply, hττ j]
      rw [hfe]
    rw [← hconv, hkey, hθ'0]
  · -- degenerate case n = 1
    have hn1 : n = 1 := by
      have := i.isLt
      omega
    subst hn1
    have hi : i = (0 : Fin 1) := Fin.fin_one_eq_zero i
    let a : ℝ := MvPolynomial.eval (fun _ : Fin 1 => (1:ℝ)) Z
    let b : ℝ := MvPolynomial.eval (fun _ : Fin 1 => (-1:ℝ)) Z
    refine ⟨Polynomial.C ((a+b)/2) + Polynomial.C ((a-b)/2) * Polynomial.X, ?_⟩
    intro θ
    have hnorm : ‖(θ : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
      have h := Metric.mem_sphere.mp θ.2
      simpa [dist_eq_norm] using h
    have hsq : ((θ : EuclideanSpace ℝ (Fin 1)) i)^2 = 1 := by
      have h1 : ‖(θ : EuclideanSpace ℝ (Fin 1))‖^2 = ∑ j : Fin 1, ((θ : EuclideanSpace ℝ (Fin 1)) j)^2 := by
        rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
      have h2 : (∑ j : Fin 1, ((θ : EuclideanSpace ℝ (Fin 1)) j)^2) =
          ((θ : EuclideanSpace ℝ (Fin 1)) i)^2 := by
        rw [Fin.sum_univ_one, hi]
      have h3 : ‖(θ : EuclideanSpace ℝ (Fin 1))‖^2 = ((θ : EuclideanSpace ℝ (Fin 1)) i)^2 := by
        rw [h1, h2]
      rw [← h3, hnorm]; norm_num
    rcases (sq_eq_one_iff.mp hsq) with h1 | h1
    · have hfun : (fun j : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) j) = (fun _ : Fin 1 => (1:ℝ)) := by
        funext j
        rw [show j = i from Subsingleton.elim j i, h1]
      rw [hfun, h1]
      show a = (Polynomial.C ((a+b)/2) + Polynomial.C ((a-b)/2) * Polynomial.X).eval 1
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
    · have hfun : (fun j : Fin 1 => (θ : EuclideanSpace ℝ (Fin 1)) j) = (fun _ : Fin 1 => (-1:ℝ)) := by
        funext j
        rw [show j = i from Subsingleton.elim j i, h1]
      rw [hfun, h1]
      show b = (Polynomial.C ((a+b)/2) + Polynomial.C ((a-b)/2) * Polynomial.X).eval (-1)
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring

end Commons.Algebra.MvPolynomial
