import Mathlib
import Submission.Commons.Algebra.MvPolynomial.axisInv_harmonic_pole_eval_zero_eq_zero
import Submission.Commons.Algebra.MvPolynomial.x0_pow_not_eq_r2_mul
import Submission.Commons.Algebra.MvPolynomial.harmonic_part_axisInvariant
import Submission.Commons.Algebra.MvPolynomial.harmonic_X2_intersection
set_option linter.style.haveILetI false



open scoped BigOperators
open MvPolynomial

noncomputable section

namespace Commons.Algebra.MvPolynomial

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev X2 (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ j : Fin n, (MvPolynomial.X j)^2

lemma rename_mem_homogeneous {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    MvPolynomial.renameEquiv ℝ σ P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP ⊢
  simpa [MvPolynomial.renameEquiv_apply] using
    (MvPolynomial.IsHomogeneous.rename_isHomogeneous (f := (σ : Fin n → Fin n)) hP)

lemma rename_pderiv_equiv {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : Fin n)
    (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv t (MvPolynomial.renameEquiv ℝ σ P) =
      MvPolynomial.renameEquiv ℝ σ (MvPolynomial.pderiv (σ.symm t) P) := by
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply]
  have h := MvPolynomial.pderiv_rename (f := (σ : Fin n → Fin n)) σ.injective (σ.symm t) P
  have h2 : σ (σ.symm t) = t := by simp
  rwa [h2] at h

lemma rename_X2 (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.renameEquiv ℝ σ (X2 n) = X2 n := by
  calc
    MvPolynomial.renameEquiv ℝ σ (X2 n)
        = (MvPolynomial.rename (σ : Fin n → Fin n)) (∑ j : Fin n, (MvPolynomial.X j)^2) := by
            rw [MvPolynomial.renameEquiv_apply]
    _ = ∑ j : Fin n, (MvPolynomial.rename (σ : Fin n → Fin n)) ((MvPolynomial.X j)^2) := by
            rw [map_sum]
    _ = ∑ j : Fin n, ((MvPolynomial.rename (σ : Fin n → Fin n)) (MvPolynomial.X j))^2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_pow]
    _ = ∑ j : Fin n, (MvPolynomial.X (σ j))^2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [MvPolynomial.rename_X]
    _ = X2 n := by
            rw [X2]
            rw [Equiv.sum_comp σ (fun j : Fin n => (MvPolynomial.X j)^2)]

/-- lap commutes with a permutation rename -/
lemma rename_lap {n : ℕ} (σ : Equiv.Perm (Fin n))
    (P : MvPolynomial (Fin n) ℝ) :
    (∑ t : Fin n, MvPolynomial.pderiv t (MvPolynomial.pderiv t
        (MvPolynomial.renameEquiv ℝ σ P))) =
      MvPolynomial.renameEquiv ℝ σ (∑ t : Fin n,
        MvPolynomial.pderiv t (MvPolynomial.pderiv t P)) := by
  calc
    (∑ t : Fin n, MvPolynomial.pderiv t (MvPolynomial.pderiv t (MvPolynomial.renameEquiv ℝ σ P)))
        = ∑ t : Fin n, MvPolynomial.renameEquiv ℝ σ
            (MvPolynomial.pderiv (σ.symm t) (MvPolynomial.pderiv (σ.symm t) P)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [rename_pderiv_equiv σ t]
            rw [rename_pderiv_equiv σ t]
    _ = MvPolynomial.renameEquiv ℝ σ (∑ t : Fin n,
            MvPolynomial.pderiv (σ.symm t) (MvPolynomial.pderiv (σ.symm t) P)) := by
            rw [← map_sum]
    _ = MvPolynomial.renameEquiv ℝ σ (∑ s : Fin n,
            MvPolynomial.pderiv s (MvPolynomial.pderiv s P)) := by
            congr 1
            rw [Equiv.sum_comp σ.symm (fun s : Fin n =>
              MvPolynomial.pderiv s (MvPolynomial.pderiv s P))]

/-- homogeneous of degree zero polynomials are constants -/
lemma hom_zero_eq_C {n : ℕ} (Z : MvPolynomial (Fin n) ℝ)
    (hZ : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) : ∃ c : ℝ, Z = MvPolynomial.C c := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_zero] at hZ
  rcases Submodule.mem_one.mp hZ with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [MvPolynomial.C_eq_algebraMap]
  exact hc.symm

/-- the pole-zero core: harmonic part of X₀^k has nonzero value at e₀ -/
theorem zonal_pole_zero_value_ne_zero {n k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (Z0 R0 : MvPolynomial (Fin n) ℝ)
    (hZ0 : Z0 ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ0 : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z0)) = 0)
    (hR0 : R0 ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hdec0 : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) = Z0 + X2 n * R0) :
    MvPolynomial.eval (fun j : Fin n =>
      (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j) Z0 ≠ 0 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    -- hdec0 : (X 0)^0 = Z0 + X2*R0 i.e. 1 = ...
    rcases hom_zero_eq_C (n := n) Z0 hZ0 with ⟨c, hZc⟩
    have hval1 : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) Z0 = 1 := by
      have hdec1 : (1 : MvPolynomial (Fin n) ℝ) = Z0 + X2 n * R0 := by
        simpa using hdec0
      have he0 : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (Z0 + X2 n * R0) = 1 := by
        rw [← hdec1]
        simp
      have heX2 : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (X2 n) = 0 := by
        simp [X2]
      have heR : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (X2 n * R0) = 0 := by
        rw [MvPolynomial.eval_mul, heX2]
        ring
      have headd : MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) Z0 +
            MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (X2 n * R0) =
          MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (Z0 + X2 n * R0) := by
        rw [MvPolynomial.eval_add]
      calc
        MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) Z0
            = MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) Z0 +
                MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (X2 n * R0) := by rw [heR]; ring
        _ = MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) (Z0 + X2 n * R0) := headd
        _ = 1 := he0
    have hconst : ∀ y : Fin n → ℝ, MvPolynomial.eval y Z0 = c := by
      intro y
      rw [hZc]
      simp
    have hc1 : c = 1 := by
      calc c = MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) Z0 := (hconst (fun _ : Fin n => (0 : ℝ))).symm
           _ = 1 := hval1
    intro hv
    have hv' : MvPolynomial.eval (fun j : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j) Z0 = 1 := by
      rw [hconst (fun j : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)]
      exact hc1
    rw [hv'] at hv
    norm_num at hv
  · have hk1 : 1 ≤ k := by omega
    have hZne : Z0 ≠ 0 := by
      intro hz
      have hX : (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k = X2 n * R0 := by
        rw [hdec0, hz]
        simp
      exact x0_pow_not_eq_r2_mul (n := n) (k := k) hn2 hk1 R0 hR0 hX
    have hIP : ∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
        L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
        ∀ x : EuclideanSpace ℝ (Fin n),
          MvPolynomial.eval (fun i : Fin n => (L x) i) Z0 =
            MvPolynomial.eval (fun i : Fin n => x i) Z0 :=
      harmonic_part_axisInvariant (n := n) (k := k) Z0 R0 hZ0 hlapZ0 hR0 hdec0
    intro hval0
    have hz : Z0 = 0 :=
      axisInv_harmonic_pole_eval_zero_eq_zero (n := n) (k := k) hn2 Z0 hZ0 hlapZ0 hIP hval0
    exact hZne hz

section FinalTransport

variable {n : ℕ}

/-- linear form `(∑_j C (single i 1 j) * X j)` is just `X i` -/
lemma zpo_linearForm_eq_X (i : Fin n) :
    (∑ j : Fin n, (MvPolynomial.C (((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)))
        * (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) = MvPolynomial.X i := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end FinalTransport

section Main

theorem zonal_pole_value_ne_zero
    {n : ℕ} {k : ℕ} (i : Fin n) (hji : ∃ j : Fin n, j ≠ i)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hdec : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) * (MvPolynomial.X j)) ^ k) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    MvPolynomial.eval (fun j : Fin n => ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j) Z ≠ 0 := by
  classical
  haveI : NeZero n := ⟨by
    intro hn
    subst n
    exact Fin.elim0 i⟩
  have hn2 : 2 ≤ n := by
    rcases hji with ⟨j, hji'⟩
    by_contra hnle
    apply hji'
    apply Fin.ext
    omega
  have hdecXi : ((MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ k) =
      Z + X2 n * R := by
    rw [← zpo_linearForm_eq_X i]
    simpa [X2] using hdec
  let σ : Equiv.Perm (Fin n) := Equiv.swap i (0 : Fin n)
  have hσi : σ i = (0 : Fin n) := by
    simp [σ]
  let Z0 : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ σ Z
  let R0 : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ σ R
  have hZ0 : Z0 ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
    dsimp [Z0]
    exact rename_mem_homogeneous σ Z hZmem
  have hR0 : R0 ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) := by
    dsimp [R0]
    exact rename_mem_homogeneous σ R hRmem
  have hlapZ0 : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z0)) = 0 := by
    dsimp [Z0]
    rw [rename_lap σ Z]
    rw [hlapZ]
    simp
  have hdec0 : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) = Z0 + X2 n * R0 := by
    have hren : MvPolynomial.renameEquiv ℝ σ ((MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ k)
        = MvPolynomial.renameEquiv ℝ σ (Z + X2 n * R) := by
      rw [hdecXi]
    have hLHS : MvPolynomial.renameEquiv ℝ σ ((MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ k)
        = (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k := by
      rw [map_pow]
      have hX : MvPolynomial.renameEquiv ℝ σ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)
          = (MvPolynomial.X (σ i) : MvPolynomial (Fin n) ℝ) := by
        rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
      rw [hX, hσi]
    have hRHS : MvPolynomial.renameEquiv ℝ σ (Z + X2 n * R) = Z0 + X2 n * R0 := by
      dsimp [Z0, R0]
      rw [map_add]
      congr 1
      rw [map_mul]
      rw [rename_X2 n σ]
    calc
      (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k
          = MvPolynomial.renameEquiv ℝ σ ((MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ k) := hLHS.symm
      _ = MvPolynomial.renameEquiv ℝ σ (Z + X2 n * R) := hren
      _ = Z0 + X2 n * R0 := hRHS
  have hcore : MvPolynomial.eval (fun j : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j) Z0 ≠ 0 :=
    zonal_pole_zero_value_ne_zero (n := n) (k := k) hn2 Z0 R0 hZ0 hlapZ0 hR0 hdec0
  have htrans : MvPolynomial.eval (fun j : Fin n =>
        ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) j) Z
      = MvPolynomial.eval (fun j : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j) Z0 := by
    dsimp [Z0]
    rw [MvPolynomial.renameEquiv_apply]
    rw [MvPolynomial.eval_rename]
    apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f Z)
    funext j
    dsimp [σ]
    by_cases hj : j = i
    · subst j
      simp
    · have hnot : (Equiv.swap i (0 : Fin n)) j ≠ (0 : Fin n) := by
        intro hz
        apply hj
        exact (Equiv.swap i (0 : Fin n)).injective (by simpa using (show (Equiv.swap i (0 : Fin n)) j = (Equiv.swap i (0 : Fin n)) i from by rw [hz]; simp))
      simp [hj, hnot]
  rw [htrans]
  exact hcore

end Main

end Commons.Algebra.MvPolynomial
