import Mathlib
import Submission.Commons.Algebra.MvPolynomial.zonal_even_eigenvalue_sign
import Submission.Commons.Algebra.MvPolynomial.zonal_even_eigenvalue_ne_zero
import Submission.Commons.Algebra.MvPolynomial.zonal_radial
import Submission.Commons.Analysis.MeasureTheory.zonal_fibre_integral_abs_poly

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 1600000

open scoped BigOperators
open MeasureTheory

namespace Commons.Algebra.MvPolynomial

private abbrev Ez (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Sp (n : ℕ) := Metric.sphere (0 : Ez n) 1

private def zdp_pole {n : ℕ} [NeZero n] : Fin n → ℝ := fun j => if j = 0 then 1 else 0

private lemma zdp_pole_eq_single {n : ℕ} [NeZero n] :
    zdp_pole (n := n) = (fun j : Fin n => (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : Ez n) j) := by
  funext j
  rw [EuclideanSpace.single_apply]
  by_cases h : j = (0 : Fin n)
  · subst h; simp [zdp_pole]
  · simp [zdp_pole, h]

private lemma zdp_sphere_sum_sq {n : ℕ} (θ : Sp n) :
    (∑ i : Fin n, ((θ : Ez n) i) ^ 2) = 1 := by
  have h1 : ‖(θ : Ez n)‖ ^ 2 = ∑ i : Fin n, ((θ : Ez n) i) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
  have hnorm : ‖(θ : Ez n)‖ = 1 := by
    have h := Metric.mem_sphere.mp θ.2; simpa [dist_eq_norm] using h
  rw [← h1, hnorm]; norm_num

private lemma zdp_eval_zhSq_sphere {n : ℕ} [NeZero n] (θ : Sp n) :
    MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) zh_Sq
      = 1 - ((θ : Ez n) (0 : Fin n)) ^ 2 := by
  have h1 : MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) zh_Sq
      = ∑ i : {i : Fin n // i ≠ 0}, ((θ : Ez n) (i : Fin n)) ^ 2 := by
    dsimp [zh_Sq]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_pow, MvPolynomial.eval_X]
  rw [h1]
  have h2 : (∑ i : {i : Fin n // i ≠ 0}, ((θ : Ez n) (i : Fin n)) ^ 2)
      = ∑ i ∈ (Finset.univ.erase (0 : Fin n)), ((θ : Ez n) i) ^ 2 :=
    (Finset.sum_subtype (s := Finset.univ.erase (0 : Fin n))
      (fun x => by simp [Finset.mem_erase]) (fun i : Fin n => ((θ : Ez n) i) ^ 2)).symm
  rw [h2]
  have h3 := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
    (fun i => ((θ : Ez n) i) ^ 2) (Finset.mem_univ (0 : Fin n))
  rw [zdp_sphere_sum_sq θ] at h3
  linarith

private lemma zdp_eval_range_sum_pole {n : ℕ} [NeZero n] {k r : ℕ} (ch : ℕ → ℝ) :
    MvPolynomial.eval (zdp_pole (n := n))
      (∑ j ∈ Finset.range (r + 1), ch j • zh_zterm (n := n) k j) = ch 0 := by
  classical
  rw [MvPolynomial.eval_sum]
  have hterm : ∀ j, MvPolynomial.eval (zdp_pole (n := n))
      (ch j • zh_zterm (n := n) k j)
      = ch j * (zdp_pole (n := n) (0 : Fin n)) ^ (k - 2 * j)
          * (MvPolynomial.eval (zdp_pole (n := n)) zh_Sq) ^ j := by
    intro j
    simp only [MvPolynomial.smul_eq_C_mul, zh_zterm, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_pow, MvPolynomial.eval_X]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hSq : MvPolynomial.eval (zdp_pole (n := n)) zh_Sq = 0 := by
    dsimp [zh_Sq]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_pow, MvPolynomial.eval_X]
    have hi : (i : Fin n) ≠ (0 : Fin n) := i.2
    simp [zdp_pole, hi]
  rw [Finset.sum_eq_single 0]
  · rw [hSq]
    simp [zdp_pole]
  · intro j _ hj
    rw [hSq, zero_pow hj]
    ring
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos r)) h

private theorem zdp_axis0_profile_extract {n m : ℕ} [NeZero n] (hn : 2 ≤ n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m))
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m - 2))
    (hdec : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ)) ^ (2 * m) = Z +
        (∑ j : Fin n, (MvPolynomial.X j) ^ 2) * R) :
    ∃ ch : ℕ → ℝ,
      ch 0 ≠ 0 ∧
      (∀ j : ℕ, j < m →
        ch j * (((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ))
          + ch (j + 1) * ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) = 0) ∧
      (∀ θ : Sp n,
        MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z =
          ∑ j ∈ Finset.range (m + 1), ch j * ((θ : Ez n) (0 : Fin n)) ^ (2 * m - 2 * j)
            * (1 - ((θ : Ez n) (0 : Fin n)) ^ 2) ^ j) ∧
      (MvPolynomial.eval (fun j : Fin n =>
          (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : Ez n) j) Z = ch 0) := by
  classical
  have hk : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by norm_num)
  have hIP := harmonic_part_axisInvariant (n := n) (k := 2 * m) Z R hZmem hlapZ hRmem hdec
  rcases axisInv_homogeneous_structure (n := n) (k := 2 * m) hn Z hZmem hIP with ⟨c, hc⟩
  let ch : ℕ → ℝ := zh_extc (2 * m / 2) c
  have hZrange : Z = ∑ j ∈ Finset.range (2 * m / 2 + 1), ch j • zh_zterm (n := n) (2 * m) j := by
    rw [hc]
    dsimp [ch]
    simpa only [zh_zterm, zh_Sq] using (zh_fin_sum_range (n := n) (2 * m) c)
  have hch0eq : ch 0 = MvPolynomial.eval (zdp_pole (n := n)) Z := by
    rw [hZrange]
    rw [show (2 * m / 2 + 1) = (m + 1) from by rw [hk]]
    exact (zdp_eval_range_sum_pole (n := n) (k := 2 * m) (r := m) ch).symm
  have hZpole : MvPolynomial.eval (zdp_pole (n := n)) Z ≠ 0 := by
    have hh := zonal_pole_zero_value_ne_zero (n := n) (k := 2 * m) hn Z R hZmem hlapZ hRmem
      (by simpa [X2] using hdec)
    rw [zdp_pole_eq_single]
    exact hh
  have hch0ne : ch 0 ≠ 0 := by rw [hch0eq]; exact hZpole
  refine ⟨ch, hch0ne, ?_, ?_, ?_⟩
  · intro j hj
    have hj1 : j + 1 ≤ 2 * m / 2 := by rw [hk]; omega
    have h1 := zh_coeff_lap_zonal_sum (n := n) hn (2 * m) ch j hj1
    have hzl : zh_lap (n := n) (∑ jj ∈ Finset.range (2 * m / 2 + 1),
        ch jj • zh_zterm (n := n) (2 * m) jj) = 0 := by
      rw [← hZrange]; dsimp [zh_lap]; exact hlapZ
    rw [hzl] at h1
    rw [MvPolynomial.coeff_zero] at h1
    have ha : zh_alpha (2 * m) j = (((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ)) := by
      rw [zh_alpha, Nat.cast_mul]
    have hb : zh_beta n (2 * m) (j + 1) = ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) := by
      rw [zh_beta]
    rw [ha, hb] at h1
    exact h1.symm
  · intro θ
    have hsum : ∀ j, MvPolynomial.eval (fun i : Fin n => (θ : Ez n) i)
        (ch j • zh_zterm (n := n) (2 * m) j)
        = ch j * ((θ : Ez n) (0 : Fin n)) ^ (2 * m - 2 * j)
            * (MvPolynomial.eval (fun i : Fin n => (θ : Ez n) i) zh_Sq) ^ j := by
      intro j
      simp only [MvPolynomial.smul_eq_C_mul, zh_zterm, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_pow, MvPolynomial.eval_X]
      ring
    rw [hZrange, MvPolynomial.eval_sum, show (2 * m / 2 + 1) = (m + 1) from by rw [hk]]
    rw [Finset.sum_congr rfl (fun j _ => hsum j)]
    rw [Finset.sum_congr rfl (fun j _ => by rw [zdp_eval_zhSq_sphere θ])]
  · rw [hch0eq, zdp_pole_eq_single]

private theorem zdp_profile_extract {n m : ℕ} (i : Fin n) (hn : 2 ≤ n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m))
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m - 2))
    (hdec : ((∑ j : Fin n,
        (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : Ez n) j)) * (MvPolynomial.X j)) ^ (2 * m)) = Z +
        (∑ j : Fin n, (MvPolynomial.X j) ^ 2) * R) :
    ∃ ch : ℕ → ℝ,
      ch 0 ≠ 0 ∧
      (∀ j : ℕ, j < m →
        ch j * (((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ))
          + ch (j + 1) * ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) = 0) ∧
      (∀ θ : Sp n,
        MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z =
          ∑ j ∈ Finset.range (m + 1), ch j * ((θ : Ez n) i) ^ (2 * m - 2 * j)
            * (1 - ((θ : Ez n) i) ^ 2) ^ j) ∧
      (MvPolynomial.eval (fun j : Fin n =>
          (EuclideanSpace.single i (1 : ℝ) : Ez n) j) Z = ch 0) := by
  classical
  haveI : NeZero n := ⟨by rintro rfl; exact i.elim0⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap i (0 : Fin n)
  have hσi : σ i = (0 : Fin n) := by simp [σ]
  have hσ0 : σ (0 : Fin n) = i := by simp [σ]
  have hσinv : ∀ k : Fin n, σ (σ k) = k := by
    intro k
    show Equiv.swap i (0 : Fin n) (Equiv.swap i (0 : Fin n) k) = k
    simp only [Equiv.swap_apply_def]
    by_cases h1 : k = i
    · subst h1; simp
    · by_cases h2 : k = (0 : Fin n)
      · subst h2; simp [h1]
      · simp [h1, h2]
  let Z' : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ σ Z
  let R' : MvPolynomial (Fin n) ℝ := MvPolynomial.renameEquiv ℝ σ R
  have hZ'mem : Z' ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) := by
    dsimp [Z']; exact rename_mem_homogeneous σ Z hZmem
  have hlapZ' : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z')) = 0 := by
    dsimp [Z']; rw [rename_lap σ Z, hlapZ, map_zero]
  have hR'mem : R' ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m - 2) := by
    dsimp [R']; exact rename_mem_homogeneous σ R hRmem
  have hdec2 : ((MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) ^ (2 * m)
      = Z + (∑ j : Fin n, (MvPolynomial.X j) ^ 2) * R := by
    rw [← zpo_linearForm_eq_X i]; exact hdec
  have hdec' : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ)) ^ (2 * m)
      = Z' + (∑ j : Fin n, (MvPolynomial.X j) ^ 2) * R' := by
    have h := congrArg (MvPolynomial.renameEquiv ℝ σ) hdec2
    simp only [map_pow, map_add, map_mul] at h
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hσi,
      Commons.Algebra.MvPolynomial.rename_X2 n σ] at h
    simpa only [Z', R'] using h
  obtain ⟨ch, hch0ne, hrec, hrad', hval'⟩ :=
    zdp_axis0_profile_extract hn Z' R' hZ'mem hlapZ' hR'mem hdec'
  refine ⟨ch, hch0ne, hrec, ?_, ?_⟩
  · intro θ
    let y : Ez n := WithLp.toLp 2 (fun k : Fin n => (θ : Ez n) (σ k))
    have hycoe : ∀ k : Fin n, (y : Ez n) k = (θ : Ez n) (σ k) := fun k => rfl
    have hynorm : ‖y‖ = 1 := by
      have hsq : ‖y‖ ^ 2 = ∑ k : Fin n, ((θ : Ez n) (σ k)) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [hycoe, Real.norm_eq_abs, sq_abs]
      have hsum : (∑ k : Fin n, ((θ : Ez n) (σ k)) ^ 2) = ∑ k : Fin n, ((θ : Ez n) k) ^ 2 :=
        Equiv.sum_comp σ (fun k => ((θ : Ez n) k) ^ 2)
      have hθsq : (∑ k : Fin n, ((θ : Ez n) k) ^ 2) = 1 := by
        have h1 : ‖(θ : Ez n)‖ ^ 2 = ∑ k, ((θ : Ez n) k) ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
        have h2 : ‖(θ : Ez n)‖ = 1 := by
          have := Metric.mem_sphere.mp θ.2; simpa [dist_eq_norm] using this
        rw [← h1, h2]; norm_num
      have hsq2 : ‖y‖ ^ 2 = 1 := by rw [hsq, hsum, hθsq]
      nlinarith [norm_nonneg y, hsq2]
    have hymem : y ∈ Sp n := by
      rw [Metric.mem_sphere, dist_eq_norm]; simpa using hynorm
    have hkey := hrad' ⟨y, hymem⟩
    have hconv : MvPolynomial.eval (fun j : Fin n => (y : Ez n) j) Z'
        = MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z := by
      dsimp [Z']
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
      apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f Z)
      funext k
      rw [Function.comp_apply, hycoe (σ k), hσinv k]
    rw [← hconv, hkey]
    apply Finset.sum_congr rfl
    intro j _
    rw [hycoe 0, hσ0]
  · have hconv : MvPolynomial.eval (fun j : Fin n =>
        (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : Ez n) j) Z'
        = MvPolynomial.eval (fun j : Fin n =>
            (EuclideanSpace.single i (1 : ℝ) : Ez n) j) Z := by
      dsimp [Z']
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
      apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f Z)
      funext k
      rw [Function.comp_apply]
      by_cases hk : k = i
      · subst hk; rw [hσi]; simp
      · have hσk : σ k ≠ (0 : Fin n) := by
          intro hh
          apply hk
          have h2 := congrArg σ hh
          rw [hσinv k, hσ0] at h2
          exact h2
        rw [Pi.single_eq_of_ne hσk, Pi.single_eq_of_ne hk]
    rw [← hval', hconv]

private theorem zdp_ratio_bound {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (ch : ℕ → ℝ)
    (hch0 : ch 0 ≠ 0)
    (hrec : ∀ j : ℕ, j < m →
        ch j * (((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ))
          + ch (j + 1) * ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) = 0) :
    |ch 0| ≤ ((n : ℝ) - 1) ^ (n - 2) * (m : ℝ) ^ (n - 2) * |ch m| := by
  have hn2r : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hm1r : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set A : ℕ → ℝ := fun j => ((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ) with hA
  set B : ℕ → ℝ := fun j => ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) with hB
  have hAeq : ∀ j, A j = ((2 * m - 2 * j : ℕ) : ℝ) * ((2 * m - 2 * j - 1 : ℕ) : ℝ) :=
    fun j => by simp only [hA]
  have hBeq : ∀ j, B j = ((2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) : ℝ) :=
    fun j => by simp only [hB]
  have hrec' : ∀ j, j < m → ch j * A j + ch (j + 1) * B j = 0 := by
    intro j hj; rw [hAeq j, hBeq j]; exact hrec j hj
  have hApos : ∀ j, j < m → 0 < A j := by
    intro j hj
    have e1 : (2 * m - 2 * j : ℕ) = 2 * (m - j) := by omega
    have e2 : (2 * m - 2 * j - 1 : ℕ) = 2 * (m - j) - 1 := by omega
    have hAj : A j = ((2 * (m - j) : ℕ) : ℝ) * (((2 * (m - j) - 1) : ℕ) : ℝ) := by
      rw [hAeq j, e2, e1]
    rw [hAj]
    apply mul_pos <;> (rw [Nat.cast_pos]; omega)
  have hBpos : ∀ j, j < m → 0 < B j := by
    intro j hj
    rw [hBeq j, Nat.cast_pos]
    exact Nat.mul_pos (by omega) (by omega)
  have hstep : ∀ j, j < m → |ch (j + 1)| = |ch j| * (A j / B j) := by
    intro j hj
    have h := hrec' j hj
    have hBne : B j ≠ 0 := ne_of_gt (hBpos j hj)
    have hcx : ch (j + 1) = -(ch j * A j) / B j := by
      rw [eq_div_iff hBne]; linarith
    rw [hcx, abs_div, abs_neg, abs_mul, abs_of_pos (hBpos j hj), abs_of_pos (hApos j hj)]
    ring_nf
  have hprod : ∀ k, k ≤ m → |ch k| = |ch 0| * ∏ j ∈ Finset.range k, (A j / B j) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hk' : k < m := by omega
        rw [Finset.prod_range_succ, hstep k hk', ih (by omega), mul_assoc]
  have hchm : |ch m| = |ch 0| * ∏ j ∈ Finset.range m, (A j / B j) := hprod m le_rfl
  have hprodA : ∏ j ∈ Finset.range m, A j
      = ∏ j ∈ Finset.range m, ((2*(j:ℝ)+2) * (2*(j:ℝ)+1)) := by
    rw [← Finset.prod_range_reflect A m]
    apply Finset.prod_congr rfl
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have e1 : (2 * m - 2 * (m - 1 - j) : ℕ) = 2 * j + 2 := by omega
    have e2 : (2 * m - 2 * (m - 1 - j) - 1 : ℕ) = 2 * j + 1 := by omega
    rw [hAeq (m - 1 - j), e2, e1]
    push_cast
    ring
  have hprodB : ∏ j ∈ Finset.range m, B j
      = ∏ j ∈ Finset.range m, ((2*(j:ℝ)+2) * ((n:ℝ) + 2*(j:ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro j _
    have e1 : (2 * (j + 1) * (n + 2 * (j + 1) - 3) : ℕ) = (2 * j + 2) * (n + 2 * j - 1) := by
      have h : (n + 2 * (j + 1) - 3 : ℕ) = n + 2 * j - 1 := by omega
      rw [h]; ring
    rw [hBeq j, e1, Nat.cast_mul]
    have hc1 : ((n + 2 * j - 1 : ℕ) : ℝ) = (n : ℝ) + 2 * (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n + 2 * j)]; push_cast; ring
    rw [hc1]
    push_cast
    ring
  have hP2pos : 0 < ∏ j ∈ Finset.range m, (2*(j:ℝ)+2) :=
    Finset.prod_pos (fun j _ => by positivity)
  have hratio : ∏ j ∈ Finset.range m, (A j / B j)
      = ∏ j ∈ Finset.range m, ((2*(j:ℝ)+1) / ((n:ℝ) + 2*(j:ℝ) - 1)) := by
    rw [Finset.prod_div_distrib, hprodA, hprodB]
    simp only [Finset.prod_mul_distrib]
    rw [mul_div_mul_left _ _ (ne_of_gt hP2pos), ← Finset.prod_div_distrib]
  have hnumR : ∏ j ∈ Finset.range m, ((j:ℝ)+1) = (m.factorial : ℝ) := by
    rw [show (∏ j ∈ Finset.range m, ((j:ℝ)+1)) = ∏ j ∈ Finset.range m, ((j+1:ℕ):ℝ) from
      Finset.prod_congr rfl (fun j _ => by push_cast; ring)]
    rw [← Nat.cast_prod, Nat.factorial_eq_prod_range_add_one]
  have hdenR : ∏ j ∈ Finset.range m, ((j:ℝ)+(n:ℝ)-1) = (((n-1).ascFactorial m : ℕ) : ℝ) := by
    rw [show (∏ j ∈ Finset.range m, ((j:ℝ)+(n:ℝ)-1))
        = ∏ j ∈ Finset.range m, (((n-1)+j:ℕ):ℝ) from
      Finset.prod_congr rfl (fun j _ => by
        have h1 : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        rw [Nat.cast_add, h1]; push_cast; ring)]
    rw [← Nat.cast_prod, ← Nat.ascFactorial_eq_prod_range]
  have hasc : (n-1).ascFactorial m = m.factorial * (m+n-2).choose (n-2) := by
    have h := Nat.ascFactorial_eq_factorial_mul_choose (n := n-2) (k := m)
    rw [show n - 2 + 1 = n - 1 from by omega] at h
    rw [h, show n - 2 + m = m + n - 2 from by omega]
    congr 1
    have hsym := Nat.choose_symm (show n - 2 ≤ m + n - 2 by omega)
    rw [show m + n - 2 - (n - 2) = m from by omega] at hsym
    exact hsym
  have hprodform : ∏ j ∈ Finset.range m, ((j:ℝ)+1)/((j:ℝ)+(n:ℝ)-1)
      = 1 / ((Nat.choose (m + n - 2) (n - 2) : ℕ) : ℝ) := by
    rw [Finset.prod_div_distrib, hnumR, hdenR, hasc, Nat.cast_mul]
    have hmf : (m.factorial : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Nat.factorial_ne_zero m
    have hch : (((m+n-2).choose (n-2) : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Nat.choose_ne_zero_iff.mpr (by omega)
    field_simp
  have hfac : ∀ j, j < m → ((j:ℝ)+1) / ((j:ℝ) + (n:ℝ) - 1)
      ≤ (2*(j:ℝ)+1) / ((n:ℝ) + 2*(j:ℝ) - 1) := by
    intro j hj
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have hb1 : 0 < (j:ℝ) + (n:ℝ) - 1 := by linarith
    have hb2 : 0 < (n:ℝ) + 2*(j:ℝ) - 1 := by linarith
    rw [div_le_div_iff₀ hb1 hb2]
    nlinarith [hn2r, hj0, mul_nonneg hj0 (by linarith : (0:ℝ) ≤ (n:ℝ)-2)]
  have hleprod : ∏ j ∈ Finset.range m, ((j:ℝ)+1)/((j:ℝ)+(n:ℝ)-1)
      ≤ ∏ j ∈ Finset.range m, ((2*(j:ℝ)+1) / ((n:ℝ)+2*(j:ℝ)-1)) := by
    apply Finset.prod_le_prod
    · intro j _
      apply div_nonneg (by positivity) (by
        have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        linarith)
    · intro j hj; exact hfac j (Finset.mem_range.mp hj)
  have hchoose_le : ((m+n-2).choose (n-2) : ℝ) ≤ ((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2) := by
    have hpow : (((m+n-2 : ℕ)) : ℝ) ^ (n-2) ≤ (((n:ℝ)-1) * (m:ℝ)) ^ (n-2) := by
      apply pow_le_pow_left₀ (by positivity) _ (n-2)
      rw [Nat.cast_sub (by omega : 2 ≤ m + n)]
      push_cast
      nlinarith [hm1r, hn2r]
    have h1 : ((m+n-2).choose (n-2) : ℝ) ≤ ((m+n-2 : ℕ) : ℝ) ^ (n-2) := by
      exact_mod_cast Nat.choose_le_pow (m+n-2) (n-2)
    calc ((m+n-2).choose (n-2) : ℝ) ≤ ((m+n-2 : ℕ) : ℝ) ^ (n-2) := h1
      _ ≤ (((n:ℝ)-1) * (m:ℝ)) ^ (n-2) := hpow
      _ = ((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2) := mul_pow _ _ _
  have hCpos : 0 < ((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2) := by
    apply mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _)
  have hchpos : (0:ℝ) < ((m+n-2).choose (n-2) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : n - 2 ≤ m + n - 2)
  have hbig : 1 / (((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2))
      ≤ ∏ j ∈ Finset.range m, (A j / B j) := by
    rw [hratio]
    refine le_trans ?_ hleprod
    rw [hprodform]
    exact one_div_le_one_div_of_le hchpos hchoose_le
  have hCP : 1 ≤ (((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2)) * (∏ j ∈ Finset.range m, (A j / B j)) := by
    have h := mul_le_mul_of_nonneg_left hbig (le_of_lt hCpos)
    have h2 : (((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2)) * (1 / (((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2))) = 1 := by
      rw [mul_one_div, div_self (ne_of_gt hCpos)]
    rwa [h2] at h
  calc |ch 0| = |ch 0| * 1 := (mul_one _).symm
    _ ≤ |ch 0| * ((((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2)) * (∏ j ∈ Finset.range m, (A j / B j))) :=
        mul_le_mul_of_nonneg_left hCP (abs_nonneg _)
    _ = ((n:ℝ)-1)^(n-2) * (m:ℝ)^(n-2) * |ch m| := by rw [hchm]; ring




theorem zonal_eigenvalue_poly_decay
    {n : ℕ} (i : Fin n) (hn : 2 ≤ n) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ K : ℕ, ∀ (m : ℕ) (hm : 1 ≤ m)
      (Z R : MvPolynomial (Fin n) ℝ)
      (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m))
      (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
      (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m - 2))
      (hdec : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) * (MvPolynomial.X j)) ^ (2 * m)) = Z +
          (∑ j : Fin n, (MvPolynomial.X j)^2) * R)
      (c : ℝ)
      (hsc : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
          ∂MeasureTheory.volume.toSphere) = c * MvPolynomial.eval (fun j : Fin n => (u : EuclideanSpace ℝ (Fin n)) j) Z),
      c0 * (m : ℝ) ^ (-(K : ℤ)) ≤ |c| := by
  classical
  haveI : NeZero n := ⟨by rintro rfl; exact i.elim0⟩
  let Fib : Type := {j : Fin n // j ≠ i}
  haveI hFibne : Nonempty Fib := by
    have hcard : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    exact ⟨⟨j, hj⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ Fib) := inferInstance
  let s : ℝ := (MeasureTheory.volume.toSphere :
      Measure (Metric.sphere (0 : EuclideanSpace ℝ Fib) 1)).real Set.univ
  have hs : 0 < s := by
    dsimp [s]
    rw [MeasureTheory.measureReal_def]
    refine ENNReal.toReal_pos ?_ ?_
    · rw [ne_eq, MeasureTheory.Measure.measure_univ_eq_zero]
      exact MeasureTheory.Measure.toSphere_ne_zero (MeasureTheory.volume)
    · exact MeasureTheory.measure_ne_top _ _
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  refine ⟨s / (((n : ℝ) - 1) ^ (n - 2) * ((n : ℝ) + 1)), ?_, n, ?_⟩
  · apply div_pos hs
    exact mul_pos (pow_pos hn1pos _) (by linarith)
  · intro m hm Z R hZmem hlapZ hRmem hdec c hsc
    obtain ⟨ch, hch0ne, hrec, hrad, hval⟩ := zdp_profile_extract i hn Z R hZmem hlapZ hRmem hdec
    let F : ℝ → ℝ := fun t =>
      |t| * (∑ j ∈ Finset.range (m + 1), ch j * t ^ (2 * m - 2 * j) * (1 - t ^ 2) ^ j)
    let eS : Sp n := ⟨EuclideanSpace.single i (1 : ℝ), by
      rw [Metric.mem_sphere, dist_eq_norm]; simp⟩
    have heScoe : (eS : Ez n) = EuclideanSpace.single i (1 : ℝ) := rfl
    have heval : MvPolynomial.eval (fun j : Fin n => (eS : Ez n) j) Z = ch 0 := by
      rw [heScoe]; exact hval
    have hE := hsc eS
    rw [heval] at hE
    have hstep0 : (∫ θ : Sp n,
          |inner ℝ (eS : Ez n) (θ : Ez n)| *
            MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z
        ∂MeasureTheory.volume.toSphere)
        = ∫ θ : Sp n, F ((θ : Ez n) i) ∂MeasureTheory.volume.toSphere := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [hrad θ]
      have habs : |inner ℝ (eS : Ez n) (θ : Ez n)| = |(θ : Ez n) i| := by
        rw [heScoe, EuclideanSpace.inner_single_left]; simp
      rw [habs]
    have hfib := Commons.Analysis.MeasureTheory.zonal_fibre_integral (n := n) (i := i) hn F
    have hinner : ∀ t : ℝ,
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ Fib) 1,
            F t * (1 - t ^ 2) ^ (((Fintype.card Fib : ℝ) - 2) / 2)
          ∂MeasureTheory.volume.toSphere)
          = s * (F t * (1 - t ^ 2) ^ (((Fintype.card Fib : ℝ) - 2) / 2)) := by
      intro t
      rw [MeasureTheory.integral_const]
      simp only [smul_eq_mul]
      rfl
    have hcardi : Fintype.card Fib = n - 1 := by
      dsimp [Fib]
      rw [Fintype.card_subtype_compl (p := fun j : Fin n => j = i),
        Fintype.card_subtype_eq, Fintype.card_fin]
    have hexp : (((Fintype.card Fib : ℝ) - 2) / 2) = ((n : ℝ) - 3) / 2 := by
      rw [hcardi]
      have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
      rw [h1]; ring
    have hLHS : (∫ θ : Sp n,
          |inner ℝ (eS : Ez n) (θ : Ez n)| *
            MvPolynomial.eval (fun j : Fin n => (θ : Ez n) j) Z
        ∂MeasureTheory.volume.toSphere)
        = s * (- ch m / ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2))) := by
      rw [hstep0, hfib]
      have hcong : (∫ t : ℝ in Set.Ioo (-1) 1,
            ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ Fib) 1,
              F t * (1 - t ^ 2) ^ (((Fintype.card Fib : ℝ) - 2) / 2)
            ∂MeasureTheory.volume.toSphere)
          = ∫ t : ℝ in Set.Ioo (-1) 1,
              s * (F t * (1 - t ^ 2) ^ (((Fintype.card Fib : ℝ) - 2) / 2)) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hinner t]
      rw [hcong, MeasureTheory.integral_const_mul]
      congr 1
      rw [hexp]
      rw [show (∫ t : ℝ in Set.Ioo (-1) 1, F t * (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2))
          = ∫ t : ℝ in Set.Ioo (-1) 1,
              |t| * (∑ j ∈ Finset.range (m + 1), ch j * t ^ (2 * m - 2 * j) * (1 - t ^ 2) ^ j)
                * (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) from by
            apply integral_congr_ae
            filter_upwards with t
            simp only [F]]
      exact Commons.Analysis.MeasureTheory.zonal_profile_integral_value n hn m ch hrec
    have heqn : s * (- ch m / ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2))) = c * ch 0 := by
      rw [← hLHS]; exact hE
    have hDpos : 0 < (2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2) := by
      apply mul_pos
      · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have : (0 : ℝ) < ((n : ℝ) - 1) / 2 := by linarith
        linarith
    have hc_eq : c = s * (- ch m)
        / (((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2)) * ch 0) := by
      rw [eq_div_iff (mul_ne_zero (ne_of_gt hDpos) hch0ne)]
      have h2 : s * (- ch m / ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2)))
            * ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2)) = s * (- ch m) := by
        rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hDpos)]
      calc c * (((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2)) * ch 0)
          = (c * ch 0) * ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2)) := by ring
        _ = (s * (- ch m / ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2))))
              * ((2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2)) := by rw [← heqn]
        _ = s * (- ch m) := h2
    -- ===== final bound =====
    set D : ℝ := (2 * (m : ℝ) - 1) * ((m : ℝ) + ((n : ℝ) - 1) / 2) with hDdef
    have hDpos' : 0 < D := by rw [hDdef]; exact hDpos
    have hc_eqD : c = s * (- ch m) / (D * ch 0) := by rw [hDdef]; exact hc_eq
    have hcab : |c| = s * |ch m| / (D * |ch 0|) := by
      rw [hc_eqD, abs_div, abs_mul, abs_mul, abs_neg, abs_of_pos hs, abs_of_pos hDpos']
    have habs0 : 0 < |ch 0| := abs_pos.mpr hch0ne
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    set K : ℝ := ((n : ℝ) - 1) ^ (n - 2) * (m : ℝ) ^ (n - 2) with hKdef
    have hKpos : 0 < K := by
      rw [hKdef]
      exact mul_pos (pow_pos hn1pos _) (pow_pos (by linarith : (0:ℝ) < (m:ℝ)) _)
    have hrat : |ch 0| ≤ ((n : ℝ) - 1) ^ (n - 2) * (m : ℝ) ^ (n - 2) * |ch m| :=
      zdp_ratio_bound hn hm ch hch0ne hrec
    have hle : |ch 0| ≤ K * |ch m| := by rw [hKdef]; exact hrat
    have hineq : |ch 0| ≤ |ch m| * K := by rw [mul_comm]; exact hle
    have hmain : s / (D * K) ≤ |c| := by
      rw [div_le_iff₀ (mul_pos hDpos' hKpos)]
      rw [hcab]
      have hsimp : s * |ch m| / (D * |ch 0|) * (D * K) = s * (|ch m| * K) / |ch 0| := by
        field_simp
      rw [hsimp, le_div_iff₀ habs0]
      exact mul_le_mul_of_nonneg_left hineq (le_of_lt hs)
    have hDbound : D ≤ ((n : ℝ) + 1) * (m : ℝ) ^ 2 := by
      rw [hDdef]
      have hmm : (0:ℝ) ≤ (m:ℝ)^2 - (m:ℝ) := by nlinarith [hmreal]
      have hprod : (0:ℝ) ≤ ((n:ℝ)-1) * ((m:ℝ)^2 - (m:ℝ)) := mul_nonneg (by linarith) hmm
      nlinarith [hprod, hmreal, hnreal]
    have hAKpos : 0 < ((n : ℝ) + 1) * (m : ℝ) ^ 2 * K := by
      have : (0:ℝ) < (m:ℝ)^2 := pow_pos (by linarith : (0:ℝ) < (m:ℝ)) 2
      positivity
    have hDKle : D * K ≤ ((n : ℝ) + 1) * (m : ℝ) ^ 2 * K := by
      apply mul_le_mul_of_nonneg_right hDbound (le_of_lt hKpos)
    have hden : s / (((n : ℝ) + 1) * (m : ℝ) ^ 2 * K) ≤ s / (D * K) := by
      apply div_le_div_of_nonneg_left (le_of_lt hs) (mul_pos hDpos' hKpos) hDKle
    have hmpow : (m : ℝ) ^ 2 * (m : ℝ) ^ (n - 2) = (m : ℝ) ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have hzpow : (m : ℝ) ^ (-(n : ℤ)) = 1 / (m : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_eq_one_div]
    have hfinal : s / (((n : ℝ) - 1) ^ (n - 2) * ((n : ℝ) + 1)) * (m : ℝ) ^ (-(n : ℤ))
        = s / (((n : ℝ) + 1) * (m : ℝ) ^ 2 * K) := by
      rw [hzpow, hKdef]
      have hden : ((n : ℝ) + 1) * (m : ℝ) ^ 2 * (((n : ℝ) - 1) ^ (n - 2) * (m : ℝ) ^ (n - 2))
          = (((n : ℝ) - 1) ^ (n - 2) * ((n : ℝ) + 1)) * (m : ℝ) ^ n := by
        calc ((n : ℝ) + 1) * (m : ℝ) ^ 2 * (((n : ℝ) - 1) ^ (n - 2) * (m : ℝ) ^ (n - 2))
            = (((n : ℝ) - 1) ^ (n - 2) * ((n : ℝ) + 1)) * ((m : ℝ) ^ 2 * (m : ℝ) ^ (n - 2)) := by ring
          _ = (((n : ℝ) - 1) ^ (n - 2) * ((n : ℝ) + 1)) * (m : ℝ) ^ n := by rw [hmpow]
      rw [hden]
      field_simp
    rw [hfinal]
    exact le_trans hden hmain

end Commons.Algebra.MvPolynomial
