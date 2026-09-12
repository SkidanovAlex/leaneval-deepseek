import Mathlib
import Submission.E0Complex

/-!
# E2c (algebra): geometric moment bounds force the Hankel determinants to zero

The Pólya/Hankel shell concludes `hankelDet a k = 0` for all large `k` from:
(i) `Submission.E0Complex.cHankelDet_eq_det_cMomentMatrix` — for any monic
polynomials `pᵢ ∈ ℂ[X]` of degree `i`, the complex Hankel determinant equals
the determinant of the moment matrix `M_{ij} := B(pᵢ,pⱼ)` (the moment
pairings of the Laurent coefficients of `g`);
(ii) a *geometric* bound on the moment pairings coming from polynomial
control on the fattened hedgehog and the contour estimate
`‖B(pᵢ,pⱼ)‖ ≤ K · θ^(i+j)` with `θ < 1`;
(iii) the elementary determinant estimate `‖det M‖ ≤ k! · ∏ᵢ ‖rowᵢ‖₂`
(from `Matrix.det_apply`, triangle inequality and `‖Mᵢⱼ‖ ≤ ‖rowᵢ‖₂`);
(iv) integrality: an integer with complex norm `< 1` is zero.

Row-norm computation: with `‖M_ij‖ ≤ K θ^(i+j)`,
`‖row_i‖₂² = Σ_j ‖M_ij‖² ≤ K² θ^{2i} · Σ_{j<k} θ^{2j} ≤ K²θ^{2i}/(1−θ²)`, so
`‖det M‖ ≤ k! · K^k · (1−θ²)^(−k/2) · θ^{k(k−1)/2}`, which tends to `0`
geometrically since `θ < 1`; hence `< 1` for all large `k`.

The file develops this elementary algebra (no contour geometry here).  All
helper lemmas below need proofs; no sorries may remain.
-/

noncomputable section

open scoped Polynomial BigOperators Topology

namespace Submission.HankelDecay

open Polynomial
open Submission.E0Complex
open Submission.Kronecker

/-- Determinant bound from row norms (`|det| ≤ k! · ∏ row-2-norms`), by the
Leibniz formula + triangle inequality + `|M_ij| ≤ ‖row i‖₂`. -/
lemma det_norm_le_factorial_prod_row (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    ‖M.det‖ ≤ (k.factorial : ℝ) *
      ∏ i : Fin k, Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2) := by
  classical
  rw [Matrix.det_apply]
  let r : Fin k → ℝ := fun i => Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2)
  have hleM : ∀ i j : Fin k, ‖M i j‖ ≤ r i := by
    intro i j
    dsimp [r]
    have hsq : ‖M i j‖ ^ 2 ≤ ∑ j : Fin k, ‖M i j‖ ^ 2 := by
      exact Finset.single_le_sum (fun x hx => sq_nonneg ‖M i x‖) (Finset.mem_univ j)
    exact Real.le_sqrt_of_sq_le hsq
  have hnorm_prod : ∀ σ : Equiv.Perm (Fin k),
      ‖(Equiv.Perm.sign σ) • ∏ i : Fin k, M (σ i) i‖ = ∏ i : Fin k, ‖M (σ i) i‖ := by
    intro σ
    have hsgn : ‖(Equiv.Perm.sign σ) • (∏ i : Fin k, M (σ i) i)‖ =
        ‖∏ i : Fin k, M (σ i) i‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    rw [hsgn]
    exact norm_prod Finset.univ (fun i : Fin k => M (σ i) i)
  calc
    ‖∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ) • ∏ i : Fin k, M (σ i) i‖
        ≤ ∑ σ : Equiv.Perm (Fin k), ‖(Equiv.Perm.sign σ) • ∏ i : Fin k, M (σ i) i‖ :=
          norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, ‖M (σ i) i‖) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hnorm_prod σ
    _ ≤ ∑ σ : Equiv.Perm (Fin k), (∏ i : Fin k, r (σ i)) := by
          apply Finset.sum_le_sum
          intro σ hσ
          apply Finset.prod_le_prod
          · intro i hi
            exact norm_nonneg (M (σ i) i)
          · intro i hi
            exact hleM (σ i) i
    _ = ∑ σ : Equiv.Perm (Fin k), (∏ j : Fin k, r j) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact Equiv.prod_comp σ (fun j : Fin k => r j)
    _ = (Fintype.card (Equiv.Perm (Fin k)) : ℝ) * (∏ j : Fin k, r j) := by
          simp
    _ = (k.factorial : ℝ) * (∏ j : Fin k, r j) := by
          rw [Fintype.card_perm]
          simp
/-- Geometric series bound: `Σ_{j<k} θ^{2j} ≤ 1/(1−θ²)` for `0 ≤ θ < 1`
(use the closed form `Finset.geom_sum` / `geom_sum_eq` and `0 ≤ θ^{2k}`). -/
lemma geom_sum_even_le (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, θ ^ (2 * j)) ≤ 1 / (1 - θ ^ 2) := by
  have hx1 : θ ^ 2 ≠ 1 := by
    have hsq : θ ^ 2 < 1 := by
      calc
        θ ^ 2 = θ * θ := by ring
        _ ≤ θ * 1 := by gcongr
        _ = θ := by ring
        _ < 1 := hθ1
    exact ne_of_lt hsq
  have hden : 0 < 1 - θ ^ 2 := by nlinarith [sq_nonneg θ, hθ1]
  have hsum0 : (∑ j ∈ Finset.range k, (θ ^ 2) ^ j) = ((θ ^ 2) ^ k - 1) / (θ ^ 2 - 1) :=
    geom_sum_eq hx1 k
  have hsum : (∑ j ∈ Finset.range k, θ ^ (2 * j)) = ((θ ^ 2) ^ k - 1) / (θ ^ 2 - 1) := by
    calc
      (∑ j ∈ Finset.range k, θ ^ (2 * j))
          = (∑ j ∈ Finset.range k, (θ ^ 2) ^ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← pow_mul θ 2 j]
      _ = ((θ ^ 2) ^ k - 1) / (θ ^ 2 - 1) := hsum0
  rw [hsum]
  have hsplit : ((θ ^ 2) ^ k - 1) / (θ ^ 2 - 1) = (1 - (θ ^ 2) ^ k) / (1 - θ ^ 2) := by
    field_simp [sub_ne_zero.mpr hx1]
    ring
  rw [hsplit]
  have hnum : 1 - (θ ^ 2) ^ k ≤ 1 := by
    have hpk : 0 ≤ (θ ^ 2) ^ k := pow_nonneg (sq_nonneg θ) k
    linarith
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
/-- Complex norm of `θ^(i+j)`: `‖(θ : ℂ)^(i+j)‖ = θ^(i+j)` for `0 ≤ θ`. -/
lemma norm_rpow_nat_cast_complex (θ : ℝ) (hθ0 : 0 ≤ θ) (n : ℕ) :
    ‖((θ : ℂ) ^ n)‖ = θ ^ n := by
  calc
    ‖((θ : ℂ) ^ n)‖ = ‖(θ : ℂ)‖ ^ n := norm_pow (θ : ℂ) n
    _ = (|θ| : ℝ) ^ n := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = θ ^ n := by rw [abs_of_nonneg hθ0]

/-! ## Row-norm and eventual-smallness infrastructure -/

/-- `(θ^n)^2 = θ^(2n)`. -/
lemma pow_sq_two_mul (θ : ℝ) (n : ℕ) : (θ ^ n) ^ 2 = θ ^ (2 * n) := by
  rw [show 2 * n = n * 2 by omega]
  exact (pow_mul θ n 2).symm

/-- Squared row-sum bound from geometric moment bounds. -/
lemma rowSq_le (θ K : ℝ) (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (k : ℕ) (i : Fin k) (M : Matrix (Fin k) (Fin k) ℂ)
    (hM : ∀ j : Fin k, ‖M i j‖ ≤ K * θ ^ (i.val + j.val)) :
    (∑ j : Fin k, ‖M i j‖ ^ 2) ≤ (K * θ ^ i.val) ^ 2 / (1 - θ ^ 2) := by
  have hS : 0 < 1 - θ ^ 2 := by nlinarith [sq_nonneg θ, hθ1]
  have hnonneg : ∀ j : Fin k, 0 ≤ K * θ ^ (i.val + j.val) := by
    intro j
    exact mul_nonneg hK (pow_nonneg hθ0 _)
  have hsq_entries : ∀ j : Fin k, ‖M i j‖ ^ 2 ≤ (K * θ ^ (i.val + j.val)) ^ 2 := by
    intro j
    exact (sq_le_sq₀ (norm_nonneg (M i j)) (hnonneg j)).2 (hM j)
  have hgeom : (∑ j ∈ Finset.range k, θ ^ (2 * j)) ≤ 1 / (1 - θ ^ 2) :=
    geom_sum_even_le θ hθ0 hθ1 k
  have hreindex : (∑ j : Fin k, θ ^ (2 * j.val)) = ∑ j ∈ Finset.range k, θ ^ (2 * j) := by
    exact Fin.sum_univ_eq_sum_range (fun t : ℕ => θ ^ (2 * t)) k
  have hsumj : (∑ j : Fin k, (θ ^ j.val) ^ 2) ≤ 1 / (1 - θ ^ 2) := by
    calc
      (∑ j : Fin k, (θ ^ j.val) ^ 2) = ∑ j : Fin k, θ ^ (2 * j.val) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact pow_sq_two_mul θ j.val
      _ = ∑ j ∈ Finset.range k, θ ^ (2 * j) := hreindex
      _ ≤ 1 / (1 - θ ^ 2) := hgeom
  calc
    (∑ j : Fin k, ‖M i j‖ ^ 2)
        ≤ ∑ j : Fin k, (K * θ ^ (i.val + j.val)) ^ 2 := by
          exact Finset.sum_le_sum (by intro j hj; exact hsq_entries j)
    _ = K^2 * (θ ^ i.val) ^ 2 * (∑ j : Fin k, (θ ^ j.val) ^ 2) := by
          calc
            (∑ j : Fin k, (K * θ ^ (i.val + j.val)) ^ 2)
                = ∑ j : Fin k, (K^2 * (θ ^ i.val) ^ 2 * (θ ^ j.val) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [pow_add]
                  ring
            _ = K^2 * (θ ^ i.val) ^ 2 * (∑ j : Fin k, (θ ^ j.val) ^ 2) := by
                  rw [Finset.mul_sum]
    _ ≤ K^2 * (θ ^ i.val) ^ 2 * (1 / (1 - θ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hsumj
            (mul_nonneg (sq_nonneg K) (sq_nonneg (θ ^ i.val)))
    _ = (K * θ ^ i.val) ^ 2 / (1 - θ ^ 2) := by
          rw [show K ^ 2 * (θ ^ i.val) ^ 2 = (K * θ ^ i.val) ^ 2 by ring]
          field_simp [hS.ne']

/-- Row-norm bound from geometric moment bounds. -/
lemma rowNorm_le (θ K : ℝ) (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (k : ℕ) (i : Fin k) (M : Matrix (Fin k) (Fin k) ℂ)
    (hM : ∀ j : Fin k, ‖M i j‖ ≤ K * θ ^ (i.val + j.val)) :
    Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2) ≤ (K / Real.sqrt (1 - θ ^ 2)) * θ ^ i.val := by
  have hsq := rowSq_le θ K hK hθ0 hθ1 k i M hM
  calc
    Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2) ≤ Real.sqrt ((K * θ ^ i.val) ^ 2 / (1 - θ ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = (K / Real.sqrt (1 - θ ^ 2)) * θ ^ i.val := by
      have hnum : 0 ≤ (K * θ ^ i.val) ^ 2 := sq_nonneg _
      rw [Real.sqrt_div hnum (1 - θ ^ 2)]
      rw [Real.sqrt_sq_eq_abs]
      have h2 : |K * θ ^ i.val| = K * θ ^ i.val := abs_of_nonneg (mul_nonneg hK (pow_nonneg hθ0 _))
      rw [h2]
      rw [div_eq_mul_inv]
      ring

/-- Product of row norms is bounded by the geometric factors. -/
lemma prod_rowNorm_le (θ K : ℝ) (hK : 0 ≤ K) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ)
    (hM : ∀ i j : Fin k, ‖M i j‖ ≤ K * θ ^ (i.val + j.val)) :
    (∏ i : Fin k, Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2)) ≤
      (K / Real.sqrt (1 - θ ^ 2)) ^ k * θ ^ (∑ t ∈ Finset.range k, t) := by
  let C : ℝ := K / Real.sqrt (1 - θ ^ 2)
  have hrow : ∀ i : Fin k,
      Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2) ≤ C * θ ^ i.val := by
    intro i
    rw [show C = K / Real.sqrt (1 - θ ^ 2) by rfl]
    exact rowNorm_le θ K hK hθ0 hθ1 k i M (by intro j; exact hM i j)
  have hsumid : (∑ i : Fin k, i.val) = ∑ t ∈ Finset.range k, t := by
    simpa using Fin.sum_univ_eq_sum_range (fun t : ℕ => t) k
  calc
    (∏ i : Fin k, Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2))
        ≤ ∏ i : Fin k, (C * θ ^ i.val) := by
          apply Finset.prod_le_prod
          · intro i hi
            exact Real.sqrt_nonneg _
          · intro i hi
            exact hrow i
    _ = C ^ k * θ ^ (∑ i : Fin k, i.val) := by
          rw [Finset.prod_mul_distrib]
          rw [Finset.prod_const]
          rw [Finset.prod_pow_eq_pow_sum]
          simp
    _ = C ^ k * θ ^ (∑ t ∈ Finset.range k, t) := by
          rw [hsumid]

/-- An integer with complex norm `< 1` is zero. -/
lemma int_norm_lt_one_eq_zero (z : ℤ) (h : ‖(z : ℂ)‖ < 1) : z = 0 := by
  by_contra hz
  have hzabs : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have hn : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
    have hn' : ‖(z : ℂ)‖ = |(z : ℝ)| := by simp
    rw [hn']
    have hcast : |(z : ℝ)| = ((|z| : ℤ) : ℝ) := by simp [Int.cast_abs]
    rw [hcast]
    exact_mod_cast hzabs
  linarith

/-- `u_k := k! · C^k · θ^(∑_{t<k} t)` is eventually `< 1` for `0 ≤ C` and `0 ≤ θ < 1`. -/
lemma eventually_small (C θ : ℝ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (k.factorial : ℝ) * C ^ k * θ ^ (∑ t ∈ Finset.range k, t) < 1 := by
  classical
  let Ssum : ℕ → ℕ := fun k => ∑ t ∈ Finset.range k, t
  let u : ℕ → ℝ := fun k => (k.factorial : ℝ) * C ^ k * θ ^ Ssum k
  let q : ℕ → ℝ := fun k => (k + 1 : ℝ) * C * θ ^ k
  have hu0 : ∀ k : ℕ, 0 ≤ u k := by
    intro k
    dsimp [u]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hC k)) (pow_nonneg hθ0 (Ssum k))
  have hSucc : ∀ k : ℕ, Ssum (k + 1) = Ssum k + k := by
    intro k
    dsimp [Ssum]
    simpa using (Finset.sum_range_succ (fun t : ℕ => t) k)
  have hrec : ∀ k : ℕ, u (k + 1) = u k * q k := by
    intro k
    dsimp [u, q]
    rw [Nat.factorial_succ]
    rw [pow_succ]
    rw [hSucc k]
    rw [pow_add]
    simp [Nat.cast_mul, Nat.cast_add]
    ring
  have ht1 : Filter.Tendsto (fun k : ℕ => (k : ℝ) * θ ^ k) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 1 hθ0 hθ1)
  have ht2 : Filter.Tendsto (fun k : ℕ => θ ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
  have htsum : Filter.Tendsto (fun k : ℕ => (k : ℝ) * θ ^ k + θ ^ k) Filter.atTop (𝓝 0) := by
    simpa using ht1.add ht2
  have hq0 : ∀ k : ℕ, 0 ≤ q k := by
    intro k
    dsimp [q]
    exact mul_nonneg (mul_nonneg (by positivity) hC) (pow_nonneg hθ0 k)
  have hq : Filter.Tendsto q Filter.atTop (𝓝 0) := by
    apply Filter.Tendsto.congr' ?_ (by simpa using htsum.const_mul C)
    filter_upwards with k
    dsimp [q]
    ring
  have hqev : ∀ᶠ k : ℕ in Filter.atTop, q k < (1 / 2 : ℝ) := by
    exact hq.eventually (IsOpen.mem_nhds isOpen_Iio (by norm_num))
  rcases Filter.mem_atTop_sets.mp hqev with ⟨K0, hK0⟩
  have hqhalf : ∀ k : ℕ, K0 ≤ k → q k ≤ 1 / 2 := by
    intro k hk
    exact le_of_lt (hK0 k hk)
  have hind : ∀ m : ℕ, u (K0 + m) ≤ u K0 * (1 / 2) ^ m := by
    intro m
    induction m with
    | zero =>
        dsimp [u]
        simp
    | succ m ih =>
        calc
          u (K0 + (m + 1)) = u ((K0 + m) + 1) := by
                rw [show K0 + (m + 1) = (K0 + m) + 1 by omega]
          _ = u (K0 + m) * q (K0 + m) := hrec (K0 + m)
          _ ≤ (u K0 * (1 / 2) ^ m) * (1 / 2) := by
                exact mul_le_mul ih (hqhalf (K0 + m) (by omega))
                  (hq0 (K0 + m))
                  (mul_nonneg (hu0 K0) (pow_nonneg (by norm_num) m))
          _ = u K0 * (1 / 2) ^ (m + 1) := by
                rw [pow_succ]
                ring
  have hgeom : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgeomC : Filter.Tendsto (fun m : ℕ => u K0 * (1 / 2 : ℝ) ^ m) Filter.atTop (𝓝 0) := by
    simpa using hgeom.const_mul (u K0)
  have hlt : ∀ᶠ m : ℕ in Filter.atTop, u K0 * (1 / 2 : ℝ) ^ m < (1 : ℝ) := by
    exact hgeomC.eventually (IsOpen.mem_nhds isOpen_Iio (by norm_num))
  rcases Filter.mem_atTop_sets.mp hlt with ⟨n0, hn0⟩
  refine ⟨K0 + n0, ?_⟩
  intro k hk
  let m : ℕ := k - K0
  have hk' : k = K0 + m := by
    dsimp [m]
    omega
  have hm : n0 ≤ m := by
    dsimp [m]
    omega
  rw [hk']
  exact lt_of_le_of_lt (hind m) (hn0 m hm)

/-- Complex Hankel determinant of `(a n)` is bounded by the geometric expression. -/
lemma hankelDet_norm_le (a : ℕ → ℤ) (p : ℕ → ℂ[X])
    (hpmonic : ∀ j : ℕ, (p j).Monic) (hpdeg : ∀ j : ℕ, (p j).natDegree = j)
    {K : ℝ} (hK : 0 ≤ K) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hmom : ∀ k : ℕ, 1 ≤ k → ∀ i j : Fin k,
      ‖(cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j)‖ ≤
        K * θ ^ (i.val + j.val)) :
    ∀ k : ℕ, 1 ≤ k →
      ‖(hankelDet a k : ℂ)‖ ≤
        (k.factorial : ℝ) * (K / Real.sqrt (1 - θ ^ 2)) ^ k *
          θ ^ (∑ t ∈ Finset.range k, t) := by
  intro k hk
  let Seq : ℕ → ℂ := fun n : ℕ => (a n : ℂ)
  let pf : Fin k → ℂ[X] := fun t : Fin k => p t.val
  let M : Matrix (Fin k) (Fin k) ℂ := cMomentMatrix k Seq pf
  have hseq : (hankelDet a k : ℂ) = cHankelDet Seq k := by
    dsimp [Seq]
    exact hankelDet_cast_complex a k
  have hmdet : cHankelDet Seq k = M.det := by
    dsimp [M, pf, Seq]
    exact cHankelDet_eq_det_cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val)
      (by intro i; exact hpmonic i.val) (by intro i; exact hpdeg i.val)
  have hM : ∀ i j : Fin k, ‖M i j‖ ≤ K * θ ^ (i.val + j.val) := by
    intro i j
    dsimp [M, Seq, pf]
    exact hmom k hk i j
  calc
    ‖(hankelDet a k : ℂ)‖ = ‖M.det‖ := by
          rw [hseq, hmdet]
    _ ≤ (k.factorial : ℝ) * (∏ i : Fin k, Real.sqrt (∑ j : Fin k, ‖M i j‖ ^ 2)) := by
          exact det_norm_le_factorial_prod_row k M
    _ ≤ (k.factorial : ℝ) * ((K / Real.sqrt (1 - θ ^ 2)) ^ k *
          θ ^ (∑ t ∈ Finset.range k, t)) := by
          exact mul_le_mul_of_nonneg_left (prod_rowNorm_le θ K hK hθ0 hθ1 k M hM) (by positivity)
    _ = (k.factorial : ℝ) * (K / Real.sqrt (1 - θ ^ 2)) ^ k *
          θ ^ (∑ t ∈ Finset.range k, t) := by
          ring

theorem hankelDet_eventually_zero_of_moment_bound (a : ℕ → ℤ) (p : ℕ → ℂ[X])
    (hpmonic : ∀ j : ℕ, (p j).Monic) (hpdeg : ∀ j : ℕ, (p j).natDegree = j)
    {K : ℝ} (hK : 0 ≤ K) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hmom : ∀ k : ℕ, 1 ≤ k → ∀ i j : Fin k,
      ‖(cMomentMatrix k (fun n : ℕ => (a n : ℂ)) (fun t : Fin k => p t.val) i j)‖ ≤
        K * θ ^ (i.val + j.val)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → hankelDet a k = 0 := by
  classical
  rcases eventually_small (K / Real.sqrt (1 - θ ^ 2)) θ
      (div_nonneg hK (Real.sqrt_nonneg _)) hθ0 hθ1 with ⟨N, hN⟩
  refine ⟨max N 1, ?_⟩
  intro k hk
  have hkN : N ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hb := hankelDet_norm_le a p hpmonic hpdeg hK hθ0 hθ1 hmom k hk1
  have hlt : ‖(hankelDet a k : ℂ)‖ < 1 := by
    exact lt_of_le_of_lt hb (hN k hkN)
  exact int_norm_lt_one_eq_zero (hankelDet a k) hlt

end Submission.HankelDecay
