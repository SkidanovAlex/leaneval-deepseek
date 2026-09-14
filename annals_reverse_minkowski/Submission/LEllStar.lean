import Mathlib
import Submission.KConvexGauge

/-!
# The `ℓ`-norm on matrices and the `ℓℓ*` theorem

This file develops the `ℓ`-norm of a matrix with respect to a symmetric convex body `K`,

`ℓ_K(B) = (∫ ‖B x‖_K²  dμ_m(x))^{1/2}`  (`dμ_m = e^{-‖x‖²/2} dx`),

proves that its unit ball is a convex compact body containing `0` in its interior (so Lewis' theorem
`Commons.LinearAlgebra.Matrix.lewis_det_max_normal` applies), establishes the `ℓℓ*` comparison
(Pisier's Lemma 3.10) from the K-convexity bound `Submission.KConvexGauge.kconvex_gauge`, and finally
derives `Submission.IsotropicMass.EllEllStarHyp`.

The K-convexity constant of `X = (ℝᵐ, ‖·‖_K)` is bounded by `4 (1 + log₂ d(X, ℓ₂ᵐ))`, and
`d ≤ √m` by John's theorem, giving `ℓ_K(A) ℓ_{K°}((Aᵀ)⁻¹) ≤ 2 m (log₂ m + 2)` in the `μ_m`
normalization; the conversion to the `e^{-π‖x‖²}` normalization divides by `2π` (each of the two
factors contributes `(2π)^{-1/2}` up to the total mass `(2π)^{m/2}` of `μ_m`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal Topology Real Pointwise

namespace Submission.LEllStar

variable {m : ℕ}

noncomputable section

/-- The total mass of the Gaussian weight measure `μ_m` on `ℝᵐ`, i.e. `(2π)^{m/2}`. -/
noncomputable def gaussZ (m : ℕ) : ℝ := (Real.sqrt (2 * Real.pi)) ^ m

@[simp] theorem gaussZ_zero : gaussZ 0 = 1 := by simp [gaussZ]

theorem gaussZ_pos (m : ℕ) : 0 < gaussZ m := by
  rw [gaussZ]; positivity

theorem gaussZ_ne_zero (m : ℕ) : gaussZ m ≠ 0 := (gaussZ_pos m).ne'

/-- `xᵢ` is the degree-one Hermite polynomial attached to the multi-index `eᵢ`. -/
theorem herm_single_one {m : ℕ} (i : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    Submission.GaussianChaos.herm (Pi.single i 1) x = x.ofLp i := by
  simp only [Submission.GaussianChaos.herm]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, Polynomial.hermite_one, Polynomial.aeval_X]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, Polynomial.hermite_zero]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The second moments of the coordinate functions for `μ_m`. -/
theorem integral_coord_mul_coord {m : ℕ} (i j : Fin m) :
    ∫ x : EuclideanSpace ℝ (Fin m), (x.ofLp i * x.ofLp j) ∂Submission.GaussianChaos.μ m
      = gaussZ m * (if i = j then 1 else 0) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, mul_one]
    rw [show (fun x : EuclideanSpace ℝ (Fin m) => x.ofLp i * x.ofLp i)
        = (fun x => (Submission.GaussianChaos.herm (Pi.single i 1) x) ^ 2) from by
      funext x; rw [herm_single_one]; ring]
    rw [Submission.GaussianChaos.integral_herm_sq]
    simp only [Submission.GaussianChaos.energy]
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same, Nat.factorial_one, Nat.cast_one, one_mul]
      rw [gaussZ, Real.sqrt_eq_rpow, ← Real.rpow_natCast]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, Nat.factorial_zero, Nat.cast_one]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hij, mul_zero]
    rw [show (fun x : EuclideanSpace ℝ (Fin m) => x.ofLp i * x.ofLp j)
        = (fun x => Submission.GaussianChaos.herm (Pi.single i 1) x
            * Submission.GaussianChaos.herm (Pi.single j 1) x) from by
      funext x; rw [herm_single_one, herm_single_one]]
    refine Submission.GaussianChaos.integral_herm_mul_herm (fun h => hij ?_)
    have h3 := congrFun h i
    simp only [Pi.single_eq_same] at h3
    rw [Pi.single_eq_of_ne hij] at h3
    exact (one_ne_zero h3).elim

/-! ### The matrix action -/

theorem toLpLin_add_apply (A B : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    Matrix.toLpLin 2 2 (A + B) x = Matrix.toLpLin 2 2 A x + Matrix.toLpLin 2 2 B x := by
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, Matrix.toLpLin_apply, Matrix.add_mulVec,
    WithLp.toLp_add]

theorem toLpLin_smul_apply (c : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    Matrix.toLpLin 2 2 (c • A) x = c • Matrix.toLpLin 2 2 A x := by
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, smul_mulVec, WithLp.toLp_smul]

theorem toLpLin_zero_apply (x : EuclideanSpace ℝ (Fin m)) :
    Matrix.toLpLin 2 2 (0 : Matrix (Fin m) (Fin m) ℝ) x = 0 := by
  rw [Matrix.toLpLin_apply, Matrix.zero_mulVec, WithLp.toLp_zero]

local notation "act" B => (Matrix.toLpLin 2 2 B)

/-- The Frobenius square of a matrix, `∑ᵢⱼ Bᵢⱼ²`. -/
noncomputable def frobSq (B : Matrix (Fin m) (Fin m) ℝ) : ℝ := ∑ i, ∑ j, (B i j) ^ 2

theorem frobSq_nonneg (B : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ frobSq B :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `‖(act B) x‖²` expands into the Frobenius data. -/
theorem norm_sq_act (B : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    ‖(act B) x‖ ^ 2 = ∑ i, ∑ j, ∑ k, (B i j * B i k) * (x.ofLp j * x.ofLp k) := by
  rw [Matrix.toLpLin_apply, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WithLp.ofLp_toLp]
  simp only [Matrix.mulVec, dotProduct, Real.norm_eq_abs, sq_abs]
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Integrability of the summands in `norm_sq_act`. -/
theorem integrable_summand (B : Matrix (Fin m) (Fin m) ℝ) (i j k : Fin m) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) =>
      (B i j * B i k) * (x.ofLp j * x.ofLp k)) (Submission.GaussianChaos.μ m) := by
  have h := (Submission.GaussianChaos.integrable_herm_mul_herm
    (Pi.single j 1) (Pi.single k 1)).const_mul (B i j * B i k)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [herm_single_one, herm_single_one]

/-- The second moment of a matrix image: `∫ ‖B x‖² dμ = gaussZ m · frobSq B`. -/
theorem integral_norm_sq_act (B : Matrix (Fin m) (Fin m) ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin m), ‖(act B) x‖ ^ 2 ∂Submission.GaussianChaos.μ m
      = gaussZ m * frobSq B := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m), ‖(act B) x‖ ^ 2
      = ∑ i, ∑ j, ∑ k, (B i j * B i k) * (x.ofLp j * x.ofLp k) := norm_sq_act B
  rw [funext hpt]
  rw [integral_finsetSum]
  swap
  · intro i _
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => integrable_summand B i j k
  rw [frobSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum]
  swap
  · intro j _
    exact integrable_finsetSum _ fun k _ => integrable_summand B i j k
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum]
  swap
  · intro k _; exact integrable_summand B i j k
  rw [Finset.sum_eq_single j]
  · rw [integral_const_mul, integral_coord_mul_coord, if_pos rfl]
    ring
  · intro k _ hk
    rw [integral_const_mul, integral_coord_mul_coord, if_neg (Ne.symm hk)]
    ring
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Integrability of `‖(act B) x‖²` with respect to the Gaussian weight measure. -/
theorem integrable_norm_sq_act (B : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => ‖(act B) x‖ ^ 2)
      (Submission.GaussianChaos.μ m) := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m), ‖(act B) x‖ ^ 2
      = ∑ i, ∑ j, ∑ k, (B i j * B i k) * (x.ofLp j * x.ofLp k) := norm_sq_act B
  rw [funext hpt]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_summand B i j k

end

/-! ### Combinatorics of the degree-one multi-indices -/

/-- A multi-index of degree one is a standard basis vector. -/
theorem deg_one_eq_single {N : ℕ} {α : Fin N → ℕ} (h : ∑ i, α i = 1) :
    ∃ i, α = Pi.single i (1:ℕ) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [h]; exact one_ne_zero)
  have hsplit : ∑ k, α k = (∑ k ∈ Finset.univ.erase i, α k) + α i :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  refine ⟨i, funext fun j => ?_⟩
  rcases eq_or_ne j i with hji | hj
  · rw [hji, Pi.single_eq_same]
    have h1 : 1 ≤ α i := Nat.one_le_iff_ne_zero.mpr hi
    have h2 : ∑ k ∈ Finset.univ.erase i, α k = 0 := by omega
    omega
  · rw [Pi.single_eq_of_ne hj]
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hle : α j ≤ ∑ k ∈ Finset.univ.erase i, α k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) hmem
    have h2 : ∑ k ∈ Finset.univ.erase i, α k = 0 := by omega
    omega

theorem deg_single_one {N : ℕ} (i : Fin N) :
    Submission.KConvex.deg (Pi.single i (1:ℕ)) = 1 := by
  classical
  simp [Submission.KConvex.deg, Pi.single_apply]

theorem filter_deg_one_eq {N : ℕ} (s : Finset (Fin N → ℕ)) :
    s.filter (fun α => Submission.KConvex.deg α = 1)
      = (Finset.univ.filter (fun i : Fin N => Pi.single i (1:ℕ) ∈ s)).image
          (fun i => Pi.single i (1:ℕ)) := by
  classical
  ext α
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hs, hdeg⟩
    obtain ⟨i, rfl⟩ := deg_one_eq_single hdeg
    exact ⟨i, hs, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, deg_single_one i⟩

/-- The first-chaos component as an explicit sum over the coordinate directions. -/
theorem comp_one_eq {N n : ℕ} (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin N)) :
    Submission.KConvex.comp 1 s C x
      = ∑ i : Fin N,
          (if Pi.single i (1:ℕ) ∈ s then (x.ofLp i) • C (Pi.single i (1:ℕ)) else 0) := by
  classical
  rw [Submission.KConvex.comp, filter_deg_one_eq, Finset.sum_image, Finset.sum_filter]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [herm_single_one]
  · intro i _ j _ hij
    by_contra hne
    have h3 := congrFun hij i
    simp only [Pi.single_eq_same] at h3
    rw [Pi.single_eq_of_ne hne] at h3
    exact one_ne_zero h3



/-- The squared `ℓ`-norm of a matrix w.r.t. `K` (in the `μ_m` normalization). -/
noncomputable def ellSq (K : Set (EuclideanSpace ℝ (Fin m))) (X : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ x, (gauge K (Matrix.toLpLin 2 2 X x)) ^ 2 ∂Submission.GaussianChaos.μ m

theorem ellSq_nonneg (K : Set (EuclideanSpace ℝ (Fin m))) (X : Matrix (Fin m) (Fin m) ℝ) :
    0 ≤ ellSq K X := integral_nonneg fun x => sq_nonneg _

/-- Homogeneity of `ellSq`. -/
theorem ellSq_smul (K : Set (EuclideanSpace ℝ (Fin m))) (hbal : Balanced ℝ K) (t : ℝ)
    (X : Matrix (Fin m) (Fin m) ℝ) : ellSq K (t • X) = t ^ 2 * ellSq K X := by
  rw [ellSq, ellSq]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      (gauge K (Matrix.toLpLin 2 2 (t • X) x)) ^ 2
        = t ^ 2 * (gauge K (Matrix.toLpLin 2 2 X x)) ^ 2 := by
    intro x
    rw [toLpLin_smul_apply, gauge_smul hbal, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [show (fun x : EuclideanSpace ℝ (Fin m) =>
        (gauge K (Matrix.toLpLin 2 2 (t • X) x)) ^ 2)
      = fun x => t ^ 2 * (gauge K (Matrix.toLpLin 2 2 X x)) ^ 2 from funext hpt]
  rw [integral_const_mul]

/-- Homogenized form of a bound on `tr (v X)`: `tr (v X) ≤ L √(ellSq K X)`. -/
theorem trace_le_mul_sqrt_ellSq (K : Set (EuclideanSpace ℝ (Fin m))) (hbal : Balanced ℝ K)
    {v : Matrix (Fin m) (Fin m) ℝ} {L : ℝ} (hLnn : 0 ≤ L)
    (hL : ∀ X : Matrix (Fin m) (Fin m) ℝ, ellSq K X ≤ 1 → Matrix.trace (v * X) ≤ L)
    (X : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.trace (v * X) ≤ L * Real.sqrt (ellSq K X) := by
  rcases eq_or_lt_of_le (ellSq_nonneg K X) with h0 | hpos
  · rw [← h0, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set t : ℝ := ε / (L + 1) with ht
    have htpos : 0 < t := by rw [ht]; positivity
    have hs : ellSq K (t⁻¹ • X) ≤ 1 := by
      rw [ellSq_smul K hbal, inv_pow, ← h0]; simp
    have h1 := hL _ hs
    have htr : Matrix.trace (v * (t⁻¹ • X)) = t⁻¹ * Matrix.trace (v * X) := by
      rw [Matrix.mul_smul, Matrix.trace_smul]; rfl
    rw [htr, inv_mul_le_iff₀ htpos] at h1
    calc Matrix.trace (v * X) ≤ t * L := h1
      _ ≤ 0 + ε := by
          rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < L + 1)]
          nlinarith [hLnn, hε]
  · have hs : ellSq K ((Real.sqrt (ellSq K X))⁻¹ • X) ≤ 1 := by
      rw [ellSq_smul K hbal, inv_pow, ← div_eq_inv_mul, Real.sq_sqrt hpos.le,
        div_self (ne_of_gt hpos)]
    have h1 := hL _ hs
    have htr : Matrix.trace (v * ((Real.sqrt (ellSq K X))⁻¹ • X))
        = (Real.sqrt (ellSq K X))⁻¹ * Matrix.trace (v * X) := by
      rw [Matrix.mul_smul, Matrix.trace_smul]; rfl
    rw [htr, inv_mul_le_iff₀ (Real.sqrt_pos.mpr hpos)] at h1
    calc Matrix.trace (v * X) ≤ Real.sqrt (ellSq K X) * L := h1
      _ = L * Real.sqrt (ellSq K X) := mul_comm _ _


end Submission.LEllStar
