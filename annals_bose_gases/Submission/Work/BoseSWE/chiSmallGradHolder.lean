import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseB1Cube.chiSmallBase_fderiv_e3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pointwise Hölder gradient bound for the cosine cube bump `chiSmall M`

`Submission.BoseGases.chiSmall M z = (ζ(z₀)ζ(z₁)ζ(z₂))^M / √∫(ζζζ)^{2M}` with
`ζ = zeta1d` (`Submission.Work.ChiSmall`).  This file proves

    ‖fderiv ℝ (fun w => chiSmall M (s⁻¹ • w - v)) z‖
      ≤ C_M · s⁻¹ · (chiSmall M (s⁻¹ • z - v)) ^ ((M - 1)/M)      (`M ≥ 2`),

the pointwise Hölder-type bound on the gradient in terms of the function itself, with a constant
`C_M = 2·M·π·κ_M^{1/M}` depending only on `M` (`κ_M = chiSmallNormFactor M`).

## Strategy

* The one-dimensional profile `ζ^M` has derivative
  `deriv (ζ^M) y = M·cos(πy)^{M-1}·(−sin(πy)·π)` in `|y| < 1/2` and `0` elsewhere
  (`Submission.BoseGases.zeta1dDerivPiecewise_eq_deriv`), hence
  `|deriv (ζ^M) y| ≤ Mπ·ζ(y)^{M-1}` (`abs_deriv_zeta1dPow_le`): the derivative is bounded by the
  `(M-1)`-th power of the profile itself.
* `chiSmallBase M` is the product of the three one-coordinate factors `ζ(x_j)^M`, so its
  `k`-th coordinate derivative is `deriv (ζ^M) (z_k)` times the product of the *other* two factors
  (`chiSmallBase_fderiv_e3_two`, the `M ≥ 2` version of `Work.BoseB1Cube.chiSmallBase_fderiv_e3`).
  With `P = ∏_j ζ(z_j)` and `Q = ∏_{i ≠ k} ζ(z_i) ≤ 1` this gives
  `|∂_k chiSmallBase M z| ≤ Mπ·ζ(z_k)^{M-1}Q^M ≤ Mπ·(ζ(z_k)Q)^{M-1} = Mπ·P^{M-1}`.
* `‖∇chiSmallBase M z‖ ≤ 2·Mπ·P^{M-1}` from the basis expansion
  `‖L‖² = Σ_j (L (e3 j))²` (`Work.BoseB1Cube.norm_sq_eq_sum_e3`) and `√3 ≤ 2`.
* Multiplying by the normalisation `κ_M = chiSmallNormFactor M > 0` and using
  `κ_M^{1/M}·κ_M^{(M-1)/M} = κ_M` (rpow algebra at a positive base) converts
  `κ_M·Mπ·P^{M-1}` into `C_M·(κ_M P^M)^{(M-1)/M}`, i.e. into `C_M·(chiSmall M z)^{(M-1)/M}`.
* The scaling by `s⁻¹`: the chain rule gives
  `fderiv ℝ (fun w => chiSmall M (s⁻¹ • w - v)) z
     = (fderiv ℝ (chiSmall M) (s⁻¹ • z - v)) ∘SL (s⁻¹ • 1)`
  and `‖s⁻¹ • (1 : ℝ³ →L[ℝ] ℝ³)‖ = s⁻¹`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The one-dimensional derivative bound -/

/-- **The derivative of `ζ^M` is bounded by `Mπ` times the `(M-1)`-st power of `ζ`**:
`|deriv (ζ^M) y| ≤ Mπ·ζ(y)^{M-1}` for `M ≥ 2`.  This is the pointwise form of FS's
`∂_j(ζ^M) = Mπ sin(πy)ζ^{M-1}` (the remaining factors being `≤ 1`). -/
lemma abs_deriv_zeta1dPow_le {M : ℕ} (hM : 2 ≤ M) (y : ℝ) :
    |deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) y|
      ≤ (M : ℝ) * Real.pi * (Submission.BoseGases.zeta1d y) ^ (M - 1) := by
  rw [congr_fun (Submission.BoseGases.zeta1dDerivPiecewise_eq_deriv hM) y]
  dsimp only [Submission.BoseGases.zeta1dDerivPiecewise]
  split_ifs with hy
  · have hz : Submission.BoseGases.zeta1d y = Real.cos (Real.pi * y) :=
      Submission.BoseGases.zeta1d_of_abs_le (le_of_lt hy)
    have hc : 0 ≤ Real.cos (Real.pi * y) := by
      rw [← hz]; exact Submission.BoseGases.zeta1d_nonneg y
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hs : |Real.sin (Real.pi * y)| ≤ 1 := Real.abs_sin_le_one _
    rw [Submission.BoseGases.zeta1dDerivF, hz, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg M), abs_of_nonneg (pow_nonneg hc _), abs_neg,
      abs_of_nonneg hpi]
    have h1 : (0 : ℝ) ≤ (M : ℝ) * Real.cos (Real.pi * y) ^ (M - 1) :=
      mul_nonneg (Nat.cast_nonneg M) (pow_nonneg hc _)
    calc (M : ℝ) * Real.cos (Real.pi * y) ^ (M - 1) * (|Real.sin (Real.pi * y)| * Real.pi)
        ≤ (M : ℝ) * Real.cos (Real.pi * y) ^ (M - 1) * (1 * Real.pi) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs hpi) h1
      _ = (M : ℝ) * Real.pi * Real.cos (Real.pi * y) ^ (M - 1) := by ring
  · rw [abs_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg M) (le_of_lt Real.pi_pos))
      (pow_nonneg (Submission.BoseGases.zeta1d_nonneg y) _)

/-! ## 2. The coordinate derivative of `chiSmallBase M` for `M ≥ 2` -/

/-- **Coordinate derivative of the cosine-power bump** (`M ≥ 2`): the `k`-th partial derivative of
`chiSmallBase M = ∏_i ζ(x_i)^M` is the derivative of the one-dimensional profile in the `k`-th
coordinate times the product of the other two factors.

This is `Work.BoseB1Cube.chiSmallBase_fderiv_e3` with the hypothesis relaxed from `3 ≤ M` to
`2 ≤ M` (only the latter is used in the proof, and the Hölder bound below needs `M = 2`). -/
lemma chiSmallBase_fderiv_e3_two {M : ℕ} (hM : 2 ≤ M) (z : E3) (k : Fin 3) :
    fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)
      = deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp k)
        * ∏ i ∈ Finset.univ.erase k, Submission.BoseGases.zeta1d (z.ofLp i) ^ M := by
  rw [Work.BoseB1Cube.chiSmallBase_eq_prod_zeta1d]
  have hp : ∀ i : Fin 3, HasFDerivAt (fun x : E3 => x.ofLp i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) z :=
    fun i => by
      simpa using (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i) (x := z))
  have hd : ∀ i : Fin 3, HasFDerivAt (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M)
      (ContinuousLinearMap.toSpanSingleton ℝ
        (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))) (z.ofLp i) :=
    fun i => (Work.BoseB1Cube.zeta1d_pow_hasDerivAt_all hM (z.ofLp i)).hasFDerivAt
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasFDerivAt (fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp i) ^ M)
        (ContinuousLinearMap.toSpanSingleton ℝ
            (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))
          ∘SL EuclideanSpace.proj (𝕜 := ℝ) i) z :=
    fun i _ => HasFDerivAt.comp (f := fun x : E3 => x.ofLp i)
      (g := fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) z (hd i) (hp i)
  have hfin := HasFDerivAt.finsetProd hg
  rw [hfin.fderiv]
  have hval : ∀ i : Fin 3,
      ((ContinuousLinearMap.toSpanSingleton ℝ
            (deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i))
          ∘SL EuclideanSpace.proj (𝕜 := ℝ) i) (Work.BoseB1Cube.e3 k))
        = ((Work.BoseB1Cube.e3 k).ofLp i)
            * deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp i) := by
    intro i
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [sum_apply, smul_apply, hval, smul_eq_mul, Work.BoseB1Cube.e3_ofLp_apply]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi])
      (fun hk => absurd (Finset.mem_univ k) hk)]
  simp only [↓reduceIte, one_mul]
  ring

/-! ## 3. The coordinate bound in terms of the product of the three profiles -/

/-- **Coordinate gradient bound for `chiSmallBase M`**: with `P = ∏_j ζ(z_j)`,
`|∂_k chiSmallBase M z| ≤ Mπ·P^{M-1}` (`M ≥ 2`). -/
lemma abs_fderiv_chiSmallBase_e3_le {M : ℕ} (hM : 2 ≤ M) (z : E3) (k : Fin 3) :
    |fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)|
      ≤ (M : ℝ) * Real.pi * (∏ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i)) ^ (M - 1) := by
  rw [chiSmallBase_fderiv_e3_two hM z k, abs_mul]
  set Q : ℝ := ∏ i ∈ Finset.univ.erase k, Submission.BoseGases.zeta1d (z.ofLp i) with hQ
  have hQnn : 0 ≤ Q :=
    Finset.prod_nonneg (fun i _ => Submission.BoseGases.zeta1d_nonneg _)
  have hQle : Q ≤ 1 := Finset.prod_le_one₀ (fun i _ => Submission.BoseGases.zeta1d_nonneg _)
    (fun i _ => Submission.BoseGases.zeta1d_le_one _)
  have hprod : (∏ i ∈ Finset.univ.erase k, Submission.BoseGases.zeta1d (z.ofLp i) ^ M)
      = Q ^ M := by
    rw [hQ, Finset.prod_pow]
  have hb : |∏ i ∈ Finset.univ.erase k, Submission.BoseGases.zeta1d (z.ofLp i) ^ M|
      ≤ Q ^ (M - 1) := by
    rw [hprod, abs_of_nonneg (pow_nonneg hQnn M)]
    exact pow_le_pow_of_le_one hQnn hQle (by omega)
  calc |deriv (fun w : ℝ => Submission.BoseGases.zeta1d w ^ M) (z.ofLp k)|
        * |∏ i ∈ Finset.univ.erase k, Submission.BoseGases.zeta1d (z.ofLp i) ^ M|
      ≤ ((M : ℝ) * Real.pi * (Submission.BoseGases.zeta1d (z.ofLp k)) ^ (M - 1)) * Q ^ (M - 1) :=
        mul_le_mul (abs_deriv_zeta1dPow_le hM _) hb (abs_nonneg _)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg M) (le_of_lt Real.pi_pos))
            (pow_nonneg (Submission.BoseGases.zeta1d_nonneg _) _))
      _ = (M : ℝ) * Real.pi * (Submission.BoseGases.zeta1d (z.ofLp k) * Q) ^ (M - 1) := by
        rw [mul_pow]; ring
      _ = (M : ℝ) * Real.pi
            * (∏ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i)) ^ (M - 1) := by
        rw [hQ, Finset.mul_prod_erase Finset.univ
          (fun i => Submission.BoseGases.zeta1d (z.ofLp i)) (Finset.mem_univ k)]

/-! ## 4. The operator-norm bound for the unnormalised bump -/

/-- **Gradient bound for `chiSmallBase M`** (`M ≥ 2`): with `P = ∏_j ζ(z_j)`,
`‖∇chiSmallBase M z‖ ≤ 2Mπ·P^{M-1}`.  (The factor `2` covers `√3` from the basis expansion of the
operator norm; the constants here are not optimised.) -/
lemma norm_fderiv_chiSmallBase_le {M : ℕ} (hM : 2 ≤ M) (z : E3) :
    ‖fderiv ℝ (Submission.BoseGases.chiSmallBase M) z‖
      ≤ 2 * ((M : ℝ) * Real.pi
          * (∏ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i)) ^ (M - 1)) := by
  have hcoord : ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)|
        ≤ (M : ℝ) * Real.pi
          * (∏ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i)) ^ (M - 1) :=
    fun k => abs_fderiv_chiSmallBase_e3_le hM z k
  set K : ℝ := (M : ℝ) * Real.pi
      * (∏ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i)) ^ (M - 1) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg M) (le_of_lt Real.pi_pos))
      (pow_nonneg (Finset.prod_nonneg (fun i _ => Submission.BoseGases.zeta1d_nonneg _)) _)
  have hsq := Work.BoseB1Cube.norm_sq_eq_sum_e3 (fderiv ℝ (Submission.BoseGases.chiSmallBase M) z)
  have h1 : ∀ k : Fin 3,
      (fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)) ^ 2 ≤ K ^ 2 := by
    intro k
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hKnn] using hcoord k)
  have h2 : (∑ k : Fin 3,
        (fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)) ^ 2)
      ≤ (2 * K) ^ 2 := by
    calc ∑ k : Fin 3,
          (fderiv ℝ (Submission.BoseGases.chiSmallBase M) z (Work.BoseB1Cube.e3 k)) ^ 2
        ≤ ∑ _k : Fin 3, K ^ 2 := Finset.sum_le_sum (fun k _ => h1 k)
      _ = 3 * K ^ 2 := by simp
      _ ≤ (2 * K) ^ 2 := by nlinarith [hKnn]
  have h3 : ‖fderiv ℝ (Submission.BoseGases.chiSmallBase M) z‖ ^ 2 ≤ (2 * K) ^ 2 := by
    rw [hsq]; exact h2
  have h4 := sq_le_sq.mp h3
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * K)] at h4
  rw [hK] at h4
  exact h4

/-! ## 5. Differentiability of the bump and the factorisation through the normalisation -/

/-- `chiSmallBase M` is differentiable everywhere for `M ≥ 2`. -/
lemma differentiableAt_chiSmallBase {M : ℕ} (hM : 2 ≤ M) (z : E3) :
    DifferentiableAt ℝ (Submission.BoseGases.chiSmallBase M) z := by
  rw [Work.BoseB1Cube.chiSmallBase_eq_prod_zeta1d]
  have hp : ∀ i : Fin 3, DifferentiableAt ℝ (fun x : E3 => x.ofLp i) z :=
    fun i => by simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
  have d0 : DifferentiableAt ℝ (fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp 0) ^ M) z := by
    have h :=
      (Work.BoseB1Cube.zeta1d_pow_hasDerivAt_all hM (z.ofLp 0)).differentiableAt.comp z (hp 0)
    simpa [Function.comp_def] using h
  have d1 : DifferentiableAt ℝ (fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp 1) ^ M) z := by
    have h :=
      (Work.BoseB1Cube.zeta1d_pow_hasDerivAt_all hM (z.ofLp 1)).differentiableAt.comp z (hp 1)
    simpa [Function.comp_def] using h
  have d2 : DifferentiableAt ℝ (fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp 2) ^ M) z := by
    have h :=
      (Work.BoseB1Cube.zeta1d_pow_hasDerivAt_all hM (z.ofLp 2)).differentiableAt.comp z (hp 2)
    simpa [Function.comp_def] using h
  rw [show (fun x : E3 => ∏ i : Fin 3, Submission.BoseGases.zeta1d (x.ofLp i) ^ M)
      = fun x : E3 => Submission.BoseGases.zeta1d (x.ofLp 0) ^ M
          * Submission.BoseGases.zeta1d (x.ofLp 1) ^ M
          * Submission.BoseGases.zeta1d (x.ofLp 2) ^ M from by
      funext x; rw [Fin.prod_univ_three]]
  exact (d0.mul d1).mul d2

/-- `chiSmall M` is its normalisation constant times the unnormalised bump. -/
lemma chiSmall_eq_normFactor_mul_base (M : ℕ) (z : E3) :
    Submission.BoseGases.chiSmall M z
      = Submission.BoseGases.chiSmallNormFactor M * Submission.BoseGases.chiSmallBase M z := by
  rw [Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallNormFactor, div_eq_mul_inv]
  ring

/-- The derivative of `chiSmall M` is the normalisation constant times that of `chiSmallBase M`. -/
lemma fderiv_chiSmall_eq {M : ℕ} (hM : 2 ≤ M) (z : E3) :
    fderiv ℝ (Submission.BoseGases.chiSmall M) z
      = Submission.BoseGases.chiSmallNormFactor M
        • fderiv ℝ (Submission.BoseGases.chiSmallBase M) z := by
  have h : Submission.BoseGases.chiSmall M
      = fun z : E3 => Submission.BoseGases.chiSmallNormFactor M
          * Submission.BoseGases.chiSmallBase M z := by
    funext z
    exact chiSmall_eq_normFactor_mul_base M z
  rw [h]
  exact fderiv_const_mul (differentiableAt_chiSmallBase hM z) _

/-- `chiSmall M` is differentiable everywhere for `M ≥ 2`. -/
lemma differentiableAt_chiSmall {M : ℕ} (hM : 2 ≤ M) (z : E3) :
    DifferentiableAt ℝ (Submission.BoseGases.chiSmall M) z := by
  have h : Submission.BoseGases.chiSmall M
      = fun z : E3 => Submission.BoseGases.chiSmallNormFactor M
          * Submission.BoseGases.chiSmallBase M z := by
    funext z
    exact chiSmall_eq_normFactor_mul_base M z
  rw [h]
  exact (differentiableAt_const _).mul (differentiableAt_chiSmallBase hM z)

/-! ## 6. The pointwise Hölder bound at scale one -/

/-- **Pointwise Hölder gradient bound (unscaled)**: with `κ_M = chiSmallNormFactor M`,
`‖∇chiSmall M z‖ ≤ (2Mπ·κ_M^{1/M})·(chiSmall M z)^{(M-1)/M}` for `M ≥ 2`. -/
lemma norm_fderiv_chiSmall_le {M : ℕ} (hM : 2 ≤ M) (z : E3) :
    ‖fderiv ℝ (Submission.BoseGases.chiSmall M) z‖
      ≤ 2 * (M : ℝ) * Real.pi * (Submission.BoseGases.chiSmallNormFactor M) ^ (1 / (M : ℝ))
        * (Submission.BoseGases.chiSmall M z) ^ (((M : ℝ) - 1) / M) := by
  set A : ℝ := Submission.BoseGases.chiSmallNormFactor M with hA
  set P : ℝ := ∏ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i) with hP
  have hAnn : 0 ≤ A := by rw [hA]; exact Submission.BoseGases.chiSmallNormFactor_nonneg M
  have hApos : 0 < A := by
    rw [hA, Submission.BoseGases.chiSmallNormFactor]
    exact inv_pos.mpr
      (Real.sqrt_pos.mpr (Submission.BoseGases.chiSmallNormSq_pos (by omega : 1 ≤ M)))
  have hPnn : 0 ≤ P := by
    rw [hP]; exact Finset.prod_nonneg (fun i _ => Submission.BoseGases.zeta1d_nonneg _)
  have hbase : ‖fderiv ℝ (Submission.BoseGases.chiSmallBase M) z‖
      ≤ 2 * (M : ℝ) * Real.pi * P ^ (M - 1) := by
    have h := norm_fderiv_chiSmallBase_le hM z
    rw [← hP] at h
    simpa [mul_assoc] using h
  have hchi : Submission.BoseGases.chiSmall M z = A * P ^ M := by
    rw [hA, hP, Submission.BoseGases.chiSmall, Submission.BoseGases.chiSmallNormFactor,
      div_eq_mul_inv, Work.BoseB1Cube.chiSmallBase_eq_prod_zeta1d]
    simp only [Finset.prod_pow]
    ring
  have h1 : A ^ (1 / (M : ℝ)) * A ^ (((M : ℝ) - 1) / M) = A := by
    rw [← Real.rpow_add hApos]
    rw [show (1 : ℝ) / (M : ℝ) + ((M : ℝ) - 1) / (M : ℝ) = 1 by
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      field_simp
      ring]
    rw [Real.rpow_one]
  have h2 : (A * P ^ M) ^ (((M : ℝ) - 1) / M) = A ^ (((M : ℝ) - 1) / M) * P ^ (M - 1) := by
    rw [Real.mul_rpow hAnn (pow_nonneg hPnn M)]
    congr 1
    rw [← Real.rpow_natCast P M, ← Real.rpow_mul hPnn]
    have hexp : (M : ℝ) * (((M : ℝ) - 1) / (M : ℝ)) = (M : ℝ) - 1 := by
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hexp]
    have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
    rw [← hcast, Real.rpow_natCast]
  calc ‖fderiv ℝ (Submission.BoseGases.chiSmall M) z‖
      = A * ‖fderiv ℝ (Submission.BoseGases.chiSmallBase M) z‖ := by
        rw [fderiv_chiSmall_eq hM z, norm_smul, Real.norm_eq_abs, abs_of_nonneg hAnn]
    _ ≤ A * (2 * (M : ℝ) * Real.pi * P ^ (M - 1)) := mul_le_mul_of_nonneg_left hbase hAnn
    _ = 2 * (M : ℝ) * Real.pi * A ^ (1 / (M : ℝ))
          * (A ^ (((M : ℝ) - 1) / M) * P ^ (M - 1)) := by
        calc A * (2 * (M : ℝ) * Real.pi * P ^ (M - 1))
            = 2 * (M : ℝ) * Real.pi * A * P ^ (M - 1) := by ring
          _ = 2 * (M : ℝ) * Real.pi * (A ^ (1 / (M : ℝ)) * A ^ (((M : ℝ) - 1) / M))
                * P ^ (M - 1) := by rw [h1]
          _ = 2 * (M : ℝ) * Real.pi * A ^ (1 / (M : ℝ))
                * (A ^ (((M : ℝ) - 1) / M) * P ^ (M - 1)) := by ring
    _ = 2 * (M : ℝ) * Real.pi * A ^ (1 / (M : ℝ)) * ((A * P ^ M) ^ (((M : ℝ) - 1) / M)) := by
        rw [h2]
    _ = 2 * (M : ℝ) * Real.pi * A ^ (1 / (M : ℝ))
          * (Submission.BoseGases.chiSmall M z) ^ (((M : ℝ) - 1) / M) := by rw [hchi]

/-! ## 7. The Hölder gradient bound at scale `s` -/

/-- **Pointwise Hölder gradient bound for the cosine cube bump at a scale (fixed `M`).**

For every `M ≥ 2` there is `C ≥ 0` with, for every `s > 0`, shift `v` and `z`,
`‖∇(χ_M(s⁻¹•· − v))(z)‖ ≤ C·s⁻¹·(χ_M(s⁻¹•z − v))^((M−1)/M)`, where `χ_M = Submission.BoseGases.chiSmall M`
(`= (ζ₁ζ₂ζ₃)^M / √∫(ζ₁ζ₂ζ₃)^{2M}`, `ζ = zeta1d`).  (The constant necessarily depends on `M`.)

Route: the explicit coordinate derivative `∂_j(ζ^M)(y) = Mπ sin(πy)ζ(y)^{M-1}` gives
`|∂_j χ_M| ≤ Mπ·κ_M^{-1/M}·χ_M^{(M−1)/M}` (the remaining factors are `≤ 1`), and the chain rule for
the rescaling by `s`.  Corpus bricks: `Work.BoseB1Cube.chiSmallBase_fderiv_e3` (coordinate
formula), `Work.BoseB1Cube.abs_zeta1dDerivF_le`, `Submission.BoseGases.chiSmall_eq_chiSmallBase_mul`,
`chiSmall_nonneg`, `chiSmall_hasCompactSupport`. -/
theorem chiSmallGradHolder (M : ℕ) (hM : 2 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ), 0 < s → ∀ (v z : EuclideanSpace ℝ (Fin 3)),
      ‖fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmall M (s⁻¹ • w - v)) z‖
        ≤ C * s⁻¹ * (Submission.BoseGases.chiSmall M (s⁻¹ • z - v)) ^ (((M : ℝ) - 1) / M) := by
  refine ⟨2 * (M : ℝ) * Real.pi * (Submission.BoseGases.chiSmallNormFactor M) ^ (1 / (M : ℝ)),
    ?_, ?_⟩
  · have hA : (0 : ℝ) ≤ Submission.BoseGases.chiSmallNormFactor M :=
      Submission.BoseGases.chiSmallNormFactor_nonneg M
    have h1 : (0 : ℝ) ≤ (Submission.BoseGases.chiSmallNormFactor M) ^ (1 / (M : ℝ)) :=
      Real.rpow_nonneg hA _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg M))
      (le_of_lt Real.pi_pos)) h1
  · intro s hs v z
    have hbound : ∀ y : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmall M) y‖
        ≤ 2 * (M : ℝ) * Real.pi * (Submission.BoseGases.chiSmallNormFactor M) ^ (1 / (M : ℝ))
          * (Submission.BoseGases.chiSmall M y) ^ (((M : ℝ) - 1) / M) :=
      fun y => norm_fderiv_chiSmall_le hM y
    have hχd : DifferentiableAt ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v) :=
      differentiableAt_chiSmall hM _
    have hφd : DifferentiableAt ℝ (fun w : E3 => s⁻¹ • w - v) z :=
      ((differentiableAt_id (x := z)).const_smul (s⁻¹)).sub_const v
    have hφ : fderiv ℝ (fun w : E3 => s⁻¹ • w - v) z = s⁻¹ • (1 : E3 →L[ℝ] E3) := by
      have h1 : fderiv ℝ (fun w : E3 => s⁻¹ • w) z = s⁻¹ • (1 : E3 →L[ℝ] E3) := by
        have h := fderiv_fun_const_smul (𝕜 := ℝ) (f := fun y : E3 => y) (x := z)
          differentiableAt_id (s⁻¹)
        rw [fderiv_fun_id] at h
        rw [show (1 : E3 →L[ℝ] E3) = ContinuousLinearMap.id ℝ E3 from rfl]
        exact h
      rw [fderiv_sub_const, h1]
    have hfd : fderiv ℝ (fun w : E3 => Submission.BoseGases.chiSmall M (s⁻¹ • w - v)) z
        = (fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v))
          ∘SL (s⁻¹ • (1 : E3 →L[ℝ] E3)) := by
      have h := fderiv_comp z hχd hφd
      rw [hφ] at h
      simpa [Function.comp_def] using h
    have hnorm : ‖(fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v))
          ∘SL (s⁻¹ • (1 : E3 →L[ℝ] E3))‖
        ≤ s⁻¹ * ‖fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v)‖ := by
      have h1 : ‖(s⁻¹ • (1 : E3 →L[ℝ] E3))‖ = s⁻¹ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hs)),
          show (1 : E3 →L[ℝ] E3) = ContinuousLinearMap.id ℝ E3 from rfl,
          ContinuousLinearMap.norm_id, mul_one]
      calc ‖(fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v))
            ∘SL (s⁻¹ • (1 : E3 →L[ℝ] E3))‖
          ≤ ‖fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v)‖
              * ‖(s⁻¹ • (1 : E3 →L[ℝ] E3))‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = s⁻¹ * ‖fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v)‖ := by
            rw [h1]; ring
    calc ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiSmall M (s⁻¹ • w - v)) z‖
        = ‖(fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v))
            ∘SL (s⁻¹ • (1 : E3 →L[ℝ] E3))‖ := by rw [hfd]
      _ ≤ s⁻¹ * ‖fderiv ℝ (Submission.BoseGases.chiSmall M) (s⁻¹ • z - v)‖ := hnorm
      _ ≤ s⁻¹ * (2 * (M : ℝ) * Real.pi
            * (Submission.BoseGases.chiSmallNormFactor M) ^ (1 / (M : ℝ))
            * (Submission.BoseGases.chiSmall M (s⁻¹ • z - v)) ^ (((M : ℝ) - 1) / M)) :=
          mul_le_mul_of_nonneg_left (hbound _) (inv_nonneg.mpr (le_of_lt hs))
      _ = 2 * (M : ℝ) * Real.pi * (Submission.BoseGases.chiSmallNormFactor M) ^ (1 / (M : ℝ))
            * s⁻¹ * (Submission.BoseGases.chiSmall M (s⁻¹ • z - v)) ^ (((M : ℝ) - 1) / M) := by
          ring

end Work.BoseSWE
