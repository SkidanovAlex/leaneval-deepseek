import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.BusemannDeriv
import Submission.Work.Mostow.BusemannBound
import Submission.Work.Mostow.BaryBase

/-!
# Facts about the Poisson kernel `pfun` and its derivative `dpfun`

`pfun n x ξ = (tpart x - ⟪x,ξ⟫)^{-(n-1)}` is the density of the visual (Poisson) measure
`visual n x` with respect to `sigma n`, and `dpfun n x ξ` is its derivative in the base point.
This file records the five analytic facts about the pair `(pfun, dpfun)` that the natural-map
computation needs: differentiability with the stated derivative, the normalisation
`pfun n 0 ξ = 1`, positivity, the value of the derivative at the base point, and a uniform bound
for the derivative on each ball `‖x‖ ≤ R`, uniform over `ξ ∈ Sph n`.

The whole computation is the chain rule applied to `x ↦ tpart x - ⟪x,ξ⟫` followed by the real
power `t ↦ t^{-(n-1)}`; the hypothesis `ξ ∈ Sph n` is what keeps the base strictly positive.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-! ## Helper lemmas -/

/-- `innerSL ℝ` is compatible with scalar multiplication in its first argument. -/
private lemma innerSL_smul_pf (c : ℝ) (v : E n) : innerSL ℝ (c • v) = c • innerSL ℝ v := by
  ext h
  simp [innerSL_apply_apply]

/-- The chart time coordinate has derivative `(tpart x)⁻¹ • innerSL ℝ x`. -/
private lemma hasFDerivAt_tpart_pf (x : E n) :
    HasFDerivAt (fun y : E n => tpart y) ((tpart x)⁻¹ • innerSL ℝ x) x := by
  have h := Work.Mostow.hasFDerivAt_tpart n x
  rwa [innerSL_smul_pf] at h

/-- The functional `y ↦ ⟪y,ξ⟫` has derivative `innerSL ℝ ξ`. -/
private lemma hasFDerivAt_inner_pf (ξ : E n) (x : E n) :
    HasFDerivAt (fun y : E n => inner ℝ y ξ) (innerSL ℝ ξ) x := by
  simpa [real_inner_comm] using (innerSL ℝ ξ).hasFDerivAt (x := x)

/-! ## Differentiability of `x ↦ pfun n x ξ` -/

/-- `x ↦ pfun n x ξ` is Fréchet differentiable on all of `E n`, with derivative `dpfun n x ξ`. -/
theorem pfun_hasFDerivAt (n : ℕ) (ξ : E n) (hξ : ξ ∈ Sph n) (x : E n) :
    HasFDerivAt (fun x => pfun n x ξ) (dpfun n x ξ) x := by
  have hbase : 0 < tpart x - inner ℝ x ξ := busemann_arg_pos ξ hξ x
  have hp := ((hasFDerivAt_tpart_pf x).sub (hasFDerivAt_inner_pf ξ x)).rpow_const
    (p := -((n : ℝ) - 1)) (Or.inl (ne_of_gt hbase))
  have key : HasFDerivAt
      (fun y : E n => (tpart y - inner ℝ y ξ) ^ (-((n : ℝ) - 1)))
      ((-((n : ℝ) - 1) * (tpart x - inner ℝ x ξ) ^ (-((n : ℝ) - 1) - 1)) •
        ((tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ)) x := hp
  simpa only [pfun, dpfun] using key

/-! ## The size of `dpfun` -/

/-- Norm of `dpfun n x ξ`, written as a product of a scalar factor and the norm of the linear
part. -/
private lemma norm_dpfun_factor (n : ℕ) (ξ x : E n) (hξ : ξ ∈ Sph n) :
    ‖dpfun n x ξ‖ = |(n : ℝ) - 1| * (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) *
      ‖(tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ‖ := by
  have hFpos : 0 < tpart x - inner ℝ x ξ := busemann_arg_pos ξ hξ x
  have he : -((n : ℝ) - 1) - 1 = -(n : ℝ) := by ring
  rw [dpfun, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos hFpos _), he]

/-- The norm of the linear factor `(tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ` is at most `R + 1`
on the ball `‖x‖ ≤ R`. -/
private lemma norm_lin_factor_le (ξ x : E n) (hξ : ξ ∈ Sph n) {R : ℝ} (hx : ‖x‖ ≤ R) :
    ‖(tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ‖ ≤ R + 1 := by
  have hξ1 : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have htpos : 0 < tpart x := tpart_pos x
  have h1 := norm_sub_le ((tpart x)⁻¹ • innerSL ℝ x) (innerSL ℝ ξ)
  have h2 : ‖(tpart x)⁻¹ • innerSL ℝ x‖ = (tpart x)⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), innerSL_apply_norm]
  have h3 : ‖innerSL ℝ ξ‖ = 1 := by rw [innerSL_apply_norm, hξ1]
  have h4 : (tpart x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_tpart x)
  have h5 : (tpart x)⁻¹ * ‖x‖ ≤ R := by
    calc (tpart x)⁻¹ * ‖x‖ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right h4 (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ ≤ R := hx
  calc ‖(tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ‖
      ≤ ‖(tpart x)⁻¹ • innerSL ℝ x‖ + ‖innerSL ℝ ξ‖ := h1
    _ = (tpart x)⁻¹ * ‖x‖ + 1 := by rw [h2, h3]
    _ ≤ R + 1 := by linarith

/-- Uniform bound on `dpfun` on a ball, uniform in `ξ ∈ Sph n`. -/
theorem norm_dpfun_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) (ξ : E n) (hξ : ξ ∈ Sph n) (x : E n)
    (hx : ‖x‖ ≤ R) :
    ‖dpfun n x ξ‖ ≤
      |(n : ℝ) - 1| * (Real.sqrt (1 + R ^ 2) + R) ^ (n : ℝ) * (R + 1) := by
  set M : ℝ := Real.sqrt (1 + R ^ 2) + R with hM
  have hFpos : 0 < tpart x - inner ℝ x ξ := busemann_arg_pos ξ hξ x
  have hM0 : 0 ≤ M := by
    rw [hM]
    have := Real.sqrt_nonneg (1 + R ^ 2)
    linarith
  have hMpos : 0 < M := by
    rw [hM]
    have h1 : (1 : ℝ) ≤ Real.sqrt (1 + R ^ 2) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + R ^ 2 by nlinarith [sq_nonneg R])
      rwa [Real.sqrt_one] at this
    linarith
  -- the reciprocal of the base is bounded by `M`, so the `-n`-th power is bounded by `M ^ n`
  have hinv : (tpart x - inner ℝ x ξ)⁻¹ ≤ M := by
    rw [hM]
    exact inv_g_le ξ x hξ hR hx
  have hMg : M⁻¹ ≤ tpart x - inner ℝ x ξ := (inv_le_comm₀ hFpos hMpos).mp hinv
  have hpow : (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) ≤ M ^ (n : ℝ) := by
    have h1 : (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) ≤ M⁻¹ ^ (-(n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hMpos) hMg (neg_nonpos.mpr (Nat.cast_nonneg n))
    have h2 : M⁻¹ ^ (-(n : ℝ)) = M ^ (n : ℝ) := by
      rw [Real.inv_rpow hM0, Real.rpow_neg hM0, inv_inv]
    rwa [h2] at h1
  have hlin := norm_lin_factor_le ξ x hξ hx
  have hrpow0 : 0 ≤ (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) := Real.rpow_nonneg hFpos.le _
  rw [norm_dpfun_factor n ξ x hξ]
  calc |(n : ℝ) - 1| * (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) *
        ‖(tpart x)⁻¹ • innerSL ℝ x - innerSL ℝ ξ‖
      ≤ |(n : ℝ) - 1| * (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) * (R + 1) :=
        mul_le_mul_of_nonneg_left hlin (mul_nonneg (abs_nonneg _) hrpow0)
    _ = (|(n : ℝ) - 1| * (R + 1)) * (tpart x - inner ℝ x ξ) ^ (-(n : ℝ)) := by ring
    _ ≤ (|(n : ℝ) - 1| * (R + 1)) * M ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = |(n : ℝ) - 1| * M ^ (n : ℝ) * (R + 1) := by ring

/-! ## The five facts -/

theorem PfunFacts (n : ℕ) :
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ x : Submission.Mostow.E n,
        HasFDerivAt (fun x => Work.Mostow.pfun n x ξ) (Work.Mostow.dpfun n x ξ) x) ∧
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n → Work.Mostow.pfun n 0 ξ = 1) ∧
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ x : Submission.Mostow.E n, 0 < Work.Mostow.pfun n x ξ) ∧
    (∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      Work.Mostow.dpfun n 0 ξ = ((n : ℝ) - 1) • innerSL ℝ ξ) ∧
    (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ x : Submission.Mostow.E n, ‖x‖ ≤ R → ‖Work.Mostow.dpfun n x ξ‖ ≤ C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ x
    exact pfun_hasFDerivAt n ξ hξ x
  · intro ξ hξ
    simp [pfun, tpart]
  · intro ξ hξ x
    show 0 < (tpart x - inner ℝ x ξ) ^ (-((n : ℝ) - 1))
    exact Real.rpow_pos_of_pos (busemann_arg_pos ξ hξ x) _
  · intro ξ hξ
    simp [dpfun, tpart]
    module
  · intro R hR
    exact ⟨|(n : ℝ) - 1| * (Real.sqrt (1 + R ^ 2) + R) ^ (n : ℝ) * (R + 1),
      fun ξ hξ x hx => norm_dpfun_le n hR ξ hξ x hx⟩

end

end Work.Mostow
