import Mathlib
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Log-convexity of the `L^p` norms on `ℤ/Qℤ`

`Work.Analysis.Concentration.LpNormZMod Q p f` is the `L^p` norm of `f : ℤ/Qℤ → ℂ` with respect
to the Haar probability measure on `ℤ/Qℤ` (normalized counting measure),
`‖f‖_{L^p} = (Q⁻¹ ∑_x ‖f x‖^p)^{1/p}`.

The result proved here is the standard log-convexity (Riesz–Thorin interpolation at the level of
norms) of the family `p ↦ ‖f‖_{L^p}`: for `1 < q`, `0 ≤ θ ≤ 1` and

`1/r = θ/1 + (1 - θ)/q`,

one has `‖f‖_{L^r} ≤ ‖f‖_{L^1}^θ ‖f‖_{L^q}^{1-θ}`.

The proof is exactly the classical one.  Writing `S_p = ∑_x ‖f x‖^p`, the definition gives
`‖f‖_{L^p} = Q^{-1/p} S_p^{1/p}`, and since `Q^{-1/r} = Q^{-θ} Q^{-(1-θ)/q}` by the hypothesis on
the exponents, everything reduces to the pure Hölder inequality

`S_r^{1/r} ≤ S_1^θ S_q^{(1-θ)/q}`,

which follows from `Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg` applied to
`f x = ‖f x‖^θ`, `g x = ‖f x‖^{1-θ}` and the Hölder triple
`(1/θ, q/(1-θ), r)` — indeed `θ + (1-θ)/q = 1/r`.  The endpoint cases `θ = 0` and `θ = 1`
(where `r = q`, resp. `r = 1`) are equalities and are handled separately.

-/

namespace Work.Analysis.Paraproduct

/-- **Hölder interpolation of finite `ℓ^p` sums.**  For nonnegative `w : ι → ℝ` on a finite set
`s`, exponents `q, r > 0`, `0 < θ < 1` with `1/r = θ + (1-θ)/q`,

`(∑_{i ∈ s} w_i^r)^{1/r} ≤ (∑_{i ∈ s} w_i)^θ (∑_{i ∈ s} w_i^q)^{(1-θ)/q}`.

This is Hölder's inequality applied to `w^θ · w^{1-θ}` with the conjugate exponents `1/θ` and
`q/(1-θ)` (whose sum of reciprocals is `θ + (1-θ)/q = 1/r`). -/
private lemma sum_rpow_holder {ι : Type*} (s : Finset ι) {q r θ : ℝ} (hq : 0 < q) (hr : 0 < r)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hrel : 1 / r = θ + (1 - θ) / q) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, w i) ^ θ * (∑ i ∈ s, w i ^ q) ^ ((1 - θ) / q) := by
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  have h1θne : 1 - θ ≠ 0 := by linarith
  have htriple : (1 / θ).HolderTriple (q / (1 - θ)) r :=
    ⟨by rw [inv_div, inv_div, ← one_div, div_one, ← hrel],
     one_div_pos.mpr hθ0, div_pos hq (sub_pos.mpr hθ1)⟩
  have hH := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg s (f := fun i => w i ^ θ)
    (g := fun i => w i ^ (1 - θ)) htriple
    (fun i hi => Real.rpow_nonneg (hw i hi) θ)
    (fun i hi => Real.rpow_nonneg (hw i hi) (1 - θ))
  -- the left-hand side of Hölder's inequality is `∑ wᵢ^r`
  have h1 : (∑ i ∈ s, (w i ^ θ * w i ^ (1 - θ)) ^ r) = ∑ i ∈ s, w i ^ r := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Real.rpow_add' (hw i hi) (by norm_num : θ + (1 - θ) ≠ 0),
      show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  -- the two `L^p` factors are `∑ wᵢ` and `∑ wᵢ^q`
  have h2 : (∑ i ∈ s, (w i ^ θ) ^ (1 / θ)) = ∑ i ∈ s, w i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Real.rpow_mul (hw i hi) θ (1 / θ), mul_one_div_cancel hθne, Real.rpow_one]
  have h3 : (∑ i ∈ s, (w i ^ (1 - θ)) ^ (q / (1 - θ))) = ∑ i ∈ s, w i ^ q := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Real.rpow_mul (hw i hi) (1 - θ) (q / (1 - θ)), ← mul_div_assoc,
      mul_div_cancel_left₀ q h1θne]
  have hexp1 : r / (1 / θ) = r * θ := by rw [one_div, div_inv_eq_mul]
  have hexp2 : r / (q / (1 - θ)) = r * (1 - θ) / q := by rw [div_div_eq_mul_div]
  have hH' : ∑ i ∈ s, w i ^ r ≤
      (∑ i ∈ s, w i) ^ (r * θ) * (∑ i ∈ s, w i ^ q) ^ (r * (1 - θ) / q) := by
    rw [h1, h2, h3, hexp1, hexp2] at hH
    exact hH
  have hLHS : 0 ≤ ∑ i ∈ s, w i ^ r := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hw i hi) r
  have hA : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hB : 0 ≤ ∑ i ∈ s, w i ^ q := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hw i hi) q
  have hexp3 : (r * θ) * (1 / r) = θ := by
    rw [mul_one_div, mul_div_cancel_left₀ _ (ne_of_gt hr)]
  have hexp4 : (r * (1 - θ) / q) * (1 / r) = (1 - θ) / q := by
    field_simp
  -- raise both sides to the power `1/r`
  refine le_trans (Real.rpow_le_rpow hLHS hH' (by positivity)) ?_
  rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)]
  rw [← Real.rpow_mul hA, ← Real.rpow_mul hB, hexp3, hexp4]

/-- `LpNormZMod` with the normalizing factor `Q^{-1/p}` split off:
`‖f‖_{L^p} = Q^{-1/p} (∑_x ‖f x‖^p)^{1/p}` (the un-normalized `ℓ^p` sum w.r.t. counting measure
raised to `1/p`).  No positivity assumption on `p` is needed. -/
private lemma LpNormZMod_eq_rpow (Q : ℕ) [NeZero Q] {p : ℝ} (u : ZMod Q → ℂ) :
    Work.Analysis.Concentration.LpNormZMod Q p u
      = (Q:ℝ) ^ (-(1/p)) * (∑ x : ZMod Q, ‖u x‖ ^ p) ^ (1/p) := by
  have hQnn : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
  unfold Work.Analysis.Concentration.LpNormZMod
  rw [Real.mul_rpow (inv_nonneg.mpr hQnn)
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p)]
  rw [Real.inv_rpow hQnn, ← Real.rpow_neg hQnn]

/-- The `L^1` norm: `‖f‖_{L^1} = Q⁻¹ ∑_x ‖f x‖`. -/
private lemma LpNormZMod_one (Q : ℕ) [NeZero Q] (u : ZMod Q → ℂ) :
    Work.Analysis.Concentration.LpNormZMod Q 1 u = (Q:ℝ)⁻¹ * ∑ x : ZMod Q, ‖u x‖ := by
  unfold Work.Analysis.Concentration.LpNormZMod
  simp only [one_div, inv_one, Real.rpow_one]

/-- Bookkeeping of the normalizing factors `Q^{-1/p}`: under `1/r = θ/1 + (1-θ)/q` the right-hand
side of the log-convexity inequality equals `Q^{-1/r} (A^θ B^{(1-θ)/q})`. -/
private lemma rpow_combine (Q : ℕ) [NeZero Q] {q r θ : ℝ}
    (hrel : 1 / r = θ / 1 + (1 - θ) / q) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ((Q:ℝ)⁻¹ * A) ^ θ * ((Q:ℝ) ^ (-(1/q)) * B ^ (1/q)) ^ (1 - θ)
      = (Q:ℝ) ^ (-(1/r)) * (A ^ θ * B ^ ((1 - θ)/q)) := by
  have hQnn : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
  have hQpos : (0:ℝ) < Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne Q))
  have hrel' : θ + (1 - θ) / q = 1 / r := by rw [hrel, div_one]
  have hcast : (Q:ℝ)⁻¹ = (Q:ℝ) ^ (-1:ℝ) := by rw [Real.rpow_neg hQnn 1, Real.rpow_one]
  rw [hcast, Real.mul_rpow (Real.rpow_nonneg hQnn (-1)) hA,
    Real.mul_rpow (Real.rpow_nonneg hQnn (-(1/q))) (Real.rpow_nonneg hB (1/q)),
    ← Real.rpow_mul hQnn (-1) θ,
    ← Real.rpow_mul hQnn (-(1/q)) (1 - θ),
    ← Real.rpow_mul hB (1/q) (1 - θ)]
  rw [show (-1:ℝ) * θ = -θ by ring,
    show (-(1/q)) * (1 - θ) = -(1 - θ)/q by ring_nf,
    show (1/q) * (1 - θ) = (1 - θ)/q by ring]
  rw [show Q ^ (-θ) * A ^ θ * (Q ^ (-(1 - θ) / q) * B ^ ((1 - θ) / q))
      = (Q ^ (-θ) * Q ^ (-(1 - θ) / q)) * (A ^ θ * B ^ ((1 - θ) / q)) by ring]
  rw [← Real.rpow_add hQpos (-θ) (-(1 - θ) / q),
    show -θ + -(1 - θ)/q = -(1/r) by
      rw [show -θ + -(1 - θ)/q = -(θ + (1 - θ)/q) by ring, hrel']]

/-- **Log-convexity of the `L^p` norms on `ℤ/Qℤ`** (the `L^p`-interpolation / Hölder estimate):
for `1 < q`, `0 ≤ θ ≤ 1` and `1/r = θ/1 + (1-θ)/q`,
`‖f‖_{L^r(ℤ/Qℤ)} ≤ ‖f‖_{L^1(ℤ/Qℤ)}^θ ‖f‖_{L^q(ℤ/Qℤ)}^{1-θ}`. -/
theorem LpNormZMod_logconvex (Q : ℕ) [NeZero Q] {q r θ : ℝ} (hq : 1 < q)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hrel : 1 / r = θ / 1 + (1 - θ) / q) (u : ZMod Q → ℂ) :
    Work.Analysis.Concentration.LpNormZMod Q r u
      ≤ Work.Analysis.Concentration.LpNormZMod Q 1 u ^ θ *
        Work.Analysis.Concentration.LpNormZMod Q q u ^ (1 - θ) := by
  by_cases hθzero : θ = 0
  · -- endpoint `θ = 0`: then `1/r = 1/q`, i.e. `r = q`, and both sides are `‖f‖_{L^q}`
    subst hθzero
    have hrq : r = q := by
      have h1 : 1 / r = 1 / q := by rw [hrel]; norm_num
      rw [one_div, one_div] at h1
      exact inv_inj.mp h1
    rw [hrq, sub_zero, Real.rpow_zero, Real.rpow_one, one_mul]
  · by_cases hθone : θ = 1
    · -- endpoint `θ = 1`: then `1/r = 1`, i.e. `r = 1`, and both sides are `‖f‖_{L^1}`
      subst hθone
      have hr1 : r = 1 := by
        have h1 : 1 / r = 1 := by rw [hrel]; norm_num
        rw [one_div] at h1
        exact inv_eq_one.mp h1
      rw [hr1, sub_self, Real.rpow_one, Real.rpow_zero, mul_one]
    · -- main case `0 < θ < 1`: pure Hölder interpolation plus the `Q` bookkeeping
      have hθ0' : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθzero)
      have hθ1' : θ < 1 := lt_of_le_of_ne hθ1 hθone
      have hqpos : 0 < q := lt_trans zero_lt_one hq
      have h1r : 0 < 1 / r := by
        have h2 : 1 / r = (1 / q) + θ * (1 - 1 / q) := by rw [hrel, div_one]; ring
        rw [h2]
        have hq1 : 0 < 1 / q := one_div_pos.mpr hqpos
        have hq2 : 0 < 1 - 1 / q := sub_pos.mpr ((div_lt_one hqpos).mpr hq)
        positivity
      have hr : 0 < r := one_div_pos.mp h1r
      have hQnn : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
      have hcore : (∑ x : ZMod Q, ‖u x‖ ^ r) ^ (1 / r) ≤
          (∑ x : ZMod Q, ‖u x‖) ^ θ * (∑ x : ZMod Q, ‖u x‖ ^ q) ^ ((1 - θ) / q) :=
        sum_rpow_holder Finset.univ hqpos hr hθ0' hθ1' (by rw [hrel, div_one])
          (fun x _ => norm_nonneg _)
      have hsplit := rpow_combine (Q := Q) (q := q) (r := r) (θ := θ) hrel
        (A := ∑ x : ZMod Q, ‖u x‖) (B := ∑ x : ZMod Q, ‖u x‖ ^ q)
        (Finset.sum_nonneg fun x _ => norm_nonneg _)
        (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) q)
      rw [LpNormZMod_eq_rpow Q u, LpNormZMod_one Q u, LpNormZMod_eq_rpow Q u (p := q), hsplit]
      exact mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hQnn _)

end Work.Analysis.Paraproduct
