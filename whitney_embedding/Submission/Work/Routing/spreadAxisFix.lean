import Mathlib

/-!
# Spreading a diffeo-germ of `ℝⁿ` which fixes a coordinate axis

`Work.Routing.spreadAxisFix` is the crux of the "extension/gluing" step of the arc straightening
(see `wfmy/NOTES_rjl_SESSION4_DESIGN.md`).  Its content: a diffeo-germ `σ` of `EuclideanSpace ℝ (Fin n)`
which fixes the first coordinate axis pointwise near `0` and is close to the identity there can be
"spread" to a diffeo-germ `τ` which still fixes the whole axis pointwise, agrees with `σ` near `0`,
and whose source contains an arbitrary half-space cylinder.

This file currently contains the linear-algebra/mean-value core (a `κ`-perturbation of the identity
on a convex set is injective) and the statement of the main lemma.
-/

noncomputable section

open Set Metric Topology
open scoped Topology

namespace Work.Routing

/-- **A `κ`-perturbation of the identity on a convex set is injective.**  If `f : E → E` is
differentiable on a convex set `s` with `‖fderiv f x - 1‖ ≤ κ < 1` there, then `f` is injective
on `s`. -/
theorem injOn_of_norm_fderiv_sub_id_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {s : Set E} (hs : Convex ℝ s) {κ : ℝ} (hκ : κ < 1)
    (hfd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hbd : ∀ x ∈ s, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ κ) :
    Set.InjOn f s := by
  have hgd : ∀ x ∈ s, DifferentiableAt ℝ (f - id) x := fun x hx =>
    (hfd x hx).sub (differentiableAt_id)
  have hder : ∀ x ∈ s, fderiv ℝ (f - id) x
      = fderiv ℝ f x - ContinuousLinearMap.id ℝ E := by
    intro x hx
    have h := ((hfd x hx).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
    simpa using h
  have hbd' : ∀ x ∈ s, ‖fderiv ℝ (f - id) x‖ ≤ κ := by
    intro x hx
    rw [hder x hx]
    exact hbd x hx
  intro x hx y hy hxy
  have hlip := hs.norm_image_sub_le_of_norm_fderiv_le hgd hbd' hy hx
  have hlip' : ‖(f x - x) - (f y - y)‖ ≤ κ * ‖x - y‖ := by
    simpa only [Pi.sub_apply, id_eq] using hlip
  have h3 : (f x - x) - (f y - y) = -(x - y) := by rw [hxy]; abel
  have h4 : ‖x - y‖ ≤ κ * ‖x - y‖ := by
    rw [h3, norm_neg] at hlip'
    exact hlip'
  have h5 : (1 - κ) * ‖x - y‖ ≤ 0 := by linarith
  have h6 : 0 < 1 - κ := by linarith
  have h7 : ‖x - y‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (x - y), h5, h6, hc]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h7 (norm_nonneg _)))

/-- **The axis-fixing estimate.**  If `σ` fixes the coordinate axis pointwise and its derivative is
`-close to the identity, then `σ z - z` is bounded by `δ` times the transverse part of `z`.  (Used
with `δ = 1/16` and `r` the radius of the ball on which `hclose` holds.) -/
theorem norm_sub_le_of_axis_fixing {n : ℕ} (hn : 1 ≤ n) {r δ : ℝ} (hr : 0 < r)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hax : ∀ t : ℝ, σ (t • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))
      = t • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))
    (hfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hbd : ∀ z, ‖z‖ ≤ r → ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ ≤ r / 2) :
    ‖σ z - z‖ ≤ δ * ‖z - (z ⟨0, hn⟩) • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)‖ := by
  set w : EuclideanSpace ℝ (Fin n) := (z ⟨0, hn⟩) • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ) with hw
  have hgw : σ w = w := hax (z ⟨0, hn⟩)
  have hzw : ‖z - w‖ = ‖z - (z ⟨0, hn⟩) • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)‖ := by rw [hw]
  have hzn : ‖w‖ ≤ r / 2 := by
    rw [hw, norm_smul, PiLp.norm_single]
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    exact le_trans (PiLp.norm_apply_le z ⟨0, hn⟩) hz
  have hzr : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  have hwr : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  have hdiff : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
      DifferentiableAt ℝ (σ - id) x := by
    intro x hx
    exact (hfd x).differentiableAt.sub differentiableAt_id
  have hbnd : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖fderiv ℝ (σ - id) x‖ ≤ δ := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    have h1 : fderiv ℝ (σ - id) x
        = fderiv ℝ σ x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      have h2 := ((hfd x).sub (hasFDerivAt_id x)).fderiv
      simpa only using h2
    rw [h1]
    exact hbd x hx.le
  have hmvt := (convex_ball (0 : EuclideanSpace ℝ (Fin n)) r).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbnd hzr hwr
  have hmvt' : ‖((σ - id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) w
      - ((σ - id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) z‖
      ≤ δ * ‖w - z‖ := hmvt
  have h0 : ((σ - id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) w = 0 := by
    simp only [Pi.sub_apply, id_eq, hgw, sub_self]
  rw [h0, zero_sub] at hmvt'
  rw [norm_sub_rev] at hmvt'
  rw [hzw] at hmvt'
  simpa only [Pi.sub_apply, id_eq, norm_neg] using hmvt'

theorem norm_sub_le_of_close {n : ℕ} (hn : 1 ≤ n) {r δ : ℝ} (hr : 0 < r)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (h0 : σ 0 = 0)
    (hfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hbd : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ ≤ 2 * r) : ‖σ z - z‖ ≤ δ * ‖z‖ := by
  set φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := σ - id with hφ
  have hφ0 : φ 0 = 0 := by
    simp only [hφ, Pi.sub_apply, id_eq, h0, sub_self]
  set F : ℝ → EuclideanSpace ℝ (Fin n) := fun t => φ (t • z) with hF
  have hF0 : F 0 = φ 0 := by simp only [hF, zero_smul]
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt F (((fderiv ℝ σ (t • z) - ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) z) (Set.Icc (0:ℝ) 1) t := by
    intro t ht
    have h2 : HasDerivAt (fun s : ℝ => s • z) z t := by
      simpa using (hasDerivAt_id t).smul_const z
    have h4 : HasDerivAt (fun s : ℝ => σ (s • z)) ((fderiv ℝ σ (t • z)) z) t :=
      (hfd (t • z)).comp_hasDerivAt t h2
    have h5 : HasDerivAt F ((fderiv ℝ σ (t • z)) z - z) t := by
      have h6 := h4.sub h2
      have h7 : (fun s : ℝ => φ (s • z))
          = ((fun s : ℝ => σ (s • z)) - fun s : ℝ => s • z) := by
        funext s
        simp only [Pi.sub_apply, hφ, id_eq]
      rw [hF, h7]
      exact h6
    have h6 : ((fderiv ℝ σ (t • z) - ContinuousLinearMap.id ℝ
        (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) z = (fderiv ℝ σ (t • z)) z - z := by
      simp only [sub_apply, ContinuousLinearMap.id_apply]
    rw [h6]
    exact h5.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖((fderiv ℝ σ (t • z) - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) z‖ ≤ δ * ‖z‖ := by
    intro t ht
    have htz : ‖t • z‖ < 2 * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      have h1 : t * ‖z‖ ≤ t * (2 * r) := mul_le_mul_of_nonneg_left hz ht.1
      have h2 : t * (2 * r) < 1 * (2 * r) := mul_lt_mul_of_pos_right ht.2 (by linarith)
      linarith
    calc ‖((fderiv ℝ σ (t • z) - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) z‖
        ≤ ‖fderiv ℝ σ (t • z) - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ * ‖z‖ :=
          ContinuousLinearMap.le_opNorm _ z
      _ ≤ δ * ‖z‖ := mul_le_mul_of_nonneg_right (hbd (t • z) htz) (norm_nonneg z)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := F)
    (f' := fun t : ℝ => ((fderiv ℝ σ (t • z) - ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) z) (C := δ * ‖z‖) hderiv hbound
  rw [hF0, hφ0, sub_zero] at hmvt
  simpa only [hF, one_smul, hφ, Pi.sub_apply, id_eq] using hmvt

lemma div_mul_two_mul {r δ K : ℝ} (hr : r ≠ 0) : (K / r) * (δ * (2 * r)) = 2 * δ * K := by
  field_simp

/-- The operator-norm bound for `smulRight`: `‖f.smulRight v‖ ≤ ‖f‖ * ‖v‖`.  (`smulRight` is a
bounded bilinear map, `ContinuousLinearMap.isBoundedBilinearMap_smulRight`.) -/
lemma norm_smulRight_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (v : E) : ‖f.smulRight v‖ ≤ ‖f‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖f w‖ * ‖v‖ ≤ (‖f‖ * ‖w‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ w) (norm_nonneg _)
    _ = (‖f‖ * ‖v‖) * ‖w‖ := by rw [mul_assoc, mul_assoc, mul_comm ‖w‖ ‖v‖]

/-- **The derivative bound for `ψ = z ↦ χ z • (σ z - z)`.**  This is the analytical core of the
spread: the product rule plus `‖fderiv χ‖ ≤ K/r`, `‖fderiv σ - 1‖ ≤ δ` on `‖z‖ < 2r` and
`χ = 0` on `‖z‖ ≥ 2r` give `‖fderiv ψ z‖ ≤ δ * (1 + 2*K)` everywhere. -/
theorem norm_fderiv_psi_le {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hσ0 : σ 0 = 0)
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y)) z‖
      ≤ δ * (1 + 2 * K) := by
  have hφfd : ∀ y : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => σ y - y)
        (fderiv ℝ σ y - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
    fun y => (hσfd y).sub (hasFDerivAt_id y)
  have hχfd : HasFDerivAt χ (fderiv ℝ χ z) z :=
    (hχsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y))
      (χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
        + (fderiv ℝ χ z).smulRight (σ z - z)) z := hχfd.smul (hφfd z)
  rw [hd.fderiv]
  rcases lt_or_ge ‖z‖ (2 * r) with hz | hz
  · have h1 : ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ :=
      hσball z hz
    have h2 : ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
        ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχnonneg z)]
      calc χ z * ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖
          ≤ 1 * δ := mul_le_mul (hχle z) h1 (norm_nonneg _) zero_le_one
        _ = δ := one_mul δ
    have hb : ‖σ z - z‖ ≤ δ * ‖z‖ :=
      norm_sub_le_of_close hn hr hσ0 hσfd hσball (z := z) hz.le
    have h3 : ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ ≤ 2 * δ * K :=
      calc ‖(fderiv ℝ χ z).smulRight (σ z - z)‖
          ≤ ‖fderiv ℝ χ z‖ * ‖σ z - z‖ := norm_smulRight_le _ _
        _ ≤ (K / r) * (δ * ‖z‖) :=
            mul_le_mul (hχbd z) hb (norm_nonneg _) (by positivity)
        _ ≤ (K / r) * (δ * (2 * r)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz.le (le_of_lt hδ))
              (by positivity)
        _ = 2 * δ * K := div_mul_two_mul (ne_of_gt hr)
    linarith [norm_add_le (χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin n)))) ((fderiv ℝ χ z).smulRight (σ z - z)), h2, h3]
  · rcases lt_or_eq_of_le hz with hzlt | hzeq
    · have hev : χ =ᶠ[nhds z] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hzlt] with y hy
        exact hχzero y hy.le
      have h1 : fderiv ℝ χ z = 0 := by
        rw [hev.fderiv_eq]
        simp
      have h2 : χ z = 0 := hχzero z hzlt.le
      have hs : (fderiv ℝ χ z).smulRight (σ z - z) = 0 := by
        rw [h1]
        ext w
        simp [ContinuousLinearMap.smulRight_apply]
      have hb1 : ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
          ≤ δ * (1 + 2 * K) := by
        rw [norm_smul, Real.norm_eq_abs, h2, abs_zero, zero_mul]
        positivity
      have hb2 : ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ = 0 := by
        rw [hs, norm_zero]
      calc ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
            + (fderiv ℝ χ z).smulRight (σ z - z)‖
          ≤ ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
            + ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ := norm_add_le _ _
        _ ≤ δ * (1 + 2 * K) + 0 := add_le_add hb1 hb2.le
        _ = δ * (1 + 2 * K) := add_zero _
    · have h2 : χ z = 0 := hχzero z hzeq.le
      have hb : ‖σ z - z‖ ≤ δ * (2 * r) := by
        have h := norm_sub_le_of_close hn hr hσ0 hσfd hσball (z := z) (le_of_eq hzeq.symm)
        rw [← hzeq] at h
        exact h
      have h3 : ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ ≤ 2 * δ * K :=
        calc ‖(fderiv ℝ χ z).smulRight (σ z - z)‖
            ≤ ‖fderiv ℝ χ z‖ * ‖σ z - z‖ := norm_smulRight_le _ _
          _ ≤ (K / r) * (δ * (2 * r)) :=
              mul_le_mul (hχbd z) hb (norm_nonneg _) (by positivity)
          _ = 2 * δ * K := div_mul_two_mul (ne_of_gt hr)
      have hB : ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ ≤ δ * (1 + 2 * K) :=
        calc ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ ≤ 2 * δ * K := h3
          _ ≤ δ * (1 + 2 * K) := by nlinarith [hδ]
      have hb1 : ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
          = 0 := by
        rw [norm_smul, Real.norm_eq_abs, h2, abs_zero, zero_mul]
      calc ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
            + (fderiv ℝ χ z).smulRight (σ z - z)‖
          ≤ ‖χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖
            + ‖(fderiv ℝ χ z).smulRight (σ z - z)‖ := norm_add_le _ _ 
        _ ≤ 0 + δ * (1 + 2 * K) := add_le_add hb1.le hB
        _ = δ * (1 + 2 * K) := zero_add _

/-- **`ψ = z ↦ χ z • (σ z - z)` is `δ*(1+2K)`-Lipschitz.**  Immediate from the mean value
inequality on the convex set `univ`, fed by `norm_fderiv_psi_le`. -/
theorem psi_lipschitz {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hσ0 : σ 0 = 0)
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖χ x • (σ x - x) - χ y • (σ y - y)‖ ≤ δ * (1 + 2 * K) * ‖x - y‖ := by
  have hdiff : ∀ z ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y)) z := by
    intro z _
    exact (hχsm.contDiffAt.differentiableAt (by simp)).smul
      ((hσfd z).differentiableAt.sub (differentiableAt_id))
  have hbd : ∀ z ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y)) z‖
        ≤ δ * (1 + 2 * K) :=
    fun z _ => norm_fderiv_psi_le hn hr hδ hK hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle z
  intro x y
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le hdiff hbd
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [norm_sub_rev] using h

/-- **Injectivity of `τ = id + ψ`.**  `fderiv τ z - 1 = fderiv ψ z`, so
`injOn_of_norm_fderiv_sub_id_le` applies with `κ = δ*(1+2K) < 1` on `s = univ`. -/
theorem tau_injective {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K) (hsmall : δ * (1 + 2 * K) < 1)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hσ0 : σ 0 = 0)
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1) :
    Function.Injective
      (fun z : EuclideanSpace ℝ (Fin n) => z + χ z • (σ z - z)) := by
  have hτfd : ∀ z : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y + χ y • (σ y - y))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
          + fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y)) z) z := by
    intro z
    have hψ : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y))
        (χ z • (fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
          + (fderiv ℝ χ z).smulRight (σ z - z)) z :=
      ((hχsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt).smul
        ((hσfd z).sub (hasFDerivAt_id z))
    have h2 := (hasFDerivAt_id z).add hψ
    rw [← hψ.fderiv] at h2
    exact h2
  have hτder : ∀ z : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => y + χ y • (σ y - y)) z
        - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
      = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => χ y • (σ y - y)) z := by
    intro z
    rw [(hτfd z).fderiv]
    abel
  have hinj := injOn_of_norm_fderiv_sub_id_le (f := fun y : EuclideanSpace ℝ (Fin n) =>
      y + χ y • (σ y - y)) (s := Set.univ) convex_univ hsmall
    (fun z _ => (hτfd z).differentiableAt)
    (fun z _ => by
      rw [hτder z]
      exact norm_fderiv_psi_le hn hr hδ hK hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle z)
  exact fun x y hxy => hinj (Set.mem_univ x) (Set.mem_univ y) hxy

/-- **Surjectivity of `τ = id + ψ`.**  For `y`, the map `z ↦ y - ψ z` is a
`(δ*(1+2K))`-contraction on the complete space `E`, so it has a fixed point `w`; then `τ w = y`. -/
theorem tau_surjective {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K) (hsmall : δ * (1 + 2 * K) < 1)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hσ0 : σ 0 = 0)
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1) :
    Function.Surjective (fun z : EuclideanSpace ℝ (Fin n) => z + χ z • (σ z - z)) := by
  have hc0 : (0 : ℝ) ≤ δ * (1 + 2 * K) := by positivity
  have hψlip : LipschitzWith ⟨δ * (1 + 2 * K), hc0⟩
      (fun z : EuclideanSpace ℝ (Fin n) => χ z • (σ z - z)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := psi_lipschitz hn hr hδ hK hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle x y
    rw [dist_eq_norm, dist_eq_norm]
    push_cast
    exact h
  intro y
  have hFlix : LipschitzWith ⟨δ * (1 + 2 * K), hc0⟩
      (fun z : EuclideanSpace ℝ (Fin n) => y - χ z • (σ z - z)) := by
    refine LipschitzWith.of_dist_le_mul fun x y' => ?_
    have hd : dist (y - χ x • (σ x - x)) (y - χ y' • (σ y' - y'))
        = dist (χ x • (σ x - x)) (χ y' • (σ y' - y')) := by
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : (y - χ x • (σ x - x)) - (y - χ y' • (σ y' - y'))
          = -((χ x • (σ x - x)) - (χ y' • (σ y' - y'))) := by abel
      rw [h1, norm_neg]
    rw [hd]
    exact hψlip.dist_le_mul x y'
  have hF : ContractingWith ⟨δ * (1 + 2 * K), hc0⟩
      (fun z : EuclideanSpace ℝ (Fin n) => y - χ z • (σ z - z)) :=
    ⟨by exact_mod_cast hsmall, hFlix⟩
  have hfin : edist (0 : EuclideanSpace ℝ (Fin n)) (y - χ 0 • (σ 0 - 0)) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  obtain ⟨w, hw, _⟩ := hF.exists_fixedPoint (0 : EuclideanSpace ℝ (Fin n)) hfin
  refine ⟨w, ?_⟩
  show w + χ w • (σ w - w) = y
  rw [add_comm]
  exact (sub_eq_iff_eq_add'.mp hw).symm

/-- **`τ = id + ψ` is `(1 - δ*(1+2K))`-expanding.**  Immediate from `psi_lipschitz`:
`‖x - y‖ = ‖(τ x - τ y) - (ψ x - ψ y)‖ ≤ ‖τ x - τ y‖ + δ*(1+2K)*‖x - y‖`. -/
theorem tau_expanding {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hσ0 : σ 0 = 0)
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1) :
    ∀ x y : EuclideanSpace ℝ (Fin n), (1 - δ * (1 + 2 * K)) * ‖x - y‖
      ≤ ‖(x + χ x • (σ x - x)) - (y + χ y • (σ y - y))‖ := by
  intro x y
  have hψ := psi_lipschitz hn hr hδ hK hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle x y
  have h1 : (x + χ x • (σ x - x)) - (y + χ y • (σ y - y))
      = (x - y) + (χ x • (σ x - x) - χ y • (σ y - y)) := by abel
  have h2 : ‖x - y‖ ≤ ‖(x + χ x • (σ x - x)) - (y + χ y • (σ y - y))‖
      + δ * (1 + 2 * K) * ‖x - y‖ := by
    have h3 : (x - y) = ((x + χ x • (σ x - x)) - (y + χ y • (σ y - y)))
        - (χ x • (σ x - x) - χ y • (σ y - y)) := by
      rw [h1]
      abel
    calc ‖x - y‖ = ‖((x + χ x • (σ x - x)) - (y + χ y • (σ y - y)))
            - (χ x • (σ x - x) - χ y • (σ y - y))‖ := by rw [h3]
      _ ≤ ‖(x + χ x • (σ x - x)) - (y + χ y • (σ y - y))‖
            + ‖χ x • (σ x - x) - χ y • (σ y - y)‖ := norm_sub_le _ _
      _ ≤ ‖(x + χ x • (σ x - x)) - (y + χ y • (σ y - y))‖
            + δ * (1 + 2 * K) * ‖x - y‖ := add_le_add le_rfl hψ
  linarith [h2]

/-- **The inverse of `τ = id + ψ` is `(1 - δ*(1+2K))⁻¹`-Lipschitz.**  From `tau_expanding`. -/
theorem tau_inverse_lipschitz {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K) (hsmall : δ * (1 + 2 * K) < 1)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hσ0 : σ 0 = 0)
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1)
    (e : EuclideanSpace ℝ (Fin n) ≃ EuclideanSpace ℝ (Fin n))
    (he : ∀ z : EuclideanSpace ℝ (Fin n), e z = z + χ z • (σ z - z)) :
    LipschitzWith ⟨(1 - δ * (1 + 2 * K))⁻¹, by rw [inv_nonneg]; linarith⟩ e.symm := by
  refine LipschitzWith.of_dist_le_mul fun y w => ?_
  rw [dist_eq_norm, dist_eq_norm]
  push_cast
  have h2 := tau_expanding hn hr hδ hK hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle
    (e.symm y) (e.symm w)
  rw [← he (e.symm y), ← he (e.symm w), Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  calc ‖e.symm y - e.symm w‖
      = (1 - δ * (1 + 2 * K))⁻¹
        * ((1 - δ * (1 + 2 * K)) * ‖e.symm y - e.symm w‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (by linarith : (1 - δ * (1 + 2 * K)) ≠ 0), one_mul]
    _ ≤ (1 - δ * (1 + 2 * K))⁻¹ * ‖y - w‖ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The spread, in the form actually used by the gluing step** (see
`wfmy/NOTES_rjl_SESSION4_DESIGN.md`).  The bump `χ` is an *input*: this avoids having to extract a
derivative bound for Mathlib's `ContDiffBump` (which its API does not provide); the caller chooses
`χ`, `δ` (the closeness of `σ`) and `K` (the derivative bound of `χ`) consistently.

`τ z = z + (χ z) • (σ z - z)`; the support of `χ` lies in `B (0, 2*r)`, on which `σ` is
`δ`-close to the identity, and `δ * (1 + 2*K) < 1`. -/
theorem spreadAxisFix_bump {n : ℕ} (hn : 1 ≤ n) {r δ K : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hK : 0 < K) (hsmall : δ * (1 + 2 * K) < 1)
    {σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hσfd : ∀ z : EuclideanSpace ℝ (Fin n), HasFDerivAt σ (fderiv ℝ σ z) z)
    (hσball : ∀ z, ‖z‖ < 2 * r →
      ‖fderiv ℝ σ z - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ δ)
    (hσax : ∀ t : ℝ, |t| ≤ 2 * r → σ (t • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))
      = t • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχone : ∀ z, ‖z‖ ≤ r → χ z = 1)
    (hχzero : ∀ z, 2 * r ≤ ‖z‖ → χ z = 0)
    (hχbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ K / r)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hχle : ∀ z, χ z ≤ 1) :
    ∃ τ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      τ.source = Set.univ ∧
      (∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ < r → τ z = σ z) ∧
      (∀ t : ℝ, τ (t • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))
        = t • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)) := by
  classical
  have hσ0 : σ 0 = 0 := by
    have h := hσax 0 (by rw [abs_zero]; linarith)
    simpa using h
  have hτinj : Function.Injective
      (fun z : EuclideanSpace ℝ (Fin n) => z + χ z • (σ z - z)) :=
    tau_injective hn hr hδ hK hsmall hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle
  have hτsurj : Function.Surjective
      (fun z : EuclideanSpace ℝ (Fin n) => z + χ z • (σ z - z)) :=
    tau_surjective hn hr hδ hK hsmall hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle
  set τf : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => z + χ z • (σ z - z) with hτf
  set e : EuclideanSpace ℝ (Fin n) ≃ EuclideanSpace ℝ (Fin n) :=
    Equiv.ofBijective τf ⟨hτinj, hτsurj⟩ with he
  have heapp : ∀ z : EuclideanSpace ℝ (Fin n), e z = z + χ z • (σ z - z) := fun z => rfl
  have hinv : LipschitzWith
      ⟨(1 - δ * (1 + 2 * K))⁻¹, by rw [inv_nonneg]; linarith⟩ e.symm :=
    tau_inverse_lipschitz hn hr hδ hK hsmall hσ0 hσfd hσball hχsm hχzero hχbd hχnonneg hχle
      e heapp
  have hτcont : Continuous τf := by
    rw [continuous_iff_continuousAt]
    intro z
    exact ((hasFDerivAt_id z).add
      (((hχsm.contDiffAt.differentiableAt (by simp)).hasFDerivAt).smul
        ((hσfd z).sub (hasFDerivAt_id z)))).continuousAt
  refine ⟨(show OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) from
    { toFun := τf
      invFun := ⇑e.symm
      source := Set.univ
      target := Set.univ
      map_source' := fun z _ => Set.mem_univ _
      map_target' := fun y _ => Set.mem_univ _
      left_inv' := fun z _ => Equiv.symm_apply_apply e z
      right_inv' := fun y _ => Equiv.apply_symm_apply e y
      open_source := isOpen_univ
      open_target := isOpen_univ
      continuousOn_toFun := hτcont.continuousOn
      continuousOn_invFun := hinv.continuous.continuousOn }), ?_, ?_, ?_⟩
  · rfl
  · intro z hz
    have hχ1 : χ z = 1 := hχone z hz.le
    show z + χ z • (σ z - z) = σ z
    rw [hχ1, one_smul]
    abel
  · intro t
    have hnorm : ‖t • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)‖ = |t| := by
      rw [norm_smul, PiLp.norm_single]
      simp only [Real.norm_eq_abs, abs_one, mul_one]
    show t • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
      + χ (t • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
        • (σ (t • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
            - t • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
      = t • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
    by_cases h : |t| ≤ 2 * r
    · rw [hσax t h, sub_self, smul_zero, add_zero]
    · rw [hχzero _ (by rw [hnorm]; exact le_of_lt (not_le.mp h)), zero_smul, add_zero]

end Work.Routing
