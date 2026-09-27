import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.Geo.Prism.Stretch
import Submission.Work.Geo.Prism.Theta
import Submission.Work.PL.Defs
import Submission.Work.Geo.Prism.Push.prismPushFun_continuous

namespace Work.Geo.Prism.Push

open Set Metric Filter
open scoped Topology
open Classical

set_option linter.unusedVariables false

/-! ## Auxiliary lemmas about `prismThetaInv`

`prismThetaInv s 0 δ` is the identity (`prismThetaInv_zero_aux`), and for `ℓ ≥ 0`, `δ > 0`
its displacement is bounded by `2ℓ` (`prismThetaInv_dist_le_aux`): the two elementary
stretches it is built from have amplitudes `ℓ - min δ ℓ` and `min δ ℓ - ℓ`. -/

/-- For `ℓ = 0` the inverse prism stretch is the identity. -/
theorem prismThetaInv_zero_aux {s δ t : ℝ} (hδ : 0 < δ) :
    Work.Geo.Prism.prismThetaInv s 0 δ t = t := by
  simp only [Work.Geo.Prism.prismThetaInv, min_eq_right (le_of_lt hδ), add_zero, mul_zero,
    Work.Geo.Prism.str_self_of_eq]

/-- The displacement of `prismThetaInv` is at most `2ℓ` (for `ℓ ≥ 0`, `δ > 0`). -/
theorem prismThetaInv_dist_le_aux (s ℓ δ t : ℝ) (hℓ : 0 ≤ ℓ) (hδ : 0 < δ) :
    |Work.Geo.Prism.prismThetaInv s ℓ δ t - t| ≤ 2 * ℓ := by
  have hμ : min δ ℓ ≤ ℓ := min_le_right _ _
  have hμ0 : 0 ≤ min δ ℓ := le_min (le_of_lt hδ) hℓ
  have h1 : |Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t - t| ≤
      ℓ - min δ ℓ := by
    refine le_trans (Work.Geo.Prism.str_dist_le _ _ _ _) ?_
    rw [show (s + 2 * ℓ) - (s + ℓ + min δ ℓ) = ℓ - min δ ℓ by ring,
      abs_of_nonneg (by linarith : 0 ≤ ℓ - min δ ℓ)]
  have h2 : |Work.Geo.Prism.str s (s + ℓ) (s + min δ ℓ)
      (Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t)
      - Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t| ≤ ℓ - min δ ℓ := by
    refine le_trans (Work.Geo.Prism.str_dist_le _ _ _ _) ?_
    rw [show (s + min δ ℓ) - (s + ℓ) = min δ ℓ - ℓ by ring,
      abs_of_nonpos (by linarith : min δ ℓ - ℓ ≤ 0)]
    linarith
  unfold Work.Geo.Prism.prismThetaInv
  calc |Work.Geo.Prism.str s (s + ℓ) (s + min δ ℓ)
          (Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t) - t|
      ≤ |Work.Geo.Prism.str s (s + ℓ) (s + min δ ℓ)
            (Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t)
          - Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t|
        + |Work.Geo.Prism.str (s + ℓ) (s + ℓ + min δ ℓ) (s + 2 * ℓ) t - t| :=
          abs_sub_le _ _ _
    _ ≤ (ℓ - min δ ℓ) + (ℓ - min δ ℓ) := add_le_add h2 h1
    _ ≤ 2 * ℓ := by linarith

/-- Continuity at a point of `y ↦ prismThetaInv (s y) (ℓ y) δ (t y)` for `ℓ ≥ 0`, `δ > 0`.
Where `ℓ x > 0` both elementary stretches of `prismThetaInv` have distinct endpoints
(`min δ (ℓ x) > 0` and `ℓ x > 0`), so `str_continuousAt` applies twice.  Where `ℓ x = 0`
the value is `t x` (`prismThetaInv_zero_aux`) and we squeeze, using
`prismThetaInv_dist_le_aux`, which bounds the displacement by `2 ℓ y → 0`. -/
theorem prismThetaInv_continuousAt_aux {X : Type*} [TopologicalSpace X]
    {s ℓ t : X → ℝ} {x : X} (hs : ContinuousAt s x) (hℓ : ContinuousAt ℓ x)
    (ht : ContinuousAt t x) (hℓnn : ∀ y, 0 ≤ ℓ y) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousAt (fun y => Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y)) x := by
  rcases eq_or_lt_of_le (hℓnn x) with hzero | hpos
  · -- `ℓ x = 0`: the value is `t x`, and the displacement is at most `2 * ℓ y`.
    have hval : Work.Geo.Prism.prismThetaInv (s x) (ℓ x) δ (t x) = t x := by
      rw [← hzero]; exact prismThetaInv_zero_aux hδ
    have hlim : Tendsto (fun y => Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y))
        (𝓝 x) (𝓝 (t x)) := by
      have hdiff : Tendsto (fun y => t y - t x) (𝓝 x) (𝓝 0) := by
        have h : Tendsto (fun y => t y - t x) (𝓝 x) (𝓝 (t x - t x)) :=
          Filter.Tendsto.sub ht tendsto_const_nhds
        simpa using h
      have ht2 : Tendsto (fun y => |t y - t x|) (𝓝 x) (𝓝 0) := by simpa using hdiff.abs
      have h1 : Tendsto (fun y => 2 * ℓ y) (𝓝 x) (𝓝 0) := by
        have h : Tendsto (fun y => 2 * ℓ y) (𝓝 x) (𝓝 (2 * ℓ x)) := hℓ.const_mul 2
        rw [← hzero] at h
        simpa using h
      have hsum : Tendsto (fun y => 2 * ℓ y + |t y - t x|) (𝓝 x) (𝓝 0) := by
        simpa using h1.add ht2
      have hsq : Tendsto (fun y => |Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y) - t x|)
          (𝓝 x) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
          (fun y => abs_nonneg _) (fun y => ?_)
        calc |Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y) - t x|
            ≤ |Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y) - t y| + |t y - t x| :=
              abs_sub_le _ _ _
          _ ≤ 2 * ℓ y + |t y - t x| := by
              have h := prismThetaInv_dist_le_aux (s y) (ℓ y) δ (t y) (hℓnn y) hδ
              linarith
      have h3 : Tendsto (fun y => Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y) - t x)
          (𝓝 x) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa only [Real.norm_eq_abs] using hsq
      have h4 : Tendsto (fun y => Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y))
          (𝓝 x) (𝓝 (t x)) := by
        have hc : Tendsto (fun _ : X => t x) (𝓝 x) (𝓝 (t x)) := tendsto_const_nhds
        have h := h3.add hc
        simpa using h
      exact h4
    change Tendsto (fun y => Work.Geo.Prism.prismThetaInv (s y) (ℓ y) δ (t y)) (𝓝 x)
      (𝓝 (Work.Geo.Prism.prismThetaInv (s x) (ℓ x) δ (t x)))
    rw [hval]
    exact hlim
  · -- `ℓ x > 0`: both elementary stretches are non-degenerate.
    have hμ : 0 < min δ (ℓ x) := lt_min hδ hpos
    have hmin : ContinuousAt (fun y => min δ (ℓ y)) x := continuousAt_const.min hℓ
    have hinner : ContinuousAt
        (fun y => Work.Geo.Prism.str (s y + ℓ y) (s y + ℓ y + min δ (ℓ y)) (s y + 2 * ℓ y)
          (t y)) x := by
      refine Work.Geo.Prism.str_continuousAt (hs.add hℓ) ((hs.add hℓ).add hmin)
        (hs.add (hℓ.const_mul 2)) ht ?_
      intro h
      linarith [hμ]
    have houter : ContinuousAt
        (fun y => Work.Geo.Prism.str (s y) (s y + ℓ y) (s y + min δ (ℓ y))
          (Work.Geo.Prism.str (s y + ℓ y) (s y + ℓ y + min δ (ℓ y)) (s y + 2 * ℓ y)
            (t y))) x := by
      refine Work.Geo.Prism.str_continuousAt hs (hs.add hℓ) (hs.add hmin) hinner ?_
      intro h
      linarith [hpos]
    simpa only [Work.Geo.Prism.prismThetaInv] using houter

/-! ## The inverse is a two-sided inverse of the prism push

These need no hypothesis on `F`, `φ`, `γ`, `η`: the length `ℓ = lam η y * len F φ γ z` is always
nonnegative, which is all `prismThetaInv_prismTheta`/`prismTheta_prismThetaInv` ask for (besides
`δ > 0`). -/

/-- `prismPushInvFun` is a left inverse of `prismPushFun`. -/
theorem prismPushInvFun_prismPushFun {a b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ)
    {η δ : ℝ} (hδ : 0 < δ) (x : Pr a b) :
    Work.Geo.Prism.prismPushInvFun F φ γ η δ (Work.Geo.Prism.prismPushFun F φ γ η δ x) = x := by
  rcases x with ⟨y, z, t⟩
  simp only [Work.Geo.Prism.prismPushInvFun, Work.Geo.Prism.prismPushFun]
  exact Prod.ext rfl (Prod.ext rfl (Work.Geo.Prism.prismThetaInv_prismTheta
    (mul_nonneg (lam_nonneg_aux η y) (len_nonneg_aux F φ γ z)) hδ))

/-- `prismPushInvFun` is a right inverse of `prismPushFun`. -/
theorem prismPushFun_prismPushInvFun {a b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ)
    {η δ : ℝ} (hδ : 0 < δ) (x : Pr a b) :
    Work.Geo.Prism.prismPushFun F φ γ η δ (Work.Geo.Prism.prismPushInvFun F φ γ η δ x) = x := by
  rcases x with ⟨y, z, t⟩
  simp only [Work.Geo.Prism.prismPushInvFun, Work.Geo.Prism.prismPushFun]
  exact Prod.ext rfl (Prod.ext rfl (Work.Geo.Prism.prismTheta_prismThetaInv
    (mul_nonneg (lam_nonneg_aux η y) (len_nonneg_aux F φ γ z)) hδ))

/-- The explicit inverse `prismPushInvFun F φ γ η δ` of the prism push is continuous; same argument as `prismPushFun_continuous` (split on `ℓ = lam η y * len F φ γ z ≥ 0`; use `Work.Geo.Prism.str_continuousAt` where `ℓ > 0`, and where `ℓ = 0` use that `prismThetaInv` is the identity there and satisfies the same bound `|prismThetaInv s ℓ δ t - t| ≤ 2 * ℓ` for `ℓ ≥ 0`, `δ > 0` — its two stretches have amplitudes `ℓ - min δ ℓ` and `min δ ℓ - ℓ`). -/
theorem prismPushInvFun_continuous {a b : ℕ} {F : Set (PL.E b)} (hF : IsClosed F)
    {φ γ : PL.E b → ℝ} (hφ : Continuous φ) (hγ : Continuous γ)
    (hfr : ∀ z ∈ frontier F, φ z = γ z) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    Continuous (Work.Geo.Prism.prismPushInvFun (a := a) F φ γ η δ) := by
  have hlen : Continuous (Work.Geo.Prism.len F φ γ) := len_continuous_aux hF hφ hγ hfr
  have hlam : Continuous (Work.Geo.Prism.lam (a := a) η) := lam_continuous_aux η
  have hL : Continuous
      (fun x : Pr a b => Work.Geo.Prism.lam η x.1 * Work.Geo.Prism.len F φ γ x.2.1) :=
    (hlam.comp continuous_fst).mul (hlen.comp continuous_snd.fst)
  have hG : Continuous (fun x : Pr a b => Work.Geo.Prism.prismThetaInv (φ x.2.1)
      (Work.Geo.Prism.lam η x.1 * Work.Geo.Prism.len F φ γ x.2.1) δ x.2.2) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact prismThetaInv_continuousAt_aux (hφ.comp continuous_snd.fst).continuousAt
      hL.continuousAt continuous_snd.snd.continuousAt
      (fun y => mul_nonneg (lam_nonneg_aux η y.1) (len_nonneg_aux F φ γ y.2.1)) hδ
  refine Continuous.prodMk continuous_fst ?_
  exact Continuous.prodMk continuous_snd.fst hG

end Work.Geo.Prism.Push
