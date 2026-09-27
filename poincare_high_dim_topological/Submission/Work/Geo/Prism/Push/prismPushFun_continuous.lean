import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.Geo.Prism.Stretch
import Submission.Work.Geo.Prism.Theta
import Submission.Work.PL.Defs

namespace Work.Geo.Prism.Push

set_option linter.unusedVariables false

open Set Metric Filter
open scoped Topology
open Classical

/-! Auxiliary lemmas for `prismPushFun_continuous`. -/

/-- `len F φ γ` is nonnegative. -/
theorem len_nonneg_aux {b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ) (z : PL.E b) :
    0 ≤ Work.Geo.Prism.len F φ γ z := by
  unfold Work.Geo.Prism.len
  split_ifs with h
  · exact le_max_left _ _
  · exact le_refl 0

/-- `lam η` is nonnegative. -/
theorem lam_nonneg_aux {a : ℕ} (η : ℝ) (y : PL.E a) : 0 ≤ Work.Geo.Prism.lam η y := by
  unfold Work.Geo.Prism.lam
  exact le_max_left _ _

/-- `lam η` is continuous (no hypothesis on `η`). -/
theorem lam_continuous_aux {a : ℕ} (η : ℝ) : Continuous (Work.Geo.Prism.lam (a := a) η) := by
  unfold Work.Geo.Prism.lam
  exact continuous_const.max (continuous_const.sub (continuous_norm.div_const η))

/-- `len F φ γ` is continuous when `F` is closed and `φ = γ` on `frontier F`: it is the
gluing of `max 0 (γ - φ)` on `F` and `0` off `F`, and the two agree on the frontier. -/
theorem len_continuous_aux {b : ℕ} {F : Set (PL.E b)} (hF : IsClosed F)
    {φ γ : PL.E b → ℝ} (hφ : Continuous φ) (hγ : Continuous γ)
    (hfr : ∀ z ∈ frontier F, φ z = γ z) :
    Continuous (Work.Geo.Prism.len F φ γ) := by
  have heq : Work.Geo.Prism.len F φ γ
      = F.piecewise (fun z => max 0 (γ z - φ z)) (fun _ => 0) := by
    funext z
    by_cases hz : z ∈ F <;> simp [Work.Geo.Prism.len, Set.piecewise, hz]
  rw [heq]
  refine Continuous.piecewise (fun z hz => ?_) (continuous_const.max (hγ.sub hφ)) continuous_const
  rw [← hfr z hz, sub_self, max_eq_left le_rfl]

/-- Continuity at a point of `y ↦ prismTheta (s y) (ℓ y) δ (t y)` for `ℓ ≥ 0` and `δ > 0`.
Where `ℓ x > 0` both elementary stretches of `prismTheta` have distinct endpoints, so
`str_continuousAt` applies twice; where `ℓ x = 0` we squeeze using `prismTheta_dist_le`,
which bounds the displacement by `2 ℓ`. -/
theorem prismTheta_continuousAt_aux {X : Type*} [TopologicalSpace X]
    {s ℓ t : X → ℝ} {x : X} (hs : ContinuousAt s x) (hℓ : ContinuousAt ℓ x)
    (ht : ContinuousAt t x) (hℓnn : ∀ y, 0 ≤ ℓ y) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousAt (fun y => Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y)) x := by
  rcases eq_or_lt_of_le (hℓnn x) with hzero | hpos
  · -- `ℓ x = 0`: squeeze.
    have hval : Work.Geo.Prism.prismTheta (s x) (ℓ x) δ (t x) = t x := by
      rw [← hzero, Work.Geo.Prism.prismTheta_zero (le_of_lt hδ)]
    have hlim : Tendsto (fun y => Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y))
        (𝓝 x) (𝓝 (t x)) := by
      have hdiff : Tendsto (fun y => t y - t x) (𝓝 x) (𝓝 0) := by
        have h : Tendsto (fun y => t y - t x) (𝓝 x) (𝓝 (t x - t x)) :=
          Filter.Tendsto.sub ht tendsto_const_nhds
        simpa using h
      have h2 : Tendsto (fun y => |t y - t x|) (𝓝 x) (𝓝 0) := by
        simpa using hdiff.abs
      have h1 : Tendsto (fun y => 2 * ℓ y) (𝓝 x) (𝓝 0) := by
        have h : Tendsto (fun y => 2 * ℓ y) (𝓝 x) (𝓝 (2 * ℓ x)) := hℓ.const_mul 2
        rw [← hzero] at h
        simpa using h
      have hsum : Tendsto (fun y => 2 * ℓ y + |t y - t x|) (𝓝 x) (𝓝 0) := by
        simpa using h1.add h2
      have hsq : Tendsto (fun y => |Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y) - t x|)
          (𝓝 x) (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
          (fun y => abs_nonneg _) (fun y => ?_)
        calc |Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y) - t x|
            ≤ |Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y) - t y| + |t y - t x| :=
              abs_sub_le _ _ _
          _ ≤ 2 * ℓ y + |t y - t x| := by
              have h : |Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y) - t y| ≤ 2 * ℓ y :=
                Work.Geo.Prism.prismTheta_dist_le (hℓnn y) hδ
              linarith
      have h3 : Tendsto (fun y => Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y) - t x)
          (𝓝 x) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa only [Real.norm_eq_abs] using hsq
      have h4 : Tendsto (fun y => Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y))
          (𝓝 x) (𝓝 (t x)) := by
        have hc : Tendsto (fun _ : X => t x) (𝓝 x) (𝓝 (t x)) := tendsto_const_nhds
        have h := h3.add hc
        simpa using h
      exact h4
    change Tendsto (fun y => Work.Geo.Prism.prismTheta (s y) (ℓ y) δ (t y))
      (𝓝 x) (𝓝 (Work.Geo.Prism.prismTheta (s x) (ℓ x) δ (t x)))
    rw [hval]
    exact hlim
  · -- `ℓ x > 0`: both stretches are non-degenerate.
    have hμ : 0 < min δ (ℓ x) := lt_min hδ hpos
    have hmin : ContinuousAt (fun y => min δ (ℓ y)) x := continuousAt_const.min hℓ
    have hinner : ContinuousAt
        (fun y => Work.Geo.Prism.str (s y) (s y + min δ (ℓ y)) (s y + ℓ y) (t y)) x := by
      refine Work.Geo.Prism.str_continuousAt hs (hs.add hmin) (hs.add hℓ) ht ?_
      intro h
      linarith [hμ]
    have houter : ContinuousAt
        (fun y => Work.Geo.Prism.str (s y + ℓ y) (s y + 2 * ℓ y) (s y + ℓ y + min δ (ℓ y))
          (Work.Geo.Prism.str (s y) (s y + min δ (ℓ y)) (s y + ℓ y) (t y))) x := by
      refine Work.Geo.Prism.str_continuousAt (hs.add hℓ) (hs.add (hℓ.const_mul 2))
        ((hs.add hℓ).add hmin) hinner ?_
      intro h
      linarith [hpos]
    simpa only [Work.Geo.Prism.prismTheta] using houter

/-- The explicit prism push `prismPushFun F φ γ η δ` of `Pr a b` is continuous.  Its parameters are continuous: `s z = φ z`, `ℓ y z = lam η y * len F φ γ z` with `lam η y = max 0 (1 - ‖y‖/η)` and `len F φ γ z = max 0 (γ z - φ z)` on `F` and `0` off `F` (continuous because `φ = γ` on `frontier F`), and `δ > 0`; note `ℓ ≥ 0`.  Suggested route: reduce to continuity of `(y,z,t) ↦ prismTheta (φ z) (lam η y * len F φ γ z) δ t`, and split on `ℓ > 0` vs `ℓ = 0`: where `ℓ > 0` both elementary stretches in `prismTheta` have distinct endpoints (`min δ ℓ > 0` and `ℓ > 0`) so `Work.Geo.Prism.str_continuousAt` applies twice; where `ℓ = 0` use the uniform bound `Work.Geo.Prism.prismTheta_dist_le` (`|prismTheta s ℓ δ t - t| ≤ 2 * ℓ`) together with `ℓ → 0` to squeeze towards `(y,z,t) ↦ (y,z,t)`, which is the value there (`Work.Geo.Prism.prismTheta_zero`).  Continuity of `len F φ γ` may be proved inline if `Geo/Prism/Len/len_continuous` is not yet available. -/
theorem prismPushFun_continuous {a b : ℕ} {F : Set (PL.E b)} (hF : IsClosed F)
    {φ γ : PL.E b → ℝ} (hφ : Continuous φ) (hγ : Continuous γ)
    (hfr : ∀ z ∈ frontier F, φ z = γ z) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    Continuous (Work.Geo.Prism.prismPushFun (a := a) F φ γ η δ) := by
  have hlen : Continuous (Work.Geo.Prism.len F φ γ) := len_continuous_aux hF hφ hγ hfr
  have hlam : Continuous (Work.Geo.Prism.lam (a := a) η) := lam_continuous_aux η
  have hL : Continuous
      (fun x : Pr a b => lam η x.1 * Work.Geo.Prism.len F φ γ x.2.1) :=
    (hlam.comp continuous_fst).mul (hlen.comp continuous_snd.fst)
  have hG : Continuous (fun x : Pr a b =>
      prismTheta (φ x.2.1) (lam η x.1 * Work.Geo.Prism.len F φ γ x.2.1) δ x.2.2) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact prismTheta_continuousAt_aux (hφ.comp continuous_snd.fst).continuousAt
      hL.continuousAt continuous_snd.snd.continuousAt
      (fun y => mul_nonneg (lam_nonneg_aux η y.1) (len_nonneg_aux F φ γ y.2.1)) hδ
  refine Continuous.prodMk continuous_fst ?_
  exact Continuous.prodMk continuous_snd.fst hG

end Work.Geo.Prism.Push
