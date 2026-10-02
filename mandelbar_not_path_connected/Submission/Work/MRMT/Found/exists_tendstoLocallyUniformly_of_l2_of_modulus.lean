/-
Work.MRMT.Found — the Ascoli–Arzelà style "locally uniform limit" lemma for the mandelbar drive.

Given a sequence `u : ℕ → ℂ → ℂ` which
* is uniformly equicontinuous, with a modulus `ω` that tends to `0` at `0⁺`
  (`hmod`, `hω`), and
* is `L²`-Cauchy on every compact set (`hc`),

we construct a continuous limit `u₀` which is the locally uniform limit of `u`.

The proof has three steps:

* `exists_modulus_lt_of_tendsto_nhdsWithin`: read off from `hω` a radius on which `ω` is small;
* `cauchySeq_of_l2_of_modulus`: the `L²` bound on a small closed ball around a point `z` forces
  some point `w` of that ball to have `‖u m w - u n w‖` small (otherwise the integral would be
  too large), and the modulus of continuity then bounds `‖u m z - u n z‖`.  Hence the sequence
  `n ↦ u n z` is Cauchy, and `u₀` is defined as the pointwise limit;
* the modulus bound passes to the limit `u₀`, which is therefore continuous, and on a fixed
  compact ball around any point the pointwise convergence upgrades to uniform convergence by
  equicontinuity and a finite `δ`-net.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology

namespace Work.MRMT.Found

/-- From `ω → 0` along `𝓝[>] 0` one gets a radius `δ ≤ 1` on which `ω` is `< ε`. -/
theorem exists_modulus_lt_of_tendsto_nhdsWithin {ω : ℝ → ℝ}
    (hω : Filter.Tendsto ω (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ → ω t < ε := by
  have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), ω t ∈ Set.Iio ε :=
    hω (Iio_mem_nhds hε)
  rw [eventually_nhdsWithin_iff] at h1
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδpos, hδ⟩ := h1
  refine ⟨min δ 1, lt_min hδpos one_pos, min_le_right _ _, fun t ht0 htlt => ?_⟩
  have htd : dist t (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_lt_of_le htlt (min_le_left _ _)
  exact hδ htd ht0

/-- If the `L²`-norm of `f` over a finite-measure set `s` is strictly smaller than
`c² * volume s`, then `f` is bounded by `c` somewhere on `s`. -/
theorem exists_norm_le_of_setIntegral_sq_lt {f : ℂ → ℂ} {s : Set ℂ} {c : ℝ}
    (hs : MeasurableSet s) (hc : 0 < c) (hfin : (volume : Measure ℂ) s ≠ ⊤)
    (hint : IntegrableOn (fun z => ‖f z‖ ^ 2) s (volume : Measure ℂ))
    (hlt : ∫ z in s, ‖f z‖ ^ 2 < c ^ 2 * ((volume : Measure ℂ) s).toReal) :
    ∃ w ∈ s, ‖f w‖ ≤ c := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hconst : Integrable (fun _ : ℂ => c^2) ((volume : Measure ℂ).restrict s) :=
    integrableOn_const (C := c^2) hfin (by simp)
  have hae : (fun _ : ℂ => c^2) ≤ᵐ[((volume : Measure ℂ).restrict s)] (fun z => ‖f z‖ ^ 2) := by
    filter_upwards [ae_restrict_mem hs] with z hz
    have h1 : c < ‖f z‖ := hcon z hz
    nlinarith [norm_nonneg (f z)]
  have hmono : ∫ z in s, (c^2) ∂(volume : Measure ℂ)
      ≤ ∫ z in s, ‖f z‖ ^ 2 ∂(volume : Measure ℂ) :=
    integral_mono_ae hconst hint hae
  have hval : ∫ z in s, (c^2) ∂(volume : Measure ℂ) = c^2 * ((volume : Measure ℂ) s).toReal := by
    rw [setIntegral_const, Measure.real_def, smul_eq_mul]
    ring
  rw [hval] at hmono
  linarith

/-- The pointwise limit of the `L²` bound: for every `z` the sequence `n ↦ u n z` is Cauchy. -/
theorem cauchySeq_of_l2_of_modulus {u : ℕ → ℂ → ℂ} {ω : ℝ → ℝ}
    (hω : Filter.Tendsto ω (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hmod : ∀ n z z', ‖z - z'‖ ≤ 1 → ‖u n z - u n z'‖ ≤ ω ‖z - z'‖)
    (hc : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      IntegrableOn (fun z => ‖u n z - u m z‖^2) K (volume : Measure ℂ) ∧
      ∫ z in K, ‖u n z - u m z‖^2 < ε) (z : ℂ) :
    CauchySeq (fun n => u n z) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδle, hδ⟩ :=
    exists_modulus_lt_of_tendsto_nhdsWithin hω (show 0 < ε/4 by linarith)
  set R : ℝ := δ/4 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  set A : Set ℂ := Metric.closedBall z R with hAdef
  have hAc : IsCompact A := isCompact_closedBall z R
  have hs : MeasurableSet A := hAc.isClosed.measurableSet
  have hfin : (volume : Measure ℂ) A ≠ ⊤ := hAc.measure_lt_top.ne
  have hpos : 0 < (volume : Measure ℂ) A :=
    Metric.measure_closedBall_pos (volume : Measure ℂ) z hRpos
  set c₀ : ℝ := (ε/4)^2 * ((volume : Measure ℂ) A).toReal with hcdef
  have hcpos : 0 < c₀ := by
    rw [hcdef]
    exact mul_pos (pow_pos (by linarith : (0:ℝ) < ε/4) 2) (ENNReal.toReal_pos hpos.ne' hfin)
  obtain ⟨N, hN⟩ := hc A hAc c₀ hcpos
  refine ⟨N, fun m hm n hn => ?_⟩
  obtain ⟨hint, hlt⟩ := hN m n hm hn
  have hlt' : ∫ z in A, ‖u m z - u n z‖ ^ 2 < (ε/4) ^ 2 * (volume A).toReal := by
    rw [hcdef] at hlt; exact hlt
  obtain ⟨w, hwA, hwle⟩ :=
    exists_norm_le_of_setIntegral_sq_lt (f := fun z => u m z - u n z) (s := A) (c := ε/4)
      hs (by linarith) hfin hint hlt'
  have hzw : dist z w ≤ R := by
    rw [hAdef] at hwA
    rw [dist_comm]
    exact Metric.mem_closedBall.mp hwA
  have hzwδ : dist z w < δ := by rw [hRdef] at hzw; linarith
  have hling : ‖z - w‖ ≤ 1 := by rw [← dist_eq_norm]; exact le_of_lt (lt_of_lt_of_le hzwδ hδle)
  rcases eq_or_ne z w with h | h
  · rw [h]
    rw [dist_eq_norm]
    linarith
  · have hzd : 0 < dist z w := dist_pos.mpr h
    have hωzw : ω (dist z w) < ε/4 := hδ (dist z w) hzd hzwδ
    have hmodzwn : ∀ n, ‖u n z - u n w‖ ≤ ω (dist z w) := fun n => by
      simpa [dist_eq_norm] using hmod n z w hling
    have e1 : dist (u m z) (u m w) ≤ ω (dist z w) := by rw [dist_eq_norm]; exact hmodzwn m
    have e2 : dist (u m w) (u n w) ≤ ε/4 := by rw [dist_eq_norm]; exact hwle
    have e3 : dist (u n w) (u n z) ≤ ω (dist z w) := by
      rw [dist_eq_norm, norm_sub_rev]; exact hmodzwn n
    have step := dist_triangle4 (u m z) (u m w) (u n w) (u n z)
    linarith

/-- **Ascoli–Arzelà step for the mandelbar drive.** An `L²`-Cauchy sequence of uniformly
equicontinuous functions on `ℂ` converges locally uniformly to a continuous limit. -/
theorem exists_tendstoLocallyUniformly_of_l2_of_modulus {u : ℕ → ℂ → ℂ} {ω : ℝ → ℝ}
    (hω : Filter.Tendsto ω (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hmod : ∀ n z z', ‖z - z'‖ ≤ 1 → ‖u n z - u n z'‖ ≤ ω ‖z - z'‖)
    (hc : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      MeasureTheory.IntegrableOn (fun z => ‖u n z - u m z‖ ^ 2) K (MeasureTheory.volume : MeasureTheory.Measure ℂ) ∧
      ∫ z in K, ‖u n z - u m z‖ ^ 2 < ε) :
    ∃ u₀ : ℂ → ℂ, Continuous u₀ ∧ TendstoLocallyUniformly u u₀ Filter.atTop := by
  have hcauchy : ∀ z, CauchySeq (fun n => u n z) :=
    fun z => cauchySeq_of_l2_of_modulus hω hmod hc z
  choose u₀ hu₀ using fun z => cauchySeq_tendsto_of_complete (hcauchy z)
  -- the modulus bound passes to the limit
  have hu₀mod : ∀ z z', ‖z - z'‖ ≤ 1 → ‖u₀ z - u₀ z'‖ ≤ ω ‖z - z'‖ := by
    intro z z' hz
    exact le_of_tendsto' ((hu₀ z).sub (hu₀ z')).norm (fun n => hmod n z z' hz)
  refine ⟨u₀, ?_, ?_⟩
  · -- continuity of `u₀`
    rw [Metric.continuous_iff]
    intro z ε hε
    obtain ⟨δ, hδpos, hδle, hδ⟩ := exists_modulus_lt_of_tendsto_nhdsWithin hω hε
    refine ⟨δ, hδpos, fun z' hz' => ?_⟩
    rcases eq_or_ne z' z with h | h
    · subst h
      simpa using hε
    · have hpos : 0 < ‖z' - z‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact h
      have hlt : ‖z' - z‖ < δ := by rw [← dist_eq_norm]; exact hz'
      have h1 : ‖u₀ z' - u₀ z‖ ≤ ω ‖z' - z‖ :=
        hu₀mod z' z (le_of_lt (lt_of_lt_of_le hlt hδle))
      rw [dist_eq_norm]
      linarith [h1, hδ ‖z' - z‖ hpos hlt]
  · -- local uniform convergence
    refine tendstoLocallyUniformly_of_forall_exists_nhds (fun z₀ => ?_)
    refine ⟨Metric.closedBall z₀ 1, Metric.closedBall_mem_nhds z₀ one_pos, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδle, hδ⟩ :=
      exists_modulus_lt_of_tendsto_nhdsWithin hω (show 0 < ε/3 by linarith)
    have hA : IsCompact (Metric.closedBall z₀ (1:ℝ)) := isCompact_closedBall z₀ 1
    obtain ⟨t, htfin, htsub⟩ := Metric.totallyBounded_iff.mp hA.totallyBounded δ hδpos
    -- on the finite `δ`-net the convergence is eventually good
    have hev : ∀ᶠ n in atTop, ∀ y ∈ t, dist (u₀ y) (u n y) < ε/3 := by
      refine htfin.eventually_all.mpr (fun y _ => ?_)
      exact ((hu₀ y).eventually (Metric.ball_mem_nhds (u₀ y) (ε := ε/3) (by linarith))).mono
        (fun n hn => by simpa [dist_comm] using Metric.mem_ball.mp hn)
    refine hev.mono (fun n hn => ?_)
    intro x hx
    obtain ⟨y, hyt, hxy⟩ : ∃ y ∈ t, x ∈ Metric.ball y δ := by
      simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using htsub hx
    have hdist1 : dist x y < 1 := lt_of_lt_of_le hxy hδle
    rcases eq_or_ne x y with h | h
    · rw [h]
      exact lt_trans (hn y hyt) (by linarith)
    · have hpos : 0 < dist x y := dist_pos.mpr h
      have hxy1 : ‖x - y‖ ≤ 1 := by rw [← dist_eq_norm]; exact le_of_lt hdist1
      have e1 : dist (u₀ x) (u₀ y) ≤ ω (dist x y) := by
        simpa [dist_eq_norm] using hu₀mod x y hxy1
      have e2 : dist (u₀ y) (u n y) < ε/3 := hn y hyt
      have e3 : dist (u n y) (u n x) ≤ ω (dist x y) := by
        have h' := hmod n x y hxy1
        rw [dist_eq_norm, norm_sub_rev]
        simpa [dist_eq_norm] using h'
      have step := dist_triangle4 (u₀ x) (u₀ y) (u n y) (u n x)
      linarith [step, e1, e2, e3, hδ (dist x y) hpos hxy]

end Work.MRMT.Found
