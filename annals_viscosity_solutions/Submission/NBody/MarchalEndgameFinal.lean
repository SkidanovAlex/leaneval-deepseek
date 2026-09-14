import Submission.NBody.MarchalEndgameData
import Submission.NBody.MarchalSeqBumpedData
import Submission.NBody.MarchalBumpNoColl
import Submission.NBody.MarchalShapeNondegenerate

/-!
# The endgame: the strengthened two-sided window, and the isolated-collision contradiction

This module contains

* `exists_bump_window_negative_seq_chosen`, the two-sided negative-window lemma with the index `n`
  exposed (so that all the `∀ᶠ n` data of the blow-up can be used at the chosen index), and
* `isHMinimizer_false_of_isolated_collision`, the single-class endgame.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The two-sided window is strictly negative, at a chosen index.**  This is
`exists_bump_window_negative_seq` with the index `n` of the sequence exposed, together with any
property `Q` that holds eventually. -/
theorem exists_bump_window_negative_seq_chosen {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {γ : ℝ → EN E N} {a b t₀ T : ℝ} (hT : 0 < T) (ha : a < t₀) (hb : t₀ < b)
    {k : Finset (Fin N)} {i₀ : Fin N} {δ : E} (hδ : δ ≠ 0)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n) (hlamT : Tendsto lam atTop (nhds 0))
    {KR KL : ℕ → ℝ} {MR ML WR WL : ℝ}
    (hKR : Tendsto KR atTop (nhds MR)) (hKL : Tendsto KL atTop (nhds ML))
    (hM : MR + ML < 0)
    (hR : ∀ᶠ n in atTop, (∫ t in t₀..(t₀ + lam n * T),
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * KR n + (lam n) ^ ((5:ℝ)/3) * WR)
    (hL : ∀ᶠ n in atTop, (∫ t in (t₀ - lam n * T)..t₀,
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * KL n + (lam n) ^ ((5:ℝ)/3) * WL)
    (hintR : ∀ᶠ n in atTop, IntervalIntegrable (fun t => lagR m h
        (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
        volume t₀ (t₀ + lam n * T))
    (hintL : ∀ᶠ n in atTop, IntervalIntegrable (fun t => lagR m h
        (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
        volume (t₀ - lam n * T) t₀)
    {l₀ : ℝ} (hl₀ : 0 < l₀) {Q : ℕ → Prop} (hQ : ∀ᶠ n in atTop, Q n) :
    ∃ n, 0 < lam n ∧ lam n < l₀ ∧ Q n ∧ a ≤ t₀ - lam n * T ∧ t₀ + lam n * T ≤ b ∧
      IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
          (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
        volume t₀ (t₀ + lam n * T) ∧
      IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
          (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
        volume (t₀ - lam n * T) t₀ ∧
      ∫ t in (t₀ - lam n * T)..(t₀ + lam n * T),
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)) < 0 := by
  classical
  have hneg := Commons.Analysis.Asymptotic.eventually_rpow_one_third_mul_add_rpow_five_thirds_mul_neg
    (A := fun n => KR n + KL n) (lam := lam) (a := MR + ML) (W := WR + WL)
    (hKR.add hKL) hM hlamT hlampos
  have hcT : (0:ℝ) < min (t₀ - a) (b - t₀) / T :=
    div_pos (lt_min (by linarith) (by linarith)) hT
  have hsmall : ∀ᶠ n in atTop, lam n ≤ min (t₀ - a) (b - t₀) / T :=
    hlamT.eventually (eventually_le_nhds hcT)
  have hltl : ∀ᶠ n in atTop, lam n < l₀ := hlamT.eventually (eventually_lt_nhds hl₀)
  have hAll : ∀ᶠ n in atTop, lam n ≤ min (t₀ - a) (b - t₀) / T ∧ lam n < l₀ ∧ Q n ∧
        (∫ t in t₀..(t₀ + lam n * T),
          (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
              (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
          ≤ (lam n) ^ ((1:ℝ)/3) * KR n + (lam n) ^ ((5:ℝ)/3) * WR ∧
        (∫ t in (t₀ - lam n * T)..t₀,
          (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
              (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t)))
          ≤ (lam n) ^ ((1:ℝ)/3) * KL n + (lam n) ^ ((5:ℝ)/3) * WL ∧
        lam n ^ ((1:ℝ)/3) * (KR n + KL n) + lam n ^ ((5:ℝ)/3) * (WR + WL) < 0 ∧
        IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
          volume t₀ (t₀ + lam n * T) ∧
        IntervalIntegrable (fun t => lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
          volume (t₀ - lam n * T) t₀ := by
    filter_upwards [hsmall, hltl, hQ, hR, hL, hneg, hintR, hintL] with n h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨n, hnT, hn0, hnQ, hn1, hn2, hn3, hIntR, hIntL⟩ := hAll.exists
  refine ⟨n, hlampos n, hn0, hnQ, ?_, ?_, hIntR, hIntL, ?_⟩
  · have h1 : lam n * T ≤ min (t₀ - a) (b - t₀) := by
      have := mul_le_mul_of_nonneg_right hnT hT.le
      rwa [div_mul_cancel₀ _ hT.ne'] at this
    linarith [min_le_left (t₀ - a) (b - t₀)]
  · have h1 : lam n * T ≤ min (t₀ - a) (b - t₀) := by
      have := mul_le_mul_of_nonneg_right hnT hT.le
      rwa [div_mul_cancel₀ _ hT.ne'] at this
    linarith [min_le_right (t₀ - a) (b - t₀)]
  · rw [← intervalIntegral.integral_add_adjacent_intervals hIntL hIntR]
    refine lt_of_le_of_lt (add_le_add hn2 hn1) ?_
    have hsplit : lam n ^ ((1:ℝ)/3) * KL n + lam n ^ ((5:ℝ)/3) * WL
        + (lam n ^ ((1:ℝ)/3) * KR n + lam n ^ ((5:ℝ)/3) * WR)
        = lam n ^ ((1:ℝ)/3) * (KR n + KL n) + lam n ^ ((5:ℝ)/3) * (WR + WL) := by ring
    linarith [hn3, hsplit]

/-- **The right window bound at a collision, with the collision data given explicitly.**  This is
`seq_action_window_bound_of_collision` with the data of `exists_collision_data_right` (and in
particular the Ferrario--Terracini constant `κ`) supplied by the caller, so that the same `κ` can be
used for the model direction and for the window bound. -/
theorem seq_action_window_bound_of_data {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {γ : ℝ → EN E N} {a b t₀ : ℝ} {k : Finset (Fin N)}
    (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b) (ht₀ : t₀ ∈ Ioo a b)
    {ε ν T : ℝ} (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepw : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) (hT : 0 < T)
    {C Cv κ : ℝ} (hC : 0 < C) (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hE : ∀ t ∈ Ioo (0:ℝ) ε,
      |clusterRelEnergy m k (shiftCurve γ t₀ t) (deriv (shiftCurve γ t₀) t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε,
      |crossWork m k (shiftCurve γ t₀ t) (cmRel m k (shiftCurve γ t₀ t))| ≤ C)
    (hder : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (shiftCurve γ t₀) (deriv (shiftCurve γ t₀) t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε,
      HasDerivAt (deriv (shiftCurve γ t₀)) (iteratedDeriv 2 (shiftCurve γ t₀) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv (shiftCurve γ t₀)))
      (deriv (deriv (deriv (shiftCurve γ t₀))) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε,
      iteratedDeriv 2 (shiftCurve γ t₀) t = ∇_[m] (U m) (shiftCurve γ t₀ t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (shiftCurve γ t₀ t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv (shiftCurve γ t₀) t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (shiftCurve γ t₀ t)))
    (hI0t : Tendsto (fun t : ℝ => clusterInertia m k (shiftCurve γ t₀ t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (shiftCurve γ t₀ s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUlim : Tendsto (fun s : ℝ => clusterPotential m k (shiftCurve γ t₀ s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    (hDn : Tendsto (fun s : ℝ => deriv (fun u : ℝ => clusterInertia m k (shiftCurve γ t₀ u)) s
        / s ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hIdd : Tendsto
      (fun s : ℝ => deriv (deriv (fun u : ℝ => clusterInertia m k (shiftCurve γ t₀ u))) s
        * s ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)))
    (hts : Tendsto (fun u : ℝ => u • deriv (fun u : ℝ => clusterShape m k (shiftCurve γ t₀ u)) u)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    {sbar : EN E N} (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n)
    (hlamT : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hs : Tendsto (fun n => clusterShape m k (shiftCurve γ t₀ (lam n))) atTop (nhds sbar))
    {δ : E} (hδ : δ ≠ 0) (hδT : 2 * ‖δ‖ ≤ T)
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ K : ℕ → ℝ, Tendsto K atTop (nhds (modelDiff m k i₀ κ sbar T δ)) ∧
      ∀ᶠ n in atTop, (∫ t in t₀..(t₀ + lam n * T),
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t)
          - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * K n + (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hlamT0 : Tendsto lam atTop (nhds 0) := hlamT.mono_right nhdsWithin_le_nhds
  have hncS : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (shiftCurve γ t₀ t) :=
    fun t ht => hnc (t₀ + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hseqUG := seq_shape_uniform_limit_at_collision (m := m) (k := k) (γ := γ) (t₀ := t₀)
    (T := T) (ε := ε) (ν := ν) (C := C) (Cv := Cv) (sbar := sbar) (lam := lam)
    hm hk2 hε hT hC hν hCv hncS hE hW hder hd2 hd3 hode hsep hv hI0t hlampos hlamT hs hts
  have hac' : ∀ᶠ n in atTop, AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam n * T) := by
    have hev : ∀ᶠ n in atTop, lam n < ε / T :=
      hlamT0.eventually (isOpen_Iio.mem_nhds (div_pos hε hT))
    filter_upwards [hev] with n hn
    have hlt : lam n * T < ε := (lt_div_iff₀ hT).mp hn
    refine hac.mono ?_
    rw [Set.uIcc_of_le (by nlinarith [hlampos n, hT]), Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc ht₀.1.le (by linarith [hεb])
  obtain ⟨K, hKlim, hKbd⟩ := seq_action_window_bound (m := m) (h := h) (k := k) (i₀ := i₀)
    (γ := γ) (t₀ := t₀) (T := T) (δ := δ) (κ := κ) (sbar := sbar) (lam := lam)
    (ε := ε) (C := C) (Cv := Cv) (ν := ν) (Cd := 1)
    hm hi₀ hk2 hδ hT hδT hκ hsbarnc hgood hlampos hlamT0 hε hC hν hCv
    (by norm_num : (0:ℝ) < 1) hncS hE hW hder hd2 hd3 hode hsep hv hI0t hIn hUlim hDn hts
    hseqUG hac'
  exact ⟨K, hKlim, hKbd⟩

/-- **The left window bound at a collision, with the collision data given explicitly.** -/
theorem seq_action_window_bound_left_of_data {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {γ : ℝ → EN E N} {a b t₀ : ℝ} {k : Finset (Fin N)}
    (hab : a < b) (hk2 : 2 ≤ k.card)
    (hac : AbsolutelyContinuousOnInterval γ a b) (ht₀ : t₀ ∈ Ioo a b)
    {ε ν T : ℝ} (hε : 0 < ε) (hεa : a ≤ t₀ - ε)
    (hncL : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t))
    (hν : 0 < ν) (hsepwL : ∀ t ∈ Ioo (t₀ - ε) t₀, ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) (hT : 0 < T)
    {C Cv κ : ℝ} (hC : 0 < C) (hCv : 0 ≤ Cv) (hκ : 0 < κ)
    (hE : ∀ t ∈ Ioo (0:ℝ) ε,
      |clusterRelEnergy m k (reflectCurve γ t₀ t) (deriv (reflectCurve γ t₀) t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε,
      |crossWork m k (reflectCurve γ t₀ t) (cmRel m k (reflectCurve γ t₀ t))| ≤ C)
    (hder : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (reflectCurve γ t₀) (deriv (reflectCurve γ t₀) t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε,
      HasDerivAt (deriv (reflectCurve γ t₀)) (iteratedDeriv 2 (reflectCurve γ t₀) t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv (reflectCurve γ t₀)))
      (deriv (deriv (deriv (reflectCurve γ t₀))) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε,
      iteratedDeriv 2 (reflectCurve γ t₀) t = ∇_[m] (U m) (reflectCurve γ t₀ t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (reflectCurve γ t₀ t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv (reflectCurve γ t₀) t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (reflectCurve γ t₀ t)))
    (hI0t : Tendsto (fun t : ℝ => clusterInertia m k (reflectCurve γ t₀ t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hIn : Tendsto (fun s : ℝ => clusterInertia m k (reflectCurve γ t₀ s) / s ^ ((4:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds κ))
    (hUlim : Tendsto (fun s : ℝ => clusterPotential m k (reflectCurve γ t₀ s) * s ^ ((2:ℝ)/3))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((2:ℝ)/9 * κ)))
    (hDn : Tendsto
      (fun s : ℝ => deriv (fun u : ℝ => clusterInertia m k (reflectCurve γ t₀ u)) s
        / s ^ ((1:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/3 * κ)))
    (hIdd : Tendsto
      (fun s : ℝ => deriv (deriv (fun u : ℝ => clusterInertia m k (reflectCurve γ t₀ u))) s
        * s ^ ((2:ℝ)/3)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((4:ℝ)/9 * κ)))
    (hts : Tendsto
      (fun u : ℝ => u • deriv (fun u : ℝ => clusterShape m k (reflectCurve γ t₀ u)) u)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    {sbar : EN E N} (hsbarnc : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbar i ≠ sbar j)
    {lam : ℕ → ℝ} (hlampos : ∀ n, 0 < lam n)
    (hlamT : Tendsto lam atTop (nhdsWithin (0:ℝ) (Ioi 0)))
    (hs : Tendsto (fun n => clusterShape m k (reflectCurve γ t₀ (lam n))) atTop (nhds sbar))
    {δ : E} (hδ : δ ≠ 0) (hδT : 2 * ‖δ‖ ≤ T)
    (hgood : ∀ j ∈ k.erase i₀,
      (inner ℝ (sbar i₀ - sbar j) δ) ^ 2 < ‖sbar i₀ - sbar j‖ ^ 2 * ‖δ‖ ^ 2) :
    ∃ K : ℕ → ℝ, Tendsto K atTop (nhds (modelDiff m k i₀ κ sbar T δ)) ∧
      ∀ᶠ n in atTop, (∫ t in (t₀ - lam n * T)..t₀,
        (lagR m h (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
            (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t)
          - lagR m h (γ t) (deriv γ t)))
        ≤ (lam n) ^ ((1:ℝ)/3) * K n + (lam n) ^ ((5:ℝ)/3) * restBound m k δ T ν := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hsh : shiftCurve (reflectCurve γ t₀) 0 = reflectCurve γ t₀ := by
    funext t
    simp only [shiftCurve_apply, zero_add]
  have hncS : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (reflectCurve γ t₀ t) := by
    intro t ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [reflectCurve] using hncL (t₀ - t) h1
  obtain ⟨K, hKlim, hKbd⟩ := seq_action_window_bound_of_data (m := m) (h := h)
    (γ := reflectCurve γ t₀) (a := t₀ - b) (b := t₀ - a) (t₀ := 0) (k := k)
    (ε := ε) (ν := ν) (T := T) (C := C) (Cv := Cv) (κ := κ) (i₀ := i₀) (sbar := sbar)
    (δ := δ) (lam := lam)
    hm (by linarith) hk2 (absolutelyContinuousOnInterval_reflectCurve (t₀ := t₀) hac)
    ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩ hε (by linarith) (by simpa only [zero_add] using hncS)
    hν (by
      intro t ht
      rw [zero_add] at ht
      have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa only [reflectCurve] using hsepwL (t₀ - t) h1)
    (by simpa only [reflectCurve, sub_zero] using hI0) hT hC hCv hκ
    (by simpa only [hsh] using hE)
    (by simpa only [hsh] using hW)
    (by simpa only [hsh] using hder)
    (by simpa only [hsh] using hd2)
    (by simpa only [hsh] using hd3)
    (by simpa only [hsh] using hode)
    (by simpa only [hsh] using hsep)
    (by simpa only [hsh] using hv)
    (by simpa only [hsh] using hI0t)
    (by simpa only [hsh] using hIn)
    (by simpa only [hsh] using hUlim)
    (by simpa only [hsh] using hDn)
    (by simpa only [hsh] using hIdd)
    (by simpa only [hsh] using hts)
    hi₀ hsbarnc hlampos hlamT
    (by
      refine hs.congr' ?_
      filter_upwards with n
      rw [shiftCurve_apply, zero_add])
    hδ hδT hgood
  refine ⟨K, hKlim, ?_⟩
  filter_upwards [hKbd] with n hn
  rw [left_window_eq (fun i => (hm i).le) h δ T (lam n) t₀ γ]
  simpa only [zero_add] using hn

/-- **The single-class endgame.**  An `h`-minimiser whose only collision near `t₀` is a single
cluster `k` (with `|k| ≥ 2`) cannot exist. -/
theorem isHMinimizer_false_of_isolated_collision {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    (hh : 0 < h) {γ : ℝ → EN E N} {a b t₀ : ℝ} (hab : a < b)
    (hErank : 2 ≤ Module.finrank ℝ E)
    {k : Finset (Fin N)} (hk2 : 2 ≤ k.card) (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) {ε ν : ℝ} (hε : 0 < ε) (hεa : a ≤ t₀ - ε) (hεb : t₀ + ε ≤ b)
    (hncR : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hncL : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t))
    (hcoll : ¬ WithoutCollisions (γ t₀))
    (hν : 0 < ν) (hsepwR : ∀ t ∈ Ioo t₀ (t₀ + ε), ClusterSeparatedWeak k (γ t) ν)
    (hsepwL : ∀ t ∈ Ioo (t₀ - ε) t₀, ClusterSeparatedWeak k (γ t) ν)
    (hI0 : clusterInertia m k (γ t₀) = 0) : False := by
  classical
  have hkne : k.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₀, hi₀⟩ := hkne
  have hne : (k.erase i₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hi₀]
    omega
  set T : ℝ := 1 with hTdef
  have hT : (0:ℝ) < T := by rw [hTdef]; norm_num
  -- the shape sphere
  have hmk : clusterMass m k ≠ 0 := (clusterMass_pos hm ⟨i₀, hi₀⟩).ne'
  have hshapeR : ∀ t ∈ Ioo (0:ℝ) ε, clusterShape m k (shiftCurve γ t₀ t) ∈ shapeSet m k := by
    intro t ht
    exact clusterShape_mem_shapeSet hmk
      (clusterInertia_pos hm hk2 (hncR (t₀ + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩))
  have hshapeL : ∀ t ∈ Ioo (0:ℝ) ε, clusterShape m k (reflectCurve γ t₀ t) ∈ shapeSet m k := by
    intro t ht
    exact clusterShape_mem_shapeSet hmk
      (clusterInertia_pos hm hk2 (hncL (t₀ - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩))
  obtain ⟨lam, hlampos, hlamT0, sbarR, sbarL, _hsbR, _hsbL, hsR, hsL⟩ :=
    exists_seq_shape (E := E) hm ⟨i₀, hi₀⟩ hε hshapeR hshapeL
  have hlamT : Tendsto lam atTop (nhds (0:ℝ)) := (tendsto_nhdsWithin_iff.mp hlamT0).1
  -- the collision data on both sides
  obtain ⟨rR, CR, CvR, κR, hrRpos, hrRε, hCRpos, hCvR0, hκRpos, hsepUR, hncUR, hER, hWR, hvR,
    hxR, hd2R, hd3R, hodeR, hI0UR, hInR, hUlimR, hDnR, hIddR, htsR⟩ :=
    exists_collision_data_right (m := m) (h := h) (γ := γ) (a := a) (b := b) (t₀ := t₀) (k := k)
      hm hh hab hk2 hac hmin hfin ht₀ hε hεb hncR hcoll hν hsepwR hI0
  obtain ⟨rL, CL, CvL, κL, hrLpos, hrLε, hCLpos, hCvL0, hκLpos, hsepUL, hncUL, hEL, hWL, hvL,
    hxL, hd2L, hd3L, hodeL, hI0UL, hInL, hUlimL, hDnL, hIddL, htsL⟩ :=
    exists_collision_data_left (m := m) (h := h) (γ := γ) (a := a) (b := b) (t₀ := t₀) (k := k)
      hm hh hab hk2 hac hmin hfin ht₀ hε hεa hncL hcoll hν hsepwL hI0
  -- the uniform shape limits
  have hseqUGR := seq_shape_uniform_limit_at_collision (m := m) (k := k) (γ := γ) (t₀ := t₀)
    (T := T) (ε := rR) (ν := ν) (C := CR) (Cv := CvR) (sbar := sbarR) (lam := lam)
    hm hk2 hrRpos hT hCRpos hν hCvR0 hncUR hER hWR hxR hd2R hd3R hodeR hsepUR hvR hI0UR
    hlampos hlamT0 hsR htsR
  have hsL' : Tendsto (fun n => clusterShape m k (shiftCurve (reflectCurve γ t₀) 0 (lam n)))
      atTop (nhds sbarL) := by
    refine hsL.congr' ?_
    filter_upwards with n
    rw [shiftCurve_apply, zero_add]
  have hshL : shiftCurve (reflectCurve γ t₀) 0 = reflectCurve γ t₀ := by
    funext t
    simp only [shiftCurve_apply, zero_add]
  have hseqUGL := seq_shape_uniform_limit_at_collision (m := m) (k := k) (γ := reflectCurve γ t₀)
    (t₀ := 0) (T := T) (ε := rL) (ν := ν) (C := CL) (Cv := CvL) (sbar := sbarL) (lam := lam)
    hm hk2 hrLpos hT hCLpos hν hCvL0 (by simpa only [hshL] using hncUL) (by simpa only [hshL] using hEL)
    (by simpa only [hshL] using hWL) (by simpa only [hshL] using hxL) (by simpa only [hshL] using hd2L)
    (by simpa only [hshL] using hd3L) (by simpa only [hshL] using hodeL)
    (by simpa only [hshL] using hsepUL) (by simpa only [hshL] using hvL)
    (by simpa only [hshL] using hI0UL)
    hlampos hlamT0 hsL' (by simpa only [hshL] using htsL)
  -- non-degeneracy of the limit shapes
  have hsbarncR : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbarR i ≠ sbarR j := by
    intro i hi j hj hij
    exact shape_pair_ne_of_asymptotic (m := m) (k := k) (x := shiftCurve γ t₀) hm hk2 hrRpos
      hκRpos hncUR hInR hUlimR hlampos hlamT0 hsR hi hj hij
  have hsbarncL : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → sbarL i ≠ sbarL j := by
    intro i hi j hj hij
    exact shape_pair_ne_of_asymptotic (m := m) (k := k) (x := reflectCurve γ t₀) hm hk2
      hrLpos hκLpos hncUL hInL hUlimL hlampos hlamT0 hsL hi hj hij
  -- an orthonormal pair
  let B : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let e : E := B ⟨0, by omega⟩
  let f : E := B ⟨1, by omega⟩
  have hB : ∀ i j : Fin (Module.finrank ℝ E), inner ℝ (B i) (B j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp B.orthonormal
  have he : ‖e‖ = 1 := by
    have h1 : inner ℝ e e = 1 := by
      have h2 := hB ⟨0, by omega⟩ ⟨0, by omega⟩
      simpa [e] using h2
    have h3 : ‖e‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h1
    nlinarith [norm_nonneg e]
  have hf : ‖f‖ = 1 := by
    have h1 : inner ℝ f f = 1 := by
      have h2 := hB ⟨1, by omega⟩ ⟨1, by omega⟩
      simpa [f] using h2
    have h3 : ‖f‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h1
    nlinarith [norm_nonneg f]
  have hef : inner ℝ e f = 0 := by
    have h2 := hB ⟨0, by omega⟩ ⟨1, by omega⟩
    have h3 : (⟨0, by omega⟩ : Fin (Module.finrank ℝ E)) ≠ ⟨1, by omega⟩ := by
      simp
    simpa [e, f, h3] using h2
  -- the radius
  set cRk : Fin N → ℝ := fun j =>
    (1/8) * Real.sqrt κR * (T/2) ^ ((2:ℝ)/3) * ‖sbarR i₀ - sbarR j‖ with hcRdef
  set cLk : Fin N → ℝ := fun j =>
    (1/8) * Real.sqrt κL * (T/2) ^ ((2:ℝ)/3) * ‖sbarL i₀ - sbarL j‖ with hcLdef
  set ρmax : ℝ := min (min (T/2) ((k.erase i₀).inf' hne cRk)) ((k.erase i₀).inf' hne cLk)
    with hρmaxdef
  have hcRpos : ∀ j ∈ k.erase i₀, 0 < cRk j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
    rw [hcRdef]
    have h3 : 0 < ‖sbarR i₀ - sbarR j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hsbarncR i₀ hi₀ j hj2 (Ne.symm hj1)))
    have h2 : 0 < (T/2) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos (by linarith [hT]) _
    have h4 : 0 < Real.sqrt κR := Real.sqrt_pos.mpr hκRpos
    exact mul_pos (mul_pos (mul_pos (by norm_num) h4) h2) h3
  have hcLpos : ∀ j ∈ k.erase i₀, 0 < cLk j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
    rw [hcLdef]
    have h3 : 0 < ‖sbarL i₀ - sbarL j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hsbarncL i₀ hi₀ j hj2 (Ne.symm hj1)))
    have h2 : 0 < (T/2) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos (by linarith [hT]) _
    have h4 : 0 < Real.sqrt κL := Real.sqrt_pos.mpr hκLpos
    exact mul_pos (mul_pos (mul_pos (by norm_num) h4) h2) h3
  have hρmaxpos : 0 < ρmax := by
    rw [hρmaxdef]
    refine lt_min (lt_min (by linarith [hT]) ?_) ?_
    · exact (Finset.lt_inf'_iff hne).mpr (fun j hj => hcRpos j hj)
    · exact (Finset.lt_inf'_iff hne).mpr (fun j hj => hcLpos j hj)
  have hρmaxT : ρmax ≤ T/2 := by
    rw [hρmaxdef]
    exact le_trans (min_le_left (min (T/2) _) _) (min_le_left _ _)
  have hsmallR : ∀ j ∈ k.erase i₀,
      ρmax / (Real.sqrt κR * (T/2) ^ ((2:ℝ)/3) * ‖sbarR i₀ - sbarR j‖) ≤ 1/8 := by
    intro j hj
    have h1 : ρmax ≤ (k.erase i₀).inf' hne cRk :=
      le_trans (min_le_left (min (T/2) ((k.erase i₀).inf' hne cRk)) _) (min_le_right (T/2) _)
    have h2 : (k.erase i₀).inf' hne cRk ≤ cRk j := Finset.inf'_le cRk hj
    have h3 : ρmax ≤ cRk j := le_trans h1 h2
    rw [hcRdef] at h3
    have hpos : 0 < Real.sqrt κR * (T/2) ^ ((2:ℝ)/3) * ‖sbarR i₀ - sbarR j‖ := by
      have h4 : 0 < Real.sqrt κR := Real.sqrt_pos.mpr hκRpos
      have h5 : 0 < (T/2) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos (by linarith [hT]) _
      exact mul_pos (mul_pos h4 h5) (norm_pos_iff.mpr (sub_ne_zero.mpr
        (hsbarncR i₀ hi₀ j (Finset.mem_erase.mp hj).2 (Ne.symm (Finset.mem_erase.mp hj).1))))
    rw [div_le_iff₀ hpos]
    linarith [h3]
  have hsmallL : ∀ j ∈ k.erase i₀,
      ρmax / (Real.sqrt κL * (T/2) ^ ((2:ℝ)/3) * ‖sbarL i₀ - sbarL j‖) ≤ 1/8 := by
    intro j hj
    have h1 : ρmax ≤ (k.erase i₀).inf' hne cLk := le_trans (min_le_right _ _) le_rfl
    have h2 : (k.erase i₀).inf' hne cLk ≤ cLk j := Finset.inf'_le cLk hj
    have h3 : ρmax ≤ cLk j := le_trans h1 h2
    rw [hcLdef] at h3
    have hpos : 0 < Real.sqrt κL * (T/2) ^ ((2:ℝ)/3) * ‖sbarL i₀ - sbarL j‖ := by
      have h4 : 0 < Real.sqrt κL := Real.sqrt_pos.mpr hκLpos
      have h5 : 0 < (T/2) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos (by linarith [hT]) _
      exact mul_pos (mul_pos h4 h5) (norm_pos_iff.mpr (sub_ne_zero.mpr
        (hsbarncL i₀ hi₀ j (Finset.mem_erase.mp hj).2 (Ne.symm (Finset.mem_erase.mp hj).1))))
    rw [div_le_iff₀ hpos]
    linarith [h3]
  -- the outward direction
  obtain ⟨ρ, hρpos, hρle, θ, _hθ, hgoodR, hgoodL, hMneg⟩ :=
    exists_model_dir_two_sided_of_blowup (m := m) (k := k) (i₀ := i₀) hm hi₀ hne
      hκRpos hκLpos hT sbarR sbarL hsbarncR hsbarncL e f he hf hef hρmaxpos hρmaxT hsmallR hsmallL
  set δ : E := ρ • circleDir e f θ with hδdef
  have hδnorm : ‖δ‖ = ρ := by
    rw [hδdef, norm_smul, norm_circleDir he hf hef θ, Real.norm_eq_abs, abs_of_pos hρpos, mul_one]
  have hδ : δ ≠ 0 := by
    rw [← norm_ne_zero_iff, hδnorm]
    exact hρpos.ne'
  have hδT : 2 * ‖δ‖ ≤ T := by
    rw [hδnorm]
    have h1 : ρ ≤ T/2 := le_trans hρle hρmaxT
    linarith
  have hncRr : ∀ t ∈ Ioo t₀ (t₀ + rR), WithoutCollisions (γ t) :=
    fun t ht => hncR t ⟨ht.1, by linarith [ht.2, hrRε]⟩
  have hsepRr : ∀ t ∈ Ioo t₀ (t₀ + rR), ClusterSeparatedWeak k (γ t) ν :=
    fun t ht => hsepwR t ⟨ht.1, by linarith [ht.2, hrRε]⟩
  have hncLr : ∀ t ∈ Ioo (t₀ - rL) t₀, WithoutCollisions (γ t) :=
    fun t ht => hncL t ⟨by linarith [ht.1, hrLε], ht.2⟩
  have hsepLr : ∀ t ∈ Ioo (t₀ - rL) t₀, ClusterSeparatedWeak k (γ t) ν :=
    fun t ht => hsepwL t ⟨by linarith [ht.1, hrLε], ht.2⟩
  -- the two window bounds
  obtain ⟨KR, hKRlim, hKRbd⟩ := seq_action_window_bound_of_data (m := m) (h := h)
    (γ := γ) (a := a) (b := b) (t₀ := t₀) (k := k) (ε := rR) (ν := ν) (T := T)
    (C := CR) (Cv := CvR) (κ := κR) (i₀ := i₀) (sbar := sbarR) (δ := δ) (lam := lam)
    hm hab hk2 hac ht₀ hrRpos (by linarith [hrRε, hεb]) hncRr hν hsepRr hI0 hT hCRpos hCvR0 hκRpos
    hER hWR hxR hd2R hd3R hodeR hsepUR hvR hI0UR hInR hUlimR hDnR hIddR htsR
    hi₀ hsbarncR hlampos hlamT0 hsR hδ hδT hgoodR
  obtain ⟨KL, hKLlim, hKLbd⟩ := seq_action_window_bound_left_of_data (m := m) (h := h)
    (γ := γ) (a := a) (b := b) (t₀ := t₀) (k := k) (ε := rL) (ν := ν) (T := T)
    (C := CL) (Cv := CvL) (κ := κL) (i₀ := i₀) (sbar := sbarL) (δ := δ) (lam := lam)
    hm hab hk2 hac ht₀ hrLpos (by linarith [hrLε, hεa]) hncLr hν hsepLr hI0 hT hCLpos hCvL0 hκLpos
    hEL hWL hxL hd2L hd3L hodeL hsepUL hvL hI0UL hInL hUlimL hDnL hIddL htsL
    hi₀ hsbarncL hlampos hlamT0 hsL hδ hδT hgoodL
  -- the velocity bounds and the bumped data
  obtain ⟨CdR, hCdRpos, hvelR⟩ := seq_vel_bound (m := m) (k := k) (x := shiftCurve γ t₀)
    (ε := rR) (C := CR) (ν := ν) (Cv := CvR) (T := T)
    hm hk2 hrRpos hCRpos hν hCvR0 hT hncUR hER hWR hxR hd2R hd3R hodeR hsepUR hvR hI0UR hlamT0
  obtain ⟨CdL, hCdLpos, hvelL⟩ := seq_vel_bound (m := m) (k := k) (x := reflectCurve γ t₀)
    (ε := rL) (C := CL) (ν := ν) (Cv := CvL) (T := T)
    hm hk2 hrLpos hCLpos hν hCvL0 hT hncUL hEL hWL hxL hd2L hd3L hodeL hsepUL hvL hI0UL hlamT0
  obtain ⟨Cp2R, hCp2Rpos, hUpotBR, hnnBR⟩ := seq_bumped_data (m := m) (k := k) (i₀ := i₀)
    hm hi₀ hk2 hδ hT hrRpos hδT hκRpos hgoodR
    hlampos hlamT hsR hncUR hInR hUlimR hseqUGR
  obtain ⟨Cp2L, hCp2Lpos, hUpotBL, hnnBL⟩ := seq_bumped_data (m := m) (k := k) (i₀ := i₀)
    hm hi₀ hk2 hδ hT hrLpos hδT hκLpos hgoodL
    hlampos hlamT hsL' (by simpa only [hshL] using hncUL) (by simpa only [hshL] using hInL)
    (by simpa only [hshL] using hUlimL) hseqUGL
  -- the un-bumped potential bounds along the sequence
  have hUpotR : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k γ t₀ (lam n) t) ≤ ((2:ℝ)/9 * κR + 1) * t ^ (-(2:ℝ)/3) := by
    have h := seq_potential_bound (m := m) (k := k) (x := shiftCurve γ t₀) (κ := κR) (T := T)
      hκRpos hT hUlimR hlamT0
    filter_upwards [h] with n hn
    intro t ht
    simpa only [bumpRescaled] using hn t ht
  have hUpotL : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k (reflectCurve γ t₀) 0 (lam n) t)
        ≤ ((2:ℝ)/9 * κL + 1) * t ^ (-(2:ℝ)/3) := by
    have h := seq_potential_bound (m := m) (k := k) (x := reflectCurve γ t₀) (κ := κL) (T := T)
      hκLpos hT hUlimL hlamT0
    filter_upwards [h] with n hn
    intro t ht
    simpa only [bumpRescaled, hshL] using hn t ht
  have hvelR' : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k γ t₀ (lam n)) t‖_[m] ≤ CdR * t ^ (-(1:ℝ)/3) := by
    filter_upwards [hvelR] with n hn
    intro t ht
    simpa only [bumpRescaled] using hn t ht
  have hvelL' : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k (reflectCurve γ t₀) 0 (lam n)) t‖_[m] ≤ CdL * t ^ (-(1:ℝ)/3) := by
    filter_upwards [hvelL] with n hn
    intro t ht
    simpa only [bumpRescaled, hshL] using hn t ht
  -- the smallness and separation facts along the sequence
  have hsmall4 : ∀ᶠ n in atTop, 4 * (lam n ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν := by
    have hpow : Tendsto (fun n => lam n ^ ((2:ℝ)/3)) atTop (nhds 0) :=
      hlamT.rpow_const_nhds_zero (by norm_num)
    have hpos : (0:ℝ) < ν / (4 * ‖δ‖) :=
      div_pos hν (mul_pos (by norm_num) (norm_pos_iff.mpr hδ))
    filter_upwards [hpow.eventually (eventually_lt_nhds hpos)] with n hn
    have h2 : lam n ^ ((2:ℝ)/3) * ‖δ‖ < ν / 4 := by
      calc lam n ^ ((2:ℝ)/3) * ‖δ‖ < (ν / (4 * ‖δ‖)) * ‖δ‖ :=
            mul_lt_mul_of_pos_right hn (norm_pos_iff.mpr hδ)
        _ = ν / 4 := by field_simp
    linarith
  have hsmallmin : ∀ᶠ n in atTop, lam n * T < min ε (min rR rL) := by
    have hpos : (0:ℝ) < min ε (min rR rL) / T := div_pos (lt_min hε (lt_min hrRpos hrLpos)) hT
    filter_upwards [hlamT.eventually (eventually_lt_nhds hpos)] with n hn
    have h := (lt_div_iff₀ hT).mp hn
    linarith
  have hsepRQ : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      ClusterSeparatedWeak k (γ (t₀ + lam n * t)) ν := by
    filter_upwards [hsmallmin] with n hn
    intro t ht
    have h1 : lam n * t < rR := by
      have h3 : lam n * t ≤ lam n * T := mul_le_mul_of_nonneg_left ht.2 (hlampos n).le
      linarith [(min_le_right ε (min rR rL)).trans (min_le_left rR rL)]
    exact hsepUR (lam n * t) ⟨mul_pos (hlampos n) ht.1, h1⟩
  have hsepLQ : ∀ᶠ n in atTop, ∀ t ∈ Ioc (0:ℝ) T,
      ClusterSeparatedWeak k (reflectCurve γ t₀ (0 + lam n * t)) ν := by
    filter_upwards [hsmallmin] with n hn
    intro t ht
    rw [zero_add]
    have h1 : lam n * t < rL := by
      have h3 : lam n * t ≤ lam n * T := mul_le_mul_of_nonneg_left ht.2 (hlampos n).le
      linarith [(min_le_right ε (min rR rL)).trans (min_le_right rR rL)]
    exact hsepUL (lam n * t) ⟨mul_pos (hlampos n) ht.1, h1⟩
  have hncRQ : ∀ᶠ n in atTop, ∀ t ∈ Ioo (0:ℝ) T, WithoutCollisions (γ (t₀ + lam n * t)) := by
    filter_upwards [hsmallmin] with n hn
    intro t ht
    have h1 : lam n * t < ε := by
      have h3 : lam n * t ≤ lam n * T :=
        mul_le_mul_of_nonneg_left (le_of_lt ht.2) (hlampos n).le
      linarith [min_le_left ε (min rR rL)]
    exact hncR (t₀ + lam n * t) ⟨by linarith [mul_pos (hlampos n) ht.1], by linarith [h1]⟩
  have hncLQ : ∀ᶠ n in atTop, ∀ t ∈ Ioo (0:ℝ) T,
      WithoutCollisions (reflectCurve γ t₀ (0 + lam n * t)) := by
    filter_upwards [hsmallmin] with n hn
    intro t ht
    rw [zero_add]
    have h1 : lam n * t < ε := by
      have h3 : lam n * t ≤ lam n * T :=
        mul_le_mul_of_nonneg_left (le_of_lt ht.2) (hlampos n).le
      linarith [min_le_left ε (min rR rL)]
    exact hncL (t₀ - lam n * t) ⟨by linarith [h1], by linarith [mul_pos (hlampos n) ht.1]⟩
  -- the window
  set Q : ℕ → Prop := fun n =>
    (2 * (lam n ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) ∧
    (∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam n * t)) ν) ∧
    (∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (reflectCurve γ t₀ (0 + lam n * t)) ν) ∧
    (∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k γ t₀ (lam n) t + stdVarVec m k i₀ δ T t) ≤ Cp2R * t ^ (-(2:ℝ)/3)) ∧
    (∀ t ∈ Ioo (0:ℝ) T, ClusterNoColl k
      (bumpRescaled m k γ t₀ (lam n) t + stdVarVec m k i₀ δ T t)) ∧
    (∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k (reflectCurve γ t₀) 0 (lam n) t + stdVarVec m k i₀ δ T t)
        ≤ Cp2L * t ^ (-(2:ℝ)/3)) ∧
    (∀ t ∈ Ioo (0:ℝ) T, ClusterNoColl k
      (bumpRescaled m k (reflectCurve γ t₀) 0 (lam n) t + stdVarVec m k i₀ δ T t)) ∧
    (∀ t ∈ Ioo (0:ℝ) T, WithoutCollisions (γ (t₀ + lam n * t))) ∧
    (∀ t ∈ Ioo (0:ℝ) T, WithoutCollisions (reflectCurve γ t₀ (0 + lam n * t))) with hQdef
  have hQ : ∀ᶠ n in atTop, Q n := by
    rw [show Q = fun n => _ from rfl]
    filter_upwards [hsmall4, hsepRQ, hsepLQ, hUpotBR, hnnBR, hUpotBL, hnnBL, hncRQ, hncLQ]
      with n h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨by linarith [h1], h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hintRseq : ∀ᶠ n in atTop, IntervalIntegrable (fun t => lagR m h
      (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      volume t₀ (t₀ + lam n * T) := by
    filter_upwards [hvelR', hUpotR, hUpotBR, hnnBR, hsepRQ, hsmall4, hsmallmin,
      Filter.Eventually.of_forall hlampos] with n h1 h2 h3 h4 h5 h6 h8 h7
    have hacn : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam n * T) := by
      refine hac.mono ?_
      rw [Set.uIcc_of_le (by nlinarith [h7, hT]), Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc ht₀.1.le
        (by linarith [hεb, lt_of_lt_of_le h8 (min_le_left ε (min rR rL))])
    have hncI : ∀ t ∈ Ioo t₀ (t₀ + lam n * T), WithoutCollisions (γ t) := by
      intro t ht
      have hlt : lam n * T < ε := lt_of_lt_of_le h8 (min_le_left ε (min rR rL))
      exact hncR t ⟨ht.1, by linarith [ht.2, hlt]⟩
    obtain ⟨h1i, h2i, h3i, h4i, h56i⟩ := bump_pieces_intervalIntegrable_good
      (m := m) (k := k) (i₀ := i₀) hm hi₀ hδ h7 hT hacn hncI (le_of_lt hCdRpos)
      (by positivity : (0:ℝ) ≤ (2:ℝ)/9 * κR + 1) hCp2Rpos.le hν h1 h2 h4 h3 h5 h6
    exact intervalIntegrable_bump_lagR_diff (m := m) (k := k) (i₀ := i₀) hm hi₀ hδ h7 hT
      hacn h1i h2i h3i h4i h56i
  have hintLseq : ∀ᶠ n in atTop, IntervalIntegrable (fun t => lagR m h
      (bumpCurve m k i₀ δ T (lam n) t₀ γ t)
      (deriv (bumpCurve m k i₀ δ T (lam n) t₀ γ) t) - lagR m h (γ t) (deriv γ t))
      volume (t₀ - lam n * T) t₀ := by
    filter_upwards [hvelL', hUpotL, hUpotBL, hnnBL, hsepLQ, hsmall4, hsmallmin,
      Filter.Eventually.of_forall hlampos] with n h1 h2 h3 h4 h5 h6 h8 h7
    have hacn : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) 0 (0 + lam n * T) := by
      have h := absolutelyContinuousOnInterval_reflectCurve (t₀ := t₀) hac
      rw [zero_add]
      refine h.mono ?_
      rw [Set.uIcc_of_le (by nlinarith [h7, hT]),
        Set.uIcc_of_le (by linarith [hab.le])]
      exact Set.Icc_subset_Icc (by linarith [ht₀.2])
        (by linarith [hεa, lt_of_lt_of_le h8 (min_le_left ε (min rR rL))])
    have hncI : ∀ t ∈ Ioo (0:ℝ) (0 + lam n * T), WithoutCollisions (reflectCurve γ t₀ t) := by
      intro t ht
      rw [zero_add] at ht
      have hlt : lam n * T < ε := lt_of_lt_of_le h8 (min_le_left ε (min rR rL))
      have h1' : t₀ - t ∈ Ioo (t₀ - ε) t₀ :=
        ⟨by linarith [ht.2, hlt], by linarith [ht.1]⟩
      simpa only [reflectCurve] using hncL (t₀ - t) h1'
    obtain ⟨h1i, h2i, h3i, h4i, h56i⟩ := bump_pieces_intervalIntegrable_good
      (m := m) (k := k) (i₀ := i₀) (γ := reflectCurve γ t₀) (t₀ := 0) hm hi₀ hδ h7 hT
      hacn hncI (le_of_lt hCdLpos)
      (by positivity : (0:ℝ) ≤ (2:ℝ)/9 * κL + 1) hCp2Lpos.le hν h1 h2 h4 h3 h5 h6
    have hRL := intervalIntegrable_bump_lagR_diff (m := m) (h := h) (k := k) (i₀ := i₀)
      (γ := reflectCurve γ t₀) (t₀ := 0) hm hi₀ hδ h7 hT hacn h1i h2i h3i h4i h56i
    rw [zero_add] at hRL
    exact intervalIntegrable_bump_lagR_diff_left (m := m) (h := h) (k := k) (i₀ := i₀)
      hm hi₀ hδ h7 hT hRL
  obtain ⟨n, hnpos, _hnlt, hnQ, hn1, hn2, hIntR, hIntL, hwin⟩ :=
    exists_bump_window_negative_seq_chosen (m := m) (h := h) (γ := γ) (a := a) (b := b)
      (t₀ := t₀) (T := T) (k := k) (i₀ := i₀) (δ := δ) hm hT
      (by linarith [ht₀.1]) (by linarith [ht₀.2]) hδ hlampos hlamT hKRlim hKLlim hMneg
      hKRbd hKLbd hintRseq hintLseq (l₀ := 1) (by norm_num) hQ
  rw [hQdef] at hnQ
  obtain ⟨hnQ1, hnsepR, hnsepL, hnUpotBR, hnhnnBR, hnUpotBL, hnhnnBL, hnγR, hnγL⟩ := hnQ
  have hfinγ : actionOn m h γ a b < ⊤ := hmin.symm ▸ hfin (γ a) (γ b)
  have hfinη : actionOn m h (bumpCurve m k i₀ δ T (lam n) t₀ γ) a b < ⊤ :=
    actionOn_bumpCurve_lt_top (m := m) (h := h) hm hh.le hi₀ hδ hnpos hT hab.le hac hfinγ hn1 hn2
      (fun t ht => by
        have ht' : 0 < (t - t₀) / lam n ∧ (t - t₀) / lam n < T := by
          constructor
          · exact div_pos (sub_pos.mpr ht.1) hnpos
          · rw [div_lt_iff₀ hnpos]
            linarith [ht.2]
        have htu : t₀ + lam n * ((t - t₀) / lam n) = t := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnpos.ne']
          ring
        rw [← htu]
        exact withoutCollisions_bumpCurve_shift hm hi₀ hδ hnpos ht'.1.le hν
          (hnsepR ((t - t₀) / lam n) ⟨ht'.1, le_of_lt ht'.2⟩) hnQ1
          (hnγR ((t - t₀) / lam n) ⟨ht'.1, ht'.2⟩)
          (hnhnnBR ((t - t₀) / lam n) ⟨ht'.1, ht'.2⟩))
      (fun t ht => by
        have ht' : 0 < (t₀ - t) / lam n ∧ (t₀ - t) / lam n < T := by
          constructor
          · exact div_pos (sub_pos.mpr ht.2) hnpos
          · rw [div_lt_iff₀ hnpos]
            linarith [ht.1]
        have hmem : (t₀ - t) / lam n ∈ Ioo (0:ℝ) T := ⟨ht'.1, ht'.2⟩
        have hbr : bumpCurve m k i₀ δ T (lam n) 0 (reflectCurve γ t₀) (0 + lam n * ((t₀ - t) / lam n))
            = bumpCurve m k i₀ δ T (lam n) t₀ γ (t₀ - lam n * ((t₀ - t) / lam n)) := by
          rw [zero_add]
          exact bumpCurve_reflect δ T (lam n) t₀ γ _
        have htu : t₀ - lam n * ((t₀ - t) / lam n) = t := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnpos.ne']
          ring
        rw [← htu, ← hbr]
        exact withoutCollisions_bumpCurve_shift hm hi₀ hδ hnpos ht'.1.le hν
          (hnsepL ((t₀ - t) / lam n) ⟨ht'.1, le_of_lt ht'.2⟩) hnQ1
          (hnγL ((t₀ - t) / lam n) hmem)
          (hnhnnBL ((t₀ - t) / lam n) hmem))
      (le_of_lt hCp2Rpos) (le_of_lt hCp2Lpos) hν hν hnUpotBR hnUpotBL hnsepR hnsepL hnQ1 hnQ1
  exact isHMinimizer_false_of_bump_window (m := m) hm hh.le hab hi₀ hδ hnpos (le_of_lt hT) hac
    hmin hfinγ hfinη (by simpa using hIntL.trans hIntR) hn1 hn2 hwin

end Submission.NBody
