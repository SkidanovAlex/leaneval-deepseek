import Mathlib
import Submission.Work.Drive.Mono.CutTransverse
import Submission.Work.Drive.Mono.TiltedTraceData

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/- Almost every level of the `σ 2`-coordinate of `K`, shifted by `c (σ 2)`, has positive
distance from the set of critical values of that coordinate.

The proof has two halves.  Sard's theorem in dimension one shows that the set `S` of critical
values (shifted by `c (σ 2)`) is Lebesgue-null.  To upgrade nullity of `S` to nullity of
`closure S` -- which is what the positive distance `δ` demands -- we use that `S` is compact:
the critical set in one period is a closed subset of the compact interval `[0, 2π]`, and the curve
is `2π`-periodic, so the critical values on the whole line are the image of that compact piece. -/
theorem ae_noCritValue_near (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
        δ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| := by
  -- The `σ 2`-coordinate of the curve, as a scalar function of the parameter.
  set f : ℝ → ℝ := fun r => (K.curve r) (σ 2) with hf
  change ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, deriv f t = 0 → δ ≤ |f t - (c (σ 2) + u)|
  -- `f` is smooth (the knot is `C^∞`).
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf]
    have h1 := ContDiff.continuousLinearMap_comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ 2)) K.smooth
    simpa using h1
  -- `f` and `deriv f` are `2π`-periodic.
  have hperf : Function.Periodic f (2 * Real.pi) := by
    intro x
    show (K.curve (x + 2 * Real.pi)) (σ 2) = (K.curve x) (σ 2)
    rw [K.periodic x]
  have hperdf : Function.Periodic (deriv f) (2 * Real.pi) := by
    intro x
    rw [(deriv_comp_add_const f (2 * Real.pi) x).symm]
    rw [funext hperf]
  -- `G` is `f` shifted by the constant `c (σ 2)`; its critical set is that of `f`.
  set G : ℝ → ℝ := fun t => f t - c (σ 2) with hG
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [hG]
    exact hf_smooth.sub contDiff_const
  have hGderiv : ∀ t, HasDerivAt G (deriv G t) t := fun t =>
    (hG_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hderivG : ∀ t, deriv G t = deriv f t := fun t => by
    rw [hG]; exact deriv_sub_const (c (σ 2))
  -- The critical set `Z` of `f` and the corresponding set `S` of critical values (shifted).
  set Z : Set ℝ := {t | deriv f t = 0} with hZ
  set S : Set ℝ := G '' Z with hS
  have hZeq : Z = {t | deriv G t = 0} := by
    ext t; simp only [hZ, Set.mem_ofPred_eq]; rw [hderivG t]
  -- Sard in dimension one: `S` is Lebesgue-null.
  have hSard : MeasureTheory.volume (G '' {t | deriv G t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := MeasureTheory.volume) (f := G)
      (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv G t)) ?_ ?_
    · intro t _
      exact (hGderiv t).hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      rw [ht, ContinuousLinearMap.det_toSpanSingleton]
  have hnull : MeasureTheory.volume S = 0 := by
    rw [hS, hZeq]; exact hSard
  -- `Z` is closed, hence the critical set in one period is compact.
  have hZc : IsClosed Z := by
    have hcont : Continuous (deriv f) := hf_smooth.continuous_deriv (by norm_num)
    exact isClosed_eq hcont continuous_const
  have hcompact : IsCompact (Z ∩ Icc 0 (2 * Real.pi)) := isCompact_Icc.inter_left hZc
  -- Periodicity: every critical value is attained at a critical parameter in `[0, 2π]`.
  have hred : G '' Z = G '' (Z ∩ Icc 0 (2 * Real.pi)) := by
    refine Set.Subset.antisymm ?_ (Set.image_mono Set.inter_subset_left)
    rintro _ ⟨t, ht, rfl⟩
    have ht' : deriv f t = 0 := by simpa [hZ] using ht
    -- Reduce `t` modulo `2π`.
    set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
    set s : ℝ := t - k • (2 * Real.pi) with hs
    have hpi : (0:ℝ) < 2 * Real.pi := by positivity
    have h1 : (k:ℝ) * (2*Real.pi) ≤ t := by
      rw [← le_div_iff₀ hpi]
      rw [hk]
      exact Int.floor_le _
    have h2 : t < ((k:ℝ) + 1) * (2*Real.pi) := by
      have hh : t / (2*Real.pi) < (k:ℝ) + 1 := by
        have h3 := Int.lt_floor_add_one (t / (2 * Real.pi))
        rwa [← hk] at h3
      rwa [div_lt_iff₀ hpi] at hh
    have hs_mem : s ∈ Ico (0:ℝ) (2*Real.pi) := by
      constructor
      · rw [hs]; simp only [zsmul_eq_mul]; linarith
      · rw [hs]; simp only [zsmul_eq_mul]; nlinarith [h2]
    have hst : s + k • (2 * Real.pi) = t := by rw [hs]; simp
    have hf_eq : f t = f s := by rw [← hst]; exact (hperf.zsmul k) s
    have hdf_eq : deriv f t = deriv f s := by rw [← hst]; exact (hperdf.zsmul k) s
    refine ⟨s, ⟨?_, Ico_subset_Icc_self hs_mem⟩, ?_⟩
    · rw [hZ]; simp only [Set.mem_ofPred_eq]; rw [← hdf_eq]; exact ht'
    · simp only [hG, hf_eq]
  -- Hence `S` is compact, therefore closed.
  have hGcont : Continuous G := hG_smooth.continuous
  have hS_closed : IsClosed S := by
    rw [hS, hred]
    exact (hcompact.image hGcont).isClosed
  -- Almost every `u` avoids the null closed set `S`.
  have hae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), u ∉ S := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  filter_upwards [hae] with u hu
  rcases S.eq_empty_or_nonempty with hE | hne
  · -- No critical points at all: any `δ > 0` works.
    refine ⟨1, one_pos, fun t ht => ?_⟩
    have hmemZ : t ∈ Z := by simpa [hZ] using ht
    have : G t ∈ S := ⟨t, hmemZ, rfl⟩
    rw [hE] at this
    exact absurd this (by simp)
  · -- Otherwise take `δ` to be the distance from `u` to `S`.
    refine ⟨Metric.infDist u S, ?_, ?_⟩
    · rw [← Metric.infDist_pos_iff_notMem_closure hne, hS_closed.closure_eq]
      exact hu
    · intro t ht
      have hmemZ : t ∈ Z := by simpa [hZ] using ht
      have hmem : G t ∈ S := ⟨t, hmemZ, rfl⟩
      have h1 : Metric.infDist u S ≤ dist u (G t) := Metric.infDist_le_dist_of_mem (x := u) hmem
      calc Metric.infDist u S ≤ dist u (G t) := h1
        _ = |f t - (c (σ 2) + u)| := by
              rw [Real.dist_eq, abs_sub_comm]
              congr 1
              simp only [hG]
              ring

end Work.Drive.Mono
