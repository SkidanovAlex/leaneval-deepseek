import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.PressureOn.Connect.BoundaryTime

theorem rightDeriv_zero_of_hasDerivAt_Ioo
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g c : ℝ → F} {S : ℝ} (hS : 0 < S)
    (hg : ContinuousOn g (Set.Icc 0 S)) (hc : ContinuousOn c (Set.Icc 0 S))
    (h : ∀ t ∈ Set.Ioo 0 S, HasDerivAt g (c t) t) :
    HasDerivWithinAt g (c 0) (Set.Ici 0) 0 ∧
    (∀ C : ℝ, (∀ t ∈ Set.Ioo 0 S, ‖c t - c 0‖ ≤ C) →
      ∀ t ∈ Set.Icc 0 S, ‖g t - g 0 - t • c 0‖ ≤ C * t) := by
  -- `Ioo 0 S` is a right neighbourhood of `0`, and on it `deriv g` agrees with `c`; hence `c`
  -- has the limit `c 0` along `𝓝[>] 0`.
  have hmem : Set.Ioo (0 : ℝ) S ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hS]
    exact self_mem_nhdsWithin
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Icc 0 S] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hS]
    exact nhdsWithin_mono 0 Set.Ioo_subset_Icc_self
  have hct : Filter.Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 (c 0)) :=
    (hc.continuousWithinAt ⟨le_rfl, hS.le⟩).mono_left hle
  have hderiv_eq : (fun x => deriv g x) =ᶠ[𝓝[>] (0 : ℝ)] c := by
    filter_upwards [hmem] with x hx
    exact (h x hx).deriv
  -- First conjunct: right differentiability of `g` at `0`, with derivative the limit of `c`.
  have hdiff : DifferentiableOn ℝ g (Set.Ioo 0 S) :=
    fun x hx => (h x hx).differentiableAt.differentiableWithinAt
  have hcontW : ContinuousWithinAt g (Set.Ioo 0 S) (0 : ℝ) :=
    (hg.continuousWithinAt ⟨le_rfl, hS.le⟩).mono Set.Ioo_subset_Icc_self
  have hfirst : HasDerivWithinAt g (c 0) (Set.Ici 0) 0 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo 0 S) (a := (0 : ℝ)) (e := c 0)
      (f := g) hdiff hcontW hmem (Filter.Tendsto.congr' hderiv_eq.symm hct)
  refine ⟨hfirst, ?_⟩
  -- Second conjunct: the mean value inequality for `φ t = g t - g 0 - t • c 0`.
  intro C hC
  have hC0 : 0 ≤ C := by
    have ht : S / 2 ∈ Set.Ioo (0 : ℝ) S := ⟨by linarith, by linarith⟩
    have := hC (S / 2) ht
    linarith [norm_nonneg (c (S / 2) - c 0)]
  have hφcont : ContinuousOn (fun x : ℝ => g x - g 0 - x • c 0) (Set.Icc 0 S) :=
    (hg.sub continuousOn_const).sub (continuousOn_id.smul continuousOn_const)
  have hfun : ((g - fun _ : ℝ => g 0) - fun y : ℝ => y • c 0)
      = (fun y : ℝ => g y - g 0 - y • c 0) := by
    funext y; simp [Pi.sub_apply]
  have hφderiv : ∀ x ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt (fun y : ℝ => g y - g 0 - y • c 0) (c x - c 0) (Set.Ici x) x := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hxpos | hxeq
    · have h1 : HasDerivWithinAt g (c x) (Set.Ici x) x :=
        (h x ⟨hxpos, hx.2⟩).hasDerivWithinAt
      have h2 : HasDerivWithinAt (fun y : ℝ => y • c 0) (c 0) (Set.Ici x) x := by
        simpa using ((hasDerivAt_id x).smul_const (c 0)).hasDerivWithinAt
      have h3 := (h1.sub (hasDerivWithinAt_const x (Set.Ici x) (g 0))).sub h2
      rw [hfun] at h3
      simpa using h3
    · obtain rfl : x = 0 := hxeq.symm
      have h1 : HasDerivWithinAt (fun y : ℝ => y • c 0) (c 0) (Set.Ici (0 : ℝ)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c 0)).hasDerivWithinAt
      have h2 := (hfirst.sub (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) (g 0))).sub h1
      rw [hfun] at h2
      simpa using h2
  have hφbound : ∀ x ∈ Set.Ico (0 : ℝ) S, ‖c x - c 0‖ ≤ C := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with hxpos | hxeq
    · exact hC x ⟨hxpos, hx.2⟩
    · obtain rfl : x = 0 := hxeq.symm
      simpa using hC0
  intro t ht
  have hmain := norm_image_sub_le_of_norm_deriv_right_le_segment (a := (0 : ℝ)) (b := S)
    (f := fun y : ℝ => g y - g 0 - y • c 0) (f' := fun x => c x - c 0) (C := C)
    hφcont hφderiv hφbound t ht
  simpa using hmain

end Work.FTS.PressureOn.Connect.BoundaryTime
