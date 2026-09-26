/-
# The far-side (`Re τ > 1`) tail of the CKMRV layer

The library's cusp expansion of the kernel along the contour,
`Work.Asymptotics.cusp_expansion_of_kernel`, requires the parameter `τ` to lie in the fundamental
region `𝒟` (`Re τ < 1`), because the *middle* range `1 ≤ t ≤ T` of the contour is bounded there by
the classification of the coincidences `j τ = j (i t)` in `𝒟` (`τ = i t` or `τ = S·(i t)`), where
the kernel is nevertheless finite (the residue vanishes).

On the **far side** (`1 < Re τ`) the coincidences are simply *absent*: the web classification
(`Work.LayerCont.FarTail.clean_axis_of_web_re_gt_one`) shows that no `SL(2,ℤ)`-translate of `τ`
lies on the imaginary axis.  This file records the resulting hypothesis-free version of the two
statements: replace `K ⊆ 𝒟` by

  `hclean : ∀ τ ∈ K, ∀ t > 0, j τ ≠ j (i t)`.

The two ingredients are the same as in `cuspExpansionKernel`:

* `Work.Asymptotics.kernel_axis_bound` — the geometric decay
  `‖Kaxis - Aexp‖ ≤ C (1+t)^M e^{-π (t - T₀)}` for `t` beyond a threshold `T`, uniform on any
  compact `K` (no `𝒟`);
* the boundedness of `Kaxis - Aexp` on the compact *middle* range `K × [1, T]`, which needs the
  kernel's only singularities, the coincidences, to be absent — hence `hclean`
  (`Kaxis_le_on_compact_segment` here, and `Work.LayerCont.Aexp_compact_bound` for the model).

The resulting `tail_integrableOn_of_clean` is the far-side tail integrability consumed by the
first recurrence `T2op_layerWindowContinuation`.
-/
import Mathlib
import Submission.Work.LayerCont.Defs
import Submission.Work.LayerCont.TailIntegrable
import Submission.Work.LayerCont.AexpLow
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.LayerCont.TruncHolomorphy
import Submission.Work.Asymptotics.Kaxis_local_tail
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
import Submission.Work.Asymptotics.layer_vadd_ladder

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

/-- **Boundedness of the kernel on a compact contour segment avoiding the coincidences.**  If
`j τ ≠ j (i t)` for `t ∈ [δ,B]` and `τ ∈ K`, then `‖K^{(d)}(τ, i t)‖` is bounded on `K × [δ,B]`
uniformly in `τ ∈ K`.  (The compact version of
`Work.Asymptotics.Kaxis_le_on_segment`, which is stated for a single `τ`.) -/
theorem Kaxis_le_on_compact_segment (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {δ B : ℝ} (hδ : 0 < δ)
    (hclean : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ K → δ ≤ t → t ≤ B →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ (t : ℝ) (ht : 0 < t), δ ≤ t → t ≤ B →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
    ℓ d hd hK (Work.Asymptotics.isCompact_csegL hδ) (fun τ hτ z hz => by
      obtain ⟨t, ht, rfl⟩ := hz
      have ht0 : 0 < t := lt_of_lt_of_le hδ (Set.mem_Icc.mp ht).1
      rw [Work.Asymptotics.ctPointL_eq_imagAxis ht0]
      exact hclean τ t ht0 hτ (Set.mem_Icc.mp ht).1 (Set.mem_Icc.mp ht).2)
  refine ⟨M, hMpos, fun τ hτ t ht htδ htB => ?_⟩
  rw [Work.Kernels.Kaxis, dif_pos ht]
  exact hM τ hτ (Work.Kernels.imagAxis t ht) (by
    rw [← Work.Asymptotics.ctPointL_eq_imagAxis ht]
    exact Work.Asymptotics.ctPointL_mem_csegL (Set.mem_Icc.mpr ⟨htδ, htB⟩))

/-- **The far-side (clean) cusp expansion of the kernel along the contour.**

For a compact `K ⊆ ℍ` and a contour `(τ, i t)` (`τ ∈ K`, `t > 0`) free of coincidences
`j τ = j (i t)`, the kernel differs from its cusp model by `O((1+t)^M e^{-π t})`:

  `‖K^{(d)}(τ, i t) - 𝒢(τ, i t)‖ ≤ C (1+t)^M e^{-π (t - T₀)}`  for `t ≥ 1`,

uniformly in `τ ∈ K`. -/
theorem cusp_expansion_of_kernel_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hclean : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ K →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨Ck, Mk, Tk, hCk, hMk, hTk, hkb⟩ := Work.Asymptotics.kernel_axis_bound ℓ d hd hK
  have hT1 : (0 : ℝ) < max Tk 1 := lt_max_of_lt_left hTk
  obtain ⟨M₁, hM₁, hb₁⟩ := Kaxis_le_on_compact_segment ℓ d hd hK (δ := 1) (B := max Tk 1) one_pos
    (fun τ t ht hτ _ _ => hclean τ t ht hτ)
  obtain ⟨M₂, hM₂, hb₂⟩ := Work.LayerCont.Aexp_compact_bound ℓ d hd hK (T := max Tk 1)
  have hM₂' : (0 : ℝ) ≤ M₂ := hM₂
  refine ⟨max (M₁ + M₂) (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1), max Mk 0, max Tk 1,
    lt_max_of_lt_left (by positivity), le_max_right _ _, hT1.le, fun τ t hτ ht1 => ?_⟩
  rcases le_or_gt t (max Tk 1) with ht | ht
  · -- the compact middle range: the kernel and the model are bounded
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ M₁ := hb₁ τ hτ t ht0 ht1 ht
    have h2 : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ M₂ :=
      hb₂ τ hτ t (by rw [abs_of_nonneg (by linarith)]; exact ht)
    have h12 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ M₁ + M₂ :=
      add_le_add h1 h2
    refine le_trans (norm_sub_le _ _) (le_trans h12 ?_)
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have hA : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.one_le_rpow hw (by positivity)
    have hB : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - max Tk 1))) := by
      rw [Real.one_le_exp_iff]; nlinarith [Real.pi_pos]
    have hA0 : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hB0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - max Tk 1))) := (Real.exp_pos _).le
    have h3 : M₁ + M₂ ≤ (M₁ + M₂) * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) :=
      le_mul_of_one_le_right (by linarith) (by nlinarith [hA, hB, hA0, hB0])
    have h4 : M₁ + M₂ ≤ max (M₁ + M₂) (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) :=
      le_max_left _ _
    calc M₁ + M₂
        ≤ max (M₁ + M₂) (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) :=
          le_trans h3 (mul_le_mul_of_nonneg_right h4 (mul_nonneg hA0 hB0))
      _ = max (M₁ + M₂) (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - max Tk 1))) := by ring
  · -- beyond the threshold: the geometric decay
    have ht2 : max Tk 1 ≤ t := le_of_lt ht
    have ht3 : Tk ≤ t := le_trans (le_max_left _ _) ht2
    have hb := hkb τ hτ t ht3
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have h2 : (1 + t) ^ Mk ≤ (1 + t) ^ max Mk 0 :=
      Real.rpow_le_rpow_of_exponent_le hw (le_max_left _ _)
    have hexp : Real.exp (-(Real.pi * t))
        = Real.exp (-(Real.pi * (t - max Tk 1))) * Real.exp (-(Real.pi * max Tk 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h7 : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have h5 : (0 : ℝ) < Real.exp (-(Real.pi * (t - max Tk 1))) := Real.exp_pos _
    have h4 : (0 : ℝ) < Real.exp (-(Real.pi * max Tk 1)) := Real.exp_pos _
    have hB : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1))) :=
      mul_nonneg h7 h5.le
    refine le_trans hb ?_
    calc Ck * (1 + t) ^ Mk * Real.exp (-(Real.pi * t))
        = Ck * Real.exp (-(Real.pi * max Tk 1))
            * ((1 + t) ^ Mk * Real.exp (-(Real.pi * (t - max Tk 1)))) := by
          rw [hexp]; ring
      _ ≤ Ck * Real.exp (-(Real.pi * max Tk 1))
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_pos hCk h4).le
          exact mul_le_mul_of_nonneg_right h2 h5.le
      _ ≤ (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) := by
          refine mul_le_mul_of_nonneg_right (by linarith) hB
      _ ≤ max (M₁ + M₂) (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - max Tk 1))) := by
          calc (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1)
                * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1))))
              = (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
                  * Real.exp (-(Real.pi * (t - max Tk 1))) := by ring
            _ ≤ max (M₁ + M₂) (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
                  * Real.exp (-(Real.pi * (t - max Tk 1))) := by
                refine mul_le_mul_of_nonneg_right ?_ h5.le
                exact mul_le_mul_of_nonneg_right (le_max_right _ _) h7

/-- **Far-side tail integrability of the cusp-subtracted contour integrand.**

If the contour `t ↦ i t` (`t > 0`) carries no coincidence with `σ`, then
`(K^{(d)}(σ, i t) - 𝒢(σ, i t)) e^{-π r² t}` is integrable on `[1,∞)` — the hypothesis under which
`layerAt_eq_paperLayer` (and hence the first recurrence) is applied on the far side.
(`Work.Asymptotics.integrableOn_contour_trunc` has exactly this content with `Complex.exp` in
place of `gaussWeight`.) -/
theorem tail_integrableOn_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {σ : UpperHalfPlane} {r : ℝ}
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) := by
  simpa only [Work.Asymptotics.gaussWeight] using
    Work.Asymptotics.integrableOn_contour_trunc ℓ d hd σ hclean r

/-- **Tail integrability of the cusp-subtracted contour integrand on the `𝒟`-side.**

This is the companion of `tail_integrableOn_of_clean` in which the cleanliness is replaced by
membership in the fundamental region `𝒟` (the situation in which the library's cusp expansion
`Work.Asymptotics.cusp_expansion_of_kernel` applies).  It is what the first recurrence needs at
the two points `τ, τ+1` that lie on the `𝒟`-side of the chart ball. -/
theorem tail_integrableOn_of_mem_DomainD (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {σ : UpperHalfPlane} (hD : σ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) := by
  obtain ⟨C₂, M, T₀, hC₂pos, hMnn, hT₀nn, hbnd⟩ :=
    Work.Asymptotics.cusp_expansion_of_kernel ℓ d hd (K := {σ}) isCompact_singleton
      (by rintro x rfl; exact hD)
  have hdom : ∀ t : ℝ, 1 ≤ t →
      ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t‖
      ≤ (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
          * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
    intro t ht
    have hb := hbnd σ t (Set.mem_singleton σ) ht
    have hexp : Real.exp (-(Real.pi * (t - T₀)))
        = Real.exp (-(Real.pi * t)) * Real.exp (Real.pi * T₀) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [norm_mul, Work.LayerCont.norm_gaussWeight]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t‖
          * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ (C₂ * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
            * Real.exp (-(Real.pi * r ^ 2 * t)) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
            * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
          rw [hexp]; ring
  have hdomint : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (C₂ * Real.exp (Real.pi * T₀)) * ((1 + t) ^ M
        * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))))
      (Set.Ici (1 : ℝ)) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (1 + t) ^ M
        * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) (Set.Ici (1 : ℝ)) :=
      Work.LayerCont.TailIntegrable hMnn (by positivity)
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀))
        * ((1 + t) ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (Set.Ici (1 : ℝ)) :=
      hbase.const_mul (C₂ * Real.exp (Real.pi * T₀))
    refine h1.congr_fun ?_ measurableSet_Ici
    intro t _
    simp only
    rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
        = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
      rw [← Real.exp_add]; congr 1; ring]
  show MeasureTheory.Integrable _ (volume.restrict (Set.Ici (1 : ℝ)))
  refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => (C₂ * Real.exp (Real.pi * T₀))
      * ((1 + t) ^ M * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))))
    ?_ ?_ ?_
  · rw [← MeasureTheory.IntegrableOn]; exact hdomint
  · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd σ).sub
      (by unfold Work.Asymptotics.Aexp; fun_prop)).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hdom t ht

end Work.LayerCont.FarTail

