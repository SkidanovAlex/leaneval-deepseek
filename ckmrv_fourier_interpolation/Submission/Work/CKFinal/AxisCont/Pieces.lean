/-
# Continuity of the two contour pieces of the CKMRV layer

`paperLayer = layerLow + layerTrunc + highPart` (`Work.Asymptotics.F2LayerDefs`).  This file
proves that `τ ↦ layerLow ℓ d τ r` is continuous at every point `τ₁` of the fundamental domain
`𝒟`, by dominated convergence over the contour `z = i t`.

* The integrand `τ ↦ Kaxis (Kfun ℓ d) τ t` is differentiable at every `τ` with
  `j τ ≠ j (i t)` (`Work.Asymptotics.differentiableAt_Kfun_tau`); for `τ₁ ∈ 𝒟` the exceptional
  `t`'s are at most the two orbit heights `Im τ₁` and `1 / Im τ₁`
  (`Work.CKFinal.finite_coincidenceSet_imagAxis`), hence a null set.
* The dominator on `(0,1]` is a constant: off the axis the contour is clean on a whole ball
  (`Work.CKFinal.jInvariantFun_ne_imagAxis_of_re_ne_zero`), and on the axis the two coincidence
  heights are removed, where `Work.Asymptotics.Kaxis_local_coincidence` bounds the kernel; the
  retained set is handled by `GapBoundKaxisLow` together with the cusp-`0` flatness
  (`Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded`).

NOTE (import hygiene).  The modules imported here are exactly the mutually compatible ones: the
`Kaxis_local_flat`/`KernelBoundAux` branch of the workspace cannot be imported together with the
`MiddleRange`/cusp-expansion branch (duplicate `Work.Asymptotics.continuous_scale`), so this file
deliberately uses `Kaxis_local_coincidence`, `GapBoundKaxisLow` and `Kaxis_cusp_of_bounded`.
-/
import Mathlib
import Submission.Work.CKFinal.AxisCont.Basic
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.Kaxis_bounded_compact
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.LayerCont.KaxisLowBound
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.LayerCont.GcuspHolomorphic
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.CKFinal.AxisCont

open MeasureTheory Filter Topology
open UpperHalfPlane Work.Kernels

/-! ## The contour parametrisation -/

/-- The contour point `i t` (the globally defined parametrisation of
`Submission/Work/Asymptotics/Kaxis_bounded_compact.lean`). -/
abbrev contourPt : ℝ → UpperHalfPlane := Work.Asymptotics.KbcAux.ct

private lemma continuousOn_contourPt_Icc {α β : ℝ} (hα : 0 < α) :
    ContinuousOn contourPt (Set.Icc α β) := by
  have h1 : ContinuousOn (fun t : ℝ => UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))
      (Set.Ioi 0) := UpperHalfPlane.continuousOn_ofComplex_I_mul
  refine (h1.mono ?_).congr ?_
  · intro t ht
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le hα (Set.mem_Icc.mp ht).1)
  · intro t _
    show Work.Asymptotics.KbcAux.ct t = UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))
    exact congrArg UpperHalfPlane.ofComplex (mul_comm (t : ℂ) Complex.I)

private lemma isCompact_contourPt_Icc {α β : ℝ} (hα : 0 < α) :
    IsCompact (contourPt '' Set.Icc α β) :=
  IsCompact.image_of_continuousOn isCompact_Icc (continuousOn_contourPt_Icc hα)

/-! ## The two pieces as indicator integrals over `(0,∞)` -/

private lemma layerLow_eq_indicator (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ)
    (τ : UpperHalfPlane) :
    Work.Asymptotics.layerLow ℓ d τ r
      = Work.Asymptotics.sinSq r * ∫ t, (Set.Ioc (0 : ℝ) 1).indicator
          (fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) t
        ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi (0 : ℝ) := fun y hy => Set.mem_Ioi.mpr hy.1
  rw [Work.Asymptotics.layerLow]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator (μ := volume.restrict (Set.Ioi (0 : ℝ))) measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hsub]

/-! ## The a.e. continuity of the integrand in `τ` -/

/-- A finite set is a.e. (for `volume` restricted to `(0,∞)`) avoided. -/
private lemma ae_notMem_finite {S : Set ℝ} (hS : S.Finite) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), t ∉ S := by
  have h : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ S := by
    rw [MeasureTheory.ae_iff]
    simpa using hS.measure_zero (volume : Measure ℝ)
  exact MeasureTheory.ae_restrict_of_ae h

/-- **A.e. continuity of `τ ↦ Kaxis (Kfun ℓ d) τ t` at a point of `𝒟`.**  For all `t > 0` outside
the (at most two) coincidence heights of `τ₁` the kernel is complex differentiable in `τ` at
`τ₁`; for `t ≤ 0` it is the constant `0`. -/
theorem ae_continuousAt_Kaxis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousAt (fun τ : UpperHalfPlane =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) τ₁ := by
  obtain ⟨S, hSfin, hS⟩ := Work.CKFinal.finite_coincidenceSet_imagAxis hτ₁
  filter_upwards [ae_notMem_finite hSfin] with t htS
  by_cases ht : 0 < t
  · have hJ : Work.Kernels.jInvariantFun τ₁ ≠ Work.Kernels.jInvariantFun
        (Work.Kernels.imagAxis t ht) := fun h => htS (hS t ht h)
    have hmd : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)) τ₁ :=
      UpperHalfPlane.mdifferentiableAt_iff.mpr
        (Work.Asymptotics.differentiableAt_Kfun_tau (d := d) hd
          (τ := τ₁) (z := Work.Kernels.imagAxis t ht) hJ)
    have hfun : (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
        = fun τ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht) := by
      funext τ
      simp only [Work.Kernels.Kaxis, dif_pos ht]
    rw [hfun]
    exact hmd.continuousAt
  · have hfun : (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
        = fun _ : UpperHalfPlane => (0 : ℂ) := by
      funext τ
      simp only [Work.Kernels.Kaxis, dif_neg ht]
    rw [hfun]
    exact continuousAt_const

/-! ## The low-range dominator -/

/-- **A bound on the low range `(0,1]` outside an open window `(a,b)`** (`b > 0`).  If the contour
is clean on `(0,1] ∖ (a,b)` for every `τ` of a compact set `K ⊆ 𝒟`, then the kernel is uniformly
bounded there. -/
theorem exists_bound_Kaxis_low_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {a b : ℝ} (hb : 0 < b)
    (hclean : ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → t ∉ Set.Ioo a b →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → t ∉ Set.Ioo a b →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δc, hδcpos, hcusp⟩ :=
    Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd (K := K) hK.isBounded
  obtain ⟨c, hcpos, hcb⟩ := hcusp 0 le_rfl
  set A : ℝ := min 1 a with hA
  have hA1 : A ≤ 1 := min_le_left _ _
  have hAa : A ≤ a := min_le_right _ _
  have hpiece1 : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ τ ∈ K, ∀ t : ℝ, 0 < t → t ≤ A →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C₁ := by
    by_cases hA0 : 0 < A
    · set δ : ℝ := min δc (A / 2) with hδdef
      have hδpos : 0 < δ := lt_min hδcpos (by linarith)
      have hδδc : δ ≤ δc := min_le_left _ _
      have hδA : δ ≤ A := le_trans (min_le_right _ _) (by linarith)
      obtain ⟨C₁, hC₁, hC₁b⟩ := Work.LayerCont.GapBoundKaxisLow ℓ d hd (K := K) hK
        (δ := δ) (T := A) hδpos
        (fun τ hτ t ht htI => hclean τ hτ t ht (le_trans htI.2 hA1)
          (fun hmem => absurd hmem.1 (not_lt.mpr (le_trans htI.2 hAa))))
      refine ⟨max c C₁, le_trans hcpos.le (le_max_left _ _), fun τ hτ t ht htA => ?_⟩
      by_cases htδ : t ≤ δ
      · refine le_trans (le_trans ?_ (le_max_left c C₁)) le_rfl
        simpa using hcb τ t hτ ht (le_trans htδ hδδc)
      · rw [not_le] at htδ
        exact le_trans (hC₁b τ t hτ ⟨htδ.le, htA⟩) (le_max_right c C₁)
    · rw [not_lt] at hA0
      exact ⟨c, hcpos.le, fun τ hτ t ht htA => absurd (le_trans htA hA0) (not_le.mpr ht)⟩
  obtain ⟨C₁, hC₁, hC₁b⟩ := hpiece1
  obtain ⟨C₂, hC₂, hC₂b⟩ := Work.LayerCont.GapBoundKaxisLow ℓ d hd (K := K) hK
    (δ := b) (T := 1) hb
    (fun τ hτ t ht htI => hclean τ hτ t ht htI.2
      (fun hmem => absurd hmem.2 (not_lt.mpr htI.1)))
  refine ⟨max (max c C₁) C₂, le_trans hC₁ (le_trans (le_max_right c C₁) (le_max_left _ _)),
    fun τ hτ t ht ht1 htnotin => ?_⟩
  rcases le_or_gt t A with h | h
  · exact le_trans (hC₁b τ hτ t ht h) (le_trans (le_max_right c C₁) (le_max_left _ _))
  · have hb' : b ≤ t := by
      by_contra hcon
      rw [not_le] at hcon
      have hat : a < t := by
        rcases le_or_gt a 1 with ha1 | ha1
        · rwa [hA, min_eq_right ha1] at h
        · exfalso
          rw [hA, min_eq_left ha1.le] at h
          linarith
      exact htnotin ⟨hat, hcon⟩
    exact le_trans (hC₂b τ t hτ ⟨hb', ht1⟩) (le_max_right _ _)

/-! ## Bounding the two coincidence windows of an axis point -/

private lemma abs_sub_le_of_mem_Icc {a b L U : ℝ} (ha : a ∈ Set.Icc L U)
    (hb : b ∈ Set.Icc L U) : |a - b| ≤ U - L := by
  rw [abs_sub_le_iff]
  exact ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩

private lemma one_sub_le_inv_one_add {σ : ℝ} (hσ0 : 0 ≤ σ) : 1 - σ ≤ (1 + σ)⁻¹ := by
  have h1 : 0 < 1 + σ := by linarith
  rw [inv_eq_one_div, le_div_iff₀ h1]
  nlinarith

/-- **The coincidence heights of a contour point below a small ball around `i y₁`.** -/
theorem coincidence_height_near {y₁ y t σ : ℝ} (hy₁ : 0 < y₁) (hy : 0 < y)
    (hσ : |y - y₁| ≤ σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 4) (ht : 0 < t) (ht1 : t ≤ 1)
    (hcoin : t = y ∨ t = y⁻¹) :
    |t - y₁| ≤ 8 * σ ∨ |t - y₁⁻¹| ≤ 8 * σ := by
  have hσ' := abs_le.mp hσ
  rcases le_or_gt y₁ 1 with h1 | h1
  · left
    rcases hcoin with h | h
    · rw [h]; linarith [hσ, hσ0]
    · rw [h]
      have hyge1 : 1 ≤ y := by
        have h2 : y⁻¹ ≤ 1 := by rw [← h]; exact ht1
        rwa [inv_le_one₀ hy] at h2
      have hyb : y ≤ 1 + σ := by linarith [hσ'.2, h1]
      have hy1ge : 1 - σ ≤ y₁ := by linarith [hσ'.2, hyge1]
      have hinv : y⁻¹ ∈ Set.Icc (1 - σ) 1 := by
        refine ⟨?_, (inv_le_one₀ hy).mpr hyge1⟩
        calc 1 - σ ≤ (1 + σ)⁻¹ := one_sub_le_inv_one_add hσ0
          _ ≤ y⁻¹ := inv_anti₀ (by linarith) hyb
      exact le_trans (abs_sub_le_of_mem_Icc hinv ⟨hy1ge, h1⟩) (by linarith)
  · right
    rcases hcoin with h | h
    · rw [h]
      have hy1 : y ≤ 1 := by rw [← h]; exact ht1
      have hyb : y₁ ≤ 1 + σ := by linarith [hσ'.1, hy1]
      have hyge : 1 - σ ≤ y := by linarith [hσ'.1, h1.le]
      have hinv : y₁⁻¹ ∈ Set.Icc (1 - σ) 1 := by
        refine ⟨?_, (inv_le_one₀ hy₁).mpr h1.le⟩
        calc 1 - σ ≤ (1 + σ)⁻¹ := one_sub_le_inv_one_add hσ0
          _ ≤ y₁⁻¹ := inv_anti₀ (by linarith) hyb
      refine le_trans (abs_sub_le_of_mem_Icc (a := y) (b := y₁⁻¹) ⟨hyge, hy1⟩ hinv) ?_
      linarith
    · rw [h]
      have hy : 0 < y := by linarith [hσ'.1, h1.le]
      have hyge : (3 : ℝ) / 4 ≤ y := by linarith [hσ'.1, h1.le, hσ1]
      have heq : y⁻¹ - y₁⁻¹ = (y₁ - y) / (y * y₁) := inv_sub_inv hy.ne' hy₁.ne'
      rw [heq, abs_div, abs_of_pos (mul_pos hy hy₁)]
      have hnum : |y₁ - y| ≤ σ := by rwa [abs_sub_comm]
      have hden : (3 : ℝ) / 4 ≤ y * y₁ := by nlinarith
      calc |y₁ - y| / (y * y₁) ≤ |y₁ - y| / ((3 : ℝ) / 4) :=
            div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
        _ ≤ σ / ((3 : ℝ) / 4) := div_le_div_of_nonneg_right hnum (by norm_num)
        _ ≤ 8 * σ := by
            rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4)]
            linarith

/-- **A bound on the low range `(0,1]` outside two open windows `(a,b)`, `(c,e)`** with
`a ≤ c`, `b ≤ e` and positive right endpoints.  The retained set is covered by the three pieces
`(0, min 1 a]`, `[b, min c 1]` and `[e,1]`, on each of which the contour is clean by hypothesis. -/
theorem exists_bound_Kaxis_low_clean_two (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane} (hK : IsCompact K) {a b c e : ℝ}
    (hb : 0 < b) (he : 0 < e) (hac : a ≤ c) (hbe : b ≤ e)
    (hclean : ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → t ∉ Set.Ioo a b →
      t ∉ Set.Ioo c e → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun
        (Work.Kernels.imagAxis t ht)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → t ∉ Set.Ioo a b →
      t ∉ Set.Ioo c e → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δc, hδcpos, hcusp⟩ :=
    Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd (K := K) hK.isBounded
  obtain ⟨c₀, hc₀pos, hc₀b⟩ := hcusp 0 le_rfl
  -- the three pieces
  have hP1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ K, ∀ t : ℝ, 0 < t → t ≤ min 1 a →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
    by_cases hA0 : 0 < min 1 a
    · set δ : ℝ := min δc (min 1 a / 2) with hδdef
      have hδpos : 0 < δ := lt_min hδcpos (by linarith)
      have hδδc : δ ≤ δc := min_le_left _ _
      have hδA : δ ≤ min 1 a := le_trans (min_le_right _ _) (by linarith)
      obtain ⟨C, hC, hCb⟩ := Work.LayerCont.GapBoundKaxisLow ℓ d hd (K := K) hK
        (δ := δ) (T := min 1 a) hδpos
        (fun τ hτ t ht htI => hclean τ hτ t ht (le_trans htI.2 (min_le_left _ _))
          (fun hmem => absurd hmem.1 (not_lt.mpr (le_trans htI.2 (min_le_right _ _))))
          (fun hmem => absurd hmem.1 (not_lt.mpr (le_trans htI.2 (le_trans (min_le_right _ _) hac)))))
      refine ⟨max c₀ C, le_trans hc₀pos.le (le_max_left _ _), fun τ hτ t ht htA => ?_⟩
      by_cases htδ : t ≤ δ
      · refine le_trans (le_trans ?_ (le_max_left c₀ C)) le_rfl
        simpa using hc₀b τ t hτ ht (le_trans htδ hδδc)
      · rw [not_le] at htδ
        exact le_trans (hCb τ t hτ ⟨htδ.le, htA⟩) (le_max_right c₀ C)
    · rw [not_lt] at hA0
      exact ⟨c₀, hc₀pos.le, fun τ hτ t ht htA => absurd (le_trans htA hA0) (not_le.mpr ht)⟩
  obtain ⟨C₁, hC₁, hC₁b⟩ := hP1
  obtain ⟨C₂, hC₂, hC₂b⟩ := Work.LayerCont.GapBoundKaxisLow ℓ d hd (K := K) hK
    (δ := b) (T := min c 1) hb
    (fun τ hτ t ht htI => hclean τ hτ t ht (le_trans htI.2 (min_le_right c 1))
      (fun hmem => absurd hmem.2 (not_lt.mpr htI.1))
      (fun hmem => absurd hmem.1 (not_lt.mpr (le_trans htI.2 (min_le_left c 1)))))
  obtain ⟨C₃, hC₃, hC₃b⟩ := Work.LayerCont.GapBoundKaxisLow ℓ d hd (K := K) hK
    (δ := e) (T := 1) he
    (fun τ hτ t ht htI => hclean τ hτ t ht htI.2
      (fun hmem => absurd hmem.2 (not_lt.mpr (le_trans hbe htI.1)))
      (fun hmem => absurd hmem.2 (not_lt.mpr htI.1)))
  refine ⟨max (max (max c₀ C₁) C₂) C₃,
    le_trans (le_trans (le_trans hc₀pos.le (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _),
    fun τ hτ t ht ht1 h1 h2 => ?_⟩
  rcases le_or_gt t (min 1 a) with h | h
  · exact le_trans (hC₁b τ hτ t ht h)
      (le_trans (le_max_right c₀ C₁) (le_trans (le_max_left _ _) (le_max_left _ _)))
  · have hb' : b ≤ t := by
      by_contra hcon
      rw [not_le] at hcon
      have hat : a < t := by
        rcases le_or_gt a 1 with ha1 | ha1
        · rwa [min_eq_right ha1] at h
        · exfalso
          rw [min_eq_left ha1.le] at h
          linarith
      exact h1 ⟨hat, hcon⟩
    by_cases htA₂ : t ≤ min c 1
    · exact le_trans (hC₂b τ t hτ ⟨hb', htA₂⟩)
        (le_trans (le_max_right (max c₀ C₁) C₂) (le_max_left (max (max c₀ C₁) C₂) C₃))
    · rw [not_le] at htA₂
      have he' : e ≤ t := by
        by_contra hcon
        rw [not_le] at hcon
        refine h2 ⟨?_, hcon⟩
        rcases le_or_gt c 1 with hc1 | hc1
        · rwa [min_eq_left hc1] at htA₂
        · exfalso
          rw [min_eq_right hc1.le] at htA₂
          linarith
      exact le_trans (hC₃b τ t hτ ⟨he', ht1⟩) (le_max_right (max (max c₀ C₁) C₂) C₃)

/-! ## The low-range dominator at a point of `𝒟` -/

/-- **The kernel is bounded on `(0,1]` by a constant, uniformly on a neighbourhood of a point of
`𝒟`.** -/
theorem exists_bound_Kaxis_low (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : UpperHalfPlane, dist τ τ₁ ≤ ε →
      ∀ t : ℝ, 0 < t → t ≤ 1 → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := (Metric.isOpen_iff.mp Work.Asymptotics.isOpen_DomainD τ₁) hτ₁
  have him : 0 < τ₁.im := τ₁.im_pos
  by_cases hre : τ₁.re = 0
  · -- the point is on the imaginary axis
    have hτ₁eq : τ₁ = Work.Kernels.imagAxis τ₁.im him :=
      Work.CKFinal.eq_imagAxis_of_re_eq_zero (by rwa [UpperHalfPlane.coe_re])
    have hcoin₁ : Work.Kernels.jInvariantFun τ₁ =
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis τ₁.im him) :=
      congrArg Work.Kernels.jInvariantFun hτ₁eq
    have hcoin₂ : Work.Kernels.jInvariantFun τ₁ =
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis τ₁.im⁻¹ (inv_pos.mpr him)) :=
      (congrArg Work.Kernels.jInvariantFun hτ₁eq).trans
        (Work.CKFinal.jInvariantFun_imagAxis_inv τ₁.im him).symm
    obtain ⟨r₁, hr₁, C₁, hC₁, hb₁⟩ :=
      Work.Asymptotics.Kaxis_local_coincidence ℓ d hd hτ₁ him hcoin₁
    obtain ⟨r₂, hr₂, C₂, hC₂, hb₂⟩ :=
      Work.Asymptotics.Kaxis_local_coincidence ℓ d hd hτ₁ (inv_pos.mpr him) hcoin₂
    set r : ℝ := min r₁ r₂ with hrdef
    have hrpos : 0 < r := lt_min hr₁ hr₂
    set σmax : ℝ := min (min (τ₁.im / 8) (1 / 8)) (r / 128) with hσmaxdef
    have hσmaxpos : 0 < σmax :=
      lt_min (lt_min (div_pos him (by norm_num)) (by norm_num)) (div_pos hrpos (by norm_num))
    set ε : ℝ := min (min (ε₀ / 2) (r / 2)) (Real.log (1 + σmax / (2 * τ₁.im))) with hεdef
    have hσpos : 0 < σmax / (2 * τ₁.im) := div_pos hσmaxpos (mul_pos (by norm_num) him)
    have hεpos : 0 < ε :=
      lt_min (lt_min (by linarith) (by linarith)) (Real.log_pos (by linarith))
    have hεε₀ : ε < ε₀ :=
      lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
    have hεr : ε < r :=
      lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
    have hsub : Metric.closedBall τ₁ ε ⊆ Work.Asymptotics.DomainD := fun τ hτ =>
      hε₀sub (Metric.closedBall_subset_ball hεε₀ hτ)
    set σ : ℝ := τ₁.im * (Real.exp ε - 1) with hσdef
    have hσle : σ ≤ σmax / 2 := by
      rw [hσdef]
      have h1 : Real.exp ε - 1 ≤ σmax / (2 * τ₁.im) := by
        have h2 : Real.exp ε ≤ 1 + σmax / (2 * τ₁.im) := by
          calc Real.exp ε ≤ Real.exp (Real.log (1 + σmax / (2 * τ₁.im))) :=
                Real.exp_le_exp.mpr (min_le_right _ _)
            _ = 1 + σmax / (2 * τ₁.im) := Real.exp_log (by linarith)
        linarith
      calc τ₁.im * (Real.exp ε - 1) ≤ τ₁.im * (σmax / (2 * τ₁.im)) :=
            mul_le_mul_of_nonneg_left h1 him.le
        _ = σmax / 2 := by field_simp
    have hσ0 : 0 ≤ σ := by
      rw [hσdef]
      exact mul_nonneg him.le (by linarith [Real.one_le_exp hεpos.le])
    have hσpos : 0 < σ := by
      rw [hσdef]
      refine mul_pos him ?_
      have := Real.exp_lt_exp.mpr hεpos
      rw [Real.exp_zero] at this
      linarith
    have hτinv : 0 < τ₁.im⁻¹ := inv_pos.mpr him
    have hσ1 : σ ≤ 1 / 4 := by
      have h2 : σmax ≤ 1 / 8 := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith [hσle, h2]
    have hσr : 16 * σ ≤ r / 4 := by
      have h2 : σmax ≤ r / 128 := min_le_right _ _
      linarith [hσle, h2]
    have hswath : ∀ (τ : UpperHalfPlane), dist τ τ₁ ≤ ε → τ.re = 0 → ∀ (t : ℝ) (ht : 0 < t),
        t ≤ 1 → Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun
          (Work.Kernels.imagAxis t ht) →
        |t - τ₁.im| ≤ 8 * σ ∨ |t - τ₁.im⁻¹| ≤ 8 * σ := by
      intro τ hτ hτre t ht ht1 hj
      have hτD : τ ∈ Work.Asymptotics.DomainD := hsub (Metric.mem_closedBall.mpr hτ)
      obtain ⟨-, hcoin⟩ := Work.CKFinal.eq_or_inv_of_jInvariantFun_eq_imagAxis hτD ht hj
      have hy : 0 < τ.im := τ.im_pos
      have hτeq : τ = Work.Kernels.imagAxis τ.im hy :=
        Work.CKFinal.eq_imagAxis_of_re_eq_zero (by rwa [UpperHalfPlane.coe_re])
      have hΔ : |τ.im - τ₁.im| ≤ σ := by
        have h0 := UpperHalfPlane.dist_coe_le τ τ₁
        have h1 : ‖(τ : ℂ) - (τ₁ : ℂ)‖ ≤ σ := by
          calc ‖(τ : ℂ) - (τ₁ : ℂ)‖ = dist (τ : ℂ) (τ₁ : ℂ) := by rw [dist_eq_norm]
            _ ≤ τ₁.im * (Real.exp (dist τ τ₁) - 1) := h0
            _ ≤ σ := by
                rw [hσdef]
                exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.mpr hτ]) him.le
        have h3 : ((Work.Kernels.imagAxis τ.im hy : ℍ) : ℂ) = (τ : ℂ) :=
          (congrArg (fun z : ℍ => (z : ℂ)) hτeq).symm
        have h4 : ((Work.Kernels.imagAxis τ₁.im him : ℍ) : ℂ) = (τ₁ : ℂ) :=
          (congrArg (fun z : ℍ => (z : ℂ)) hτ₁eq).symm
        have h5 : ‖(τ : ℂ) - (τ₁ : ℂ)‖ = |τ.im - τ₁.im| := by
          rw [← h3, ← h4]
          exact Work.CKFinal.norm_imagAxis_sub_imagAxis τ.im τ₁.im hy him
        rwa [h5] at h1
      rcases hcoin with h | h
      · exact coincidence_height_near him hy hΔ hσ0 hσ1 ht ht1 (Or.inl h)
      · refine coincidence_height_near him hy hΔ hσ0 hσ1 ht ht1 (Or.inr ?_)
        have hcomm : τ.im * t = 1 := by rw [mul_comm]; exact h
        exact eq_inv_of_mul_eq_one_right hcomm
    have hclean₂ : ∀ τ ∈ Metric.closedBall τ₁ ε, ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        t ∉ Set.Ioo (τ₁.im - 16 * σ) (τ₁.im + 16 * σ) →
        t ∉ Set.Ioo (τ₁.im⁻¹ - 16 * σ) (τ₁.im⁻¹ + 16 * σ) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun
          (Work.Kernels.imagAxis t ht) := by
      intro τ hτ t ht ht1 h1 h2 hj
      have hτD : τ ∈ Work.Asymptotics.DomainD := hsub hτ
      by_cases hτre : τ.re = 0
      · rcases hswath τ (Metric.mem_closedBall.mp hτ) hτre t ht ht1 hj with h | h
        · exact h1 ⟨by linarith [abs_le.mp h |>.1, hσpos], by linarith [abs_le.mp h |>.2, hσpos]⟩
        · exact h2 ⟨by linarith [abs_le.mp h |>.1, hσpos], by linarith [abs_le.mp h |>.2, hσpos]⟩
      · exact Work.CKFinal.jInvariantFun_ne_imagAxis_of_re_ne_zero hτD hτre t ht hj
    have hwin : ∀ τ : UpperHalfPlane, dist τ τ₁ ≤ ε → ∀ (p : ℝ),
        (p = τ₁.im ∨ p = τ₁.im⁻¹) → ∀ t : ℝ, 0 < t → |t - p| < r →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ max C₁ C₂ := by
      intro τ hτ p hp t ht hlt
      have hτD : τ ∈ Work.Asymptotics.DomainD := hsub (Metric.mem_closedBall.mpr hτ)
      have hεr₁ : ε < r₁ := lt_of_lt_of_le hεr (min_le_left _ _)
      have hεr₂ : ε < r₂ := lt_of_lt_of_le hεr (min_le_right _ _)
      rcases hp with h | h
      · subst h
        exact le_trans (hb₁ τ t hτD ht (lt_of_le_of_lt hτ hεr₁)
          (lt_of_lt_of_le hlt (min_le_left _ _))) (le_max_left _ _)
      · subst h
        exact le_trans (hb₂ τ t hτD ht (lt_of_le_of_lt hτ hεr₂)
          (lt_of_lt_of_le hlt (min_le_right _ _))) (le_max_right _ _)
    rcases le_or_gt τ₁.im τ₁.im⁻¹ with hle | hgt
    · obtain ⟨Cret, hCret, hCretb⟩ := exists_bound_Kaxis_low_clean_two ℓ d hd
        (K := Metric.closedBall τ₁ ε) (isCompact_closedBall τ₁ ε)
        (a := τ₁.im - 16 * σ) (b := τ₁.im + 16 * σ) (c := τ₁.im⁻¹ - 16 * σ)
        (e := τ₁.im⁻¹ + 16 * σ)
        (by linarith [hσ0]) (by linarith [hσ0]) (by linarith) (by linarith) hclean₂
      refine ⟨ε, hεpos, max Cret (max C₁ C₂), le_trans hCret (le_max_left _ _),
        fun τ hτ t ht ht1 => ?_⟩
      by_cases h1 : t ∈ Set.Ioo (τ₁.im - 16 * σ) (τ₁.im + 16 * σ)
      · exact le_trans (hwin τ hτ τ₁.im (Or.inl rfl) t ht
          (by rw [abs_lt]; exact ⟨by linarith [h1.1, hσr, hrpos, hτinv], by linarith [h1.2, hσr, hrpos, hτinv]⟩))
          (le_max_right _ _)
      by_cases h2 : t ∈ Set.Ioo (τ₁.im⁻¹ - 16 * σ) (τ₁.im⁻¹ + 16 * σ)
      · exact le_trans (hwin τ hτ τ₁.im⁻¹ (Or.inr rfl) t ht
          (by rw [abs_lt]; exact ⟨by linarith [h2.1, hσr, hrpos, hτinv], by linarith [h2.2, hσr, hrpos, hτinv]⟩))
          (le_max_right _ _)
      · exact le_trans (hCretb τ hτ t ht ht1 h1 h2) (le_max_left _ _)
    · obtain ⟨Cret, hCret, hCretb⟩ := exists_bound_Kaxis_low_clean_two ℓ d hd
        (K := Metric.closedBall τ₁ ε) (isCompact_closedBall τ₁ ε)
        (a := τ₁.im⁻¹ - 16 * σ) (b := τ₁.im⁻¹ + 16 * σ) (c := τ₁.im - 16 * σ)
        (e := τ₁.im + 16 * σ)
        (by linarith [hσ0]) (by linarith [hσ0]) (by linarith) (by linarith)
        (fun τ hτ t ht ht1 h1 h2 => hclean₂ τ hτ t ht ht1 h2 h1)
      refine ⟨ε, hεpos, max Cret (max C₁ C₂), le_trans hCret (le_max_left _ _),
        fun τ hτ t ht ht1 => ?_⟩
      by_cases h1 : t ∈ Set.Ioo (τ₁.im⁻¹ - 16 * σ) (τ₁.im⁻¹ + 16 * σ)
      · exact le_trans (hwin τ hτ τ₁.im⁻¹ (Or.inr rfl) t ht
          (by rw [abs_lt]; exact ⟨by linarith [h1.1, hσr, hrpos, hτinv], by linarith [h1.2, hσr, hrpos, hτinv]⟩))
          (le_max_right _ _)
      by_cases h2 : t ∈ Set.Ioo (τ₁.im - 16 * σ) (τ₁.im + 16 * σ)
      · exact le_trans (hwin τ hτ τ₁.im (Or.inl rfl) t ht
          (by rw [abs_lt]; exact ⟨by linarith [h2.1, hσr, hrpos, hτinv], by linarith [h2.2, hσr, hrpos, hτinv]⟩))
          (le_max_right _ _)
      · exact le_trans (hCretb τ hτ t ht ht1 h1 h2) (le_max_left _ _)
  · -- the point is off the imaginary axis: the contour is clean on the whole ball
    have hcoe : (τ₁ : ℂ).re ≠ 0 := by rwa [UpperHalfPlane.coe_re]
    set η : ℝ := |(τ₁ : ℂ).re| / (2 * τ₁.im) with hηdef
    have hηpos : 0 < η := div_pos (abs_pos.mpr hcoe) (by positivity)
    set ε : ℝ := min (ε₀ / 2) (Real.log (1 + η)) with hεdef
    have hεpos : 0 < ε := lt_min (by linarith) (Real.log_pos (by linarith))
    have hεε₀ : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsub : Metric.closedBall τ₁ ε ⊆ Work.Asymptotics.DomainD := fun τ hτ =>
      hε₀sub (Metric.closedBall_subset_ball hεε₀ hτ)
    have hoff : ∀ τ : UpperHalfPlane, dist τ τ₁ ≤ ε → τ.re ≠ 0 := by
      intro τ hτ hzero
      have h0 := UpperHalfPlane.dist_coe_le τ τ₁
      have h1 : ‖(τ : ℂ) - (τ₁ : ℂ)‖ ≤ τ₁.im * (Real.exp ε - 1) := by
        calc ‖(τ : ℂ) - (τ₁ : ℂ)‖ = dist (τ : ℂ) (τ₁ : ℂ) := by rw [dist_eq_norm]
          _ ≤ τ₁.im * (Real.exp (dist τ τ₁) - 1) := h0
          _ ≤ τ₁.im * (Real.exp ε - 1) :=
              mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.mpr hτ]) him.le
      have hexp : Real.exp ε - 1 ≤ η := by
        have h2 : Real.exp ε ≤ 1 + η := by
          calc Real.exp ε ≤ Real.exp (Real.log (1 + η)) := Real.exp_le_exp.mpr (min_le_right _ _)
            _ = 1 + η := Real.exp_log (by linarith)
        linarith
      have h3 : τ₁.im * (Real.exp ε - 1) ≤ τ₁.im * η := mul_le_mul_of_nonneg_left hexp him.le
      have h4 : τ₁.im * η = |(τ₁ : ℂ).re| / 2 := by
        rw [hηdef, mul_div_assoc', mul_comm τ₁.im |(τ₁ : ℂ).re|,
          mul_div_mul_right _ _ (ne_of_gt him)]
      have h5 : |((τ : ℂ) - (τ₁ : ℂ)).re| ≤ ‖(τ : ℂ) - (τ₁ : ℂ)‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h5
      have hz : (τ : ℂ).re = 0 := by rw [UpperHalfPlane.coe_re]; exact hzero
      rw [hz, zero_sub] at h5
      rw [abs_neg] at h5
      have h6 : 0 < |(τ₁ : ℂ).re| := abs_pos.mpr hcoe
      linarith
    have hclean : ∀ τ ∈ Metric.closedBall τ₁ ε, ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
        t ∉ Set.Ioo 2 3 → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun
          (Work.Kernels.imagAxis t ht) := by
      intro τ hτ t ht ht1 hnot
      exact Work.CKFinal.jInvariantFun_ne_imagAxis_of_re_ne_zero (hsub hτ)
        (hoff τ (Metric.mem_closedBall.mp hτ)) t ht
    obtain ⟨C, hC, hCb⟩ := exists_bound_Kaxis_low_clean ℓ d hd
      (K := Metric.closedBall τ₁ ε) (isCompact_closedBall τ₁ ε) (a := 2) (b := 3)
      (by norm_num) hclean
    exact ⟨ε, hεpos, C, hC, fun τ hτ t ht ht1 =>
      hCb τ hτ t ht ht1 (by intro hmem; linarith [hmem.1, ht1])⟩

/-! ## Continuity of the low piece -/

/-- **Dominated convergence for the low piece.** -/
theorem continuousAt_layerLow_of_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD)
    {ε C : ℝ} (hε : 0 < ε)
    (hC : ∀ τ : UpperHalfPlane, dist τ τ₁ ≤ ε → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C) :
    ContinuousAt (fun τ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d τ r) τ₁ := by
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCb : ∀ τ : UpperHalfPlane, dist τ τ₁ ≤ ε → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C' :=
    fun τ hτ t ht ht1 => le_trans (hC τ hτ t ht ht1) (le_max_left _ _)
  set F : UpperHalfPlane → ℝ → ℂ := fun τ t => (Set.Ioc (0 : ℝ) 1).indicator
      (fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) t with hF
  set bound : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator (fun _ => C') with hbound
  have hbint : Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [hbound]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    show Integrable (fun _ : ℝ => C')
      ((volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Ioc (0 : ℝ) 1))
    rw [Measure.restrict_restrict_of_subset (fun y hy => Set.mem_Ioi.mpr hy.1)]
    exact MeasureTheory.integrableOn_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hmeas : ∀ᶠ x in 𝓝 τ₁, AEStronglyMeasurable (F x) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall (fun x => by
      have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t) :=
        Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd x
      have h2 : Measurable (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
        fun_prop
      exact ((h1.mul h2).indicator measurableSet_Ioc).aestronglyMeasurable)
  have hbb : ∀ᶠ x in 𝓝 τ₁, ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖F x t‖ ≤ bound t := by
    filter_upwards [Metric.closedBall_mem_nhds τ₁ hε] with x hx
    filter_upwards with t
    rw [Metric.mem_closedBall] at hx
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · simp only [hF, hbound, Set.indicator_of_mem ht, norm_mul]
      have hK : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t‖ ≤ C' :=
        hCb x hx t ht.1 ht.2
      have he : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        have hre : (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))).re = -(Real.pi * r ^ 2 * t) := by
          have h1 : Real.pi * (r : ℂ) ^ 2 * (t : ℂ) = ((Real.pi * r ^ 2 * t : ℝ) : ℂ) := by
            push_cast
            ring
          rw [h1, Complex.neg_re, Complex.ofReal_re]
        rw [hre, Real.exp_le_one_iff]
        have hnn : 0 ≤ Real.pi * r ^ 2 * t :=
          mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht.1.le
        linarith
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t‖
            * ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ C' * 1 :=
            mul_le_mul hK he (norm_nonneg _) hC'0
        _ = C' := mul_one _
    · simp only [hF, hbound, Set.indicator_of_notMem ht, norm_zero]
      exact le_refl 0
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousAt (fun x : UpperHalfPlane => F x t) τ₁ := by
    filter_upwards [ae_continuousAt_Kaxis ℓ d hd hτ₁] with t ht
    rw [hF]
    by_cases hmem : t ∈ Set.Ioc (0 : ℝ) 1
    · have hfun : (fun x : UpperHalfPlane => (Set.Ioc (0 : ℝ) 1).indicator
          (fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) t)
          = fun x : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
        funext x
        exact Set.indicator_of_mem hmem _
      rw [hfun]
      exact ht.mul_const _
    · have hfun : (fun x : UpperHalfPlane => (Set.Ioc (0 : ℝ) 1).indicator
          (fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) x t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) t)
          = fun _ : UpperHalfPlane => (0 : ℂ) := by
        funext x
        exact Set.indicator_of_notMem hmem _
      rw [hfun]
      exact continuousAt_const
  have key : ContinuousAt
      (fun x : UpperHalfPlane => ∫ t, F x t ∂(volume.restrict (Set.Ioi (0 : ℝ)))) τ₁ :=
    MeasureTheory.continuousAt_of_dominated hmeas hbb hbint hae
  have hEq : (fun τ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d τ r)
      = fun τ : UpperHalfPlane =>
          Work.Asymptotics.sinSq r * ∫ t, F τ t ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
    funext τ
    rw [layerLow_eq_indicator ℓ d r τ, hF]
  rw [hEq]
  exact key.const_mul _

/-- **The low piece is continuous at every point of `𝒟`.** -/
theorem continuousAt_layerLow_of_mem_DomainD_self (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₁ : UpperHalfPlane} (hτ₁ : τ₁ ∈ Work.Asymptotics.DomainD) :
    ContinuousAt (fun τ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d τ r) τ₁ := by
  obtain ⟨ε, hε, C, hC, hCb⟩ := exists_bound_Kaxis_low ℓ d hd hτ₁
  exact continuousAt_layerLow_of_bound ℓ d hd r hτ₁ hε hCb

end Work.CKFinal.AxisCont
