import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.tiltData_in_window

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open Work.Drive.Mono.Band

noncomputable section

/-!
# The thin-slab tilt data in a prescribed window, with the face regularity exported

`Work.Drive.Mono.tiltData_window_of_dir` (`Submission/Work/Drive/Mono/tiltData_in_window.lean`) is
`private`; its proof produces two conclusions that the public wrap
`Work.Drive.Mono.tiltData_in_window` discards: the thin-cut margin
`h + |u| < boxWidth s σ v` and, above all, the **face regularity** — at every point of the surface
inside the box whose tilted height is at one of the two face levels, the pulled-back slab functional
has a non-vanishing derivative.  This file re-runs the same proof as a public theorem and exports
both, together with the tilt genericity of `Work.Drive.Final.TiltedGenericity` and the fact that the
high and low faces are the two level sets `⟪v,·⟫ = ⟪v,c⟫ + u ± h`.

Nothing of the analytic content is new: the proof below is the proof of
`Work.Drive.Mono.tiltData_window_of_dir`, transcribed verbatim, with the internal conclusions
`hregA`, `hregB` (regularity of the height at the two face levels on the fundamental domain) consumed
at a last step that produces the face regularity at an arbitrary point of the surface.

The face regularity is exactly the `faceReg` conjunct of `Work.Drive.Mono.DataPackage`; it is the
missing link between the provable thin-slab analytic core and the geometric obligation
`Work.Drive.Mono.SweepGeomAEG`.
-/

/-- **The analytic core of the thin-slab band data in a prescribed window of half-widths, exporting
the thin-cut margin and the face regularity.**  At a prescribed orthonormal pair `v ⊥ n` (`n` a good
height direction) there are a half-width `h ∈ (A, B)`, a unit direction `nn` with `inner ℝ v nn = 0`
and `‖nn - n‖ < ρ`, and a finite exceptional set with the full tilt genericity; moreover the slab
cuts the box strictly (`h + |u| < boxWidth s σ v`) and the two faces of the slab meet the surface
transversally inside the box. -/
theorem tiltData_window_of_dir_export
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u A B ρ : ℝ) (v n : R3)
    (hA : 0 < A) (hAB : A < B) (hB : B ≤ boxWidth s σ v - |u|) (hρ : 0 < ρ)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hgood : HeightGood ψ n) :
    ∃ (h : ℝ) (nn : R3) (exc : Finset ℝ), A < h ∧ h < B ∧
      h + |u| < boxWidth s σ v ∧
      ‖nn - n‖ < ρ ∧ ‖nn‖ = 1 ∧ inner ℝ v nn = 0 ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) nn) exc ∧
      (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        z ∈ Submission.PBox s c σ →
        |inner ℝ v z - (inner ℝ v c + u)| = h →
        ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) := by
  classical
  -- ## 1. the adapted orthonormal basis of `v^⊥`: `n` has projective coordinate `1` in it
  obtain ⟨a₀, b₀, ha, hb, hab, hva, hvb, hnb⟩ := exists_adapted_basis hv1 hn1 hvn
  -- ## 2. an interval of good parameters `τ` around `1`
  have hgood1 : HeightGood ψ (dirOf 1 a₀ b₀) := by
    rw [dirOf_one ha hb hab hnb]; exact hgood
  obtain ⟨ρh, hρh0, hρhgood⟩ := heightGood_open ψ hgood1
  have hdene : ∀ τ : ℝ, ‖τ • a₀ + b₀‖ ≠ 0 := by
    intro τ
    have h1 : inner ℝ b₀ (τ • a₀ + b₀) = 1 := inner_b₀_add_dirOf ha hb hab τ
    intro h0
    rw [norm_eq_zero] at h0
    rw [h0, inner_zero_right] at h1
    exact one_ne_zero h1.symm
  have hcont : Continuous fun τ : ℝ => dirOf τ a₀ b₀ := by
    unfold dirOf
    exact ((continuous_norm.comp (by fun_prop)).inv₀ hdene).smul (by fun_prop)
  have hmix : {τ : ℝ | HeightGood ψ (dirOf τ a₀ b₀) ∧
      ‖dirOf τ a₀ b₀ - n‖ < ρ} ∈ nhds (1 : ℝ) := by
    have hev1 : ∀ᶠ τ in nhds (1 : ℝ), HeightGood ψ (dirOf τ a₀ b₀) := by
      have hev : ∀ᶠ τ in nhds (1 : ℝ), ‖dirOf τ a₀ b₀ - dirOf 1 a₀ b₀‖ < ρh :=
        hcont.continuousAt.eventually (Metric.ball_mem_nhds (dirOf 1 a₀ b₀) hρh0)
      filter_upwards [hev] with τ hτ
      exact hρhgood _ hτ
    have hev2 : ∀ᶠ τ in nhds (1 : ℝ), ‖dirOf τ a₀ b₀ - n‖ < ρ := by
      have hn' : n = dirOf 1 a₀ b₀ := (dirOf_one ha hb hab hnb).symm
      rw [hn']
      exact hcont.continuousAt.eventually (Metric.ball_mem_nhds (dirOf 1 a₀ b₀) hρ)
    exact hev1.and hev2
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp hmix
  have hgoodτ : ∀ τ : ℝ, |τ - 1| < δ → HeightGood ψ (dirOf τ a₀ b₀) := by
    intro τ hτ
    exact (hδ (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))).1
  have hcloseτ : ∀ τ : ℝ, |τ - 1| < δ → ‖dirOf τ a₀ b₀ - n‖ < ρ := by
    intro τ hτ
    exact (hδ (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))).2
  -- ## 3'. the window of half-widths is the prescribed interval `(A, B)`
  -- ## 4. the fundamental compact set and the null set of chart values
  set Kc : Set (ℝ × ℝ) := (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) ∩
    {p : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ)} with hKcdef
  have hKc : IsCompact Kc := by
    rw [hKcdef]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_closure.preimage (Work.BoxShrink.Pinch.par_continuous ψ))
  have hKN : ∀ N : ℕ, IsCompact (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|}) := by
    intro N
    refine hKc.inter_right ?_
    exact isClosed_le continuous_const (continuous_abs.comp (contDiff_betaV ψ v b₀).continuous)
  have hNull : ∀ N : ℕ, MeasureTheory.volume {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
        (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite} = 0 := by
    intro N
    refine chartSard_null ψ v a₀ b₀ (hKN N) ?_
    intro p hp
    have h1 : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
    exact abs_pos.mp (lt_of_lt_of_le h1 hp.2)
  set Nbad : Set (ℝ × ℝ) := ⋃ N : ℕ, {y : ℝ × ℝ |
      (((bandChart ψ v a₀ b₀) ⁻¹' {y}) ∩
        (Kc ∩ {p : ℝ × ℝ | ((N : ℝ) + 1)⁻¹ ≤ |betaV ψ v b₀ p|})).Infinite} with hNbaddef
  have hNbad0 : MeasureTheory.volume Nbad = 0 := by
    rw [hNbaddef]
    exact MeasureTheory.measure_iUnion_null hNull
  -- ## 5. the critical values of the height in the direction `v`
  set CV : Set ℝ := {y : ℝ | ∃ p : ℝ × ℝ, heightV ψ v p = y ∧ fderiv ℝ (heightV ψ v) p = 0}
    with hCVdef
  have hCV0 : MeasureTheory.volume CV = 0 := by
    rw [hCVdef]
    refine Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
      (contDiff_heightV ψ v) ?_ ?_
    · intro p
      show heightV ψ v (p.1 + 2 * Real.pi, p.2) = heightV ψ v p
      simp only [heightV]
      rw [par_add_two_pi_left ψ p]
    · intro p
      show heightV ψ v (p.1, p.2 + 2 * Real.pi) = heightV ψ v p
      simp only [heightV]
      rw [par_add_two_pi_right ψ p]
  -- ## 6. the avoidance
  obtain ⟨h, τ, hh1, hh2, hτ1, hτ2, hnoA, hnoB, hnoF1, hnoF2⟩ :=
    exists_window_avoiding hNbad0 hCV0 (a := inner ℝ v c + u) (hmin := A) (hmax := B)
      (tmin := 1 - δ) (tmax := 1 + δ) hAB (by linarith)
  -- ## 7. the final direction
  set nf : R3 := dirOf τ a₀ b₀ with hnfdef
  have hnf1 : ‖nf‖ = 1 := norm_dirOf ha hb hab τ
  have hvnf : inner ℝ v nf = 0 := inner_v_dirOf hva hvb τ
  have hgoodf : HeightGood ψ nf := hgoodτ τ (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
  have hclosen : ‖nf - n‖ < ρ := by
    rw [hnfdef]
    exact hcloseτ τ (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
  -- ## 8. regularity at the two face levels
  have hregA : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u + h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoA ⟨p, hval, hd⟩
  have hregB : ∀ p : ℝ × ℝ, p ∈ Kc → heightV ψ v p = inner ℝ v c + u - h →
      fderiv ℝ (heightV ψ v) p ≠ 0 := by
    intro p _ hval hd
    exact hnoB ⟨p, hval, hd⟩
  -- ## 9. the finiteness of the bad values
  have hfib1 := chartFibre_finite ψ v a₀ b₀ hv1 ha hb hab hva hvb hKc
    (y := (inner ℝ v c + u + h, τ)) hnoF1 hregA
  have hfib2 := chartFibre_finite ψ v a₀ b₀ hv1 ha hb hab hva hvb hKc
    (y := (inner ℝ v c + u - h, τ)) hnoF2 hregB
  have hbadfin : ({y : ℝ | ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
      |heightV ψ v p - (inner ℝ v c + u)| = h ∧
      inner ℝ (Work.Drive.Generic.crossE v nf)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 ∧
      heightIn ψ nf p = y}).Finite := by
    refine Set.Finite.subset ((hfib1.image (heightIn ψ nf)).union (hfib2.image (heightIn ψ nf))) ?_
    rintro y ⟨p, hpbox, hface, hcross, rfl⟩
    -- the fundamental representative of `p`
    obtain ⟨p₀, hp₀box, hp₀par, hp₀fd⟩ := fundamentalDomain_reduction ψ p
    have hp₀K : p₀ ∈ Kc := by
      rw [hKcdef]
      refine ⟨hp₀box, ?_⟩
      show Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ)
      rw [hp₀par]
      exact subset_closure hpbox
    have hnorm : Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p₀
        = Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p := by
      simp only [Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2]
      rw [hp₀fd]
    have hα : alphaV ψ v a₀ p₀ = alphaV ψ v a₀ p := by
      simp only [alphaV, projVv, projV, hnorm, hp₀fd]
    have hβ : betaV ψ v b₀ p₀ = betaV ψ v b₀ p := by
      simp only [betaV, projVv, projV, hnorm, hp₀fd]
    have hf0 : heightV ψ v p₀ = heightV ψ v p := by simp only [heightV, hp₀par]
    -- the projective coordinate is `τ`
    have hproj : projV (Work.BoxShrink.Pinch.par ψ) v p ≠ 0 := by
      intro h0
      have hd : fderiv ℝ (heightV ψ v) p = 0 := by
        have h := (fderiv_par_height_eq_zero_iff_projV ψ (v := v) hv1 p).mpr h0
        change fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p = 0
        exact h
      have habs : heightV ψ v p = inner ℝ v c + u + h ∨
          heightV ψ v p = inner ℝ v c + u - h := by
        have hlt : 0 < h := lt_trans hA hh1
        have := hface
        rw [abs_eq hlt.le] at this
        rcases this with h' | h'
        · left; linarith [h']
        · right; linarith [h']
      rcases habs with h' | h'
      · exact hnoA ⟨p, h'.symm ▸ rfl, hd⟩
      · exact hnoB ⟨p, h'.symm ▸ rfl, hd⟩
    have hbad := badPoint_chart ψ hv1 ha hb hab hva hvb (τ := τ) (p := p)
      (by simpa only [← hnfdef] using hcross) hproj
    have hratio : alphaV ψ v a₀ p / betaV ψ v b₀ p = τ := hbad.1
    have hb0' : betaV ψ v b₀ p ≠ 0 := hbad.2
    have hstep : ∀ z : ℝ, heightV ψ v p = z →
        bandChart ψ v a₀ b₀ p₀ = (z, τ) := by
      intro z hz
      show (heightV ψ v p₀, alphaV ψ v a₀ p₀ / betaV ψ v b₀ p₀) = (z, τ)
      rw [Prod.ext_iff]
      exact ⟨by rw [hf0, hz], by rw [hα, hβ, hratio]⟩
    have habs : heightV ψ v p = inner ℝ v c + u + h ∨
        heightV ψ v p = inner ℝ v c + u - h := by
      have hlt : 0 < h := lt_trans hA hh1
      have := hface
      rw [abs_eq hlt.le] at this
      rcases this with h' | h'
      · left; linarith [h']
      · right; linarith [h']
    rcases habs with h' | h'
    · refine Set.mem_union_left _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u + h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0'⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
    · refine Set.mem_union_right _ ?_
      have hmem : p₀ ∈ ((bandChart ψ v a₀ b₀) ⁻¹' {(inner ℝ v c + u - h, τ)}) ∩ Kc
          ∩ chartDomain ψ v b₀ := ⟨⟨hstep _ h', hp₀K⟩, by
            show betaV ψ v b₀ p₀ ≠ 0
            rw [hβ]; exact hb0'⟩
      rw [show heightIn ψ nf p = heightIn ψ nf p₀ from by
        show inner ℝ nf (Work.BoxShrink.Pinch.par ψ p)
          = inner ℝ nf (Work.BoxShrink.Pinch.par ψ p₀)
        rw [hp₀par]]
      exact Set.mem_image_of_mem _ hmem
  -- ## 10. the exceptional set
  have hcritfin : ({p : ℝ × ℝ | fderiv ℝ (heightIn ψ nf) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    Work.Drive.EpsForm.finite_critSet_box (heightIn_contDiff_two ψ nf) hgoodf.1
  -- ## 11. the four data conditions
  have hMorse : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf))) p) := by
    intro p _ hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h := hgoodf.1 p hcrit'
    rwa [Work.Drive.EpsForm.sweepHeight_innerSL]
  have hdistinct : ∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p' = 0 →
      (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p
        = (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p' →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' := by
    intro p p' _ _ hcrit hcrit' hval
    have h1 : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    have h2 : fderiv ℝ (heightIn ψ nf) p' = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit'
    have h3 : heightIn ψ nf p = heightIn ψ nf p' := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hval
    exact hgoodf.2 p p' h1 h2 h3
  have hcritMem : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) nf)) p = 0 →
      (innerSL ℝ) nf (Work.BoxShrink.Pinch.par ψ p) ∈
        hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset := by
    intro p hpbox hcrit
    have hcrit' : fderiv ℝ (heightIn ψ nf) p = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hcrit
    obtain ⟨p₀, hp₀box, hp₀crit, hp₀par⟩ :=
      Work.Drive.EpsForm.exists_fundamental_of_crit ψ (innerSL ℝ nf) hcrit
    have hp₀crit' : fderiv ℝ (heightIn ψ nf) p₀ = 0 := by
      rwa [Work.Drive.EpsForm.sweepHeight_innerSL] at hp₀crit
    have hmem : p₀ ∈ hcritfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hp₀crit', hp₀box⟩
    have hval : heightIn ψ nf p₀ ∈ hcritfin.toFinset.image (heightIn ψ nf) :=
      Finset.mem_image.mpr ⟨p₀, hmem, rfl⟩
    exact Finset.mem_union_left _ (by simpa only [innerSL_apply_apply, ← hp₀par] using hval)
  have hface : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      inner ℝ (Work.Drive.Generic.crossE v nf)
        (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) = 0 →
      (innerSL ℝ) nf (Work.BoxShrink.Pinch.par ψ p) ∈
        hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset := by
    intro p hpbox hfacept hcross
    refine Finset.mem_union_right _ ?_
    rw [hbadfin.mem_toFinset]
    exact ⟨p, hpbox, hfacept, hcross, rfl⟩

  have hfaceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
    intro z hzcarrier hzbox hzlevel
    rw [Work.BoxShrink.Pinch.carrier_eq_range] at hzcarrier
    obtain ⟨p, hp⟩ := hzcarrier
    obtain ⟨p₀, hp₀mem, hp₀par, _⟩ := fundamentalDomain_reduction ψ p
    have hp₀K : p₀ ∈ Kc := by
      rw [hKcdef]
      refine ⟨hp₀mem, ?_⟩
      show Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ)
      rw [hp₀par, hp]
      exact subset_closure hzbox
    have hzlevel' : |heightV ψ v p₀ - (inner ℝ v c + u)| = h := by
      simp only [heightV]
      rw [hp₀par, hp]
      exact hzlevel
    have habs : heightV ψ v p₀ = inner ℝ v c + u + h ∨
        heightV ψ v p₀ = inner ℝ v c + u - h := by
      have hlt : 0 < h := lt_trans hA hh1
      have h := hzlevel'
      rw [abs_eq hlt.le] at h
      rcases h with h' | h'
      · left; linarith
      · right; linarith
    refine ⟨p₀, by rw [hp₀par, hp], ?_⟩
    rcases habs with h' | h'
    · exact hregA p₀ hp₀K h'
    · exact hregB p₀ hp₀K h'
  refine ⟨h, nf, hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset,
    hh1, hh2, ?_, hclosen, hnf1, hvnf, ?_, hfaceReg⟩
  · have h3 : h < boxWidth s σ v - |u| := lt_of_lt_of_le hh2 hB
    linarith
  · exact Work.Drive.Mono.Band.tiltedGenericity_of_data ψ s c σ u v nf h
      (hcritfin.toFinset.image (heightIn ψ nf) ∪ hbadfin.toFinset)
      hv1 hnf1 hvnf hMorse hdistinct hcritMem hface

/-- **The thin-slab tilt data in a prescribed window of half-widths, with the face regularity and
the thin-cut margin exported** (project lead, `Mono/NOTES_LEAD_junctionGen.md`, child E of §6.4).

This is the *already proved* core `Work.Drive.Mono.tiltData_window_of_dir`
(`Submission/Work/Drive/Mono/tiltData_in_window.lean`, a `private` declaration) with two of its
internal conclusions exported instead of being consumed on the spot:

* `h + |u| < Work.Drive.Mono.boxWidth s σ v` — the thin-cut margin, which gives
  `Work.Drive.Mono.SlabCutsBox` through `Work.Drive.Mono.slabCutsBox_of_width`;
* the **face regularity**: at every point of the surface inside the box at the two face levels
  `⟪v,·⟫ = ⟪v,c⟫ + u ± h` the pulled-back slab functional has non-vanishing derivative.  This is
  exactly the `faceReg` conjunct of `Work.Drive.Mono.DataPackage` (the slab faces meet the surface
  transversally in the box), which the junction route's local models need;
* the tilt genericity `Work.Drive.Final.TiltedGenericity` at the produced `(h, nn)`.

The conclusion is otherwise that of `Work.Drive.Mono.tiltData_in_window`: a half-width
`h ∈ (hmin, hmax)`, a unit direction `nn ⊥ v` with `‖nn - n‖ < ρ`, and a finite exceptional set. -/
theorem tiltData_in_window_export
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u r : ℝ) (v n : R3)
    (hmin hmax ρ : ℝ)
    (hr : 0 < r) (hrs : r < s) (hu : |u| < Submission.eps * r)
    (hhmin : 0 < hmin) (hlt : hmin < hmax)
    (hmaxcut : hmax ≤ Work.Drive.Mono.boxWidth s σ v - |u|)
    (hnudge : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s)
      < Work.Drive.Mono.boxWidth s σ v - |u|)
    (hρ : 0 < ρ)
    (hv1 : ‖v‖ = 1) (hn1 : ‖n‖ = 1) (hvn : inner ℝ v n = 0)
    (hgood : Work.Drive.Mono.Band.HeightGood ψ n)
    (hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8) :
    ∃ (h : ℝ) (nn : R3) (exc : Finset ℝ), hmin < h ∧ h < hmax ∧
      h + |u| < Work.Drive.Mono.boxWidth s σ v ∧
      ‖nn - n‖ < ρ ∧ ‖nn‖ = 1 ∧ inner ℝ v nn = 0 ∧
      Work.Drive.Final.TiltedGenericity ψ s c σ u v h ((innerSL ℝ) nn) exc ∧
      (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        z ∈ Submission.PBox s c σ →
        |inner ℝ v z - (inner ℝ v c + u)| = h →
        ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) := by
  exact tiltData_window_of_dir_export ψ s c σ u hmin hmax ρ v n
    hhmin hlt hmaxcut hρ hv1 hn1 hvn hgood

end

end Work.Drive.Mono
