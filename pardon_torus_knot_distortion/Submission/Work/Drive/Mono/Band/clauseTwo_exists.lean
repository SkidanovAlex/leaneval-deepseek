import Mathlib
import Submission.Work.Drive.Mono.Band.ae_finite_preimage
import Submission.Work.Drive.Mono.Band.ae_finite_preimage_open
import Submission.Work.Drive.Mono.Band.badPoint_projNormal
import Submission.Work.Drive.Mono.Band.exists_param_avoiding
import Submission.Work.Drive.Mono.Band.fundamentalDomain_reduction
import Submission.Work.Drive.Mono.Band.BadFaceDefs
import Submission.Work.Drive.Mono.Band.noTangency_data
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.ThinWidth.exists_window_regular

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

/-! ## Auxiliary facts: periodicity of the parametrisation, and chain rules -/

/-- `par ψ` is `2π`-periodic in the first variable. -/
theorem par_add_two_pi_left (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (p.1 + 2 * Real.pi, p.2) = Work.BoxShrink.Pinch.par ψ p := by
  simp only [Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def]
  rw [Work.Core.torusMap_add_two_pi_left]

/-- `par ψ` is `2π`-periodic in the second variable. -/
theorem par_add_two_pi_right (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (p.1, p.2 + 2 * Real.pi) = Work.BoxShrink.Pinch.par ψ p := by
  simp only [Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def]
  rw [Work.Core.torusMap_add_two_pi_right]

/-- The chain rule for the height functional composed with the parametrisation. -/
theorem fderiv_inner_par_eq (ψ : Submission.Diffeo) (w : R3) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ w (Work.BoxShrink.Pinch.par ψ q)) p
      = (innerSL ℝ w).comp (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  exact Work.Drive.Generic.fderiv_height_eq (par_contDiff_three ψ) w p y

/-- The derivative of the height functional is invariant under the periodicity of `par ψ`. -/
theorem fderiv_inner_par_congr (ψ : Submission.Diffeo) (w : R3) {p p' : ℝ × ℝ}
    (h : fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p' = fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ w (Work.BoxShrink.Pinch.par ψ q)) p'
      = fderiv ℝ (fun q : ℝ × ℝ => inner ℝ w (Work.BoxShrink.Pinch.par ψ q)) p := by
  rw [fderiv_inner_par_eq, fderiv_inner_par_eq, h]

/-- **An orthonormal pair orthogonal to a unit vector `v` in `ℝ³`.** -/
theorem exists_orthonormal_perp {v : R3} (hv : ‖v‖ = 1) :
    ∃ a b : R3, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ inner ℝ a b = 0 ∧ inner ℝ v a = 0 ∧ inner ℝ v b = 0 := by
  have hv0 : v ≠ 0 := by intro h; rw [h] at hv; simp at hv
  have hne : (Submodule.span ℝ ({v} : Set R3))ᗮ ≠ ⊥ := by
    intro hbot
    have hdim := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({v} : Set R3))
    have h1 : Module.finrank ℝ (Submodule.span ℝ ({v} : Set R3)) = 1 :=
      finrank_span_singleton hv0
    have h2 : Module.finrank ℝ R3 = 3 := by
      simpa using finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 3)
    rw [hbot, h1, h2] at hdim
    have hz : Module.finrank ℝ (⊥ : Submodule ℝ R3) = 0 := (Submodule.finrank_eq_zero).mpr rfl
    rw [hz] at hdim
    omega
  obtain ⟨z, hzmem, hzne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hzv : inner ℝ v z = 0 :=
    (Submodule.mem_orthogonal (Submodule.span ℝ ({v} : Set R3)) z).mp hzmem v
      (Submodule.subset_span (by simp))
  set a : R3 := (‖z‖)⁻¹ • z with ha
  have ha1 : ‖a‖ = 1 := norm_smul_inv_norm hzne
  have hva' : inner ℝ v a = 0 := by rw [ha, inner_smul_right, hzv, mul_zero]
  have hb1 : ‖Work.Drive.Generic.crossE v a‖ = 1 := norm_crossE hv ha1 hva'
  refine ⟨a, Work.Drive.Generic.crossE v a, ha1, hb1, ?_, hva', ?_⟩
  · exact Work.Drive.Generic.inner_crossE_right v a
  · exact Work.Drive.Generic.inner_crossE_left v a


/-! ## The main statement -/

/-- **Clause (ii) of the thin-slab genericity, with the wall normal chosen jointly with the
half-width.** -/
theorem clauseTwo_exists
    (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : LeanEval.KnotTheory.PardonDistortion.R3) (hv1 : ‖v‖ = 1)
    (hmin hmax : ℝ) (hlt : hmin < hmax) :
    ∃ (n : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ) (exc : Finset ℝ),
      ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ hmin < h ∧ h < hmax ∧
      (∀ lam : ℝ, lam ∉ (exc : Set ℝ) → ∀ p : ℝ × ℝ,
        Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
        (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p = lam →
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) := by
  obtain ⟨a, b, ha1, hb1, hab, hva, hvb⟩ := exists_orthonormal_perp hv1
  -- ### 1. the height in the direction `v`, its critical values, and the periodicity
  have hG3 : ContDiff ℝ 3 (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) := by
    have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => (innerSL ℝ v) (Work.BoxShrink.Pinch.par ψ p)) :=
      (ContinuousLinearMap.contDiff (innerSL ℝ v)).comp (par_contDiff_three ψ)
    simpa only [innerSL_apply_apply] using h1
  have hG2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) :=
    hG3.of_le (by decide)
  have hGcont : Continuous (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) :=
    hG2.continuous
  have hGper1 : ∀ p : ℝ × ℝ,
      (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) (p.1 + 2 * Real.pi, p.2)
        = (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) p := by
    intro p; simpa only [par_add_two_pi_left]
  have hGper2 : ∀ p : ℝ × ℝ,
      (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) (p.1, p.2 + 2 * Real.pi)
        = (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) p := by
    intro p; simpa only [par_add_two_pi_right]
  have hN₀ : MeasureTheory.volume {u' : ℝ | ∃ p : ℝ × ℝ,
      (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) p = u' ∧
      fderiv ℝ (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) p = 0} = 0 :=
    Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic hG2 hGper1 hGper2
  -- ### 2. the compact box-region inside the fundamental square
  set Kc : Set (ℝ × ℝ) := {q : ℝ × ℝ | q ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi) ∧
    Work.BoxShrink.Pinch.par ψ q ∈ closure (Submission.PBox s c σ)} with hKc
  have hKc_comp : IsCompact Kc := by
    have h1 : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      isCompact_Icc.prod isCompact_Icc
    have h2 : IsClosed {p : ℝ × ℝ |
        Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ)} :=
      isClosed_closure.preimage (Work.Smooth.Morse.param_continuous ψ)
    exact hKc ▸ h1.inter_right h2
  -- ### 3. the projection of the Gauss normal, the slope chart and the map `Ω`
  set proj : ℝ × ℝ → R3 := fun p => Work.Drive.Mono.Band.projV (Work.BoxShrink.Pinch.par ψ) v p
    with hproj
  set dir : ℝ × ℝ → ℝ := fun p => inner ℝ a (proj p) / inner ℝ b (proj p) with hdir
  set Ω : ℝ × ℝ → ℝ × ℝ :=
    fun p => (inner ℝ v (Work.BoxShrink.Pinch.par ψ p), dir p) with hΩ
  set V : Set (ℝ × ℝ) := {q : ℝ × ℝ | inner ℝ b (proj q) ≠ 0} with hV
  have hproj2 : ContDiff ℝ 2 proj := by
    rw [hproj]; exact contDiff_projV (par_contDiff_three ψ) v
  have hprojcont : Continuous proj := hproj2.continuous
  have hY2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => inner ℝ b (proj p)) := by
    have h1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => (innerSL ℝ b) (proj p)) :=
      (ContinuousLinearMap.contDiff (innerSL ℝ b)).comp hproj2
    simpa only [innerSL_apply_apply] using h1
  have hYcont : Continuous (fun p : ℝ × ℝ => inner ℝ b (proj p)) := hY2.continuous
  have hopenV : IsOpen V := by
    rw [hV]; exact isOpen_ne.preimage hYcont
  have hΩcd : ContDiffOn ℝ 1 Ω V := by
    have h1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)) V :=
      hG2.contDiffOn.of_le (by decide)
    have h2 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => inner ℝ a (proj p)) V := by
      have h : ContDiff ℝ 2 (fun p : ℝ × ℝ => (innerSL ℝ a) (proj p)) :=
        (ContinuousLinearMap.contDiff (innerSL ℝ a)).comp hproj2
      have h' : ContDiff ℝ 2 (fun p : ℝ × ℝ => inner ℝ a (proj p)) := by
        simpa only [innerSL_apply_apply] using h
      exact h'.contDiffOn.of_le (by decide)
    have h3 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => inner ℝ b (proj p)) V :=
      hY2.contDiffOn.of_le (by decide)
    have hmain : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        (inner ℝ v (Work.BoxShrink.Pinch.par ψ p),
         inner ℝ a (proj p) / inner ℝ b (proj p))) V :=
      h1.prodMk (h2.div h3 (fun p hp => by rw [hV] at hp; exact hp))
    rw [hΩ]
    exact hmain
  -- ### 4. the compact exhaustion of the chart region and the exceptional set
  set Km : ℕ → Set (ℝ × ℝ) := fun m => Kc ∩
    {q : ℝ × ℝ | 1 / ((m : ℝ) + 1) ≤ |inner ℝ b (proj q)|} with hKm
  have hKm_comp : ∀ m : ℕ, IsCompact (Km m) := by
    intro m
    rw [hKm]
    exact hKc_comp.inter_right
      (isClosed_le continuous_const (continuous_abs.comp hYcont))
  have hKm_sub : ∀ m : ℕ, Km m ⊆ V := by
    intro m p hp
    rw [hV]
    rw [hKm] at hp
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hp
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    intro h0
    rw [h0, abs_zero] at hp
    linarith [hp.2]
  set S : Set (ℝ × ℝ) :=
    ⋃ m : ℕ, {y : ℝ × ℝ | (Ω ⁻¹' {y} ∩ Km m).Infinite} with hS
  have hS_null : MeasureTheory.volume S = 0 := by
    rw [hS]
    exact MeasureTheory.measure_iUnion_null (fun m =>
      ae_finite_preimage_open hopenV hΩcd (hKm_comp m) (hKm_sub m))
  -- ### 5. the choice of the half-width and of the slope of the wall normal
  obtain ⟨h, t, hhmin, hhmax, hNa, hNb, hSa, hSb⟩ :=
    exists_param_avoiding (a := inner ℝ v c + u) hS_null hN₀ hlt
  -- ### 6. the wall normal determined by the slope `t`
  have hsqrt_pos : 0 < Real.sqrt (t ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_ne : Real.sqrt (t ^ 2 + 1) ≠ 0 := ne_of_gt hsqrt_pos
  set n : R3 := (Real.sqrt (t ^ 2 + 1))⁻¹ • (t • a + b) with hn
  have hNa₁ : inner ℝ a (t • a + b) = t := by
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha1, hab]
    ring
  have hNb₁ : inner ℝ b (t • a + b) = 1 := by
    rw [inner_add_right, real_inner_smul_right, real_inner_comm a b, hab,
      real_inner_self_eq_norm_sq, hb1]
    ring
  have hNv₁ : inner ℝ v (t • a + b) = 0 := by
    rw [inner_add_right, real_inner_smul_right, hva, hvb]; ring
  have hNself : inner ℝ (t • a + b) (t • a + b) = t ^ 2 + 1 := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hab, real_inner_comm a b, hab,
      ha1, hb1]
    ring
  have hNnorm : ‖t • a + b‖ = Real.sqrt (t ^ 2 + 1) := by
    have h2 : ‖t • a + b‖ ^ 2 = (Real.sqrt (t ^ 2 + 1)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity), ← real_inner_self_eq_norm_sq, hNself]
    nlinarith [norm_nonneg (t • a + b), Real.sqrt_nonneg (t ^ 2 + 1)]
  have hn1 : ‖n‖ = 1 := by
    rw [hn, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos), hNnorm,
      inv_mul_cancel₀ hsqrt_ne]
  have hvn : inner ℝ v n = 0 := by
    rw [hn, inner_smul_right, hNv₁, mul_zero]
  have han : inner ℝ a n = t * (Real.sqrt (t ^ 2 + 1))⁻¹ := by
    rw [hn, inner_smul_right, hNa₁, mul_comm]
  have hbn : inner ℝ b n = (Real.sqrt (t ^ 2 + 1))⁻¹ := by
    rw [hn, inner_smul_right, hNb₁, mul_one]
  -- ### 7. the bad points of the two faces, in the fundamental square
  set BadK : Set (ℝ × ℝ) := {q : ℝ × ℝ | q ∈ Kc ∧
    |inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u)| = h ∧
    ∃ t' : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) q = t' •
      fderiv ℝ (fun r : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ r)) q} with hBadK
  have hsw : ∀ p : ℝ × ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p
      = fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro p; rw [Work.Drive.EpsForm.sweepHeight_innerSL]
  have hproj_expl : ∀ p : ℝ × ℝ, proj p =
      Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p
        - inner ℝ v (Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) p) • v := by
    intro p
    rw [hproj]
    rfl
  have hbad_span : BadK ⊆ {q : ℝ × ℝ | proj q ∈ Submodule.span ℝ ({n} : Set R3)} := by
    intro p hp
    obtain ⟨t', ht'⟩ := hp.2.2
    rw [hsw p] at ht'
    obtain ⟨c', hc'0, hc'⟩ := badPoint_projNormal ψ hv1 hn1 hvn ht'
    simp only [Set.mem_setOf_eq]
    rw [hproj_expl p, hc']
    exact Submodule.smul_mem _ c' (Submodule.mem_span_singleton_self n)
  have hdir_bad : ∀ p : ℝ × ℝ, p ∈ BadK → dir p = t := by
    intro p hp
    obtain ⟨t', ht'⟩ := hp.2.2
    rw [hsw p] at ht'
    obtain ⟨c', hc'0, hc'⟩ := badPoint_projNormal ψ hv1 hn1 hvn ht'
    have h1 : inner ℝ a (proj p) = c' * (t * (Real.sqrt (t ^ 2 + 1))⁻¹) := by
      rw [hproj_expl p, hc', inner_smul_right, han]
    have h2 : inner ℝ b (proj p) = c' * (Real.sqrt (t ^ 2 + 1))⁻¹ := by
      rw [hproj_expl p, hc', inner_smul_right, hbn]
    simp only [hdir]
    rw [h1, h2]
    rw [mul_div_mul_left _ _ hc'0]
    field_simp
  have hreg : ∀ p : ℝ × ℝ,
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h → proj p ≠ 0 := by
    intro p hp h0
    have hdG : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p = 0 :=
      (fderiv_par_height_eq_zero_iff_projV ψ hv1 p).mpr (by simpa only [hproj] using h0)
    have hh0 : 0 ≤ h := by rw [← hp]; exact abs_nonneg _
    rcases (abs_eq hh0).mp hp with h1 | h1
    · exact hNa ⟨p, by linarith, hdG⟩
    · exact hNb ⟨p, by linarith, hdG⟩
  have hBadK_fin : BadK.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    let e : ℕ ↪ BadK := Set.Infinite.natEmbedding BadK hinf
    have hxK : ∀ k : ℕ, ((e k : BadK) : ℝ × ℝ) ∈ Kc := fun k => (e k).2.1
    obtain ⟨pstar, hpstarK, φ, hφmono, hφtend⟩ := hKc_comp.tendsto_subseq hxK
    have hlev_closed : IsClosed {q : ℝ × ℝ |
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u)| = h} :=
      isClosed_eq (continuous_abs.comp (hGcont.sub continuous_const)) continuous_const
    have hpstar_lev : |inner ℝ v (Work.BoxShrink.Pinch.par ψ pstar)
        - (inner ℝ v c + u)| = h :=
      hlev_closed.mem_of_tendsto hφtend
        (Filter.Eventually.of_forall fun k => (e (φ k)).2.2.1)
    have hspan_closed : IsClosed ((Submodule.span ℝ ({n} : Set R3)) : Set R3) :=
      Submodule.closed_of_finiteDimensional _
    have hpstar_span : proj pstar ∈ (Submodule.span ℝ ({n} : Set R3) : Set R3) :=
      hspan_closed.mem_of_tendsto ((hprojcont.tendsto pstar).comp hφtend)
        (Filter.Eventually.of_forall fun k => hbad_span (e (φ k)).2)
    have hpstar_ne : proj pstar ≠ 0 := hreg pstar hpstar_lev
    obtain ⟨cstar, hcstar⟩ := Submodule.mem_span_singleton.mp hpstar_span
    have hcstar_ne : cstar ≠ 0 := by
      intro h0
      exact hpstar_ne (by rw [← hcstar, h0, zero_smul])
    have hYstar : inner ℝ b (proj pstar) = cstar * (Real.sqrt (t ^ 2 + 1))⁻¹ := by
      rw [← hcstar, inner_smul_right, hbn]
    have hYstar_ne : inner ℝ b (proj pstar) ≠ 0 := by
      rw [hYstar]
      exact mul_ne_zero hcstar_ne (inv_ne_zero hsqrt_ne)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 / |inner ℝ b (proj pstar)| ≤ (m : ℝ) + 1 := by
      obtain ⟨m, hm⟩ := exists_nat_ge (2 / |inner ℝ b (proj pstar)|)
      exact ⟨m + 1, by push_cast; linarith⟩
    have hY_gt : 1 / ((m : ℝ) + 1) < |inner ℝ b (proj pstar)| := by
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hpos]
      have h2 : 2 ≤ |inner ℝ b (proj pstar)| * ((m : ℝ) + 1) := by
        rw [div_le_iff₀ (abs_pos.mpr hYstar_ne)] at hm
        linarith [hm, mul_comm (|inner ℝ b (proj pstar)|) ((m : ℝ) + 1)]
      nlinarith [abs_nonneg (inner ℝ b (proj pstar))]
    have hopen_gt : IsOpen {q : ℝ × ℝ | 1 / ((m : ℝ) + 1) < |inner ℝ b (proj q)|} :=
      isOpen_lt continuous_const (continuous_abs.comp hYcont)
    have hev : ∀ᶠ k in Filter.atTop,
        1 / ((m : ℝ) + 1) < |inner ℝ b (proj ((e (φ k) : BadK) : ℝ × ℝ))| :=
      hφtend.eventually (hopen_gt.mem_nhds hY_gt)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hinj : Set.InjOn (fun k : ℕ => ((e (φ k) : BadK) : ℝ × ℝ)) (Set.Ici N) := by
      intro k _ l _ hkl
      exact hφmono.injective (e.injective (Subtype.coe_injective hkl))
    have hAinf : (Set.Ici N : Set ℕ).Infinite :=
      Set.Infinite.mono (s := Set.range fun k : ℕ => k + N)
        (by rintro _ ⟨k, rfl⟩; exact Set.mem_Ici.mpr (Nat.le_add_left N k))
        (Set.infinite_range_of_injective fun a b hab' => Nat.add_right_cancel hab')
    have himg_inf : ((fun k : ℕ => ((e (φ k) : BadK) : ℝ × ℝ)) '' (Set.Ici N : Set ℕ)).Infinite :=
      Set.Infinite.image hinj hAinf
    have hsub : ((fun k : ℕ => ((e (φ k) : BadK) : ℝ × ℝ)) '' (Set.Ici N : Set ℕ)) ⊆
        (Ω ⁻¹' {((inner ℝ v c + u) + h, t)} ∩ Km m) ∪
          (Ω ⁻¹' {((inner ℝ v c + u) - h, t)} ∩ Km m) := by
      rintro q ⟨k, hk, rfl⟩
      have hlev : |inner ℝ v (Work.BoxShrink.Pinch.par ψ ((e (φ k) : BadK) : ℝ × ℝ))
          - (inner ℝ v c + u)| = h := (e (φ k)).2.2.1
      have hdirq : dir ((e (φ k) : BadK) : ℝ × ℝ) = t := hdir_bad _ (e (φ k)).2
      have hKcq : ((e (φ k) : BadK) : ℝ × ℝ) ∈ Kc := (e (φ k)).2.1
      have hYm : 1 / ((m : ℝ) + 1) ≤
          |inner ℝ b (proj ((e (φ k) : BadK) : ℝ × ℝ))| := le_of_lt (hN k hk)
      have hKmq : ((e (φ k) : BadK) : ℝ × ℝ) ∈ Km m := ⟨hKcq, hYm⟩
      have hh0 : 0 ≤ h := by rw [← hlev]; exact abs_nonneg _
      rcases (abs_eq hh0).mp hlev with h1 | h1
      · left
        refine ⟨?_, hKmq⟩
        rw [hΩ]
        exact Prod.ext (by linarith) hdirq
      · right
        refine ⟨?_, hKmq⟩
        rw [hΩ]
        exact Prod.ext (by linarith) hdirq
    have hunion_inf : ((Ω ⁻¹' {((inner ℝ v c + u) + h, t)} ∩ Km m) ∪
        (Ω ⁻¹' {((inner ℝ v c + u) - h, t)} ∩ Km m)).Infinite := himg_inf.mono hsub
    have hcase : (Ω ⁻¹' {((inner ℝ v c + u) + h, t)} ∩ Km m).Infinite ∨
        (Ω ⁻¹' {((inner ℝ v c + u) - h, t)} ∩ Km m).Infinite := by
      by_contra hc
      rw [not_or] at hc
      exact hunion_inf ((Set.not_infinite.mp hc.1).union (Set.not_infinite.mp hc.2))
    rcases hcase with hc | hc
    · exact hSa (by rw [hS]; exact Set.mem_iUnion.mpr ⟨m, hc⟩)
    · exact hSb (by rw [hS]; exact Set.mem_iUnion.mpr ⟨m, hc⟩)
  -- ### 8. the exceptional set of levels and the final verification
  set F : ℝ × ℝ → ℝ := Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n) with hF
  refine ⟨n, h, (hBadK_fin.image F).toFinset, hn1, hvn, hhmin, hhmax, ?_⟩
  intro lam hlam p hbox hpabs hpF t' ht'
  obtain ⟨p₀, hp₀mem, hp₀par, hp₀der⟩ := fundamentalDomain_reduction ψ p
  have hp₀K : p₀ ∈ Kc := ⟨hp₀mem, by rw [hp₀par]; exact subset_closure hbox⟩
  have hp₀abs : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p₀) - (inner ℝ v c + u)| = h := by
    rw [hp₀par]; exact hpabs
  have hFp₀ : F p₀ = F p := by
    simp only [hF, Work.Drive.EpsForm.sweepHeight_innerSL]
    rw [hp₀par]
  have hbad₀ : ∃ t'' : ℝ, fderiv ℝ F p₀
      = t'' • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p₀ := by
    refine ⟨t', ?_⟩
    have h1 : fderiv ℝ F p₀ = fderiv ℝ F p := by
      simp only [hF, Work.Drive.EpsForm.sweepHeight_innerSL]
      exact fderiv_inner_par_congr ψ n hp₀der
    have h2 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p₀
        = fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p :=
      fderiv_inner_par_congr ψ v hp₀der
    rw [h1, h2]
    exact ht'
  have hmem : p₀ ∈ BadK := ⟨hp₀K, hp₀abs, hbad₀⟩
  have hF₀ : F p₀ = lam := by rw [hFp₀]; exact hpF
  have : lam ∈ ((hBadK_fin.image F).toFinset : Set ℝ) := by
    rw [Set.Finite.coe_toFinset]
    exact ⟨p₀, hmem, hF₀⟩
  exact hlam this

end

end Work.Drive.Mono.Band
