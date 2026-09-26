import Submission.Work.Smooth.JordanSeparation.BumpCylinder
import Submission.Work.Smooth.JordanSeparation.far_chord_bound

/-!
# The chord-free window

`chord_free_window` is the per-step legality input of the bump-push chain of `SCHOENFLIES.md` §6: at
any parameter `θ₀` where a `C¹` simple closed curve `γ` is transverse to a unit direction `ν`, there
is a window `|θ - θ₀| < η` and a length `u > 0` such that **no** chord `γ θ - γ θ'` with `θ` in the
window is a nonzero multiple of `ν` of length `≤ u`.

The proof combines two elementary facts:

* the scalar function `θ ↦ detV (γ θ) ν` has derivative `detV (γ' θ) ν`, nonzero at `θ₀`, hence is
  strictly monotone (Rolle) on a neighbourhood of `θ₀`;
* away from `θ₀`, modulo `2π`, the chord length is bounded below by compactness.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- Every real number is congruent modulo `2π` to a point within distance `π` of `θ₀`. -/
theorem exists_int_shift_close (θ θ₀ : ℝ) :
    ∃ k : ℤ, |θ + (k : ℝ) * (2 * Real.pi) - θ₀| ≤ Real.pi := by
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Ico (θ - θ₀)
  rw [Set.mem_Ico] at hk
  by_cases h : (θ - θ₀) - (k : ℝ) * (2 * Real.pi) ≤ Real.pi
  · refine ⟨-k, ?_⟩
    have h2 : θ + ((-k : ℤ) : ℝ) * (2 * Real.pi) - θ₀
        = (θ - θ₀) - (k : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [h2, abs_of_nonneg hk.1]; exact h
  · push_neg at h
    refine ⟨-(k + 1), ?_⟩
    have h2 : θ + ((-(k + 1) : ℤ) : ℝ) * (2 * Real.pi) - θ₀
        = (θ - θ₀) - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi := by push_cast; ring
    rw [h2]
    have h3 : (θ - θ₀) - (k : ℝ) * (2 * Real.pi) - 2 * Real.pi < 0 := by linarith [hk.2]
    rw [abs_of_neg h3]
    linarith [hk.2]

/-- Congruent parameters modulo `2π` are forced by a coincidence of the curve. -/
theorem eq_mod_period_of_eq {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    (hsimp : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {a b : ℝ} (h : γ a = γ b) :
    ∃ k : ℤ, b = a + (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨k₁, hk₁⟩ := exists_int_sub_mem_Ico a
  obtain ⟨k₂, hk₂⟩ := exists_int_sub_mem_Ico b
  have e1 : γ (a - (k₁ : ℝ) * (2 * Real.pi)) = γ a := by
    have := (hper.int_mul (-k₁)) a
    simpa [sub_eq_add_neg] using this
  have e2 : γ (b - (k₂ : ℝ) * (2 * Real.pi)) = γ b := by
    have := (hper.int_mul (-k₂)) b
    simpa [sub_eq_add_neg] using this
  have h1 : a - (k₁ : ℝ) * (2 * Real.pi) = b - (k₂ : ℝ) * (2 * Real.pi) := by
    have := hsimp hk₁ hk₂ (by rw [e1, e2, h])
    exact this
  refine ⟨k₂ - k₁, ?_⟩
  push_cast
  linarith

/-- **The chord-free window.** -/
theorem chord_free_window {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hsimp : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {θ₀ : ℝ} {d : ℝ → ℂ} (hd : ∀ θ, HasDerivAt γ (d θ) θ) (hdc : Continuous d)
    {ν : ℂ} (hν : ‖ν‖ = 1) (hdet : detV (d θ₀) ν ≠ 0) :
    ∃ η > 0, ∃ u > 0, ∀ θ θ' t : ℝ, |θ - θ₀| < η → |t| ≤ u →
      γ θ - γ θ' = t * ν → t = 0 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- ## Step 1: `G θ = detV (γ θ) ν` has derivative `detV (d θ) ν`
  have hG : ∀ θ : ℝ, HasDerivAt (fun θ => detV (γ θ) ν) (detV (d θ) ν) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => star (γ θ)) (star (d θ)) θ := (hd θ).star
    have h2 : HasDerivAt (fun θ => star (γ θ) * ν) (star (d θ) * ν) θ := h1.mul_const ν
    have h3 : HasDerivAt (fun θ => (star (γ θ) * ν).im) ((star (d θ) * ν).im) θ := by
      have h4 := (Complex.imCLM.hasFDerivAt.comp θ (hasDerivAt_iff_hasFDerivAt.mp h2)).hasDerivAt
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul, Function.comp_apply] at h4
      exact h4
    have hfun : (fun θ => detV (γ θ) ν) = fun θ => (star (γ θ) * ν).im := by
      funext x; rw [detV_def, starRingEnd_apply]
    rw [hfun]; exact h3
  have hcontG : Continuous fun θ : ℝ => detV (d θ) ν := by
    have h : (fun θ : ℝ => detV (d θ) ν) = fun θ => (star (d θ) * ν).im := by
      funext θ; rw [detV_def, starRingEnd_apply]
    rw [h]
    exact Complex.continuous_im.comp ((continuous_star.comp hdc).mul continuous_const)
  -- ## Step 2: a radius `ρ₂ > 0` (also `≤ π/2`) on which the scalar derivative never vanishes
  obtain ⟨ρ₂, hρ₂pos, hρ₂π, hρ₂det⟩ :
      ∃ ρ₂ > 0, ρ₂ ≤ Real.pi / 2 ∧ ∀ θ : ℝ, |θ - θ₀| ≤ ρ₂ → detV (d θ) ν ≠ 0 := by
    have hpos : (0 : ℝ) < ‖detV (d θ₀) ν‖ := norm_pos_iff.mpr hdet
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp hcontG.continuousAt (‖detV (d θ₀) ν‖ / 2) (by linarith)
    refine ⟨min (δ / 2) (Real.pi / 2), lt_min (by linarith) (by linarith),
      min_le_right _ _, fun θ hθ => ?_⟩
    intro hzero
    have h1 : dist θ θ₀ < δ := by
      rw [Real.dist_eq]
      have := (abs_le.mp hθ).2
      have := min_le_left (δ / 2) (Real.pi / 2)
      linarith
    have h2 := hδ h1
    rw [Real.dist_eq, hzero, zero_sub, abs_neg, Real.norm_eq_abs] at h2
    linarith [h2, abs_pos.mpr hdet]
  -- ## Step 3: `G` is injective on the window
  have hGinj : Set.InjOn (fun θ : ℝ => detV (γ θ) ν)
      (Set.Ioo (θ₀ - ρ₂) (θ₀ + ρ₂)) := by
    have key : ∀ a b : ℝ, a ∈ Set.Ioo (θ₀ - ρ₂) (θ₀ + ρ₂) →
        b ∈ Set.Ioo (θ₀ - ρ₂) (θ₀ + ρ₂) → a < b →
        detV (γ a) ν = detV (γ b) ν → False := by
      intro a b ha hb hab heq
      have hc : ContinuousOn (fun θ : ℝ => detV (γ θ) ν) (Set.Icc a b) :=
        fun x _ => (hG x).continuousAt.continuousWithinAt
      obtain ⟨c, hc1, hc2⟩ := exists_deriv_eq_zero hab hc heq
      have hder : deriv (fun θ : ℝ => detV (γ θ) ν) c = detV (d c) ν := (hG c).deriv
      rw [hder] at hc2
      have hcl : |c - θ₀| ≤ ρ₂ := by
        rw [abs_le]
        exact ⟨by linarith [ha.1, hc1.1], by linarith [hb.2, hc1.2]⟩
      exact hρ₂det c hcl hc2
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd (key a b ha hb hlt hab) (not_false)
    · exact heq
    · exact absurd (key b a hb ha hgt hab.symm) (not_false)
  -- ## Step 4: the compactness separation away from the window
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε > 0, ∀ θ θ' : ℝ, |θ - θ₀| ≤ ρ₂ / 2 →
      ρ₂ ≤ |θ' - θ₀| → |θ' - θ₀| ≤ Real.pi → ε ≤ ‖γ θ - γ θ'‖ := by
    set S : Set (ℝ × ℝ) := (Set.Icc (θ₀ - ρ₂ / 2) (θ₀ + ρ₂ / 2)) ×ˢ
        (Set.Icc (θ₀ + ρ₂) (θ₀ + Real.pi) ∪ Set.Icc (θ₀ - Real.pi) (θ₀ - ρ₂)) with hS
    have hScomp : IsCompact S := isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)
    have hSne : S.Nonempty := by
      refine ⟨(θ₀, θ₀ + ρ₂), ?_⟩
      rw [hS, Set.mem_prod]
      exact ⟨⟨by linarith, by linarith⟩, Or.inl ⟨le_refl _, by linarith [hρ₂π]⟩⟩
    have hf_cont : Continuous fun p : ℝ × ℝ => ‖γ p.1 - γ p.2‖ :=
      ((hcont.comp continuous_fst).sub (hcont.comp continuous_snd)).norm
    have hf_pos : ∀ p ∈ S, 0 < ‖γ p.1 - γ p.2‖ := by
      intro p hp
      rw [hS, Set.mem_prod] at hp
      have hp1 : |p.1 - θ₀| ≤ ρ₂ / 2 := by
        rw [abs_le]; exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      have hp2 : ρ₂ ≤ |p.2 - θ₀| := by
        rcases hp.2 with h | h
        · rw [abs_of_nonneg (by linarith [h.1])]; linarith [h.1]
        · rw [abs_of_nonpos (by linarith [h.2])]; linarith [h.2]
      have hp2π : |p.2 - θ₀| ≤ Real.pi := by
        rcases hp.2 with h | h
        · rw [abs_of_nonneg (by linarith [h.1])]; linarith [h.2]
        · rw [abs_of_nonpos (by linarith [h.2])]; linarith [h.1]
      refine norm_pos_iff.mpr (sub_ne_zero.mpr fun hcon => ?_)
      obtain ⟨k, hk⟩ := eq_mod_period_of_eq hper hsimp hcon
      have h3 : |p.2 - p.1| ≤ Real.pi + ρ₂ / 2 := by
        have h7 : (p.2 - θ₀) - (p.1 - θ₀) = p.2 - p.1 := by ring
        calc |p.2 - p.1| = |(p.2 - θ₀) - (p.1 - θ₀)| := by rw [h7]
          _ ≤ |p.2 - θ₀| + |p.1 - θ₀| := abs_sub _ _
          _ ≤ Real.pi + ρ₂ / 2 := by linarith
      have h5 : ρ₂ / 2 ≤ |p.2 - p.1| := by
        have h7 : (p.2 - θ₀) - (p.1 - θ₀) = p.2 - p.1 := by ring
        have := abs_sub_abs_le_abs_sub (p.2 - θ₀) (p.1 - θ₀)
        rw [h7] at this
        linarith
      have h4 : |p.2 - p.1| = |(k : ℝ)| * (2 * Real.pi) := by
        have h3' : p.2 - p.1 = (k : ℝ) * (2 * Real.pi) := by linarith [hk]
        rw [h3', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have h8 : |(k : ℝ)| * (2 * Real.pi) ≤ Real.pi + ρ₂ / 2 := by linarith [h4, h3]
      have h9 : |(k : ℝ)| < 1 := by nlinarith [h8, hπ, hρ₂π]
      rw [abs_lt] at h9
      have h10 : k = 0 := by
        have : (-1 : ℤ) < k ∧ k < 1 := by exact_mod_cast h9
        omega
      rw [h10] at h4
      simp at h4
      rw [h4, abs_zero] at h5
      linarith [hρ₂pos]
    obtain ⟨p, hp_mem, hmin⟩ := hScomp.exists_isMinOn hSne hf_cont.continuousOn
    rw [isMinOn_iff] at hmin
    refine ⟨‖γ p.1 - γ p.2‖, hf_pos p hp_mem, fun θ θ' hθ hfar hfarπ => ?_⟩
    refine hmin (θ, θ') ?_
    rw [hS, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨by linarith [(abs_le.mp hθ).1], by linarith [(abs_le.mp hθ).2]⟩
    · rcases le_or_gt 0 (θ' - θ₀) with h | h
      · rw [abs_of_nonneg h] at hfar hfarπ
        exact Or.inl ⟨by linarith, by linarith⟩
      · rw [abs_of_neg h] at hfar hfarπ
        exact Or.inr ⟨by linarith, by linarith⟩
  -- ## Step 5: reduce `θ'` and conclude
  refine ⟨ρ₂ / 2, by linarith, ε / 2, by linarith, ?_⟩
  intro θ θ' t hθ ht heq
  obtain ⟨k, hk⟩ := exists_int_shift_close θ' θ₀
  have hper2 : γ (θ' + (k : ℝ) * (2 * Real.pi)) = γ θ' := by
    have := hper.int_mul k θ'
    simpa using this
  have hGθθ' : detV (γ θ) ν = detV (γ θ') ν := by
    have hadd : detV (γ θ - γ θ') ν = detV (γ θ) ν - detV (γ θ') ν := by
      rw [detV_eq, detV_eq, detV_eq]; simp only [Complex.sub_re, Complex.sub_im]; ring
    have h0 : detV (γ θ - γ θ') ν = 0 := by rw [heq, detV_eq]; simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; ring
    rw [hadd] at h0
    linarith
  rcases le_or_gt ρ₂ |θ' + (k : ℝ) * (2 * Real.pi) - θ₀| with hfar | hnear
  · -- far case
    have h1 : ε ≤ ‖γ θ - γ θ'‖ := by
      have h2 : ε ≤ ‖γ θ - γ (θ' + (k : ℝ) * (2 * Real.pi))‖ :=
        hε θ (θ' + (k : ℝ) * (2 * Real.pi)) (le_of_lt hθ) hfar hk
      rwa [hper2] at h2
    have ht' : ‖γ θ - γ θ'‖ = |t| := by
      rw [heq, norm_mul, hν, mul_one]
      simp
    rw [ht'] at h1
    linarith [abs_le.mp ht]
  · -- near case: monotonicity
    have h1 : θ ∈ Set.Ioo (θ₀ - ρ₂) (θ₀ + ρ₂) := by
      rw [abs_lt] at hθ
      exact ⟨by linarith [hρ₂pos, hθ.1], by linarith [hθ.2]⟩
    have h2 : θ' + (k : ℝ) * (2 * Real.pi) ∈ Set.Ioo (θ₀ - ρ₂) (θ₀ + ρ₂) := by
      rw [abs_lt] at hnear
      exact ⟨by linarith [hnear.1], by linarith [hnear.2]⟩
    have hkey : detV (γ θ) ν = detV (γ (θ' + (k : ℝ) * (2 * Real.pi))) ν := by
      rw [hper2, ← hGθθ']
    have hthis := hGinj h1 h2 hkey
    have ht0 : γ θ - γ θ' = 0 := by rw [← hper2, hthis, sub_self]
    rw [ht0] at heq
    have htν : ((t : ℝ) : ℂ) * ν = 0 := heq.symm
    rcases mul_eq_zero.mp htν with h | h
    · exact Complex.ofReal_eq_zero.mp h
    · exact absurd h (fun h0 => by rw [h0, norm_zero] at hν; norm_num at hν)

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The one-step legality of the bump push.**  If the profile `φ` is supported in a chord-free
window of `γ` at `θ₀` (with data `η`, `u` from `chord_free_window`) and takes values in `[0,u]`,
then the bump push `(θ,s) ↦ γ θ + (s * φ θ) • ν` is injective: this is `bumpCylinder_of_chord`
with the chord hypothesis supplied by the window. -/
theorem bumpCylinder_of_window {γ : ℝ → ℂ} {ν : ℂ} {φ : ℝ → ℝ} {θ₀ η u : ℝ}
    (hν : ‖ν‖ = 1) (hφ0 : ∀ θ, 0 ≤ φ θ) (hφu : ∀ θ, φ θ ≤ u)
    (hw : ∀ θ θ' t : ℝ, |θ - θ₀| < η → |t| ≤ u → γ θ - γ θ' = t * ν → t = 0)
    (hsupp : ∀ θ : ℝ, φ θ ≠ 0 → |θ - θ₀| < η) :
    ∀ θ s θ' s' : ℝ, s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
      γ θ + ((s * φ θ : ℝ) : ℂ) * ν = γ θ' + ((s' * φ θ' : ℝ) : ℂ) * ν →
      s * φ θ = s' * φ θ' ∧ γ θ = γ θ' := by
  refine bumpCylinder_of_chord hφ0 hφu ?_
  intro θ θ' t ht hne heq
  rcases hne with h | h
  · exact hw θ θ' t (hsupp θ h) ht heq
  · have h2 : |(-t)| ≤ u := by rw [abs_neg]; exact ht
    have hthree : γ θ' - γ θ = -(((t : ℝ) : ℂ) * ν) := by
      rw [show γ θ' - γ θ = -((γ θ) - (γ θ')) by ring, heq]
    have hcast : -(((t : ℝ) : ℂ) * ν) = (((-t : ℝ) : ℂ)) * ν := by push_cast; ring
    have h3 : γ θ' - γ θ = (((-t : ℝ) : ℂ)) * ν := hthree.trans hcast
    have h4 := hw θ' θ (-t) (hsupp θ' h) h2 h3
    simpa using h4

end

end Work.Smooth.JordanSeparation
