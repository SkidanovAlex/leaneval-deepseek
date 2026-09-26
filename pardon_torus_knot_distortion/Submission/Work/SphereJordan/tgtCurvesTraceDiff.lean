import Mathlib
import Submission.Work.SphereJordan.annulusAux
import Submission.Work.SphereJordan.annulusTargetCurves
import Submission.Work.Smooth.SphereJordan.plainAnnulusSetup

namespace Work.SphereJordan

open Set
open Work.Smooth.SphereJordan
  (tgtUpB tgtDnB tgtCut₁ tgtCut₂ srcOuterUp srcOuterDn cut₁ cut₂ perPt cutDir)

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Unfolded branch forms of the target curves on one period

`tgtUpB` and `tgtDnB` are defined in terms of `perPt`; on a parameter `σ ∈ [0, 2π)` the reduction
`perPt σ = σ` is the identity, which gives the plain four-branch `if`-chain. -/

theorem tgtUpB_of_mem_Ico (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (b : Bool) (θ₁ θ₂ : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ σ =
      (if σ ≤ Real.pi / 2 then srcOuterUp S (σ / (Real.pi / 2))
       else if σ ≤ Real.pi then tgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2))
       else if σ ≤ 3 * Real.pi / 2 then
        (if b then γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂))
         else γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi)))
       else tgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))) := by
  rw [Work.Smooth.SphereJordan.tgtUpB, Work.SphereJordan.perPt_self hσ]

theorem tgtDnB_of_mem_Ico (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (b : Bool) (θ₁ θ₂ : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ σ =
      (if σ ≤ Real.pi / 2 then srcOuterDn S (σ / (Real.pi / 2))
       else if σ ≤ Real.pi then tgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2))
       else if σ ≤ 3 * Real.pi / 2 then
        (if b then γ.γ (θ₁ - 2 * Real.pi +
            ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
         else γ.γ (θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁)))
       else tgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))) := by
  rw [Work.Smooth.SphereJordan.tgtDnB, Work.SphereJordan.perPt_self hσ]

/-! ## The lower outer semicircle -/

theorem srcOuterDn_mem_sphere (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    srcOuterDn S x ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, srcOuterDn, norm_mul, norm_neg,
    Complex.norm_exp_ofReal_mul_I, mul_one, Work.Smooth.SphereJordan.norm_cutDir]

/-! ## The traces of `tgtDnB` lie in `∂𝔻 ∪ cut₁ ∪ cut₂ ∪ (arc)` -/

/-- **The trace of `tgtDnB` with `b = true` lies in `∂𝔻 ∪ cut₁ ∪ cut₂ ∪ γ '' Icc (θ₁-2π) θ₂`.** -/
theorem tgtDnB_true_mem_trace (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ ≤ s₁) (ht₂ : t₂ ≤ s₂) {θ₁ θ₂ : ℝ} (hθ' : θ₁ < θ₂ + 2 * Real.pi) (τ : ℝ) :
    tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂ τ ∈ Metric.sphere (0 : ℂ) 1 ∪
      (cut₁ S t₁ s₁ ∪ cut₂ S t₂ s₂ ∪ γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂) := by
  set σ := perPt τ with hσdef
  have hσmem : σ ∈ Set.Ico (0:ℝ) (2 * Real.pi) := Work.SphereJordan.perPt_mem τ
  rw [Work.Smooth.SphereJordan.tgtDnB, ← hσdef]
  rw [if_pos rfl]
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [if_pos h1]
    have hmem : srcOuterDn S (σ / (Real.pi / 2)) ∈ Metric.sphere (0 : ℂ) 1 :=
      srcOuterDn_mem_sphere S _
    simp only [Set.mem_union]; tauto
  · rw [if_neg h1]
    by_cases h2 : σ ≤ Real.pi
    · rw [if_pos h2]
      have hmem : tgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2)) ∈ cut₁ S t₁ s₁ :=
        tgtCut₁_mem_cut₁ S ht₁ (halfParam_mem (le_of_lt (not_le.mp h1)) h2)
      simp only [Set.mem_union]; tauto
    · rw [if_neg h2]
      by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        obtain ⟨hs0, hs1⟩ := midParam_mem (le_of_lt (not_le.mp h2)) h3
        have hd : 0 < θ₂ - θ₁ + 2 * Real.pi := by linarith
        have hmem : γ.γ (θ₁ - 2 * Real.pi + (σ - Real.pi) / (Real.pi / 2) *
            (θ₂ - θ₁ + 2 * Real.pi)) ∈ γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂ :=
          ⟨_, ⟨by linarith [mul_nonneg hs0 hd.le], by nlinarith [hs1, hd]⟩, rfl⟩
        simp only [Set.mem_union]; tauto
      · rw [if_neg h3]
        have hmem : tgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) ∈
            cut₂ S t₂ s₂ :=
          tgtCut₂_mem_cut₂ S ht₂ (lastParam_mem (le_of_lt (not_le.mp h3)) (le_of_lt hσmem.2))
        simp only [Set.mem_union]; tauto

/-- **The trace of `tgtDnB` with `b = false` lies in `∂𝔻 ∪ cut₁ ∪ cut₂ ∪ γ '' Icc θ₂ θ₁`.** -/
theorem tgtDnB_false_mem_trace (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ ≤ s₁) (ht₂ : t₂ ≤ s₂) {θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁) (τ : ℝ) :
    tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂ τ ∈ Metric.sphere (0 : ℂ) 1 ∪
      (cut₁ S t₁ s₁ ∪ cut₂ S t₂ s₂ ∪ γ '' Set.Icc θ₂ θ₁) := by
  set σ := perPt τ with hσdef
  have hσmem : σ ∈ Set.Ico (0:ℝ) (2 * Real.pi) := Work.SphereJordan.perPt_mem τ
  rw [Work.Smooth.SphereJordan.tgtDnB, ← hσdef]
  rw [if_neg Bool.false_ne_true]
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [if_pos h1]
    have hmem : srcOuterDn S (σ / (Real.pi / 2)) ∈ Metric.sphere (0 : ℂ) 1 :=
      srcOuterDn_mem_sphere S _
    simp only [Set.mem_union]; tauto
  · rw [if_neg h1]
    by_cases h2 : σ ≤ Real.pi
    · rw [if_pos h2]
      have hmem : tgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2)) ∈ cut₁ S t₁ s₁ :=
        tgtCut₁_mem_cut₁ S ht₁ (halfParam_mem (le_of_lt (not_le.mp h1)) h2)
      simp only [Set.mem_union]; tauto
    · rw [if_neg h2]
      by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [if_pos h3]
        obtain ⟨hs0, hs1⟩ := midParam_mem (le_of_lt (not_le.mp h2)) h3
        have hc : θ₂ - θ₁ ≤ 0 := by linarith
        have hle : (σ - Real.pi) / (Real.pi / 2) * (θ₂ - θ₁) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hs0 hc
        have hge : θ₂ - θ₁ ≤ (σ - Real.pi) / (Real.pi / 2) * (θ₂ - θ₁) := by
          simpa using mul_le_mul_of_nonpos_right hs1 hc
        have hmem : γ.γ (θ₁ + (σ - Real.pi) / (Real.pi / 2) * (θ₂ - θ₁)) ∈
            γ '' Set.Icc θ₂ θ₁ :=
          ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
        simp only [Set.mem_union]; tauto
      · rw [if_neg h3]
        have hmem : tgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) ∈
            cut₂ S t₂ s₂ :=
          tgtCut₂_mem_cut₂ S ht₂ (lastParam_mem (le_of_lt (not_le.mp h3)) (le_of_lt hσmem.2))
        simp only [Set.mem_union]; tauto

/-! ## The cuts and the `γ`-arcs lie in the ranges of the target curves -/

/-- `cut₁ ⊆ range (tgtUpB _ false)`: the outer endpoint is the outer semicircle at `τ = 0`, the
inner endpoint `a₁ = γ θ₁` is the middle arc at `τ = 3π/2` (where it reads `γ (θ₁ - 2π) = γ θ₁`),
and the intermediate points are the fourth (radial) arc. -/
theorem cut₁_subset_range_upFalse (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (ht : t₁ < s₁)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * cutDir S = cutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S) :
    cut₁ S t₁ s₁ ⊆ Set.range (tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂) := by
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₁ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₁ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · rw [heq']
      refine ⟨3 * Real.pi / 2, ?_⟩
      have hper : γ.γ θ₁ = γ.γ (θ₁ - 2 * Real.pi) := by
        have h := γ.apply_add_int_mul (θ₁ - 2 * Real.pi) 1
        rw [show θ₁ - 2 * Real.pi + (1:ℤ) * (2 * Real.pi) = θ₁ from by push_cast; ring] at h
        exact h
      rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
        if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi)),
        if_pos le_rfl, if_neg Bool.false_ne_true]
      rw [show θ₂ + ((3 * Real.pi / 2 - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi) =
          θ₁ - 2 * Real.pi from by
        rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring]
        ring]
      rw [← hper]
      exact hγ₁
    · have hst : (0:ℝ) < s₁ - t₁ := by linarith
      set y : ℝ := (s₁ - σ) / (s₁ - t₁) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by rw [hydef, div_lt_one hst]; linarith
      have hys : s₁ + y * (t₁ - s₁) = σ := by rw [hydef]; field_simp; ring
      refine ⟨3 * Real.pi / 2 + (1 - y) * (Real.pi / 2), ?_⟩
      have hτmem : 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ∈
          Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [hy1, Real.pi_pos], by nlinarith [hy0, Real.pi_pos]⟩
      rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂ hτmem,
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi / 2)),
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi)),
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ 3 * Real.pi / 2))]
      rw [tgtCut₁,
        show 1 - (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2) /
            (Real.pi / 2) = y from by
          rw [show 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2 =
              (1 - y) * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]
          ring,
        hys]
  · rw [heq]
    refine ⟨0, ?_⟩
    rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
      ⟨le_refl 0, by positivity⟩, if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    rw [show (0:ℝ) / (Real.pi / 2) = 0 from by simp, srcOuterUp_zero]
    exact hout₁.symm
  · exact absurd hσ2 (not_le.mpr hgt)

/-- `cut₂ ⊆ range (tgtUpB _ false)`: the outer endpoint `-u` is the outer semicircle at `τ = π/2`,
and every other point is the second (radial) arc. -/
theorem cut₂_subset_range_upFalse (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (ht : t₂ < s₂)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * cutDir S = -cutDir S) :
    cut₂ S t₂ s₂ ⊆ Set.range (tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂) := by
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₂ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₂ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · rw [heq']
      refine ⟨Real.pi, ?_⟩
      rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
        ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩,
        if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl]
      rw [tgtCut₂,
        show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring,
        show s₂ + 1 * (t₂ - s₂) = t₂ from by ring]
    · have hst : (0:ℝ) < s₂ - t₂ := by linarith
      set y : ℝ := (s₂ - σ) / (s₂ - t₂) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by rw [hydef, div_lt_one hst]; linarith
      have hys : s₂ + y * (t₂ - s₂) = σ := by rw [hydef]; field_simp; ring
      refine ⟨Real.pi / 2 + y * (Real.pi / 2), ?_⟩
      have hτmem : Real.pi / 2 + y * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [hy0, Real.pi_pos], by nlinarith [hy1, Real.pi_pos]⟩
      rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂ hτmem,
        if_neg (by nlinarith [hy0, Real.pi_pos] :
          ¬ (Real.pi / 2 + y * (Real.pi / 2) ≤ Real.pi / 2)),
        if_pos (by nlinarith [hy1, Real.pi_pos] :
          Real.pi / 2 + y * (Real.pi / 2) ≤ Real.pi)]
      rw [tgtCut₂,
        show (Real.pi / 2 + y * (Real.pi / 2) - Real.pi / 2) / (Real.pi / 2) = y from by
          rw [show Real.pi / 2 + y * (Real.pi / 2) - Real.pi / 2 = y * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)],
        hys]
  · rw [heq]
    refine ⟨Real.pi / 2, ?_⟩
    rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, if_pos le_rfl]
    rw [show Real.pi / 2 / (Real.pi / 2) = 1 from by
      rw [div_self (by positivity : (Real.pi : ℝ) / 2 ≠ 0)], srcOuterUp_one]
    exact hout₂.symm
  · exact absurd hσ2 (not_le.mpr hgt)

/-- `γ '' Icc (θ₁-2π) θ₂ ⊆ range (tgtUpB _ false)`: the endpoint `γ θ₂` is the second (radial)
arc at `τ = π` (its inner endpoint), and the rest is the middle arc. -/
theorem arc_subset_range_upFalse (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂ ⊆ Set.range (tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂) := by
  rintro z ⟨θ, ⟨hθ1, hθ2⟩, rfl⟩
  rcases eq_or_lt_of_le hθ2 with heq | hlt
  · rw [heq]
    refine ⟨Real.pi, ?_⟩
    rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
      ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩,
      if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl]
    rw [tgtCut₂,
      show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring,
      show s₂ + 1 * (t₂ - s₂) = t₂ from by ring]
    exact hγ₂.symm
  · have hden : (0:ℝ) < θ₂ - θ₁ + 2 * Real.pi := by linarith
    set u : ℝ := (θ₂ - θ) / (θ₂ - θ₁ + 2 * Real.pi) with hudef
    have hu0 : 0 < u := by rw [hudef]; exact div_pos (by linarith) hden
    have hu1 : u ≤ 1 := by rw [hudef, div_le_one hden]; linarith
    have hval : θ₂ + u * (θ₁ - θ₂ - 2 * Real.pi) = θ := by
      rw [hudef]; field_simp; ring
    refine ⟨Real.pi + u * (Real.pi / 2), ?_⟩
    have hτmem : Real.pi + u * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
      ⟨by nlinarith [hu0, Real.pi_pos], by nlinarith [hu1, Real.pi_pos]⟩
    rw [tgtUpB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂ hτmem,
      if_neg (by nlinarith [hu0, Real.pi_pos] :
        ¬ (Real.pi + u * (Real.pi / 2) ≤ Real.pi / 2)),
      if_neg (by nlinarith [hu0, Real.pi_pos] :
        ¬ (Real.pi + u * (Real.pi / 2) ≤ Real.pi)),
      if_pos (by nlinarith [hu1, Real.pi_pos] :
        Real.pi + u * (Real.pi / 2) ≤ 3 * Real.pi / 2),
      if_neg Bool.false_ne_true]
    rw [show (Real.pi + u * (Real.pi / 2) - Real.pi) / (Real.pi / 2) = u from by
      rw [show Real.pi + u * (Real.pi / 2) - Real.pi = u * (Real.pi / 2) from by ring,
        mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]]
    rw [hval]

/-- `cut₁ ⊆ range (tgtDnB _ _)`: independent of the flag `b`. -/
theorem cut₁_subset_range_dn (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (ht : t₁ < s₁) (b : Bool)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * cutDir S = cutDir S) :
    cut₁ S t₁ s₁ ⊆ Set.range (tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂) := by
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₁ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₁ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · rw [heq']
      refine ⟨Real.pi, ?_⟩
      rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ b θ₁ θ₂
        ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩,
        if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl]
      rw [tgtCut₁,
        show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring,
        show s₁ + 1 * (t₁ - s₁) = t₁ from by ring]
    · have hst : (0:ℝ) < s₁ - t₁ := by linarith
      set y : ℝ := (s₁ - σ) / (s₁ - t₁) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by rw [hydef, div_lt_one hst]; linarith
      have hys : s₁ + y * (t₁ - s₁) = σ := by rw [hydef]; field_simp; ring
      refine ⟨Real.pi / 2 + y * (Real.pi / 2), ?_⟩
      have hτmem : Real.pi / 2 + y * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [hy0, Real.pi_pos], by nlinarith [hy1, Real.pi_pos]⟩
      rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ b θ₁ θ₂ hτmem,
        if_neg (by nlinarith [hy0, Real.pi_pos] :
          ¬ (Real.pi / 2 + y * (Real.pi / 2) ≤ Real.pi / 2)),
        if_pos (by nlinarith [hy1, Real.pi_pos] :
          Real.pi / 2 + y * (Real.pi / 2) ≤ Real.pi)]
      rw [tgtCut₁,
        show (Real.pi / 2 + y * (Real.pi / 2) - Real.pi / 2) / (Real.pi / 2) = y from by
          rw [show Real.pi / 2 + y * (Real.pi / 2) - Real.pi / 2 = y * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)],
        hys]
  · rw [heq]
    refine ⟨Real.pi / 2, ?_⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ b θ₁ θ₂
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, if_pos le_rfl]
    rw [show Real.pi / 2 / (Real.pi / 2) = 1 from by
      rw [div_self (by positivity : (Real.pi : ℝ) / 2 ≠ 0)], srcOuterDn_one]
    exact hout₁.symm
  · exact absurd hσ2 (not_le.mpr hgt)

/-- `cut₂ ⊆ range (tgtDnB _ true)`: the outer endpoint `-u` is the outer semicircle at `τ = 0`,
the inner endpoint `a₂ = γ θ₂` is the middle arc at `τ = 3π/2`, and the rest the fourth arc. -/
theorem cut₂_subset_range_dnTrue (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (ht : t₂ < s₂)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * cutDir S = -cutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    cut₂ S t₂ s₂ ⊆ Set.range (tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂) := by
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₂ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₂ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · rw [heq']
      refine ⟨3 * Real.pi / 2, ?_⟩
      rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ true θ₁ θ₂
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
        if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi)),
        if_pos le_rfl, if_pos rfl]
      rw [show θ₁ - 2 * Real.pi + ((3 * Real.pi / 2 - Real.pi) / (Real.pi / 2)) *
          (θ₂ - θ₁ + 2 * Real.pi) = θ₂ from by
        rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring]
        ring]
      exact hγ₂
    · have hst : (0:ℝ) < s₂ - t₂ := by linarith
      set y : ℝ := (s₂ - σ) / (s₂ - t₂) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by rw [hydef, div_lt_one hst]; linarith
      have hys : s₂ + y * (t₂ - s₂) = σ := by rw [hydef]; field_simp; ring
      refine ⟨3 * Real.pi / 2 + (1 - y) * (Real.pi / 2), ?_⟩
      have hτmem : 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ∈
          Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [hy1, Real.pi_pos], by nlinarith [hy0, Real.pi_pos]⟩
      rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ true θ₁ θ₂ hτmem,
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi / 2)),
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi)),
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ 3 * Real.pi / 2))]
      rw [tgtCut₂,
        show 1 - (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2) /
            (Real.pi / 2) = y from by
          rw [show 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2 =
              (1 - y) * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]
          ring,
        hys]
  · rw [heq]
    refine ⟨0, ?_⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ true θ₁ θ₂
      ⟨le_refl 0, by positivity⟩, if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    rw [show (0:ℝ) / (Real.pi / 2) = 0 from by simp, srcOuterDn_zero]
    exact hout₂.symm
  · exact absurd hσ2 (not_le.mpr hgt)

/-- `γ '' Icc (θ₁-2π) θ₂ ⊆ range (tgtDnB _ true)`: the endpoint `γ (θ₁-2π) = γ θ₁` is the second
(radial) arc at `τ = π` (its inner endpoint), and the rest is the middle arc. -/
theorem arc_subset_range_dnTrue (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S) :
    γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂ ⊆ Set.range (tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂) := by
  rintro z ⟨θ, ⟨hθ1, hθ2⟩, rfl⟩
  have hden : (0:ℝ) < θ₂ - θ₁ + 2 * Real.pi := by linarith
  rcases eq_or_lt_of_le hθ1 with heq | hlt
  · rw [← heq]
    have hper : γ.γ (θ₁ - 2 * Real.pi) = γ.γ θ₁ := by
      have h := γ.apply_add_int_mul (θ₁ - 2 * Real.pi) 1
      rw [show θ₁ - 2 * Real.pi + (1:ℤ) * (2 * Real.pi) = θ₁ from by push_cast; ring] at h
      exact h.symm
    refine ⟨Real.pi, ?_⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ true θ₁ θ₂
      ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩,
      if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl]
    rw [tgtCut₁,
      show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring,
      show s₁ + 1 * (t₁ - s₁) = t₁ from by ring]
    rw [hper]
    exact hγ₁.symm
  · set u : ℝ := (θ - (θ₁ - 2 * Real.pi)) / (θ₂ - θ₁ + 2 * Real.pi) with hudef
    have hu0 : 0 < u := by rw [hudef]; exact div_pos (by linarith) hden
    have hu1 : u ≤ 1 := by rw [hudef, div_le_one hden]; linarith
    have hval : θ₁ - 2 * Real.pi + u * (θ₂ - θ₁ + 2 * Real.pi) = θ := by
      rw [hudef]; field_simp; ring
    refine ⟨Real.pi + u * (Real.pi / 2), ?_⟩
    have hτmem : Real.pi + u * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
      ⟨by nlinarith [hu0, Real.pi_pos], by nlinarith [hu1, Real.pi_pos]⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ true θ₁ θ₂ hτmem,
      if_neg (by nlinarith [hu0, Real.pi_pos] :
        ¬ (Real.pi + u * (Real.pi / 2) ≤ Real.pi / 2)),
      if_neg (by nlinarith [hu0, Real.pi_pos] :
        ¬ (Real.pi + u * (Real.pi / 2) ≤ Real.pi)),
      if_pos (by nlinarith [hu1, Real.pi_pos] :
        Real.pi + u * (Real.pi / 2) ≤ 3 * Real.pi / 2),
      if_pos rfl]
    rw [show (Real.pi + u * (Real.pi / 2) - Real.pi) / (Real.pi / 2) = u from by
      rw [show Real.pi + u * (Real.pi / 2) - Real.pi = u * (Real.pi / 2) from by ring,
        mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]]
    rw [hval]

/-- `cut₂ ⊆ range (tgtDnB _ false)`. -/
theorem cut₂_subset_range_dnFalse (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (ht : t₂ < s₂)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * cutDir S = -cutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    cut₂ S t₂ s₂ ⊆ Set.range (tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂) := by
  rintro z ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
  rcases lt_trichotomy σ s₂ with hlt | heq | hgt
  · rcases lt_trichotomy σ t₂ with hlt' | heq' | hgt'
    · exact absurd hσ1 (not_le.mpr hlt')
    · rw [heq']
      refine ⟨3 * Real.pi / 2, ?_⟩
      rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
        if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
        if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi)),
        if_pos le_rfl, if_neg Bool.false_ne_true]
      rw [show θ₁ + ((3 * Real.pi / 2 - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁) = θ₂ from by
        rw [show (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring]
        ring]
      exact hγ₂
    · have hst : (0:ℝ) < s₂ - t₂ := by linarith
      set y : ℝ := (s₂ - σ) / (s₂ - t₂) with hydef
      have hy0 : 0 < y := by rw [hydef]; exact div_pos (by linarith) hst
      have hy1 : y < 1 := by rw [hydef, div_lt_one hst]; linarith
      have hys : s₂ + y * (t₂ - s₂) = σ := by rw [hydef]; field_simp; ring
      refine ⟨3 * Real.pi / 2 + (1 - y) * (Real.pi / 2), ?_⟩
      have hτmem : 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ∈
          Set.Ico (0:ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [hy1, Real.pi_pos], by nlinarith [hy0, Real.pi_pos]⟩
      rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂ hτmem,
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi / 2)),
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ Real.pi)),
        if_neg (by nlinarith [hy1, Real.pi_pos] :
          ¬ (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) ≤ 3 * Real.pi / 2))]
      rw [tgtCut₂,
        show 1 - (3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2) /
            (Real.pi / 2) = y from by
          rw [show 3 * Real.pi / 2 + (1 - y) * (Real.pi / 2) - 3 * Real.pi / 2 =
              (1 - y) * (Real.pi / 2) from by ring,
            mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]
          ring,
        hys]
  · rw [heq]
    refine ⟨0, ?_⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
      ⟨le_refl 0, by positivity⟩, if_pos (by positivity : (0:ℝ) ≤ Real.pi / 2)]
    rw [show (0:ℝ) / (Real.pi / 2) = 0 from by simp, srcOuterDn_zero]
    exact hout₂.symm
  · exact absurd hσ2 (not_le.mpr hgt)

/-- `γ '' Icc θ₂ θ₁ ⊆ range (tgtDnB _ false)`. -/
theorem arc_subset_range_dnFalse (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S) :
    γ '' Set.Icc θ₂ θ₁ ⊆ Set.range (tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂) := by
  rintro z ⟨θ, ⟨hθ1, hθ2⟩, rfl⟩
  have hden : (0:ℝ) < θ₁ - θ₂ := by linarith
  rcases eq_or_lt_of_le hθ2 with heq | hlt
  · rw [heq]
    refine ⟨Real.pi, ?_⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂
      ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩,
      if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl]
    rw [tgtCut₁,
      show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [div_eq_one_iff_eq (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]; ring,
      show s₁ + 1 * (t₁ - s₁) = t₁ from by ring]
    exact hγ₁.symm
  · set u : ℝ := (θ₁ - θ) / (θ₁ - θ₂) with hudef
    have hu0 : 0 < u := by rw [hudef]; exact div_pos (by linarith) hden
    have hu1 : u ≤ 1 := by rw [hudef, div_le_one hden]; linarith
    have hval : θ₁ + u * (θ₂ - θ₁) = θ := by rw [hudef]; field_simp; ring
    refine ⟨Real.pi + u * (Real.pi / 2), ?_⟩
    have hτmem : Real.pi + u * (Real.pi / 2) ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
      ⟨by nlinarith [hu0, Real.pi_pos], by nlinarith [hu1, Real.pi_pos]⟩
    rw [tgtDnB_of_mem_Ico S t₁ s₁ t₂ s₂ false θ₁ θ₂ hτmem,
      if_neg (by nlinarith [hu0, Real.pi_pos] :
        ¬ (Real.pi + u * (Real.pi / 2) ≤ Real.pi / 2)),
      if_neg (by nlinarith [hu0, Real.pi_pos] :
        ¬ (Real.pi + u * (Real.pi / 2) ≤ Real.pi)),
      if_pos (by nlinarith [hu1, Real.pi_pos] :
        Real.pi + u * (Real.pi / 2) ≤ 3 * Real.pi / 2),
      if_neg Bool.false_ne_true]
    rw [show (Real.pi + u * (Real.pi / 2) - Real.pi) / (Real.pi / 2) = u from by
      rw [show Real.pi + u * (Real.pi / 2) - Real.pi = u * (Real.pi / 2) from by ring,
        mul_div_cancel_right₀ _ (by positivity : (Real.pi : ℝ) / 2 ≠ 0)]]
    rw [hval]

/-! ## The three trace-difference identities -/

theorem tgtUpB_false_traceDiff (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ : ℝ} (ht₁ : t₁ < s₁) (ht₂ : t₂ < s₂) {θ₁ θ₂ : ℝ}
    (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * cutDir S = cutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * cutDir S = -cutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    Set.range (tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (cut₁ S t₁ s₁ ∪ cut₂ S t₂ s₂ ∪ γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂) \
        Metric.sphere (0 : ℂ) 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzr, hzs⟩
    obtain ⟨τ, rfl⟩ := hzr
    rcases tgtUpB_false_mem_trace S ht₁.le ht₂.le hθ' τ with h | h
    · exact absurd h hzs
    · exact ⟨h, hzs⟩
  · rintro z ⟨hzu, hzs⟩
    exact ⟨Set.union_subset (Set.union_subset
      (cut₁_subset_range_upFalse S ht₁ hout₁ hγ₁)
      (cut₂_subset_range_upFalse S ht₂ hout₂))
      (arc_subset_range_upFalse S hθ' hγ₂) hzu, hzs⟩

theorem tgtDnB_true_traceDiff (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ : ℝ} (ht₁ : t₁ < s₁) (ht₂ : t₂ < s₂) {θ₁ θ₂ : ℝ}
    (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * cutDir S = cutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * cutDir S = -cutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    Set.range (tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (cut₁ S t₁ s₁ ∪ cut₂ S t₂ s₂ ∪ γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂) \
        Metric.sphere (0 : ℂ) 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzr, hzs⟩
    obtain ⟨τ, rfl⟩ := hzr
    rcases tgtDnB_true_mem_trace S ht₁.le ht₂.le hθ' τ with h | h
    · exact absurd h hzs
    · exact ⟨h, hzs⟩
  · rintro z ⟨hzu, hzs⟩
    exact ⟨Set.union_subset (Set.union_subset
      (cut₁_subset_range_dn S ht₁ true hout₁)
      (cut₂_subset_range_dnTrue S ht₂ hout₂ hγ₂))
      (arc_subset_range_dnTrue S hθ' hγ₁) hzu, hzs⟩

theorem tgtDnB_false_traceDiff (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    {t₁ s₁ t₂ s₂ : ℝ} (ht₁ : t₁ < s₁) (ht₂ : t₂ < s₂) {θ₁ θ₂ : ℝ}
    (hθ : θ₂ < θ₁)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * cutDir S = cutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * cutDir S = -cutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S) :
    Set.range (tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (cut₁ S t₁ s₁ ∪ cut₂ S t₂ s₂ ∪ γ '' Set.Icc θ₂ θ₁) \ Metric.sphere (0 : ℂ) 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzr, hzs⟩
    obtain ⟨τ, rfl⟩ := hzr
    rcases tgtDnB_false_mem_trace S ht₁.le ht₂.le hθ τ with h | h
    · exact absurd h hzs
    · exact ⟨h, hzs⟩
  · rintro z ⟨hzu, hzs⟩
    exact ⟨Set.union_subset (Set.union_subset
      (cut₁_subset_range_dn S ht₁ false hout₁)
      (cut₂_subset_range_dnFalse S ht₂ hout₂ hγ₂))
      (arc_subset_range_dnFalse S hθ hγ₁) hzu, hzs⟩

theorem tgtCurvesTraceDiff {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : t₁ < s₁) (ht₂ : t₂ < s₂) {θ₁ θ₂ : ℝ} (hθ : θ₂ < θ₁)
    (hθ' : θ₁ < θ₂ + 2 * Real.pi)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hγ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hγ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S) :
    (Set.range (Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ false θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ ∪
        γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂) \ Metric.sphere (0 : ℂ) 1) ∧
    (Set.range (Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ true θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ ∪
        γ '' Set.Icc (θ₁ - 2 * Real.pi) θ₂) \ Metric.sphere (0 : ℂ) 1) ∧
    (Set.range (Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ false θ₁ θ₂) \ Metric.sphere (0 : ℂ) 1 =
      (Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂ ∪
        γ '' Set.Icc θ₂ θ₁) \ Metric.sphere (0 : ℂ) 1) := by
  exact ⟨tgtUpB_false_traceDiff S ht₁ ht₂ hθ' hout₁ hγ₁ hout₂ hγ₂,
    tgtDnB_true_traceDiff S ht₁ ht₂ hθ' hout₁ hγ₁ hout₂ hγ₂,
    tgtDnB_false_traceDiff S ht₁ ht₂ hθ hout₁ hγ₁ hout₂ hγ₂⟩

end Work.SphereJordan
