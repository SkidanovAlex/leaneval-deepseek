import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71Fc_imag_re_eq
import Submission.Work.ZeroFreeTables.tf71cf_eq_D
import Submission.Work.ZeroFreeTables.tf71_J_closed
import Submission.Work.ZeroFreeTables.tf71_key_ring
import Submission.Work.ZeroFreeTables.tf71_ibp_phi
import Submission.Work.ZeroFreeTables.tf71_cont_phi

namespace Work.ZeroFreeTables

noncomputable section

/-- The explicit trigonometric polynomial `D` in the `u`-variable into which the closed
form `tf71cf` transforms under `x = u/ζ`; it is the convolution `g ∗ g` for HB Lemma 7.1. -/
def tf71D (θ x : ℝ) : ℝ :=
  (θ - x/2 - Real.sin θ * Real.cos θ) * Real.cos x + Real.cos θ ^ 2 * (2*θ - x)
    + (Real.cos θ ^ 2 + 1/2) * Real.sin x - 2 * Real.sin θ * Real.cos θ

/-! ### The key positivity statement -/

/-- Integration by parts gives `(1-c²)·∫₀^{2θ}cos(cu)D(u)du = ∫₀^{2θ}cos(cu)R(u)du`, the closed
form of the latter is the explicit expression `Jc`, and `(1-c²)·Jc = 2·(...)²`.  Hence `φ ≥ 0`. -/
lemma tf71_phi_nonneg (θ : ℝ) (c : ℝ) :
    0 ≤ ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u := by
  have hgeneral : ∀ c : ℝ, c ≠ 0 → c ≠ 1 → c ≠ -1 →
      0 ≤ ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u := by
    intro c hc0 hc1 hc2
    have h1 : (1 - c^2) * (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u)
        = 2 * Real.cos θ ^ 2 * (Real.sin (c*θ))^2 / c^2
          - (Real.cos θ * Real.sin (c*θ) - Real.sin θ * Real.cos (c*θ))^2 / (c-1)
          + (Real.cos θ * Real.sin (c*θ) + Real.sin θ * Real.cos (c*θ))^2 / (c+1)
          - 4 * Real.sin θ * Real.cos θ * Real.sin (c*θ) * Real.cos (c*θ) / c := by
      simp only [tf71D]
      rw [tf71_ibp_phi, tf71_J_closed θ c hc0 hc1 hc2]
    have h2 : (1 - c^2)^2 * (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u)
        = 2 * (Real.sin θ * Real.cos (c*θ) - Real.cos θ * Real.sin (c*θ) / c)^2 := by
      rw [show (1 - c^2)^2 * (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u)
            = (1 - c^2) * ((1 - c^2) * ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u)
            from by ring]
      rw [h1, tf71_key_ring θ c hc0 hc1 hc2]
    have hA : 0 < (1 - c^2)^2 := by
      apply sq_pos_of_ne_zero
      intro hc
      have hfac : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfac with h | h
      · exact hc1 (by linarith)
      · exact hc2 (by linarith)
    by_contra hneg
    push Not at hneg
    nlinarith [h2, hA, hneg]
  by_cases hc : c = 0 ∨ c = 1 ∨ c = -1
  · have hcont : Continuous
        (fun c : ℝ => ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u) := by
      simpa only [tf71D] using tf71_cont_phi θ
    have hclosed : IsClosed
        {c : ℝ | 0 ≤ ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u} :=
      isClosed_le continuous_const hcont
    have hfin : ({0, 1, -1} : Set ℝ).Finite :=
      ((Set.finite_singleton (-1)).insert 1).insert 0
    have hdense : Dense ({0, 1, -1}ᶜ : Set ℝ) := hfin.countable.dense_compl ℝ
    have hsub : ({0, 1, -1}ᶜ : Set ℝ) ⊆
        {c : ℝ | 0 ≤ ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u} := by
      intro c' hc'
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc'
      exact hgeneral c' hc'.1 hc'.2.1 hc'.2.2
    have : (Set.univ : Set ℝ) ⊆
        {c : ℝ | 0 ≤ ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * tf71D θ u} := by
      rw [← Dense.closure_eq hdense]
      exact hclosed.closure_subset_iff.mpr hsub
    exact this (Set.mem_univ c)
  · push Not at hc
    exact hgeneral c hc.1 hc.2.1 hc.2.2

/-! ### The target -/

theorem tf71Fc_imag_re_nonneg (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (y : ℝ) : 0 ≤ (Work.ZeroFreeTables.tf71Fc θ lam ((y : ℂ) * Complex.I)).re := by
  have hζ : 0 < tf71ζ θ lam := tf71ζ_pos hθ0 hθ1 hlam
  have hζne : tf71ζ θ lam ≠ 0 := ne_of_gt hζ
  have hζγ : tf71ζ θ lam * tf71γ θ lam = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
  have hγ : 0 < tf71γ θ lam := tf71γ_pos hθ0 hθ1 hlam
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  -- step A: real part of the Laplace transform along the imaginary axis
  rw [tf71Fc_imag_re_eq θ lam hθ0 hθ1 hlam y]
  -- step B: on `[0,2γ]` the test function is its closed form
  have hA : (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        Real.cos (y * t) * tf71f θ lam t)
      = ∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.cos (y * t) * tf71cf θ lam t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 2 * tf71γ θ lam)] at ht
    unfold tf71f
    rw [if_pos ht.1, min_eq_left ht.2]
  rw [hA]
  -- step C: substitute `u = ζ t`
  have hB : (∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.cos (y * t) * tf71cf θ lam t)
      = (tf71ζ θ lam)⁻¹ * ∫ u in (0:ℝ)..(2*θ),
          Real.cos ((y / tf71ζ θ lam) * u) * tf71cf θ lam (u / tf71ζ θ lam) := by
    rw [show (∫ t in (0:ℝ)..(2 * tf71γ θ lam), Real.cos (y * t) * tf71cf θ lam t)
          = ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
              (fun u => Real.cos ((y / tf71ζ θ lam) * u) * tf71cf θ lam (u / tf71ζ θ lam))
                (tf71ζ θ lam * t) from by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only
      have h1 : (tf71ζ θ lam * t) / tf71ζ θ lam = t := mul_div_cancel_left₀ t hζne
      have h2 : (y / tf71ζ θ lam) * (tf71ζ θ lam * t) = y * t := by field_simp
      rw [h2, h1]]
    rw [intervalIntegral.integral_comp_mul_left
          (f := fun u => Real.cos ((y / tf71ζ θ lam) * u) * tf71cf θ lam (u / tf71ζ θ lam))
          hζne,
        show tf71ζ θ lam * (0:ℝ) = 0 by ring,
        show tf71ζ θ lam * (2 * tf71γ θ lam) = 2 * θ by
          calc tf71ζ θ lam * (2 * tf71γ θ lam) = 2 * (tf71ζ θ lam * tf71γ θ lam) := by ring
            _ = 2 * θ := by rw [hζγ],
        smul_eq_mul]
  rw [hB]
  -- step D: the pointwise identity `tf71cf(u/ζ) = (λ(1+tan²θ)/(sinθcosθ)) · D(u)`
  have hC : (∫ u in (0:ℝ)..(2*θ),
        Real.cos ((y / tf71ζ θ lam) * u) * tf71cf θ lam (u / tf71ζ θ lam))
      = (lam * (1 + Real.tan θ ^ 2) / (Real.sin θ * Real.cos θ)) *
          ∫ u in (0:ℝ)..(2*θ), Real.cos ((y / tf71ζ θ lam) * u) * tf71D θ u := by
    rw [show (∫ u in (0:ℝ)..(2*θ),
          Real.cos ((y / tf71ζ θ lam) * u) * tf71cf θ lam (u / tf71ζ θ lam))
        = ∫ u in (0:ℝ)..(2*θ), (lam * (1 + Real.tan θ ^ 2) / (Real.sin θ * Real.cos θ)) *
            (Real.cos ((y / tf71ζ θ lam) * u) * tf71D θ u) from by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [show tf71D θ u = (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.cos u
          + Real.cos θ ^ 2 * (2 * θ - u) + (Real.cos θ ^ 2 + 1 / 2) * Real.sin u
          - 2 * Real.sin θ * Real.cos θ from rfl]
      rw [tf71cf_eq_D θ lam u hθ0 hθ1 hlam]
      ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hC]
  have hk : 0 ≤ lam * (1 + Real.tan θ ^ 2) / (Real.sin θ * Real.cos θ) :=
    div_nonneg (mul_nonneg hlam.le (by positivity)) (mul_pos hsin hcos).le
  exact mul_nonneg (le_of_lt (inv_pos.mpr hζ))
    (mul_nonneg hk (tf71_phi_nonneg θ (y / tf71ζ θ lam)))

end

end Work.ZeroFreeTables
