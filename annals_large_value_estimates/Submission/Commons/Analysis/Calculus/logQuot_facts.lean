import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_uIcc

namespace Commons.Analysis.Calculus

open MeasureTheory Set
open scoped Topology

private lemma one_add_mul_pos (s x t : ℝ) (hs : |s| < 1/2)
    (hx : x ∈ Set.Icc (s - 1/4) (s + 1/4)) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    0 < 1 + x * t := by
  have hxs : |x - s| ≤ 1/4 := by
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxabs : |x| ≤ |s| + 1/4 := by
    calc |x| = |(x - s) + s| := by rw [show (x - s) + s = x from by ring]
      _ ≤ |x - s| + |s| := abs_add_le _ _
      _ ≤ 1/4 + |s| := by linarith
      _ = |s| + 1/4 := by ring
  have ht0 : (0:ℝ) ≤ t := by simpa using ht.1
  have ht1 : t ≤ 1 := by simpa using ht.2
  have htabs : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hmul : |x * t| < 3/4 := by
    rw [abs_mul]
    calc |x| * |t| ≤ (|s| + 1/4) * 1 :=
          mul_le_mul hxabs htabs (abs_nonneg t) (by linarith [abs_nonneg s])
      _ = |s| + 1/4 := by ring
      _ < 3/4 := by linarith
  have hb := abs_le.mp (le_of_lt hmul)
  linarith [hb.1]

private lemma hasDerivAt_div_one_add_mul (s t : ℝ) (h : 1 + s * t ≠ 0) :
    HasDerivAt (fun u : ℝ => t / (1 + u * t)) (-(t ^ 2 / (1 + s * t) ^ 2)) s := by
  have hg : HasDerivAt (fun u : ℝ => 1 + u * t) t s := by
    simpa using ((hasDerivAt_id s).mul_const t).const_add 1
  have h1 : HasDerivAt (fun u : ℝ => t / (1 + u * t)) (t * (-t / (1 + s * t) ^ 2)) s := by
    have hinv := hg.fun_inv h
    have := hinv.const_mul t
    simpa [div_eq_mul_inv] using this
  refine h1.congr_deriv ?_
  ring_nf

private lemma hasDerivAt_neg_div_sq (s t : ℝ) (h : 1 + s * t ≠ 0) :
    HasDerivAt (fun u : ℝ => -(t ^ 2 / (1 + u * t) ^ 2)) (2 * t ^ 3 / (1 + s * t) ^ 3) s := by
  have hg : HasDerivAt (fun u : ℝ => 1 + u * t) t s := by
    simpa using ((hasDerivAt_id s).mul_const t).const_add 1
  have hsq : HasDerivAt (fun u : ℝ => (1 + u * t) ^ 2) (2 * (1 + s * t) * t) s := by
    have hp := hg.fun_pow 2
    simpa using hp
  have hinv : HasDerivAt (fun u : ℝ => ((1 + u * t) ^ 2)⁻¹)
      (-(2 * (1 + s * t) * t) / ((1 + s * t) ^ 2) ^ 2) s :=
    hsq.fun_inv (pow_ne_zero 2 h)
  have hc : HasDerivAt (fun u : ℝ => t ^ 2 * ((1 + u * t) ^ 2)⁻¹)
      (t ^ 2 * (-(2 * (1 + s * t) * t) / ((1 + s * t) ^ 2) ^ 2)) s := by
    simpa using hinv.const_mul (t ^ 2)
  refine hc.fun_neg.congr_deriv ?_
  have h1 : (1 + s*t)^2 ≠ 0 := pow_ne_zero 2 h
  have h2 : ((1 + s*t)^2)^2 ≠ 0 := pow_ne_zero 2 h1
  have h3 : (1 + s*t)^3 ≠ 0 := pow_ne_zero 3 h
  field_simp

private lemma continuousOn_div_one_add_mul (s : ℝ)
    (hden : ∀ t ∈ Set.uIcc (0:ℝ) 1, 1 + s * t ≠ 0) :
    ContinuousOn (fun t : ℝ => t / (1 + s * t)) (Set.uIcc (0:ℝ) 1) := by
  apply ContinuousOn.div
  · exact continuous_id.continuousOn
  · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  · intro t ht; exact hden t ht

private lemma integral_div_one_add_mul (s : ℝ) (hs : s ≠ 0)
    (hden : ∀ t ∈ Set.uIcc (0:ℝ) 1, 1 + s * t ≠ 0) :
    ∫ t in (0:ℝ)..1, t / (1 + s * t) = 1/s - Real.log (1 + s) / s^2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => t / s - Real.log (1 + s * t) / s^2) (t / (1 + s * t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t / s) (1 / s) t := (hasDerivAt_id t).div_const s
    have hg : HasDerivAt (fun t : ℝ => 1 + s * t) s t := by
      simpa using ((hasDerivAt_id t).const_mul s).const_add 1
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + s * t)) (s / (1 + s * t)) t :=
      hg.log (hden t ht)
    have h3 : HasDerivAt (fun t : ℝ => Real.log (1 + s * t) / s^2) ((s / (1 + s * t)) / s^2) t :=
      h2.div_const (s^2)
    have hsub := h1.sub h3
    refine hsub.congr_deriv ?_
    have hne : 1 + s * t ≠ 0 := hden t ht
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t / (1 + s * t)) volume 0 1 :=
    (continuousOn_div_one_add_mul s hden).intervalIntegrable
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hmain]
  simp [Real.log_one]

private lemma parametric_hasDerivAt_first (s : ℝ) (hs : |s| < 1/2) :
    HasDerivAt (fun s : ℝ => ∫ t in (0:ℝ)..1, t / (1 + s * t))
      (-(∫ t in (0:ℝ)..1, t ^ 2 / (1 + s * t) ^ 2)) s := by
  have h₁ : s - 1/4 < s := by norm_num
  have h₂ : s < s + 1/4 := by norm_num
  have hne : ∀ x ∈ Set.Icc (s - 1/4) (s + 1/4), ∀ t ∈ Set.uIcc (0:ℝ) 1, 1 + x * t ≠ 0 :=
    fun x hx t ht => ne_of_gt (one_add_mul_pos s x t hs hx ht)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.2 / (1 + p.1 * p.2))
      (Set.Icc (s - 1/4) (s + 1/4) ×ˢ Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.div
    · exact continuous_snd.continuousOn
    · exact (continuous_const.add (continuous_fst.mul continuous_snd)).continuousOn
    · intro p hp; exact hne p.1 hp.1 p.2 hp.2
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => -(p.2 ^ 2 / (1 + p.1 * p.2) ^ 2))
      (Set.Icc (s - 1/4) (s + 1/4) ×ˢ Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · exact (continuous_snd.pow 2).continuousOn
    · exact ((continuous_const.add (continuous_fst.mul continuous_snd)).pow 2).continuousOn
    · intro p hp; exact pow_ne_zero 2 (hne p.1 hp.1 p.2 hp.2)
  have hd : ∀ x ∈ Set.Icc (s - 1/4) (s + 1/4), ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => t / (1 + u * t)) (-(t ^ 2 / (1 + x * t) ^ 2)) x :=
    fun x hx t ht => hasDerivAt_div_one_add_mul x t (hne x hx t ht)
  have key := intervalIntegral_hasDerivAt_of_continuousOn_uIcc
      (F := fun x t : ℝ => t / (1 + x * t))
      (F' := fun x t : ℝ => -(t ^ 2 / (1 + x * t) ^ 2))
      (s₀ := s) (a := (0:ℝ)) (b := 1) (s₁ := s - 1/4) (s₂ := s + 1/4)
      h₁ h₂ hcont hcont' hd
  simpa [intervalIntegral.integral_neg] using key

private lemma parametric_hasDerivAt_second (s : ℝ) (hs : |s| < 1/2) :
    HasDerivAt (fun u : ℝ => -(∫ t in (0:ℝ)..1, t ^ 2 / (1 + u * t) ^ 2))
      (∫ t in (0:ℝ)..1, 2 * t ^ 3 / (1 + s * t) ^ 3) s := by
  have h₁ : s - 1/4 < s := by norm_num
  have h₂ : s < s + 1/4 := by norm_num
  have hne : ∀ x ∈ Set.Icc (s - 1/4) (s + 1/4), ∀ t ∈ Set.uIcc (0:ℝ) 1, 1 + x * t ≠ 0 :=
    fun x hx t ht => ne_of_gt (one_add_mul_pos s x t hs hx ht)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => -(p.2 ^ 2 / (1 + p.1 * p.2) ^ 2))
      (Set.Icc (s - 1/4) (s + 1/4) ×ˢ Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.neg
    apply ContinuousOn.div
    · exact (continuous_snd.pow 2).continuousOn
    · exact ((continuous_const.add (continuous_fst.mul continuous_snd)).pow 2).continuousOn
    · intro p hp; exact pow_ne_zero 2 (hne p.1 hp.1 p.2 hp.2)
  have hcont' : ContinuousOn (fun p : ℝ × ℝ => 2 * p.2 ^ 3 / (1 + p.1 * p.2) ^ 3)
      (Set.Icc (s - 1/4) (s + 1/4) ×ˢ Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.div
    · exact ((continuous_snd.pow 3).const_mul 2).continuousOn
    · exact ((continuous_const.add (continuous_fst.mul continuous_snd)).pow 3).continuousOn
    · intro p hp; exact pow_ne_zero 3 (hne p.1 hp.1 p.2 hp.2)
  have hd : ∀ x ∈ Set.Icc (s - 1/4) (s + 1/4), ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => -(t ^ 2 / (1 + u * t) ^ 2)) (2 * t ^ 3 / (1 + x * t) ^ 3) x :=
    fun x hx t ht => hasDerivAt_neg_div_sq x t (hne x hx t ht)
  have key := intervalIntegral_hasDerivAt_of_continuousOn_uIcc
      (F := fun x t : ℝ => -(t ^ 2 / (1 + x * t) ^ 2))
      (F' := fun x t : ℝ => 2 * t ^ 3 / (1 + x * t) ^ 3)
      (s₀ := s) (a := (0:ℝ)) (b := 1) (s₁ := s - 1/4) (s₂ := s + 1/4)
      h₁ h₂ hcont hcont' hd
  simpa [intervalIntegral.integral_neg] using key

theorem logQuot_facts :
    (∫ t in (0:ℝ)..1, t / (1 + (0:ℝ) * t)) = 1/2 ∧
    (∀ s : ℝ, |s| < 1/2 →
      HasDerivAt (fun s : ℝ => ∫ t in (0:ℝ)..1, t / (1 + s * t))
        (-(∫ t in (0:ℝ)..1, t^2 / (1 + s * t)^2)) s) ∧
    (∀ s : ℝ, |s| < 1/2 →
      HasDerivAt (fun u : ℝ => -(∫ t in (0:ℝ)..1, t^2 / (1 + u * t)^2))
        (∫ t in (0:ℝ)..1, 2 * t^3 / (1 + s * t)^3) s) ∧
    (∀ s : ℝ, |s| < 1/2 →
      s^2 * (∫ t in (0:ℝ)..1, t / (1 + s * t)) = s - Real.log (1 + s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [integral_id]
  · intro s hs; exact parametric_hasDerivAt_first s hs
  · intro s hs; exact parametric_hasDerivAt_second s hs
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0; simp
    · have hden : ∀ t ∈ Set.uIcc (0:ℝ) 1, 1 + s * t ≠ 0 :=
        fun t ht => ne_of_gt (one_add_mul_pos s s t hs ⟨by linarith, by linarith⟩ ht)
      rw [integral_div_one_add_mul s hs0 hden]
      field_simp

end Commons.Analysis.Calculus