import Mathlib
import Submission.Unif.UnivalentCompactness
import Submission.Work.Motion.deriv_rescale
import Submission.Work.Motion.norm_deriv_mob
import Submission.Work.Motion.schwarz_pick_deriv

namespace Work.Motion

open Metric Set
open scoped ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

/-! ## TEMPORARY placeholders for the two delegated lemmas -/

private theorem growth_lower_local :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ h z) →
      InjOn h (ball (0 : ℂ) 1) → h 0 = 0 → deriv h 0 = 1 →
      ∀ t ∈ ball (0 : ℂ) 1, κ * ‖t‖ ≤ ‖h t‖ := by
  obtain ⟨c₀, hc₀pos, hlandau⟩ := Commons.Analysis.Complex.Landau.landau_theorem
  refine ⟨c₀ / Real.pi, div_pos hc₀pos Real.pi_pos, ?_⟩
  intro h hh hinj h0 hd0 t ht
  by_cases ht0 : t = 0
  · subst ht0
    simp [h0]
  · have htlt : ‖t‖ < 1 := by simpa [mem_ball, dist_eq_norm] using ht
    have hrpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have hrc : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
    have hmem_of : ∀ z : ℂ, ‖z‖ < 1 → (‖t‖ : ℂ) * z ∈ ball (0:ℂ) 1 := by
      intro z hz
      rw [mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrpos]
      nlinarith [htlt, hz, norm_nonneg z, norm_nonneg t]
    have hg_an : ∀ z ∈ ball (0:ℂ) 1,
        AnalyticAt ℂ (fun z => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ)) z := by
      intro z hz
      have hzn : ‖z‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
      have hinner : AnalyticAt ℂ (fun z : ℂ => (‖t‖:ℂ)*z) z := analyticAt_const.mul analyticAt_id
      have h1 : AnalyticAt ℂ (fun z : ℂ => h ((‖t‖:ℂ)*z)) z :=
        (hh ((‖t‖:ℂ)*z) (hmem_of z hzn)).comp hinner
      exact h1.div_const (c := (‖t‖:ℂ))
    have hg_inj : InjOn (fun z => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ)) (ball (0:ℂ) 1) := by
      intro z1 hz1 z2 hz2 heq
      have hz1n : ‖z1‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz1
      have hz2n : ‖z2‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz2
      have he : h ((‖t‖:ℂ)*z1) = h ((‖t‖:ℂ)*z2) := by
        have hh' : h ((‖t‖:ℂ)*z1) * (‖t‖:ℂ)⁻¹ = h ((‖t‖:ℂ)*z2) * (‖t‖:ℂ)⁻¹ := by
          simpa [div_eq_mul_inv] using heq
        exact mul_right_cancel₀ (inv_ne_zero hrc) hh'
      exact mul_left_cancel₀ hrc (hinj (hmem_of z1 hz1n) (hmem_of z2 hz2n) he)
    have hg0 : (fun z => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ)) 0 = 0 := by
      simp [h0]
    have hgd : deriv (fun z => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ)) 0 = 1 := by
      have h0mem : (0:ℂ) ∈ ball (0:ℂ) 1 := by simp [mem_ball, dist_self]
      have hf : HasDerivAt h (deriv h 0) ((‖t‖:ℂ)*0) := by
        rw [mul_zero]
        exact (hh 0 h0mem).differentiableAt.hasDerivAt
      have hinner : HasDerivAt (fun z : ℂ => (‖t‖:ℂ)*z) (‖t‖:ℂ) 0 := by
        simpa using (hasDerivAt_id (0:ℂ)).const_mul (‖t‖:ℂ)
      have hcomp : HasDerivAt (fun z : ℂ => h ((‖t‖:ℂ)*z)) (deriv h 0 * (‖t‖:ℂ)) 0 := by
        simpa [Function.comp_def] using hf.comp 0 hinner
      have h2 : HasDerivAt (fun z : ℂ => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ))
          ((deriv h 0 * (‖t‖:ℂ))/(‖t‖:ℂ)) 0 := hcomp.div_const (‖t‖:ℂ)
      rw [h2.deriv, hd0, one_mul, div_self hrc]
    have hw : h t / (‖t‖:ℂ) ∉ (fun z => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ)) '' (ball (0:ℂ) 1) := by
      rintro ⟨z, hz, hzeq⟩
      have hzn : ‖z‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
      have he : h t = h ((‖t‖:ℂ)*z) := by
        have hh' : h ((‖t‖:ℂ)*z) * (‖t‖:ℂ)⁻¹ = h t * (‖t‖:ℂ)⁻¹ := by
          simpa [div_eq_mul_inv] using hzeq
        exact (mul_right_cancel₀ (inv_ne_zero hrc) hh').symm
      have ht_eq : t = (‖t‖:ℂ)*z := hinj ht (hmem_of z hzn) he
      have hnorm : ‖t‖ = ‖t‖ * ‖z‖ := by
        nth_rewrite 1 [ht_eq]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
      have hthis : ‖t‖ * (1 - ‖z‖) = 0 := by nlinarith [hnorm]
      have hp : 0 < ‖t‖ * (1 - ‖z‖) := mul_pos hrpos (by linarith)
      linarith
    have hwk := Commons.Analysis.Complex.Koebe.weak_koebe_of_landau hc₀pos hlandau
      (fun z => h ((‖t‖:ℂ)*z)/(‖t‖:ℂ)) hg_an hg_inj hg0 hgd (h t / (‖t‖:ℂ)) hw
    have hkey : ‖h t / (‖t‖:ℂ)‖ = ‖h t‖ / ‖t‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [hkey] at hwk
    exact (le_div_iff₀ hrpos).mp hwk

/-! ## Elementary helpers -/

/-- Monotonicity of `t ↦ (1+t)/(1-t)` on `[0,1)`. -/
private lemma div_one_sub_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (1 + a) / (1 - a) ≤ (1 + b) / (1 - b) := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - b := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-- `(1+t)/(1-t)` is nonnegative for `t < 1`. -/
private lemma div_one_sub_nonneg {t : ℝ} (h0 : 0 ≤ t) (ht : t < 1) : 0 ≤ (1 + t) / (1 - t) := by
  apply div_nonneg <;> linarith

/-- A holomorphic injection on the unit disc has nonvanishing derivative. -/
private lemma deriv_ne_zero_of_injOn_ball {g : ℂ → ℂ}
    (hgan : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ g z) (hginj : InjOn g (ball (0 : ℂ) 1))
    {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) : deriv g u ≠ 0 := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hr : (0 : ℝ) < (1 - ‖u‖) / 2 := by linarith
  have hsub : ball u ((1 - ‖u‖) / 2) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    have h1 : ‖w‖ ≤ ‖w - u‖ + ‖u‖ := by
      calc ‖w‖ = ‖(w - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le _ _
    linarith
  exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr (hgan u hu)
    (InjOn.mono hsub hginj)

/-- The Möbius self-map of the disc `ζ ↦ (ζ+u)/(1+conj u * ζ)`. -/
private def mobZu (u : ℂ) : ℂ → ℂ := fun ζ => (ζ + u) / (1 + conj u * ζ)

private lemma conj_neg' (u : ℂ) : conj (-u) = -conj u := by simp

private lemma mobZu_eq_mob (u : ℂ) : mobZu u = mob (-u) := by
  funext ζ
  simp only [mobZu, mob_apply, sub_neg_eq_add]
  rw [conj_neg']
  ring_nf

private lemma conj_mul_self (u : ℂ) : conj u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']; norm_num

private lemma one_add_conj_mul_ne_zero {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) :
    (1 : ℂ) + conj z * ζ ≠ 0 := by
  intro hh
  have h1 : ‖(1:ℂ) + conj z * ζ‖ = 0 := by rw [hh, norm_zero]
  have h3 : ‖(1:ℂ) + conj z * ζ - conj z * ζ‖ ≤ ‖(1:ℂ) + conj z * ζ‖ + ‖conj z * ζ‖ :=
    norm_sub_le _ _
  rw [add_sub_cancel_right, norm_one, h1, zero_add, norm_mul, Complex.norm_conj] at h3
  nlinarith [norm_nonneg z, norm_nonneg ζ]

private lemma mobZu_deriv_eq {u t : ℂ} (ht : (1 : ℂ) + conj u * t ≠ 0) :
    deriv (mobZu u) t = (1 - conj u * u) / (1 + conj u * t) ^ 2 := by
  have ha : (1 : ℂ) - conj (-u) * t ≠ 0 := by
    rw [show (1 : ℂ) - conj (-u) * t = 1 + conj u * t from by rw [conj_neg']; ring]
    exact ht
  rw [mobZu_eq_mob, deriv_mob ha]
  have hn : (1 : ℂ) - conj (-u) * (-u) = 1 - conj u * u := by
    rw [conj_neg']; ring
  have hd : (1 : ℂ) - conj (-u) * t = 1 + conj u * t := by
    rw [conj_neg']; ring
  rw [hn, hd]

private lemma mobZ_local (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) :
    DifferentiableOn ℂ (fun u => (u + z) / (1 + conj z * u)) (ball 0 1) ∧
    MapsTo (fun u => (u + z) / (1 + conj z * u)) (ball 0 1) (ball 0 1) ∧
    InjOn (fun u => (u + z) / (1 + conj z * u)) (ball 0 1) ∧
    (fun u => (u + z) / (1 + conj z * u)) 0 = z ∧
    deriv (fun u => (u + z) / (1 + conj z * u)) (-z) = 1 / (1 - ‖z‖^2) ∧
    deriv (fun u => (u + z) / (1 + conj z * u)) 0 = 1 - ‖z‖^2 ∧
    (∀ u v : ℂ, u ∈ ball (0:ℂ) 1 → v ∈ ball (0:ℂ) 1 →
      (fun w => (w + u) / (1 + conj u * w)) ((v - u)/(1 - conj u * v)) = v ∧
      ((v - u)/(1 - conj u * v)) ∈ ball (0:ℂ) 1 ∧
      ‖v - u‖ ≤ (1 + ‖u‖*‖v‖) * ‖(v - u)/(1 - conj u * v)‖) := by
  have hzn : ‖(-z)‖ < 1 := by rw [norm_neg]; exact mem_ball_zero_iff.mp hz
  obtain ⟨hmapsM, hdiffM, _⟩ := mob_disc hzn
  have hdiff : DifferentiableOn ℂ (mobZu z) (ball (0:ℂ) 1) := by
    rw [mobZu_eq_mob]; exact hdiffM
  have hmaps : MapsTo (mobZu z) (ball (0:ℂ) 1) (ball (0:ℂ) 1) := by
    rw [mobZu_eq_mob]; exact hmapsM
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hzz : (1 : ℂ) - conj z * z ≠ 0 := by
    rw [conj_mul_self z, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    nlinarith [norm_nonneg z]
  have hinj : InjOn (mobZu z) (ball (0:ℂ) 1) := by
    intro ζ1 hζ1 ζ2 hζ2 heq
    have hd1 : (1 : ℂ) + conj z * ζ1 ≠ 0 :=
      one_add_conj_mul_ne_zero hznorm (mem_ball_zero_iff.mp hζ1)
    have hd2 : (1 : ℂ) + conj z * ζ2 ≠ 0 :=
      one_add_conj_mul_ne_zero hznorm (mem_ball_zero_iff.mp hζ2)
    rw [mobZu, mobZu, div_eq_div_iff hd1 hd2] at heq
    have h2 : ζ1 * (1 - conj z * z) = ζ2 * (1 - conj z * z) := by
      linear_combination heq
    exact mul_right_cancel₀ hzz h2
  have hm0 : mobZu z 0 = z := by simp [mobZu]
  have hdnz : deriv (mobZu z) (-z) = 1 / (1 - conj z * z) := by
    have hden : (1 : ℂ) + conj z * (-z) ≠ 0 := by
      rw [show (1:ℂ) + conj z * (-z) = 1 - conj z * z by ring]
      exact hzz
    rw [mobZu_deriv_eq hden]
    rw [show (1:ℂ) + conj z * (-z) = 1 - conj z * z by ring]
    field_simp
  have hd0 : deriv (mobZu z) 0 = 1 - conj z * z := by
    rw [mobZu_deriv_eq (by simp)]
    norm_num
  have hnr : (1 : ℂ) - conj z * z = ((1 - ‖z‖^2 : ℝ) : ℂ) := by
    rw [conj_mul_self z, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  have hinv : ∀ u v : ℂ, u ∈ ball (0:ℂ) 1 → v ∈ ball (0:ℂ) 1 →
      (fun w => (w + u) / (1 + conj u * w)) ((v - u)/(1 - conj u * v)) = v ∧
      ((v - u)/(1 - conj u * v)) ∈ ball (0:ℂ) 1 ∧
      ‖v - u‖ ≤ (1 + ‖u‖*‖v‖) * ‖(v - u)/(1 - conj u * v)‖ := by
    intro u v hu hv
    have hun : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    have hvn : ‖v‖ < 1 := mem_ball_zero_iff.mp hv
    have hden : (1 : ℂ) - conj u * v ≠ 0 := one_sub_conj_mul_ne_zero hun hvn
    have hmem : ((v - u)/(1 - conj u * v)) ∈ ball (0:ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
      have hlt : Complex.normSq (v - u) < Complex.normSq (1 - conj u * v) := by
        have h := normSq_one_sub_conj_mul u v
        have hu1 : Complex.normSq u < 1 := by
          rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
        have hv1 : Complex.normSq v < 1 := by
          rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg v]
        nlinarith [Complex.normSq_nonneg (v - u)]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt
      rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hlt
      exact hlt
    have hden2 : (1 : ℂ) + conj u * ((v - u)/(1 - conj u * v)) ≠ 0 :=
      one_add_conj_mul_ne_zero hun (mem_ball_zero_iff.mp hmem)
    refine ⟨?_, hmem, ?_⟩
    · show ((v - u)/(1 - conj u * v) + u) / (1 + conj u * ((v - u)/(1 - conj u * v))) = v
      have hden' : (1 : ℂ) - v * conj u ≠ 0 := by rw [mul_comm]; exact hden
      rw [div_eq_iff hden2]
      field_simp [hden, hden']
      ring
    · have hdenpos : 0 < ‖1 - conj u * v‖ := norm_pos_iff.mpr hden
      have h1 : ‖1 - conj u * v‖ ≤ 1 + ‖u‖ * ‖v‖ := by
        calc ‖(1:ℂ) - conj u * v‖ ≤ ‖(1:ℂ)‖ + ‖conj u * v‖ := norm_sub_le _ _
          _ = 1 + ‖u‖ * ‖v‖ := by rw [norm_one, norm_mul, Complex.norm_conj]
      rw [norm_div, ← mul_div_assoc, le_div_iff₀ hdenpos]
      nlinarith [norm_nonneg (v - u)]
  refine ⟨hdiff, hmaps, hinj, hm0, ?_, ?_, hinv⟩
  · change deriv (mobZu z) (-z) = 1 / (1 - ‖z‖^2)
    rw [hdnz, hnr]
    rw [show ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = 1 - (‖z‖ : ℂ) ^ 2 from by push_cast; ring]
  · change deriv (mobZu z) 0 = 1 - ‖z‖^2
    rw [hd0, hnr]
    rw [show ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) = 1 - (‖z‖ : ℂ) ^ 2 from by push_cast; ring]

/-- The Koebe transform of `g` at the point `u`. -/
def koebeT (g : ℂ → ℂ) (u : ℂ) : ℂ → ℂ :=
  fun ζ => (g (mobZu u ζ) - g u) / (((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u)

/-- The Koebe transform of a holomorphic injection is a normalised holomorphic injection. -/
theorem koebeT_normalized {g : ℂ → ℂ} (hgan : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ g z)
    (hginj : InjOn g (ball (0 : ℂ) 1)) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1)
    (hgu : deriv g u ≠ 0) :
    (∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ (koebeT g u) ζ) ∧
      InjOn (koebeT g u) (ball (0 : ℂ) 1) ∧ koebeT g u 0 = 0 ∧ deriv (koebeT g u) 0 = 1 := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hcR : (0 : ℝ) < 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  have hcN : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcR.ne'
  have hcC : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u ≠ 0 := mul_ne_zero hcN hgu
  obtain ⟨hmdiff, hmmaps, hminj, hm0, hmdnz, hmd0, _hinv⟩ := mobZ_local u hu
  have hmmaps' : MapsTo (mobZu u) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := hmmaps
  have hminj' : InjOn (mobZu u) (ball (0 : ℂ) 1) := hminj
  have hm0' : mobZu u 0 = u := hm0
  have hdm0 : deriv (mobZu u) 0 = ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
    have hcast : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) = 1 - (‖u‖ : ℂ) ^ 2 := by push_cast; ring
    rw [hcast, show deriv (mobZu u) 0 = deriv (fun w : ℂ => (w + u) / (1 + conj u * w)) 0 from rfl]
    exact hmd0
  have hinner_an : ∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ (mobZu u) ζ :=
    fun ζ hζ => hmdiff.analyticAt (isOpen_ball.mem_nhds hζ)
  have han : ∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ (koebeT g u) ζ := by
    intro ζ hζ
    have hg_an : AnalyticAt ℂ g (mobZu u ζ) := hgan _ (hmmaps' hζ)
    have h1 : AnalyticAt ℂ (fun ζ => g (mobZu u ζ)) ζ := hg_an.comp (hinner_an ζ hζ)
    have h2 : AnalyticAt ℂ (fun ζ => g (mobZu u ζ) - g u) ζ := h1.sub analyticAt_const
    have h3 : AnalyticAt ℂ
        (fun ζ => (g (mobZu u ζ) - g u) / (((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u)) ζ :=
      h2.div_const (c := ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u)
    exact h3
  refine ⟨han, ?_, ?_, ?_⟩
  · intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    have hi1 : mobZu u ζ₁ ∈ ball (0 : ℂ) 1 := hmmaps' hζ₁
    have hi2 : mobZu u ζ₂ ∈ ball (0 : ℂ) 1 := hmmaps' hζ₂
    have heq' : (g (mobZu u ζ₁) - g u) / (((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u)
        = (g (mobZu u ζ₂) - g u) / (((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u) := heq
    rw [div_eq_div_iff hcC hcC] at heq'
    have hsub : g (mobZu u ζ₁) - g u = g (mobZu u ζ₂) - g u :=
      mul_right_cancel₀ hcC heq'
    have hge : g (mobZu u ζ₁) = g (mobZu u ζ₂) := by
      have h := hsub
      rw [sub_eq_add_neg, sub_eq_add_neg] at h
      exact add_right_cancel h
    exact hminj' hζ₁ hζ₂ (hginj hi1 hi2 hge)
  · unfold koebeT
    simp [hm0']
  · have hchain : deriv (fun ζ : ℂ => g (mobZu u ζ)) 0
        = deriv g u * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : HasDerivAt (mobZu u) ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) 0 := by
        have := (hinner_an 0 (by simp)).differentiableAt.hasDerivAt
        rwa [hdm0] at this
      have h2 : HasDerivAt g (deriv g u) (mobZu u 0) := by
        rw [hm0']; exact (hgan u hu).differentiableAt.hasDerivAt
      have h3 : HasDerivAt (g ∘ mobZu u) (deriv g u * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ)) 0 :=
        h2.comp 0 h1
      exact h3.deriv
    have hd : deriv (fun ζ : ℂ => (g (mobZu u ζ) - g u) /
        (((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u)) 0 = 1 := by
      rw [deriv_div_const, deriv_sub_const, hchain]
      rw [mul_comm (deriv g u) (((1 - ‖u‖ ^ 2 : ℝ) : ℂ)), div_self hcC]
    unfold koebeT
    exact hd

/-- The derivative of the Koebe transform at `-u` in terms of `g`. -/
theorem deriv_koebeT_neg {g : ℂ → ℂ} (hgan : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ g z)
    {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) (hgu : deriv g u ≠ 0) :
    deriv (koebeT g u) (-u)
      = deriv g 0 / ((((1 - ‖u‖ ^ 2 : ℝ) : ℂ)) ^ 2 * deriv g u) := by
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hmun : (-u) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg]; exact hu1
  obtain ⟨hmdiff, hmmaps, hminj, hm0, hmdnz, hmd0, hinv⟩ := mobZ_local u hu
  have hval : mobZu u (-u) = 0 := by simp [mobZu]
  have hdmnz : deriv (mobZu u) (-u) = 1 / ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) := by
    have hcast : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) = 1 - (‖u‖ : ℂ) ^ 2 := by push_cast; ring
    rw [hcast, show deriv (mobZu u) (-u) = deriv (fun w : ℂ => (w + u) / (1 + conj u * w)) (-u)
      from rfl]
    exact hmdnz
  have hinner_an : ∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ (mobZu u) ζ :=
    fun ζ hζ => hmdiff.analyticAt (isOpen_ball.mem_nhds hζ)
  have hchain : deriv (fun ζ : ℂ => g (mobZu u ζ)) (-u)
      = deriv g 0 * (1 / ((1 - ‖u‖ ^ 2 : ℝ) : ℂ)) := by
    have h1 : HasDerivAt (mobZu u) (1 / ((1 - ‖u‖ ^ 2 : ℝ) : ℂ)) (-u) := by
      have := (hinner_an (-u) hmun).differentiableAt.hasDerivAt
      rwa [hdmnz] at this
    have h2 : HasDerivAt g (deriv g 0) (mobZu u (-u)) := by
      rw [hval]; exact (hgan 0 (by simp)).differentiableAt.hasDerivAt
    have h3 : HasDerivAt (g ∘ mobZu u) (deriv g 0 * (1 / ((1 - ‖u‖ ^ 2 : ℝ) : ℂ))) (-u) :=
      h2.comp (-u) h1
    exact h3.deriv
  unfold koebeT
  rw [deriv_div_const, deriv_sub_const, hchain]
  field_simp

/-! ## Distortion on the unit disc -/


theorem unit_disc_distortion (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ c ≤ C ∧
      ∀ g : ℂ → ℂ, (∀ z ∈ ball (0:ℂ) 1, AnalyticAt ℂ g z) → InjOn g (ball (0:ℂ) 1) →
        g 0 = 0 → deriv g 0 = 1 →
        (∀ z ∈ closedBall (0:ℂ) σ, c ≤ ‖deriv g z‖ ∧ ‖deriv g z‖ ≤ C) ∧
        (∀ u ∈ closedBall (0:ℂ) σ, ∀ v ∈ closedBall (0:ℂ) σ,
          c * ‖u - v‖ ≤ ‖g u - g v‖ ∧ ‖g u - g v‖ ≤ C * ‖u - v‖) := by
  obtain ⟨C₀, hC₀pos, hgro⟩ := Submission.exists_growth_bound_normalized_injective
  obtain ⟨κ, hκpos, hκ⟩ := growth_lower_local
  set ρ : ℝ := (1 + σ) / 2 with hρdef
  have hσρ : σ < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρ2σ2 : 0 < ρ ^ 2 - σ ^ 2 := by nlinarith
  set M : ℝ := ((1 + ρ) / (1 - ρ)) ^ C₀ - 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 : 1 < (1 + ρ) / (1 - ρ) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have h2 := Real.one_lt_rpow h1 hC₀pos
    linarith
  have hM1pos : 0 < M + 1 := by linarith
  set C : ℝ := (M + 1) * ρ / (ρ ^ 2 - σ ^ 2) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact div_pos (mul_pos hM1pos hρpos) hρ2σ2
  set c₁ : ℝ := 1 / C with hc₁def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; positivity
  set c₂ : ℝ := (1 - σ ^ 2) * c₁ * κ / (1 + σ ^ 2) with hc₂def
  have hσ2pos : 0 < 1 - σ ^ 2 := by nlinarith
  have hσ2pos' : 0 < 1 + σ ^ 2 := by nlinarith [sq_nonneg σ]
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; positivity
  refine ⟨min (min c₁ c₂) C, C, lt_min (lt_min hc₁pos hc₂pos) hCpos, hCpos,
    min_le_right _ _, ?_⟩
  intro g hgan hginj hg0 hg1
  have hgro' := hgro g hgan hginj hg0 hg1
  have hgM : ∀ z ∈ closedBall (0:ℂ) ρ, ‖g z‖ ≤ M := by
    intro z hz
    have hzle : ‖z‖ ≤ ρ := by rwa [mem_closedBall_zero_iff] at hz
    have hz1 : z ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
    have h1 := hgro' z hz1
    have h2 : (1 + ‖z‖) / (1 - ‖z‖) ≤ (1 + ρ) / (1 - ρ) := div_one_sub_mono hzle hρ1
    have h3 : ((1 + ‖z‖) / (1 - ‖z‖)) ^ C₀ ≤ ((1 + ρ) / (1 - ρ)) ^ C₀ :=
      Real.rpow_le_rpow (div_one_sub_nonneg (norm_nonneg z) (by linarith)) h2 hC₀pos.le
    rw [hMdef]; linarith
  have hgdiffρ : DifferentiableOn ℂ g (ball (0:ℂ) ρ) := fun z hz =>
    (hgan z (by rw [mem_ball_zero_iff] at hz ⊢; linarith)).differentiableAt.differentiableWithinAt
  have hmapsM : MapsTo g (ball (0:ℂ) ρ) (ball (0:ℂ) (M + 1)) := by
    intro w hw
    have hwle : ‖w‖ ≤ ρ := le_of_lt (by rwa [mem_ball_zero_iff] at hw)
    have h1 : ‖g w‖ ≤ M := hgM w (mem_closedBall_zero_iff.mpr hwle)
    rw [mem_ball_zero_iff]; linarith
  have hup : ∀ z ∈ closedBall (0:ℂ) σ, ‖deriv g z‖ ≤ C := by
    intro z hz
    have hzle : ‖z‖ ≤ σ := by rwa [mem_closedBall_zero_iff] at hz
    have hzρ : z ∈ ball (0:ℂ) ρ := by rw [mem_ball_zero_iff]; linarith
    have hsp := schwarz_pick_deriv hρpos hgdiffρ hmapsM hzρ
    simp only [sub_zero] at hsp
    have h1 : (M + 1) * ρ / (ρ ^ 2 - ‖z‖ ^ 2) ≤ (M + 1) * ρ / (ρ ^ 2 - σ ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hM1pos.le hρpos.le) hρ2σ2
        (by nlinarith [norm_nonneg z])
    rw [hCdef]; linarith
  have hlow : ∀ z ∈ closedBall (0:ℂ) σ, c₁ ≤ ‖deriv g z‖ := by
    intro z hz
    have hzle : ‖z‖ ≤ σ := by rwa [mem_closedBall_zero_iff] at hz
    have hz1 : z ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
    have hgz : deriv g z ≠ 0 := deriv_ne_zero_of_injOn_ball hgan hginj hz1
    obtain ⟨hkTan, hkTinj, hkT0, hkTd1⟩ := koebeT_normalized hgan hginj hz1 hgz
    have hkTdiff : DifferentiableOn ℂ (koebeT g z) (ball (0:ℂ) ρ) := fun w hw =>
      (hkTan w (by rw [mem_ball_zero_iff] at hw ⊢; linarith)).differentiableAt.differentiableWithinAt
    have hmapsT : MapsTo (koebeT g z) (ball (0:ℂ) ρ) (ball (0:ℂ) (M + 1)) := by
      intro w hw
      have hwle : ‖w‖ ≤ ρ := le_of_lt (by rwa [mem_ball_zero_iff] at hw)
      have h1 := hgro (koebeT g z) hkTan hkTinj hkT0 hkTd1 w
        (by rw [mem_ball_zero_iff]; linarith)
      have h2 : (1 + ‖w‖) / (1 - ‖w‖) ≤ (1 + ρ) / (1 - ρ) := div_one_sub_mono hwle hρ1
      have h3 : ((1 + ‖w‖) / (1 - ‖w‖)) ^ C₀ ≤ ((1 + ρ) / (1 - ρ)) ^ C₀ :=
        Real.rpow_le_rpow (div_one_sub_nonneg (norm_nonneg w) (by linarith)) h2 hC₀pos.le
      have h4 : ‖koebeT g z w‖ ≤ M := by rw [hMdef]; linarith
      rw [mem_ball_zero_iff]; linarith
    have hnegρ : (-z) ∈ ball (0:ℂ) ρ := by rw [mem_ball_zero_iff, norm_neg]; linarith
    have hsp := schwarz_pick_deriv hρpos hkTdiff hmapsT hnegρ
    simp only [sub_zero] at hsp
    have h2 : ‖deriv (koebeT g z) (-z)‖ ≤ C := by
      have h1 : (M + 1) * ρ / (ρ ^ 2 - ‖-z‖ ^ 2) ≤ (M + 1) * ρ / (ρ ^ 2 - σ ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hM1pos.le hρpos.le) hρ2σ2
          (by rw [norm_neg]; nlinarith [norm_nonneg z])
      rw [hCdef]; linarith
    have h3 := deriv_koebeT_neg hgan hz1 hgz
    have hD : ‖(((1 - ‖z‖ ^ 2 : ℝ)) : ℂ)‖ = 1 - ‖z‖ ^ 2 := by
      rw [show ‖(((1 - ‖z‖ ^ 2 : ℝ)) : ℂ)‖ = |(1 - ‖z‖ ^ 2 : ℝ)| from RCLike.norm_ofReal _,
        abs_of_pos (by nlinarith [norm_nonneg z])]
    have h4 : ‖deriv (koebeT g z) (-z)‖ = 1 / ((1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖) := by
      rw [h3, hg1]
      simp only [norm_div, norm_one, norm_mul, norm_pow, hD]
    have h5 : 1 ≤ C * ((1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖) := by
      have hpos : 0 < (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖ :=
        mul_pos (pow_pos (by nlinarith [norm_nonneg z]) 2) (norm_pos_iff.mpr hgz)
      have hh := h2
      rw [h4] at hh
      exact (div_le_iff₀ hpos).mp hh
    have h6 : (1 - ‖z‖ ^ 2) ^ 2 ≤ 1 := by
      have h : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hzle, hσ1]
      nlinarith
    rw [hc₁def, div_le_iff₀ hCpos]
    have h7 : C * ((1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖) ≤ ‖deriv g z‖ * C := by
      have h8 : (1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖ ≤ ‖deriv g z‖ := by
        nlinarith [norm_nonneg (deriv g z)]
      calc C * ((1 - ‖z‖ ^ 2) ^ 2 * ‖deriv g z‖) ≤ C * ‖deriv g z‖ :=
            mul_le_mul_of_nonneg_left h8 hCpos.le
        _ = ‖deriv g z‖ * C := by ring
    linarith
  have hdqlow : ∀ u ∈ closedBall (0:ℂ) σ, ∀ v ∈ closedBall (0:ℂ) σ,
      c₂ * ‖u - v‖ ≤ ‖g u - g v‖ := by
    intro u hu v hv
    have hule : ‖u‖ ≤ σ := by rwa [mem_closedBall_zero_iff] at hu
    have hvle : ‖v‖ ≤ σ := by rwa [mem_closedBall_zero_iff] at hv
    have hu1 : u ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
    have hv1 : v ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
    have hgu : deriv g u ≠ 0 := deriv_ne_zero_of_injOn_ball hgan hginj hu1
    obtain ⟨hkTan, hkTinj, hkT0, hkTd1⟩ := koebeT_normalized hgan hginj hu1 hgu
    obtain ⟨_, _, _, _, _, _, hinv⟩ := mobZ_local u hu1
    obtain ⟨hinv1, hinv2, hinv3⟩ := hinv u v hu1 hv1
    set ζ : ℂ := (v - u) / (1 - conj u * v) with hζdef
    have hzeta : mobZu u ζ = v := by rw [hζdef]; exact hinv1
    have hzetamem : ζ ∈ ball (0:ℂ) 1 := by rw [hζdef]; exact hinv2
    have hzetanorm : ‖v - u‖ ≤ (1 + ‖u‖ * ‖v‖) * ‖ζ‖ := by rw [hζdef]; exact hinv3
    have hκζ := hκ (koebeT g u) hkTan hkTinj hkT0 hkTd1 ζ hzetamem
    have hD : ‖(((1 - ‖u‖ ^ 2 : ℝ)) : ℂ)‖ = 1 - ‖u‖ ^ 2 := by
      rw [show ‖(((1 - ‖u‖ ^ 2 : ℝ)) : ℂ)‖ = |(1 - ‖u‖ ^ 2 : ℝ)| from RCLike.norm_ofReal _,
        abs_of_pos (by nlinarith [norm_nonneg u])]
    have hnorm : ‖koebeT g u ζ‖ = ‖g v - g u‖ / ((1 - ‖u‖ ^ 2) * ‖deriv g u‖) := by
      have hval : koebeT g u ζ = (g v - g u) / (((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * deriv g u) := by
        unfold koebeT; rw [hzeta]
      rw [hval]
      simp only [norm_div, norm_mul, norm_pow, hD]
    set D : ℝ := (1 - ‖u‖ ^ 2) * ‖deriv g u‖ with hDdef
    have hDpos : 0 < D := by
      rw [hDdef]; exact mul_pos (by nlinarith [norm_nonneg u]) (norm_pos_iff.mpr hgu)
    have hstep : κ * ‖ζ‖ * D ≤ ‖g v - g u‖ := by
      have h1 : κ * ‖ζ‖ ≤ ‖g v - g u‖ / D := by
        rw [hnorm] at hκζ
        rw [hDdef]
        exact hκζ
      exact (le_div_iff₀ hDpos).mp h1
    rw [norm_sub_rev] at hstep
    have hDge : (1 - σ ^ 2) * c₁ ≤ D := by
      rw [hDdef]
      have h1 : 1 - σ ^ 2 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
      exact mul_le_mul h1 (hlow u hu) hc₁pos.le (by nlinarith [norm_nonneg u])
    have hzge : ‖u - v‖ / (1 + σ ^ 2) ≤ ‖ζ‖ := by
      have h1 : 1 + ‖u‖ * ‖v‖ ≤ 1 + σ ^ 2 := by nlinarith [norm_nonneg u, norm_nonneg v]
      have h2 : ‖u - v‖ ≤ ‖ζ‖ * (1 + σ ^ 2) := by
        rw [norm_sub_rev]
        calc ‖v - u‖ ≤ (1 + ‖u‖ * ‖v‖) * ‖ζ‖ := hzetanorm
          _ ≤ (1 + σ ^ 2) * ‖ζ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg ζ)
          _ = ‖ζ‖ * (1 + σ ^ 2) := by ring
      exact (div_le_iff₀ hσ2pos').mpr h2
    have h8 : κ * (‖u - v‖ / (1 + σ ^ 2)) * ((1 - σ ^ 2) * c₁) ≤ κ * ‖ζ‖ * D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hzge hκpos.le) hDge
        (mul_nonneg hσ2pos.le hc₁pos.le) (mul_nonneg hκpos.le (norm_nonneg ζ))
    have h10 : c₂ * ‖u - v‖ = κ * (‖u - v‖ / (1 + σ ^ 2)) * ((1 - σ ^ 2) * c₁) := by
      rw [hc₂def, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h10]
    linarith
  have hdqup : ∀ u ∈ closedBall (0:ℂ) σ, ∀ v ∈ closedBall (0:ℂ) σ,
      ‖g u - g v‖ ≤ C * ‖u - v‖ := by
    intro u hu v hv
    have hdiff : ∀ x ∈ closedBall (0:ℂ) σ, DifferentiableAt ℂ g x := fun x hx =>
      (hgan x (by rw [mem_closedBall_zero_iff] at hx; rw [mem_ball_zero_iff]; linarith)).differentiableAt
    exact Convex.norm_image_sub_le_of_norm_deriv_le (s := closedBall (0:ℂ) σ) hdiff
      (fun x hx => hup x hx) (convex_closedBall (0:ℂ) σ) hv hu
  refine ⟨fun z hz => ⟨?_, ?_⟩, fun u hu v hv => ⟨?_, ?_⟩⟩
  · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (hlow z hz))
  · exact hup z hz
  · exact le_trans (mul_le_mul_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_right _ _)) (norm_nonneg _)) (hdqlow u hu v hv)
  · exact hdqup u hu v hv

/-- **Koebe distortion on a strictly smaller disc.** -/
theorem koebe_distortion (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ c ≤ C ∧
      ∀ (f : ℂ → ℂ) (p : ℂ) (R : ℝ), 0 < R → DifferentiableOn ℂ f (ball p R) →
        InjOn f (ball p R) →
        (∀ z ∈ closedBall p (σ * R), c * ‖deriv f p‖ ≤ ‖deriv f z‖ ∧
            ‖deriv f z‖ ≤ C * ‖deriv f p‖) ∧
        (∀ u ∈ closedBall p (σ * R), ∀ v ∈ closedBall p (σ * R),
          c * ‖deriv f p‖ * ‖u - v‖ ≤ ‖f u - f v‖ ∧
            ‖f u - f v‖ ≤ C * ‖deriv f p‖ * ‖u - v‖) := by
  obtain ⟨c, C, hc, hC, hcC, H⟩ := unit_disc_distortion σ hσ0 hσ1
  refine ⟨c, C, hc, hC, hcC, ?_⟩
  intro f p R hR hdiff hinj
  have hp : p ∈ ball p R := by rw [mem_ball]; simpa using hR
  have hfp : deriv f p ≠ 0 := Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hR
    (hdiff.analyticAt (isOpen_ball.mem_nhds hp)) hinj
  have hfp_pos : 0 < ‖deriv f p‖ := norm_pos_iff.mpr hfp
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hRnorm : ‖(R : ℂ)‖ = R := (RCLike.norm_ofReal R).trans (abs_of_pos hR)
  have hDne : (R : ℂ) * deriv f p ≠ 0 := mul_ne_zero hRne hfp
  have hDnorm : ‖(R : ℂ) * deriv f p‖ = R * ‖deriv f p‖ := by rw [norm_mul, hRnorm]
  set g : ℂ → ℂ := fun w => (f (p + (R : ℂ) * w) - f p) / ((R : ℂ) * deriv f p) with hgdef
  have hmem : ∀ w : ℂ, ‖w‖ < 1 → p + (R : ℂ) * w ∈ ball p R := by
    intro w hw
    rw [mem_ball, dist_eq_norm,
      show p + (R : ℂ) * w - p = (R : ℂ) * w by ring, norm_mul, hRnorm]
    nlinarith
  have hgan : ∀ w ∈ ball (0 : ℂ) 1, AnalyticAt ℂ g w := by
    intro w hw
    rw [hgdef]
    have hwm : p + (R : ℂ) * w ∈ ball p R := hmem w (mem_ball_zero_iff.mp hw)
    have hinner : AnalyticAt ℂ (fun w : ℂ => p + (R : ℂ) * w) w := by fun_prop
    have h1 : AnalyticAt ℂ (fun w : ℂ => f (p + (R : ℂ) * w)) w := by
      have hc := AnalyticAt.comp (x := w) (f := fun w : ℂ => p + (R : ℂ) * w) (g := f)
        (hdiff.analyticAt (isOpen_ball.mem_nhds hwm)) hinner
      simpa only [Function.comp_def] using hc
    have h2 : AnalyticAt ℂ (fun w : ℂ => f (p + (R : ℂ) * w) - f p) w := h1.sub analyticAt_const
    exact h2.div_const (c := (R : ℂ) * deriv f p)
  have hginj : InjOn g (ball (0 : ℂ) 1) := by
    intro w₁ hw₁ w₂ hw₂ heq
    rw [hgdef] at heq
    have h1 : f (p + (R : ℂ) * w₁) = f (p + (R : ℂ) * w₂) := by
      rw [div_eq_div_iff hDne hDne] at heq
      have h2 := mul_right_cancel₀ hDne heq
      have h3 : f (p + (R : ℂ) * w₁) - f p = f (p + (R : ℂ) * w₂) - f p := h2
      have h4 := h3
      rw [sub_eq_add_neg, sub_eq_add_neg] at h4
      exact add_right_cancel h4
    have h5 : p + (R : ℂ) * w₁ = p + (R : ℂ) * w₂ :=
      hinj (hmem w₁ (mem_ball_zero_iff.mp hw₁)) (hmem w₂ (mem_ball_zero_iff.mp hw₂)) h1
    have h6 : (R : ℂ) * w₁ = (R : ℂ) * w₂ := add_left_cancel h5
    exact mul_left_cancel₀ hRne h6
  have hg0 : g 0 = 0 := by rw [hgdef]; simp
  have hgd0 : deriv (fun w : ℂ => f (p + (R : ℂ) * w)) 0 = deriv f p * (R : ℂ) := by
    have hd : DifferentiableAt ℂ f (p + (R : ℂ) * 0) := by
      rw [mul_zero, add_zero]
      exact hdiff.differentiableAt (isOpen_ball.mem_nhds hp)
    rw [deriv_affine_comp (w := 0) hd, mul_zero, add_zero]
  have hg1 : deriv g 0 = 1 := by
    rw [hgdef, deriv_div_const, deriv_sub_const, hgd0]
    rw [mul_comm (deriv f p) (R : ℂ), div_self hDne]
  obtain ⟨hlong, hlng⟩ := H g hgan hginj hg0 hg1
  have hder : ∀ w : ℂ, ‖w‖ < 1 → deriv g w = deriv f (p + (R : ℂ) * w) / deriv f p := by
    intro w hw
    rw [hgdef]
    have hd : deriv (fun u : ℂ => f (p + (R : ℂ) * u)) w
        = deriv f (p + (R : ℂ) * w) * (R : ℂ) :=
      deriv_affine_comp (w := w) (hdiff.differentiableAt (isOpen_ball.mem_nhds (hmem w hw)))
    rw [deriv_div_const, deriv_sub_const, hd,
      mul_comm (deriv f (p + (R : ℂ) * w)) (R : ℂ), mul_div_mul_left _ _ hRne]
  have hkey : ∀ z : ℂ, z ∈ closedBall p (σ * R) →
      (z - p) / (R : ℂ) ∈ closedBall (0 : ℂ) σ ∧ p + (R : ℂ) * ((z - p) / (R : ℂ)) = z := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    constructor
    · rw [mem_closedBall_zero_iff, norm_div, hRnorm, div_le_iff₀ hR]
      linarith
    · rw [mul_div_cancel₀ (z - p) hRne]
      ring
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hz', hzp⟩ := hkey z hz
    have hzw : ‖(z - p) / (R : ℂ)‖ < 1 := by
      have h := mem_closedBall_zero_iff.mp hz'
      linarith
    have hd : deriv g ((z - p) / (R : ℂ)) = deriv f z / deriv f p := by
      rw [hder _ hzw, hzp]
    obtain ⟨h1, h2⟩ := hlong _ hz'
    constructor
    · have h1' : c ≤ ‖deriv f z‖ / ‖deriv f p‖ := by
        rw [← norm_div, ← hd]; exact h1
      rw [le_div_iff₀ hfp_pos] at h1'
      linarith
    · have h2' : ‖deriv f z‖ / ‖deriv f p‖ ≤ C := by
        rw [← norm_div, ← hd]; exact h2
      rw [div_le_iff₀ hfp_pos] at h2'
      linarith
  · intro u hu v hv
    obtain ⟨hu', hup⟩ := hkey u hu
    obtain ⟨hv', hvp⟩ := hkey v hv
    have hnormu : ‖u - v‖ = R * ‖(u - p) / (R : ℂ) - (v - p) / (R : ℂ)‖ := by
      have h1 : u - v = (R : ℂ) * ((u - p) / (R : ℂ) - (v - p) / (R : ℂ)) := by
        rw [mul_sub, mul_div_cancel₀ (u - p) hRne, mul_div_cancel₀ (v - p) hRne]
        ring
      rw [h1, norm_mul, hRnorm]
    have hgu : g ((u - p) / (R : ℂ)) = (f u - f p) / ((R : ℂ) * deriv f p) := by
      rw [hgdef]
      show (f (p + (R : ℂ) * ((u - p) / (R : ℂ))) - f p) / ((R : ℂ) * deriv f p) = _
      rw [hup]
    have hgv : g ((v - p) / (R : ℂ)) = (f v - f p) / ((R : ℂ) * deriv f p) := by
      rw [hgdef]
      show (f (p + (R : ℂ) * ((v - p) / (R : ℂ))) - f p) / ((R : ℂ) * deriv f p) = _
      rw [hvp]
    have hnormg : ‖g ((u - p) / (R : ℂ)) - g ((v - p) / (R : ℂ))‖
        = ‖f u - f v‖ / (R * ‖deriv f p‖) := by
      rw [hgu, hgv,
        show (f u - f p) / ((R : ℂ) * deriv f p) - (f v - f p) / ((R : ℂ) * deriv f p)
          = (f u - f v) / ((R : ℂ) * deriv f p) by ring,
        norm_div, hDnorm]
    obtain ⟨h1, h2⟩ := hlng _ hu' _ hv'
    rw [hnormg] at h1 h2
    have hem2 : R * (‖f u - f v‖ / (R * ‖deriv f p‖)) = ‖f u - f v‖ / ‖deriv f p‖ := by
      rw [← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hR)]
    constructor
    · have hem1 : c * ‖u - v‖ = R * (c * ‖(u - p) / (R : ℂ) - (v - p) / (R : ℂ)‖) := by
        rw [hnormu]; ring
      have hh : R * (c * ‖(u - p) / (R : ℂ) - (v - p) / (R : ℂ)‖)
          ≤ R * (‖f u - f v‖ / (R * ‖deriv f p‖)) := mul_le_mul_of_nonneg_left h1 hR.le
      rw [← hem1, hem2] at hh
      rw [le_div_iff₀ hfp_pos] at hh
      linarith
    · have hem3 : R * (C * ‖(u - p) / (R : ℂ) - (v - p) / (R : ℂ)‖) = C * ‖u - v‖ := by
        rw [hnormu]; ring
      have hh : R * (‖f u - f v‖ / (R * ‖deriv f p‖))
          ≤ R * (C * ‖(u - p) / (R : ℂ) - (v - p) / (R : ℂ)‖) :=
        mul_le_mul_of_nonneg_left h2 hR.le
      rw [hem2, hem3] at hh
      rw [div_le_iff₀ hfp_pos] at hh
      linarith

end
end Work.Motion
