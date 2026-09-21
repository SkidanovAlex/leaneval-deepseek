import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_of_close
import Submission.Work.OddVolterra.Existence.dev_bounds
import Submission.Work.OddVolterra.Existence.glue_cutoff_defs
import Submission.Work.OddVolterra.Existence.glue_ramp

namespace Work.OddVolterra.Existence

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

noncomputable section

/-- The semicircle chord function agrees with the definition used in the envelope development. -/
lemma profileX_eq (s : ℝ) :
    Work.OddEnvelope.profileX s = Commons.Geometry.Ulam.profileX s := rfl

lemma devZero_eq_zero (Z : ℝ → Work.OddVolterra.St) (s : ℝ) : devZero Z s = dev Z 0 s := rfl

lemma devOne_eq_zero (Z : ℝ → Work.OddVolterra.St) (s : ℝ) : devOne Z s = dev Z 1 s := rfl

/-- `profileX` is smooth. -/
lemma profX_contDiff : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX := by
  have hfun : Commons.Geometry.Ulam.profileX = fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹ := by
    funext s; simp [Commons.Geometry.Ulam.profileX, one_div]
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    ContDiff.sqrt (by fun_prop) (fun x => by positivity)
  rw [hfun]
  exact hsq.inv (fun x => by positivity)

/-- The primitive of the bump is bounded by one. -/
lemma gluePrim_le_one (t : ℝ) : gluePrim t ≤ 1 := by
  rcases lt_or_ge t 1 with h | h
  · by_cases h0 : t ≤ 0
    · rw [gluePrim_zero_of_nonpos h0]; norm_num
    · exact le_trans (gluePrim_le_self_all (by linarith)) h.le
  · rw [gluePrim_eq_of_one_le h]
    exact gluePrim_one_bounds.2

/-- The derivative of the gluing function lies in `[-2, 1]`. -/
lemma gluePhi_deriv_mem (s : ℝ) : -2 ≤ deriv gluePhi s ∧ deriv gluePhi s ≤ 1 := by
  have h1 : 0 ≤ gluePrim ((1 / 2 - s) / gW) := gluePrim_nonneg_all _
  have h2 : gluePrim ((1 / 2 - s) / gW) ≤ 1 := gluePrim_le_one _
  have h3 : (71 : ℝ) / 200 ≤ gW * gI := gW_gI_lo
  have h4 : 0 < gW * gI := gW_gI_pos
  rw [gluePhi_deriv]
  constructor
  · have h5 : gluePrim ((1 / 2 - s) / gW) / (gW * gI) ≤ 3 := by
      rw [div_le_iff₀ h4]; nlinarith
    linarith
  · have h5 : 0 ≤ gluePrim ((1 / 2 - s) / gW) / (gW * gI) := div_nonneg h1 h4.le
    linarith

/-- For small slopes the gluing function stays above `9/10`. -/
lemma gluePhi_ge_nine_tenths {s : ℝ} (hs : s ≤ 1 / 100) : 9 / 10 ≤ gluePhi s := by
  have hψ : gluePhi s = s + (∫ u in (0 : ℝ)..((1 / 2 - s) / gW), gluePrim u) / gI := rfl
  rw [hψ]
  have ht1 : (1 : ℝ) ≤ (1 / 2 - s) / gW := by rw [gW]; linarith
  have hsplit : (∫ u in (0 : ℝ)..((1 / 2 - s) / gW), gluePrim u) =
      (∫ u in (0 : ℝ)..1, gluePrim u) + ∫ u in (1 : ℝ)..((1 / 2 - s) / gW), gluePrim u :=
    (intervalIntegral.integral_add_adjacent_intervals (gluePrim_intble 0 1) (gluePrim_intble 1 _)).symm
  have htail : (∫ u in (1 : ℝ)..((1 / 2 - s) / gW), gluePrim u)
      = ((1 / 2 - s) / gW - 1) * gluePrim 1 := by
    have hconst : (∫ u in (1 : ℝ)..((1 / 2 - s) / gW), gluePrim u)
        = ∫ u in (1 : ℝ)..((1 / 2 - s) / gW), gluePrim 1 := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht1, Set.mem_Icc] at hu
      exact gluePrim_eq_of_one_le hu.1
    rw [hconst, intervalIntegral.integral_const]
    ring
  have h1 : (24 : ℝ) / 25 * (24 / 25) / 2 ≤ (∫ u in (0 : ℝ)..1, gluePrim u) := gluePrim_int_Icc_ge
  have h2 : (24 : ℝ) / 25 ≤ gluePrim 1 := gluePrim_one_bounds.1
  have h3 : gI ≤ 3 / 2 := gI_bounds.2
  have h4 : (1 / 2 - s) / gW - 1 = 1 - 4 * s := by rw [gW]; ring
  rw [hsplit, htail, h4]
  have hnum : (24 : ℝ) / 25 * (24 / 25) / 2 + (1 - 4 * s) * (24 / 25)
      ≤ (∫ u in (0 : ℝ)..1, gluePrim u) + (1 - 4 * s) * gluePrim 1 := by
    have hs' : (0 : ℝ) ≤ 1 - 4 * s := by linarith
    nlinarith [h1, h2, hs']
  have hdiv : ((24 : ℝ) / 25 * (24 / 25) / 2 + (1 - 4 * s) * (24 / 25)) / gI
      ≤ ((∫ u in (0 : ℝ)..1, gluePrim u) + (1 - 4 * s) * gluePrim 1) / gI :=
    div_le_div_of_nonneg_right hnum gI_pos.le
  have hmain : 9 / 10 - s
      ≤ ((24 : ℝ) / 25 * (24 / 25) / 2 + (1 - 4 * s) * (24 / 25)) / gI := by
    rw [le_div_iff₀ gI_pos]
    nlinarith
  linarith

/-- The first derivative of `profileX` is bounded above on `[1/100, 9/10]`. -/
lemma deriv_profileX_le {s : ℝ} (hs1 : 1 / 100 ≤ s) (hs2 : s ≤ 9 / 10) :
    deriv Commons.Geometry.Ulam.profileX s ≤ -(1 / 200) := by
  have hPX : Commons.Geometry.Ulam.profileX s ^ 2 = 1 / (1 + s ^ 2) := by
    rw [Commons.Geometry.Ulam.profileX, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hPXpos : 0 < Commons.Geometry.Ulam.profileX s := by
    rw [Commons.Geometry.Ulam.profileX]; positivity
  have h1s : 0 < 1 + s ^ 2 := by positivity
  have hcube : Commons.Geometry.Ulam.profileX s ^ 3
      = Commons.Geometry.Ulam.profileX s / (1 + s ^ 2) := by
    have h : Commons.Geometry.Ulam.profileX s ^ 3
        = Commons.Geometry.Ulam.profileX s * Commons.Geometry.Ulam.profileX s ^ 2 := by ring
    rw [h, hPX]; ring
  rw [deriv_profileX_eq, hcube]
  rw [show -s * (Commons.Geometry.Ulam.profileX s / (1 + s ^ 2))
      = - (s * Commons.Geometry.Ulam.profileX s / (1 + s ^ 2)) by ring, neg_le_neg_iff]
  rw [le_div_iff₀ h1s]
  have hkey : (1 + s ^ 2) ^ 3 ≤ 40000 * s ^ 2 := by
    have h3 : (1 : ℝ) / 10000 ≤ s ^ 2 := by nlinarith
    have h4 : s ^ 2 ≤ (9 : ℝ) / 10 * (9 / 10) := by nlinarith
    nlinarith [sq_nonneg (s ^ 2), sq_nonneg (s ^ 2 - 1 / 10000), sq_nonneg (s ^ 2 - 81 / 100),
      sq_nonneg (s ^ 2 * (1 - s ^ 2))]
  have hgoal : ((1 / 200) * (1 + s ^ 2)) ^ 2
      ≤ (s * Commons.Geometry.Ulam.profileX s) ^ 2 := by
    have e1 : ((1 / 200) * (1 + s ^ 2)) ^ 2 = (1 / 40000) * (1 + s ^ 2) ^ 2 := by ring
    have e2 : (s * Commons.Geometry.Ulam.profileX s) ^ 2 = s ^ 2 * (1 / (1 + s ^ 2)) := by
      rw [mul_pow, hPX]
    rw [e1, e2, show s ^ 2 * (1 / (1 + s ^ 2)) = s ^ 2 / (1 + s ^ 2) by ring,
      le_div_iff₀ h1s]
    nlinarith
  have hnn : 0 ≤ (1 / 200) * (1 + s ^ 2) := by positivity
  have hnn2 : 0 ≤ s * Commons.Geometry.Ulam.profileX s := by positivity
  nlinarith [hgoal, hnn, hnn2,
    sq_nonneg ((1 / 200) * (1 + s ^ 2) + s * Commons.Geometry.Ulam.profileX s)]

/-- The first derivative of `profileX` is negative on `(0, ∞)`. -/
lemma deriv_profileX_neg {s : ℝ} (hs : 0 < s) : deriv Commons.Geometry.Ulam.profileX s < 0 := by
  have hPX : 0 < Commons.Geometry.Ulam.profileX s := by
    rw [Commons.Geometry.Ulam.profileX]; positivity
  rw [deriv_profileX_eq]
  nlinarith [pow_pos hPX 3]

/-- The main closeness/gluing lemma. -/
theorem glue_close {Z : ℝ → Work.OddVolterra.St} (i j : Fin 4) (hi : i = 0 ∨ i = 1)
    (hj : j = 2 ∨ j = 3)
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)))
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s)
    (hval : ∀ s : ℝ, 1 / 4 ≤ s → |Z s i - Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000)
    (hderiv : ∀ s : ℝ, 1 / 4 ≤ s → deriv (fun u : ℝ => Z u i) s = Z s j)
    (hdd : ∀ s : ℝ, 1 / 4 ≤ s →
      |deriv (fun u : ℝ => Z u j) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 1000) :
    (∀ s : ℝ, 0 < s →
      |Commons.Geometry.Ulam.profileX s + dev Z i (gluePhi s) - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t)) s
        - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t))) s
        - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) ∧
    (∀ s : ℝ, 1 / 2 ≤ s →
      Commons.Geometry.Ulam.profileX s + dev Z i (gluePhi s) = Z s i) ∧
    (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s →
      Commons.Geometry.Ulam.profileX s + dev Z i (gluePhi s) = Work.OddEnvelope.profileX s) ∧
    (∀ s : ℝ, 0 < s →
      deriv (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t)) s < 0) ∧
    Tendsto (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t)) (Set.Ioi 0) := by
  have hd := dev_bounds i j hi hj hZsm htail hval hderiv hdd
  have hΔdiff : ∀ x : ℝ, 1 / 4 < x → HasDerivAt (dev Z i) (deriv (dev Z i) x) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => Z u i) (deriv (fun u : ℝ => Z u i) x) x :=
      (comp_diff (by linarith) i hZsm).hasDerivAt
    have h2 : HasDerivAt Commons.Geometry.Ulam.profileX
        (deriv Commons.Geometry.Ulam.profileX x) x := (profX_diff x).hasDerivAt
    have h3 : HasDerivAt ((fun u : ℝ => Z u i) - Commons.Geometry.Ulam.profileX)
        (deriv (fun u : ℝ => Z u i) x - deriv Commons.Geometry.Ulam.profileX x) x := h1.sub h2
    have hder : deriv (dev Z i) x
        = deriv (fun u : ℝ => Z u i) x - deriv Commons.Geometry.Ulam.profileX x :=
      deriv_sub (comp_diff (by linarith) i hZsm) (profX_diff x)
    rw [hder]
    exact h3
  have hΔ2diff : ∀ x : ℝ, 1 / 4 < x →
      HasDerivAt (deriv (dev Z i)) (deriv (deriv (dev Z i)) x) x := by
    intro x hx
    have hev : deriv (dev Z i) =ᶠ[𝓝 x]
        (fun z : ℝ => Z z j - deriv Commons.Geometry.Ulam.profileX z) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
      exact dev_ident1 hz i j hderiv hZsm
    have hdiff : DifferentiableAt ℝ (deriv (dev Z i)) x := by
      rw [hev.differentiableAt_iff]
      exact (comp_diff (by linarith) j hZsm).sub (deriv_profX_diff x)
    exact hdiff.hasDerivAt
  have hψdiff : ∀ s : ℝ, HasDerivAt gluePhi (deriv gluePhi s) s := fun s =>
    (gluePhi_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hχ : ∀ s : ℝ, 0 < s → deriv (fun t : ℝ => dev Z i (gluePhi t)) s
      = deriv (dev Z i) (gluePhi s) * deriv gluePhi s := by
    intro s hs
    have h1 : HasDerivAt ((dev Z i) ∘ gluePhi)
        (deriv (dev Z i) (gluePhi s) * deriv gluePhi s) s :=
      HasDerivAt.comp s (hΔdiff (gluePhi s) (gluePhi_gt_quarter hs)) (hψdiff s)
    have hfun : (dev Z i) ∘ gluePhi = fun t : ℝ => dev Z i (gluePhi t) := by
      funext x; rfl
    rw [hfun] at h1
    exact h1.deriv
  have hχdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ (fun t : ℝ => dev Z i (gluePhi t)) s := by
    intro s hs
    exact (hΔdiff (gluePhi s) (gluePhi_gt_quarter hs)).differentiableAt.comp s
      (hψdiff s).differentiableAt
  have hχ2 : ∀ s : ℝ, 0 < s →
      deriv (deriv (fun t : ℝ => dev Z i (gluePhi t))) s
        = deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2
          + deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s := by
    intro s hs
    have hmem : (1 : ℝ) / 4 < gluePhi s := gluePhi_gt_quarter hs
    have hcont : ContinuousAt gluePhi s := gluePhi_contDiff.continuous.continuousAt
    have hev : deriv (fun t : ℝ => dev Z i (gluePhi t))
        =ᶠ[𝓝 s] (fun t : ℝ => deriv (dev Z i) (gluePhi t) * deriv gluePhi t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs, hcont.eventually (isOpen_Ioi.mem_nhds hmem)]
        with t ht _ht
      exact hχ t ht
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun t : ℝ => deriv (dev Z i) (gluePhi t))
        (deriv (deriv (dev Z i)) (gluePhi s) * deriv gluePhi s) s := by
      have h2 : HasDerivAt ((deriv (dev Z i)) ∘ gluePhi)
          (deriv (deriv (dev Z i)) (gluePhi s) * deriv gluePhi s) s :=
        HasDerivAt.comp s (hΔ2diff (gluePhi s) hmem) (hψdiff s)
      have hfun : (deriv (dev Z i)) ∘ gluePhi = fun t : ℝ => deriv (dev Z i) (gluePhi t) := by
        funext x; rfl
      rwa [hfun] at h2
    have h2 : HasDerivAt (fun t : ℝ => deriv gluePhi t) (deriv (deriv gluePhi) s) s :=
      (hasDerivAt_deriv_gluePhi s).congr_deriv (gluePhi_deriv2 s).symm
    have hprod := h1.mul h2
    rw [show (fun t : ℝ => deriv (dev Z i) (gluePhi t) * deriv gluePhi t)
        = (fun t : ℝ => deriv (dev Z i) (gluePhi t)) * fun t : ℝ => deriv gluePhi t from rfl]
    rw [hprod.deriv]
    ring
  have hχ2diff : ∀ s : ℝ, 0 < s →
      DifferentiableAt ℝ (deriv (fun t : ℝ => dev Z i (gluePhi t))) s := by
    intro s hs
    have hmem : (1 : ℝ) / 4 < gluePhi s := gluePhi_gt_quarter hs
    have hcont : ContinuousAt gluePhi s := gluePhi_contDiff.continuous.continuousAt
    have hev : deriv (fun t : ℝ => dev Z i (gluePhi t))
        =ᶠ[𝓝 s] (fun t : ℝ => deriv (dev Z i) (gluePhi t) * deriv gluePhi t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs, hcont.eventually (isOpen_Ioi.mem_nhds hmem)]
        with t ht _ht
      exact hχ t ht
    rw [hev.differentiableAt_iff]
    exact ((hΔ2diff (gluePhi s) hmem).differentiableAt.comp s
      (hψdiff s).differentiableAt).mul ((hasDerivAt_deriv_gluePhi s).differentiableAt)
  have hXderiv : ∀ s : ℝ, 0 < s →
      deriv (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t)) s
      = deriv Commons.Geometry.Ulam.profileX s + deriv (fun t : ℝ => dev Z i (gluePhi t)) s := by
    intro s hs
    rw [show (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t))
        = Commons.Geometry.Ulam.profileX + fun t : ℝ => dev Z i (gluePhi t) from rfl]
    exact deriv_add (profX_diff s) (hχdiff s hs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- closeness
    intro s hs
    have hmem : (1 : ℝ) / 4 < gluePhi s := gluePhi_gt_quarter hs
    obtain ⟨hb1, hb2, hb3⟩ := hd (gluePhi s) hmem
    have hψmem := gluePhi_deriv_mem s
    have hcost := gluePhi_cost hs
    have hmax : max 0 (9 / 10 - gluePhi s) ≤ 9 / 10 := max_le (by norm_num) (by linarith)
    have hb : |deriv gluePhi s| ≤ 2 := abs_le.mpr ⟨hψmem.1, le_trans hψmem.2 (by norm_num)⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [add_sub_cancel_left]
      linarith
    · have ha : |deriv (dev Z i) (gluePhi s)| ≤ 1 / 1000 * (9 / 10) :=
        le_trans hb2 (mul_le_mul_of_nonneg_left hmax (by norm_num))
      rw [hXderiv s hs, hχ s hs]
      have heq : deriv Commons.Geometry.Ulam.profileX s
          + deriv (dev Z i) (gluePhi s) * deriv gluePhi s
          - deriv Commons.Geometry.Ulam.profileX s
          = deriv (dev Z i) (gluePhi s) * deriv gluePhi s := by ring
      rw [heq, abs_mul]
      calc |deriv (dev Z i) (gluePhi s)| * |deriv gluePhi s|
          ≤ (1 / 1000 * (9 / 10)) * 2 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
        _ ≤ 1 / 100 := by norm_num
    · have hξ2 : deriv (deriv (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t))) s
          = deriv (deriv Commons.Geometry.Ulam.profileX) s
            + deriv (deriv (fun t : ℝ => dev Z i (gluePhi t))) s := by
        have hev : deriv (fun t : ℝ => Commons.Geometry.Ulam.profileX t + dev Z i (gluePhi t))
            =ᶠ[𝓝 s] (fun t : ℝ => deriv Commons.Geometry.Ulam.profileX t
              + deriv (fun u : ℝ => dev Z i (gluePhi u)) t) := by
          filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
          exact hXderiv t ht
        rw [hev.deriv_eq]
        exact deriv_add (deriv_profX_diff s) (hχ2diff s hs)
      rw [hξ2, hχ2 s hs]
      have hA : |deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2|
          ≤ 1 / 1000 * (deriv gluePhi s) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv gluePhi s))]
        exact mul_le_mul_of_nonneg_right hb3 (sq_nonneg _)
      have hB : |deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s|
          ≤ 1 / 1000 * (max 0 (9 / 10 - gluePhi s) * |deriv (deriv gluePhi) s|) := by
        rw [abs_mul]
        calc |deriv (dev Z i) (gluePhi s)| * |deriv (deriv gluePhi) s|
            ≤ (1 / 1000 * max 0 (9 / 10 - gluePhi s)) * |deriv (deriv gluePhi) s| :=
              mul_le_mul_of_nonneg_right hb2 (abs_nonneg _)
          _ = 1 / 1000 * (max 0 (9 / 10 - gluePhi s) * |deriv (deriv gluePhi) s|) := by ring
      have hmain : |deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2
          + deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s| ≤ 1 / 100 := by
        calc |deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2
              + deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s|
            ≤ |deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2|
              + |deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s| := abs_add_le _ _
          _ ≤ 1 / 1000 * (deriv gluePhi s) ^ 2
              + 1 / 1000 * (max 0 (9 / 10 - gluePhi s) * |deriv (deriv gluePhi) s|) :=
              add_le_add hA hB
          _ = 1 / 1000 * ((deriv gluePhi s) ^ 2
                + max 0 (9 / 10 - gluePhi s) * |deriv (deriv gluePhi) s|) := by ring
          _ ≤ 1 / 1000 * 10 := mul_le_mul_of_nonneg_left hcost (by norm_num)
          _ ≤ 1 / 100 := by norm_num
      have hsplit : deriv (deriv Commons.Geometry.Ulam.profileX) s
          + (deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2
            + deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s)
          - deriv (deriv Commons.Geometry.Ulam.profileX) s
          = deriv (deriv (dev Z i)) (gluePhi s) * (deriv gluePhi s) ^ 2
            + deriv (dev Z i) (gluePhi s) * deriv (deriv gluePhi) s := by ring
      rw [hsplit]
      exact hmain
  · -- equality on [1/2, ∞)
    intro s hs
    have hψ : gluePhi s = s := gluePhi_of_half_le hs
    rw [hψ]
    rw [show dev Z i s = Z s i - Commons.Geometry.Ulam.profileX s from rfl]
    ring
  · -- tail
    intro s hs
    have hs9 : (9 : ℝ) / 10 ≤ s := by
      have h1 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
      linarith [hs, h1]
    have hψ : gluePhi s = s := gluePhi_of_half_le (by linarith)
    have hdev0 : dev Z i (gluePhi s) = 0 := by
      rw [hψ]
      exact dev_tail i hi htail s (by
        have h1 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
        linarith [hs9, h1])
    rw [hdev0, add_zero]
    exact (profileX_eq s).symm
  · -- sign
    intro s hs
    have hmem : (1 : ℝ) / 4 < gluePhi s := gluePhi_gt_quarter hs
    obtain ⟨hb1, hb2, hb3⟩ := hd (gluePhi s) hmem
    have hmax : max 0 (9 / 10 - gluePhi s) ≤ 9 / 10 := max_le (by norm_num) (by linarith)
    have hψmem := gluePhi_deriv_mem s
    have hb : |deriv gluePhi s| ≤ 2 := abs_le.mpr ⟨hψmem.1, le_trans hψmem.2 (by norm_num)⟩
    have hsmall : |deriv (dev Z i) (gluePhi s) * deriv gluePhi s| ≤ 18 / 10000 := by
      rw [abs_mul]
      have ha : |deriv (dev Z i) (gluePhi s)| ≤ 1 / 1000 * (9 / 10) :=
        le_trans hb2 (mul_le_mul_of_nonneg_left hmax (by norm_num))
      calc |deriv (dev Z i) (gluePhi s)| * |deriv gluePhi s|
          ≤ (1 / 1000 * (9 / 10)) * 2 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
        _ = 18 / 10000 := by norm_num
    rw [hXderiv s hs, hχ s hs]
    rcases lt_or_ge s (1 / 100) with hs1 | hs1
    · have hzero : deriv (dev Z i) (gluePhi s) = 0 := by
        have h9 : 9 / 10 ≤ gluePhi s := gluePhi_ge_nine_tenths hs1.le
        have hmax0 : max 0 (9 / 10 - gluePhi s) = 0 := max_eq_left (by linarith)
        rw [hmax0, mul_zero] at hb2
        exact abs_eq_zero.mp (le_antisymm hb2 (abs_nonneg _))
      rw [hzero, zero_mul, add_zero]
      exact deriv_profileX_neg hs
    · rcases le_or_gt s (9 / 10) with hs2 | hs2
      · have hb' := deriv_profileX_le hs1 hs2
        have hb'' : deriv (dev Z i) (gluePhi s) * deriv gluePhi s ≤ 18 / 10000 := (abs_le.mp hsmall).2
        linarith
      · have hψs : gluePhi s = s := gluePhi_of_half_le (by linarith)
        have hzero : deriv (dev Z i) (gluePhi s) = 0 := by
          have h9 : 9 / 10 ≤ gluePhi s := by rw [hψs]; linarith
          have hmax0 : max 0 (9 / 10 - gluePhi s) = 0 := max_eq_left (by linarith)
          rw [hmax0, mul_zero] at hb2
          exact abs_eq_zero.mp (le_antisymm hb2 (abs_nonneg _))
        rw [hzero, zero_mul, add_zero]
        exact deriv_profileX_neg hs
  · -- tendsto
    have hPX_tend : Tendsto Commons.Geometry.Ulam.profileX (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hcont : ContinuousAt Commons.Geometry.Ulam.profileX 0 :=
        profX_contDiff.continuous.continuousAt
      have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      have h0 : Commons.Geometry.Ulam.profileX 0 = 1 := by
        rw [Commons.Geometry.Ulam.profileX]
        norm_num
      simpa [h0] using h
    have hdev_tend : Tendsto (fun t : ℝ => dev Z i (gluePhi t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hψt : Tendsto gluePhi (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hcont : ContinuousAt gluePhi 0 := gluePhi_contDiff.continuous.continuousAt
        have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
        simpa [gluePhi_zero] using h
      have hdevc : ContinuousAt (dev Z i) 1 := by
        have hproj : Continuous fun f : Work.OddVolterra.St => f i :=
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).continuous
        have hZi : ContinuousAt (fun x : ℝ => Z x i) 1 :=
          hproj.continuousAt.comp
            (hZsm.continuousOn.continuousAt (isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ) < 1)))
        exact hZi.sub (profX_contDiff.continuous.continuousAt)
      have h1 := hdevc.tendsto.comp hψt
      have h0 : dev Z i 1 = 0 := by
        have hb : Z 1 = Work.OddVolterra.baseState 1 :=
          htail 1 (by norm_num [Work.OddVolterra.tau])
        have hZi1 : (Z 1) i = Commons.Geometry.Ulam.profileX 1 := by
          rw [hb]
          rcases hi with rfl | rfl <;> simp [Work.OddVolterra.baseState]
        simp only [dev, hZi1, sub_self]
      simpa [h0, Function.comp_def] using h1
    simpa using hPX_tend.add hdev_tend
  · -- smoothness
    have hZi : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => Z x i) (Set.Ioi 0) :=
      ((contDiff_apply ℝ ℝ (n := (⊤ : ℕ∞)) i).contDiffOn (s := Set.univ)).comp hZsm
        (fun x _ => trivial)
    have hgφ : ContDiffOn ℝ (⊤ : ℕ∞) gluePhi (Set.Ioi 0) := gluePhi_contDiff.contDiffOn
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => Z (gluePhi t) i) (Set.Ioi 0) :=
      hZi.comp hgφ (fun t ht => show 0 < gluePhi t from by linarith [gluePhi_gt_quarter ht])
    have hdev : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => dev Z i (gluePhi t)) (Set.Ioi 0) := by
      have h1 : (fun t : ℝ => dev Z i (gluePhi t))
          = fun t : ℝ => Z (gluePhi t) i - Commons.Geometry.Ulam.profileX (gluePhi t) := by
        funext t; rfl
      rw [h1]
      exact hcomp.sub ((profX_contDiff.contDiffOn (s := Set.univ)).comp hgφ (fun t _ => trivial))
    exact (profX_contDiff.contDiffOn (s := Set.Ioi 0)).add hdev

theorem exists_isEnvelopeCurve_of_window_solution (n : ℕ) (hn : 1 ≤ n)
    {h : ℝ → ℝ} {Z : ℝ → Work.OddVolterra.St}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hhsmall : ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧
      |deriv (deriv h) s| ≤ 1 / 100)
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0 : ℝ)))
    (htail : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = Work.OddVolterra.baseState s)
    (hclose : ∀ s : ℝ, 1 / 4 ≤ s →
      |Z s 0 - Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
      |Z s 2 - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
      |deriv (fun u : ℝ => Z u 2) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 1000 ∧
      |Z s 1 - Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
      |Z s 3 - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 1000 ∧
      |deriv (fun u : ℝ => Z u 3) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 1000)
    (hderiv : ∀ s : ℝ, 1 / 4 ≤ s →
      deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3)
    (hsign : ∀ s : ℝ, 1 / 4 ≤ s → 0 < Z s 0 ∧ 0 < Z s 1 ∧ Z s 2 < 0 ∧ Z s 3 < 0) :
    ∃ X Y : ℝ → ℝ,
      Work.OddEnvelope.IsEnvelopeCurve h X Y ∧
      (∀ s : ℝ, 0 < s →
        |X s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
        |deriv X s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
        |deriv (deriv X) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
        |Y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
        |deriv Y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
        |deriv (deriv Y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100) ∧
      (∀ s : ℝ, 1 / 2 ≤ s → X s = Z s 0 ∧ Y s = Z s 1) := by
  have hX := glue_close (Z := Z) 0 2 (Or.inl rfl) (Or.inl rfl) hZsm htail
    (fun s hs => (hclose s hs).1) (fun s hs => (hderiv s hs).1)
    (fun s hs => (hclose s hs).2.2.1)
  have hY := glue_close (Z := Z) 1 3 (Or.inr rfl) (Or.inr rfl) hZsm htail
    (fun s hs => (hclose s hs).2.2.2.1) (fun s hs => (hderiv s hs).2)
    (fun s hs => (hclose s hs).2.2.2.2.2)
  have hh0 : h 0 = 0 := by
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    rw [Set.mem_Icc] at hmem
    have htau : Work.OddVolterra.tau = 1 / 10 := rfl
    rw [htau] at hmem
    norm_num at hmem
  refine ⟨fun s => Commons.Geometry.Ulam.profileX s + dev Z 0 (gluePhi s),
    fun s => Commons.Geometry.Ulam.profileX s + dev Z 1 (gluePhi s), ?_, ?_, ?_⟩
  · refine Work.OddEnvelope.Close.isEnvelopeCurve_of_close (δ := 1 / 100) (by norm_num)
      hX.2.2.2.2.2 hY.2.2.2.2.2 (hh.contDiffOn (s := Set.Ioi 0))
      hX.2.2.2.1 hY.2.2.2.1 hX.2.2.2.2.1 hY.2.2.2.2.1 hX.2.2.1 hY.2.2.1 hh0 hsupp
      (fun s hs => ⟨(hX.1 s hs).1, (hX.1 s hs).2.1, (hX.1 s hs).2.2⟩)
      (fun s hs => ⟨(hY.1 s hs).1, (hY.1 s hs).2.1, (hY.1 s hs).2.2⟩)
      (fun s => hhsmall s)
  · intro s hs
    exact ⟨(hX.1 s hs).1, (hX.1 s hs).2.1, (hX.1 s hs).2.2,
      (hY.1 s hs).1, (hY.1 s hs).2.1, (hY.1 s hs).2.2⟩
  · intro s hs
    exact ⟨hX.2.1 s hs, hY.2.1 s hs⟩

end

end Work.OddVolterra.Existence
