import Submission.Work.Fatou.Setup

/-!
# Analytic properties of the interpolating cut-off `smoothstep`

`smoothstep` is the `C¹` cut-off which is `0` on `(-∞,1/8]`, rises to `1` on `[1/8,7/8]`,
equals `1` on `[7/8,9/8]`, falls to `0` on `[9/8,15/8]` and equals `0` on `[15/8,∞)`.

We prove here that it is `C¹`, that `|smoothstep'| ≤ 2`, and the elementary evaluations used in
the construction of `devH`.  The `C¹` statement is obtained by writing `smoothstep` as the
difference of two rescaled copies of the elementary "ramp" `3t²-2t³`, whose `C¹`-regularity at the
two junction points is proved directly.
-/

namespace Work.Fatou

open Filter Set
open scoped Topology

noncomputable section

/-- The elementary smoothstep `0 → 1` on `[0,1]`. -/
def ramp (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 1 else 3 * t ^ 2 - 2 * t ^ 3

/-- The derivative of `ramp`. -/
def rampD (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else 6 * t * (1 - t)

theorem ramp_of_nonpos {t : ℝ} (h : t ≤ 0) : ramp t = 0 := by simp [ramp, h]

theorem rampD_of_nonpos {t : ℝ} (h : t ≤ 0) : rampD t = 0 := by simp [rampD, h]

theorem ramp_of_one_le {t : ℝ} (h : 1 ≤ t) : ramp t = 1 := by
  have h0 : ¬ (t ≤ 0) := by linarith
  simp [ramp, h0, h]

theorem rampD_of_one_le {t : ℝ} (h : 1 ≤ t) : rampD t = 0 := by
  have h0 : ¬ (t ≤ 0) := by linarith
  simp [rampD, h0, h]

theorem ramp_of_mem {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : ramp t = 3 * t ^ 2 - 2 * t ^ 3 := by
  have h0' : ¬ (t ≤ 0) := by linarith
  have h1' : ¬ (1 ≤ t) := by linarith
  simp [ramp, h0', h1']

theorem rampD_of_mem {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : rampD t = 6 * t * (1 - t) := by
  have h0' : ¬ (t ≤ 0) := by linarith
  have h1' : ¬ (1 ≤ t) := by linarith
  simp [rampD, h0', h1']

theorem ramp_eq_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ramp t = 3 * t ^ 2 - 2 * t ^ 3 := by
  rcases lt_or_eq_of_le h0 with h | h
  · rcases lt_or_eq_of_le h1 with h1 | h1
    · exact ramp_of_mem h h1
    · subst h1; norm_num [ramp]
  · subst h; norm_num [ramp]

theorem rampD_eq_poly {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : rampD t = 6 * t * (1 - t) := by
  rcases lt_or_eq_of_le h0 with h | h
  · rcases lt_or_eq_of_le h1 with h1 | h1
    · exact rampD_of_mem h h1
    · subst h1; norm_num [rampD]
  · subst h; norm_num [rampD]

/-- `rampD` is a continuous function (`max 0 (6t(1-t))`). -/
theorem rampD_eq_max (t : ℝ) : rampD t = max 0 (6 * t * (1 - t)) := by
  rcases le_or_gt t 0 with h | h
  · rw [rampD_of_nonpos h, max_eq_left]; nlinarith
  rcases le_or_gt 1 t with h1 | h1
  · rw [rampD_of_one_le h1, max_eq_left]; nlinarith
  · rw [rampD_of_mem h h1, max_eq_right]; nlinarith

theorem rampD_nonneg (t : ℝ) : 0 ≤ rampD t := by
  rw [rampD_eq_max]; exact le_max_left _ _

theorem abs_rampD_le (t : ℝ) : |rampD t| ≤ 3 / 2 := by
  rw [rampD_eq_max]
  rcases le_or_gt (6 * t * (1 - t)) 0 with h | h
  · rw [max_eq_left h, abs_zero]; norm_num
  · rw [max_eq_right h.le, abs_of_pos h]
    nlinarith [sq_nonneg (t - 1 / 2)]

theorem hasDerivAt_poly (t : ℝ) :
    HasDerivAt (fun s : ℝ => 3 * s ^ 2 - 2 * s ^ 3) (6 * t * (1 - t)) t := by
  have h1' : HasDerivAt (fun s : ℝ => 3 * s ^ 2) (3 * (2 * t ^ (2 - 1))) t :=
    (hasDerivAt_pow 2 t).const_mul 3
  have h2' : HasDerivAt (fun s : ℝ => 2 * s ^ 3) (2 * (3 * t ^ (3 - 1))) t :=
    (hasDerivAt_pow 3 t).const_mul 2
  have h := h1'.sub h2'
  convert h using 1 <;> ring

theorem hasDerivAt_ramp (t : ℝ) : HasDerivAt ramp (rampD t) t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [rampD_of_nonpos h.le]
    refine (hasDerivAt_const (x := t) (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds h] with s hs
    exact ramp_of_nonpos hs.le
  · rw [rampD_of_nonpos le_rfl]
    have hL : HasDerivWithinAt ramp 0 (Set.Iic 0) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).hasDerivWithinAt.congr
        (fun s hs => ramp_of_nonpos hs) (by rw [ramp_of_nonpos le_rfl])
    have hR : HasDerivWithinAt ramp 0 (Set.Ici 0) 0 := by
      have hp : HasDerivAt (fun s : ℝ => 3 * s ^ 2 - 2 * s ^ 3) 0 0 := by
        simpa using hasDerivAt_poly (0 : ℝ)
      refine hp.hasDerivWithinAt.congr_of_eventuallyEq ?_ (by rw [ramp_of_nonpos le_rfl]; norm_num)
      have h1 : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
      have h1' : Set.Iio (1 : ℝ) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := nhdsWithin_le_nhds h1
      filter_upwards [self_mem_nhdsWithin, h1'] with s hs hs1
      exact ramp_eq_poly (by simpa using hs) hs1.le
    have hunion : Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ) = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
      exact le_total x 0
    exact hasDerivWithinAt_univ.mp (hunion ▸ hL.union hR)
  · rcases lt_trichotomy t 1 with h1 | rfl | h1
    · rw [rampD_of_mem h h1]
      refine (hasDerivAt_poly t).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds ⟨h, h1⟩] with s hs
      exact ramp_eq_poly hs.1.le hs.2.le
    · rw [rampD_of_one_le le_rfl]
      have hR : HasDerivWithinAt ramp 0 (Set.Ici 1) 1 :=
        (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).hasDerivWithinAt.congr
          (fun s hs => ramp_of_one_le hs) (by rw [ramp_of_one_le le_rfl])
      have hL : HasDerivWithinAt ramp 0 (Set.Iic 1) 1 := by
        have hp : HasDerivAt (fun s : ℝ => 3 * s ^ 2 - 2 * s ^ 3) 0 1 := by
          simpa using hasDerivAt_poly (1 : ℝ)
        refine hp.hasDerivWithinAt.congr_of_eventuallyEq ?_
          (by rw [ramp_of_one_le le_rfl]; norm_num)
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds
            (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 from by norm_num))]
          with s hs hs1
        exact ramp_eq_poly hs1.le hs
      have hunion : Set.Iic (1 : ℝ) ∪ Set.Ici (1 : ℝ) = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
        exact le_total x 1
      exact hasDerivWithinAt_univ.mp (hunion ▸ hL.union hR)
    · rw [rampD_of_one_le h1.le]
      refine (hasDerivAt_const (x := t) (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds h1] with s hs
      exact ramp_of_one_le hs.le

theorem differentiable_ramp : Differentiable ℝ ramp :=
  fun t => (hasDerivAt_ramp t).differentiableAt

theorem deriv_ramp (t : ℝ) : deriv ramp t = rampD t := (hasDerivAt_ramp t).deriv

theorem continuous_rampD : Continuous rampD := by
  rw [show rampD = fun t : ℝ => max 0 (6 * t * (1 - t)) from funext rampD_eq_max]
  fun_prop

theorem contDiff_ramp : ContDiff ℝ 1 ramp := by
  rw [contDiff_one_iff_deriv]
  refine ⟨differentiable_ramp, ?_⟩
  rw [show deriv ramp = rampD from funext deriv_ramp]
  exact continuous_rampD

/-! ### Transferring to `smoothstep` -/

theorem ramp_arg_sub (t : ℝ) :
    (t - 1 / 8) / (3 / 4) = (t - 9 / 8) / (3 / 4) + 4 / 3 := by
  field_simp; ring

theorem ramp_arg₁_nonpos {t : ℝ} (h : t ≤ 1 / 8) : (t - 1 / 8) / (3 / 4) ≤ 0 := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₂_nonpos {t : ℝ} (h : t ≤ 9 / 8) : (t - 9 / 8) / (3 / 4) ≤ 0 := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₁_pos {t : ℝ} (h : 1 / 8 < t) : 0 < (t - 1 / 8) / (3 / 4) :=
  div_pos (by linarith) (by norm_num)

theorem ramp_arg₂_pos {t : ℝ} (h : 9 / 8 < t) : 0 < (t - 9 / 8) / (3 / 4) :=
  div_pos (by linarith) (by norm_num)

theorem ramp_arg₁_lt_one {t : ℝ} (h : t < 7 / 8) : (t - 1 / 8) / (3 / 4) < 1 := by
  rw [div_lt_one (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₂_lt_one {t : ℝ} (h : t < 15 / 8) : (t - 9 / 8) / (3 / 4) < 1 := by
  rw [div_lt_one (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₁_le_one {t : ℝ} (h : t ≤ 7 / 8) : (t - 1 / 8) / (3 / 4) ≤ 1 := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₂_le_one {t : ℝ} (h : t ≤ 15 / 8) : (t - 9 / 8) / (3 / 4) ≤ 1 := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₁_one_le {t : ℝ} (h : 7 / 8 ≤ t) : 1 ≤ (t - 1 / 8) / (3 / 4) := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem ramp_arg₂_one_le {t : ℝ} (h : 15 / 8 ≤ t) : 1 ≤ (t - 9 / 8) / (3 / 4) := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3 / 4)]; linarith

theorem smoothstep_eq_zero_of_le {t : ℝ} (h : t ≤ 1 / 8) : smoothstep t = 0 := by
  simp only [smoothstep]; rw [if_pos h]

theorem smoothstep_eq_one_of_mem {t : ℝ} (h1 : 7 / 8 ≤ t) (h2 : t ≤ 9 / 8) : smoothstep t = 1 := by
  have h : ¬ t ≤ 1 / 8 := by linarith
  have h' : ¬ t < 7 / 8 := by linarith
  simp only [smoothstep, if_neg h, if_neg h', if_pos h2]

theorem smoothstep_eq_zero_of_ge {t : ℝ} (h : 15 / 8 ≤ t) : smoothstep t = 0 := by
  have h1 : ¬ t ≤ 1 / 8 := by linarith
  have h2 : ¬ t < 7 / 8 := by linarith
  have h3 : ¬ t ≤ 9 / 8 := by linarith
  have h4 : ¬ t < 15 / 8 := by linarith
  simp only [smoothstep, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- `smoothstep t = 3u² - 2u³` in the rising part `1/8 < t < 7/8`, `u = (t-1/8)/(3/4)`. -/
theorem smoothstep_eq_mid {t : ℝ} (h1 : 1 / 8 < t) (h2 : t < 7 / 8) :
    smoothstep t = 3 * ((t - 1 / 8) / (3 / 4)) ^ 2 - 2 * ((t - 1 / 8) / (3 / 4)) ^ 3 := by
  have h : ¬ t ≤ 1 / 8 := by linarith
  simp only [smoothstep, if_neg h, if_pos h2]

/-- `smoothstep t = 3v² - 2v³` in the falling part `9/8 < t < 15/8`, `v = (15/8-t)/(3/4)`. -/
theorem smoothstep_eq_mid2 {t : ℝ} (h1 : 9 / 8 < t) (h2 : t < 15 / 8) :
    smoothstep t = 3 * ((15 / 8 - t) / (3 / 4)) ^ 2 - 2 * ((15 / 8 - t) / (3 / 4)) ^ 3 := by
  have h : ¬ t ≤ 1 / 8 := by linarith
  have h' : ¬ t < 7 / 8 := by linarith
  have h'' : ¬ t ≤ 9 / 8 := by linarith
  simp only [smoothstep, if_neg h, if_neg h', if_neg h'', if_pos h2]

/-- `smoothstep` is the difference of two rescaled copies of `ramp`. -/
theorem smoothstep_eq_ramp (t : ℝ) :
    smoothstep t = ramp ((t - 1 / 8) / (3 / 4)) - ramp ((t - 9 / 8) / (3 / 4)) := by
  rcases le_or_gt t (1 / 8) with h | h
  · rw [smoothstep_eq_zero_of_le h, ramp_of_nonpos (ramp_arg₁_nonpos h),
      ramp_of_nonpos (ramp_arg₂_nonpos (by linarith))]
    norm_num
  rcases lt_or_ge t (7 / 8) with h2 | h2
  · rw [smoothstep_eq_mid h h2, ramp_of_mem (ramp_arg₁_pos h) (ramp_arg₁_lt_one h2),
      ramp_of_nonpos (ramp_arg₂_nonpos (by linarith))]
    ring
  rcases le_or_gt t (9 / 8) with h3 | h3
  · rw [smoothstep_eq_one_of_mem h2 h3, ramp_of_one_le (ramp_arg₁_one_le h2),
      ramp_of_nonpos (ramp_arg₂_nonpos h3)]
    norm_num
  rcases lt_or_ge t (15 / 8) with h4 | h4
  · rw [smoothstep_eq_mid2 h3 h4, ramp_of_one_le (ramp_arg₁_one_le (by linarith)),
      ramp_eq_poly (ramp_arg₂_pos h3).le (ramp_arg₂_le_one h4.le)]
    have hsub : (15 / 8 - t) / (3 / 4) = 1 - (t - 9 / 8) / (3 / 4) := by
      rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff (by norm_num : (3 : ℝ) / 4 ≠ 0)]; ring
    rw [hsub]; ring
  · rw [smoothstep_eq_zero_of_ge h4, ramp_of_one_le (ramp_arg₁_one_le (by linarith)),
      ramp_of_one_le (ramp_arg₂_one_le h4)]
    norm_num

theorem smoothstep_mem_Icc (t : ℝ) : smoothstep t ∈ Set.Icc (0 : ℝ) 1 := by
  rcases le_or_gt t (1 / 8) with h | h
  · rw [smoothstep_eq_zero_of_le h]; norm_num
  rcases lt_or_ge t (7 / 8) with h2 | h2
  · rw [smoothstep_eq_mid h h2]
    have hu : 0 < (t - 1 / 8) / (3 / 4) := ramp_arg₁_pos h
    have hu1 : (t - 1 / 8) / (3 / 4) < 1 := ramp_arg₁_lt_one h2
    have h3u : 0 < 3 - 2 * ((t - 1 / 8) / (3 / 4)) := by linarith
    constructor
    · nlinarith [mul_nonneg (sq_nonneg ((t - 1 / 8) / (3 / 4))) h3u.le]
    · nlinarith [sq_nonneg (1 - (t - 1 / 8) / (3 / 4))]
  rcases le_or_gt t (9 / 8) with h3 | h3
  · rw [smoothstep_eq_one_of_mem h2 h3]; norm_num
  rcases lt_or_ge t (15 / 8) with h4 | h4
  · rw [smoothstep_eq_mid2 h3 h4]
    have hu : 0 < (15 / 8 - t) / (3 / 4) := div_pos (by linarith) (by norm_num)
    have hu1 : (15 / 8 - t) / (3 / 4) < 1 := by
      rw [div_lt_one (by norm_num : (0:ℝ) < 3 / 4)]; linarith
    have h3u : 0 < 3 - 2 * ((15 / 8 - t) / (3 / 4)) := by linarith
    constructor
    · nlinarith [mul_nonneg (sq_nonneg ((15 / 8 - t) / (3 / 4))) h3u.le]
    · nlinarith [sq_nonneg (1 - (15 / 8 - t) / (3 / 4))]
  · rw [smoothstep_eq_zero_of_ge h4]; norm_num

theorem hasDerivAt_smoothstep (t : ℝ) :
    HasDerivAt smoothstep ((rampD ((t - 1 / 8) / (3 / 4))) * (4 / 3) -
      (rampD ((t - 9 / 8) / (3 / 4))) * (4 / 3)) t := by
  have hf : smoothstep = fun s : ℝ =>
      ramp ((s - 1 / 8) / (3 / 4)) - ramp ((s - 9 / 8) / (3 / 4)) :=
    funext smoothstep_eq_ramp
  rw [hf]
  have hg : ∀ c : ℝ, HasDerivAt (fun s : ℝ => (s - c) / (3 / 4)) (4 / 3) t := by
    intro c
    have h := (hasDerivAt_id t).sub_const c |>.div_const (3 / 4)
    convert h using 1 <;> norm_num
  exact ((hasDerivAt_ramp ((t - 1 / 8) / (3 / 4))).comp t (hg (1 / 8))).sub
    ((hasDerivAt_ramp ((t - 9 / 8) / (3 / 4))).comp t (hg (9 / 8)))

theorem abs_deriv_smoothstep_le (t : ℝ) : |deriv smoothstep t| ≤ 2 := by
  rw [(hasDerivAt_smoothstep t).deriv]
  have hkey : rampD ((t - 9 / 8) / (3 / 4)) = 0 ∨ rampD ((t - 1 / 8) / (3 / 4)) = 0 := by
    by_cases hb0 : rampD ((t - 9 / 8) / (3 / 4)) = 0
    · exact Or.inl hb0
    refine Or.inr ?_
    have hab := ramp_arg_sub t
    rcases le_or_gt ((t - 9 / 8) / (3 / 4)) 0 with h' | h'
    · exact absurd (rampD_of_nonpos h') hb0
    have hlt1 : ((t - 9 / 8) / (3 / 4)) < 1 := by
      by_contra hcon
      exact hb0 (rampD_of_one_le (not_lt.mp hcon))
    have : 1 < ((t - 1 / 8) / (3 / 4)) := by rw [hab]; linarith
    exact rampD_of_one_le this.le
  rcases hkey with h' | h'
  · rw [h', zero_mul, sub_zero, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4 / 3)]
    have := abs_rampD_le ((t - 1 / 8) / (3 / 4))
    linarith
  · rw [h', zero_mul, zero_sub, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 4 / 3)]
    have := abs_rampD_le ((t - 9 / 8) / (3 / 4))
    linarith

end

end Work.Fatou
