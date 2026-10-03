import Mathlib
import Submission.Work.Repel.log_deriv_bound_unit
import Submission.Work.Repel.gronwall_lower
import Submission.Work.Repel.logGronwall_factor

namespace Work.Repel

open scoped Real
open Metric

/-- **Grönwall upper bound, differential form.**  Dual to `Work.Repel.gronwall_lower`: if
`y' ≤ K · y` on `(a,b)` and `A' = K`, then `y b ≤ y a · exp (A b - A a)`.

Proof: `s ↦ y s · exp (-A s)` has derivative `exp (-A s) · (y' s - K s · y s) ≤ 0`, hence is
antitone, and `exp (A b - A a) = exp (A b) · exp (-A a)`. -/
theorem gronwall_upper_alt {y y' A K : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Set.Icc a b))
    (hyd : ∀ t ∈ Set.Ioo a b, HasDerivAt y (y' t) t)
    (hA : ContinuousOn A (Set.Icc a b))
    (hAd : ∀ t ∈ Set.Ioo a b, HasDerivAt A (K t) t)
    (hineq : ∀ t ∈ Set.Ioo a b, y' t ≤ K t * y t) :
    y b ≤ y a * Real.exp (A b - A a) := by
  have hexp_neg : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s => Real.exp (-(A s))) (Real.exp (-(A t)) * (-(K t))) t := by
    intro t ht
    have h := (hAd t ht).neg.exp
    simpa only [Pi.neg_apply] using h
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s => y s * Real.exp (-(A s)))
        (Real.exp (-(A t)) * (y' t - K t * y t)) t := by
    intro t ht
    have h := (hyd t ht).mul (hexp_neg t ht)
    have h2 : y' t * Real.exp (-(A t)) + y t * (Real.exp (-(A t)) * (-(K t)))
        = Real.exp (-(A t)) * (y' t - K t * y t) := by ring
    rw [h2] at h
    exact h
  have hcont : ContinuousOn (fun s => y s * Real.exp (-(A s))) (Set.Icc a b) :=
    hy.mul (Real.continuous_exp.comp_continuousOn hA.neg)
  have hdiff : DifferentiableOn ℝ (fun s => y s * Real.exp (-(A s)))
      (interior (Set.Icc a b)) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ t ∈ interior (Set.Icc a b),
      deriv (fun s => y s * Real.exp (-(A s))) t ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    rw [(hderiv t ht).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hineq t ht])
  have hanti : AntitoneOn (fun s => y s * Real.exp (-(A s))) (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff hnonpos
  have hmain : y b * Real.exp (-(A b)) ≤ y a * Real.exp (-(A a)) :=
    hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have h2 := mul_le_mul_of_nonneg_right hmain (Real.exp_pos (A b)).le
  calc y b = (y b * Real.exp (-(A b))) * Real.exp (A b) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ (y a * Real.exp (-(A a))) * Real.exp (A b) := h2
    _ = y a * Real.exp (A b - A a) := by
        rw [mul_assoc, ← Real.exp_add, show -A a + A b = A b - A a by ring]

/-- Chain rule along a complex line: the real derivative of `t ↦ P (t * z)` is `z * P'(t z)`. -/
private lemma hasDerivAt_comp_mul_right_alt {P : ℂ → ℂ} {z : ℂ} {t : ℝ}
    (hd : DifferentiableAt ℂ P ((t : ℂ) * z)) :
    HasDerivAt (fun s : ℝ => P ((s : ℂ) * z)) (z * deriv P ((t : ℂ) * z)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
    have h := (Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt
    simpa using h.mul_const z
  have h1 : HasDerivAt P (deriv P ((t : ℂ) * z)) ((t : ℂ) * z) := hd.hasDerivAt
  have h3 := h1.scomp t h2
  simpa [Function.comp_def, smul_eq_mul] using h3

/-- **Sharp distortion (derivative) upper bound on the unit disc.**  For `g` holomorphic on the
unit disc whose second derivative is controlled by
`‖g''(w)‖ ≤ ((4 + 2‖w‖)/(1 - ‖w‖²)) ‖g'(w)‖` (the Bieberbach/log-derivative inequality), and
`z` with `‖z‖ ≤ 1/2`,

`‖g'(z)‖ ≤ ‖g'(0)‖ (1 + ‖z‖)/(1 - ‖z‖)³`.

The proof integrates the logarithmic derivative radially: with `y t = ‖g'(t z)‖²` one has
`y' t ≤ K t · y t` where `K t = 2‖z‖(4 + 2t‖z‖)/(1 - (t‖z‖)²)`, and the integrating factor is
`A t = 2 log (1 + t‖z‖) - 6 log (1 - t‖z‖)` (`Work.Repel.logGronwall_factor`), giving
`y 1 ≤ y 0 ((1 + ‖z‖)/(1 - ‖z‖)³)²`. -/
theorem deriv_upper_of_log_deriv_bound {g : ℂ → ℂ}
    (han : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ g w)
    (hbound : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      ‖deriv (deriv g) w‖ ≤ (4 + 2 * ‖w‖) / (1 - ‖w‖ ^ 2) * ‖deriv g w‖)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖deriv g z‖ ≤ ‖deriv g 0‖ * ((1 + ‖z‖) / (1 - ‖z‖) ^ 3) := by
  set r : ℝ := ‖z‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg z
  have hr1 : r ≤ 1 / 2 := by rw [hr]; exact hz
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ‖(t : ℂ) * z‖ = t * r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1, ← hr]
      _ ≤ 1 * (1 / 2) := mul_le_mul ht.2 hr1 hr0 (by norm_num)
      _ < 1 := by norm_num
  have hdan : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (deriv g) w :=
    fun w hw => (han w hw).deriv
  obtain ⟨hAc0, hAd0, hAexp0⟩ := logGronwall_factor r hr0 hr1
  set A : ℝ → ℝ := fun t => 2 * Real.log (1 + t * r) - 6 * Real.log (1 - t * r) with hAdef
  set K : ℝ → ℝ := fun t => 2 * r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)) with hKdef
  have hAc : ContinuousOn A (Set.Icc 0 1) := by rw [hAdef]; exact hAc0
  have hAd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt A (K t) t := by
    intro t ht; rw [hAdef, hKdef]; exact hAd0 t ht
  have hFc : ContinuousOn (fun t : ℝ => deriv g ((t : ℂ) * z)) (Set.Icc 0 1) := by
    intro t ht
    have h1 : ContinuousAt (deriv g) ((t : ℂ) * z) := (hdan _ (hmem t ht)).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => (s : ℂ) * z) t := by fun_prop
    have h3 : ContinuousAt ((deriv g) ∘ fun s : ℝ => (s : ℂ) * z) t :=
      ContinuousAt.comp (f := fun s : ℝ => (s : ℂ) * z) (x := t) h1 h2
    simpa [Function.comp_def] using h3.continuousWithinAt
  have hyc : ContinuousOn (fun t : ℝ => ‖deriv g ((t : ℂ) * z)‖ ^ 2) (Set.Icc 0 1) :=
    (hFc.norm).pow 2
  have hyd : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ‖deriv g ((s : ℂ) * z)‖ ^ 2)
        (2 * inner ℝ (deriv g ((t : ℂ) * z)) (z * deriv (deriv g) ((t : ℂ) * z))) t := by
    intro t ht
    have hw : ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := hmem t (Set.Ioo_subset_Icc_self ht)
    have hd : DifferentiableAt ℂ (deriv g) ((t : ℂ) * z) := (hdan _ hw).differentiableAt
    exact (hasDerivAt_comp_mul_right_alt hd).norm_sq
  have hineq : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (2 * inner ℝ (deriv g ((t : ℂ) * z)) (z * deriv (deriv g) ((t : ℂ) * z)))
        ≤ K t * ‖deriv g ((t : ℂ) * z)‖ ^ 2 := by
    intro t ht
    rw [hKdef]
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hw : ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := hmem t (Set.Ioo_subset_Icc_self ht)
    have htnorm : ‖((t : ℂ) * z)‖ = t * r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, ← hr]
    have hb := hbound ((t : ℂ) * z) hw
    rw [htnorm] at hb
    have hkey : ‖z * deriv (deriv g) ((t : ℂ) * z)‖
        ≤ (r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2))) * ‖deriv g ((t : ℂ) * z)‖ := by
      rw [norm_mul, ← hr]
      calc r * ‖deriv (deriv g) ((t : ℂ) * z)‖
          ≤ r * (((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)) * ‖deriv g ((t : ℂ) * z)‖) :=
            mul_le_mul_of_nonneg_left hb hr0
        _ = (r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2))) * ‖deriv g ((t : ℂ) * z)‖ := by
            ring
    have hcs := abs_real_inner_le_norm (deriv g ((t : ℂ) * z))
      (z * deriv (deriv g) ((t : ℂ) * z))
    have hle : inner ℝ (deriv g ((t : ℂ) * z)) (z * deriv (deriv g) ((t : ℂ) * z))
        ≤ ‖deriv g ((t : ℂ) * z)‖ * ((r * ((4 + 2 * (t * r)) / (1 - (t * r) ^ 2)))
            * ‖deriv g ((t : ℂ) * z)‖) :=
      (le_abs_self _).trans (hcs.trans (mul_le_mul_of_nonneg_left hkey (norm_nonneg _)))
    nlinarith [hle, norm_nonneg (deriv g ((t : ℂ) * z))]
  have hmain := gronwall_upper_alt (y := fun t : ℝ => ‖deriv g ((t : ℂ) * z)‖ ^ 2)
      (y' := fun t : ℝ => 2 * inner ℝ (deriv g ((t : ℂ) * z))
        (z * deriv (deriv g) ((t : ℂ) * z)))
      (A := A) (K := K) (by norm_num) hyc hyd hAc hAd hineq
  have hA0 : A 0 = 0 := by rw [hAdef]; simp [Real.log_one]
  have hexp : Real.exp (A 1 - A 0) = ((1 + r) / (1 - r) ^ 3) ^ 2 := by
    rw [hA0, sub_zero]
    have hpos1 : 0 < 1 + r := by linarith
    have hpos2 : 0 < 1 - r := by linarith
    have h3 : (Real.exp (A 1))⁻¹ = ((1 - r) ^ 3 / (1 + r)) ^ 2 := by
      rw [← Real.exp_neg]; exact hAexp0
    have h2 : Real.exp (A 1) = (((1 - r) ^ 3 / (1 + r)) ^ 2)⁻¹ := by
      rw [← h3, inv_inv]
    rw [h2, ← inv_pow, inv_div]
  have hkey : ‖deriv g z‖ ^ 2 ≤ (‖deriv g 0‖ * ((1 + r) / (1 - r) ^ 3)) ^ 2 := by
    rw [hexp] at hmain
    rw [mul_pow]
    simpa using hmain
  have hfpos : 0 < (1 + r) / (1 - r) ^ 3 :=
    div_pos (by linarith) (pow_pos (by linarith) 3)
  have h := sq_le_sq.mp hkey
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (norm_nonneg _) hfpos.le)] at h
  simpa [hr] using h

/-- **Growth step on the unit disc from a pointwise derivative bound along a ray.**  If the
derivative of `g` along the segment `[0, z]` is bounded by `‖g'(0)‖ (1 + t‖z‖)/(1 - t‖z‖)³`, then
`‖g z - g 0‖ ≤ ‖g'(0)‖ ‖z‖/(1 - ‖z‖)²`.

The proof fences `F t = g (t z) - g 0` by the explicit envelope
`B t = ‖g'(0)‖ (t‖z‖)/(1 - t‖z‖)²`, whose derivative `‖g'(0)‖ ‖z‖(1 + t‖z‖)/(1 - t‖z‖)³`
dominates `‖F' t‖ = ‖g'(t z)‖ ‖z‖`; note `B 1 = ‖g'(0)‖ ‖z‖/(1 - ‖z‖)²`. -/
theorem growth_of_deriv_bound_alt {g : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1)
    (hdiff : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ g w)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv g ((t : ℂ) * z)‖ ≤ ‖deriv g 0‖ * ((1 + t * ‖z‖) / (1 - t * ‖z‖) ^ 3)) :
    ‖g z - g 0‖ ≤ ‖deriv g 0‖ * (‖z‖ / (1 - ‖z‖) ^ 2) := by
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  set r : ℝ := ‖z‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg z
  have hr1 : r < 1 := by rw [hr]; exact hz1
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ‖(t : ℂ) * z‖ = t * r := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1, ← hr]
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right ht.2 hr0
      _ = r := one_mul _
      _ < 1 := hr1
  let F : ℝ → ℂ := fun t => g ((t : ℂ) * z) - g 0
  let F' : ℝ → ℂ := fun t => deriv g ((t : ℂ) * z) * z
  have hFc : ContinuousOn F (Set.Icc 0 1) := by
    have hgc : ContinuousOn g (Metric.ball (0 : ℂ) 1) :=
      fun w hw => (hdiff w hw).continuousAt.continuousWithinAt
    have hp : ContinuousOn (fun t : ℝ => (t : ℂ) * z) (Set.Icc 0 1) := by fun_prop
    have h1 : ContinuousOn (fun t : ℝ => g ((t : ℂ) * z)) (Set.Icc 0 1) :=
      hgc.comp hp hseg
    exact h1.sub continuousOn_const
  have hFd : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt F (F' x) (Set.Ici x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
    have hmem := hseg x hxIcc
    have hgx : HasDerivAt g (deriv g ((x : ℂ) * z)) ((x : ℂ) * z) := (hdiff _ hmem).hasDerivAt
    have hpath : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const z
    have h1 : HasDerivAt (fun t : ℝ => g ((t : ℂ) * z)) (deriv g ((x : ℂ) * z) * z) x :=
      hgx.comp x hpath
    exact (h1.sub_const (g 0)).hasDerivWithinAt
  let B : ℝ → ℝ := fun t => ‖deriv g 0‖ * ((t * r) / (1 - t * r) ^ 2)
  let B' : ℝ → ℝ := fun t => ‖deriv g 0‖ * (r * (1 + t * r) / (1 - t * r) ^ 3)
  have hB0 : ‖F 0‖ ≤ B 0 := by
    have hF0 : F 0 = 0 := by simp [F]
    have hBz : B 0 = 0 := by simp [B]
    rw [hF0, norm_zero, hBz]
  have hBc : ContinuousOn B (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun t : ℝ => t * r) (Set.Icc 0 1) := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => (1 - t * r) ^ 2) (Set.Icc 0 1) := by fun_prop
    have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t * r) ^ 2 ≠ 0 := by
      intro t ht
      have hle : t * r ≤ r := by
        have h := mul_le_mul_of_nonneg_right ht.2 hr0; rwa [one_mul] at h
      exact pow_ne_zero 2 (ne_of_gt (by linarith))
    have h3 : ContinuousOn (fun t : ℝ => (t * r) / (1 - t * r) ^ 2) (Set.Icc 0 1) :=
      h1.div h2 hne
    simpa only [B] using h3.const_mul (‖deriv g 0‖)
  have hBd : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt B (B' x) (Set.Ici x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
    have hne : 1 - x * r ≠ 0 := by
      have hle : x * r ≤ r := by
        have h := mul_le_mul_of_nonneg_right hxIcc.2 hr0; rwa [one_mul] at h
      linarith
    have hnum : HasDerivAt (fun t : ℝ => t * r) r x := by
      simpa using (hasDerivAt_id x).mul_const r
    have hden : HasDerivAt (fun t : ℝ => (1 - t * r) ^ 2) (2 * (1 - x * r) * (-r)) x := by
      have h1 : HasDerivAt (fun t : ℝ => 1 - t * r) (-r) x := by
        simpa using ((hasDerivAt_id x).mul_const r).const_sub 1
      have hp := h1.pow 2
      have h2 : (((2 : ℕ) : ℝ) * (1 - x * r) ^ (2 - 1) * (-r))
          = 2 * (1 - x * r) * (-r) := by
        simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      rw [h2] at hp
      exact hp
    have hq : HasDerivAt (fun t : ℝ => (t * r) / (1 - t * r) ^ 2)
        (r * (1 + x * r) / (1 - x * r) ^ 3) x := by
      have h := hnum.div hden (pow_ne_zero 2 hne)
      have h2 : (r * (1 - x * r) ^ 2 - x * r * (2 * (1 - x * r) * (-r)))
            / ((1 - x * r) ^ 2) ^ 2 = r * (1 + x * r) / (1 - x * r) ^ 3 := by
        field_simp
        ring
      rw [h2] at h
      exact h
    exact (hq.const_mul (‖deriv g 0‖)).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖F' x‖ ≤ B' x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
    have hd := hderiv x hxIcc
    have hFx : ‖F' x‖ = ‖deriv g ((x : ℂ) * z)‖ * r := by
      show ‖deriv g ((x : ℂ) * z) * z‖ = ‖deriv g ((x : ℂ) * z)‖ * r
      rw [norm_mul, ← hr]
    rw [hFx]
    calc ‖deriv g ((x : ℂ) * z)‖ * r
        ≤ (‖deriv g 0‖ * ((1 + x * r) / (1 - x * r) ^ 3)) * r :=
          mul_le_mul_of_nonneg_right hd hr0
      _ = B' x := by
          simp only [B']
          ring
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := 0) (b := 1)
    hFc hFd hB0 hBc hBd hbound
  have h1 := hmain (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have hF1 : F 1 = g z - g 0 := by simp [F]
  have hB1 : B 1 = ‖deriv g 0‖ * (r / (1 - r) ^ 2) := by
    simp only [B, one_mul]
  rw [hF1, hB1] at h1
  simpa [hr] using h1

/-- **Growth bound at quarter scale (independent second proof).**  For `f` holomorphic on
`closedBall c R` and injective on `ball c R` (`0 < R`), the image of the sub-disc of radius `R/6`
lies in the Koebe ball of radius `‖deriv f c‖ * R/4` about `f c`.

The classical sharp growth bound gives `‖f z - f c‖ ≤ ‖deriv f c‖ * ‖z - c‖ / (1 - ‖z-c‖/R)^2`
for `z ∈ ball c R`; at `‖z - c‖ ≤ R/6` this is `6R/25 < R/4` times `‖deriv f c‖`, so the
statement is TRUE (`deriv f c ≠ 0` follows from injectivity on the ball).

IMPORTANT: the proof must not use any declaration tainted by `sorry`.  In particular

* usable (verified axiom-clean): `Work.Repel.bieberbach_two_aux`,
  `Work.Repel.Koebe.bieberbach_two_of_area`, `Work.Repel.Koebe.area_theorem`,
  `Work.Repel.koebeT_iteratedDeriv_two`, `Work.Repel.deriv_lower_aux`,
  `Work.Repel.deriv_lower_of_second_deriv_bound`, `Work.Repel.koebe_covering_scaled`,
  `Work.Repel.two_point_lower_half_ball`, `Work.Repel.deriv_variation_small_ball`,
  `Work.Repel.log_deriv_bound_unit`;
* NOT usable (they import `Submission.Work.Repel.KoebeAuxStub`, which contains `sorry`):
  `Work.Repel.koebe_covering`, `Work.Repel.Koebe.bieberbach_two`,
  `Work.Repel.upper_growth_small_ball`.

Routes.  (a) sharp: normalise to the unit disc; the Koebe transform plus the sharp Bieberbach
bound `‖a₂‖ ≤ 2` (`bieberbach_two_aux`, `koebeT_iteratedDeriv_two`) gives
`‖(1 - ‖z‖^2) * f''(z)/f'(z) - 2 * conj z‖ ≤ 4`; integrating the logarithmic derivative gives the
distortion bound `‖f'(z)‖ ≤ ‖f'(0)‖ * (1+r)/(1-r)^3`, and integrating once more radius-wise gives
`‖f(z)‖ ≤ ‖f'(0)‖ * r/(1-r)^2`, so `‖f z‖ ≤ (6/25) ‖deriv f c‖ * R < ‖deriv f c‖ * R / 4`.
(b) cruder: integrate `‖f''/f'‖ ≤ (4 + 2r)/(1 - r^2)` radially, getting
`‖f'(c + t e^{iθ})‖ ≤ ‖f'(c)‖ * ((1 + t/R)/(1 - t/R))^2` and
`‖f z - f c‖ ≤ ‖deriv f c‖ * R * (τ + 4*(τ/(1-τ) + Real.log (1-τ)))` with `τ = ‖z-c‖/R`;
at `τ = 1/6` this is `≈ 0.2374 < 1/4`.  Both routes are acceptable. -/
theorem growth_le_quarter_alt {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hinj : Set.InjOn f (Metric.ball c R)) :
    ∀ z ∈ Metric.closedBall c (R / 6), ‖f z - f c‖ ≤ ‖deriv f c‖ * (R / 4) := by
  intro z hz
  have hzc : ‖z - c‖ ≤ R / 6 := by
    have h := Metric.mem_closedBall.mp hz
    rwa [dist_eq_norm] at h
  have hzR : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hcmem : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  set G : ℂ → ℂ := fun w => f (c + (R : ℂ) * w) with hGdef
  have hmem : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → c + (R : ℂ) * w ∈ Metric.ball c R := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hw
    rw [Metric.mem_ball, dist_eq_norm,
      show c + (R : ℂ) * w - c = (R : ℂ) * w by ring, norm_mul,
      Complex.norm_of_nonneg hR.le]
    nlinarith
  have hGan : ∀ w ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G w := by
    intro w hw
    rw [hGdef]
    have hwm : c + (R : ℂ) * w ∈ Metric.ball c R := hmem w hw
    have hf_at : AnalyticAt ℂ f (c + (R : ℂ) * w) :=
      hf.analyticAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hwm)
        Metric.ball_subset_closedBall)
    have hinner : AnalyticAt ℂ (fun v : ℂ => c + (R : ℂ) * v) w := by fun_prop
    have h1 : AnalyticAt ℂ (fun v : ℂ => f (c + (R : ℂ) * v)) w :=
      AnalyticAt.comp hf_at hinner
    simpa [Function.comp_def] using h1
  have hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1) := by
    intro w₁ hw₁ w₂ hw₂ heq
    rw [hGdef] at heq
    have h3 : c + (R : ℂ) * w₁ = c + (R : ℂ) * w₂ :=
      hinj (hmem w₁ hw₁) (hmem w₂ hw₂) heq
    have h4 : (R : ℂ) * w₁ = (R : ℂ) * w₂ := add_left_cancel h3
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne') h4
  have hGdiff : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℂ G w :=
    fun w hw => (hGan w hw).differentiableAt
  have hfc : AnalyticAt ℂ f c :=
    hf.analyticAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hcmem)
        Metric.ball_subset_closedBall)
  have hGd0 : deriv G 0 = (R : ℂ) * deriv f c := by
    have h1 : HasDerivAt (fun w : ℂ => c + (R : ℂ) * w) (R : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (R : ℂ)).const_add c
    have hd : DifferentiableAt ℂ f (c + (R : ℂ) * (0 : ℂ)) := by
      rw [mul_zero, add_zero]; exact hfc.differentiableAt
    have h2 : HasDerivAt (fun w : ℂ => f (c + (R : ℂ) * w)) (deriv f c * (R : ℂ)) 0 := by
      have hc := hd.hasDerivAt.comp 0 h1
      simpa [Function.comp_def, smul_eq_mul] using hc
    rw [hGdef]
    rw [h2.deriv, mul_comm]
  set w : ℂ := (z - c) / (R : ℂ) with hwdef
  have hwlt : ‖w‖ < 1 := by
    rw [hwdef, norm_div, Complex.norm_of_nonneg hR.le, div_lt_one hR]
    linarith
  have hw1 : w ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hwlt
  have hwq : 0 ≤ ‖w‖ := norm_nonneg w
  have hw16 : ‖w‖ ≤ 1 / 6 := by
    rw [hwdef, norm_div, Complex.norm_of_nonneg hR.le, div_le_iff₀ hR]
    linarith
  have hGw : G w = f z := by
    have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    rw [hGdef, hwdef]
    simp only []
    rw [mul_div_cancel₀ (z - c) hRne]
    ring_nf
  have hG0 : G 0 = f c := by
    rw [hGdef]; simp
  have hlog := log_deriv_bound_unit hGan hGinj
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv G ((t : ℂ) * w)‖ ≤ ‖deriv G 0‖ * ((1 + t * ‖w‖) / (1 - t * ‖w‖) ^ 3) := by
    intro t ht
    have htr : ‖((t : ℂ) * w)‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [ht.2, hwq, hw16]
    have hstep := deriv_upper_of_log_deriv_bound hGan hlog htr
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] at hstep
  have hgrowth := growth_of_deriv_bound_alt hw1 hGdiff hderiv
  rw [hGw, hG0, hGd0, norm_mul, Complex.norm_of_nonneg hR.le] at hgrowth
  have hq : ‖w‖ / (1 - ‖w‖) ^ 2 ≤ 1 / 4 := by
    have hpos : 0 < (1 - ‖w‖) ^ 2 := by nlinarith [hwlt]
    rw [div_le_iff₀ hpos]
    nlinarith [hwq, hw16, sq_nonneg (1 / 6 - ‖w‖)]
  calc ‖f z - f c‖ ≤ R * ‖deriv f c‖ * (‖w‖ / (1 - ‖w‖) ^ 2) := hgrowth
    _ ≤ R * ‖deriv f c‖ * (1 / 4) := by
        exact mul_le_mul_of_nonneg_left hq (by positivity)
    _ = ‖deriv f c‖ * (R / 4) := by ring

end Work.Repel
