import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

/-- If `0 < s ≤ t ≤ 1` then `t ^ (-e)` is bounded below by `min (s ^ (-e)) 1`,
for every real exponent `e`. -/
theorem rpow_neg_ge_min {t s e : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    min (s ^ (-e)) 1 ≤ t ^ (-e) := by
  rcases le_or_gt 0 e with he | he
  · have ht0 : 0 < t := lt_of_lt_of_le hs hst
    have hte1 : t ^ e ≤ 1 := Real.rpow_le_one (le_of_lt ht0) ht he
    have htpos : 0 < t ^ e := Real.rpow_pos_of_pos ht0 e
    have h1 : (1 : ℝ) ≤ t ^ (-e) := by
      rw [Real.rpow_neg (le_of_lt ht0) e, one_le_inv₀ htpos]
      exact hte1
    exact le_trans (min_le_right _ _) h1
  · have he' : 0 ≤ -e := by linarith
    have h : s ^ (-e) ≤ t ^ (-e) := Real.rpow_le_rpow (le_of_lt hs) hst he'
    exact le_trans (min_le_left _ _) h

theorem theta_integral_lower (g : ℝ → ℝ → ℝ) (e θ₀ : ℝ) (hθ₀ : θ₀ ∈ Work.Spaces.Iθ)
    (hcont : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (0, θ₀)) (hne : g 0 θ₀ ≠ 0)
    (hint : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) Work.Spaces.Iθ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ Set.Ioo 0 ε,
      c ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := by
  -- ## Step 1: the level `c₀ = |g 0 θ₀| / 2` and a box on which `|g| ≥ c₀`.
  set c₀ : ℝ := |g 0 θ₀| / 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    have h : 0 < |g 0 θ₀| := abs_pos.mpr hne
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont c₀ hc₀pos
  have hθ₀Icc : θ₀ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    simpa only [Work.Spaces.Iθ] using hθ₀
  -- ## Step 2: an interior point `θ₁` close to `θ₀`.
  have hcl : θ₀ ∈ closure (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [closure_Ioo (a := (0 : ℝ)) (b := Real.pi / 2) (by linarith [Real.pi_pos])]
    exact hθ₀Icc
  obtain ⟨θ₁, hθ₁Ioo, hθ₁dist₀⟩ := Metric.mem_closure_iff.mp hcl (δ / 4) (by linarith)
  have hθ₁dist : dist θ₁ θ₀ < δ / 4 := by rwa [dist_comm] at hθ₁dist₀
  have hθ₁abs : |θ₁ - θ₀| < δ / 4 := by rwa [Real.dist_eq] at hθ₁dist
  have hθ₁pos : 0 < θ₁ := hθ₁Ioo.1
  have hθ₁lt : θ₁ < Real.pi / 2 := hθ₁Ioo.2
  have hspos : 0 < Real.sin (2 * θ₁) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- ## Step 3: a radius `γ` around `θ₁` on which `sin (2θ) ≥ sin (2θ₁)/2`.
  obtain ⟨γ, hγpos, hγ⟩ := Metric.continuousAt_iff.mp
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt)
    (Real.sin (2 * θ₁) / 2) (by linarith)
  have hγ'' : ∀ x : ℝ, dist x θ₁ < γ →
      dist ((fun σ : ℝ => Real.sin (2 * σ)) x) ((fun σ : ℝ => Real.sin (2 * σ)) θ₁)
        < Real.sin (2 * θ₁) / 2 := fun x hx => hγ (x := x) hx
  have hγ' : ∀ θ : ℝ, dist θ θ₁ < γ → Real.sin (2 * θ₁) / 2 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have h2 : dist (Real.sin (2 * θ)) (Real.sin (2 * θ₁)) < Real.sin (2 * θ₁) / 2 :=
      hγ'' θ hθ
    rw [Real.dist_eq] at h2
    have h3 := (abs_lt.mp h2).1
    linarith
  -- ## Step 4: the sub-interval `K = [θ₁ - rad, θ₁ + rad]`.
  set rad : ℝ := min (δ / 4) (min (γ / 2) (min (θ₁ / 2) ((Real.pi / 2 - θ₁) / 2))) with hrad
  have hradpos : 0 < rad := by
    rw [hrad]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hradδ : rad ≤ δ / 4 := by rw [hrad]; exact min_le_left _ _
  have hradγ : rad ≤ γ / 2 := by
    rw [hrad]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hradθ : rad ≤ θ₁ / 2 := by
    rw [hrad]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hradπ : rad ≤ (Real.pi / 2 - θ₁) / 2 := by
    rw [hrad]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hKsub : Set.Icc (θ₁ - rad) (θ₁ + rad) ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hθ.1, hradθ, hθ₁pos], by linarith [hθ.2, hradπ, hθ₁lt]⟩
  have hKmem : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad), |θ - θ₁| ≤ rad := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hsin_lb : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad),
      Real.sin (2 * θ₁) / 2 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    refine hγ' θ ?_
    rw [Real.dist_eq]
    have h1 : |θ - θ₁| ≤ rad := hKmem θ hθ
    have h2 : rad < γ := by linarith [hradγ, hγpos]
    linarith
  have hsin_gt : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad), 0 < Real.sin (2 * θ) :=
    fun θ hθ => lt_of_lt_of_le (by linarith [hspos]) (hsin_lb θ hθ)
  have hsin_le1 : ∀ θ : ℝ, Real.sin (2 * θ) ≤ 1 := fun θ => Real.sin_le_one (2 * θ)
  -- ## Step 5: `|g| ≥ c₀` on the box `|z| < δ`, `|θ - θ₀| < δ`.
  have hglb : ∀ (z θ : ℝ), |z| < δ → |θ - θ₀| < δ → c₀ ^ 2 ≤ (g z θ) ^ 2 := by
    intro z θ hz hθ
    have hdist : dist ((z, θ) : ℝ × ℝ) (0, θ₀) < δ := by
      have h1 : dist z 0 < δ := by rwa [Real.dist_eq, sub_zero]
      have h2 : dist θ θ₀ < δ := by rwa [Real.dist_eq]
      rw [Prod.dist_eq]
      exact max_lt h1 h2
    have hraw := hδ hdist
    rw [Real.dist_eq] at hraw
    have hlt : |g z θ - g 0 θ₀| < c₀ := hraw
    have htri : |g 0 θ₀| ≤ |g 0 θ₀ - g z θ| + |g z θ| := by
      calc |g 0 θ₀| = |(g 0 θ₀ - g z θ) + g z θ| := by
            rw [show (g 0 θ₀ - g z θ) + g z θ = g 0 θ₀ by ring]
        _ ≤ |g 0 θ₀ - g z θ| + |g z θ| := abs_add_le _ _
    have h2c₀ : |g 0 θ₀| = 2 * c₀ := by rw [hc₀]; ring
    have habs : |g 0 θ₀ - g z θ| = |g z θ - g 0 θ₀| := abs_sub_comm _ _
    have hlt2 : |g 0 θ₀| < c₀ + |g z θ| := by
      have h' : |g 0 θ₀ - g z θ| + |g z θ| < c₀ + |g z θ| := by
        rw [habs]; linarith
      linarith [htri]
    have hcle : c₀ < |g z θ| := by
      rw [h2c₀] at hlt2
      linarith
    have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ c₀ by linarith) (le_of_lt hcle) 2
    rwa [sq_abs] at hpow
  -- ## Step 6: the pointwise lower bound on `K`.
  set b₀ : ℝ := min ((Real.sin (2 * θ₁) / 2) ^ (-e)) 1 with hb₀
  have hb₀pos : 0 < b₀ := by
    rw [hb₀]
    exact lt_min (Real.rpow_pos_of_pos (show (0 : ℝ) < Real.sin (2 * θ₁) / 2 by linarith) _)
      one_pos
  have hptwise : ∀ (z θ : ℝ), |z| < δ → |θ - θ₀| < δ →
      θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad) →
      c₀ ^ 2 * b₀ ≤ (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := by
    intro z θ hz hθ hθK
    have h1 : c₀ ^ 2 ≤ (g z θ) ^ 2 := hglb z θ hz hθ
    have h2 : b₀ ≤ (Real.sin (2 * θ)) ^ (-e) := by
      rw [hb₀]
      exact rpow_neg_ge_min (s := Real.sin (2 * θ₁) / 2) (t := Real.sin (2 * θ)) (e := e)
        (by linarith) (hsin_lb θ hθK) (hsin_le1 θ)
    exact mul_le_mul h1 h2 (le_of_lt hb₀pos) (le_trans (sq_nonneg _) h1)
  -- ## Step 7: assemble.
  refine ⟨δ / 2, by linarith, c₀ ^ 2 * b₀ * (2 * rad), ?_, ?_⟩
  · exact mul_pos (mul_pos (pow_pos hc₀pos 2) hb₀pos) (by linarith)
  · intro z hz
    have hz0 : 0 < z := hz.1
    have hzabs : |z| < δ := by
      rw [abs_of_pos hz0]
      linarith [hz.2]
    have hIntθ : MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)) Work.Spaces.Iθ := hint z hz0
    have hIntK : MeasureTheory.IntegrableOn
        (fun θ => (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e))
        (Set.Icc (θ₁ - rad) (θ₁ + rad)) := hIntθ.mono_set hKsub
    have hθδ : ∀ θ ∈ Set.Icc (θ₁ - rad) (θ₁ + rad), |θ - θ₀| < δ := by
      intro θ hθK
      have h1 : |θ - θ₁| ≤ rad := hKmem θ hθK
      have h3 : |θ - θ₀| ≤ |θ - θ₁| + |θ₁ - θ₀| := by
        have h4 := abs_add_le (θ - θ₁) (θ₁ - θ₀)
        rwa [show (θ - θ₁) + (θ₁ - θ₀) = θ - θ₀ by ring] at h4
      linarith [h3, h1, hθ₁abs, hradδ, hδpos]
    have hstep1 : ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad), (c₀ ^ 2 * b₀)
        ≤ ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad),
            (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) :=
      MeasureTheory.setIntegral_mono_of_nonneg
        (fun θ _ => le_of_lt (mul_pos (pow_pos hc₀pos 2) hb₀pos))
        (fun θ hθK => hptwise z θ hzabs (hθδ θ hθK) hθK) hIntK
    have hval : ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad), (c₀ ^ 2 * b₀)
        = c₀ ^ 2 * b₀ * (2 * rad) := by
      rw [MeasureTheory.setIntegral_const (c₀ ^ 2 * b₀),
        MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [hradpos]), smul_eq_mul]
      ring
    have hstep2 : ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad),
          (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e)
        ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) :=
      MeasureTheory.setIntegral_mono_set hIntθ
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)))
        (Filter.Eventually.of_forall fun θ hθ => hKsub hθ)
    calc c₀ ^ 2 * b₀ * (2 * rad)
        = ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad), (c₀ ^ 2 * b₀) := hval.symm
      _ ≤ ∫ θ in Set.Icc (θ₁ - rad) (θ₁ + rad),
            (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := hstep1
      _ ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-e) := hstep2

end Work.FTS.EllipticEst.remov
