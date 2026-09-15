import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Complex

open Filter Set Metric
open scoped Topology

/-- For every `n ≥ 2` there is an `n`-th root of unity in `ℂ` which is not `1`. -/
private lemma exists_pow_eq_one_ne_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ ω : ℂ, ω ^ n = 1 ∧ ω ≠ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  set r : ℝ := 2 * Real.pi / n with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrlt : r < 2 * Real.pi := by
    rw [hr, div_lt_iff₀ hn0]; nlinarith [Real.pi_pos]
  refine ⟨Complex.exp ((r : ℂ) * Complex.I), ?_, ?_⟩
  · have hnr : (n : ℂ) * ((r : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I := by
      have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [hr]; push_cast; field_simp
    rw [← Complex.exp_nat_mul ((r : ℂ) * Complex.I) n, hnr]
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) = (2 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by ring
    rw [h2, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    norm_num
  · intro h
    have h1 : ((Circle.exp r : Circle) : ℂ) = 1 := by
      rw [Circle.coe_exp]; simpa using h
    have h2 : ((Circle.exp 0 : Circle) : ℂ) = 1 := by simp [Circle.exp_zero]
    have hcirc : Circle.exp r = Circle.exp 0 := Circle.coe_inj.mp (h1.trans h2.symm)
    have hr0 : r = 0 := by
      have hinj := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
      exact hinj ⟨hrpos.le, hrlt⟩ ⟨le_refl _, Real.two_pi_pos⟩ hcirc
    exact hrpos.ne' hr0

theorem exists_two_preimages_near_of_deriv_eq_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (h1 : deriv f z₀ = 0)
    (hnc : ¬ ∀ᶠ z in nhds z₀, f z = f z₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ, w ≠ f z₀ ∧ ‖w - f z₀‖ < ε ∧
      ∃ a b : ℂ, a ≠ b ∧ ‖a - z₀‖ < ε ∧ ‖b - z₀‖ < ε ∧ f a = w ∧ f b = w := by
  classical
  set F : ℂ → ℂ := fun z => f z - f z₀ with hFdef
  have hF : AnalyticAt ℂ F z₀ := hf.sub analyticAt_const
  have hFz : F z₀ = 0 := by simp [hFdef]
  have hFtop : analyticOrderAt F z₀ ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    apply hnc
    filter_upwards [h] with z hz
    exact sub_eq_zero.mp (by simpa [hFdef] using hz)
  have hFnz : analyticOrderAt F z₀ ≠ 0 := hF.analyticOrderAt_ne_zero.mpr hFz
  set n : ℕ := analyticOrderNatAt F z₀ with hn
  have hncast : (n : ℕ∞) = analyticOrderAt F z₀ := by
    rw [hn]; exact Nat.cast_analyticOrderNatAt hFtop
  have hn_ne_zero : n ≠ 0 := by
    intro h0
    apply hFnz
    rw [← hncast, h0]; simp
  have hn2 : 2 ≤ n := by
    have hderivF : deriv F z₀ = 0 := by
      have h' : deriv F z₀ = deriv f z₀ := by rw [hFdef]; exact deriv_sub_const (f z₀)
      rw [h', h1]
    have hli : (1 : ℕ∞) ≤ analyticOrderAt (deriv F) z₀ := by
      rw [Order.one_le_iff_ne_zero]
      exact (hF.deriv.analyticOrderAt_ne_zero).mpr hderivF
    have h2' : (((1 : ℕ) : ℕ∞) + 1) ≤ analyticOrderAt F z₀ :=
      (analyticOrderAt_deriv_ge_iff hF hFz).mp hli
    have h3' : (2 : ℕ∞) ≤ analyticOrderAt F z₀ := by norm_num at h2' ⊢; exact h2'
    rw [← hncast] at h3'
    exact Nat.cast_le.mp h3'
  obtain ⟨ψ, hψan, hψne, hψeq⟩ := (hF.analyticOrderNatAt_eq_iff hFtop).mp hn.symm
  set u : ℂ → ℂ := fun z => (ψ z - ψ z₀) / ψ z₀ with hu_def
  set ψ' : ℂ → ℂ := fun z => (1 + u z) ^ ((n : ℂ)⁻¹) with hψ'_def
  set Q : ℂ → ℂ := fun z => (z - z₀) * ψ' z with hQ_def
  have hu0 : u z₀ = 0 := by rw [hu_def]; simp
  have hψ'an : AnalyticAt ℂ ψ' z₀ := by
    rw [hψ'_def]
    refine AnalyticAt.cpow (f := fun z => 1 + u z) (g := fun _ => (n : ℂ)⁻¹) ?_ ?_ ?_
    · exact analyticAt_const.add ((hψan.sub analyticAt_const).div_const)
    · exact analyticAt_const
    · rw [hu0]; simp
  have hψ'z : ψ' z₀ = 1 := by simp only [hψ'_def, hu0, add_zero, Complex.one_cpow]
  have hQan : AnalyticAt ℂ Q z₀ := by
    rw [hQ_def]
    exact (analyticAt_id.sub analyticAt_const).mul hψ'an
  have hQz : Q z₀ = 0 := by rw [hQ_def]; simp
  have hQderiv : deriv Q z₀ = 1 := by
    have hd1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).sub_const z₀
    have hd2 : HasDerivAt ψ' (deriv ψ' z₀) z₀ := hψ'an.differentiableAt.hasDerivAt
    have hmul : HasDerivAt (fun z : ℂ => (z - z₀) * ψ' z)
        (1 * ψ' z₀ + (z₀ - z₀) * deriv ψ' z₀) z₀ := hd1.mul hd2
    have hval : (1 * ψ' z₀ + (z₀ - z₀) * deriv ψ' z₀) = 1 := by rw [hψ'z]; ring
    rw [hQ_def]
    exact hmul.deriv.trans hval
  have hQpow : ∀ z, Q z ^ n = (z - z₀) ^ n * ψ z / ψ z₀ := by
    intro z
    have hbase : ((1 + u z) ^ ((n : ℂ)⁻¹)) ^ n = 1 + u z := by
      rw [← Complex.cpow_nat_mul (1 + u z) n ((n : ℂ)⁻¹)]
      have : (n : ℂ) * (n : ℂ)⁻¹ = 1 := by
        rw [mul_inv_cancel₀]; exact_mod_cast hn_ne_zero
      rw [this, Complex.cpow_one]
    have hQz' : Q z = (z - z₀) * ((1 + u z) ^ ((n : ℂ)⁻¹)) := by
      simp only [hQ_def, hψ'_def]
    rw [hQz', mul_pow, hbase, hu_def]
    field_simp
    ring
  have hFeq : F =ᶠ[𝓝 z₀] fun z => ψ z₀ * Q z ^ n := by
    filter_upwards [hψeq] with z hz
    rw [hz, hQpow z, smul_eq_mul]
    field_simp
  obtain ⟨δ, hδpos, hδball⟩ : ∃ δ > 0, ∀ z, ‖z - z₀‖ < δ → F z = ψ z₀ * Q z ^ n := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hFeq
    exact ⟨δ, hδpos, fun z hz => hδ (by simpa [dist_eq_norm] using hz)⟩
  have hQstrict : HasStrictDerivAt Q (deriv Q z₀) z₀ := hQan.hasStrictDerivAt
  have hQd : deriv Q z₀ ≠ 0 := by rw [hQderiv]; norm_num
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv Q z₀) hQd)
  have hinv : HasStrictFDerivAt Q (e : ℂ →L[ℂ] ℂ) z₀ := hQstrict.hasStrictFDerivAt_equiv hQd
  let r : ℂ → ℂ := HasStrictFDerivAt.localInverse Q e z₀ hinv
  have hrtend : Tendsto r (𝓝 (0 : ℂ)) (𝓝 z₀) := by
    have h' : Tendsto r (𝓝 (Q z₀)) (𝓝 z₀) := hinv.localInverse_tendsto
    rwa [hQz] at h'
  have hrinv : ∀ᶠ y in 𝓝 (0 : ℂ), Q (r y) = y := by
    have h' : ∀ᶠ y in 𝓝 (Q z₀), Q (r y) = y := hinv.eventually_right_inverse
    rwa [hQz] at h'
  obtain ⟨ω, hω1, hωne⟩ := exists_pow_eq_one_ne_one n hn2
  have hcomb : ∀ᶠ s in 𝓝 (0 : ℂ),
      Q (r s) = s ∧ Q (r (ω * s)) = ω * s ∧
      ‖r s - z₀‖ < min δ ε ∧ ‖r (ω * s) - z₀‖ < min δ ε ∧
      ‖ψ z₀ * s ^ n‖ < ε := by
    have hmin : (0 : ℝ) < min δ ε := lt_min hδpos hε
    have h2' : ∀ᶠ s in 𝓝 (0 : ℂ), Q (r (ω * s)) = ω * s := by
      have ht : Tendsto (fun s : ℂ => ω * s) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hc : Continuous fun s : ℂ => ω * s := by fun_prop
        simpa using hc.tendsto (0 : ℂ)
      exact ht.eventually hrinv
    have h3' : ∀ᶠ s in 𝓝 (0 : ℂ), ‖r s - z₀‖ < min δ ε := by
      have h' := hrtend.eventually (Metric.ball_mem_nhds z₀ hmin)
      simpa [Metric.mem_ball, dist_eq_norm] using h'
    have h4' : ∀ᶠ s in 𝓝 (0 : ℂ), ‖r (ω * s) - z₀‖ < min δ ε := by
      have ht : Tendsto (fun s : ℂ => ω * s) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hc : Continuous fun s : ℂ => ω * s := by fun_prop
        simpa using hc.tendsto (0 : ℂ)
      exact ht.eventually h3'
    have h5' : ∀ᶠ s in 𝓝 (0 : ℂ), ‖ψ z₀ * s ^ n‖ < ε := by
      have ht : Tendsto (fun s : ℂ => ψ z₀ * s ^ n) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hc : Continuous fun s : ℂ => ψ z₀ * s ^ n := by fun_prop
        simpa [zero_pow (by omega : n ≠ 0)] using hc.tendsto (0 : ℂ)
      have h' := ht.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)
      simpa [Metric.mem_ball, dist_eq_norm] using h'
    filter_upwards [hrinv, h2', h3', h4', h5'] with s hs1 hs2 hs3 hs4 hs5
    exact ⟨hs1, hs2, hs3, hs4, hs5⟩
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hcomb
  set s : ℂ := ((η / 2 : ℝ) : ℂ) with hs
  have hsne : s ≠ 0 := by rw [hs]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hsd : dist s 0 < η := by
    rw [hs, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0:ℝ) < η / 2)]
    linarith
  obtain ⟨hQs, hQws, hrs, hrws, h5s⟩ := hη hsd
  have hFa : f (r s) - f z₀ = ψ z₀ * s ^ n := by
    have h' := hδball (r s) (lt_of_lt_of_le hrs (min_le_left _ _))
    rw [hFdef, hQs] at h'
    exact h'
  have hFb : f (r (ω * s)) - f z₀ = ψ z₀ * s ^ n := by
    have h' := hδball (r (ω * s)) (lt_of_lt_of_le hrws (min_le_left _ _))
    rw [hFdef, hQws, mul_pow, hω1, one_mul] at h'
    exact h'
  refine ⟨f (r s), ?_, ?_, r s, r (ω * s), ?_, ?_, ?_, rfl, ?_⟩
  · rw [← sub_ne_zero, hFa]
    exact mul_ne_zero hψne (pow_ne_zero n hsne)
  · rw [hFa]; exact h5s
  · intro hab
    have hseq : s = ω * s := by
      calc s = Q (r s) := hQs.symm
        _ = Q (r (ω * s)) := by rw [hab]
        _ = ω * s := hQws
    have hsub : s - ω * s = 0 := sub_eq_zero.mpr hseq
    have hprod : s * (1 - ω) = 0 := by
      rw [mul_sub, mul_one, mul_comm s ω]; exact hsub
    rcases mul_eq_zero.mp hprod with h | h
    · exact hsne h
    · exact (sub_ne_zero.mpr (Ne.symm hωne)) h
  · exact lt_of_lt_of_le hrs (min_le_right _ _)
  · exact lt_of_lt_of_le hrws (min_le_right _ _)
  · have h' : f (r s) - f z₀ = f (r (ω * s)) - f z₀ := hFa.trans hFb.symm
    have := congrArg (fun x : ℂ => x + f z₀) h'
    simp only [sub_add_cancel] at this
    exact this.symm

end Commons.Analysis.Complex