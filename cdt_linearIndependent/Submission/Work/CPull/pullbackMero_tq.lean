import Mathlib
import Submission.Work.CPull.defs

/-!
# Area CPull — meromorphic pullback of the tail series `tq k f`

`Work.CPull.pullbackMero_tq`: if the germ at `0` of `z ↦ Σₙ (coeffₙ f) · Ψ(z)ⁿ` is the
holomorphic function `N`, then the pullback of the formal tail series
`tq k f = Σₙ (coeff (n+k) f) Xⁿ` along `Ψ` is meromorphic on the unit disc (with `P = 1`).

The mathematics: writing `c n = coeff n f`,

* the convergence hypothesis at a non-zero point `w₀ = Ψ z₁` forces the power series
  `Σₙ cₙ wⁿ` to have a positive radius of convergence `R ≥ ‖w₀‖`, so its `k`-th tail
  `H w = Σₙ c (n+k) wⁿ` is holomorphic near `0` and `H 0 = c k`
  (`Work.CPull.analyticOn_of_hasSum_at`);
* consequently, for `0 < ‖z‖ < δ` the germ of the pullback is
  `(N z − Σ_{i<k} cᵢ Ψ(z)ⁱ) / Ψ(z)^k = H (Ψ z)`, which is holomorphic on the punctured unit
  disc and has a removable singularity at `0` with value `c k`
  (`Work.CPull.hasSum_tail_eq` for the recombination identity, then Riemann's theorem).
-/

namespace Work.CPull

open Filter Metric
open scoped Topology NNReal ENNReal

/-- **A power series which converges at one non-zero point is holomorphic near `0`.**
If `Σₙ gₙ w₀ⁿ` converges with `w₀ ≠ 0`, then the series defines a holomorphic function `H`
on the disc of radius `‖w₀‖`, the Taylor series there being `Σₙ gₙ wⁿ`; in particular
`H 0 = g 0`. -/
theorem analyticOn_of_hasSum_at {g : ℕ → ℂ} {w₀ S : ℂ} (hw₀ : w₀ ≠ 0)
    (h : HasSum (fun n : ℕ => g n * w₀ ^ n) S) :
    ∃ (H : ℂ → ℂ) (R : ℝ), 0 < R ∧ ‖w₀‖ ≤ R ∧ DifferentiableOn ℂ H (Metric.ball 0 R) ∧
      H 0 = g 0 ∧ ∀ w : ℂ, ‖w‖ < ‖w₀‖ → HasSum (fun n : ℕ => g n * w ^ n) (H w) := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ g with hp
  have hpnorm : ∀ n, ‖p n‖ = ‖g n‖ := fun n => by
    rw [hp]; exact FormalMultilinearSeries.ofScalars_norm ℂ g n
  have htend : Tendsto (fun n => ‖g n * w₀ ^ n‖) atTop (𝓝 0) := by
    simpa using h.summable.tendsto_atTop_zero.norm
  obtain ⟨M, hM⟩ := htend.bddAbove_range
  have hM' : ∀ n, ‖g n‖ * ‖w₀‖ ^ n ≤ M := by
    intro n
    have := hM (Set.mem_range_self n)
    rwa [norm_mul, norm_pow] at this
  have hbound : ∀ n, ‖p n‖ * (‖w₀‖₊ : ℝ) ^ n ≤ M := by
    intro n
    rw [hpnorm n]
    simpa [NNReal.coe_pow, coe_nnnorm] using hM' n
  have hrad : (‖w₀‖₊ : ℝ≥0∞) ≤ p.radius := p.le_radius_of_bound M hbound
  have hradpos : 0 < p.radius :=
    lt_of_lt_of_le (by exact_mod_cast nnnorm_pos.mpr hw₀) hrad
  have hpball : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall hradpos
  have hsubset : Metric.ball (0:ℂ) ‖w₀‖ ⊆ Metric.eball (0:ℂ) p.radius := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr (by exact_mod_cast hz)) hrad
  refine ⟨p.sum, ‖w₀‖, norm_pos_iff.mpr hw₀, le_rfl, hpball.differentiableOn.mono hsubset, ?_, ?_⟩
  · have h0 : HasSum (fun n : ℕ => p n (fun _ => (0:ℂ))) (p.sum 0) := by
      have := hpball.hasSum (y := 0) (by rw [mem_eball_zero_iff]; simpa using hradpos)
      simpa using this
    have hcongr : (fun n : ℕ => p n (fun _ => (0:ℂ))) = fun n => if n = 0 then g 0 else 0 := by
      funext n
      rw [hp, FormalMultilinearSeries.ofScalars_apply_eq]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [hn, zero_pow hn]
    rw [hcongr] at h0
    exact h0.unique (hasSum_ite_eq 0 (g 0))
  · intro w hw
    have hwmem : w ∈ Metric.eball (0:ℂ) p.radius := by
      rw [mem_eball_zero_iff, enorm_eq_nnnorm]
      exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr (by exact_mod_cast hw)) hrad
    have h2 := hpball.hasSum hwmem
    rw [zero_add] at h2
    refine h2.congr_fun (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- **Tail of a converging power series.** If `Σₙ cₙ wⁿ` converges to `S` and `w ≠ 0`, then the
series of the `k`-shifted coefficients converges, with sum the `k`-th tail of `S` divided by
`w^k`. -/
theorem hasSum_tail_eq {c : ℕ → ℂ} {w S : ℂ} (k : ℕ) (hw : w ≠ 0)
    (h : HasSum (fun n : ℕ => c n * w ^ n) S) :
    HasSum (fun n : ℕ => c (n + k) * w ^ n)
      ((S - ∑ i ∈ Finset.range k, c i * w ^ i) / w ^ k) := by
  have hwk : w ^ k ≠ 0 := pow_ne_zero k hw
  have h1 : HasSum (fun n : ℕ => c (n + k) * w ^ (n + k))
      (S - ∑ i ∈ Finset.range k, c i * w ^ i) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => c n * w ^ n) k).mpr (by rw [sub_add_cancel]; exact h)
  rw [div_eq_mul_inv]
  refine (h1.mul_right ((w ^ k)⁻¹)).congr_fun (fun n => ?_)
  rw [pow_add, mul_assoc, mul_assoc, mul_inv_cancel₀ hwk, mul_one]

theorem pullbackMero_tq {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ} (k : ℕ)
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hΨ0 : Ψ 0 = 0)
    (hΨne : ∀ z ∈ Metric.ball (0:ℂ) 1, Ψ z = 0 → z = 0)
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ), HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    Submission.CDTPlan.PullbackMero (Submission.CDTPlan.tq k f) Ψ := by
  classical
  set c : ℕ → ℂ := fun n => ((PowerSeries.coeff n f : ℚ) : ℂ) with hc
  have hgerm' : ∀ᶠ z in nhds (0:ℂ), HasSum (fun n : ℕ => c n * Ψ z ^ n) (N z) := hgerm
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hgerm'
  -- a point `z₁ ≠ 0` inside the neighbourhood of validity, and `w₀ = Ψ z₁ ≠ 0`
  set z₁ : ℂ := (((min ε 1) / 2 : ℝ) : ℂ) with hz₁def
  have hz₁norm : ‖z₁‖ = min ε 1 / 2 := by
    rw [hz₁def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hz₁ε : dist z₁ 0 < ε := by
    rw [dist_zero_right, hz₁norm]
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    linarith
  have hz₁1 : ‖z₁‖ < 1 := by
    rw [hz₁norm]
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    linarith
  have hz₁ne : z₁ ≠ 0 := by
    intro hh
    have h0 : ‖z₁‖ = 0 := by rw [hh]; simp
    rw [hz₁norm] at h0
    have h2 : 0 < min ε 1 := lt_min hεpos one_pos
    linarith
  have hz₁mem : z₁ ∈ Metric.ball (0:ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz₁1
  have hΨz₁ : Ψ z₁ ≠ 0 := fun h => hz₁ne (hΨne z₁ hz₁mem h)
  set w₀ : ℂ := Ψ z₁ with hw₀def
  have hw₀ : w₀ ≠ 0 := hΨz₁
  -- the tail series converges at the non-zero point `w₀`
  have hshift : HasSum (fun n : ℕ => c (n + k) * w₀ ^ n)
      ((N z₁ - ∑ i ∈ Finset.range k, c i * w₀ ^ i) / w₀ ^ k) :=
    hasSum_tail_eq k hw₀ (hε hz₁ε)
  -- hence it is holomorphic near `0`
  obtain ⟨H, R, hRpos, -, hHdiff, hH0, hHsum⟩ :=
    analyticOn_of_hasSum_at (g := fun n : ℕ => c (n + k)) (w₀ := w₀) hw₀ hshift
  have hH0' : H 0 = c k := by simpa using hH0
  have hΨcont : ContinuousAt Ψ 0 := hΨ.continuousOn.continuousAt (Metric.ball_mem_nhds 0 one_pos)
  -- a disc on which `Ψ` takes values in the disc of convergence of `H`
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ z : ℂ, ‖z‖ < δ₀ → ‖Ψ z‖ < ‖w₀‖ / 2 := by
    have hcm := Metric.continuousAt_iff.mp hΨcont (‖w₀‖ / 2) (by positivity)
    obtain ⟨d, hdpos, hd⟩ := hcm
    refine ⟨d, hdpos, fun z hz => ?_⟩
    have h := hd (by simpa [dist_eq_norm] using hz)
    rwa [hΨ0, dist_zero_right] at h
  set δ : ℝ := min δ₀ (min ε 1) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min hεpos one_pos)
  have hδle₀ : δ ≤ δ₀ := min_le_left _ _
  have hδleε : δ ≤ ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδle1 : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hwpos : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  -- the truncated series and the candidate quotient
  set T : ℂ → ℂ := fun w => ∑ i ∈ Finset.range k, c i * w ^ i with hTdef
  set g : ℂ → ℂ := fun z => (N z - T (Ψ z)) / Ψ z ^ k with hgdef
  -- the germ identity on the punctured disc
  have hgerm_eq : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → g z = H (Ψ z) := by
    intro z hz0 hzδ
    have hzε : dist z 0 < ε := by
      rw [dist_zero_right]; exact lt_of_lt_of_le hzδ hδleε
    have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzδ hδle1
    have hzmem : z ∈ Metric.ball (0:ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hz1
    have hzne : Ψ z ≠ 0 := fun hzero => hz0.ne' (by rw [hΨne z hzmem hzero]; simp)
    have hs1 : HasSum (fun n : ℕ => c (n + k) * Ψ z ^ n) (H (Ψ z)) :=
      hHsum (Ψ z) (by have := hδ₀ z (lt_of_lt_of_le hzδ hδle₀); linarith [hwpos])
    have hs2 := hasSum_tail_eq (c := c) k hzne (hε hzε)
    rw [hgdef]
    exact hs2.unique hs1
  -- the removable-singularity extension
  set N' : ℂ → ℂ := Function.update g 0 (c k) with hN'def
  refine ⟨1, N', by simp, ?_, ?_⟩
  · refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (f := N') (s := Metric.ball 0 1) (c := 0) (Metric.ball_mem_nhds 0 one_pos)).mp ⟨?_, ?_⟩
    · -- differentiable on the punctured disc
      have hTdiff : DifferentiableOn ℂ T Set.univ := by
        rw [hTdef]
        refine DifferentiableOn.fun_sum (u := Finset.range k)
          (A := fun i w => c i * w ^ i) (fun i _ => ?_)
        exact (differentiableOn_const (c i)).mul (differentiableOn_id.pow i)
      have hTcomp : DifferentiableOn ℂ (fun z => T (Ψ z)) (Metric.ball (0:ℂ) 1 \ {0}) :=
        hTdiff.comp (hΨ.mono (fun z hz => hz.1)) (fun z _ => trivial)
      have hnum : DifferentiableOn ℂ (fun z => N z - T (Ψ z)) (Metric.ball (0:ℂ) 1 \ {0}) :=
        (hN.mono (fun z hz => hz.1)).sub hTcomp
      have hden : DifferentiableOn ℂ (fun z => Ψ z ^ k) (Metric.ball (0:ℂ) 1 \ {0}) :=
        (hΨ.pow k).mono (fun z hz => hz.1)
      have hgdiff : DifferentiableOn ℂ g (Metric.ball (0:ℂ) 1 \ {0}) := by
        rw [hgdef]
        exact hnum.div hden (fun z hz => pow_ne_zero k (fun h => hz.2 (by simpa using hΨne z hz.1 h)))
      exact hgdiff.congr (fun z hz => by
        rw [hN'def, Function.update_apply, if_neg (fun h => hz.2 (by simpa using h))])
    · -- continuity at `0`
      have hHc : ContinuousAt H (Ψ 0) := by
        rw [hΨ0]; exact hHdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hRpos)
      have hHcont : ContinuousAt (fun z => H (Ψ z)) 0 := hHc.comp hΨcont
      refine hHcont.congr ?_
      refine Filter.Eventually.mono (Metric.ball_mem_nhds 0 hδpos) (fun z hz => ?_)
      have hzδ : ‖z‖ < δ := by simpa using hz
      simp only []
      rcases eq_or_ne z 0 with rfl | hzne
      · simp [hN'def, hΨ0, hH0']
      · rw [hN'def, Function.update_apply, if_neg hzne]
        exact (hgerm_eq z (norm_pos_iff.mpr hzne) hzδ).symm
  · -- the germ of the pullback
    refine Filter.Eventually.mono (Metric.ball_mem_nhds 0 hδpos) (fun z hz => ?_)
    have hzδ : ‖z‖ < δ := by simpa using hz
    have hcoeff : ∀ n : ℕ,
        ((PowerSeries.coeff n (Submission.CDTPlan.tq k f) : ℚ) : ℂ) = c (n + k) := by
      intro n
      rw [Submission.CDTPlan.tq, PowerSeries.coeff_mk, hc]
    rw [show (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDTPlan.tq k f) : ℚ) : ℂ) * Ψ z ^ n)
        = fun n : ℕ => c (n + k) * Ψ z ^ n from funext (fun n => by rw [hcoeff n])]
    rw [show (1 : Polynomial ℂ).eval z = 1 from by simp, div_one]
    rcases eq_or_ne z 0 with rfl | hzne
    · have hfun : (fun n : ℕ => c (n + k) * Ψ 0 ^ n) = fun n : ℕ => if n = 0 then c k else 0 := by
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [hΨ0]
        · simp [hΨ0, hn, zero_pow hn]
      rw [hN'def, Function.update_apply, if_pos rfl, hfun]
      exact hasSum_ite_eq 0 (c k)
    · have hs : HasSum (fun n : ℕ => c (n + k) * Ψ z ^ n) (H (Ψ z)) :=
        hHsum (Ψ z) (by have := hδ₀ z (lt_of_lt_of_le hzδ hδle₀); linarith [hwpos])
      rw [hN'def, Function.update_apply, if_neg hzne, hgerm_eq z (norm_pos_iff.mpr hzne) hzδ]
      exact hs

end Work.CPull
