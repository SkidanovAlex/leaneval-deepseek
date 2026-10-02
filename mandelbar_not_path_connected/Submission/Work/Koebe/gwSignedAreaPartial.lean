import Mathlib
import Submission.Work.Koebe.gwDefs
import Submission.Work.Koebe.signedArea_coeff_bound
import Submission.Work.Koebe.gwTruncUniformOnSphere
import Submission.Work.Koebe.gwFiniteTruncInterior

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Koebe

open Complex Metric MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

/-!
# The signed-area value of the truncations of `F = 1/z + H`
-/


/-! ## Notation -/

/-- Truncated Taylor polynomial of `H` at `0`. -/
noncomputable def tP (H : ℂ → ℂ) (M : ℕ) : ℂ → ℂ :=
  fun z => ∑ n ∈ Finset.range M, gco H n * z ^ n

/-- The truncated Laurent function `z⁻¹ + tP H M`. -/
noncomputable def tF (H : ℂ → ℂ) (M : ℕ) : ℂ → ℂ := fun z => z⁻¹ + tP H M z

/-- The `M`-th partial sum of the signed-area coefficients. -/
noncomputable def aS (H : ℂ → ℂ) (r : ℝ) (M : ℕ) : ℝ :=
  (∑ n ∈ Finset.range M, (n : ℝ) * ‖gco H n‖ ^ 2 * r ^ (2 * n)) - r ^ (-2 : ℤ)

lemma tP_eq_fun (H : ℂ → ℂ) (M : ℕ) :
    tP H M = fun z => ∑ n ∈ Finset.range M, gco H n * z ^ n := rfl

lemma tF_eq_fun (H : ℂ → ℂ) (M : ℕ) :
    tF H M = fun z => z⁻¹ + ∑ n ∈ Finset.range M, gco H n * z ^ n := by
  funext z; rw [tF, tP_eq_fun]

/-! ## Helpers -/

lemma tendstoUniformlyOn_conj {ι α : Type*} {F : ι → α → ℂ} {f : α → ℂ} {p : Filter ι}
    {s : Set α} (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i a => starRingEnd ℂ (F i a)) (fun a => starRingEnd ℂ (f a)) p s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi
  intro a ha
  rw [Complex.dist_conj_conj]
  exact hi a ha

lemma tendstoUniformlyOn_const_index {ι α : Type*} {f : α → ℂ} {p : Filter ι} {s : Set α} :
    TendstoUniformlyOn (fun _ : ι => f) f p s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Eventually.of_forall (fun _ _ _ => by simpa using hε)

lemma TendstoUniformlyOn.mul_of_bdd {ι α : Type*} [PseudoMetricSpace α] {F G : ι → α → ℂ}
    {f g : α → ℂ} {p : Filter ι} {s : Set α}
    (hF : TendstoUniformlyOn F f p s) (hG : TendstoUniformlyOn G g p s)
    (hf : ∃ D : ℝ, ∀ x ∈ s, ‖f x‖ ≤ D) (hg : ∃ D : ℝ, ∀ x ∈ s, ‖g x‖ ≤ D) :
    TendstoUniformlyOn (fun i x => F i x * G i x) (fun x => f x * g x) p s := by
  obtain ⟨Df, hDf⟩ := hf
  obtain ⟨Dg, hDg⟩ := hg
  set Df' : ℝ := max Df 0 with hDf'def
  set Dg' : ℝ := max Dg 0 with hDg'def
  have hDf'0 : 0 ≤ Df' := le_max_right _ _
  have hDg'0 : 0 ≤ Dg' := le_max_right _ _
  have hDf'b : ∀ x ∈ s, ‖f x‖ ≤ Df' := fun x hx => le_trans (hDf x hx) (le_max_left _ _)
  have hDg'b : ∀ x ∈ s, ‖g x‖ ≤ Dg' := fun x hx => le_trans (hDg x hx) (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  filter_upwards [hG (ε / (2 * (Df' + 1))) (by positivity),
    hF (ε / (2 * (Dg' + 1))) (by positivity), hF 1 (by norm_num)] with i hiG hiF hiF1
  intro x hx
  have hiG' : ‖g x - G i x‖ < ε / (2 * (Df' + 1)) := by
    have := hiG x hx; rwa [dist_eq_norm] at this
  have hiF' : ‖f x - F i x‖ < ε / (2 * (Dg' + 1)) := by
    have := hiF x hx; rwa [dist_eq_norm] at this
  have hiF1' : ‖f x - F i x‖ < 1 := by
    have := hiF1 x hx; rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  have hFi : ‖F i x‖ ≤ Df' + 1 := by
    have h1 : ‖F i x - f x‖ = ‖f x - F i x‖ := norm_sub_rev _ _
    calc ‖F i x‖ = ‖(F i x - f x) + f x‖ := by
          rw [show (F i x - f x) + f x = F i x by ring]
      _ ≤ ‖F i x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ = ‖f x - F i x‖ + ‖f x‖ := by rw [h1]
      _ ≤ 1 + Df' := by linarith [hDf'b x hx, hiF1']
      _ = Df' + 1 := by ring
  have ht1 : ‖f x - F i x‖ * ‖g x‖ < ε / 2 := by
    have hpos : (0:ℝ) < Dg' + 1 := by linarith
    calc ‖f x - F i x‖ * ‖g x‖ ≤ ‖f x - F i x‖ * (Dg' + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [hDg'b x hx]) (norm_nonneg _)
      _ < (ε / (2 * (Dg' + 1))) * (Dg' + 1) := mul_lt_mul_of_pos_right hiF' hpos
      _ = ε / 2 := by field_simp
  have ht2 : ‖F i x‖ * ‖g x - G i x‖ < ε / 2 := by
    have hpos : (0:ℝ) < Df' + 1 := by linarith
    calc ‖F i x‖ * ‖g x - G i x‖ ≤ (Df' + 1) * ‖g x - G i x‖ :=
          mul_le_mul_of_nonneg_right hFi (norm_nonneg _)
      _ < (Df' + 1) * (ε / (2 * (Df' + 1))) := mul_lt_mul_of_pos_left hiG' hpos
      _ = ε / 2 := by field_simp
  calc ‖f x * g x - F i x * G i x‖
      = ‖(f x - F i x) * g x + F i x * (g x - G i x)‖ := by
        rw [show f x * g x - F i x * G i x
              = (f x - F i x) * g x + F i x * (g x - G i x) by ring]
    _ ≤ ‖(f x - F i x) * g x‖ + ‖F i x * (g x - G i x)‖ := norm_add_le _ _
    _ = ‖f x - F i x‖ * ‖g x‖ + ‖F i x‖ * ‖g x - G i x‖ := by rw [norm_mul, norm_mul]
    _ < ε := by linarith

lemma deriv_tP (H : ℂ → ℂ) (M : ℕ) :
    deriv (tP H M) = fun z => ∑ n ∈ Finset.range M, (n : ℂ) * gco H n * z ^ (n - 1) := by
  funext z
  rw [show tP H M = ∑ n ∈ Finset.range M, (fun z : ℂ => gco H n * z ^ n) from by
        funext z; simp only [tP_eq_fun, Finset.sum_apply]]
  rw [deriv_sum]
  · apply Finset.sum_congr rfl; intro n hn
    rw [deriv_const_mul]
    · rw [(hasDerivAt_pow n z).deriv]; ring
    · fun_prop
  · intro i hi; fun_prop

lemma deriv_tF (H : ℂ → ℂ) (M : ℕ) {z : ℂ} (hz : z ≠ 0) :
    deriv (tF H M) z = -(z ^ 2)⁻¹ + deriv (tP H M) z := by
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := differentiableAt_inv_iff.mpr hz
  have hd2 : DifferentiableAt ℂ (tP H M) z := by
    rw [tP_eq_fun]; fun_prop
  have hEq : tF H M = (fun z : ℂ => z⁻¹) + tP H M := by
    funext z; rw [tF]; rfl
  rw [hEq, deriv_add hd1 hd2, deriv_inv]

lemma deriv_PH (H : ℂ → ℂ) {z : ℂ} (hdH : DifferentiableAt ℂ H z) (hz : z ≠ 0) :
    deriv (fun w : ℂ => w⁻¹ + H w) z = -(z ^ 2)⁻¹ + deriv H z := by
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) z := differentiableAt_inv_iff.mpr hz
  have hEq : (fun w : ℂ => w⁻¹ + H w) = (fun z : ℂ => z⁻¹) + H := by funext z; rfl
  rw [hEq, deriv_add hd1 hdH, deriv_inv]

private lemma twoI_inv_mul_pi (x : ℝ) :
    (2 * (Complex.I : ℂ))⁻¹ * (2 * (Real.pi : ℂ) * Complex.I * ((x : ℝ) : ℂ))
      = ((Real.pi * x : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul]
  have h2I : (2 * (Complex.I : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((x:ℝ):ℂ))
        = (2 * (Complex.I:ℂ)) * ((Real.pi:ℂ) * x) by ring,
    ← mul_assoc, inv_mul_cancel₀ h2I, one_mul]

/-! ## The main theorem -/

theorem gwSignedAreaPartial (F H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hF : Set.InjOn F (Metric.ball 0 1 \ {0}))
    (hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, F z = 1 / z + H z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    Real.pi * ((∑ n ∈ Finset.range N, (n : ℝ) * ‖Work.Koebe.gco H n‖ ^ 2 * r ^ (2 * n)) - r ^ (-2 : ℤ))
      ≤ (Work.Koebe.sArea F r).re := by
  change Real.pi * aS H r N ≤ (sArea F r).re
  have hs : Metric.sphere (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact ⟨by rw [Metric.mem_ball, dist_zero_right]; linarith,
      by rintro rfl; simp at hz; linarith⟩
  have hznz : ∀ z ∈ Metric.sphere (0 : ℂ) r, z ≠ 0 := fun z hz => (hs hz).2
  have hzball : ∀ z ∈ Metric.sphere (0 : ℂ) r, z ∈ Metric.ball (0 : ℂ) 1 := fun z hz => (hs hz).1
  have hFeq : Set.EqOn F (fun z => z⁻¹ + H z) (Metric.sphere 0 r) := by
    intro z hz
    rw [hexp z (hs hz), one_div]
  have hFdeq : Set.EqOn (deriv F) (deriv (fun z => z⁻¹ + H z)) (Metric.sphere 0 r) := by
    intro z hz
    have hnb : Metric.ball (0 : ℂ) 1 \ {0} ∈ 𝓝 z :=
      (Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds (hs hz)
    have hev : (fun w => F w) =ᶠ[𝓝 z] (fun w => w⁻¹ + H w) :=
      eventually_of_mem hnb (fun w hw => by simp only [hexp w hw, one_div])
    simpa using hev.deriv_eq
  -- Uniform convergence of the truncations.
  obtain ⟨hP, hPd⟩ := gwTruncUniformOnSphere H hH hr hr1
  have hP' : TendstoUniformlyOn (fun M z => tP H M z) H atTop (Metric.sphere 0 r) := by
    simpa only [tP_eq_fun] using hP
  have hPd' : TendstoUniformlyOn (fun M z => deriv (tP H M) z) (deriv H) atTop
      (Metric.sphere 0 r) := by
    simpa only [tP_eq_fun] using hPd
  have hFM_tend : TendstoUniformlyOn (fun M z => tF H M z) F atTop (Metric.sphere 0 r) := by
    have h1 : TendstoUniformlyOn (fun M z => (∑ n ∈ Finset.range M, gco H n * z ^ n) + z⁻¹)
        (fun z => H z + z⁻¹) atTop (Metric.sphere 0 r) :=
      hP.add (tendstoUniformlyOn_const_index (f := fun z : ℂ => z⁻¹))
    have h2 : TendstoUniformlyOn (fun M z => z⁻¹ + ∑ n ∈ Finset.range M, gco H n * z ^ n)
        (fun z => z⁻¹ + H z) atTop (Metric.sphere 0 r) :=
      (h1.congr (Eventually.of_forall fun M => fun z _ => by ring)).congr_right
        (fun z _ => by ring)
    have h3 : TendstoUniformlyOn (fun M z => z⁻¹ + ∑ n ∈ Finset.range M, gco H n * z ^ n)
        F atTop (Metric.sphere 0 r) :=
      h2.congr_right (fun z hz => (hFeq hz).symm)
    simpa only [tF_eq_fun] using h3
  have hFMd_tend : TendstoUniformlyOn (fun M z => deriv (tF H M) z) (deriv F) atTop
      (Metric.sphere 0 r) := by
    have hbase : TendstoUniformlyOn (fun M z => -(z ^ 2)⁻¹ + deriv (tP H M) z)
        (fun z => -(z ^ 2)⁻¹ + deriv H z) atTop (Metric.sphere 0 r) :=
      (tendstoUniformlyOn_const_index (f := fun z : ℂ => -(z ^ 2)⁻¹)).add hPd'
    have hbase' : TendstoUniformlyOn (fun M z => deriv (tF H M) z)
        (fun z => -(z ^ 2)⁻¹ + deriv H z) atTop (Metric.sphere 0 r) :=
      hbase.congr (Eventually.of_forall fun M => fun z hz => (deriv_tF H M (hznz z hz)).symm)
    have hlim : Set.EqOn (fun z => -(z ^ 2)⁻¹ + deriv H z) (deriv F) (Metric.sphere 0 r) := by
      intro z hz
      have hdH : DifferentiableAt ℂ H z := hH.differentiableAt (Metric.isOpen_ball.mem_nhds (hzball z hz))
      exact ((hFdeq hz).trans (deriv_PH H hdH (hznz z hz))).symm
    exact hbase'.congr_right hlim
  -- Continuity of the truncations and their derivatives on the circle.
  have hcontP_all : ∀ M, ContinuousOn (tF H M) (Metric.sphere 0 r) := by
    intro M
    have h1 : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere 0 r) :=
      ContinuousOn.inv₀ continuousOn_id (fun z hz => hznz z hz)
    have h2 : ContinuousOn (fun z => ∑ n ∈ Finset.range M, gco H n * z ^ n) (Metric.sphere 0 r) := by
      refine continuousOn_finsetSum _ (fun n _ => ?_)
      exact continuousOn_const.mul (continuousOn_id.pow n)
    rw [tF_eq_fun]
    exact h1.add h2
  have hcontd_all : ∀ M, ContinuousOn (deriv (tF H M)) (Metric.sphere 0 r) := by
    intro M
    have hEq2 : Set.EqOn (deriv (tF H M)) (fun z => -(z ^ 2)⁻¹ + deriv (tP H M) z)
        (Metric.sphere 0 r) := fun z hz => deriv_tF H M (hznz z hz)
    refine ContinuousOn.congr ?_ hEq2
    have hd1 : ContinuousOn (fun z : ℂ => -(z ^ 2)⁻¹) (Metric.sphere 0 r) := by
      refine ContinuousOn.neg (ContinuousOn.inv₀ ?_ ?_)
      · fun_prop
      · intro z hz; exact pow_ne_zero 2 (hznz z hz)
    have hd2 : ContinuousOn (deriv (tP H M)) (Metric.sphere 0 r) := by
      rw [deriv_tP]
      refine continuousOn_finsetSum _ (fun n _ => ?_)
      exact (continuousOn_const.mul continuousOn_const).mul (continuousOn_id.pow _)
    exact hd1.add hd2
  have hcont : ∀ᶠ M in atTop,
      ContinuousOn (fun z => (starRingEnd ℂ (tF H M z)) * deriv (tF H M) z)
        (Metric.sphere 0 r) :=
    Eventually.of_forall fun M =>
      (Complex.continuous_conj.comp_continuousOn (hcontP_all M)).mul (hcontd_all M)
  -- Bounds on the limit functions.
  have hFcont : ContinuousOn F (Metric.sphere 0 r) :=
    hFM_tend.continuousOn (Eventually.of_forall hcontP_all).frequently
  have hFdcont : ContinuousOn (deriv F) (Metric.sphere 0 r) :=
    hFMd_tend.continuousOn (Eventually.of_forall hcontd_all).frequently
  obtain ⟨DF, hDF⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hFcont
  obtain ⟨DFd, hDFd⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hFdcont
  have hg : TendstoUniformlyOn
      (fun M z => (starRingEnd ℂ (tF H M z)) * deriv (tF H M) z)
      (fun z => (starRingEnd ℂ (F z)) * deriv F z) atTop (Metric.sphere 0 r) :=
    TendstoUniformlyOn.mul_of_bdd (tendstoUniformlyOn_conj hFM_tend) hFMd_tend
      ⟨DF, fun z hz => by rw [Complex.norm_conj]; exact hDF z hz⟩
      ⟨DFd, fun z hz => hDFd z hz⟩
  -- Pass to the limit in the circle integral.
  have hci := hg.tendsto_circleIntegral_of_continuousOn hr.le hcont
  have hconv0 : Tendsto (fun M => sArea (tF H M) r) atTop (𝓝 (sArea F r)) := by
    simpa only [sArea] using hci.const_mul (2 * Complex.I)⁻¹
  have hconv : Tendsto (fun M => (sArea (tF H M) r).re) atTop (𝓝 ((sArea F r).re)) :=
    (Complex.continuous_re.tendsto (sArea F r)).comp hconv0
  -- The exact value of the signed area of each truncation.
  have hfin : ∀ M, (∮ z in C(0, r), (starRingEnd ℂ (tF H M z)) * deriv (tF H M) z)
      = 2 * Real.pi * Complex.I * ((aS H r M : ℝ) : ℂ) := by
    intro M
    simpa only [tF_eq_fun, tP_eq_fun, aS] using gwFiniteTruncInterior (fun n => gco H n) r hr M
  have hval : ∀ M, (sArea (tF H M) r).re = Real.pi * aS H r M := by
    intro M
    have hsq : sArea (tF H M) r = ((Real.pi * aS H r M : ℝ) : ℂ) := by
      rw [sArea, hfin M]
      exact twoI_inv_mul_pi (aS H r M)
    rw [hsq, Complex.ofReal_re]
  -- Monotone growth of the partial sums.
  refine ge_of_tendsto hconv ?_
  rw [eventually_atTop]
  refine ⟨N, fun M hM => ?_⟩
  rw [hval M]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  unfold aS
  have hsum : (∑ n ∈ Finset.range N, (n : ℝ) * ‖gco H n‖ ^ 2 * r ^ (2 * n))
      ≤ (∑ n ∈ Finset.range M, (n : ℝ) * ‖gco H n‖ ^ 2 * r ^ (2 * n)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hM)
      (fun i _ _ => by positivity)
  linarith

end

end Work.Koebe
