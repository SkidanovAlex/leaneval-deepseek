import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherFar

open Filter Function Set
open scoped Topology ComplexConjugate

set_option autoImplicit false

noncomputable section

/-! ## Growth of the `p_c`-orbit of the critical value, for `‖c‖ ≥ 8`

Everything in this file is uniform on the *closed* region `{c | 8 ≤ ‖c‖}`.  The only
new input compared with the pointwise asymptotics already in the workspace
(`Work.Bottcher.Critical.Phi_isBigO_atTop`) is that the bounds may be taken uniform on that
region, and that each term `c ↦ bottcherTerm c n c` is continuous there. -/

/-! ### The first iterate of the critical value is large -/

private lemma half_norm_pow_four_le_norm_pMap_self (c : ℂ) (hc : 8 ≤ ‖c‖) :
    (1 / 2) * ‖c‖ ^ 4 ≤ ‖Work.Bottcher.pMap c c‖ := by
  have ht : (0 : ℝ) ≤ ‖c‖ := by linarith
  have h1 : ‖c‖ ^ 2 - ‖c‖ ≤ ‖c ^ 2 + conj c‖ := by
    have := norm_sub_norm_le (c ^ 2) (-(conj c))
    rw [sub_neg_eq_add, norm_neg, norm_pow, Complex.norm_conj] at this
    exact this
  have h2 : (7 / 8 : ℝ) * ‖c‖ ^ 2 ≤ ‖c ^ 2 + conj c‖ := by nlinarith
  have h3 : ((7 / 8 : ℝ) * ‖c‖ ^ 2) ^ 2 ≤ ‖(c ^ 2 + conj c) ^ 2‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h4 : ((7 / 8 : ℝ) * ‖c‖ ^ 2) ^ 2 = (49 / 64 : ℝ) * ‖c‖ ^ 4 := by ring
  rw [h4] at h3
  have h5 : (49 / 64 : ℝ) * ‖c‖ ^ 4 - ‖c‖ ≤ ‖(c ^ 2 + conj c) ^ 2 + c‖ := by
    have := norm_sub_norm_le ((c ^ 2 + conj c) ^ 2) (-c)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hexp : ‖Work.Bottcher.pMap c c‖ = ‖(c ^ 2 + conj c) ^ 2 + c‖ := by
    rw [Work.Bottcher.pMap_apply]
  rw [hexp]
  have h6 : ‖c‖ ≤ ‖c‖ ^ 4 / 512 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 512)]
    nlinarith [hc, ht, sq_nonneg ‖c‖, sq_nonneg (‖c‖ - 8)]
  linarith

/-- The critical value `c` lands beyond the uniform radius `normRadius c` after one step. -/
private lemma normRadius_le_norm_pMap_self (c : ℂ) (hc : 8 ≤ ‖c‖) :
    Work.Bottcher.Core.normRadius c ≤ ‖Work.Bottcher.pMap c c‖ := by
  have h := half_norm_pow_four_le_norm_pMap_self c hc
  have ht : (8 : ℝ) ≤ ‖c‖ := hc
  have ht0 : (0 : ℝ) < ‖c‖ := by linarith
  have h2 : (2 : ℝ) ≤ (1 / 2) * ‖c‖ ^ 4 := by
    nlinarith [ht, sq_nonneg ‖c‖, sq_nonneg (‖c‖ - 8), sq_nonneg (‖c‖ ^ 2 - 8 * ‖c‖)]
  have h8 : 8 * ‖c‖ + 1 ≤ (1 / 2) * ‖c‖ ^ 4 := by
    nlinarith [ht, sq_nonneg ‖c‖, sq_nonneg (‖c‖ - 8), sq_nonneg (‖c‖ ^ 2 - 8 * ‖c‖)]
  have hq : ‖c‖ ^ 2 + ‖c‖ + 2 ≤ (1 / 2) * ‖c‖ ^ 4 := by
    nlinarith [ht, sq_nonneg ‖c‖, sq_nonneg (‖c‖ - 8), sq_nonneg (‖c‖ ^ 2 - 8 * ‖c‖)]
  have hm : 2 * (‖c‖ ^ 2 + 3 * ‖c‖) + 1 ≤ (1 / 2) * ‖c‖ ^ 4 := by
    nlinarith [ht, sq_nonneg ‖c‖, sq_nonneg (‖c‖ - 8), sq_nonneg (‖c‖ ^ 2 - 8 * ‖c‖)]
  unfold Work.Bottcher.Core.normRadius
  apply max_le
  · linarith
  · apply max_le
    · linarith
    · apply max_le
      · linarith
      · linarith

/-- Every later iterate stays beyond `normRadius c`. -/
private lemma half_norm_pow_four_le_norm_iterate_succ (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) :
    (1 / 2) * ‖c‖ ^ 4 ≤ ‖(Work.Bottcher.pMap c)^[n + 1] c‖ := by
  have hbase : Work.Bottcher.Core.normRadius c ≤ ‖Work.Bottcher.pMap c c‖ :=
    normRadius_le_norm_pMap_self c hc
  have hiter :=
    Work.Bottcher.Core.norm_iterate_pMap_ge_normRadius c (Work.Bottcher.pMap c c) hbase n
  have heq : (Work.Bottcher.pMap c)^[n] (Work.Bottcher.pMap c c)
      = (Work.Bottcher.pMap c)^[n + 1] c := by
    rw [Function.iterate_succ_apply]
  rw [heq] at hiter
  have hb := half_norm_pow_four_le_norm_pMap_self c hc
  linarith [hiter.2, hb]

/-- The whole orbit of the critical value stays outside the disc of radius `8`. -/
private lemma eight_le_norm_iterate_self (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) :
    (8 : ℝ) ≤ ‖(Work.Bottcher.pMap c)^[n] c‖ := by
  rcases n with _ | n
  · simpa using hc
  · have hzn := half_norm_pow_four_le_norm_iterate_succ c hc n
    have hpow : (8 : ℝ) ^ 4 ≤ ‖c‖ ^ 4 := pow_le_pow_left₀ (by norm_num) hc 4
    nlinarith [hzn, hpow]

/-! ### The normalised Böttcher factor is uniformly within `1/2` of `1` -/

private lemma normFactor_sub_one_le_half_self (c : ℂ) (hc : 8 ≤ ‖c‖) :
    ‖Work.Bottcher.normFactor c c - 1‖ ≤ 1 / 2 := by
  have ht0 : (0 : ℝ) < ‖c‖ := by linarith
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at ht0
    exact lt_irrefl _ ht0
  have hrew : Work.Bottcher.normFactor c c - 1
      = 2 * conj c / c ^ 2 + ((conj c) ^ 2 + c) / c ^ 4 := by
    rw [Work.Bottcher.normFactor, Work.Bottcher.pMap_apply]
    field_simp
    ring
  rw [hrew]
  have h1 : ‖2 * conj c / c ^ 2‖ = 2 / ‖c‖ := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_ofNat]
    field_simp
  have h2 : ‖((conj c) ^ 2 + c) / c ^ 4‖ ≤ (‖c‖ ^ 2 + ‖c‖) / ‖c‖ ^ 4 := by
    rw [norm_div, norm_pow]
    gcongr
    calc ‖(conj c) ^ 2 + c‖ ≤ ‖(conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
      _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
  have h3 : 2 / ‖c‖ + (‖c‖ ^ 2 + ‖c‖) / ‖c‖ ^ 4 ≤ 1 / 2 := by
    have h4 : (‖c‖ ^ 2 + ‖c‖) / ‖c‖ ^ 4 = 1 / ‖c‖ ^ 2 + 1 / ‖c‖ ^ 3 := by field_simp
    rw [h4]
    have ha : 2 / ‖c‖ ≤ 1 / 4 := by rw [div_le_iff₀ ht0]; linarith
    have hb : 1 / ‖c‖ ^ 2 ≤ 1 / 64 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    have hd : 1 / ‖c‖ ^ 3 ≤ 1 / 512 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖c‖, sq_nonneg (‖c‖ - 8)]
    linarith
  calc ‖2 * conj c / c ^ 2 + ((conj c) ^ 2 + c) / c ^ 4‖
      ≤ ‖2 * conj c / c ^ 2‖ + ‖((conj c) ^ 2 + c) / c ^ 4‖ := norm_add_le _ _
    _ ≤ 2 / ‖c‖ + (‖c‖ ^ 2 + ‖c‖) / ‖c‖ ^ 4 := by rw [h1]; linarith
    _ ≤ 1 / 2 := h3

private lemma normFactor_sub_one_le_half_succ (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) :
    ‖Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n + 1] c) - 1‖ ≤ 1 / 2 := by
  have ht0 : (0 : ℝ) < ‖c‖ := by linarith
  have hzn : (1 / 2) * ‖c‖ ^ 4 ≤ ‖(Work.Bottcher.pMap c)^[n + 1] c‖ :=
    half_norm_pow_four_le_norm_iterate_succ c hc n
  have h1 : (1 : ℝ) ≤ ‖(Work.Bottcher.pMap c)^[n + 1] c‖ := by
    have hpow : (8 : ℝ) ^ 4 ≤ ‖c‖ ^ 4 := pow_le_pow_left₀ (by norm_num) hc 4
    nlinarith [hzn, hpow]
  have hb := Work.Bottcher.Core.norm_normFactor_sub_one_le_of_one_le c
    ((Work.Bottcher.pMap c)^[n + 1] c) h1
  refine le_trans hb ?_
  have hzn' : ‖c‖ ^ 4 / 2 ≤ ‖(Work.Bottcher.pMap c)^[n + 1] c‖ := by linarith [hzn]
  have hz2 : ‖c‖ ^ 8 / 4 ≤ ‖(Work.Bottcher.pMap c)^[n + 1] c‖ ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ‖c‖ ^ 4 / 2) hzn' 2
    rw [div_pow] at h
    have e : (‖c‖ ^ 4) ^ 2 = ‖c‖ ^ 8 := by ring
    linarith [h, e]
  have h8 : 8 * (‖c‖ ^ 2 + 3 * ‖c‖) ≤ ‖c‖ ^ 8 := by
    nlinarith [sq_nonneg (‖c‖ ^ 4), sq_nonneg (‖c‖ ^ 4 - 8 ^ 4),
      mul_nonneg (by linarith : (0 : ℝ) ≤ ‖c‖) (sq_nonneg (‖c‖ ^ 2 - 8 * ‖c‖))]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hz2, h8]

private lemma normFactor_sub_one_le_half (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) :
    ‖Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c) - 1‖ ≤ 1 / 2 := by
  rcases n with _ | n
  · exact normFactor_sub_one_le_half_self c hc
  · exact normFactor_sub_one_le_half_succ c hc n

/-- Uniform bound for the individual logarithmic factors along the critical orbit. -/
private lemma log_normFactor_le_one (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) :
    ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))‖ ≤ 1 := by
  have h1 := normFactor_sub_one_le_half c hc n
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c) - 1) h1
  have hsum : (1 : ℂ) + (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c) - 1)
      = Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c) := by ring
  rw [hsum] at hlog
  linarith

/-! ### Uniform majorant for the terms of the Böttcher series -/

private lemma summable_quarter_pow_succ : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
  have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [pow_succ] using h0.mul_right (1 / 4 : ℝ)

private lemma norm_bottcherTerm_self_le (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) :
    ‖Work.Bottcher.bottcherTerm c n c‖ ≤ (1 / 4 : ℝ) ^ (n + 1) := by
  have h := log_normFactor_le_one c hc n
  have hnn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (n + 1) := by positivity
  have hone : ‖Work.Bottcher.bottcherTerm c n c‖
      = (1 / 4 : ℝ) ^ (n + 1)
        * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))‖ := by
    rw [Work.Bottcher.bottcherTerm, norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  rw [hone]
  calc (1 / 4 : ℝ) ^ (n + 1)
        * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))‖
      ≤ (1 / 4 : ℝ) ^ (n + 1) * 1 := mul_le_mul_of_nonneg_left h hnn
    _ = (1 / 4 : ℝ) ^ (n + 1) := mul_one _

/-! ### Continuity of each term -/

private lemma continuous_iterate_self (n : ℕ) :
    Continuous (fun c : ℂ => (Work.Bottcher.pMap c)^[n] c) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
      have hfun : (fun c : ℂ => (Work.Bottcher.pMap c)^[n + 1] c)
          = (fun c : ℂ => (((Work.Bottcher.pMap c)^[n] c) ^ 2 + conj c) ^ 2 + c) := by
        funext c
        rw [Function.iterate_succ_apply', Work.Bottcher.pMap_apply]
      rw [hfun]
      exact (((ih.pow 2).add Complex.continuous_conj).pow 2).add continuous_id

private lemma continuousOn_bottcherTerm (n : ℕ) :
    ContinuousOn (fun c : ℂ => Work.Bottcher.bottcherTerm c n c) {c : ℂ | 8 ≤ ‖c‖} := by
  have hiter := continuous_iterate_self n
  have hP : Continuous (fun c : ℂ => Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[n] c)) := by
    have h := continuous_iterate_self (n + 1)
    have hfun : (fun c : ℂ => (Work.Bottcher.pMap c)^[n + 1] c)
        = (fun c : ℂ => Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[n] c)) := by
      funext c
      rw [Function.iterate_succ_apply']
    rwa [hfun] at h
  have h1 : ContinuousOn (fun c : ℂ => Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[n] c))
      {c : ℂ | 8 ≤ ‖c‖} := hP.continuousOn
  have h2 : ContinuousOn (fun c : ℂ => ((Work.Bottcher.pMap c)^[n] c) ^ 4)
      {c : ℂ | 8 ≤ ‖c‖} := (hiter.pow 4).continuousOn
  have h3 : ∀ c ∈ {c : ℂ | 8 ≤ ‖c‖}, ((Work.Bottcher.pMap c)^[n] c) ^ 4 ≠ 0 := by
    intro c hc
    have hz := eight_le_norm_iterate_self c hc n
    exact pow_ne_zero 4 (by
      intro hzero
      rw [hzero, norm_zero] at hz
      norm_num at hz)
  have hnf : ContinuousOn (fun c : ℂ => Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))
      {c : ℂ | 8 ≤ ‖c‖} := h1.div h2 h3
  have hslit : ∀ c ∈ {c : ℂ | 8 ≤ ‖c‖},
      Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c) ∈ Complex.slitPlane := by
    intro c hc
    refine Complex.ball_one_subset_slitPlane ?_
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (normFactor_sub_one_le_half c hc n) (by norm_num)
  have hlog := hnf.clog hslit
  have hmul := hlog.const_mul (((1 / 4 : ℝ) ^ (n + 1) : ℂ))
  have hfun : (fun c : ℂ => Work.Bottcher.bottcherTerm c n c)
      = (fun c : ℂ => ((1 / 4 : ℝ) ^ (n + 1) : ℂ)
          * Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] c))) := by
    funext c
    rw [Work.Bottcher.bottcherTerm]
  rw [hfun]
  exact hmul

/-! ### The diagonal of the Böttcher map is continuous on `{‖c‖ ≥ 8}` -/

/-- **The product formula is continuous along the diagonal `c ↦ bottcher c c` for large `‖c‖`.**

Needed for the uniform asymptotic `Φ c / c → 1`: the ratio `φ_c(c) / bottcher c c` is a `4`-th root
of unity which must be shown locally constant in `c`, so `c ↦ bottcher c c` has to be continuous at
`z = c`.  (The far-region lemma `continuousOn_jointBottcher` does *not* apply, since
`escapeRadius c = 2(1+‖c‖) > ‖c‖`.)

Route: `bottcher c c = c * exp (Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] c)))`
(`Work.Bottcher.bottcher`, `Work.Bottcher.bottcherSeries`).  For `‖c‖ ≥ 8` the normalised factor is
uniformly within `1/2` of `1` along the whole critical orbit, so `‖log (normFactor c z_n)‖ ≤ 1` for
all `n`; the terms are dominated by the summable sequence `4^{-(n+1)}`, and each partial sum is
continuous, so the series — hence `bottcher · ·` — is continuous on `{c | 8 ≤ ‖c‖}`
(`continuousOn_tsum`). -/
theorem continuousOn_bottcher_self :
    ContinuousOn (fun c : ℂ => Work.Bottcher.bottcher c c) {c : ℂ | 8 ≤ ‖c‖} := by
  have hsum : ContinuousOn (fun c : ℂ => ∑' n : ℕ, Work.Bottcher.bottcherTerm c n c)
      {c : ℂ | 8 ≤ ‖c‖} :=
    continuousOn_tsum continuousOn_bottcherTerm summable_quarter_pow_succ
      (fun n c hc => norm_bottcherTerm_self_le c hc n)
  have hfinal : ContinuousOn
      (fun c : ℂ => c * Complex.exp (∑' n : ℕ, Work.Bottcher.bottcherTerm c n c))
      {c : ℂ | 8 ≤ ‖c‖} :=
    (continuous_id.continuousOn).mul (Complex.continuous_exp.comp_continuousOn hsum)
  convert hfinal using 1
  ext c
  rw [Work.Bottcher.bottcher, Work.Bottcher.bottcherSeries]

end

end Work.NAKANE.BottcherFar
