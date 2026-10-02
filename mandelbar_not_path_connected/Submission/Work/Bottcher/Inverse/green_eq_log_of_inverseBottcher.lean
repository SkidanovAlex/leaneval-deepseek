import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Escape.geom_le_norm_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `G_c (Ψ w) = log ‖w‖` for an inverse Böttcher coordinate `Ψ`

Let `c : ℂ` and let `Ψ : ℂ → ℂ` be a *right inverse of the Böttcher coordinate at infinity*:
it satisfies the functional equation `p_c (Ψ w) = Ψ (w^4)` for `‖w‖ > 1` (with `p_c` the
holomorphic second iterate `p_c = T_c ∘ T_c` of the tricorn map `T_c(z) = z̄² + c`) and it is
tangent to the identity at infinity, `Ψ w / w → 1`.

The Green function `G_c = green c` satisfies `G_c ∘ p_c = 4 G_c` (`green_pMap`) and is asymptotic
to `log ‖·‖` at infinity (`tendsto_green_sub_log`).  Hence
`Γ(w) := G_c (Ψ w)` satisfies `Γ(w^4) = 4 Γ(w)` and `Γ(w) - log ‖w‖ → 0`; iterating the
functional equation along `w ↦ w^4` (which escapes to infinity) forces `Γ(w) = log ‖w‖`.

This is the "automatic Green identity" step of the construction of the inverse Böttcher
coordinate in the multicorn chapter.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Inverse

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The Green function doubles under `T_c` and quadruples under `p_c` -/

/-- The Green function of the tricorn, composed with the holomorphic second iterate `p_c`,
multiplies by `4`.  Immediate from two applications of `G_c (T_c z) = 2 G_c z`. -/
theorem green_pMap (c z : ℂ) : green c (pMap c z) = 4 * green c z := by
  have h1 : pMap c z = Tantibar c (Tantibar c z) := by
    rw [pMap_eq_iterate_two]; rfl
  rw [h1, Green.green_comm c (Tantibar c z), Green.green_comm c z]
  ring

/-! ## Lower bound for the Green function in the escaping region -/

/-- In the escaping region `{z | max 2 ‖c‖ < ‖z‖}` the Green function dominates
`log ‖z‖ - log 2`.

The point is the geometric lower bound `2 (‖z‖/2)^{2^n} ≤ ‖T_c^n z‖`
(`Work.Escape.geom_le_norm_iterate`), which after taking `2^{-n} log` and letting `n → ∞`
gives the claim (the lost `log 2` is the additive constant of the monic-growth bound). -/
theorem log_sub_log2_le_green (c z : ℂ) (hz : max 2 ‖c‖ < ‖z‖) :
    Real.log ‖z‖ - Real.log 2 ≤ green c z := by
  have hz2 : (2 : ℝ) < ‖z‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) hz
  have hzpos : 0 < ‖z‖ := by linarith
  have hge : ∀ n : ℕ, Real.log ‖z‖ - Real.log 2
      ≤ Work.Escape.greenIter (Tantibar c) 2 z n := by
    intro n
    have hgeom := Work.Escape.geom_le_norm_iterate (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) le_rfl hz n
    set s : ℝ := 2 * (‖z‖ / 2) ^ ((2 : ℕ) ^ n) with hs
    have hhalf1 : (1 : ℝ) ≤ ‖z‖ / 2 := by linarith
    have hs1 : (1 : ℝ) ≤ s := by
      have hpow : (1 : ℝ) ≤ (‖z‖ / 2) ^ ((2 : ℕ) ^ n) := one_le_pow₀ hhalf1
      rw [hs]; nlinarith
    have hmono : Work.Escape.logPos s ≤ Work.Escape.logPos ‖(Tantibar c)^[n] z‖ :=
      Work.Escape.logPos_mono hgeom
    have hlogeq : Work.Escape.logPos s = Real.log s := Work.Escape.logPos_eq_log hs1
    have hlogcalc : Real.log s
        = Real.log 2 + (2 : ℝ) ^ n * (Real.log ‖z‖ - Real.log 2) := by
      rw [hs]
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_pow,
        Real.log_div (ne_of_gt hzpos) (by norm_num)]
      push_cast
      ring
    have hne : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    have hkey : ((2 : ℝ) ^ n)⁻¹ * (Real.log 2
          + (2 : ℝ) ^ n * (Real.log ‖z‖ - Real.log 2))
        = ((2 : ℝ) ^ n)⁻¹ * Real.log 2 + (Real.log ‖z‖ - Real.log 2) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hnn : 0 ≤ ((2 : ℝ) ^ n)⁻¹ * Real.log 2 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    have hlow : Real.log ‖z‖ - Real.log 2 ≤ ((2 : ℝ) ^ n)⁻¹ * Work.Escape.logPos s := by
      rw [hlogeq, hlogcalc, hkey]
      linarith
    have hup : ((2 : ℝ) ^ n)⁻¹ * Work.Escape.logPos s
        ≤ ((2 : ℝ) ^ n)⁻¹ * Work.Escape.logPos ‖(Tantibar c)^[n] z‖ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    rw [Work.Escape.greenIter_def]
    exact le_trans hlow hup
  exact ge_of_tendsto (Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖
    (Work.Escape.monicGrowth_Tantibar c) le_rfl z) (Filter.Eventually.of_forall hge)

/-! ## The critical domain is eventually all of a neighbourhood of infinity -/

/-- For every parameter `c`, points of sufficiently large norm already lie in the critical
domain `CritDomain c = {G_c > G_c(0)}`. -/
theorem eventually_mem_CritDomain (c : ℂ) :
    ∀ᶠ z : ℂ in cocompact ℂ, z ∈ CritDomain c := by
  set R : ℝ := max (max 2 ‖c‖ + 1) (Real.exp (greenParam c + Real.log 2) + 1) with hRdef
  have hRbig : max 2 ‖c‖ < R :=
    lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hRexp : Real.exp (greenParam c + Real.log 2) < R :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hRpos : 0 < R := lt_trans (Real.exp_pos _) hRexp
  have hgplog : greenParam c < Real.log R - Real.log 2 := by
    have h1 : Real.log (Real.exp (greenParam c + Real.log 2)) < Real.log R :=
      Real.log_lt_log (Real.exp_pos _) hRexp
    rw [Real.log_exp] at h1
    linarith
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)] with z hz
  rw [mem_CritDomain]
  have hzbig : max 2 ‖c‖ < ‖z‖ := lt_of_lt_of_le hRbig hz
  have hlow := log_sub_log2_le_green c z hzbig
  have hlogz : Real.log R ≤ Real.log ‖z‖ := Real.log_le_log hRpos hz
  linarith

/-! ## The Green function is asymptotic to `log ‖·‖` at infinity -/

/-- `G_c z - log ‖z‖ → 0` as `z → ∞`.  For large `z` the point lies in `CritDomain c`, where
`‖bottcher c z‖ = exp (G_c z)` (`norm_bottcher_domain`); the claim is then the tangency
`bottcher c z / z → 1` of the Böttcher coordinate. -/
theorem tendsto_green_sub_log (c : ℂ) :
    Tendsto (fun z : ℂ => green c z - Real.log ‖z‖) (cocompact ℂ) (nhds 0) := by
  have hlog : Tendsto (fun z : ℂ => Real.log ‖bottcher c z / z‖) (cocompact ℂ) (nhds 0) := by
    have hratio : Tendsto (fun z : ℂ => ‖bottcher c z / z‖) (cocompact ℂ) (nhds 1) := by
      have h := (continuous_norm.tendsto (1 : ℂ)).comp (Core.bottcher_tendsto_atTop c)
      simpa only [Function.comp_def, norm_one] using h
    have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
    simpa only [Function.comp_def, Real.log_one] using h2
  refine hlog.congr' ?_
  filter_upwards [eventually_mem_CritDomain c] with z hz
  have hz0 : z ≠ 0 := fun h => zero_notMem_CritDomain c (h ▸ hz)
  have hb : green c z = Real.log ‖bottcher c z‖ := by
    have h := Core.norm_bottcher_domain c z hz
    rw [h, Real.log_exp]
  have hbnz : ‖bottcher c z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact bottcher_ne_zero c hz0
  have hznz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  rw [hb, ← Real.log_div hbnz hznz, norm_div]

/-! ## A map tangent to the identity at infinity is cocompact -/

/-- If `Ψ w / w → 1` at infinity then `Ψ` is proper: it sends `cocompact` to `cocompact`. -/
theorem tendsto_cocompact_of_ratio (Ψ : ℂ → ℂ)
    (has : Tendsto (fun w : ℂ => Ψ w / w) (cocompact ℂ) (nhds (1 : ℂ))) :
    Tendsto Ψ (cocompact ℂ) (cocompact ℂ) := by
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) ?_
  simp only [dist_zero_right]
  have hratio : Tendsto (fun w : ℂ => ‖Ψ w / w‖) (cocompact ℂ) (nhds 1) := by
    have h := (continuous_norm.tendsto (1 : ℂ)).comp has
    simpa only [Function.comp_def, norm_one] using h
  have hev : ∀ᶠ w : ℂ in cocompact ℂ, ‖w‖ * (1 / 2) ≤ ‖Ψ w‖ := by
    have hhalf : ∀ᶠ w : ℂ in cocompact ℂ, (1 / 2 : ℝ) ≤ ‖Ψ w / w‖ :=
      hratio.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have hne : ∀ᶠ w : ℂ in cocompact ℂ, w ≠ 0 := by
      filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop 0)] with w hw
      exact norm_pos_iff.mp hw
    filter_upwards [hhalf, hne] with w hw1 hw2
    have hEq : (Ψ w / w) * w = Ψ w := div_mul_cancel₀ (Ψ w) hw2
    have hnorm : ‖Ψ w‖ = ‖Ψ w / w‖ * ‖w‖ := by
      calc ‖Ψ w‖ = ‖(Ψ w / w) * w‖ := by rw [hEq]
        _ = ‖Ψ w / w‖ * ‖w‖ := norm_mul _ _
    rw [hnorm]
    nlinarith [norm_nonneg w]
  have hf1 : Tendsto (fun w : ℂ => ‖w‖ * (1 / 2)) (cocompact ℂ) atTop :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).atTop_mul_const (by norm_num)
  exact Filter.tendsto_atTop_mono' (cocompact ℂ) hev hf1

/-! ## The main theorem -/

theorem green_eq_log_of_inverseBottcher (c : ℂ) (Ψ : ℂ → ℂ)
    (hcont : ContinuousOn Ψ {w : ℂ | 1 < ‖w‖})
    (hfe : ∀ w : ℂ, 1 < ‖w‖ → Work.Bottcher.pMap c (Ψ w) = Ψ (w ^ 4))
    (has : Filter.Tendsto (fun w : ℂ => Ψ w / w) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    ∀ w : ℂ, 1 < ‖w‖ → Work.Bottcher.green c (Ψ w) = Real.log ‖w‖ := by
  have hPsi : Tendsto Ψ (cocompact ℂ) (cocompact ℂ) := tendsto_cocompact_of_ratio Ψ has
  -- `H u = G_c (Ψ u) - log ‖u‖` tends to `0` at infinity
  have hH : Tendsto (fun u : ℂ => green c (Ψ u) - Real.log ‖u‖) (cocompact ℂ) (nhds 0) := by
    have h1 : Tendsto (fun u : ℂ => green c (Ψ u) - Real.log ‖Ψ u‖) (cocompact ℂ) (nhds 0) :=
      (tendsto_green_sub_log c).comp hPsi
    have h2 : Tendsto (fun u : ℂ => Real.log ‖Ψ u‖ - Real.log ‖u‖) (cocompact ℂ) (nhds 0) := by
      have hratio : Tendsto (fun u : ℂ => ‖Ψ u / u‖) (cocompact ℂ) (nhds 1) := by
        have h := (continuous_norm.tendsto (1 : ℂ)).comp has
        simpa only [Function.comp_def, norm_one] using h
      have hlogr : Tendsto (fun u : ℂ => Real.log ‖Ψ u / u‖) (cocompact ℂ) (nhds 0) := by
        have h3 := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
        simpa only [Function.comp_def, Real.log_one] using h3
      refine hlogr.congr' ?_
      have hne : ∀ᶠ u : ℂ in cocompact ℂ, u ≠ 0 := by
        filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop 0)] with u hu
        exact norm_pos_iff.mp hu
      have hPsinz : ∀ᶠ u : ℂ in cocompact ℂ, Ψ u ≠ 0 := by
        filter_upwards [hratio.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1)), hne] with u hr hu
        intro h0
        rw [h0, zero_div, norm_zero] at hr
        norm_num at hr
      filter_upwards [hne, hPsinz] with u hu hPs
      have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
      have hnp : ‖Ψ u‖ ≠ 0 := norm_ne_zero_iff.mpr hPs
      rw [norm_div, Real.log_div hnp hnu]
    have hsum := h1.add h2
    have hfe' : (fun u : ℂ => (green c (Ψ u) - Real.log ‖Ψ u‖)
        + (Real.log ‖Ψ u‖ - Real.log ‖u‖))
        = fun u : ℂ => green c (Ψ u) - Real.log ‖u‖ := by
      funext u; ring
    rw [hfe'] at hsum
    simpa using hsum
  intro w hw
  -- functional equation for `H` along `w ↦ w^4`
  have hHfe : ∀ u : ℂ, 1 < ‖u‖ →
      green c (Ψ (u ^ 4)) - Real.log ‖u ^ 4‖ = 4 * (green c (Ψ u) - Real.log ‖u‖) := by
    intro u hu
    rw [← hfe u hu, green_pMap, norm_pow, Real.log_pow]
    ring
  -- the constant relation `H (w^{4^n}) = 4^n H w`
  have hconst : ∀ n : ℕ,
      green c (Ψ (w ^ ((4 : ℕ) ^ n))) - Real.log ‖w ^ ((4 : ℕ) ^ n)‖
        = (4 : ℝ) ^ n * (green c (Ψ w) - Real.log ‖w‖) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have h4 : (4 : ℕ) ^ (k + 1) = (4 : ℕ) ^ k * 4 := pow_succ 4 k
        have hhu : 1 < ‖w ^ ((4 : ℕ) ^ k)‖ := by
          rw [norm_pow]
          exact one_lt_pow₀ hw (pow_ne_zero k (by norm_num))
        rw [h4, pow_mul, hHfe (w ^ ((4 : ℕ) ^ k)) hhu, ih, pow_succ]
        ring
  -- the sequence `n ↦ w^{4^n}` escapes to infinity
  have hseq : Tendsto (fun n : ℕ => w ^ ((4 : ℕ) ^ n)) atTop (cocompact ℂ) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) ?_
    simp only [dist_zero_right]
    have hbase : Tendsto (fun n : ℕ => ‖w‖ ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hw
    refine Filter.tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards with n
    rw [norm_pow]
    exact pow_le_pow_right₀ hw.le (le_of_lt (Nat.lt_pow_self (n := n) (a := 4) (by norm_num)))
  have hHseq : Tendsto
      (fun n : ℕ => green c (Ψ (w ^ ((4 : ℕ) ^ n))) - Real.log ‖w ^ ((4 : ℕ) ^ n)‖)
      atTop (nhds 0) := hH.comp hseq
  -- conclude by uniqueness of limits
  have hprod : Tendsto (fun n : ℕ => ((4 : ℝ) ^ n)⁻¹
      * (green c (Ψ (w ^ ((4 : ℕ) ^ n))) - Real.log ‖w ^ ((4 : ℕ) ^ n)‖)) atTop (nhds 0) := by
    have h4pow : Tendsto (fun n : ℕ => (4 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h := h4pow.inv_tendsto_atTop.mul hHseq
    simpa using h
  have hconstseq : ∀ n : ℕ, (green c (Ψ w) - Real.log ‖w‖)
      = ((4 : ℝ) ^ n)⁻¹
        * (green c (Ψ (w ^ ((4 : ℕ) ^ n))) - Real.log ‖w ^ ((4 : ℕ) ^ n)‖) := by
    intro n
    rw [hconst n]
    field_simp
  have hXlim : Tendsto (fun _ : ℕ => green c (Ψ w) - Real.log ‖w‖) atTop (nhds 0) :=
    hprod.congr' (Filter.Eventually.of_forall (fun n => (hconstseq n).symm))
  have hX0 : green c (Ψ w) - Real.log ‖w‖ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hXlim
  linarith [hX0]

end Work.Bottcher.Inverse
