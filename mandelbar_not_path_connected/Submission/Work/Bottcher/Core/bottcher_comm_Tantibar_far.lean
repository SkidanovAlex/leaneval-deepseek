/-
# The Böttcher equation `φ_c ∘ T_c = conj ∘ φ_c²` on the far region

The product formula `bottcher c z = z * exp (Σ_n 4^{-(n+1)} log (p_c^n z / (p_c^n z)^4))`
for the tricorn family `T_c(z) = conj z ^ 2 + c` satisfies

`bottcher c (T_c z) = conj (bottcher c z) ^ 2`      (`bottcher_comm_Tantibar_far`)

as soon as `‖z‖ ≥ escapeRadius c = 2 (1 + ‖c‖)`.

**Why the far region.**  `Complex.log` is not additive, so the product formula agrees with the
analytic Böttcher coordinate only on the region where every factor `p_c^n z / (p_c^n z)^4` stays
off the negative real axis; above `escapeRadius c` all iterates have norm `≥ 2 (1 + ‖c‖)`, hence
every factor is within `3/4` of `1` and has positive real part (`norm_nfG_le`), so the branch
corrections vanish term by term.  Off this region the statement is genuinely false: see
`Work.Bottcher.Core.bottcher_comm_Tantibar_false` in `Core/ProductFormulaTelescoping.lean`.

**Route.**  Two independent ingredients:

* *Symmetry* (`conj_bottcher_far`): `conj (bottcher c w) = bottcher (conj c) (conj w)` for
  `‖w‖ ≥ escapeRadius c`.  Term by term, `(pMap (conj c))^[n] (conj w) = conj ((pMap c)^[n] w)`
  and `normFactor (conj c) (conj v) = conj (normFactor c v)`; the log factors conjugate because
  on the far region they have positive real part (`Complex.log_conj` needs only `arg ≠ π`).
  `conj` is continuous, so it passes through the `tsum`.
* *Analytic constancy*: the ratio
  `F z = bottcher (conj c) (z² + conj c) / (bottcher c z)²` is analytic on the (preconnected,
  open) far region `{‖z‖ > escapeRadius c}`, has modulus `1` there (`‖φ_c z‖ = exp (G_c z)` and
  `G_c (T_c z) = 2 G_c z`), and tends to `1` at infinity; hence `F ≡ 1`
  (`AnalyticOnNhd.is_constant_or_isOpen`).  Substituting `z ↦ T_c z` and conjugating gives the
  Böttcher equation; the boundary case `‖z‖ = escapeRadius c` follows by continuity.

-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Core.bottcher_tendsto_atTop
import Submission.Work.Bottcher.Series.summable_bottcherTerm
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Core

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The far region and the growth of the `T_c`-orbit

These are the elementary escape-radius facts used below; they are proved here so that this file
depends only on completed modules.  (`Work.Bottcher.Core.eq_bottcher_of_analytic` proves the same
statements; the proofs are reproduced to keep this file self-contained.) -/

private theorem escapeRadius_pos (c : ℂ) : 0 < Work.Bottcher.escapeRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [Work.Bottcher.escapeRadius]
  linarith

private theorem two_add_norm_le_escapeRadius (c : ℂ) :
    2 + ‖c‖ ≤ Work.Bottcher.escapeRadius c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [Work.Bottcher.escapeRadius]
  linarith

private theorem two_mul_norm_le_norm_Tantibar (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) : 2 * ‖w‖ ≤ ‖Tantibar c w‖ := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : ‖w‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c w‖ := norm_Tantibar_ge c w
  have hR : 2 + 2 * ‖c‖ ≤ ‖w‖ := by
    rw [Work.Bottcher.escapeRadius] at hw
    linarith
  have hR2 : 2 * ‖c‖ ≤ ‖w‖ - 2 := by linarith
  have hprod : (2 + 2 * ‖c‖) * (2 * ‖c‖) ≤ ‖w‖ * (‖w‖ - 2) :=
    mul_le_mul hR hR2 (by positivity) (by linarith)
  have hle : ‖c‖ ≤ ‖w‖ * (‖w‖ - 2) := by nlinarith [hprod, ht, sq_nonneg ‖c‖]
  linarith [h1]

private theorem escapeRadius_le_norm_Tantibar (c : ℂ) {w : ℂ}
    (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) :
    Work.Bottcher.escapeRadius c ≤ ‖Tantibar c w‖ := by
  have h1 := two_mul_norm_le_norm_Tantibar c hw
  have h2 : ‖w‖ ≤ 2 * ‖w‖ := by linarith [norm_nonneg w]
  linarith

private theorem escapeRadius_le_norm_Tantibar_iterate (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) (n : ℕ) :
    Work.Bottcher.escapeRadius c ≤ ‖(Tantibar c)^[n] z‖ ∧
      2 ^ n * ‖z‖ ≤ ‖(Tantibar c)^[n] z‖ := by
  induction n with
  | zero => exact ⟨hz, by simp⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨escapeRadius_le_norm_Tantibar c ih.1, ?_⟩
      rw [pow_succ]
      have h2 : 2 * ‖(Tantibar c)^[n] z‖ ≤ ‖Tantibar c ((Tantibar c)^[n] z)‖ :=
        two_mul_norm_le_norm_Tantibar c ih.1
      nlinarith [ih.2, h2]

private theorem tendsto_norm_Tantibar_iterate_of_escapeRadius_le (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (escapeRadius_pos c) hz
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine tendsto_atTop_mono (fun n => (escapeRadius_le_norm_Tantibar_iterate c hz n).2) ?_
  simpa using hpow.atTop_mul_const hzpos

private theorem conj_Tantibar (c z : ℂ) :
    (starRingEnd ℂ) (Tantibar c z) = z ^ 2 + (starRingEnd ℂ) c := by
  simp only [LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow, Complex.conj_conj]

private theorem escapeRadius_conj (c : ℂ) :
    Work.Bottcher.escapeRadius ((starRingEnd ℂ) c) = Work.Bottcher.escapeRadius c := by
  simp [Work.Bottcher.escapeRadius]

/-! ## `‖φ_c z‖ = exp (G_c z)` on the far region -/

private theorem norm_bottcher_eq_exp_green_of_escapeRadius_le (c : ℂ) {z : ℂ}
    (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    ‖Work.Bottcher.bottcher c z‖ = Real.exp (Work.Bottcher.green c z) := by
  refine norm_bottcher_eq_exp_green c z ?_ ?_ ?_
  · exact tendsto_norm_Tantibar_iterate_of_escapeRadius_le c hz
  · have hgr := Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) (by norm_num) z
    have hfun : Work.Escape.greenIter (Tantibar c) 2 z
        = fun n : ℕ => ((1 : ℝ) / 2) ^ n * Work.Escape.logPos ‖(Tantibar c)^[n] z‖ := by
      funext n
      rw [Work.Escape.greenIter_def, one_div, inv_pow]
      norm_num
    exact hfun ▸ hgr
  · intro n
    rw [Work.Bottcher.pMap_iterate]
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (escapeRadius_pos c)
      ((escapeRadius_le_norm_Tantibar_iterate c hz (2 * n)).1)))

/-! ## The conjugation symmetry of the product formula

`conj (bottcher c w) = bottcher (conj c) (conj w)` on the far region.  This is the only place
where the far-region hypothesis is used in an essential (branch-cut) way: `Complex.log` conjugates
only when its argument stays off the negative real axis. -/

private lemma conj_tsum (f : ℕ → ℂ) (hf : Summable f) :
    (starRingEnd ℂ) (∑' n, f n) = ∑' n, (starRingEnd ℂ) (f n) := by
  have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (nhds (∑' n, f n)) :=
    hf.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N : ℕ => (starRingEnd ℂ) (∑ n ∈ Finset.range N, f n)) atTop
      (nhds ((starRingEnd ℂ) (∑' n, f n))) :=
    (Complex.continuous_conj.tendsto _).comp h1
  have h3 : (fun N : ℕ => (starRingEnd ℂ) (∑ n ∈ Finset.range N, f n))
      = fun N : ℕ => ∑ n ∈ Finset.range N, (starRingEnd ℂ) (f n) := by
    funext N
    exact map_sum (starRingEnd ℂ) f (Finset.range N)
  have h4 : Summable (fun n => (starRingEnd ℂ) (f n)) := by
    have hnf : Summable (fun n => ‖f n‖) := hf.norm
    refine Summable.of_norm ?_
    simpa [Complex.norm_conj] using hnf
  have h5 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (starRingEnd ℂ) (f n)) atTop
      (nhds (∑' n, (starRingEnd ℂ) (f n))) := h4.hasSum.tendsto_sum_nat
  rw [← h3] at h5
  exact tendsto_nhds_unique h2 h5

private lemma conj_normFactor (c v : ℂ) :
    Work.Bottcher.normFactor ((starRingEnd ℂ) c) ((starRingEnd ℂ) v)
      = (starRingEnd ℂ) (Work.Bottcher.normFactor c v) := by
  rw [Work.Bottcher.normFactor, Work.Bottcher.normFactor, Work.Bottcher.pMap_apply,
    Work.Bottcher.pMap_apply]
  simp only [map_add, map_pow, map_div₀, Complex.conj_conj]

private lemma pMap_conj (c v : ℂ) :
    Work.Bottcher.pMap ((starRingEnd ℂ) c) ((starRingEnd ℂ) v)
      = (starRingEnd ℂ) (Work.Bottcher.pMap c v) := by
  rw [Work.Bottcher.pMap_apply, Work.Bottcher.pMap_apply]
  simp only [map_add, map_pow, Complex.conj_conj]

private lemma iterate_pMap_conj (c v : ℂ) (n : ℕ) :
    (Work.Bottcher.pMap ((starRingEnd ℂ) c))^[n] ((starRingEnd ℂ) v)
      = (starRingEnd ℂ) ((Work.Bottcher.pMap c)^[n] v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, pMap_conj]

/-- On the far region every Böttcher factor has positive real part, hence argument `≠ π`, so the
principal logarithm commutes with conjugation. -/
private lemma arg_normFactor_ne_pi (c v : ℂ) (hv : Work.Bottcher.escapeRadius c ≤ ‖v‖) :
    (Work.Bottcher.normFactor c v).arg ≠ Real.pi := by
  have h1 : 1 + ‖c‖ ≤ ‖v‖ :=
    le_trans (le_trans (by linarith [norm_nonneg c]) (two_add_norm_le_escapeRadius c)) hv
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    linarith [norm_nonneg c]
  have hre : 0 < (Work.Bottcher.normFactor c v).re := by
    rw [normFactor_eq_one_add_nfG c v hv0, Complex.add_re, Complex.one_re]
    have hb := norm_nfG_le c v h1
    have h2 : -(‖nfG c v‖) ≤ (nfG c v).re := by
      have h := Complex.re_le_norm (-(nfG c v))
      rw [Complex.neg_re, norm_neg] at h
      linarith
    linarith
  intro hpi
  have hneg : (Work.Bottcher.normFactor c v).re < 0 := (Complex.arg_eq_pi_iff.mp hpi).1
  linarith

private lemma bottcherTerm_conj (c w : ℂ) (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) (n : ℕ) :
    Work.Bottcher.bottcherTerm ((starRingEnd ℂ) c) n ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) (Work.Bottcher.bottcherTerm c n w) := by
  have h1 : (Work.Bottcher.pMap ((starRingEnd ℂ) c))^[n] ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) ((Work.Bottcher.pMap c)^[n] w) := iterate_pMap_conj c w n
  have h2 : Work.Bottcher.escapeRadius c ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ := by
    rw [Work.Bottcher.pMap_iterate]
    exact (escapeRadius_le_norm_Tantibar_iterate c hw (2 * n)).1
  rw [Work.Bottcher.bottcherTerm, Work.Bottcher.bottcherTerm, h1, conj_normFactor,
    Complex.log_conj _ (arg_normFactor_ne_pi c _ h2)]
  simp only [map_mul, map_pow, Complex.conj_ofReal]

private lemma summable_bottcherTerm_conj (c w : ℂ) (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) :
    Summable (fun n => Work.Bottcher.bottcherTerm ((starRingEnd ℂ) c) n ((starRingEnd ℂ) w)) := by
  have h1 : 1 + ‖(starRingEnd ℂ) c‖ ≤ ‖(starRingEnd ℂ) w‖ := by
    rw [Complex.norm_conj, Complex.norm_conj]
    exact le_trans (by linarith [norm_nonneg c])
      (le_trans (two_add_norm_le_escapeRadius c) hw)
  refine Summable.of_norm_bounded (g := fun n : ℕ => (15 / 8 : ℝ) * (1 / 4 : ℝ) ^ n) ?_ ?_
  · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left (15 / 8)
  · intro n
    simpa using norm_term_le ((starRingEnd ℂ) c) ((starRingEnd ℂ) w) h1 n

/-- **Conjugation symmetry of the product formula on the far region.** -/
private lemma conj_bottcher_far (c w : ℂ) (hw : Work.Bottcher.escapeRadius c ≤ ‖w‖) :
    (starRingEnd ℂ) (Work.Bottcher.bottcher c w)
      = Work.Bottcher.bottcher ((starRingEnd ℂ) c) ((starRingEnd ℂ) w) := by
  have hsum : Summable (fun n => Work.Bottcher.bottcherTerm c n w) :=
    Work.Bottcher.Series.summable_bottcherTerm c w
      (tendsto_norm_Tantibar_iterate_of_escapeRadius_le c hw)
  have hterm : ∀ n : ℕ, Work.Bottcher.bottcherTerm ((starRingEnd ℂ) c) n ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) (Work.Bottcher.bottcherTerm c n w) := fun n => bottcherTerm_conj c w hw n
  have hseries : Work.Bottcher.bottcherSeries ((starRingEnd ℂ) c) ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) (Work.Bottcher.bottcherSeries c w) := by
    rw [Work.Bottcher.bottcherSeries, Work.Bottcher.bottcherSeries, conj_tsum _ hsum]
    exact tsum_congr hterm
  simp only [Work.Bottcher.bottcher]
  rw [map_mul, hseries, Complex.exp_conj]

/-! ## The Green function

`G_{conj c}(conj w) = G_c w` (the orbits are conjugate, hence have equal norms), and
`G_c (T_c z) = 2 G_c z` (`Work.Bottcher.Green.green_comm`). -/

private lemma iterate_conj_Tantibar (c w : ℂ) (n : ℕ) :
    (Tantibar ((starRingEnd ℂ) c))^[n] ((starRingEnd ℂ) w)
      = (starRingEnd ℂ) ((Tantibar c)^[n] w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp only [LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow, Complex.conj_conj]

private lemma green_conj_conj (c w : ℂ) :
    Work.Bottcher.green ((starRingEnd ℂ) c) ((starRingEnd ℂ) w) = Work.Bottcher.green c w := by
  have h : Work.Escape.greenIter (Tantibar ((starRingEnd ℂ) c)) 2 ((starRingEnd ℂ) w)
      = Work.Escape.greenIter (Tantibar c) 2 w := by
    funext n
    rw [Work.Escape.greenIter_def, Work.Escape.greenIter_def, iterate_conj_Tantibar c w n,
      Complex.norm_conj]
  change Filter.limUnder atTop
      (Work.Escape.greenIter (Tantibar ((starRingEnd ℂ) c)) 2 ((starRingEnd ℂ) w))
    = Filter.limUnder atTop (Work.Escape.greenIter (Tantibar c) 2 w)
  rw [h]

private lemma green_conj_Tantibar (c z : ℂ) :
    Work.Bottcher.green ((starRingEnd ℂ) c) (z ^ 2 + (starRingEnd ℂ) c)
      = 2 * Work.Bottcher.green c z := by
  rw [← conj_Tantibar c z, green_conj_conj, Work.Bottcher.Green.green_comm]

/-! ## The ratio `F z = φ_{conj c}(z² + conj c) / φ_c(z)²`

`F` has modulus `1` on the far region, is analytic there, and tends to `1` at infinity; hence it
is identically `1` there. -/

private lemma norm_ofReal' (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

private lemma norm_ratio (c z : ℂ) (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    ‖Work.Bottcher.bottcher ((starRingEnd ℂ) c) (z ^ 2 + (starRingEnd ℂ) c)
        / (Work.Bottcher.bottcher c z) ^ 2‖ = 1 := by
  have hzT : Work.Bottcher.escapeRadius c ≤ ‖z ^ 2 + (starRingEnd ℂ) c‖ := by
    rw [← conj_Tantibar c z, Complex.norm_conj]
    exact escapeRadius_le_norm_Tantibar c hz
  rw [norm_div, norm_pow, norm_bottcher_eq_exp_green_of_escapeRadius_le ((starRingEnd ℂ) c)
      (by rw [escapeRadius_conj]; exact hzT),
    norm_bottcher_eq_exp_green_of_escapeRadius_le c hz, green_conj_Tantibar c z]
  have hexp : Real.exp (2 * Work.Bottcher.green c z) = Real.exp (Work.Bottcher.green c z) ^ 2 := by
    rw [sq, ← Real.exp_add, two_mul]
  rw [hexp, div_self (pow_ne_zero 2 (Real.exp_ne_zero _))]

private lemma analyticAt_ratio (c : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => Work.Bottcher.bottcher ((starRingEnd ℂ) c)
        (z ^ 2 + (starRingEnd ℂ) c) / (Work.Bottcher.bottcher c z) ^ 2)
      {z : ℂ | Work.Bottcher.escapeRadius c < ‖z‖} := by
  intro z hz
  have hzle : Work.Bottcher.escapeRadius c ≤ ‖z‖ := le_of_lt hz
  have hzT : Work.Bottcher.escapeRadius c ≤ ‖z ^ 2 + (starRingEnd ℂ) c‖ := by
    rw [← conj_Tantibar c z, Complex.norm_conj]
    exact escapeRadius_le_norm_Tantibar c hzle
  have hzne : z ≠ 0 := by
    intro h
    have hz' : Work.Bottcher.escapeRadius c < ‖z‖ := hz
    rw [h] at hz'
    simp only [norm_zero] at hz'
    linarith [escapeRadius_pos c]
  refine AnalyticAt.div ?_ ?_ ?_
  · have hcomp := AnalyticAt.comp (g := fun w : ℂ => Work.Bottcher.bottcher ((starRingEnd ℂ) c) w)
      (f := fun z : ℂ => z ^ 2 + (starRingEnd ℂ) c)
      (analyticAt_bottcher ((starRingEnd ℂ) c) (z ^ 2 + (starRingEnd ℂ) c)
        (by rw [escapeRadius_conj]; exact hzT))
      (((analyticAt_id (𝕜 := ℂ) (z := z)).pow 2).add analyticAt_const)
    simpa [Function.comp_def] using hcomp
  · exact (analyticAt_bottcher c z hzle).pow 2
  · exact pow_ne_zero 2 (Work.Bottcher.bottcher_ne_zero c hzne)

private lemma tendsto_ratio (c : ℂ) :
    Tendsto (fun z : ℂ => Work.Bottcher.bottcher ((starRingEnd ℂ) c) (z ^ 2 + (starRingEnd ℂ) c)
        / (Work.Bottcher.bottcher c z) ^ 2) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  have hnorm : Tendsto (fun z : ℂ => ‖z ^ 2 + (starRingEnd ℂ) c‖) (Filter.cocompact ℂ)
      Filter.atTop := by
    have h1 : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (Filter.cocompact ℂ) Filter.atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun z : ℂ => ‖z‖ ^ 2 - ‖c‖) (Filter.cocompact ℂ) Filter.atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [h1.eventually (eventually_ge_atTop (b + ‖c‖))] with z hz
      linarith
    exact tendsto_atTop_mono (fun z => norm_sq_add_conj_ge c z) h2
  have hpoly : Tendsto (fun z : ℂ => z ^ 2 + (starRingEnd ℂ) c) (Filter.cocompact ℂ)
      (Filter.cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact] at hnorm ⊢
    exact tendsto_norm_atTop_iff_cobounded.mp hnorm
  have hA : Tendsto (fun z : ℂ => Work.Bottcher.bottcher ((starRingEnd ℂ) c)
      (z ^ 2 + (starRingEnd ℂ) c) / (z ^ 2 + (starRingEnd ℂ) c)) (Filter.cocompact ℂ)
      (nhds 1) := (bottcher_tendsto_atTop ((starRingEnd ℂ) c)).comp hpoly
  have hB : Tendsto (fun z : ℂ => (z ^ 2 + (starRingEnd ℂ) c) / z ^ 2) (Filter.cocompact ℂ)
      (nhds 1) := by
    have h0 : Tendsto (fun z : ℂ => (starRingEnd ℂ) c / z ^ 2) (Filter.cocompact ℂ) (nhds 0) := by
      have h := Work.Bottcher.Series.tendsto_div_pow_cobounded ((starRingEnd ℂ) c) (k := 2)
        (by norm_num)
      rwa [Metric.cobounded_eq_cocompact] at h
    have h1 : Tendsto (fun z : ℂ => 1 + (starRingEnd ℂ) c / z ^ 2) (Filter.cocompact ℂ)
        (nhds 1) := by
      simpa using h0.const_add 1
    refine h1.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    field_simp
  have hC : Tendsto (fun z : ℂ => z ^ 2 / (Work.Bottcher.bottcher c z) ^ 2) (Filter.cocompact ℂ)
      (nhds 1) := by
    have hb : Tendsto (fun z : ℂ => (Work.Bottcher.bottcher c z / z)⁻¹) (Filter.cocompact ℂ)
        (nhds (1 : ℂ)) := by
      simpa using (bottcher_tendsto_atTop c).inv₀ (by norm_num : (1 : ℂ) ≠ 0)
    have h2 := hb.pow 2
    simpa [inv_div, div_pow, inv_pow] using h2
  have hprod : Tendsto (fun z : ℂ => Work.Bottcher.bottcher ((starRingEnd ℂ) c)
        (z ^ 2 + (starRingEnd ℂ) c) / (z ^ 2 + (starRingEnd ℂ) c)
        * ((z ^ 2 + (starRingEnd ℂ) c) / z ^ 2)
        * (z ^ 2 / (Work.Bottcher.bottcher c z) ^ 2)) (Filter.cocompact ℂ) (nhds 1) := by
    have h := (hA.mul hB).mul hC
    simpa using h
  refine hprod.congr' ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (max 2 (‖c‖ + 1)))] with z hz
  have hz2 : (2 : ℝ) ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hzc : ‖c‖ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz2
    linarith
  have hw0 : z ^ 2 + (starRingEnd ℂ) c ≠ 0 := by
    intro h
    have h1 : ‖z ^ 2 + (starRingEnd ℂ) c‖ = 0 := by rw [h, norm_zero]
    have h2 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖z ^ 2 + (starRingEnd ℂ) c‖ := norm_sq_add_conj_ge c z
    have h3 : ‖c‖ ≤ ‖z‖ * (‖z‖ - 1) := by nlinarith [norm_nonneg c, norm_nonneg z]
    nlinarith [norm_nonneg z]
  have hb0 : Work.Bottcher.bottcher c z ≠ 0 := Work.Bottcher.bottcher_ne_zero c hz0
  field_simp

/-- An analytic function of constant modulus `1` on an open preconnected set is constant. -/
private lemma eq_const_of_norm_eq_one {U : Set ℂ} {f : ℂ → ℂ} (hUo : IsOpen U)
    (hUp : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U) (h1 : ∀ z ∈ U, ‖f z‖ = 1) :
    ∃ c : ℂ, ∀ z ∈ U, f z = c := by
  rcases hf.is_constant_or_isOpen hUp with hconst | hopen
  · exact hconst
  · by_cases hne : U.Nonempty
    · exfalso
      obtain ⟨z₀, hz₀⟩ := hne
      have himg : IsOpen (f '' U) := hopen U (subset_refl U) hUo
      have hzimg : f z₀ ∈ f '' U := ⟨z₀, hz₀, rfl⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg (f z₀) hzimg
      have hy : (f z₀ * (1 + ((ε / 2 : ℝ) : ℂ))) ∈ Metric.ball (f z₀) ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : f z₀ * (1 + ((ε / 2 : ℝ) : ℂ)) - f z₀ = f z₀ * ((ε / 2 : ℝ) : ℂ) := by ring
        rw [hsub, norm_mul, h1 z₀ hz₀, one_mul, norm_ofReal', abs_of_nonneg (by linarith)]
        linarith
      obtain ⟨w, hwU, hwy⟩ := hball hy
      have hw1 := h1 w hwU
      rw [hwy] at hw1
      have hsplit : ‖f z₀ * (1 + ((ε / 2 : ℝ) : ℂ))‖ = 1 * (1 + ε / 2) := by
        rw [norm_mul, h1 z₀ hz₀]
        congr 1
        rw [show (1 : ℂ) + ((ε / 2 : ℝ) : ℂ) = ((1 + ε / 2 : ℝ) : ℂ) by push_cast; ring,
          norm_ofReal', abs_of_nonneg (by linarith)]
      rw [hsplit, one_mul] at hw1
      linarith
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩

private lemma continuous_Tantibar (c : ℂ) : Continuous (Tantibar c) :=
  (Complex.continuous_conj.pow 2).add continuous_const

/-! ## The Böttcher equation on the far region -/

/-- **The Böttcher equation of the tricorn on the far region**: for `‖z‖ ≥ escapeRadius c` the
product formula satisfies `φ_c (T_c z) = conj (φ_c z)²`. -/
theorem bottcher_comm_Tantibar_far (c z : ℂ) (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    Work.Bottcher.bottcher c (LeanEval.ComplexAnalysis.Tantibar c z)
      = (starRingEnd ℂ) (Work.Bottcher.bottcher c z) ^ 2 := by
  set F : ℂ → ℂ := fun w => Work.Bottcher.bottcher ((starRingEnd ℂ) c) (w ^ 2 + (starRingEnd ℂ) c)
      / (Work.Bottcher.bottcher c w) ^ 2 with hF
  have hF_an : AnalyticOnNhd ℂ F {w : ℂ | Work.Bottcher.escapeRadius c < ‖w‖} := analyticAt_ratio c
  have hF_one : ∀ w ∈ {w : ℂ | Work.Bottcher.escapeRadius c < ‖w‖}, ‖F w‖ = 1 := by
    intro w hw
    exact norm_ratio c w (le_of_lt hw)
  obtain ⟨k, hk⟩ := eq_const_of_norm_eq_one (U := {w : ℂ | Work.Bottcher.escapeRadius c < ‖w‖})
    (isOpen_lt continuous_const continuous_norm)
    (Work.ParamRays.isPreconnected_lt_norm (escapeRadius_pos c).le) hF_an hF_one
  -- pin the constant: `k = 1`, using the limit at infinity along the positive real axis
  have hk1 : k = 1 := by
    set s : ℕ → ℂ := fun n => (((Work.Bottcher.escapeRadius c + 1 + n : ℝ)) : ℂ) with hs
    have hsn : Tendsto (fun n : ℕ => ‖s n‖) atTop atTop := by
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      refine tendsto_atTop_mono (fun n => ?_) hn
      have hR := escapeRadius_pos c
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      show (n : ℝ) ≤ ‖s n‖
      rw [hs, norm_ofReal', abs_of_nonneg (by linarith)]
      linarith
    have hst : Tendsto s atTop (Filter.cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_norm_atTop_iff_cobounded.mp hsn
    have hlim : Tendsto (fun n : ℕ => F (s n)) atTop (nhds 1) := (tendsto_ratio c).comp hst
    have hconst : (fun n : ℕ => F (s n)) = fun _ : ℕ => k := by
      funext n
      have hlt : Work.Bottcher.escapeRadius c < ‖s n‖ := by
        have hR := escapeRadius_pos c
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        rw [hs, norm_ofReal', abs_of_nonneg (by linarith)]
        linarith
      exact hk (s n) hlt
    rw [hconst] at hlim
    exact (tendsto_nhds_unique hlim tendsto_const_nhds).symm
  -- the identity on the open far region
  have hfar : ∀ w : ℂ, Work.Bottcher.escapeRadius c < ‖w‖ →
      Work.Bottcher.bottcher c (Tantibar c w)
        = (starRingEnd ℂ) (Work.Bottcher.bottcher c w) ^ 2 := by
    intro w hw
    have hwle : Work.Bottcher.escapeRadius c ≤ ‖w‖ := le_of_lt hw
    have hFw : Work.Bottcher.bottcher ((starRingEnd ℂ) c) (w ^ 2 + (starRingEnd ℂ) c)
        / (Work.Bottcher.bottcher c w) ^ 2 = 1 := hk1 ▸ hk w hw
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw
      linarith [escapeRadius_pos c]
    have hden : (Work.Bottcher.bottcher c w) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Work.Bottcher.bottcher_ne_zero c hw0)
    have hnum : Work.Bottcher.bottcher ((starRingEnd ℂ) c) (w ^ 2 + (starRingEnd ℂ) c)
        = (Work.Bottcher.bottcher c w) ^ 2 := (div_eq_one_iff_eq hden).mp hFw
    have hsym : (starRingEnd ℂ) (Work.Bottcher.bottcher c (Tantibar c w))
        = Work.Bottcher.bottcher ((starRingEnd ℂ) c) (w ^ 2 + (starRingEnd ℂ) c) := by
      rw [conj_bottcher_far c _ (escapeRadius_le_norm_Tantibar c hwle), conj_Tantibar]
    calc Work.Bottcher.bottcher c (Tantibar c w)
        = (starRingEnd ℂ) ((starRingEnd ℂ) (Work.Bottcher.bottcher c (Tantibar c w))) := by simp
      _ = (starRingEnd ℂ) (Work.Bottcher.bottcher ((starRingEnd ℂ) c)
            (w ^ 2 + (starRingEnd ℂ) c)) := by rw [hsym]
      _ = (starRingEnd ℂ) ((Work.Bottcher.bottcher c w) ^ 2) := by rw [hnum]
      _ = (starRingEnd ℂ) (Work.Bottcher.bottcher c w) ^ 2 := map_pow _ _ 2
  -- the closed region follows by continuity
  rcases lt_or_ge (Work.Bottcher.escapeRadius c) ‖z‖ with hlt | hge
  · exact hfar z hlt
  · have hzlt : ‖z‖ = Work.Bottcher.escapeRadius c := le_antisymm hge hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (escapeRadius_pos c) hz
    have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
    set s : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z with hs
    have hsnorm : ∀ n : ℕ, Work.Bottcher.escapeRadius c < ‖s n‖ := by
      intro n
      have h1 : (1 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      rw [hs, norm_mul, norm_ofReal', abs_of_pos (by linarith), hzlt]
      calc Work.Bottcher.escapeRadius c = 1 * Work.Bottcher.escapeRadius c := by ring
        _ < (1 + 1 / ((n : ℝ) + 1)) * Work.Bottcher.escapeRadius c :=
            mul_lt_mul_of_pos_right h1 (escapeRadius_pos c)
    have hst : Tendsto s atTop (nhds z) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1) : ℝ)) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.add h0
      have h2 : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (nhds 1) :=
        (Complex.continuous_ofReal.tendsto 1).comp h1
      simpa [hs] using h2.mul_const z
    have hTz : Work.Bottcher.escapeRadius c ≤ ‖Tantibar c z‖ :=
      escapeRadius_le_norm_Tantibar c hz
    have hφz : Tendsto (fun n : ℕ => Work.Bottcher.bottcher c (s n)) atTop
        (nhds (Work.Bottcher.bottcher c z)) :=
      (analyticAt_bottcher c z hz).continuousAt.tendsto.comp hst
    have h1t : Tendsto (fun n : ℕ => Work.Bottcher.bottcher c (Tantibar c (s n))) atTop
        (nhds (Work.Bottcher.bottcher c (Tantibar c z))) :=
      (analyticAt_bottcher c (Tantibar c z) hTz).continuousAt.tendsto.comp
        (((continuous_Tantibar c).tendsto z).comp hst)
    have h2t : Tendsto (fun n : ℕ => (starRingEnd ℂ) (Work.Bottcher.bottcher c (s n)) ^ 2) atTop
        (nhds ((starRingEnd ℂ) (Work.Bottcher.bottcher c z) ^ 2)) :=
      ((Complex.continuous_conj.tendsto (Work.Bottcher.bottcher c z)).comp hφz).pow 2
    have heq : (fun n : ℕ => Work.Bottcher.bottcher c (Tantibar c (s n)))
        = fun n : ℕ => (starRingEnd ℂ) (Work.Bottcher.bottcher c (s n)) ^ 2 :=
      funext (fun n => hfar (s n) (hsnorm n))
    exact tendsto_nhds_unique h1t
      (h2t.congr' (Eventually.of_forall (fun n => (congrFun heq n).symm)))

end Work.Bottcher.Core
