import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.analyticOnNhd_bExp
import Submission.Work.Bottcher.Contraction.bExp_re
import Submission.Work.Bottcher.Contraction.tendsto_bExp
import Submission.Work.Bottcher.Contraction.tendsto_fourPow_inv_log_norm_pMap_iterate
import Submission.Work.Bottcher.Contraction.exists_analyticBottcher_of_mem_mandelbar
import Submission.Work.Bottcher.Contraction.exists_analytic_log_normFactor_of_CritDomain
import Submission.Work.Bottcher.Critical.CritDomain_escapes
import Submission.Work.Bottcher.Contraction.bExp_re_CritDomain
import Submission.Work.Bottcher.Contraction.analyticOnNhd_bExp_CritDomain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open Filter Function
open scoped Topology

/-! ## Elementary facts about the critical domain

`CritDomain c = {z | green c z > green c 0}` is the domain on which the Böttcher coordinate is
the true one.  Because `green c 0 ≥ 0`, points of `CritDomain c` have positive Green function, so
their orbits escape and the whole escape-set theory applies to them.  This section collects those
elementary translations, needed before the series
`S z = ∑_k 4^{-(k+1)} L ((p_c)^[k] z)` can be manipulated on `CritDomain c`. -/

/-- Points of the critical domain have positive Green function (because `greenParam c ≥ 0`). -/
theorem green_pos_of_mem_CritDomain (c : ℂ) {z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) :
    0 < Work.Bottcher.green c z := by
  have h0 : (0 : ℝ) ≤ Work.Bottcher.green c 0 := Work.Bottcher.Green.green_nonneg c 0
  rw [Work.Bottcher.mem_CritDomain, Work.Bottcher.greenParam_def] at hz
  linarith

/-- Points of the critical domain are nonzero (the critical point `0` itself is not in
`CritDomain c`). -/
theorem ne_zero_of_mem_CritDomain (c : ℂ) {z : ℂ} (hz : z ∈ Work.Bottcher.CritDomain c) :
    z ≠ 0 := fun h => Work.Bottcher.CritBasic.zero_notMem_CritDomain c (h ▸ hz)

/-- The `p_c`-orbit of a point of the critical domain tends to infinity. -/
theorem tendsto_iterate_pMap_cocompact_of_mem_CritDomain (c : ℂ) {z : ℂ}
    (hz : z ∈ Work.Bottcher.CritDomain c) :
    Tendsto (fun k : ℕ => (Work.Bottcher.pMap c)^[k] z) atTop (cocompact ℂ) := by
  have hT : Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) atTop atTop :=
    Work.Bottcher.Critical.CritDomain_escapes c z hz
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have hnorm : Tendsto (fun k : ℕ => ‖(Work.Bottcher.pMap c)^[k] z‖) atTop atTop := by
    refine (hT.comp h2).congr' (Eventually.of_forall (fun k => ?_))
    simp only [Function.comp_apply]
    rw [Work.Bottcher.pMap_iterate]
  exact tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa using hnorm)

/-! ## The Böttcher exponent series on the critical domain -/

/-- The terms of the Böttcher exponent series are summable at a point of the critical domain, as
soon as `L → 0` at infinity. -/
theorem summable_bExp_terms_CritDomain (c : ℂ) {L : ℂ → ℂ}
    (hLt : Tendsto L (cocompact ℂ) (nhds (0 : ℂ))) {z : ℂ}
    (hz : z ∈ Work.Bottcher.CritDomain c) :
    Summable (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) := by
  have hbdd : ∀ᶠ w : ℂ in cocompact ℂ, ‖L w‖ ≤ 1 := by
    have h0 : Tendsto (fun w : ℂ => ‖L w‖) (cocompact ℂ) (nhds (0 : ℝ)) := by
      simpa using hLt.norm
    exact h0.eventually (eventually_le_nhds zero_lt_one)
  have hkle : ∀ᶠ k : ℕ in atTop, ‖L ((Work.Bottcher.pMap c)^[k] z)‖ ≤ 1 :=
    (tendsto_iterate_pMap_cocompact_of_mem_CritDomain c hz).eventually hbdd
  refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (1 / 4 : ℝ) ^ k)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)) ?_
  filter_upwards [hkle] with k hk
  have hcoef : ‖(((1 / 4 : ℝ) ^ (k + 1) : ℂ))‖ = (1 / 4 : ℝ) ^ (k + 1) := by
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_mul, hcoef]
  have hmono : (1 / 4 : ℝ) ^ (k + 1) ≤ (1 / 4 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  calc (1 / 4 : ℝ) ^ (k + 1) * ‖L ((Work.Bottcher.pMap c)^[k] z)‖
      ≤ (1 / 4 : ℝ) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (1 / 4 : ℝ) ^ (k + 1) := mul_one _
    _ ≤ (1 / 4 : ℝ) ^ k := hmono

/-- **The shift identity on the critical domain**: the exponent series of `p_c z` is `4 S z - L z`
for `z ∈ CritDomain c`.  This is exactly the statement that `φ = z * exp S` solves the Böttcher
equation of the quartic `p_c`. -/
theorem bExp_shift_CritDomain (c : ℂ) {L : ℂ → ℂ}
    (hLt : Tendsto L (cocompact ℂ) (nhds (0 : ℂ))) {z : ℂ}
    (hz : z ∈ Work.Bottcher.CritDomain c) :
    bExp c L (Work.Bottcher.pMap c z) = 4 * bExp c L z - L z := by
  classical
  set F : ℕ → ℂ := fun k => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z) with hF
  have hsum : Summable F := summable_bExp_terms_CritDomain c hLt hz
  have hz1 : Work.Bottcher.pMap c z ∈ Work.Bottcher.CritDomain c :=
    Work.Bottcher.CritBasic.pMap_mem_CritDomain hz
  have hsum1 : Summable (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) *
      L ((Work.Bottcher.pMap c)^[k] (Work.Bottcher.pMap c z))) :=
    summable_bExp_terms_CritDomain c hLt hz1
  have hcoe : ∀ k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) = 4 * ((1 / 4 : ℝ) ^ (k + 2) : ℂ) := by
    intro k
    rw [pow_succ]
    push_cast
    ring
  have hleft : bExp c L (Work.Bottcher.pMap c z) = 4 * (∑' k : ℕ, F (k + 1)) := by
    rw [bExp_def]
    have hfun : (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) *
          L ((Work.Bottcher.pMap c)^[k] (Work.Bottcher.pMap c z)))
        = fun k : ℕ => 4 * F (k + 1) := by
      funext k
      rw [hF, ← Function.iterate_succ_apply]
      rw [hcoe k]
      ring
    rw [hfun, tsum_mul_left]
  have htail : (∑' k : ℕ, F (k + 1)) = bExp c L z - F 0 := by
    have h := hsum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    have h' : (∑' k : ℕ, F (k + 1)) = (∑' k : ℕ, F k) - F 0 := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact h
    rw [bExp_def]
    rw [show (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) = F from
      (funext fun k => by rw [hF])]
    exact h'
  rw [hleft, htail, hF]
  simp only [Function.iterate_zero_apply]
  push_cast
  ring

end Work.Bottcher.Contraction

namespace Work.Bottcher.Contraction

open Filter Function
open scoped Topology

/--
Generalises `Work.Bottcher.Contraction.exists_analyticBottcher_of_mem_mandelbar` (there:
`c ∈ M*`, domain `EscapeSet c = {G_c > 0}`) to an arbitrary parameter and the critical domain
`CritDomain c = {G_c > G_c 0}`.

Assume the sublevel set `{z | green c z ≤ greenParam c}` is preconnected (true for every `c` by
`Work.Bottcher.Contraction.isPreconnected_green_le_greenParam`).  Then the holomorphic quartic
`p_c = T_c ∘ T_c` has an analytic Böttcher coordinate `φ` on `CritDomain c`:

`φ` analytic on `CritDomain c`, `φ ∘ p_c = φ^4` and `‖φ z‖ = exp (G_c z)` on `CritDomain c`, and
`φ z / z → 1` at infinity.

Construction: copy `exists_analyticBottcher_of_mem_mandelbar`, replacing `EscapeSet c` by
`CritDomain c` and `0 < green c z` by `z ∈ CritDomain c` throughout.  Let `L` be the holomorphic
logarithm of `pMap c z / z^4` from
`Work.Bottcher.Contraction.exists_analytic_log_normFactor_of_CritDomain c hK` (analytic on
`CritDomain c`, `exp (L z) = pMap c z / z^4` there, `L → 0` at infinity), put
`S z := ∑'_k 4^{-(k+1)} L ((pMap c)^[k] z)` (the `bExp c L z` of that file) and
`φ z := z · exp (S z)`.

* analyticity of `S`: the existing `Work.Bottcher.Contraction.analyticOnNhd_bExp` only covers
  `EscapeSet c`; prove the `CritDomain c` version: at `z₀ ∈ CritDomain c` take the open
  neighbourhood `U := {z | (green c z₀ + greenParam c)/2 < green c z} ⊆ CritDomain c`, which is
  `p_c`-invariant up to the factor `4^k` (`Work.Bottcher.CritBasic.green_pMap_four` /
  `CritBasic.pMap_iterate_mem_CritDomain`), and dominate the series on `U` by
  `Σ 4^{-(k+1)} · sup ‖L‖` over the closed set
  `{(green c z₀ + greenParam c)/2 ≤ green c z}`, where `L` is continuous (it is continuous on
  `CritDomain c`, and that closed set is contained in `CritDomain c`);
* `φ ∘ p_c = φ^4`: the shift identity `S (p_c z) = 4 S z - L z`, exactly as
  `Work.Bottcher.Contraction.bExp_shift` (whose proof uses only `z ∈ CritDomain c`, the identity
  `exp (L z) = pMap c z / z^4`, and the summability `summable_bExp_terms`);
* modulus: the real-part identity `(S z).re = green c z - log ‖z‖`, proved as
  `Work.Bottcher.Contraction.bExp_re` but with its `hc0 : green c 0 = 0` hypothesis replaced by
  `Work.Bottcher.CritBasic.normFactor_ne_zero_of_mem_CritDomain` (the only use of `hc0` there is
  non-vanishing of the `pMap`-iterates, which follows from
  `CritBasic.pMap_iterate_mem_CritDomain`), and the telescoping limit
  `Work.Bottcher.Contraction.tendsto_fourPow_inv_log_norm_pMap_iterate`;
* tangency: `S → 0` at infinity by `Work.Bottcher.Contraction.tendsto_bExp` (needs only
  `L → 0`), so `φ z / z = exp (S z) → 1`.
-/
theorem exists_analyticBottcher_of_CritDomain (c : ℂ)
    (hK : IsPreconnected {z : ℂ | Work.Bottcher.green c z ≤ Work.Bottcher.greenParam c}) :
    ∃ φ : ℂ → ℂ,
      AnalyticOnNhd ℂ φ (Work.Bottcher.CritDomain c) ∧
        (∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
          φ (Work.Bottcher.pMap c z) = (φ z) ^ 4) ∧
        (∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
          ‖φ z‖ = Real.exp (Work.Bottcher.green c z)) ∧
        Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  obtain ⟨L, hLan, hLexp, hLt⟩ := exists_analytic_log_normFactor_of_CritDomain c hK
  have hLexp' : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4 := by
    intro z hz
    rw [hLexp z hz, Work.Bottcher.normFactor]
  refine ⟨fun z => z * Complex.exp (bExp c L z), ?_, ?_, ?_, ?_⟩
  · exact analyticOnNhd_id.mul (analyticOnNhd_bExp_CritDomain c hLan hLt).cexp
  · intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_CritDomain c hz
    have hpc : Work.Bottcher.pMap c z ≠ 0 :=
      ne_zero_of_mem_CritDomain c (Work.Bottcher.CritBasic.pMap_mem_CritDomain hz)
    have hLz := hLexp' z hz
    have hS := bExp_shift_CritDomain c hLt hz
    have hexp4 : Complex.exp (4 * bExp c L z) = Complex.exp (bExp c L z) ^ 4 := by
      simpa using (Complex.exp_nat_mul (bExp c L z) 4)
    calc (Work.Bottcher.pMap c z) * Complex.exp (bExp c L (Work.Bottcher.pMap c z))
        = (Work.Bottcher.pMap c z) * Complex.exp (4 * bExp c L z - L z) := by rw [hS]
      _ = (Work.Bottcher.pMap c z) * (Complex.exp (bExp c L z) ^ 4 / Complex.exp (L z)) := by
          rw [Complex.exp_sub, hexp4]
      _ = (Work.Bottcher.pMap c z)
            * (Complex.exp (bExp c L z) ^ 4 / (Work.Bottcher.pMap c z / z ^ 4)) := by rw [hLz]
      _ = (z * Complex.exp (bExp c L z)) ^ 4 := by
          field_simp
  · intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_CritDomain c hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hre : (bExp c L z).re = Work.Bottcher.green c z - Real.log ‖z‖ :=
      bExp_re_CritDomain c hLan hLexp hLt hz
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_sub, Real.exp_log hzpos]
    field_simp
  · have h1' : Tendsto (fun z : ℂ => Complex.exp (bExp c L z)) (cocompact ℂ) (nhds 1) := by
      have h := (tendsto_bExp c hLt).cexp
      simpa only [bExp_def, Complex.exp_zero] using h
    refine h1'.congr' ?_
    have hne : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
      refine Filter.mem_cocompact.2 ⟨{0}, isCompact_singleton, ?_⟩
      intro z hz
      simpa using hz
    filter_upwards [hne] with z hz
    field_simp

end Work.Bottcher.Contraction
