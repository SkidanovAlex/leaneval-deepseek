import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Summability of the Böttcher series

The Böttcher coordinate of the tricorn is defined by the product formula
`φ_c(z) = z ∏_n (p_c^n z / (p_c^n z)^4)^{4^{-(n+1)}}`, whose exponent series is

`bottcherSeries c z = Σ_n bottcherTerm c n z`,
`bottcherTerm c n z = 4^{-(n+1)} log (p_c (p_c^n z) / (p_c^n z)^4)`.

The main point of this file is that this series **converges** as soon as the
`T_c`-orbit of `z` diverges to infinity (`T_c w = conj w ^ 2 + c`): writing
`p_c = T_c ∘ T_c` (the monic quartic `pMap c`), the `n`-th `p_c`-iterate is the
`2n`-th `T_c`-iterate, so its norm tends to infinity; and once `‖w‖` is large the
normalised factor `normFactor c w = p_c w / w^4` is close to `1`, so that
`log (normFactor c w)` tends to `0`.  Hence `‖bottcherTerm c n z‖ ≤ 4^{-(n+1)}`
eventually, and comparison with the geometric series gives summability.

The only analytic input is the continuity of `Complex.log` at `1` (Mathlib's
`Complex.continuousAt_clog`, applicable since `1` lies in the slit plane) and the
explicit expansion

`normFactor c w = (1 + conj c / w^2)^2 + c / w^4`   (`w ≠ 0`),

which shows `normFactor c w → 1` as `‖w‖ → ∞`.
-/

open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Series

open Work.Bottcher

/-- At infinity, `w ↦ a / w ^ k` tends to `0` for every `a : ℂ` and `k ≥ 1`. -/
lemma tendsto_div_pow_cobounded (a : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun w : ℂ => a / w ^ k) (Bornology.cobounded ℂ) (𝓝 0) := by
  have hk0 : 0 < k := hk
  -- `‖w‖ ^ k → ∞`
  have hnorm : Tendsto (fun w : ℂ => ‖w ^ k‖) (Bornology.cobounded ℂ) atTop := by
    have h1 : Tendsto (fun w : ℂ => ‖w‖) (Bornology.cobounded ℂ) atTop :=
      tendsto_norm_cobounded_atTop
    have h2 : Tendsto (fun w : ℂ => ‖w‖ ^ k) (Bornology.cobounded ℂ) atTop :=
      tendsto_atTop_mono' _ (h1.eventually_ge_atTop 1 |>.mono fun w hw => by
        simpa using pow_le_pow_right₀ hw hk) h1
    simpa [norm_pow] using h2
  -- hence `(w ^ k)⁻¹ → 0`
  have hinv : Tendsto (fun w : ℂ => (w ^ k)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    have h3 : Tendsto (fun w : ℂ => w ^ k) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) :=
      (tendsto_norm_atTop_iff_cobounded (f := fun w : ℂ => w ^ k)).mp hnorm
    simpa only [Function.comp_def] using (Filter.tendsto_inv₀_cobounded (α := ℂ)).comp h3
  simpa [div_eq_mul_inv] using hinv.const_mul a

/-- The normalised Böttcher factor `normFactor c w = p_c w / w^4` tends to `1` as
`‖w‖ → ∞`.  Indeed, for `w ≠ 0`,
`normFactor c w = (1 + conj c / w^2)^2 + c / w^4`, and both correction terms vanish
at infinity. -/
lemma tendsto_normFactor_atCobounded (c : ℂ) :
    Tendsto (fun w : ℂ => normFactor c w) (Bornology.cobounded ℂ) (𝓝 1) := by
  have hev : (fun w : ℂ => normFactor c w) =ᶠ[Bornology.cobounded ℂ]
      (fun w : ℂ => (1 + conj c / w ^ 2) ^ 2 + c / w ^ 4) := by
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_ge_atTop 1] with w hw
    have hw0 : w ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hw
      linarith
    rw [normFactor, pMap]
    field_simp
  have h1 : Tendsto (fun w : ℂ => (1 : ℂ) + conj c / w ^ 2) (Bornology.cobounded ℂ)
      (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_div_pow_cobounded (conj c) (k := 2) (by norm_num))
  have h2 : Tendsto (fun w : ℂ => (1 + conj c / w ^ 2) ^ 2 + c / w ^ 4)
      (Bornology.cobounded ℂ) (𝓝 1) := by
    have h2' : Tendsto (fun w : ℂ => (1 + conj c / w ^ 2) ^ 2 + c / w ^ 4)
        (Bornology.cobounded ℂ) (𝓝 ((1 + 0) ^ 2 + 0)) :=
      (h1.pow 2).add (tendsto_div_pow_cobounded c (k := 4) (by norm_num))
    simpa using h2'
  exact h2.congr' hev.symm

/-- The logarithm of the normalised Böttcher factor tends to `0` at infinity, by
continuity of `Complex.log` at `1 ∈ slitPlane` and `Complex.log 1 = 0`. -/
lemma tendsto_log_normFactor_atCobounded (c : ℂ) :
    Tendsto (fun w : ℂ => Complex.log (normFactor c w)) (Bornology.cobounded ℂ) (𝓝 0) := by
  have h := (tendsto_normFactor_atCobounded c).clog Complex.one_mem_slitPlane
  simpa using h

theorem summable_bottcherTerm (c z : ℂ)
    (h : Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖)
      Filter.atTop Filter.atTop) :
    Summable (fun n : ℕ => Work.Bottcher.bottcherTerm c n z) := by
  -- The `p_c`-orbit of `z` (the even `T_c`-iterates) also diverges to infinity.
  have hpm : Tendsto (fun n : ℕ => ‖(pMap c)^[n] z‖) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨M, hM⟩ := eventually_atTop.mp (h.eventually (eventually_ge_atTop b))
    refine ⟨M, fun n hn => ?_⟩
    rw [pMap_iterate]
    exact hM (2 * n) (le_trans hn (by omega))
  have hcob : Tendsto (fun n : ℕ => (pMap c)^[n] z) atTop (Bornology.cobounded ℂ) :=
    (tendsto_norm_atTop_iff_cobounded (f := fun n : ℕ => (pMap c)^[n] z)).mp hpm
  -- Hence `log (normFactor c (p_c^n z)) → 0`.
  have hlog : Tendsto (fun n : ℕ => Complex.log (normFactor c ((pMap c)^[n] z))) atTop (𝓝 0) :=
    (tendsto_log_normFactor_atCobounded c).comp hcob
  have hev : ∀ᶠ n : ℕ in atTop, ‖Complex.log (normFactor c ((pMap c)^[n] z))‖ ≤ 1 := by
    have h0 := tendsto_zero_iff_norm_tendsto_zero.mp hlog
    filter_upwards [h0.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    exact le_of_lt hn
  -- Compare the terms with the geometric series `Σ 4^{-(n+1)}`.
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) ?_ ?_
  · have h0 : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa [pow_succ] using h0.mul_right (1 / 4 : ℝ)
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with n hn
    rw [bottcherTerm, norm_mul]
    have hnorm : ‖((1 / 4 : ℝ) ^ (n + 1) : ℂ)‖ = (1 / 4 : ℝ) ^ (n + 1) := by simp
    rw [hnorm]
    calc (1 / 4 : ℝ) ^ (n + 1) * ‖Complex.log (normFactor c ((pMap c)^[n] z))‖
        ≤ (1 / 4 : ℝ) ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = (1 / 4 : ℝ) ^ (n + 1) := mul_one _

end Work.Bottcher.Series
