import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT_Aux
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.diffDzd_ampA_mul_L12f_open
import Submission.Work.FTS.StrongEps.EpsRLX.RadBound.radA_dzdIter_expansion_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_jet_small
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.radA_jet_big

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

/-! ## The two one-dimensional reductions

With `w z = (1+z)²/z²` one has `z·(m·w z)² = m²·(1+z)^4/z³`, so a jet bound
`|m| ≤ K z²` near `0` (resp. `|m| ≤ K/z` at `∞`) gives the two boundary traces.  These are the
two elementary facts that turn a jet estimate on `radA α x` into the trace conclusion. -/

/-- **The trace at `z → 0⁺` from a quadratic jet bound.**  If `|f z| ≤ K z²` on `(0,1)` then
`z·(f z·w z)² → 0` as `z → 0⁺` (the bound is `≤ 16 K² z`). -/
theorem tendsto_z_mul_w_sq_small {f : ℝ → ℝ} {K : ℝ}
    (h : ∀ z : ℝ, 0 < z → z < 1 → |f z| ≤ K * z ^ 2) :
    Filter.Tendsto (fun z : ℝ => z * (f z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hdom : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 * z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 * z) (nhds (0 : ℝ))
        (nhds (16 * K ^ 2 * 0)) := tendsto_const_nhds.mul Filter.tendsto_id
    rw [mul_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact mul_nonneg hz.le (sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with z hz
    obtain ⟨hz0, hz1⟩ := hz
    have hf2 : (f z) ^ 2 ≤ (K * z ^ 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h z hz0 hz1) 2
    have hw2 : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
      rw [Work.Spaces.w]
      field_simp
    calc z * (f z * Work.Spaces.w z) ^ 2
        = z * (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [mul_pow]; ring
      _ ≤ z * (K * z ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 hz0.le) (sq_nonneg _)
      _ = K ^ 2 * z ^ 5 * ((1 + z) ^ 4 / z ^ 4) := by rw [hw2]; ring
      _ = K ^ 2 * z * (1 + z) ^ 4 := by field_simp
      _ ≤ K ^ 2 * z * 16 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg K) hz0.le)
          have h1z : 1 + z ≤ 2 := by linarith
          have h0z : (0 : ℝ) ≤ 1 + z := by linarith
          have hb := pow_le_pow_left₀ h0z h1z 4
          norm_num at hb
          exact hb
      _ = 16 * K ^ 2 * z := by ring

/-- **The trace at `z → ∞` from a `1/z` jet bound.**  If `|f z| ≤ K/z` on `[1,∞)` then
`z·(f z·w z)² → 0` as `z → ∞` (the bound is `≤ 16 K²/z`, using `w z ≤ 4` there). -/
theorem tendsto_z_mul_w_sq_big {f : ℝ → ℝ} {K : ℝ}
    (h : ∀ z : ℝ, 1 ≤ z → |f z| ≤ K / z) :
    Filter.Tendsto (fun z : ℝ => z * (f z * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0) := by
  have hdom : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 / z) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun z : ℝ => 16 * K ^ 2 * z⁻¹) Filter.atTop
        (nhds (16 * K ^ 2 * 0)) :=
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (16 * K ^ 2)
    rw [mul_zero] at h1
    refine h1.congr' (Filter.Eventually.of_forall fun z => ?_)
    show 16 * K ^ 2 * z⁻¹ = 16 * K ^ 2 / z
    rw [div_eq_mul_inv]
  refine squeeze_zero' ?_ ?_ hdom
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hf2 : (f z) ^ 2 ≤ (K / z) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h z hz) 2
    have hw2 : (Work.Spaces.w z) ^ 2 ≤ 16 := by
      have hzw : (1 + z) / z ≤ 2 := by
        rw [div_le_iff₀ hz0]
        linarith
      have h0 : (0 : ℝ) ≤ (1 + z) / z := by positivity
      calc (Work.Spaces.w z) ^ 2 = ((1 + z) / z) ^ 4 := by
            rw [Work.Spaces.w]
            field_simp
        _ ≤ 2 ^ 4 := pow_le_pow_left₀ h0 hzw 4
        _ = 16 := by norm_num
    calc z * (f z * Work.Spaces.w z) ^ 2
        = z * (f z) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [mul_pow]; ring
      _ ≤ z * (K / z) ^ 2 * 16 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hf2 hz0.le) hw2 (sq_nonneg _) ?_
          exact mul_nonneg hz0.le (sq_nonneg _)
      _ = 16 * K ^ 2 / z := by field_simp

/-- **The radial trace hypotheses for the transfer profile `radA α x`.**

`radA α x z = −ampA α z·L₁₂(x)(z) + (ampB α z/c α)·L₁₂(Transport x)(0)` with
`ampA α z = 2z/(c α (1+z)²)`, `ampB α z = 2z²/(1+z)³` (`Transfer/Profiles.lean`); these are
exactly the two hypotheses that `TracesAux.BdryTraces_Gam_mul_rad` consumes in order to
conclude `BdryTraces α 4 (Corr α x)` from `Corr α x = Γ(θ)·radA α x (z)`
(`Transfer.Corr_eq_radA`).

Proof ingredients (all available: `regQo_LGammaT_Aux` + the tree):

* treat the two summands `r₁ = −ampA·L₁₂ x` and `r₂ = (ampB/c α)·L₁₂(Transport x)(0)`
  separately, so no additivity of `DzdIter` is needed: the two conclusions combine by
  `(x+y)² ≤ 2x²+2y²`;
* `DzdIter b (ampA·L₁₂ x) = Σ_{l≤b} C(b,l)·(DzdIter l ampA)·(DzdIter (b−l) L₁₂ x)` on `z > 0`
  (`OpenPkg.ProdOpen.leibniz_open_mixed` applied to the `SmoothOpen` factors `ampA α` and
  `L₁₂ x`; `Aux.L12f_eq_elliptic` identifies `Work.Coercivity.L12f x` with
  `Work.Elliptic.L12`);
* `|DzdIter m (L₁₂ x) z| ≤ D₀ z^{3/2}` on `(0,1)` (`Aux.DzdIter_L12f_small`, from the tower
  `DzdIter (k+1) (L₁₂ x) = −Qang x k` of `OpenPkg.l12_open_bundle` together with `hQ`),
  and `|DzdIter m (L₁₂ x) z| ≤ D₁` for every `z > 0` (`Aux.DzdIter_L12f_bdd`, which is where
  `ClassC` — via `classC_mixed_sup_le_four` — is used);
* `|DzdIter l (ampA α) z| ≤ K_l·z/(1+z)²` (`hA`), hence `≤ K_l·min(z,1/z)`;
* `|DzdIter b (ampB α) z| ≤ D·z²/(1+z)³` (`Aux.DzdIter_ampB_bdd`, from `ClassCRHS.DzBoundR0`),
  and scalar multiples of `ampB` are handled by `Aux.DzdIter_const_mul`;
* finally `z·(m·w)² = m²(1+z)^4/z³` (`w z = (1+z)²/z²`), so it suffices that the jets are
  `O(z²)` near `0` and `O(1/z)` at `∞`; the two polynomial limit lemmas needed here are
  private to the prover (they are not yet in `Aux`). -/
theorem radA_traces {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2))
    (hA : ∀ b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z|
        ≤ K * (z / (1 + z) ^ 2)) :
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.radA α x) z
        * Work.Spaces.w z) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
      (fun z : ℝ => z * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.radA α x) z
        * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0)) := by
  -- the two jet estimates on `radA α x` (delegated, proved in the sibling modules)
  obtain ⟨K₁, -, h₁⟩ := radA_jet_small hα hx hC hQ hA
  obtain ⟨K₂, -, h₂⟩ := radA_jet_big hα hx hC hQ hA
  -- `O(z²)` at `0⁺` gives the trace at `0⁺`, `O(1/z)` at `∞` the trace at `∞`
  exact ⟨fun b hb => tendsto_z_mul_w_sq_small (h₁ b hb),
    fun b hb => tendsto_z_mul_w_sq_big (h₂ b hb)⟩

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
