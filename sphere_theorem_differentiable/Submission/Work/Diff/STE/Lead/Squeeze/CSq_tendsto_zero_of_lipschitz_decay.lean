import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.tendsto_tail_piFinset_wt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq k (b σ) → 0` as `σ → t` along `s`, from a Lipschitz bound and uniform weighted decay

Layer A of the STE development (the Fourier/Sobolev toolkit on the torus, `Torus.lean`).

Let `b : ℝ → (ι → ℤ) → ℂ` be a time-dependent family of coefficient families on the lattice
`ℤ^ι`, let `s : Set ℝ`, `t : ℝ`, and assume

* `hbd` : `‖b σ μ‖ ≤ L |σ - t|` for `σ ∈ s` (a Lipschitz-type bound vanishing at `σ = t`), and
* `hdec` : for every `M` there is `C ≥ 0` with `‖b σ μ‖ * ⟨μ⟩^M ≤ C` for all `σ ∈ s`, `μ`
  (uniform weighted decay, faster than any power of the weight `⟨μ⟩² = wt μ`).

Then the weighted `ℓ²` masses `CSq k (b σ) = Σ_μ ⟨μ⟩^k ‖b σ μ‖²` tend to `0` along
`nhdsWithin t s`.

This is the "Lipschitz continuity of the coefficients" input of
`Work.Diff.STE.Lead.BNorm_continuous_of_coeff_lipschitz`: the decay hypothesis upgrades the
pointwise (in frequency) convergence of the coefficients to the convergence of the whole
weighted `ℓ²` norm.

## Proof

Squeeze the summands by an explicit summable dominating family and apply Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`):

* choose `N` with `card ι < 2N`; then `⟨·⟩^{-N}` is summable on `ℤ^ι`
  (`Work.Diff.STE.summable_wt_zpow`);
* the decay hypothesis at level `M = k + N` gives `‖b σ μ‖ ≤ C ⟨μ⟩^{-(k+N)}`, hence
  `⟨μ⟩^k ‖b σ μ‖² ≤ C² ⟨μ⟩^{-N}`, uniformly in `σ ∈ s`;
* each summand tends to `0` along `nhdsWithin t s`, because `‖b σ μ‖ ≤ L|σ - t| → 0`.
-/

noncomputable section

namespace Work.Diff.STE.Lead.Squeeze

/-- The exponent arithmetic of the domination: for `a ≥ 1`, `z ≥ 0` with `z * a^M ≤ C` and
`k + N ≤ 2 M`, one has `a^k z² ≤ C² a^{-N}`.

(Since `a ≥ 1`, larger exponents give larger values, and `k - 2M ≤ -N`.) -/
private lemma wt_pow_mul_zpow_sq_le_aux {a C z : ℝ} {k M N : ℕ} (ha : 1 ≤ a) (hz0 : 0 ≤ z)
    (hz : z * a ^ M ≤ C) (hkN : k + N ≤ 2 * M) :
    a ^ k * z ^ 2 ≤ C ^ 2 * a ^ (-(N : ℤ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hane : a ≠ 0 := ne_of_gt ha0
  -- `z ≤ C a^{-M}`
  have hzle : z ≤ C * a ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ha0 M)).mpr hz
  have h1 : z ^ 2 ≤ (C * a ^ (-(M : ℤ))) ^ 2 := pow_le_pow_left₀ hz0 hzle 2
  have h2 : a ^ k * z ^ 2 ≤ a ^ k * (C * a ^ (-(M : ℤ))) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg ha0.le k)
  have h3 : a ^ k * (C * a ^ (-(M : ℤ))) ^ 2 = C ^ 2 * (a ^ k * (a ^ (-(M : ℤ))) ^ 2) := by
    rw [mul_pow]; ring
  have h4 : a ^ k * (a ^ (-(M : ℤ))) ^ 2 ≤ a ^ (-(N : ℤ)) := by
    have h5 : a ^ k * (a ^ (-(M : ℤ))) ^ 2 = a ^ ((k : ℤ) - 2 * (M : ℤ)) := by
      rw [← zpow_natCast (a := a) (n := k),
        show (a ^ (-(M : ℤ))) ^ 2 = (a ^ (-(M : ℤ))) ^ ((2 : ℤ)) from (zpow_natCast _ _).symm,
        ← zpow_mul, ← zpow_add₀ hane]
      congr 1
      ring
    rw [h5]
    exact zpow_le_zpow_right₀ ha (by omega)
  calc a ^ k * z ^ 2 ≤ a ^ k * (C * a ^ (-(M : ℤ))) ^ 2 := h2
    _ = C ^ 2 * (a ^ k * (a ^ (-(M : ℤ))) ^ 2) := h3
    _ ≤ C ^ 2 * a ^ (-(N : ℤ)) := mul_le_mul_of_nonneg_left h4 (sq_nonneg C)

theorem CSq_tendsto_zero_of_lipschitz_decay
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℝ → (ι → ℤ) → ℂ) (s : Set ℝ) (t : ℝ) (k : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hbd : ∀ σ ∈ s, ∀ μ : ι → ℤ, ‖b σ μ‖ ≤ L * |σ - t|)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ s, ∀ μ : ι → ℤ,
      ‖b σ μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C) :
    Filter.Tendsto (fun σ : ℝ => Work.Diff.STE.CSq k (b σ))
      (nhdsWithin t s) (nhds 0) := by
  classical
  -- the exponent of the dominating `p`-series
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card ι < 2 * N := ⟨Fintype.card ι + 1, by omega⟩
  have hsumN : Summable (fun μ : ι → ℤ => (Work.Diff.STE.wt μ) ^ (-(N : ℤ))) :=
    Work.Diff.STE.summable_wt_zpow N hN
  -- the decay hypothesis at level `k + N`
  obtain ⟨C, _hCnn, hC⟩ := hdec (k + N)
  -- the summands tend to `0` along the filter
  have hpt : ∀ μ : ι → ℤ, Filter.Tendsto
      (fun σ : ℝ => (Work.Diff.STE.wt μ) ^ k * ‖b σ μ‖ ^ 2)
      (nhdsWithin t s) (nhds 0) := by
    intro μ
    have hwtnn : (0 : ℝ) ≤ (Work.Diff.STE.wt μ) ^ k :=
      pow_nonneg (Work.Diff.STE.wt_pos μ).le k
    -- `|σ - t| → 0` along `𝓝[s] t`
    have habs : Filter.Tendsto (fun σ : ℝ => |σ - t|) (nhdsWithin t s) (nhds 0) := by
      have h1 : Filter.Tendsto (fun σ : ℝ => σ - t) (nhds t) (nhds (t - t)) :=
        (continuous_id.sub continuous_const).tendsto t
      have h2 : Filter.Tendsto (fun σ : ℝ => σ - t) (nhdsWithin t s) (nhds 0) := by
        simpa using tendsto_nhdsWithin_of_tendsto_nhds h1
      have h3 := (continuous_abs.tendsto 0).comp h2
      simpa [Function.comp_def] using h3
    -- the dominating function `⟨μ⟩^k (L |σ - t|)² → 0`
    have hg : Filter.Tendsto (fun σ : ℝ => (Work.Diff.STE.wt μ) ^ k * (L * |σ - t|) ^ 2)
        (nhdsWithin t s) (nhds 0) := by
      have h1 : Filter.Tendsto (fun σ : ℝ => L * |σ - t|) (nhdsWithin t s) (nhds (L * 0)) :=
        tendsto_const_nhds.mul habs
      have h2 : Filter.Tendsto (fun σ : ℝ => (L * |σ - t|) ^ 2) (nhdsWithin t s)
          (nhds ((L * 0) ^ 2)) := h1.pow 2
      have h3 : Filter.Tendsto (fun σ : ℝ => (Work.Diff.STE.wt μ) ^ k * (L * |σ - t|) ^ 2)
          (nhdsWithin t s) (nhds ((Work.Diff.STE.wt μ) ^ k * ((L * 0) ^ 2))) :=
        tendsto_const_nhds.mul h2
      simpa using h3
    refine squeeze_zero' (Filter.Eventually.of_forall fun σ =>
      mul_nonneg hwtnn (sq_nonneg _)) ?_ hg
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hb := hbd σ hσ μ
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hb 2) hwtnn
  -- the uniform summable domination
  have hbd2 : ∀ᶠ σ in nhdsWithin t s, ∀ μ : ι → ℤ,
      ‖(Work.Diff.STE.wt μ) ^ k * ‖b σ μ‖ ^ 2‖
        ≤ C ^ 2 * (Work.Diff.STE.wt μ) ^ (-(N : ℤ)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ μ
    rw [Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos μ).le k) (sq_nonneg _))]
    exact wt_pow_mul_zpow_sq_le_aux (Work.Diff.STE.wt_one_le μ) (norm_nonneg _)
      (hC σ hσ μ) (by omega)
  -- Tannery's theorem
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := nhdsWithin t s)
    (f := fun (σ : ℝ) (μ : ι → ℤ) => (Work.Diff.STE.wt μ) ^ k * ‖b σ μ‖ ^ 2)
    (g := fun (_ : ι → ℤ) => (0 : ℝ))
    (bound := fun μ : ι → ℤ => C ^ 2 * (Work.Diff.STE.wt μ) ^ (-(N : ℤ)))
    (hsumN.mul_left (C ^ 2)) hpt hbd2
  simpa only [Work.Diff.STE.CSq, tsum_zero] using hmain

end Work.Diff.STE.Lead.Squeeze
