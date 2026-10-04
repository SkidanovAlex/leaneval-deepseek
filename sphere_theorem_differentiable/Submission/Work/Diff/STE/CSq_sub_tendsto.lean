import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq` of a pointwise convergent, uniformly decaying family

This file proves `Work.Diff.STE.CSq_sub_tendsto`: if the coefficient families `c m` and the limit
family `d` satisfy the uniform weighted decay

  `‖c m μ‖ · ⟨μ⟩^M ≤ C`,  `‖d μ‖ · ⟨μ⟩^M ≤ C`   (for every `M`, some `C`, all `m`, `μ`)

(where `⟨μ⟩² = 1 + Σ μᵢ²` is `Work.Diff.STE.wt`) and `c m μ → d μ` for every `μ`, then the
weighted `ℓ²` mass of the difference vanishes:

  `CSq k (c m - d) = Σ_μ ⟨μ⟩^{2k} ‖c m μ - d μ‖² → 0`   as `m → ∞`.

The proof is Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) for the summand
`μ ↦ ⟨μ⟩^{2k} ‖c m μ - d μ‖²`:

* pointwise, `⟨μ⟩^{2k} ‖c m μ - d μ‖² → 0` because `c m μ - d μ → 0`;
* uniformly in `m`, `‖c m μ - d μ‖ ≤ 2C ⟨μ⟩^{-M}`, so that with `M ≥ k` the summand is dominated by
  the summable `4C² ⟨μ⟩^{-N}` for any fixed `N` with `card ι < 2N` (here `M = k + N` and
  `k + N ≤ 2M`; summability of `⟨·⟩^{-N}` is `Work.Diff.STE.summable_wt_zpow`).
-/

noncomputable section

namespace Work.Diff.STE

open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- From the decay bound `‖z‖ * ⟨μ⟩^M ≤ C` deduce `‖z‖ ≤ C * ⟨μ⟩^{-M}`. -/
private lemma norm_le_mul_wt_zpow {C : ℝ} {M : ℕ} {μ : ι → ℤ} {z : ℂ}
    (h : ‖z‖ * (wt μ) ^ M ≤ C) : ‖z‖ ≤ C * (wt μ) ^ (-(M : ℤ)) := by
  have hw : (0 : ℝ) < (wt μ) ^ M := pow_pos (wt_pos μ) M
  have h1 : ‖z‖ ≤ C / (wt μ) ^ M := (le_div_iff₀ hw).mpr h
  have h2 : C / (wt μ) ^ M = C * (wt μ) ^ (-(M : ℤ)) := by
    rw [div_eq_mul_inv, ← zpow_natCast (a := wt μ) M, zpow_neg]
  rwa [h2] at h1

/-- The exponent arithmetic of the domination: for `a ≥ 1` and `k + N ≤ 2M`,
`a^k · (a^{-M})² ≤ a^{-N}`.  (Since `a ≥ 1`, larger exponents give larger values, and
`k - 2M ≤ -N`.) -/
private lemma wt_pow_mul_zpow_sq_le {a : ℝ} (ha : 1 ≤ a) (k M N : ℕ) (hkN : k + N ≤ 2 * M) :
    a ^ k * (a ^ (-(M : ℤ))) ^ 2 ≤ a ^ (-(N : ℤ)) := by
  have hapos : 0 < a := lt_of_lt_of_le one_pos ha
  have hane : a ≠ 0 := ne_of_gt hapos
  have h1 : a ^ k * (a ^ (-(M : ℤ))) ^ 2 = a ^ ((k : ℤ) - 2 * (M : ℤ)) := by
    rw [← zpow_natCast (a := a) (n := k),
      show (a ^ (-(M : ℤ))) ^ 2 = (a ^ (-(M : ℤ))) ^ ((2 : ℤ)) from (zpow_natCast _ _).symm,
      ← zpow_mul, ← zpow_add₀ hane]
    congr 1
    ring
  rw [h1]
  exact zpow_le_zpow_right₀ ha (by omega)

/-- The single domination step: `⟨μ⟩^{2k} ‖z‖² ≤ 4C² ⟨μ⟩^{-N}` from `‖z‖ ≤ 2C ⟨μ⟩^{-M}`,
`k + N ≤ 2M` and `⟨μ⟩ ≥ 1`. -/
private lemma key_le {C : ℝ} {k M N : ℕ} (hkN : k + N ≤ 2 * M)
    {a z : ℝ} (ha : 1 ≤ a) (hz0 : 0 ≤ z) (hz : z ≤ 2 * C * a ^ (-(M : ℤ))) :
    a ^ k * z ^ 2 ≤ 4 * C ^ 2 * a ^ (-(N : ℤ)) := by
  have h1 : z ^ 2 ≤ (2 * C * a ^ (-(M : ℤ))) ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have h2 : a ^ k * z ^ 2 ≤ a ^ k * (2 * C * a ^ (-(M : ℤ))) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg (zero_le_one.trans ha) k)
  have h3 : a ^ k * (2 * C * a ^ (-(M : ℤ))) ^ 2
      = 4 * C ^ 2 * (a ^ k * (a ^ (-(M : ℤ))) ^ 2) := by
    rw [mul_pow]
    ring
  have h4 : a ^ k * (a ^ (-(M : ℤ))) ^ 2 ≤ a ^ (-(N : ℤ)) := wt_pow_mul_zpow_sq_le ha k M N hkN
  calc a ^ k * z ^ 2 ≤ 4 * C ^ 2 * (a ^ k * (a ^ (-(M : ℤ))) ^ 2) := by rw [← h3]; exact h2
    _ ≤ 4 * C ^ 2 * a ^ (-(N : ℤ)) := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem CSq_sub_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ → (ι → ℤ) → ℂ) (d : (ι → ℤ) → ℂ)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (μ : ι → ℤ),
      ‖c m μ‖ * Work.Diff.STE.wt μ ^ M ≤ C ∧ ‖d μ‖ * Work.Diff.STE.wt μ ^ M ≤ C)
    (hconv : ∀ μ : ι → ℤ, Filter.Tendsto (fun m : ℕ => c m μ) Filter.atTop (nhds (d μ))) :
    ∀ k : ℕ, Filter.Tendsto (fun m : ℕ => Work.Diff.STE.CSq k (fun μ => c m μ - d μ))
      Filter.atTop (nhds 0) := by
  intro k
  -- a fixed exponent `N` with `card ι < 2N`, so that `⟨·⟩^{-N}` is summable
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card ι < 2 * N := ⟨Fintype.card ι + 1, by omega⟩
  have hsumN : Summable (fun μ : ι → ℤ => (wt μ) ^ (-(N : ℤ))) := summable_wt_zpow N hN
  -- the decay constant at level `k + N`
  obtain ⟨C, hCnn, hC⟩ := hdec (k + N)
  have hbound : Summable (fun μ : ι → ℤ => 4 * C ^ 2 * (wt μ) ^ (-(N : ℤ))) :=
    hsumN.mul_left _
  -- pointwise convergence of the summands
  have hpt : ∀ μ : ι → ℤ, Filter.Tendsto
      (fun m : ℕ => (wt μ) ^ k * ‖c m μ - d μ‖ ^ 2) Filter.atTop (nhds 0) := by
    intro μ
    have h1 : Filter.Tendsto (fun m : ℕ => c m μ - d μ) Filter.atTop (nhds (d μ - d μ)) :=
      (hconv μ).sub tendsto_const_nhds
    have h2 : Filter.Tendsto (fun m : ℕ => ‖c m μ - d μ‖) Filter.atTop (nhds 0) := by
      simpa using h1.norm
    have h3 : Filter.Tendsto (fun m : ℕ => ‖c m μ - d μ‖ ^ 2) Filter.atTop (nhds 0) := by
      simpa using h2.pow 2
    have h4 := h3.const_mul ((wt μ) ^ k)
    simpa using h4
  -- the uniform dominating family
  have hbd : ∀ᶠ m in Filter.atTop, ∀ μ : ι → ℤ,
      ‖(wt μ) ^ k * ‖c m μ - d μ‖ ^ 2‖ ≤ 4 * C ^ 2 * (wt μ) ^ (-(N : ℤ)) := by
    refine Filter.Eventually.of_forall (fun m μ => ?_)
    have hz : ‖c m μ - d μ‖ ≤ 2 * C * (wt μ) ^ (-((k + N : ℕ) : ℤ)) := by
      calc ‖c m μ - d μ‖ ≤ ‖c m μ‖ + ‖d μ‖ := norm_sub_le _ _
        _ ≤ C * (wt μ) ^ (-((k + N : ℕ) : ℤ)) + C * (wt μ) ^ (-((k + N : ℕ) : ℤ)) :=
            add_le_add (norm_le_mul_wt_zpow (hC m μ).1) (norm_le_mul_wt_zpow (hC m μ).2)
        _ = 2 * C * (wt μ) ^ (-((k + N : ℕ) : ℤ)) := by ring
    have hkey := key_le (C := C) (k := k) (M := k + N) (N := N) (by omega)
      (wt_one_le μ) (norm_nonneg _) hz
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (wt_pos μ).le k) (sq_nonneg _))]
    exact hkey
  -- Tannery's theorem
  have hmain := tendsto_tsum_of_dominated_convergence
    (f := fun (m : ℕ) (μ : ι → ℤ) => (wt μ) ^ k * ‖c m μ - d μ‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun μ : ι → ℤ => 4 * C ^ 2 * (wt μ) ^ (-(N : ℤ)))
    hbound hpt hbd
  simpa [CSq, tsum_zero] using hmain

end Work.Diff.STE
