import Mathlib
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq k (c m) → CSq k d` from pointwise convergence plus uniform weighted decay

Layer A of the STE development: the weighted `ℓ²` mass

  `CSq k c = Σ_μ ⟨μ⟩^{2k} ‖c μ‖²`   (`Work.Diff.STE.CSq`, `⟨μ⟩² = 1 + Σ μᵢ² = Work.Diff.STE.wt`)

of a lattice family `c : (ι → ℤ) → ℂ`.

Let `c : ℕ → (ι → ℤ) → ℂ` be a sequence of families and `d` a family such that

* `c m μ → d μ` for every `μ` (`hconv`), and
* both `c m` and `d` decay uniformly in `m` faster than any power of the weight
  (`hdec`: for every `M` there is `C ≥ 0` with `‖c m μ‖ ⟨μ⟩^M ≤ C` and `‖d μ‖ ⟨μ⟩^M ≤ C`,
  for all `m`, `μ`).

Then `CSq k (c m) → CSq k d`.

This is the "upgrade coefficientwise convergence to `Hᵏ` convergence" step of the energy method
(it is the exact statement used to pass the composite `Hᵏ` bounds of the DeTurck limit to the
limit section, cf. `Work.Diff.STE.Lead.BNorm_le_of_coeff_tendsto`).

## Proof

This is Tannery's theorem (`tendsto_tsum_of_dominated_convergence`, Mathlib) applied to the
summands `f m μ = ⟨μ⟩^{2k} ‖c m μ‖²` with limit `g μ = ⟨μ⟩^{2k} ‖d μ‖²` and the dominating
summable family `μ ↦ C² ⟨μ⟩^{-N}`.

* Choose `N` with `card ι < 2N`; then `⟨·⟩^{-N}` is summable on `ℤ^ι`
  (`Work.Diff.STE.summable_wt_zpow`).
* Apply the decay hypothesis with the exponent `M := k + N`.  The bound
  `‖c m μ‖ ⟨μ⟩^M ≤ C` gives `‖c m μ‖ ≤ C ⟨μ⟩^{-M}`, hence
  `⟨μ⟩^{2k} ‖c m μ‖² ≤ C² ⟨μ⟩^{2k-2M} ≤ C² ⟨μ⟩^{-N}`,
  because `⟨μ⟩ ≥ 1` and `2k - 2M ≤ -N`.  It is **uniform in `m`**, which is exactly what
  domination needs.
* Each summand converges pointwise, since `z ↦ ⟨μ⟩^{2k} ‖z‖²` is continuous.
-/

noncomputable section

namespace Work.Diff.STE.Lead

/-- From the decay bound `‖z‖ * ⟨μ⟩^M ≤ C` deduce `‖z‖ ≤ C * ⟨μ⟩^{-M}`. -/
private lemma norm_le_mul_wt_zpow_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : ℝ} {M : ℕ} {μ : ι → ℤ} {z : ℂ}
    (h : ‖z‖ * (Work.Diff.STE.wt μ) ^ M ≤ C) :
    ‖z‖ ≤ C * (Work.Diff.STE.wt μ) ^ (-(M : ℤ)) := by
  have hw : (0 : ℝ) < (Work.Diff.STE.wt μ) ^ M := pow_pos (Work.Diff.STE.wt_pos μ) M
  have h1 : ‖z‖ ≤ C / (Work.Diff.STE.wt μ) ^ M := (le_div_iff₀ hw).mpr h
  have h2 : C / (Work.Diff.STE.wt μ) ^ M = C * (Work.Diff.STE.wt μ) ^ (-(M : ℤ)) := by
    rw [div_eq_mul_inv, ← zpow_natCast (a := Work.Diff.STE.wt μ) M, zpow_neg]
  rwa [h2] at h1

/-- The exponent arithmetic of the domination: for `a ≥ 1` and `k + N ≤ 2M`,
`a^k * (a^{-M})² ≤ a^{-N}`.  (Since `a ≥ 1`, larger exponents give larger values, and
`k - 2M ≤ -N`.) -/
private lemma wt_pow_mul_zpow_sq_le_aux {a : ℝ} (ha : 1 ≤ a) (k M N : ℕ) (hkN : k + N ≤ 2 * M) :
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

/-- The single domination step: `⟨μ⟩^{2k} z² ≤ C² ⟨μ⟩^{-N}` from `0 ≤ z`,
`z ≤ C ⟨μ⟩^{-M}`, `k + N ≤ 2M` and `⟨μ⟩ ≥ 1`. -/
private lemma key_le_aux {C : ℝ} {k M N : ℕ} (hkN : k + N ≤ 2 * M)
    {a z : ℝ} (ha : 1 ≤ a) (hz0 : 0 ≤ z) (hz : z ≤ C * a ^ (-(M : ℤ))) :
    a ^ k * z ^ 2 ≤ C ^ 2 * a ^ (-(N : ℤ)) := by
  have h1 : z ^ 2 ≤ (C * a ^ (-(M : ℤ))) ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have h2 : a ^ k * z ^ 2 ≤ a ^ k * (C * a ^ (-(M : ℤ))) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg (zero_le_one.trans ha) k)
  have h3 : a ^ k * (C * a ^ (-(M : ℤ))) ^ 2
      = C ^ 2 * (a ^ k * (a ^ (-(M : ℤ))) ^ 2) := by
    rw [mul_pow]
    ring
  have h4 : a ^ k * (a ^ (-(M : ℤ))) ^ 2 ≤ a ^ (-(N : ℤ)) :=
    wt_pow_mul_zpow_sq_le_aux ha k M N hkN
  calc a ^ k * z ^ 2 ≤ C ^ 2 * (a ^ k * (a ^ (-(M : ℤ))) ^ 2) := by rw [← h3]; exact h2
    _ ≤ C ^ 2 * a ^ (-(N : ℤ)) := mul_le_mul_of_nonneg_left h4 (sq_nonneg C)

theorem CSq_tendsto_of_decay_pointwise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℕ → (ι → ℤ) → ℂ) (d : (ι → ℤ) → ℂ)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (μ : ι → ℤ),
      ‖c m μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C ∧ ‖d μ‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (hconv : ∀ μ : ι → ℤ, Filter.Tendsto (fun m : ℕ => c m μ) Filter.atTop (nhds (d μ)))
    (k : ℕ) :
    Filter.Tendsto (fun m : ℕ => Work.Diff.STE.CSq k (c m)) Filter.atTop
      (nhds (Work.Diff.STE.CSq k d)) := by
  classical
  -- a fixed exponent `N` with `card ι < 2N`, so that `⟨·⟩^{-N}` is summable
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card ι < 2 * N := ⟨Fintype.card ι + 1, by omega⟩
  have hsumN : Summable (fun μ : ι → ℤ => (Work.Diff.STE.wt μ) ^ (-(N : ℤ))) :=
    Work.Diff.STE.summable_wt_zpow N hN
  -- the decay constant at level `k + N`
  obtain ⟨C, _hCnn, hC⟩ := hdec (k + N)
  have hbound : Summable (fun μ : ι → ℤ => C ^ 2 * (Work.Diff.STE.wt μ) ^ (-(N : ℤ))) :=
    hsumN.mul_left _
  -- pointwise convergence of the summands
  have hpt : ∀ μ : ι → ℤ, Filter.Tendsto
      (fun m : ℕ => (Work.Diff.STE.wt μ) ^ k * ‖c m μ‖ ^ 2) Filter.atTop
      (nhds ((Work.Diff.STE.wt μ) ^ k * ‖d μ‖ ^ 2)) := by
    intro μ
    have h1 : Filter.Tendsto (fun m : ℕ => ‖c m μ‖) Filter.atTop (nhds ‖d μ‖) := (hconv μ).norm
    have h2 : Filter.Tendsto (fun m : ℕ => ‖c m μ‖ ^ 2) Filter.atTop (nhds (‖d μ‖ ^ 2)) :=
      h1.pow 2
    simpa using h2.const_mul ((Work.Diff.STE.wt μ) ^ k)
  -- the uniform dominating family
  have hbd : ∀ᶠ m in Filter.atTop, ∀ μ : ι → ℤ,
      ‖(Work.Diff.STE.wt μ) ^ k * ‖c m μ‖ ^ 2‖
        ≤ C ^ 2 * (Work.Diff.STE.wt μ) ^ (-(N : ℤ)) := by
    refine Filter.Eventually.of_forall (fun m μ => ?_)
    have hz : ‖c m μ‖ ≤ C * (Work.Diff.STE.wt μ) ^ (-((k + N : ℕ) : ℤ)) :=
      norm_le_mul_wt_zpow_aux (hC m μ).1
    have hkey := key_le_aux (C := C) (k := k) (M := k + N) (N := N) (by omega)
      (Work.Diff.STE.wt_one_le μ) (norm_nonneg _) hz
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos μ).le k) (sq_nonneg _))]
    exact hkey
  -- Tannery's theorem
  have hmain := tendsto_tsum_of_dominated_convergence
    (f := fun (m : ℕ) (μ : ι → ℤ) => (Work.Diff.STE.wt μ) ^ k * ‖c m μ‖ ^ 2)
    (g := fun μ : ι → ℤ => (Work.Diff.STE.wt μ) ^ k * ‖d μ‖ ^ 2)
    (bound := fun μ : ι → ℤ => C ^ 2 * (Work.Diff.STE.wt μ) ^ (-(N : ℤ)))
    hbound hpt hbd
  simpa only [Work.Diff.STE.CSq] using hmain

end Work.Diff.STE.Lead
