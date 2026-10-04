import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.tendsto_tail_piFinset_wt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq k (a m) → 0` from pointwise convergence plus uniform weighted decay

Layer A of the STE development (the Fourier/Sobolev toolkit on the unit torus, `Torus.lean`).

Let `a : ℕ → (ι → ℤ) → ℂ` be a family of coefficient families on the lattice `ℤ^ι` which

* converges to `0` coefficientwise (`hconv`: `a m ν → 0` for every `ν`), and
* decays uniformly in `m` faster than any power of the weight `⟨ν⟩² = wt ν`
  (`hdec`: for every `M` there is `C` with `‖a m ν‖ * (wt ν)^M ≤ C` for all `m`, `ν`).

Then the weighted `ℓ²`-norms `CSq k (a m) = Σ_ν (wt ν)^k ‖a m ν‖²` tend to `0`.

This is the "uniform tail decay" input to the energy method: it upgrades a pointwise
(in-frequency) limit to the convergence of the whole weighted `ℓ²` norm.

## Proof

Take `M` so large that the dominating weight is summable: with `d = card ι` the choice
`M = k + d + 1` gives `2 M - k = k + 2 d + 2`, and `⟨ν⟩^{-(k+2d+2)}` is summable on `ℤ^d`
(`summable_wt_zpow`, since `2 (k + 2d + 2) > d`).

* The decay hypothesis, squared, is `(wt ν)^{2M} ‖a m ν‖² ≤ C²`, i.e.
  `(wt ν)^k ‖a m ν‖² ≤ C² / (wt ν)^(2M-k) =: B ν`, a bound **uniform in `m`**
  (note `d`, hence `M`, `N`, may depend on `ι` and `k` only through `card ι`, which is
  available: `hdec` is a hypothesis for *every* exponent `M`).
* Each summand converges to `0` pointwise (`hconv`).
* Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) with the summable dominating
  function `B` therefore gives `Σ_ν (wt ν)^k ‖a m ν‖² → Σ_ν 0 = 0`.
-/

noncomputable section

namespace Work.Diff.STE

theorem CSq_tendsto_zero_of_decay_pointwise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℕ → (ι → ℤ) → ℂ)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (ν : ι → ℤ),
      ‖a m ν‖ * (Work.Diff.STE.wt ν) ^ M ≤ C)
    (hconv : ∀ ν : ι → ℤ, Filter.Tendsto (fun m : ℕ => a m ν) Filter.atTop (nhds 0))
    (k : ℕ) :
    Filter.Tendsto (fun m : ℕ => Work.Diff.STE.CSq k (a m)) Filter.atTop (nhds 0) := by
  classical
  -- the exponent `M` of the decay hypothesis and the resulting tail exponent `N = 2M - k`
  set d : ℕ := Fintype.card ι with hd
  set M : ℕ := k + d + 1 with hM
  obtain ⟨C, _hCnn, hC⟩ := hdec M
  set N : ℕ := 2 * M - k with hN
  have hNcard : Fintype.card ι < 2 * N := by omega
  have hkN : k + N = 2 * M := by omega
  -- the dominating function `ν ↦ C² / ⟨ν⟩^N` is summable
  have hsum : Summable (fun ν : ι → ℤ => C ^ 2 / (Work.Diff.STE.wt ν) ^ N) := by
    have h1 : Summable (fun ν : ι → ℤ => ((Work.Diff.STE.wt ν) ^ N)⁻¹) :=
      (Work.Diff.STE.summable_wt_zpow N hNcard).congr
        (fun ν => by rw [zpow_neg, zpow_natCast])
    exact (h1.mul_left (C ^ 2)).congr (fun ν => by rw [div_eq_mul_inv])
  -- the uniform pointwise bound
  have hpt : ∀ (m : ℕ) (ν : ι → ℤ), (Work.Diff.STE.wt ν) ^ k * ‖a m ν‖ ^ 2
      ≤ C ^ 2 / (Work.Diff.STE.wt ν) ^ N := by
    intro m ν
    have hwtpos : 0 < Work.Diff.STE.wt ν := Work.Diff.STE.wt_pos ν
    have hwtnn : 0 ≤ Work.Diff.STE.wt ν := le_of_lt hwtpos
    -- the decay hypothesis, squared: `⟨ν⟩^{2M} ‖a m ν‖² ≤ C²`
    have hsq : (Work.Diff.STE.wt ν) ^ (2 * M) * ‖a m ν‖ ^ 2 ≤ C ^ 2 := by
      have h1 : (Work.Diff.STE.wt ν) ^ M * ‖a m ν‖ ≤ C := by
        rw [mul_comm]; exact hC m ν
      have h2 : ((Work.Diff.STE.wt ν) ^ M * ‖a m ν‖) ^ 2 ≤ C ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (pow_nonneg hwtnn M) (norm_nonneg _)) h1 2
      rw [mul_pow, ← pow_mul] at h2
      rwa [Nat.mul_comm M 2] at h2
    have hLHS : (Work.Diff.STE.wt ν) ^ k * ‖a m ν‖ ^ 2 * (Work.Diff.STE.wt ν) ^ N
        = (Work.Diff.STE.wt ν) ^ (2 * M) * ‖a m ν‖ ^ 2 := by
      rw [← hkN, pow_add]; ring
    refine (le_div_iff₀ (pow_pos hwtpos N)).mpr ?_
    rw [hLHS]
    exact hsq
  have hpt' : ∀ (m : ℕ) (ν : ι → ℤ),
      ‖(Work.Diff.STE.wt ν) ^ k * ‖a m ν‖ ^ 2‖ ≤ C ^ 2 / (Work.Diff.STE.wt ν) ^ N := by
    intro m ν
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos ν)) k)
      (sq_nonneg _))]
    exact hpt m ν
  -- the summands converge to `0` pointwise
  have hlim : ∀ ν : ι → ℤ,
      Filter.Tendsto (fun m : ℕ => (Work.Diff.STE.wt ν) ^ k * ‖a m ν‖ ^ 2)
        Filter.atTop (nhds 0) := by
    intro ν
    have h1 : Filter.Tendsto (fun m : ℕ => ‖a m ν‖) Filter.atTop (nhds 0) := by
      simpa using (hconv ν).norm
    have h2 : Filter.Tendsto (fun m : ℕ => ‖a m ν‖ ^ 2) Filter.atTop (nhds 0) := by
      simpa using h1.pow 2
    have h3 := (tendsto_const_nhds (x := (Work.Diff.STE.wt ν) ^ k) (f := Filter.atTop)).mul h2
    simpa using h3
  -- Tannery
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (m : ℕ) (ν : ι → ℤ) => (Work.Diff.STE.wt ν) ^ k * ‖a m ν‖ ^ 2)
    (g := fun (_ : ι → ℤ) => (0 : ℝ))
    (bound := fun ν : ι → ℤ => C ^ 2 / (Work.Diff.STE.wt ν) ^ N)
    hsum hlim (Filter.Eventually.of_forall hpt')
  simpa [Work.Diff.STE.CSq] using hmain

end Work.Diff.STE
