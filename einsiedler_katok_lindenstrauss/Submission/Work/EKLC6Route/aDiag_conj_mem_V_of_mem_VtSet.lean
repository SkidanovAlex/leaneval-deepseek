import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.box_iInter_conjBox

/-!
# `EKLC6Route.aDiag_conj_mem_V_of_mem_VtSet`

The neighbourhood `V s = {g | maxᵢⱼ |gᵢⱼ - δᵢⱼ| < s}` of the identity is *expanded* under
conjugation by the powers of `aDiag t`, by the factor `e^{n · betaExp t}`:

`aDiag t ^ n · v · (aDiag t ^ n)⁻¹ ∈ V (e^{n · betaExp t} · s)`

for every `v ∈ V s`, and in particular for `v` in the parabolic subgroup `VtSet t` (whose
entries vanish below the `t`-ordering).

The hypothesis `v ∈ VtSet t` is in fact *not needed* for the estimate: for `i ≠ j` only the upper
bound `|vᵢⱼ| < s` is used, and it holds whether or not the entry vanishes.  We keep the
hypothesis because the statement is fixed as requested.

This is the expanding companion of `Work.EKLC6Route.aDiag_conj_mem_V_of_mem_uminus` (which
covers the contracted subgroup `Uminus t` and keeps the radius `s`).

## Proof

`aDiag t` is a scalar (`e^{-(∑t)/3}`) times the diagonal matrix with entries `e^{t k}`, so
`boxi_conj_pow_apply` computes the entries of the conjugate:

`(aDiag t ^ n · v · (aDiag t ^ n)⁻¹)ᵢⱼ = e^{n(tᵢ - tⱼ)} · vᵢⱼ`.

Let `β = betaExp t = max_{i,j} |tᵢ - tⱼ|` and `M = e^{nβ}`.

* `v ∈ V s` forces `s > 0` (the diagonal entry `v₀₀` is within `s` of `1`).
* `i = j`: the factor is `e^0 = 1`, so the entry is `vᵢᵢ`, and `|vᵢᵢ - 1| < s ≤ M s` because
  `M = e^{nβ} ≥ e^0 = 1`.
* `i ≠ j`: the target value is `0`, and `|e^{n(tᵢ-tⱼ)} vᵢⱼ| = e^{n(tᵢ-tⱼ)}|vᵢⱼ| <
  e^{n(tᵢ-tⱼ)} s ≤ M s`, using `|vᵢⱼ| < s`, `s > 0` and `tᵢ - tⱼ ≤ β`.
-/

-- the hypothesis `hv : v ∈ VtSet t` is not needed for the estimate below; we keep it because
-- the statement is fixed (the entry bound holds for *every* `v ∈ V s`).
set_option linter.unusedVariables false

namespace Work.EKLC6Route

open Work.EKLContract

theorem aDiag_conj_mem_V_of_mem_VtSet {t : Fin 3 → ℝ} {s : ℝ} {v : Work.EKLContract.SL3} (n : ℕ)
    (hv : v ∈ Work.EKLC6Route.VtSet t) (hvV : v ∈ Work.EKLContract.V s) :
    Work.EKLContract.aDiag t ^ n * v * (Work.EKLContract.aDiag t ^ n)⁻¹ ∈
      Work.EKLContract.V (Real.exp ((n : ℝ) * Work.EKLC6Route.betaExp t) * s) := by
  -- unpack the hypothesis `v ∈ V s`
  have hV : ∀ i j : Fin 3, |(v : Work.EKLContract.SL3) i j -
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < s := hvV
  -- `V s ≠ ∅` forces `s > 0` (diagonal entry at `(0,0)`)
  have hs : 0 < s := lt_of_le_of_lt (abs_nonneg _) (hV 0 0)
  -- `betaExp t` bounds every difference `t i - t j`
  have hβ : ∀ i j : Fin 3, t i - t j ≤ betaExp t := fun i j =>
    le_trans (le_abs_self _)
      (Finset.le_sup' (fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|) (Finset.mem_univ (i, j)))
  have hβ0 : 0 ≤ betaExp t := by linarith [hβ 0 0]
  -- the expansion factor is at least `1`
  have hexp1 : 1 ≤ Real.exp ((n : ℝ) * betaExp t) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg n) hβ0)
  -- check the defining inequalities entry by entry
  intro i j
  rw [Work.EKLC6Core.boxi_conj_pow_apply t n v i j]
  by_cases hij : i = j
  · -- diagonal entry: conjugation does nothing, and `e^{nβ} s ≥ s`
    subst hij
    rw [Matrix.one_apply_eq, sub_self, mul_zero, Real.exp_zero, one_mul]
    have hdiag : |(v : Work.EKLContract.SL3) i i - 1| < s := by
      simpa only [Matrix.one_apply_eq] using hV i i
    exact lt_of_lt_of_le hdiag (le_mul_of_one_le_left (le_of_lt hs) hexp1)
  · -- off-diagonal entry: `|e^{n(tᵢ-tⱼ)} vᵢⱼ| ≤ e^{nβ} |vᵢⱼ| < e^{nβ} s`
    rw [Matrix.one_apply_ne hij, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |(v : Work.EKLContract.SL3) i j| < s := by
      simpa only [Matrix.one_apply_ne hij, sub_zero] using hV i j
    have h2 : Real.exp ((n : ℝ) * (t i - t j)) * |(v : Work.EKLContract.SL3) i j| <
        Real.exp ((n : ℝ) * (t i - t j)) * s :=
      mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
    have h3 : Real.exp ((n : ℝ) * (t i - t j)) ≤ Real.exp ((n : ℝ) * betaExp t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hβ i j) (Nat.cast_nonneg n))
    exact lt_of_lt_of_le h2 (mul_le_mul_of_nonneg_right h3 hs.le)

end Work.EKLC6Route
