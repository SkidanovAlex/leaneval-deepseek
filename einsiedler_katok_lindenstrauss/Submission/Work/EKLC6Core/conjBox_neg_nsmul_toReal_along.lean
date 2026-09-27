import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.conjBox_neg_nsmul_toReal
import Submission.Work.EKLC6Core.log_mass_conjBox_eq_sum_along
import Submission.Work.EKLC6Core.conjBox_mass_pos

/-!
# `EKLC6Core.conjBox_neg_nsmul_toReal_along`

`conjBox_neg_nsmul_toReal` with the full `A`-covariance `ACovariant ν X''` replaced by the
covariance along the integer multiples of the single direction `t` (`ACovariantAlong ν t X''`,
EKL (4) restricted to `ℤ · t`):

`(ν x (conjBox U (-m t))).toReal = exp (∑_{j=1}^{m} growthFun U ν t (aDiag (j t) · x))`.

## Note on the statement as requested

The statement was requested with the binder `{t : Fin 3 → ℝ}` placed **after** the hypothesis
`hcov : Work.EKLC6Core.ACovariantAlong ν t X''` that mentions `t`:

```
theorem conjBox_neg_nsmul_toReal_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'')
    (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (m : ℕ) {x : Work.EKLContract.X3}
    (hx : ∀ j : ℕ, j ≤ m + 2 →
      Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'') :
    (ν x (Work.EKLC6Core.conjBox U (-((m : ℝ) • t)))).toReal
      = Real.exp (∑ j ∈ Finset.Icc 1 m,
          Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag ((j : ℝ) • t) • x)) := by sorry
```

* As written this is **not a well-formed statement** in this workspace: `t` is used in `hcov`
  before the binder that introduces it, and the package's `lakefile.toml` sets
  `autoImplicit = false`, so Lean rejects it (`Unknown identifier t`).
* Re-parsing the very same text with `autoImplicit = true` (which is how such a request is
  elaborated) does **not** repair it: it introduces `t` in `hcov` as an *independent implicit
  parameter*, giving the (printed) type
  `∀ {t : Fin 3 → ℝ} {μ} […] {X' X''}, IsLeafwise … → ACovariantAlong ν t X'' → IsHoro U → ∀ {t : Fin 3 → ℝ}, …`
  whose proof term is `fun {t} {μ} … hL hcov hU {t_1} hcontr m {x} hx => …` — the covariance
  hypothesis talks about a direction unrelated to the one in `hcontr`, `hx` and the conclusion.
  That reading is *false*: instantiating the phantom direction at `0` makes `hcov` vacuous
  (`(z : ℝ) • 0 = 0`, `aDiag 0 = 1`, so `c = 1` works for every `ν`), leaving the
  covariance-free telescoping, which is exactly the content of Pisa 7.16 and is *not* derivable
  from `IsLeafwise` (cf. `acovariantAlong_of_leafwise`, which must assume
  `MeasurePreserving (fun x => aDiag t • x) μ μ`).  Concretely, `μ = δ_{x₀}` with a generic `x₀`,
  `X' = X'' = {x₀} ∪ {aDiag (j t) · x₀}`, `ν x₀ = δ_1` (which satisfies the `condexp` clause for
  every plaque algebra, since `1 ∈ shape m U x₀` and `1 · x₀ = x₀`) and `ν` at the orbit points
  equal to normalised Haar measure on a half-sized neighbourhood `B ⊊ Box1 U` of `1` in `U`
  satisfies `IsLeafwise` and makes the identity fail already at `m = 1` (`1 = (ν x₀ (conjBox U (-t))).toReal`
  versus `exp (growthFun U ν t (aDiag t · x₀)) = Haar (B) / Haar (conjBox U t) ≠ 1`).

The intended statement — the same text with `{t : Fin 3 → ℝ}` moved above `hcov`, i.e. a single
direction `t` shared by `hcov`, `hcontr`, `hx` and the conclusion — is **true**, and that is what
is proved below.  It also builds, is `sorry`-free, and its axioms are within
`{propext, Classical.choice, Quot.sound}`.

Every use of the covariance in the telescoping `covariant_mul` is at the single parameter `-t`,
so the argument goes through verbatim with `covariant_mul_along` (Pisa 7.16 + 7.18).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- `conjBox_neg_nsmul_toReal` with the full `A`-covariance `ACovariant ν X''` replaced by the
covariance along the integer multiples of the direction `t` (`ACovariantAlong ν t X''`):
`(ν x (conjBox U (-m t))).toReal = exp (∑_{j=1}^{m} growthFun U ν t (aDiag (j t) · x))`
whenever the orbit points `x, aDiag t · x, …, aDiag ((m+2) t) · x` lie in `X' ∩ X''`.

(Here `{t : Fin 3 → ℝ}` is bound *before* `hcov`, as it must be: `hcov` mentions `t`.  See the
module docstring.) -/
theorem conjBox_neg_nsmul_toReal_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    {t : Fin 3 → ℝ}
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'')
    (hU : Work.EKLContract.IsHoro U)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (m : ℕ) {x : Work.EKLContract.X3}
    (hx : ∀ j : ℕ, j ≤ m + 2 →
      Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'') :
    (ν x (Work.EKLC6Core.conjBox U (-((m : ℝ) • t)))).toReal
      = Real.exp (∑ j ∈ Finset.Icc 1 m,
          Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag ((j : ℝ) • t) • x)) := by
  -- each one-step box along the orbit has positive, finite (hence positive real) mass
  have hpos : ∀ j ∈ Finset.range m,
      0 < ((ν (aDiag (((j : ℝ) + 1) • t) • x)) (conjBox U t)).toReal := by
    intro j hj
    have hjle : j + 1 ≤ m + 2 := by
      have := Finset.mem_range.mp hj
      omega
    have hmem : aDiag (((j : ℝ) + 1) • t) • x ∈ X' := by
      have h := (hx (j + 1) hjle).1
      rwa [aDiag_natCast_add_one_smul t j] at h
    obtain ⟨hp, hlt⟩ := conjBox_mass_pos (μ := μ) (ν := ν) (U := U) hL hU t hmem
    exact ENNReal.toReal_pos (ne_of_gt hp) (ne_of_lt hlt)
  -- the telescoping product identity of Pisa 7.16 + 7.18, along the single direction `t`
  have hmul := covariant_mul_along (μ := μ) (U := U) (ν := ν) (X' := X') (X'' := X'') t hL
    hcov (fun w => conjBox_measurable hU w) m x hx
  -- hence the mass of the big box is the reciprocal of the product of the one-step masses
  have hval : (ν x (conjBox U (-((m : ℝ) • t)))).toReal
      = ((∏ j ∈ Finset.range m, (ν (aDiag (((j : ℝ) + 1) • t) • x)) (conjBox U t)).toReal)⁻¹ := by
    have h := congrArg ENNReal.toReal hmul
    simp only [ENNReal.toReal_mul, ENNReal.toReal_one] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [hval]
  -- re-index the sum along the orbit and turn the exponential of the sum into the product
  rw [sum_Icc_one_eq_sum_range (fun k => growthFun U ν t (aDiag ((k : ℝ) • t) • x)) m]
  simp only [aDiag_natCast_add_one_smul]
  rw [ENNReal.toReal_prod, Real.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [growthFun, Real.exp_neg, Real.exp_log (hpos j hj)]

end Work.EKLC6Core

end
