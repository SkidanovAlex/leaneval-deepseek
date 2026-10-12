import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp`

The **box-restricted** localised box form `boxFormB` (the object whose infimum over free particle
number and symmetric smooth box states is FS's box energy `EΛ`, see `Defs.EΛ`) agrees with the
whole-space localised form `boxForm` at `u = 0`, for every smooth state `Φ` whose support lies in
the centred configuration box `abox N ℓ`:

    `boxFormB N v g ℓ μ d s εT b Φ = boxForm N v g ℓ μ d s εT b 0 Φ`.

Both sides are sums of *integrals over `abox N ℓ`* of expressions that, for such a state,
vanish pointwise off `abox N ℓ` — so the box integral and the whole-space integral coincide:

* the potential integrand `(Φ x)² · potWordU … 0 x` because `Φ x = 0` off `abox N ℓ`;
* the `i`-th kinetic integrand `indU ℓ 0 (xᵢ) · fsT … 0 (fibre N i Φ x)`: if `x ∉ abox N ℓ`
  then some slot `j` of `x` leaves `acube ℓ`.  If `j = i` the indicator `indU ℓ 0 (xᵢ)` kills the
  term; if `j ≠ i` then the fibre `z ↦ Φ (x with xᵢ = z)` is *identically zero* (its slot `j`
  is always `x_j ∉ acube ℓ`), so `fsT` of it vanishes by
  `Word.fsT_eq_zero_of_lamBox_const` (the zero function is constant on the box).

This is the identity that makes `EΛ` a box Rayleigh quotient: `boxFormB` is exactly the
`u = 0` form seen through the box restriction.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Word

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Support lemmas -/

/-- A state whose topological support lies in the configuration box `abox N ℓ` vanishes off it. -/
lemma eq_zero_of_not_mem_abox {N : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N ℓ) {x : Submission.BoseGases.X N}
    (hx : x ∉ Submission.BoseGases.abox N ℓ) : Φ x = 0 := by
  by_contra h
  exact hx (hsupp (subset_tsupport Φ (Function.mem_support.mpr h)))

/-- If some slot `j ≠ i` of the configuration `x` lies outside `acube ℓ`, then the `i`-th fibre of
a state supported in `abox N ℓ` vanishes identically: updating the `i`-th slot never moves the
(forbidden) `j`-th coordinate, so the updated configuration stays outside `abox N ℓ`. -/
lemma fibre_eq_zero_of_slot_not_mem {N : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N ℓ) {x : Submission.BoseGases.X N}
    {i j : Fin N} (hji : j ≠ i) (hj : x j ∉ Submission.BoseGases.acube ℓ) :
    fibre N i Φ x = 0 := by
  funext z
  have hmem : Function.update x i z ∉ Submission.BoseGases.abox N ℓ := by
    intro h
    refine hj ?_
    rw [← Function.update_of_ne hji z x]
    exact h j
  exact eq_zero_of_not_mem_abox hsupp hmem

/-- The zero function is (of course) constant on the box, so `fsT` vanishes on it. -/
lemma fsT_zero {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) :
    fsT ℓ d s εT b 0 (0 : ℝ³ → ℝ) = 0 :=
  fsT_eq_zero_of_lamBox_const hℓ 0 (c := 0) fun _ _ => rfl

/-- **The `i`-th kinetic integrand vanishes off the configuration box.**  If `x ∉ abox N ℓ` then
some slot of `x` leaves `acube ℓ`; either it is the `i`-th slot (and the indicator `indU ℓ 0 (xᵢ)`
vanishes) or it is another slot (and the fibre is identically zero). -/
lemma indU_mul_fsT_fibre_eq_zero {N : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N ℓ)
    {x : Submission.BoseGases.X N} (hx : x ∉ Submission.BoseGases.abox N ℓ) (i : Fin N) :
    indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin N, x j ∉ Submission.BoseGases.acube ℓ := by
    by_contra h
    exact hx fun k => not_not.mp (not_exists.mp h k)
  by_cases hji : j = i
  · have hj' : x i ∉ Submission.BoseGases.acube ℓ := hji ▸ hj
    have hxl : x i ∉ lamBox ℓ 0 := by
      simpa [lamBox, bsBox] using hj'
    rw [show indU ℓ 0 (x i) = 0 by
      simp only [indU]
      exact Set.indicator_of_notMem hxl _, zero_mul]
  · rw [fibre_eq_zero_of_slot_not_mem hsupp hji hj, fsT_zero hℓ, mul_zero]

/-! ## 2. The identity -/

theorem boxFormB_eq_boxForm_of_supp {N : ℕ} {v g : ℝ³ → ℝ} {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N ℓ) :
    Work.BoseKinLoc.boxFormB N v g ℓ μ d s εT b Φ
      = Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b 0 Φ := by
  have hkin : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x))
        = ∫ x : Submission.BoseGases.X N,
            indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x) :=
    fun i => MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => indU_mul_fsT_fibre_eq_zero hℓ hsupp hx i
  have hpot : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * potWordU N v g ℓ μ 0 x)
      = ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 * potWordU N v g ℓ μ 0 x :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [eq_zero_of_not_mem_abox hsupp hx]
      ring
  have hsum : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x))
      = ∑ i : Fin N, ∫ x : Submission.BoseGases.X N,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x) :=
    Finset.sum_congr rfl fun i _ => hkin i
  have hkin' : ℓ ^ (-3 : ℤ) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x))
      = ∑ i : Fin N, ℓ ^ (-3 : ℤ) * ∫ x : Submission.BoseGases.X N,
          indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre N i Φ x) := by
    rw [hsum, Finset.mul_sum]
  unfold boxFormB boxForm kinFormB kinForm slotForm
  rw [hpot, hkin']

end Work.BoseKinLoc.Word
