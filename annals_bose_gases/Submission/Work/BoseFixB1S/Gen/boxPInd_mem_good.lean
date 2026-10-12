import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Gen.n0EOpGood
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.Gen.boxPInd_mem_good` — the box projection preserves `good`

The `n₀`-spectral induction of `Gen/n0EOpGood` runs inside the class `good N` of *measurable
states bounded on every ball*, because that class is exactly what the linearity estimates for the
slot projections `Pᵢ = UBBInputs8.boxPInd volA A i` need: measurability of `PᵢΨ` and a uniform
bound of the fibre functions on the box.

The present file closes the invariance:

* `boxPInd_mem_good` — `Pᵢ` maps `good N` into itself.

Two independent ingredients, neither of which uses more than `A ⊆ acube ℓ`:

* **measurability** — `Work.BoseFixB1S.measurable_boxPInd`: the fibre mean
  `x ↦ ∫_{z∈A} Ψ(x|i↦z)` is measurable for measurable `Ψ` (joint measurability of the integrand
  plus Fubini), and the box indicator `1_A(xᵢ)` is measurable;
* **boundedness on balls** — if `‖x‖ ≤ R` and `z ∈ A ⊆ acube ℓ` then `‖x|i↦z‖ ≤ max R ℓ`
  (`Gen.norm_update_le` and `Gen.norm_le_of_mem_acube`), so `|Ψ|` is bounded by the class bound
  `C(max R ℓ)`, whence `|∫_{z∈A} Ψ(x|i↦z)| ≤ C(max R ℓ)·|A|`
  (`MeasureTheory.norm_setIntegral_le_of_norm_le_const`, with `|A| < ∞` from `A ⊆ acube ℓ`).

Note that `volA` is an *arbitrary* real: the factor `1/volA` is controlled by its absolute value,
so no positivity (nor agreement with the actual measure of `A`) is needed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S.Gen

set_option autoImplicit false

local notation "kE3" => EuclideanSpace ℝ (Fin 3)

/-- **The box projection preserves the class `good`.**  If `f` is measurable and bounded on every
ball, so is `Pᵢf = UBBInputs8.boxPInd volA A i f` (with `A` a measurable subset of the cube
`acube ℓ`). -/
theorem boxPInd_mem_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {f : Submission.BoseGases.X N → ℝ} (hf : f ∈ Work.BoseFixB1S.Gen.good N) :
    Work.UBBInputs8.boxPInd volA A i f ∈ Work.BoseFixB1S.Gen.good N := by
  obtain ⟨hfm, hfb⟩ := mem_good_iff.mp hf
  refine mem_good_iff.mpr ⟨Work.BoseFixB1S.measurable_boxPInd volA A hA i hfm, ?_⟩
  intro R
  obtain ⟨C₀, hC₀⟩ := hfb (max R ℓ)
  have hAfin : (MeasureTheory.volume : MeasureTheory.Measure kE3) A < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  refine ⟨|1 / volA| * (max C₀ 0 * (MeasureTheory.volume A).toReal), fun x hx => ?_⟩
  -- the fibre integral obeys the class bound times the measure of `A`
  have hInt : |∫ z in A, f (Function.update x i z)|
      ≤ max C₀ 0 * (MeasureTheory.volume A).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := MeasureTheory.volume)
      (s := A) (f := fun z : kE3 => f (Function.update x i z)) (C := max C₀ 0) hAfin ?_
    · rwa [MeasureTheory.Measure.real_def, Real.norm_eq_abs] at h
    · intro z hz
      rw [Real.norm_eq_abs]
      have h1 : ‖Function.update x i z‖ ≤ max R ℓ :=
        le_trans (norm_update_le x i z)
          (max_le_max hx (norm_le_of_mem_acube hℓ.le (hAc hz)))
      exact le_trans (hC₀ _ h1) (le_max_left _ _)
  have hind : |A.indicator (fun _ : kE3 => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A
    · rw [Set.indicator_of_mem hxi]; norm_num
    · rw [Set.indicator_of_notMem hxi]; norm_num
  have hbdd : (0 : ℝ) ≤ |1 / volA| * (max C₀ 0 * (MeasureTheory.volume A).toReal) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg)
  simp only [Work.UBBInputs8.boxPInd]
  rw [abs_mul, abs_mul]
  calc |1 / volA| * |∫ z in A, f (Function.update x i z)|
        * |A.indicator (fun _ => (1 : ℝ)) (x i)|
      ≤ |1 / volA| * (max C₀ 0 * (MeasureTheory.volume A).toReal) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hInt (abs_nonneg _)) hind (abs_nonneg _) hbdd
    _ = |1 / volA| * (max C₀ 0 * (MeasureTheory.volume A).toReal) := by ring

end Work.BoseFixB1S.Gen
