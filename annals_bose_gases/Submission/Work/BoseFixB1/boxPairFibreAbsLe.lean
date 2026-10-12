import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Pair
import Submission.Work.BoseFixB1S.boxPQw_mass_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPairFibreAbsLe` — the box pair fibre is bounded by `4C²·ℓ^{3N}`

The box analogue of `Submission.BoseGases.pairFibreFun_abs_le`: for a state `Φ` bounded by `C`
on the dilated box `abox (N+2) ℓ`, the peeled pair fibre `boxPairFibreFun volA ℓ A Φ i j`
— the `r2`-integral of `PᵢPⱼΦ · QⱼQᵢΦ` at the doubly inserted configuration `(i↦y, j↦z)` —
obeys `|·| ≤ 4C²·ℓ^{3N}` for `y, z ∈ acube ℓ`.

Unlike the centred-cube version the proof needs no continuity of `Φ`: the FS-faithful box
projections `boxPInd`/`boxQInd` are bounded on the box by any bound of their argument
(`Work.BoseFixB1S.abs_boxPInd_le`, `Work.BoseFixB1S.abs_boxQInd_le`, both of which only need
the pointwise bound), whence `|PᵢPⱼΦ| ≤ C` and `|QⱼQᵢΦ| ≤ 4C` on `abox (N+2) ℓ`.  The
`r2`-integral of the product is then bounded by `4C²` times the box volume
`ℓ^{3N}` (`Submission.BoseGases.real_volume_abox`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem boxPairFibreAbsLe {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hΦB : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ, |Φ x| ≤ C)
    {i j : Fin (N + 2)} (hij : i ≠ j) {y z : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Submission.BoseGases.acube ℓ) (hz : z ∈ Submission.BoseGases.acube ℓ) :
    |Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y z| ≤ 4 * C ^ 2 * ℓ ^ (3 * N) := by
  rw [Work.BoseFixB1.boxPairFibreFun, dif_pos hij]
  set j' := Submission.BoseGases.sucAboveInv i j hij with hj'def
  -- `volA` in the `Measure.real` form used by the projection bounds
  have hvolA' : volA = MeasureTheory.volume.real A := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  -- `PⱼΦ` and `PᵢPⱼΦ` are bounded by `C` on the box
  have hPj : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Work.UBBInputs8.boxPInd volA A j Φ x| ≤ C :=
    fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hA hvolA hAc j hΦB x hx
  have hPij : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| ≤ C :=
    fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hvolpos hA hvolA hAc i hPj x hx
  -- `QᵢΦ` is bounded by `2C` and `QⱼQᵢΦ` by `4C` on the box
  have hQi : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C :=
    fun x hx => Work.BoseFixB1S.abs_boxQInd_le hℓ hvolpos hA hvolA' hAc i hΦB x hx
  have hQji : ∀ x ∈ Submission.BoseGases.abox (N + 2) ℓ,
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * C := by
    intro x hx
    have h := Work.BoseFixB1S.abs_boxQInd_le hℓ hvolpos hA hvolA' hAc j hQi x hx
    linarith
  set F : Submission.BoseGases.X N → ℝ := fun r2 =>
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
          (Submission.BoseGases.ins2 i j' y z r2))
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
            (Submission.BoseGases.ins2 i j' y z r2)) with hFdef
  change |∫ r2 in Submission.BoseGases.abox N ℓ, F r2| ≤ 4 * C ^ 2 * ℓ ^ (3 * N)
  -- the pointwise bound `|F| ≤ 4C²` on the box
  have hpt : ∀ᵐ r2 ∂((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)), ‖F r2‖ ≤ 4 * C ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
      with r2 hr2
    have hmem : Submission.BoseGases.ins2 i j' y z r2 ∈ Submission.BoseGases.abox (N + 2) ℓ :=
      Submission.BoseGases.ins2_mem_abox i j' hy hz hr2
    simp only [hFdef]
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
            (Submission.BoseGases.ins2 i j' y z r2)|
          * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2)|
        ≤ C * (4 * C) := mul_le_mul (hPij _ hmem) (hQji _ hmem) (abs_nonneg _) hC0
      _ = 4 * C ^ 2 := by ring
  haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
  calc |∫ r2 in Submission.BoseGases.abox N ℓ, F r2|
      = ‖∫ r2 in Submission.BoseGases.abox N ℓ, F r2‖ := (Real.norm_eq_abs _).symm
    _ ≤ (4 * C ^ 2) * ((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hpt
    _ = 4 * C ^ 2 * ℓ ^ (3 * N) := by
        rw [Submission.BoseGases.real_volume_abox N ℓ hℓ.le, pow_mul]

end Work.BoseFixB1
