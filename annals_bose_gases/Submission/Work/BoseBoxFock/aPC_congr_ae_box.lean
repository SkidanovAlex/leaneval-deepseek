import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.cIPn_sum_aPC_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aPC_congr_ae_box`

The slot mean `aPC ℓ i Ψ x = ℓ⁻³ ∫_{acube ℓ} Ψ (x[i ↦ y]) dy` only sees the values of `Ψ`
*inside* the box `abox (n+1) ℓ`: modifying `Ψ` on a null subset of the box (a null set for the
measure `volume.restrict (abox (n+1) ℓ)`) does not change `aPC ℓ i Ψ` a.e. on the box.

This is the box-relative companion of `Work.BoseBoxFock.ae_aPC_congr`
(`cIPn_sum_aPC_re.lean`), which assumes a *global* a.e. equality
`Θ =ᵐ[volume] g'`.  The hypothesis here is the one that arises in the applications, where the
state is only known a.e. **on the box**.

The point of the argument.  Let `A := abox (n+1) ℓ` and `B := acube ℓ`.  If `D ⊆ Xn (n+1)` is
the (a priori non-measurable) set where `f` and `g` differ, then `volume (A ∩ D) = 0`; replacing
`D` by a measurable superset and intersecting with `A` we get a *globally* null measurable set
`M ⊇ A ∩ D`.  Since `x ∈ A` and `y ∈ B` imply `x[i ↦ y] ∈ A`, the set of "bad" pairs is contained
in `{(x,y) | x[i ↦ y] ∈ M}`, and by `prod_update_preimage_null` this is null for
`volume.prod volume` on `Xn (n+1) × Sp`, hence also for the restricted product
`(volume.restrict A).prod (volume.restrict B)` (monotonicity; note the restricted product is the
*smaller* measure, so `ae_mono` transfers the a.e. statement in the right direction).
`Measure.ae_prod_iff_ae_ae` then iterates, and for a.e. `x` the two slot fibres agree a.e. in `y`,
so their Bochner integrals agree (`integral_congr_ae`, which needs no integrability hypothesis).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-- **Box-relative null sets are invisible to the fibre integral.**  If two states agree a.e. on
the box `abox (n+1) ℓ` (for the restricted measure), then their fibres along the map
`y ↦ x[i ↦ y]` agree a.e. in `y ∈ acube ℓ`, for a.e. `x` in the box. -/
theorem ae_update_eq_of_ae_eq_abox {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1))
    {Θ g' : Work.BoseDict.Xn (n + 1) → ℂ}
    (h : Θ =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (n + 1)))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)] g') :
    ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (n + 1)))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ),
      ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp)).restrict
          (Submission.BoseGases.acube ℓ),
        Θ (Function.update x i y) = g' (Function.update x i y) := by
  have hbad : ((volume : Measure (Work.BoseDict.Xn (n + 1))).restrict
      (Submission.BoseGases.abox (n + 1) ℓ)) {x | ¬ (Θ x = g' x)} = 0 :=
    MeasureTheory.ae_iff.mp h
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  -- `N ⊇ {Θ ≠ g'}` is measurable and null for the restricted measure; `M := N ∩ A` is then
  -- a *globally* null measurable set containing the bad set of the box.
  have hM0 : (volume : Measure (Work.BoseDict.Xn (n + 1)))
      (N ∩ Submission.BoseGases.abox (n + 1) ℓ) = 0 := by
    rw [← Measure.restrict_apply hNm]
    exact hN0
  have hMm : MeasurableSet (N ∩ Submission.BoseGases.abox (n + 1) ℓ) :=
    hNm.inter (Submission.BoseGases.abox_measurable (n + 1) ℓ)
  have hS0 := prod_update_preimage_null (n := n) i hMm hM0
  have hmeas : MeasurableSet {p : Work.BoseDict.Xn (n + 1) × Work.BoseDict.Sp |
      ¬ (Function.update p.1 i p.2 ∈ N ∩ Submission.BoseGases.abox (n + 1) ℓ)} :=
    (hMm.preimage (by fun_prop)).compl
  have hae0 : ∀ᵐ p ∂((volume : Measure (Work.BoseDict.Xn (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)).prod
        ((volume : Measure Work.BoseDict.Sp).restrict (Submission.BoseGases.acube ℓ)),
      ¬ (Function.update p.1 i p.2 ∈ N ∩ Submission.BoseGases.abox (n + 1) ℓ) := by
    have hle : ((volume : Measure (Work.BoseDict.Xn (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)).prod
        ((volume : Measure Work.BoseDict.Sp).restrict (Submission.BoseGases.acube ℓ))
        ≤ (volume : Measure (Work.BoseDict.Xn (n + 1))).prod
            (volume : Measure Work.BoseDict.Sp) :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    have hbig : ∀ᵐ p ∂(volume : Measure (Work.BoseDict.Xn (n + 1))).prod
        (volume : Measure Work.BoseDict.Sp),
        p ∉ ({p : Work.BoseDict.Xn (n + 1) × Work.BoseDict.Sp |
          Function.update p.1 i p.2 ∈ N ∩ Submission.BoseGases.abox (n + 1) ℓ}) :=
      (MeasureTheory.compl_mem_ae_iff).mpr hS0
    exact MeasureTheory.ae_mono hle hbig
  have hiter := (Measure.ae_prod_iff_ae_ae (μ := (volume : Measure (Work.BoseDict.Xn (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ))
      (ν := (volume : Measure Work.BoseDict.Sp).restrict (Submission.BoseGases.acube ℓ))
      hmeas).mp hae0
  filter_upwards [hiter,
    MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable (n + 1) ℓ)] with x hx hxA
  have hxA' : ∀ k : Fin (n + 1), x k ∈ Submission.BoseGases.acube ℓ := by
    rwa [Submission.BoseGases.mem_abox_iff] at hxA
  filter_upwards [hx,
    MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)] with y hy hyB
  -- `x ∈ A` and `y ∈ B` force `x[i ↦ y] ∈ A`, so `x[i ↦ y] ∉ M` means `x[i ↦ y] ∉ N`.
  have hmemA : Function.update x i y ∈ Submission.BoseGases.abox (n + 1) ℓ := by
    rw [Submission.BoseGases.mem_abox_iff]
    intro k
    by_cases hk : k = i
    · subst hk; simp [hyB]
    · rw [Function.update_of_ne hk]; exact hxA' k
  by_contra hne
  exact hy ⟨hNsub hne, hmemA⟩

theorem aPC_congr_ae_box {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {f g : Work.BoseDict.Xn (n + 1) → ℂ}
    (h : f =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ))] g) :
    Work.BoseBoxFock.aPC ℓ i f =ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ))] Work.BoseBoxFock.aPC ℓ i g := by
  filter_upwards [ae_update_eq_of_ae_eq_abox (ℓ := ℓ) i h] with x hx
  unfold Work.BoseBoxFock.aPC
  rw [MeasureTheory.integral_congr_ae hx]

end Work.BoseBoxFock
