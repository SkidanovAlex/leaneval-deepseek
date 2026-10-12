import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.HighMass

open MeasureTheory

/-- **Peeling the slot-`i` integration of the large-momentum form.**

The slot-`i` lifting of the large-momentum form `momForm ℓ d 0` against the centred box
indicator `indU ℓ 0 = 1_{[−ℓ/2,ℓ/2]³}` in slot `i` of an `(m+1)`-particle configuration
integrated over `abox (m+1) ℓ` is exactly the integral of the same form applied to the
slot-`i` fibre over the remaining `m` coordinates, restricted to `abox m ℓ`:

    `ℓ⁻³ ∫_{abox (m+1) ℓ} 1_{Λ(0)}(xᵢ)·momForm(fibreᵢ Φ x) d x
        = ∫_{abox m ℓ} momForm(fibreᵢ Φ (kcInsN m i (0,r))) d r`.

The inserted coordinate `xᵢ` is integrated out: the fibre `fibre (m+1) i Φ x` depends only on
`x_{≠i}`, and its `xᵢ`-integration against the box indicator `indU ℓ 0` (whose integral is the
lattice volume `ℓ³`) cancels the `ℓ⁻³` prefactor.  The identification of the box is the
membership equivalence `kcInsN m i (y,r) ∈ abox (m+1) ℓ ↔ y ∈ acube ℓ ∧ r ∈ abox m ℓ`.

The proof is unconditional in `Φ` (no measurability, smoothness or integrability is used):
after `MeasurePreserving.integral_comp'` for the measure preserving equivalence `kcInsN m i`
the integrand is a product of a function of the inserted coordinate and a function of the
remaining coordinates, and the Bochner Fubini `MeasureTheory.integral_prod_mul` needs no
hypotheses. -/
theorem momForm_fibre_peel {ℓ d : ℝ} (hℓ : 0 < ℓ) {m : ℕ} (i : Fin (m + 1))
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} :
    ℓ ^ (-3 : ℤ) * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x)
      = ∫ r in Submission.BoseGases.abox m ℓ,
          Work.BoseKinLoc.momForm ℓ d 0
            (Work.BoseKinLoc.fibre (m + 1) i Φ (Submission.BoseGases.kcInsN m i (0, r))) := by
  -- the full `abox` integrand and the peeled integrand as local abbreviations
  set F : Submission.BoseGases.X (m + 1) → ℝ := fun x =>
      Work.BoseKinLoc.indU ℓ 0 (x i) *
        Work.BoseKinLoc.momForm ℓ d 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x) with hF
  set G : Submission.BoseGases.X m → ℝ := fun r =>
      Work.BoseKinLoc.momForm ℓ d 0
        (Work.BoseKinLoc.fibre (m + 1) i Φ (Submission.BoseGases.kcInsN m i (0, r))) with hG
  -- re-inserting any coordinate in slot `i` leaves the fibre unchanged
  have hfib : ∀ (y : ℝ³) (r : Submission.BoseGases.X m),
      Work.BoseKinLoc.fibre (m+1) i Φ (Submission.BoseGases.kcInsN m i (y, r))
        = Work.BoseKinLoc.fibre (m+1) i Φ (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro y r
    funext z
    simp only [Work.BoseKinLoc.fibre, Submission.BoseGases.update_kcInsN]
  -- the box membership under the coordinate split
  have hmem : ∀ (y : ℝ³) (r : Submission.BoseGases.X m),
      Submission.BoseGases.kcInsN m i (y, r) ∈ Submission.BoseGases.abox (m + 1) ℓ
      ↔ y ∈ Submission.BoseGases.acube ℓ ∧ r ∈ Submission.BoseGases.abox m ℓ := by
    intro y r
    rw [Submission.BoseGases.mem_abox_iff, Submission.BoseGases.mem_abox_iff]
    constructor
    · intro H
      refine ⟨by simpa [Submission.BoseGases.kc_insN_apply_same] using H i, ?_⟩
      intro j
      simpa [Submission.BoseGases.kc_insN_apply_succ] using H (i.succAbove j)
    · rintro ⟨hy, hr⟩ j
      by_cases hj : j = i
      · subst hj; simpa [Submission.BoseGases.kc_insN_apply_same] using hy
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
        subst hk
        simpa [Submission.BoseGases.kc_insN_apply_succ] using hr k
  -- the centred box is the moving box at `u = 0`, so `indU ℓ 0` vanishes off `acube ℓ`
  have hindU0 : ∀ y : ℝ³, y ∉ Submission.BoseGases.acube ℓ → Work.BoseKinLoc.indU ℓ 0 y = 0 := by
    intro y hy
    have hlamBox : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
      ext x; simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
    rw [Work.BoseKinLoc.indU]
    exact Set.indicator_of_notMem (by rwa [hlamBox]) (fun _ => (1 : ℝ))
  -- the pointwise factorisation of the box-restricted integrand
  have hH : ∀ (y : ℝ³) (r : Submission.BoseGases.X m),
      (Submission.BoseGases.abox (m + 1) ℓ).indicator F (Submission.BoseGases.kcInsN m i (y, r))
      = Work.BoseKinLoc.indU ℓ 0 y * (Submission.BoseGases.abox m ℓ).indicator G r := by
    intro y r
    by_cases hr : r ∈ Submission.BoseGases.abox m ℓ
    · by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · simp only [hF, hG]
        rw [Set.indicator_of_mem ((hmem y r).mpr ⟨hy, hr⟩), Set.indicator_of_mem hr,
            Submission.BoseGases.kc_insN_apply_same, hfib y r]
      · rw [Set.indicator_of_notMem (fun h => hy ((hmem y r).mp h).1), hindU0 y hy]
        simp
    · rw [Set.indicator_of_notMem (fun h => hr ((hmem y r).mp h).2),
          Set.indicator_of_notMem hr]
      simp
  -- Step 1: replace the `abox`-restricted integral by the indicator integral and split the
  -- inserted coordinate with the measure preserving equivalence `kcInsN m i`
  have hStep1 : ∫ x in Submission.BoseGases.abox (m + 1) ℓ, F x
      = ∫ p : ℝ³ × Submission.BoseGases.X m,
          (Submission.BoseGases.abox (m + 1) ℓ).indicator F (Submission.BoseGases.kcInsN m i p) := by
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable (m + 1) ℓ)]
    rw [← (Submission.BoseGases.kc_mp_insN m i).integral_comp'
        (fun x : Submission.BoseGases.X (m + 1) =>
          (Submission.BoseGases.abox (m + 1) ℓ).indicator F x)]
  -- Step 2: pointwise factorisation of the integrand
  have hStep2 : ∫ p : ℝ³ × Submission.BoseGases.X m,
          (Submission.BoseGases.abox (m + 1) ℓ).indicator F (Submission.BoseGases.kcInsN m i p)
      = ∫ p : ℝ³ × Submission.BoseGases.X m,
          Work.BoseKinLoc.indU ℓ 0 p.1 * (Submission.BoseGases.abox m ℓ).indicator G p.2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    exact hH p.1 p.2
  -- Step 3: Fubini over the product measure
  have hStep3 : ∫ p : ℝ³ × Submission.BoseGases.X m,
          Work.BoseKinLoc.indU ℓ 0 p.1 * (Submission.BoseGases.abox m ℓ).indicator G p.2
      = (∫ y : ℝ³, Work.BoseKinLoc.indU ℓ 0 y) *
        (∫ r : Submission.BoseGases.X m, (Submission.BoseGases.abox m ℓ).indicator G r) := by
    rw [MeasureTheory.Measure.volume_eq_prod,
        MeasureTheory.integral_prod_mul (fun y : ℝ³ => Work.BoseKinLoc.indU ℓ 0 y)
          (fun r : Submission.BoseGases.X m => (Submission.BoseGases.abox m ℓ).indicator G r)]
  -- the inserted coordinate integrates to the volume `ℓ³` of the box
  have hacube : (∫ y : ℝ³, Work.BoseKinLoc.indU ℓ 0 y) = ℓ ^ 3 :=
    Work.BoseKinLoc.Word.integral_indU_eq hℓ 0
  -- the remaining coordinates give back the `abox m ℓ`-restricted integral
  have habox : (∫ r : Submission.BoseGases.X m, (Submission.BoseGases.abox m ℓ).indicator G r)
      = ∫ r in Submission.BoseGases.abox m ℓ, G r :=
    MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable m ℓ)
  rw [hStep1, hStep2, hStep3, hacube, habox]
  -- the `ℓ⁻³` prefactor cancels the volume `ℓ³`
  rw [← mul_assoc, show ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 from by
        rw [← zpow_natCast ℓ 3, ← zpow_add₀ (ne_of_gt hℓ)]
        norm_num, one_mul]

end Work.BoseFixB3.HighMass
