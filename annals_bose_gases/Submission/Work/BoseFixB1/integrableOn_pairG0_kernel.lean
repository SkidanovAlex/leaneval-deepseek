import ChallengeDeps
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1.boxProjBoundsReal
import Submission.Work.BoseFixB1S.boxPQw_mass_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrableOn_pairG0_kernel`

`IntegrableOn`-ness, over the analysis box `abox N ℓ`, of the localised `g₀`-pair kernel
weighted by the box-projected pair prefactor

  `P_s(Q_t Φ) · P_s(P_t Φ) · w₁(x_s, x_t)`,  `w₁ := wSmall1Pair h M ℓ d u`.

The proof is the first half of `Work.BoseFixB1.integrableOn_pairCross_pieces_w1` with the
superfluous `MemLp v 1` hypothesis dropped (`w₁`'s numerator is `g₀ = v(1−w₀)`, whose
integrability and support follow from the scattering data alone, `BoseGases.g0_integrable`,
`BoseGases.g0_zero_of_norm_ge`):

* the prefactor is a product of two box projections of the continuous `Φ`, hence **measurable**
  (`Work.BoseFixB1S.measurable_boxPInd`, `Work.BoseFixB1S.measurable_boxQInd`) and **bounded on
  the compact box** `abox N ℓ` by `2·|Bf|·|Bf|` (`boxProjBoundsReal`: `P` is a contraction,
  `Q` costs a factor two);
* the slot kernel is then dominated by `C·|g₀(x_s − x_t)|` with `g₀ ∈ L¹`, which is the
  content of the general slot lemma `Work.BoseFixB1.integrableOn_slot_wSmallPair`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases
open Work.UBBInputs8
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem integrableOn_pairG0_kernel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x s) (x t)))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  classical
  -- the volume `boxMass ℓ d u` is the measure of the small box `dlBox ℓ d u`
  have hVeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- `Φ` is bounded on the compact analysis box
  obtain ⟨Bf, hBf⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ |Bf| := by
    intro x hx
    have hh := hBf x hx
    rw [Real.norm_eq_abs] at hh
    exact le_trans hh (le_abs_self Bf)
  have hΦm : Measurable Φ := hΦc.measurable
  -- the numerator `g₀` of the `w₁`-kernel: integrable, supported in `‖z‖ ≤ R0`
  have hg0Int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0Zero : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- the box projection bounds, at the volume `boxMass ℓ d u`
  have hbd : ∀ i j : Fin N,
      (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 4 * |Bf|) := by
    intro i j
    simpa only [← hVeq] using boxProjBoundsReal (N := N) hℓ hA hAc hΦb i j
  have hC0 : 0 ≤ 2 * |Bf| * |Bf| := by positivity
  -- a.e. version of a bound that holds everywhere on the box
  have ae_abox : ∀ {p : Submission.BoseGases.X N → Prop},
      (∀ x ∈ Submission.BoseGases.abox N ℓ, p x) →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)), p x :=
    fun hp => (MeasureTheory.ae_restrict_iff'
      (Submission.BoseGases.abox_measurable N ℓ)).mpr (Filter.Eventually.of_forall hp)
  -- measurability of the prefactor
  have hsmA : Measurable (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) s
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
        * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)) :=
    (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) hA s
        (Work.BoseFixB1S.measurable_boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (A := Submission.BoseGases.dlBox ℓ d u) hA t hΦm)).mul
      (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) hA s
        (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) hA t hΦm))
  -- a.e. bound of the prefactor
  have haeA : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      |(Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)| ≤ 2 * |Bf| * |Bf| := by
    refine ae_abox (fun x hx => ?_)
    rw [abs_mul]
    exact mul_le_mul ((hbd s t).2.2.2.1 x hx) ((hbd s t).2.2.1 x hx)
      (abs_nonneg _) (by positivity)
  -- the general slot lemma with numerator `g₀` and the bounded prefactor above
  have hmain := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
    hℓ hd hg0Int hg0Zero hM hR hRχ u hst
    (S := fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) s
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
        * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x))
    (i := s) (j := t) hsmA.aestronglyMeasurable (B := 2 * |Bf| * |Bf|) hC0 haeA
  simpa only [Submission.BoseGases.wSmall1Pair] using hmain

end Work.BoseFixB1
