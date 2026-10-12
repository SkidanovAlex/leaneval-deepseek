import ChallengeDeps
import Submission.Work.BoseFixB1.integrableOn_pairCross_pieces_w1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorAux

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open Work.UBBInputs8
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# `Work.BoseFixB1.SectorAux.integrableOn_pairCross_pieces_w1_g`

The generalised (measurable + box-bounded) form of
`Work.BoseFixB1.integrableOn_pairCross_pieces_w1`: the hypothesis `Continuous Φ` is replaced by
`Measurable Φ` together with a uniform bound `|Φ| ≤ Cb` on the analysis box `abox N ℓ`.

Nothing else changes: both integrands factor as `(prefactor) · wSmallPair M ℓ d u (g₀ v h)`,
with the prefactor a product of two box projections of `Φ`, hence measurable
(`Work.BoseFixB1S.measurable_boxPInd`, `measurable_boxQInd`) and bounded on the box by
`Work.BoseFixB1.boxProjBoundsReal` — at the bound `|Cb|` (a `P`-reading preserves the bound, a
`Q`-reading doubles it).  The slot kernel is then handled by `integrableOn_slot_wSmallPair`, whose
only requirements on the prefactor are a.e. strong measurability and an a.e. bound.
-/

theorem integrableOn_pairCross_pieces_w1_g {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
    {s t : Fin N} (hst : s ≠ t) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x s) (x t)))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) t
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s Φ) x)
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
  -- the bound on `Φ` holds at the nonnegative constant `|Cb|`
  have hΦb2 : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ |Cb| :=
    fun x hx => le_trans (hΦb x hx) (le_abs_self Cb)
  -- the numerator `g₀` of the `w₁`-kernel: integrable, supported in `‖z‖ ≤ R0`
  have hg0Int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0Zero : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- the box projection bounds, at the volume `boxMass ℓ d u`, with constant `|Cb|`
  have hbd : ∀ i j : Fin N,
      (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ |Cb|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ 2 * |Cb|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ |Cb|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 2 * |Cb|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 2 * |Cb|)
      ∧ (∀ x ∈ Submission.BoseGases.abox N ℓ,
          |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x| ≤ 4 * |Cb|) := by
    intro i j
    simpa only [← hVeq] using boxProjBoundsReal (N := N) hℓ hA hAc hΦb2 i j
  have hC0 : 0 ≤ 2 * |Cb| * |Cb| := by positivity
  -- a.e. version of a bound that holds everywhere on the box
  have ae_abox : ∀ {p : Submission.BoseGases.X N → Prop},
      (∀ x ∈ Submission.BoseGases.abox N ℓ, p x) →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)), p x :=
    fun hp => (MeasureTheory.ae_restrict_iff'
      (Submission.BoseGases.abox_measurable N ℓ)).mpr (Filter.Eventually.of_forall hp)
  -- measurability of the two prefactors
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
  have hsmB : Measurable (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) t
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s Φ) x)
        * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)) :=
    (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) hA t
        (Work.BoseFixB1S.measurable_boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (A := Submission.BoseGases.dlBox ℓ d u) hA s hΦm)).mul
      (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) hA s
        (Work.BoseFixB1S.measurable_boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) hA t hΦm))
  -- a.e. bounds of the two prefactors
  have haeA : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      |(Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)| ≤ 2 * |Cb| * |Cb| := by
    refine ae_abox (fun x hx => ?_)
    rw [abs_mul]
    exact mul_le_mul ((hbd s t).2.2.2.1 x hx) ((hbd s t).2.2.1 x hx)
      (abs_nonneg _) (by positivity)
  have haeB : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      |(Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) t
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)| ≤ 2 * |Cb| * |Cb| := by
    refine ae_abox (fun x hx => ?_)
    rw [abs_mul]
    exact mul_le_mul ((hbd t s).2.2.2.1 x hx) ((hbd s t).2.2.1 x hx)
      (abs_nonneg _) (by positivity)
  refine ⟨?_, ?_⟩
  · have hmain := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
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
      (i := s) (j := t) hsmA.aestronglyMeasurable (B := 2 * |Cb| * |Cb|) hC0 haeA
    simpa only [Submission.BoseGases.wSmall1Pair] using hmain
  · have hmain := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0)
      hℓ hd hg0Int hg0Zero hM hR hRχ u hst
      (S := fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) t
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x))
      (i := s) (j := t) hsmB.aestronglyMeasurable (B := 2 * |Cb| * |Cb|) hC0 haeB
    simpa only [Submission.BoseGases.wSmall1Pair] using hmain

end Work.BoseFixB1.SectorAux
