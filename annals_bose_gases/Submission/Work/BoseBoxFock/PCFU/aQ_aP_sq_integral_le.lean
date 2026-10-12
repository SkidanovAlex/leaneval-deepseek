import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseFixB1S.CoordMeanDefs
import Submission.Work.BoseFixB1S.PiAnova.piVarianceDecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.aQ_aP_sq_integral_le`

The fluctuation of a slot mean is an `L²`-contraction on the centred box:

    ∫_{abox n ℓ} (Qⱼ (Pᵢ Φ))² ≤ ∫_{abox n ℓ} Φ²          (`Φ ∈ L²(abox n ℓ)`),

where `Pᵢ Φ x = (1/ℓ³)∫_{y ∈ acube ℓ} Φ(x[i ↦ y])` and `Qᵢ = 1 − Pᵢ` are the corpus's
condensate projection and its complement (`Submission.Q0Sector`).

The statement is the `L²`-twin of the corpus's `Continuous`-state chain: both
`Submission.BoseGases.aP_sq_le` and `Work.SmallBoxKinBridge.integral_aQ_sq_le` demand a
*continuous* state, whereas here only `MemLp Φ 2` is assumed — which is what the consumers of this
file have.

The proof is the projection algebra in `L²`.  The centred box carries the product measure
`π = Measure.pi (fun _ : Fin n => ν)` with the one-particle measure `ν = volume ↾ acube ℓ`
(`Submission.BoseGases.restrict_abox_eq_pi`), and under that identification

* `Pᵢ` **is** the coordinate mean `Work.BoseFixB1S.coordMean ν i` of the product measure
  (`aP_eq_coordMean`, `aP_eq_coordMean_pt`; purely definitional, the normalisation
  `ℓ³ = (ν univ).toReal` being `Submission.BoseGases.acube_volume`);
* the coordinate mean contracts `L²`
  (`Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le`, the fibre Cauchy–Schwarz);
* the **variance decomposition** (`coordMean_variance`, the `c = 0` case of
  `Work.BoseFixB1S.PiAnova.piVarianceDecomp`)
  `∫ (f − c)² = ∫ (f − E_j f)² + ∫ (E_j f − c)²`
  says that `1 − E_j` is an orthogonal projection, so the fluctuation contracts:
  `∫ (f − E_j f)² ≤ ∫ f²`.

Applying the last two to `f = Pᵢ Φ = Eᵢ Φ` gives the chain `∫ (Qⱼ Pᵢ Φ)² ≤ ∫ (Pᵢ Φ)² ≤ ∫ Φ²`.
(The hypothesis `i ≠ j` of the statement is *not* needed: both contractions hold for every pair of
slots, and — as the corpus does not either — no commutation of `Pᵢ` and `Qⱼ` is used.)

The file also records the two box-level contractions themselves (`aP_sq_integral_le_L2`,
`aQ_sq_integral_le_L2`), which are the `MemLp`-state twins of the corpus's
`Submission.BoseGases.aP_sq_le` and `Work.SmallBoxKinBridge.integral_aQ_sq_le`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## The identification of `aP` with the coordinate mean of the product measure -/

/-- **`aP ℓ m` is the coordinate mean of the centred-box product measure.**  This is a
definitional identification: the centred box carries the product of the one-particle measures
`ν = volume ↾ acube ℓ` (`Submission.BoseGases.restrict_abox_eq_pi`), `aP ℓ m` averages over the
`m`-th coordinate with the normalisation `ℓ³ = (ν univ).toReal`, and
`Work.BoseFixB1S.coordMean ν m` is the same average. -/
private lemma aP_eq_coordMean {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin N)
    (g : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.aP ℓ m g
      = Work.BoseFixB1S.coordMean ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
          m g := by
  have hV : (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ).toReal
      = ℓ ^ 3 := by
    rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  funext x
  rw [Work.BoseFixB1S.coordMean_apply, hV]
  rfl

/-- The same identification for a measure `ν` introduced by `set`, together with the equation
`ν = volume ↾ acube ℓ`. -/
private lemma aP_eq_coordMean_set {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ν : Measure E3}
    (hν : ν = (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) (m : Fin N)
    (g : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.aP ℓ m g = Work.BoseFixB1S.coordMean ν m g := by
  rw [aP_eq_coordMean hℓ m g, hν]

/-- Pointwise form of `aP_eq_coordMean_set`. -/
private lemma aP_eq_coordMean_pt {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {ν : Measure E3}
    (hν : ν = (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) (m : Fin N)
    (g : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Submission.BoseGases.aP ℓ m g x = Work.BoseFixB1S.coordMean ν m g x := by
  rw [aP_eq_coordMean_set hℓ hν m g]

/-- The centred box `abox N ℓ` carries the product of the one-particle measures `ν`.
(`Submission.BoseGases.restrict_abox_eq_pi`, with `ν` unfolded.) -/
private lemma restrict_abox_eq_pi' {N : ℕ} {ℓ : ℝ} :
    (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ) =
      Measure.pi (fun _ : Fin N => (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
  Submission.BoseGases.restrict_abox_eq_pi N ℓ

/-- The one-particle centred cube measure is finite. -/
private lemma isFiniteMeasure_acube {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ⟩

/-- `(ν univ).toReal = ℓ³` for the one-particle centred cube measure. -/
private lemma acube_univ_toReal {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ).toReal = ℓ ^ 3 := by
  rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity)]

/-! ## The variance identity in coordinate-mean form -/

/-- **The variance decomposition in the language of `coordMean`**: for a finite measure `ν` and an
`L²`-function `f` on the product space,

    `∫ f² = ∫ (f − E_j f)² + ∫ (E_j f)²`,   `E_j f = coordMean ν j f`.

This is the `c = 0` case of `Work.BoseFixB1S.PiAnova.piVarianceDecomp`, whose conclusion spells the
coordinate mean out; the three integral conversions below are the pointwise identities
`Work.BoseFixB1S.coordMean_apply` (`E_j f x = (ν univ).toReal⁻¹ ∫ z, f (update x j z) ∂ν`) and
`sub_zero`. -/
private lemma coordMean_variance {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [SigmaFinite ν] [IsFiniteMeasure ν] (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {f : (Fin (k + 1) → α) → ℝ}
    (hfm : AEStronglyMeasurable f (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hf2 : Integrable (fun x => (f x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    (∫ x, (f x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = (∫ x, (f x - Work.BoseFixB1S.coordMean ν j f x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        + ∫ x, (Work.BoseFixB1S.coordMean ν j f x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  have hvar := Work.BoseFixB1S.PiAnova.piVarianceDecomp ν hν j hfm hf2 0
  have e1 : (∫ x, (f x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = ∫ x, (f x - 0) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [sub_zero])).symm
  have e2 : (∫ x, (f x - (1 / (ν Set.univ).toReal) * ∫ z, f (Function.update x j z) ∂ν) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = ∫ x, (f x - Work.BoseFixB1S.coordMean ν j f x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Work.BoseFixB1S.coordMean_apply])
  have e3 : (∫ x, ((1 / (ν Set.univ).toReal) * ∫ z, f (Function.update x j z) ∂ν - 0) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = ∫ x, (Work.BoseFixB1S.coordMean ν j f x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Work.BoseFixB1S.coordMean_apply, sub_zero])
  rw [e2, e3] at hvar
  exact e1.trans hvar

/-- **The fluctuation of a coordinate mean contracts `L²`**: `∫ (f − E_j f)² ≤ ∫ f²`. -/
private lemma coordMean_variance_sq_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [SigmaFinite ν] [IsFiniteMeasure ν] (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {f : (Fin (k + 1) → α) → ℝ}
    (hfm : AEStronglyMeasurable f (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hf2 : Integrable (fun x => (f x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    (∫ x, (f x - Work.BoseFixB1S.coordMean ν j f x) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      ≤ ∫ x, (f x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  have hvar := coordMean_variance ν hν j hfm hf2
  have hnn : 0 ≤ ∫ x, (Work.BoseFixB1S.coordMean ν j f x) ^ 2
      ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    integral_nonneg fun x => sq_nonneg _
  linarith [hvar, hnn]

/-! ## The target -/

theorem aQ_aP_sq_integral_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : MeasureTheory.MemLp Φ 2 (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  rcases n with _ | k
  · exact i.elim0
  · set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hνdef
    haveI : IsFiniteMeasure ν := by rw [hνdef]; exact isFiniteMeasure_acube hℓ.le
    have hVpos : 0 < (ν Set.univ).toReal := by rw [hνdef, acube_univ_toReal hℓ]; positivity
    have hπ : (volume : Measure (Submission.BoseGases.X (k + 1))).restrict
        (Submission.BoseGases.abox (k + 1) ℓ) = Measure.pi (fun _ : Fin (k + 1) => ν) := by
      rw [restrict_abox_eq_pi', hνdef]
    have haesm : AEStronglyMeasurable Φ (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hπ]; exact hΦ.aestronglyMeasurable
    have h2 : Integrable (fun x => (Φ x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hπ]; exact (memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).mp hΦ
    -- `aP ℓ m` is the coordinate mean `coordMean ν m`
    have haP : ∀ (m : Fin (k + 1)) (g : Submission.BoseGases.X (k + 1) → ℝ),
        Submission.BoseGases.aP ℓ m g = Work.BoseFixB1S.coordMean ν m g :=
      fun m g => aP_eq_coordMean_set hℓ hνdef m g
    -- the slot-`i` mean lies in `L²` and contracts
    have hPint : Integrable (fun x => (Work.BoseFixB1S.coordMean ν i Φ x) ^ 2)
        (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      have := (Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le ν hVpos i haesm h2).1
      simpa only [Work.BoseFixB1S.coordMean_apply] using this
    have hPle : (∫ x, (Work.BoseFixB1S.coordMean ν i Φ x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        ≤ ∫ x, (Φ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      have := (Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le ν hVpos i haesm h2).2
      simpa only [Work.BoseFixB1S.coordMean_apply] using this
    -- the fluctuation of the slot-`i` mean contracts
    have hΨm : AEStronglyMeasurable (Work.BoseFixB1S.coordMean ν i Φ)
        (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      (Work.BoseFixB1S.aestronglyMeasurable_pi_coordMean ν i haesm).const_mul _
    have hQle := coordMean_variance_sq_le ν hVpos j hΨm hPint
    -- the pointwise identification of the integrands
    have hpoint : ∀ x : Submission.BoseGases.X (k + 1),
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2
          = (Work.BoseFixB1S.coordMean ν i Φ x
              - Work.BoseFixB1S.coordMean ν j (Work.BoseFixB1S.coordMean ν i Φ) x) ^ 2 := by
      intro x
      simp only [Submission.BoseGases.aQ, haP]
    calc (∫ x in Submission.BoseGases.abox (k + 1) ℓ,
            (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2)
        = ∫ x, (Work.BoseFixB1S.coordMean ν i Φ x
              - Work.BoseFixB1S.coordMean ν j (Work.BoseFixB1S.coordMean ν i Φ) x) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
          rw [hπ]
          exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ ≤ ∫ x, (Work.BoseFixB1S.coordMean ν i Φ x) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := hQle
      _ ≤ ∫ x, (Φ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := hPle
      _ = ∫ x in Submission.BoseGases.abox (k + 1) ℓ, (Φ x) ^ 2 := by rw [hπ]

/-! ## The two contractions at the level of the box

These are the box-level twins of the two ingredients above; the target is their composition (for
`Ψ = Pᵢ Φ`, which is in `L²(abox)` by the first of them).  They are also the promised
`MemLp`-state twins of the corpus's `Submission.BoseGases.aP_sq_le` and
`Work.SmallBoxKinBridge.integral_aQ_sq_le`. -/

/-- **The slot mean is an `L²`-contraction on the centred box.** -/
lemma aP_sq_integral_le_L2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : MeasureTheory.MemLp Φ 2
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  rcases N with _ | k
  · exact i.elim0
  · set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hνdef
    haveI : IsFiniteMeasure ν := by rw [hνdef]; exact isFiniteMeasure_acube hℓ.le
    have hVpos : 0 < (ν Set.univ).toReal := by rw [hνdef, acube_univ_toReal hℓ]; positivity
    have hπ : (volume : Measure (Submission.BoseGases.X (k + 1))).restrict
        (Submission.BoseGases.abox (k + 1) ℓ) = Measure.pi (fun _ : Fin (k + 1) => ν) := by
      rw [restrict_abox_eq_pi', hνdef]
    have haesm : AEStronglyMeasurable Φ (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hπ]; exact hΦ.aestronglyMeasurable
    have h2 : Integrable (fun x => (Φ x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hπ]; exact (memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).mp hΦ
    have hmain : (∫ x, (Work.BoseFixB1S.coordMean ν i Φ x) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        ≤ ∫ x, (Φ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      have := (Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le ν hVpos i haesm h2).2
      simpa only [Work.BoseFixB1S.coordMean_apply] using this
    have hbox : (∫ x in Submission.BoseGases.abox (k + 1) ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) ^ 2)
        = ∫ x, (Work.BoseFixB1S.coordMean ν i Φ x) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [hπ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [aP_eq_coordMean_pt hℓ hνdef i Φ]
    rw [hbox, hπ]
    exact hmain

/-- **The fluctuation is an `L²`-contraction on the centred box.** -/
lemma aQ_sq_integral_le_L2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨm : MeasureTheory.AEStronglyMeasurable Ψ
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)))
    (hΨ2 : MeasureTheory.Integrable (fun x => (Ψ x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Ψ x) ^ 2 := by
  rcases N with _ | k
  · exact i.elim0
  · set ν : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hνdef
    haveI : IsFiniteMeasure ν := by rw [hνdef]; exact isFiniteMeasure_acube hℓ.le
    have hVpos : 0 < (ν Set.univ).toReal := by rw [hνdef, acube_univ_toReal hℓ]; positivity
    have hπ : (volume : Measure (Submission.BoseGases.X (k + 1))).restrict
        (Submission.BoseGases.abox (k + 1) ℓ) = Measure.pi (fun _ : Fin (k + 1) => ν) := by
      rw [restrict_abox_eq_pi', hνdef]
    have haesm : AEStronglyMeasurable Ψ (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hπ]; exact hΨm
    have h2 : Integrable (fun x => (Ψ x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      rw [← hπ]; exact hΨ2
    have haP : ∀ m : Fin (k + 1),
        Submission.BoseGases.aP ℓ m Ψ = Work.BoseFixB1S.coordMean ν m Ψ :=
      fun m => aP_eq_coordMean_set hℓ hνdef m Ψ
    have hQle := coordMean_variance_sq_le ν hVpos i haesm h2
    have hpoint : ∀ x : Submission.BoseGases.X (k + 1),
        (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2
          = (Ψ x - Work.BoseFixB1S.coordMean ν i Ψ x) ^ 2 := by
      intro x
      simp only [Submission.BoseGases.aQ, haP]
    calc (∫ x in Submission.BoseGases.abox (k + 1) ℓ, (Submission.BoseGases.aQ ℓ i Ψ x) ^ 2)
        = ∫ x, (Ψ x - Work.BoseFixB1S.coordMean ν i Ψ x) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
          rw [hπ]
          exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ ≤ ∫ x, (Ψ x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := hQle
      _ = ∫ x in Submission.BoseGases.abox (k + 1) ℓ, (Ψ x) ^ 2 := by rw [hπ]

end Work.BoseBoxFock.PCFU
