/-
Copyright: work module for the Elgindi finite-time singularity project.

# Level-six slot machinery for the `T1` slot estimate

This file provides, at level six, the elementary slot facts that the per-slot `D_θ`-transport
estimate `Work.FTS.StrongPersist.N6Trans.slotT1Six` consumes:

* `SlotW6 α q X f` — the predicate "the `canonW q`-weighted square of `X` is dominated
  pointwise by the `ℋ⁶`-integrand of `f`" (the level-six analogue of
  `Work.FTS.TransportS.SlotT2.SlotW`);
* the instances `slotW6_z` (a pure `D_z`-slot `D_z^j f`, `j ≤ 6`, priced with `q ≤ η`) and
  `slotW6_mixed` (a mixed slot `D_z^jD_θ^i f`, `1 ≤ i`, `i + j ≤ 6`, priced with `q ≤ γ`);
* `cs_engine6` — the two-level Cauchy–Schwarz
  `∫_z∫_θ canonW q |X| |Y| ≤ |f|_{ℋ⁶} |g|_{ℋ⁶}` for two such slots;
* the energy bounds `energy_z6`, `energy_mixed6`: `∫_z∫_θ canonW q X² ≤ HkSq α 6 f`;
* `supSix` — the pointwise bound `|D_z^bD_θ^a h| ≤ C α^{-1/2} |h|_{ℋ⁶}` for `a + b ≤ 4`,
  obtained from the proved level-six pointwise bound `Work.FTS.StrongPersist.N6.PwAny6`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.slotCS
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_eta_eq canonW_gam_eq
  canonW_mono cs_sqrt_le)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The slot predicate at level six -/

/-- A function `X` is a canonical slot of `ℋ⁶` for the datum `f` with exponent `q` if its
`canonW q`-weighted square is dominated, pointwise on `Iz × Iθ`, by the `ℋ⁶`-integrand of
`f`.  This is the level-six analogue of `Work.FTS.TransportS.SlotT2.SlotW`, and it is the
only property of a slot that the Cauchy–Schwarz bound uses. -/
structure SlotW6 (α q : ℝ) (X : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  le : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
    canonW q z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ

/-- The pointwise domination of a pure `D_z`-slot `D_z^j h`, `j ≤ 6`, at the exponent `q ≤ η`. -/
theorem canonW_mul_z_le6 (α : ℝ) (h : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ 6) :
    canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθ]
    exact canonW_mono hq0 hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j h z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 6 h z θ j hj

/-- The pointwise domination of a mixed slot `D_z^jD_θ^i h`, `1 ≤ i`, `i + j ≤ 6`, at the
exponent `q ≤ γ`. -/
theorem canonW_mul_mixed_le6 (α : ℝ) (h : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 h z θ := by
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθ]
    exact canonW_mono hq0 hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i h z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 h z θ i j hi hij

/-- A pure `D_z`-slot `D_z^j h`, `j ≤ 6`, priced with `q ≤ η`. -/
theorem slotW6_z (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    (h : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 6) :
    SlotW6 α q (Work.Spaces.DzIter j h) h := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 6 h 0 θ
  · exact canonW_mul_z_le6 α h hq0 hq hθ j hj

/-- A mixed slot `D_z^jD_θ^i h`, `1 ≤ i`, `i + j ≤ 6`, priced with `q ≤ γ`. -/
theorem slotW6_mixed (α : ℝ) {q : ℝ} (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (h : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    SlotW6 α q (Work.Spaces.mixed j i h) h := by
  refine ⟨fun z hz θ hθ => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 6 h 0 θ
  · exact canonW_mul_mixed_le6 α h hq0 hqγ hθ j i hi hij

/-! ## The two-level Cauchy–Schwarz engine at level six -/

/-- **The level-six Cauchy–Schwarz engine.**  For two canonical `ℋ⁶`-slots `X`, `Y` (of `f`
resp. `g`) priced with the same exponent `q`,

  `∫_z∫_θ canonW q z θ |X| |Y| ≤ √(HkSq α 6 f) · √(HkSq α 6 g)`.

This is `Work.FTS.TransportS.SlotT2.slotCS_engine` with `4` replaced by `6` (the pointwise
domination turns the integrand into the product of the `L²`-functions
`√(HkIntegrand α 6 f)`, `√(HkIntegrand α 6 g)`). -/
theorem cs_engine6 (α : ℝ) {q : ℝ} {X Y f g : ℝ → ℝ → ℝ}
    (hX : SlotW6 α q X f) (hY : SlotW6 α q Y g)
    (hmemf : Work.Spaces.HkMem α 6 f) (hmemg : Work.Spaces.HkMem α 6 g) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ|)
      ≤ Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ with hG
  have hFnn : ∀ z, 0 ≤ F z := fun z => MeasureTheory.setIntegral_nonneg hIθm
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
  have hGnn : ∀ z, 0 ≤ G z := fun z => MeasureTheory.setIntegral_nonneg hIθm
    (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
  have hFint : IntegrableOn F Work.Spaces.Iz := hmemf.2
  have hGint : IntegrableOn G Work.Spaces.Iz := hmemg.2
  have hpt : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
      canonW q z θ * |X z θ| * |Y z θ|) ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hdom : ∀ θ ∈ Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) *
            Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
      intro θ hθ
      have hc : 0 ≤ canonW q z θ := canonW_nonneg hθ
      have hs : Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ) = canonW q z θ := by
        rw [← sq, Real.sq_sqrt hc]
      calc canonW q z θ * |X z θ| * |Y z θ|
          = (Real.sqrt (canonW q z θ) * Real.sqrt (canonW q z θ)) * |X z θ| * |Y z θ| := by
            rw [hs]
        _ = Real.sqrt (canonW q z θ * (X z θ) ^ 2)
              * Real.sqrt (canonW q z θ * (Y z θ) ^ 2) := by
            rw [Real.sqrt_mul hc, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
            ring
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) *
              Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) :=
            mul_le_mul (Real.sqrt_le_sqrt (hX.le z hz θ hθ))
              (Real.sqrt_le_sqrt (hY.le z hz θ hθ))
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hf_sq : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      (hmemf.1 z hz).congr (Filter.Eventually.of_forall
        (fun θ => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)).symm))
    have hg_sq : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      (hmemg.1 z hz).congr (Filter.Eventually.of_forall
        (fun θ => (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)).symm))
    have hf_meas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable (hmemf.1 z hz).aestronglyMeasurable
    have hg_meas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable (hmemg.1 z hz).aestronglyMeasurable
    have hf_lp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) := (memLp_two_iff_integrable_sq hf_meas).mpr hf_sq
    have hg_lp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) 2
        (volume.restrict Work.Spaces.Iθ) := (memLp_two_iff_integrable_sq hg_meas).mpr hg_sq
    have hprod : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) *
        Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) (volume.restrict Work.Spaces.Iθ) :=
      memLp_one_iff_integrable.mp (hf_lp.mul hg_lp)
    calc (∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) *
            Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) :=
          integral_mono_of_nonneg
            (ae_restrict_of_forall_mem hIθm (fun θ hθ =>
              mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _)) (abs_nonneg _)))
            hprod (ae_restrict_of_forall_mem hIθm hdom)
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) *
            Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 g z θ) :=
          cs_sqrt_le (hmemf.1 z hz) (hmemg.1 z hz)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
      _ = Real.sqrt (F z) * Real.sqrt (G z) := by rw [hF, hG]
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * |X z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := by
    refine integral_mono_of_nonneg ?_ ?_ (ae_restrict_of_forall_mem hIzm hpt)
    · exact ae_restrict_of_forall_mem hIzm (fun z hz => MeasureTheory.setIntegral_nonneg hIθm
        (fun θ hθ => mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _)) (abs_nonneg _)))
    · have hF_meas : AEStronglyMeasurable (fun z => Real.sqrt (F z))
          (volume.restrict Work.Spaces.Iz) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
      have hG_meas : AEStronglyMeasurable (fun z => Real.sqrt (G z))
          (volume.restrict Work.Spaces.Iz) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
      have hF_sq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hFint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
      have hG_sq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
        hGint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
      have hF_lp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq
      have hG_lp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
        (memLp_two_iff_integrable_sq hG_meas).mpr hG_sq
      exact memLp_one_iff_integrable.mp (hF_lp.mul hG_lp)
  have hFeq : (∫ z in Work.Spaces.Iz, F z) = Work.Spaces.HkSq α 6 f := by
    simp only [hF, Work.Spaces.HkSq]
  have hGeq : (∫ z in Work.Spaces.Iz, G z) = Work.Spaces.HkSq α 6 g := by
    simp only [hG, Work.Spaces.HkSq]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * |X z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        cs_sqrt_le hFint hGint hFnn hGnn
    _ = Real.sqrt (Work.Spaces.HkSq α 6 f) * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
        rw [hFeq, hGeq]

/-! ## The energies of the slots -/

/-- The energy of a pure `D_z`-slot, `j ≤ 6`, priced with `q ≤ η`. -/
theorem energy_z6 (α : ℝ) (hα : 0 < α) {q : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.eta)
    {h : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 6 h) (j : ℕ) (hj : j ≤ 6) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 h := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 h z θ := fun z hz =>
    Work.FTS.TransportS.SlotT2.integral_Iθ_mono
      (fun θ hθ => canonW_mul_z_le6 α h hq0 hq hθ j hj)
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)
  have h0 : ∀ z ∈ Work.Spaces.Iz,
      0 ≤ ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.DzIter j h z θ) ^ 2 :=
    fun z _ => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))
  have hzeq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ) = Work.Spaces.HkSq α 6 h := rfl
  rw [← hzeq]
  exact Work.FTS.TransportS.SlotT2.integral_Iz_mono hslice h0 hmem.2

/-- The energy of a mixed slot, `1 ≤ i`, `i + j ≤ 6`, priced with `q ≤ γ`. -/
theorem energy_mixed6 (α : ℝ) (hα : 0 < α) {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α)
    {h : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 6 h) (j i : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 6) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 h := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 h z θ := fun z hz =>
    Work.FTS.TransportS.SlotT2.integral_Iθ_mono
      (fun θ hθ => canonW_mul_mixed_le6 α h hq0 hqγ hθ j i hi hij)
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _)) (hmem.1 z hz)
  have h0 : ∀ z ∈ Work.Spaces.Iz,
      0 ≤ ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Work.Spaces.mixed j i h z θ) ^ 2 :=
    fun z _ => MeasureTheory.setIntegral_nonneg hIθm
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))
  have hzeq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 h z θ) = Work.Spaces.HkSq α 6 h := rfl
  rw [← hzeq]
  exact Work.FTS.TransportS.SlotT2.integral_Iz_mono hslice h0 hmem.2

/-! ## The pointwise bound of order `≤ 4` with the `α^{-1/2}` loss -/

/-- **The pointwise bound at level six.**  For `h` of class `SmoothOpen` with honest
`HkMem α 6 h`, every `D_z^bD_θ^a h` with `a + b ≤ 4` is bounded on the open quadrant by
`C α^{-1/2} |h|_{ℋ⁶}`, with a universal `C`.

This is the square-root form of the proved level-six pointwise bound
`Work.FTS.StrongPersist.N6.PwAny6` (which gives the square with the factor `(γ-1)^{-1}` and
`γ - 1 = α/10`). -/
theorem supSix : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.HkMem α 6 h →
    ∀ b a : ℕ, a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a h z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 h := by
  obtain ⟨C, hC, hPw⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨Real.sqrt (C * 10), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α h hα hα1 hsm hmem b a hab z θ hz hθ hθ2
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγeq : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hA : 0 ≤ Work.Spaces.HkSq α 6 h := Work.Spaces.HkSq_nonneg α 6 h
  have hsq : (Work.Spaces.mixed b a h z θ) ^ 2
      ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 h :=
    hPw α h b a hα hα1 hsm hmem hab z hz θ ⟨hθ, hθ2⟩
  have hfac : C / (Work.Spaces.gam α - 1) = C * 10 / α := by
    rw [hγeq, div_div_eq_mul_div]
  have hinv : (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hα.le]
  have hsqrt : Real.sqrt (C / (Work.Spaces.gam α - 1))
      = Real.sqrt (C * 10) * α ^ (-(1 / 2 : ℝ)) := by
    rw [hfac, Real.sqrt_div (by positivity), div_eq_mul_inv, hinv]
  have hmain : Real.sqrt (C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 h)
      = Real.sqrt (C * 10) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 h := by
    rw [Real.sqrt_mul (div_nonneg (by positivity) hγ.le), hsqrt]
    rfl
  calc |Work.Spaces.mixed b a h z θ|
      = Real.sqrt ((Work.Spaces.mixed b a h z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 h) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C * 10) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 h := hmain

end Work.FTS.StrongPersist.N6Trans.T1SixAux
