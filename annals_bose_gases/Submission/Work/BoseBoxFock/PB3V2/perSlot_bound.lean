import Mathlib.CategoryTheory.Countable
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3V2.perSlotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.perSlot_bound` — the per-slot tail of the block-III frame

For a slot `j : Fin n`, a smooth state `Φ` and a momentum cutoff `Λ` that dominates the lattice
momenta outside the label cube `labSet N`, the difference of the *limit* slot form and the
truncated *frame* slot form is bounded by the `Λ⁻²`-decaying payers

    limSlotForm ℓ j Θ − frameSlotForm v μ N j Θ
      ≤ Λ⁻² · (6·D²·fibreMassFree ℓ j Φ + 2·fibreWave ℓ j Φ) ,

`ℓ = ellH v μ`, `Θ = boxRestrictC ℓ Φ` and `D` a Lipschitz bound of the window `χ_ℓ`.

## Route

* `PS.limSlotForm_eq_fibreMass` slices the limit form along the slot: it is the `χ²`-weighted box
  mass of the one-body slot fibres, integrated over the slice box.
* `PS.frameSlotForm_eq_sum` slices the frame form as the sum over the truncated labels of the
  squared fibre coefficients.
* Pointwise on the slice box, `fibreOneBody` bounds the tight-frame tail of the fibre by `Λ⁻²`
  times the second moment `(2π)⁻³∫_p ‖p‖²‖kinFT(χ·mf φ)(p)‖²` of the windowed mean-free fibre, and
  `energy_fibre_le` converts that second moment into `6D²` times the fibre box mass plus `2` times
  the fibre Dirichlet content.
* Integrating the pointwise inequality over the (compact, hence finite-measure) slice box and using
  that the tail of the whole-space fibre integral is nonnegative gives the statement.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory

namespace Work.BoseBoxFock

namespace PB3V2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The free labels of the truncation are the image of `Lab N` under `labVec N`. -/
theorem labVec_injective' (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

/-- **The per-fibre tail bound.**  For a fibre `x'` of the slice box, the `χ²`-weighted fibre box
mass of the smooth state minus the truncated frame sum of the fibre coefficients is at most `Λ⁻²`
times the second moment of the windowed mean-free fibre, which `energy_fibre_le` dominates by
`6D²·fibreBoxFree + 2·fibreDir`. -/
lemma perFibre_le {n : ℕ} {ℓ Λ D : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    (hΛ : 0 < Λ) (hΛk : ∀ k : Fin 3 → ℤ, k ∉ labSet N → Λ ≤ ‖kappaL ℓ k‖)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hD0 : 0 ≤ D)
    (hD : ∀ x w : E3, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x w| ≤ D * ‖w‖)
    (j : Fin n) {x' : {l : Fin n // l ≠ j} → E3}
    (hx' : x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ) :
    PS.fibreBox ℓ j (fun x => ((Φ x : ℝ) : ℂ)) x'
      - ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQInf ℓ (labVec N k) u)
          * (boxRestrictC ℓ Φ) (insertCoord j u x')‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PS.fibreBoxFree ℓ j (fun x => ((Φ x : ℝ) : ℂ)) x'
          + 2 * PS.fibreDir ℓ j (fun x => ((Φ x : ℝ) : ℂ)) x') := by
  classical
  set Ψ : Xn n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΨdef
  set Θ : Xn n → ℂ := boxRestrictC ℓ Φ with hΘdef
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [hΨdef]; exact Complex.ofRealCLM.contDiff.comp hΦ
  obtain ⟨CΘ, hCΘ⟩ := PS.bdd_boxRestrictC hℓ hΦ.continuous
  have hΘm : Measurable Θ := by
    rw [hΘdef]; exact PS.measurable_boxRestrictC ℓ hΦ.continuous.measurable
  have hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ := by
    rw [hΘdef]; exact PS.support_boxRestrictC ℓ Φ
  -- the slot-`j` section of the restricted state is `L²`
  have hsec_supp : Function.support (sect j x' Θ) ⊆ boxL ℓ := by
    intro u hu
    have h1 : Θ (insertCoord j u x') ≠ 0 := hu
    have h2 := hΘs h1
    have h3 := (Submission.BoseGases.mem_abox_iff n ℓ (insertCoord j u x')).mp h2 j
    rwa [insertCoord_self, ← corpusBox_boxL_eq_acube hℓ] at h3
  have hboxclosed : IsClosed (boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed
  have hsec_tsupp : tsupport (sect j x' Θ) ⊆ boxL ℓ :=
    (closure_mono hsec_supp).trans (by rw [hboxclosed.closure_eq])
  have hfmem : MemLp (sect j x' Θ) 2 (volume : Measure E3) :=
    HasCompactSupport.memLp_of_bound
      (IsCompact.of_isClosed_subset (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
        (isClosed_tsupport _) hsec_tsupp)
      (((hΘm.comp ((Work.BoseBoxFock.continuous_insertCoord j).comp
          (continuous_id.prodMk continuous_const)).measurable)).aestronglyMeasurable)
      CΘ (Filter.Eventually.of_forall fun u => hCΘ _)
  have hφcd : ContDiff ℝ 1 (sect j x' Ψ) := by
    have hins : ContDiff ℝ 1 (fun z : E3 => insertCoord j z x') := by
      have heq : (fun z : E3 => insertCoord j z x')
          = (fun z : E3 => Function.update (insertCoord j 0 x') j z) := by
        funext z i
        by_cases hi : i = j <;> simp [Work.BoseBoxFock.insertCoord, hi]
      rw [heq]
      exact contDiff_update (1 : WithTop ℕ∞) (insertCoord j 0 x') j
    exact (hΨcd.of_le (by simp)).comp hins
  have hagree : ∀ w ∈ boxL ℓ, sect j x' Θ w = sect j x' Ψ w := by
    rw [hΘdef]
    exact PS.sect_congr hℓ j hx'
  have hfib := fibreOneBody hℓ hΛ hΛk hfmem hφcd hagree
  -- the two rewritings
  have h1 : (∫ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ‖Work.BoseBoxFock.mf ℓ (sect j x' Θ) w‖ ^ 2)
      = PS.fibreBox ℓ j Ψ x' := by
    rw [PS.integral_fibreBox_eq hℓ j Θ x']
    rw [show PS.fibreBox ℓ j Θ x' = PS.fibreBox ℓ j Ψ x' from by
      rw [hΘdef, hΨdef]; exact PS.fibreBox_congr hℓ j hx']
  have h2 : (∑ n ∈ labSet N, ‖∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ n x)
        * sect j x' Θ x‖ ^ 2)
      = ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQInf ℓ (labVec N k) u)
          * Θ (insertCoord j u x')‖ ^ 2 := by
    have hinj : ∀ a ∈ (Finset.univ : Finset (Lab N)), ∀ b ∈ (Finset.univ : Finset (Lab N)),
        labVec N a = labVec N b → a = b := fun a _ b _ hab => labVec_injective' N hab
    rw [show labSet N = Finset.univ.image (labVec N) from rfl, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun k _ => rfl)
  have hener := energy_fibre_le hℓ j hΨcd hD0 hD x'
  calc PS.fibreBox ℓ j Ψ x' - ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQInf ℓ (labVec N k) u)
          * Θ (insertCoord j u x')‖ ^ 2
      = (∫ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2
            * ‖Work.BoseBoxFock.mf ℓ (sect j x' Θ) w‖ ^ 2)
          - ∑ n ∈ labSet N, ‖∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ n x)
              * sect j x' Θ x‖ ^ 2 := by rw [h1, h2]
    _ ≤ (Λ ^ 2)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 *
          ‖Submission.BoseGases.kinFT (fun w : E3 =>
            ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
              * Work.BoseBoxFock.mf ℓ (sect j x' Ψ) w) p‖ ^ 2) := hfib
    _ ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PS.fibreBoxFree ℓ j Ψ x' + 2 * PS.fibreDir ℓ j Ψ x') := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hener

/-- **The per-slot bound.**  For every slot `j`, the difference of the limit slot form and the
truncated frame slot form is bounded by `Λ⁻²` times the `6D²`-weighted fibre box mass plus twice
the fibre Dirichlet content. -/
theorem perSlot_bound {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (N : ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {D Λ : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x w : EuclideanSpace ℝ (Fin 3),
        |fderiv ℝ (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ)) x w| ≤ D * ‖w‖)
    (hΛ : 0 < Λ)
    (hΛk : ∀ k : Fin 3 → ℤ, k ∉ Work.BoseBoxFock.labSet N →
        Λ ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k‖)
    (j : Fin n) :
    Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      - Work.BoseBoxFock.frameSlotForm v μ N j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * Work.BoseBoxFock.PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j
            (fun x => ((Φ x : ℝ) : ℂ))
          + 2 * Work.BoseBoxFock.PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j
            (fun x => ((Φ x : ℝ) : ℂ))) := by
  classical
  set ℓ := Work.BoseBoxFock.ellH v μ with hℓdef
  set Ψ : Xn n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΨdef
  set Θ : Xn n → ℂ := boxRestrictC ℓ Φ with hΘdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBoxFock.ellH_pos v μ
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [hΨdef]; exact Complex.ofRealCLM.contDiff.comp hΦ
  obtain ⟨CΘ, hCΘ⟩ := PS.bdd_boxRestrictC hℓ hΦ.continuous
  have hΘm : Measurable Θ := by
    rw [hΘdef]; exact PS.measurable_boxRestrictC ℓ hΦ.continuous.measurable
  have hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ := by
    rw [hΘdef]; exact PS.support_boxRestrictC ℓ Φ
  have hSmeas : MeasurableSet (boxPiSet ({l : Fin n // l ≠ j}) ℓ) :=
    (isCompact_boxPiSet hℓ).measurableSet
  have hSfin : volume (boxPiSet ({l : Fin n // l ≠ j}) ℓ) ≠ ⊤ :=
    (isCompact_boxPiSet hℓ).measure_lt_top.ne
  -- the four pieces: the limit form, the frame form, the pointwise bound, the integral
  have hlim : Work.BoseBoxFock.limSlotForm ℓ j Θ
      = ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, PS.fibreBox ℓ j Ψ x' := by
    have hcx : PS.boxRestrictCX ℓ Ψ = Θ := by
      rw [hΨdef, hΘdef]; exact PS.boxRestrictCX_ofReal ℓ Φ
    rw [← hcx, PS.limSlotForm_eq_fibreMass j hℓ hΨcd, PS.fibreMass_eq_integral_fibreBox]
  have hframe : Work.BoseBoxFock.frameSlotForm v μ N j Θ
      = ∑ k : Lab N, ∫ x' : {l : Fin n // l ≠ j} → E3, ‖∫ u : E3,
          (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2 :=
    PS.frameSlotForm_eq_sum (v := v) (μ := μ) N j hΦ
  -- integrability of the fibre coefficients
  have hbint : ∀ k : Lab N, Integrable (fun x' : {l : Fin n // l ≠ j} → E3 => ‖∫ u : E3,
      (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2) volume := by
    intro k
    have h0 := PS.integrable_fibre_conj_mul hℓ j (Work.BoseBoxFock.pinQ_measurable v μ N k)
      ((Work.BoseBoxFock.pinQ_bdd v μ N k).imp fun C h => h.2) hΘm ⟨CΘ, hCΘ⟩ hΘs
    refine h0.norm.congr (Filter.Eventually.of_forall fun x' => ?_)
    dsimp only
    rw [norm_mul, Complex.norm_conj, sq]
  -- the pointwise bound on the slice box
  have hpt : ∀ x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ,
      PS.fibreBox ℓ j Ψ x' - ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Θ (insertCoord j u x')‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PS.fibreBoxFree ℓ j Ψ x' + 2 * PS.fibreDir ℓ j Ψ x') := by
    intro x' hx'
    have hres := perFibre_le (ℓ := ℓ) (Λ := Λ) (D := D) (N := N) (Φ := Φ) hℓ hΛ hΛk hΦ hD0 hD j hx'
    have hsum : (∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQInf ℓ (labVec N k) u)
          * (boxRestrictC ℓ Φ) (insertCoord j u x')‖ ^ 2)
        = ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * Θ (insertCoord j u x')‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hpk : pinQInf ℓ (labVec N k) = pinQ v μ N k := by
        rw [pinQ_eq_pinQInf]
      rw [hpk]
    rw [hsum] at hres
    exact hres
  -- integrability of the two sides on the slice box
  have hAint : IntegrableOn (fun x' => PS.fibreBox ℓ j Ψ x')
      (boxPiSet ({l : Fin n // l ≠ j}) ℓ) volume :=
    ((PS.continuous_fibreBox j hΨcd.continuous).continuousOn).integrableOn_compact
      (isCompact_boxPiSet hℓ)
  have hHcont : Continuous (fun x' : {l : Fin n // l ≠ j} → E3 =>
      6 * D ^ 2 * PS.fibreBoxFree ℓ j Ψ x' + 2 * PS.fibreDir ℓ j Ψ x') :=
    (continuous_const.mul (PS.continuous_fibreBoxFree j hΨcd.continuous)).add
      (continuous_const.mul (PS.continuous_fibreDir j hΨcd))
  have hHint : IntegrableOn (fun x' => 6 * D ^ 2 * PS.fibreBoxFree ℓ j Ψ x'
      + 2 * PS.fibreDir ℓ j Ψ x') (boxPiSet ({l : Fin n // l ≠ j}) ℓ) volume :=
    hHcont.continuousOn.integrableOn_compact (isCompact_boxPiSet hℓ)
  have hsumInt : IntegrableOn (fun x' => ∑ k : Lab N, ‖∫ u : E3,
      (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2)
      (boxPiSet ({l : Fin n // l ≠ j}) ℓ) volume :=
    integrable_finsetSum _ (fun k _ => (hbint k).integrableOn)
  have hdifInt : IntegrableOn (fun x' => PS.fibreBox ℓ j Ψ x' - ∑ k : Lab N,
      ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2)
      (boxPiSet ({l : Fin n // l ≠ j}) ℓ) volume :=
    hAint.sub hsumInt
  -- integrate the pointwise bound
  have hmono : (∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
        (PS.fibreBox ℓ j Ψ x' - ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Θ (insertCoord j u x')‖ ^ 2))
      ≤ ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
        ((Λ ^ 2)⁻¹ * (6 * D ^ 2 * PS.fibreBoxFree ℓ j Ψ x' + 2 * PS.fibreDir ℓ j Ψ x')) :=
    setIntegral_mono_on hdifInt (hHint.const_mul _) hSmeas hpt
  -- split the integral of the difference
  have hsplit : (∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
        (PS.fibreBox ℓ j Ψ x' - ∑ k : Lab N, ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
          * Θ (insertCoord j u x')‖ ^ 2))
      = (∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, PS.fibreBox ℓ j Ψ x')
        - ∑ k : Lab N, ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
            ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2 := by
    rw [integral_sub hAint hsumInt, integral_finsetSum _ (fun k _ => (hbint k).integrableOn)]
  -- the integral of the majorant
  have hHval : (∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
        ((Λ ^ 2)⁻¹ * (6 * D ^ 2 * PS.fibreBoxFree ℓ j Ψ x' + 2 * PS.fibreDir ℓ j Ψ x')))
      = (Λ ^ 2)⁻¹ * (6 * D ^ 2 * fibreMassFree ℓ j Ψ + 2 * fibreWave ℓ j Ψ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    · rw [show (∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, PS.fibreBoxFree ℓ j Ψ x')
          = fibreMassFree ℓ j Ψ from (PS.fibreMassFree_eq_integral j Ψ).symm,
        show (∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, PS.fibreDir ℓ j Ψ x')
          = fibreWave ℓ j Ψ from (PS.fibreWave_eq_integral j Ψ).symm]
    · exact ((continuous_const.mul (PS.continuous_fibreBoxFree j hΨcd.continuous)).continuousOn).integrableOn_compact
        (isCompact_boxPiSet hℓ)
    · exact ((continuous_const.mul (PS.continuous_fibreDir j hΨcd)).continuousOn).integrableOn_compact
        (isCompact_boxPiSet hℓ)
  -- the tail of the whole-space fibre integral is nonnegative
  have htail : (∑ k : Lab N, ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
        ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2)
      ≤ ∑ k : Lab N, ∫ x' : {l : Fin n // l ≠ j} → E3,
        ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => setIntegral_le_integral (hbint k)
      (Filter.Eventually.of_forall fun x' => by positivity))
  -- assembly
  have hkey : Work.BoseBoxFock.limSlotForm ℓ j Θ
      - ∑ k : Lab N, ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ,
          ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (insertCoord j u x')‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * fibreMassFree ℓ j Ψ + 2 * fibreWave ℓ j Ψ) := by
    rw [hlim]
    rw [hsplit] at hmono
    exact hmono.trans_eq hHval
  linarith [hkey, htail, hframe]

end PB3V2

end Work.BoseBoxFock
