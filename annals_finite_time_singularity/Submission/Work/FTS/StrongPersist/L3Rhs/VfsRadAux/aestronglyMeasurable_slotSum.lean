import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gLocal
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.L12Add
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.ClassC.HonestCut.HkMem_zero_psiSeries_of_capstone =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

/-!
# `HkMem α 0 (psiSeries α F)` from the capstone's finiteness data

The `H^k`-honesty of the mode series at level `0` is the conjunction of

* `∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α 0 Ψ z θ) Iθ` (`Iz = [0,∞)`), and
* `IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α 0 Ψ z θ) Iz`.

The capstone supplies the *iterated `lintegral`* bound (`hfin`, with the two measurability
inputs `hslmeas`, `hmeas`), which by `HkMemAe_of_lintegral` yields the *almost everywhere*
version of both assertions, with the outer integral taken over `(0,∞)` only (the `lintegral`
in `hfin` is over `Set.Ioi 0`).  The two gaps are closed as follows.

* The point `z = 0` (the difference between `Iz = [0,∞)` and `(0,∞)`) is trivial: the radial
  weight vanishes there, `w 0 = 0`, which kills `HkIntegrand` identically
  (`HkIntegrand_zero_at_zero`).  Likewise `{0}` is null, so integrability over `(0,∞)`
  upgrades to integrability over `[0,∞)` (`MeasureTheory.restrict_Ioi_eq_restrict_Ici`).
* The `θ`-slice at a fixed `z > 0` is integrable *everywhere*, not merely a.e., by the
  self-contained `integrableOn_slice_psiSeries_zero`, whose only input is the weighted
  summability `hcoef` of the radial coefficients (available for every `z > 0`).
-/

/-- At `z = 0` the radial weight `w` vanishes, so the whole `H^0`-integrand vanishes. -/
lemma HkIntegrand_zero_at_zero (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 Ψ 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, hw, zero_div, mul_zero]
  simp

theorem HkMem_zero_psiSeries_of_capstone {α : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hslmeas : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
        (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hfin : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ)) ≤ ENNReal.ofReal C)
    (hmeas : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0
          (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) :
    Work.Spaces.HkMem α 0 (Work.FTS.PhiStar.Series.psiSeries α F) := by
  obtain ⟨-, hout⟩ := HkMemAe_of_lintegral (α := α)
    (Ψ := Work.FTS.PhiStar.Series.psiSeries α F) hC hslmeas hfin hmeas
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- `z = 0`: the radial weight vanishes, so the slice integrand is identically zero.
      rw [← hz0]
      rw [show (fun θ => Work.Spaces.HkIntegrand α 0
              (Work.FTS.PhiStar.Series.psiSeries α F) 0 θ) = fun _ => (0 : ℝ) from
            funext fun θ => HkIntegrand_zero_at_zero α _ θ]
      exact integrableOn_zero
    · -- `z > 0`: the slice is integrable by the weighted summability of the coefficients.
      exact integrableOn_slice_psiSeries_zero z hzpos (hcoef z hzpos)
  · -- `{0}` is null, so the outer integrability over `(0,∞)` upgrades to `[0,∞)`.
    rw [Work.Spaces.Iz]
    change Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.FTS.PhiStar.Series.psiSeries α F) z θ)
      (volume.restrict (Set.Ici (0 : ℝ)))
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici (μ := volume) (a := (0 : ℝ))]
    exact hout

end Work.FTS.ClassC.HonestCut
end
-- ===== merged: Submission.Work.FTS.ClassC.bessel_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm

/-! ## Elementary facts -/

/-- `w` is continuous on `(0,∞)`. -/
theorem continuousOn_w : ContinuousOn w (Set.Ioi (0 : ℝ)) := by
  have h : w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact (continuousOn_const.add continuousOn_id).pow 2 |>.div (continuousOn_id.pow 2)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- The angular interval is measurable (needed as a *named* lemma so that `rw` can match it). -/
theorem measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

/-- `z ↦ w z² · (eNorm m · cmode m F z²)` is a.e. (strongly) measurable on `(0,∞)`. -/
theorem aemeasurable_modeTerm {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (m : ℕ) :
    AEMeasurable (fun z : ℝ => (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcm : AEMeasurable (fun z : ℝ => cmode m F z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).aemeasurable
  have hw : AEMeasurable (fun z : ℝ => (w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_w.aemeasurable measurableSet_Ioi).pow_const 2
  exact hw.mul ((hcm.pow_const 2).const_mul (eNorm m))

/-- The two Dirichlet endpoints of the angular interval are the zeros of `σ`. -/
theorem sEta_zero_at {θ : ℝ} (hθ : θ = 0 ∨ θ = Real.pi / 2) : sEta θ = 0 := by
  have hη : -(Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  rcases hθ with h | h
  · rw [h, Work.FTS.EllipticEst.sEta, mul_zero, Real.sin_zero]
    exact Real.zero_rpow hη
  · rw [h, Work.FTS.EllipticEst.sEta]
    have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h2, Real.sin_pi]
    exact Real.zero_rpow hη

/-! ## The pointwise comparison `cos θ ≤ sin(2θ)^{-η}` -/

/-- `cos θ ≤ σ θ` for `θ ∈ Iθ`, `θ ≠ 0`.  (At `θ = 0` the inequality fails: `cos 0 = 1` while
Lean's `0 ^ (-η) = 0`; the single point `{0}` is null, which is all the applications need.) -/
theorem cos_le_sEta_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) (h0 : θ ≠ 0) : Real.cos θ ≤ sEta θ := by
  rcases eq_or_lt_of_le hθ.2 with h | h
  · subst h
    rw [Real.cos_pi_div_two, sEta_zero_at (Or.inr rfl)]
  · have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), h⟩
    have h1 : 1 ≤ sEta θ := Work.FTS.EllipticEst.Honest.one_le_sEta hθ'
    have h2 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    linarith

/-- `cos θ ≤ σ θ` almost everywhere on `Iθ`. -/
theorem ae_cos_le_sEta :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), Real.cos θ ≤ sEta θ := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
  intro θ hθ
  simp only [Set.mem_setOf_eq] at hθ ⊢
  by_contra hne
  exact hθ (fun hmem => cos_le_sEta_of_mem_Iθ hmem hne)

/-! ## Bessel's inequality integrated in `z` -/

/-- **Bessel's inequality for the mode coefficients, integrated in `z` against `w²`.**

  `∑_{m ≤ N} ∫⁻_z w(z)² · eNorm m · (cmode m F z)²  ≤  ∫⁻_z ofReal (w(z)² · ∫_θ (F z θ)² cos θ)`.

The hypothesis `hint` is the slice integrability of `(F z ·)² cos` (`z > 0`); it is what makes
the `θ`-`lintegral` on the right equal to `ofReal` of the `θ`-integral. -/
theorem bessel_z (F : ℝ → ℝ → ℝ) (N : ℕ) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ) :
    (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * Real.cos θ) := by
  -- the slicewise Bessel bound, multiplied by `(w z)²` and pushed inside the θ-lintegral
  have hpt : ∀ z : ℝ, (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      ≤ ∫⁻ θ in Iθ, ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ)) := by
    intro z
    have hb : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          eNorm m * (cmode m F z) ^ 2)
        ≤ ∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ) :=
      Work.EllipticEst.ModalSolution.cmode_bessel F z N
    have hsplit : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          eNorm m * (cmode m F z) ^ 2)
        = ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal (eNorm m * (cmode m F z) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro m _
      exact mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)
    rw [hsplit] at hb
    have hw : 0 ≤ (w z) ^ 2 := by positivity
    have hmul := mul_le_mul_right hb (ENNReal.ofReal ((w z) ^ 2))
    have hleft : ENNReal.ofReal ((w z) ^ 2) * (∑ m ∈ Finset.range (N + 1),
          ENNReal.ofReal (eNorm m * (cmode m F z) ^ 2))
        = ∑ m ∈ Finset.range (N + 1),
            ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by rw [← ENNReal.ofReal_mul hw])
    have hright : ENNReal.ofReal ((w z) ^ 2) *
          (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ))
        = ∫⁻ θ in Iθ, ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ)) := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((w z) ^ 2))
        (fun θ => ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ)) ENNReal.ofReal_ne_top]
      exact MeasureTheory.lintegral_congr (fun θ => (ENNReal.ofReal_mul hw).symm)
    rw [hleft, hright] at hmul
    exact hmul
  -- integrate the pointwise-in-`z` inequality
  have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ), (∫⁻ θ in Iθ,
          ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ))) :=
    MeasureTheory.lintegral_mono hpt
  -- the summands are a.e. measurable, so the sum comes out of the `z`-integral
  have haem : ∀ m : ℕ, AEMeasurable
      (fun z : ℝ => ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun m => (aemeasurable_modeTerm hsm m).ennreal_ofReal
  have hsumsplit : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))))
      = ∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)) := by
    refine Finset.induction_on (Finset.range (N + 1)) ?_ ?_
    · simp
    · intro a s ha ih
      have hL : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ insert a s,
            ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))))
          = ∫⁻ z in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((w z) ^ 2 * (eNorm a * (cmode a F z) ^ 2))
              + ∑ m ∈ s, ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))) :=
        MeasureTheory.lintegral_congr (fun z => by
          show (∑ m ∈ insert a s, ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
            = ENNReal.ofReal ((w z) ^ 2 * (eNorm a * (cmode a F z) ^ 2))
              + ∑ m ∈ s, ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
          rw [Finset.sum_insert ha])
      rw [hL, MeasureTheory.lintegral_add_left' (haem a), ih, Finset.sum_insert ha]
  -- the RHS: `∫⁻_θ ofReal (…)` is `ofReal` of the `θ`-integral
  have hconv : (∫⁻ z in Set.Ioi (0 : ℝ), (∫⁻ θ in Iθ,
        ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ))))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * Real.cos θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hInt : MeasureTheory.Integrable (fun θ => (w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ))
        (MeasureTheory.volume.restrict Iθ) :=
      (hint z hz).const_mul ((w z) ^ 2)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => (w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ)) := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Iθ).mpr ?_
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    exact MeasureTheory.integral_const_mul ((w z) ^ 2) (fun θ => (F z θ) ^ 2 * Real.cos θ)
  rw [hsumsplit, hconv] at h1
  exact h1

/-! ## The corollary: the Bessel sum is dominated by the source's `ℋ⁰`-norm -/

/-- **Bessel's inequality for the mode coefficients against `HkSq α 0`.**

  `∑_{m ≤ N} eNorm m · ∫_z (cmode m F z)² w(z)²  ≤  HkSq α 0 F`.

This is the source-side input of the level-`0` honest-modal estimate. -/
theorem sum_eNorm_cmode_sq_le_HkSq (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ) :
    (∑ m ∈ Finset.range (N + 1), eNorm m *
        ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2) ≤ Work.Spaces.HkSq α 0 F := by
  -- the outer integrand of `HkSq` is integrable
  have hIntHk : MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (hmem.2.mono_set (fun z hz => le_of_lt hz)).congr_fun ?_ measurableSet_Ioi
    intro z _
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α (fun z θ => F z θ) z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq (fun z θ => F z θ) z θ
        (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ)]
    rfl
  have hθeq : ∀ z : ℝ, (w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ
      = ∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ := by
    intro z
    have h1 : (∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ)
        = ∫ θ in Iθ, (w z) ^ 2 * ((F z θ) ^ 2 * sEta θ) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [h1, MeasureTheory.integral_const_mul]
  have hHkSqLim : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθ,
        (F z θ) ^ 2 * (w z) ^ 2 * sEta θ) = Work.Spaces.HkSq α 0 F := by
    rw [Work.FTS.ClassC.HkSq_zero_eq_w α F]
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := MeasureTheory.volume)
      (x := (0 : ℝ))).symm
  have hB : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 F) := by
    have hpoint : (fun z : ℝ => ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ,
          (F z θ) ^ 2 * sEta θ))
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
          (fun z => ENNReal.ofReal (∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ)) :=
      Filter.Eventually.of_forall (fun z => by
        show ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ) = _
        rw [hθeq z])
    rw [MeasureTheory.lintegral_congr_ae hpoint]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntHk
      (Filter.Eventually.of_forall (fun z => by
        refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
        have hs := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs))]
    rw [hHkSqLim]
  -- Bessel, then the `cos ≤ σ` comparison
  have hbess := bessel_z F N hsm hint
  have hcmp : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * Real.cos θ))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (w z) ^ 2)
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hintσ z hz) ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Iθ).mpr ?_
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    · filter_upwards [ae_cos_le_sEta] with θ hθ
      exact mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
  have hmain : (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 F) :=
    le_trans (le_trans hbess hcmp) (le_of_eq hB)
  -- each summand is finite, and is `ofReal` of the corresponding real integral
  have hHkSq_nonneg : 0 ≤ Work.Spaces.HkSq α 0 F := by
    rw [Work.FTS.ClassC.HkSq_zero_eq_w α F]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hs := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs
  have hterm : ∀ m ∈ Finset.range (N + 1), eNorm m *
        ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2
      = (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))).toReal := by
    intro m _
    have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun z : ℝ => (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)) :=
      Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _)
        (mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)))
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aemeasurable_modeTerm hsm m).aestronglyMeasurable
    have hconv := MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg haesm
    have hw2 : (∫ z in Set.Ioi (0 : ℝ), (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
        = eNorm m * ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2 := by
      have h1 : (∫ z in Set.Ioi (0 : ℝ), (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
          = ∫ z in Set.Ioi (0 : ℝ), eNorm m * ((cmode m F z) ^ 2 * (w z) ^ 2) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
      rw [h1, MeasureTheory.integral_const_mul]
    rw [hw2] at hconv
    exact hconv
  have hfin : ∀ m ∈ Finset.range (N + 1),
      (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))) ≠ ⊤ := by
    intro m hm
    have hsingle : (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
        ≤ ∑ i ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((w z) ^ 2 * (eNorm i * (cmode i F z) ^ 2)) :=
      Finset.single_le_sum (f := fun i => ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm i * (cmode i F z) ^ 2)))
        (fun i _ => zero_le) hm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans hsingle hmain)
  have hsum_eq : (∑ m ∈ Finset.range (N + 1), eNorm m *
        ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2)
      = (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))).toReal := by
    rw [ENNReal.toReal_sum (fun m hm => hfin m hm)]
    exact Finset.sum_congr rfl (fun m hm => hterm m hm)
  rw [hsum_eq]
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain)
    (le_of_eq (ENNReal.toReal_ofReal hHkSq_nonneg))

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Angular factors -/

/-- `θ ↦ sin(2θ)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_two :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ)) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0
  exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn

/-- `θ ↦ sin θ ^ 2` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_sq :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0
  exact (((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn)

/-! ## The two explicit `F_*`-moments -/

/-- `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_L12_Fstar_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) := by
  have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := fun n =>
    contDiffOn_const.div (contDiffOn_const.add contDiffOn_id)
      (fun z hz => ne_of_gt (by
        have h : (0 : ℝ) < z := hz
        linarith))
  have hmain := Work.FTS.NonlinRows.smoothOpen_radial (r := fun z : ℝ => 2 * α / (1 + z)) hr
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  exact Work.Construction.L12_Fstar_eq hα hα1
    (le_of_lt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- `z ↦ FK(F_*)(z) = α·2z/(1+z)²` is `C^∞` on the open quadrant. -/
theorem smoothOpen_FK_Fstar_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) := by
  have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) (Set.Ioi 0) :=
    fun n =>
      contDiffOn_const.mul
        ((contDiffOn_const.mul contDiffOn_id).div
          ((contDiffOn_const.add contDiffOn_id).pow 2)
          (fun z hz => pow_ne_zero 2 (ne_of_gt (by
            have h : (0 : ℝ) < z := hz
            linarith))))
  have hmain := Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) hr
  refine hmain.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1

/-! ## Additivity of the angular moment `FK` in the profile -/

/-- **The angular moment is additive** as soon as the two θ-slices are integrable on `Iθ`: this
is `L12dens_add_of_integrableOn` transported through the definitional identity
`FK f z = z · L12dens K f z`. -/
theorem FK_add_of_slices {a b : ℝ → ℝ → ℝ} {z : ℝ} (hz : z ≠ 0)
    (ha : IntegrableOn (fun θ => Work.Spaces.K θ * a z θ / z) Work.Spaces.Iθ)
    (hb : IntegrableOn (fun θ => Work.Spaces.K θ * b z θ / z) Work.Spaces.Iθ) :
    Work.Construction.FK (fun z θ => a z θ + b z θ) z
      = Work.Construction.FK a z + Work.Construction.FK b z := by
  have hd := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K ha hb
  have hkey : ∀ f : ℝ → ℝ → ℝ, Work.Construction.FK f z
      = z * Work.FM.L12dens Work.Spaces.K f z := by
    intro f
    simp only [Work.Construction.FK, Work.FM.L12dens, Work.Spaces.Iθ]
    rw [show (fun θ => Work.Spaces.K θ * f z θ / z)
        = fun θ => (1 / z) * (f z θ * Work.Spaces.K θ) from by funext θ; ring]
    rw [MeasureTheory.integral_const_mul]
    field_simp
  rw [hkey (fun z θ => a z θ + b z θ), hd, mul_add, ← hkey a, ← hkey b]

/-! ## The repaired statement -/


end Work.FTS.GalFields.RHS
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Rl1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem Rl1 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨K, hK, h⟩ := Work.FTS.NonlinRows.rl1 IP hN hE
  exact ⟨K, hK, fun hα hα1 hαα₂ hg hs hell =>
    h (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hs hell)⟩

end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4SepDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false

/-- The angular block at order four: the `η`-weighted square of `C` plus the `γ`-weighted
squares of its `dthU`-jets of orders `1..4`. -/
def AngBlk4 (α : ℝ) (C : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 5,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)

/-- The radial slot sum at order four: the `w²`-weighted squares of the `D_z`-slots of the
radial profile `B`, up to order `4`. -/
def SlotSum4 (B : ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∑ q ∈ Finset.range 5,
    (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2

@[simp] theorem AngBlk4_apply (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) : AngBlk4 α C θ =
    (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ∑ i ∈ Finset.range 5,
          (if 1 ≤ i then (Work.Spaces.dthU^[i] C θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := rfl

@[simp] theorem SlotSum4_apply (B : ℝ → ℝ) (z : ℝ) : SlotSum4 B z =
    ∑ q ∈ Finset.range 5,
      (Work.Spaces.DzIter q (fun z' _ => B z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl

/-- `AngBlk4` is `angMaj` (order three) plus the order-four jet term. -/
theorem AngBlk4_eq_angMaj_add (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) :
    AngBlk4 α C θ = Work.FTS.StrongPersist.L3Rhs.angMaj α C θ
      + (Work.Spaces.dthU^[4] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  simp only [AngBlk4, Work.FTS.StrongPersist.L3Rhs.angMaj]
  rw [Finset.sum_range_succ, if_pos (show (1 : ℕ) ≤ 4 by norm_num)]
  ring

/-- The `η`-sunmand of `AngBlk4` is nonnegative on `Iθ`. -/
theorem AngBlk4_nonneg {α : ℝ} {C : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ AngBlk4 α C θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  simp only [AngBlk4]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
  refine Finset.sum_nonneg (fun i _ => ?_)
  by_cases h1 : 1 ≤ i
  · rw [if_pos h1]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  · rw [if_neg h1]

/-- `SlotSum4` is nonnegative. -/
theorem SlotSum4_nonneg (B : ℝ → ℝ) (z : ℝ) : 0 ≤ SlotSum4 B z :=
  Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.DiagAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

/-! ## Auxiliary material for the `L²`-route derivative of the weighted square -/

/-! ### small generic helpers -/






/-- The AM–GM pointwise inequality `|a * b| ≤ (a * a + b * b) / 2`. -/
theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a * a + b * b) / 2 := by
  have h2 : 2 * |a| * |b| ≤ a * a + b * b := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  rw [abs_mul]
  linarith

/-! ## The `L²`-data bundle and the derived objects -/





/-- **The `L²`-data of a curve and of its derivative family.**  All the hypotheses of the
`L²`-route derivative of `s ↦ ∫ p, u s p ^ 2 ρ p`, repackaged together with the elementary
consequences used by the proof (the `*`-form of the diagonal integrabilities, the a.e.
measurability of the time slices, and a window `(τ - δ, τ + δ) ⊆ (0, T)` with `δ ≤ τ / 2`). -/
structure DiagData (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Work.FTS.Galerkin.Fn) (τ T : ℝ) where
  hτ : τ ∈ Set.Ioo 0 T
  hτ1 : 0 < τ
  hτ2 : τ < T
  K : ℝ
  K_nonneg : 0 ≤ K
  ρmeas : AEMeasurable (Function.uncurry ρ) diaM
  wmeas : AEMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2) diaM
  ρnn : ∀ᵐ p ∂diaM, 0 ≤ ρ p.1 p.2
  diag : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2) diaM
  diagd : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => udot s p.1 p.2 * udot s p.1 p.2 * ρ p.1 p.2) diaM
  diagd_sq : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM
  bdd : ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM ≤ K
  bdd_sq : ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K
  aesm : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
    (MeasureTheory.volume.prod diaM)
  aesmd : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
    (MeasureTheory.volume.prod diaM)
  deriv : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s
  cont : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T)
  contU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
    (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0)
  umeas : ∀ σ ∈ Set.Ioo (0 : ℝ) T, AEMeasurable (fun p : ℝ × ℝ => u σ p.1 p.2) diaM
  dmeas : ∀ σ ∈ Set.Ioo (0 : ℝ) T, AEMeasurable (fun p : ℝ × ℝ => udot σ p.1 p.2) diaM
  δ : ℝ
  δ_pos : 0 < δ
  δ_half : δ ≤ τ / 2
  δ_T : τ + δ < T

theorem DiagData.hτIcc {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) : τ ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_of_lt D.hτ1, le_of_lt D.hτ2⟩







end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2O.C0_sq_le_HkSq0_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular factor `3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}` of the Cauchy–Schwarz weight. -/
private noncomputable def cwA (p : ℝ × ℝ) : ℝ :=
  3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
    * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)

/-- The `D_θ f`-factor of the Cauchy–Schwarz weight.  Its square is exactly
`HkIntegrand α 0 (D_θ f)`. -/
private noncomputable def cwB (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Spaces.Dth f p.1 p.2
    * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))

/-- The product measure `(volume|Iz) ⊗ (volume|Iθ)`. -/
private noncomputable def cwμ : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

/-! ## Elementary facts about the two weights -/

/-- `Iθ` agrees a.e. with its interior, so angular identities need only hold on
`(0, π/2)`. -/
private theorem Iθ_restrict_congr : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `cwA` is measurable (it is a product of measurable functions; the `sin(2θ)^{η/2}`
factor is measurable because `x ↦ x^{η/2}` is continuous, `η/2 > 0`). -/
private theorem cwA_measurable : Measurable cwA := by
  have hK : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
    apply Continuous.measurable
    show Continuous fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2
    fun_prop
  have hrat : Measurable (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 3) :=
    measurable_fst.div ((measurable_const.add measurable_fst).pow_const 3)
  have hrpow : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable.comp
      ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)).measurable)
  exact ((hK.const_mul 3).mul hrat).mul hrpow

/-- `cwB f` is a.e. strongly measurable on the product measure as soon as `f` is `C^∞` on
the **open** quadrant: `D_θ f` is continuous there, and the complement of the open quadrant
inside `Iz ×ˢ Iθ` is null. -/
private theorem cwB_aesm {f : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (cwB f) cwμ := by
  have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hO.Dth).continuousOn
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2) cwμ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hDth
  have h2 : Measurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
    have hw : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) := by
      show Measurable fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2
      exact ((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)
    have hrpow : Measurable (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
      (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable.comp
        ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)).measurable)
    exact hw.div hrpow
  exact h1.mul h2.aestronglyMeasurable

/-- The pointwise identity underlying the Cauchy–Schwarz decomposition (for `z > 0` and
`θ` in the interior of `Iθ`). -/
private theorem cwA_mul_cwB {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z))
      = cwA (z, θ) * cwB f (z, θ) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs _)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  simp only [cwA, cwB, Work.Spaces.w]
  field_simp

/-! ## `B²` integrates to `HkSq α 0 (D_θ f)` -/

/-- At `k = 0` the `ℋ⁰`-integrand of `D_θ f` is *definitionally* the square of
`D_θ f · w/ sin(2θ)^{η/2}`, and the iterated integral of that square is `HkSq α 0 (D_θ f)`.
The only place the smoothness class enters is the a.e. strong measurability. -/
private theorem B_sq_prod_eq_HkSq_O (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.Dth f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      ∫ p, (Work.Spaces.Dth f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
  have hpt : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth f) z θ
      = (Work.Spaces.Dth f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro z θ
    simp only [Work.Spaces.HkIntegrand]
    simp
  have hAE : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.Dth f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hb : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => cwB f p * cwB f p) cwμ :=
      (cwB_aesm hO).mul (cwB_aesm hO)
    simpa only [cwB, cwμ, pow_two] using hb
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => (Work.Spaces.Dth f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun z θ => sq_nonneg _) hAE
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      (hmem.1 z hz).congr (Filter.Eventually.of_forall fun θ => hpt z θ))
    (by
      have heq : (fun a : ℝ => ∫ b, (Work.Spaces.Dth f a b
              * (Work.Spaces.w a / (Real.sin (2 * b)) ^ (Work.Spaces.eta / 2))) ^ 2
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = fun a : ℝ => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth f) a θ := by
        funext a
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => (hpt a b).symm)
      rw [heq]
      exact hmem.2)
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [Work.Spaces.HkSq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  exact (hpt a b).symm

/-! ## The target -/

/-- **The `ℋ⁰`-bound for `C0` on the open quadrant**:
`(C0 f)² ≤ 16·|D_θ f|²_{ℋ⁰}` for `f` smooth on `(0,∞) × (0,π/2)` whose angular derivative
lies in `ℋ⁰`. -/
theorem C0_sq_le_HkSq0_O {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f)) :
    (Work.Coercivity.C0 f) ^ 2 ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
  have hA2 : Integrable (fun p : ℝ × ℝ => cwA p ^ 2) cwμ := by
    simpa only [cwA, cwμ] using
      Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le.1
  have hA2le : ∫ p, cwA p ^ 2 ∂cwμ ≤ 16 := by
    simpa only [cwA, cwμ] using
      Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le.2
  have hB2 : Integrable (fun p : ℝ × ℝ => cwB f p ^ 2) cwμ := by
    simpa only [cwB, cwμ] using (B_sq_prod_eq_HkSq_O α hO hmem).1
  have hB2val : ∫ p, cwB f p ^ 2 ∂cwμ = Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
    simpa only [cwB, cwμ] using (B_sq_prod_eq_HkSq_O α hO hmem).2
  have hABint : Integrable (fun p : ℝ × ℝ => cwA p * cwB f p) cwμ := by
    refine MeasureTheory.Integrable.mono' ((hA2.add hB2).const_mul (1 / 2))
      (cwA_measurable.aestronglyMeasurable.mul (cwB_aesm hO)) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    show |cwA p| * |cwB f p| ≤ 1 / 2 * (cwA p ^ 2 + cwB f p ^ 2)
    nlinarith [two_mul_le_add_sq (|cwA p|) (|cwB f p|), sq_abs (cwA p), sq_abs (cwB f p)]
  have hC0 : Work.Coercivity.C0 f = ∫ p, cwA p * cwB f p ∂cwμ := by
    rw [Work.FTS.CoercivityFix.Transfer.E2norm.C0_eq_density f]
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, cwA (z, θ) * cwB f (z, θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
      · subst h0
        simp [cwA, cwB]
      · refine MeasureTheory.integral_congr_ae ?_
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_restrict_congr]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => cwA_mul_cwB hpos hθ)
    rw [h1, cwμ]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => cwA p * cwB f p) hABint).symm
  calc (Work.Coercivity.C0 f) ^ 2
      = (∫ p, cwA p * cwB f p ∂cwμ) ^ 2 := by rw [hC0]
    _ ≤ (∫ p, cwA p ^ 2 ∂cwμ) * (∫ p, cwB f p ^ 2 ∂cwμ) :=
        Work.Coercivity.sq_integral_mul_le cwμ cwA (cwB f)
          cwA_measurable.aestronglyMeasurable (cwB_aesm hO) hA2 hB2
    _ = (∫ p, cwA p ^ 2 ∂cwμ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by rw [hB2val]
    _ ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) :=
        mul_le_mul_of_nonneg_right hA2le (Work.Spaces.HkSq_nonneg α 0 _)

end Work.FTS.StrongEps.EpsE4Thr.E2O
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.AngFac5.ang_fac5_integrable_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.AngFac5

/-- Same statement as `Work.FTS.GalFields.Norm.ang_fac_integrable_bound` but with the
coefficient `5` in place of `4` in front of the singular angular factor
`(100000·α)²·sin(2θ)^{2α/5-γ}`.  The proof is the same computation: `sin_two_rpow` gives
`∫_{Iθ} sin(2θ)^{-η} ≤ 10⁴` and `∫_{Iθ} sin(2θ)^{2α/5-γ} ≤ 1000/(3α)`, and the `α²` of the
coefficient together with `α ≤ 1` turns the `1/α` divergence into an `α`-independent
constant. -/
theorem ang_fac5_integrable_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ
        + 5 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.FTS.Nonlinear.RadialProd.smE θ
        + 5 * (100000 * α) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))) ≤ K := by
  refine ⟨10000 + 50000000000000 / 3, by norm_num, ?_⟩
  intro α hα hα1
  -- Integrability of the two summands.
  have hIe : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ := by
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).1
    simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
  have hp1 : -1 < 2 * (α / 5) - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * (α / 5) - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hIex : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow _ hp1 hp2).1
  constructor
  · exact hIe.add (hIex.const_mul _)
  · -- The two numerical bounds for the `θ`-integrals.
    have hIe_le : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ) ≤ 10000 := by
      have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
      have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
      rw [hexp] at h
      have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
      rw [h2] at h
      simpa [Work.FTS.Nonlinear.RadialProd.smE] using h
    have hIex_le : (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)) ≤ 1000 / (3 * α) := by
      have h := (Work.Spaces.sin_two_rpow _ hp1 hp2).2
      have hexp : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
        rw [Work.Spaces.gam]; ring
      rw [hexp] at h
      have heq : (100 : ℝ) / (3 * α / 10) = 1000 / (3 * α) := by
        have h1 : (3 : ℝ) * α ≠ 0 := by positivity
        have h2 : (3 : ℝ) * α / 10 ≠ 0 := by positivity
        field_simp
        ring
      calc (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α))
          ≤ 100 / (3 * α / 10) := h
        _ = 1000 / (3 * α) := heq
    have h5 : (0 : ℝ) ≤ 5 * (100000 * α) ^ 2 := by positivity
    have hkey : 10000 + 5 * (100000 * α) ^ 2 * (1000 / (3 * α))
        ≤ 10000 + 50000000000000 / 3 := by
      have heq : 5 * (100000 * α) ^ 2 * (1000 / (3 * α)) = (50000000000000 / 3) * α := by
        have h1 : α ≠ 0 := ne_of_gt hα
        field_simp
        ring
      rw [heq]
      nlinarith [hα1]
    have hsplit : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.Nonlinear.RadialProd.smE θ
            + 5 * (100000 * α) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α)))
        = (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ)
          + 5 * (100000 * α) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 * (α / 5) - Work.Spaces.gam α) := by
      rw [MeasureTheory.integral_add hIe (hIex.const_mul _), MeasureTheory.integral_const_mul]
    rw [hsplit]
    linarith [hIe_le, mul_le_mul_of_nonneg_left hIex_le h5, hkey]

end Work.FTS.StrongEps.H5.AngFac5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.fk_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## The envelope comparison `Env ≤ 3·α^{-2}(1+X)²` -/


/-! ## The two `FK(g)`-rows `N₄^{gg}`, `N₅^{gg}` -/

/-- **Rows `N₄^{gg}`, `N₅^{gg}` in the open class.**  `N₄^{gg} = -(1/2)FK(f)·D_θf` and
`N₅^{gg} = -sin²θ·FK(f)·f` are bounded by `K·Env α f`; this is the verbatim open-class version
of `Work.FTS.NonlinRows.Rl1.ggRows45`, with the slot data supplied by
`slotData_open_g`/`slotData_open_dth` in place of `slot0`/`slot1`. -/
theorem gg_fk_open_rows : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f : Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Fa (Work.FTS.Nonlin.N4gg α f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Fa (Work.FTS.Nonlin.N5gg f)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  refine ⟨12 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α f hα hα1 hso hmem
  have hXs : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have s0 : Work.FTS.NonlinRows.Rl1.SlotData α f
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_g (α := α) (f := f) hα hso hmem
  have s1 : Work.FTS.NonlinRows.Rl1.SlotData α (Work.Spaces.Dth f)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f) (Work.Spaces.HkSq α 4 f) :=
    slotData_open_dth (α := α) (f := f) hα hso hmem
  have hΦ1w := Work.FTS.NonlinRows.Rl1.invSq_mul_integrable_le
    (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f) (Xs := Work.Spaces.HkSq α 4 f)
    s1.nonneg s1.meas s1.intw s1.lew
  have hΦ0w := Work.FTS.NonlinRows.Rl1.invSq_mul_integrable_le
    (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f) (Xs := Work.Spaces.HkSq α 4 f)
    s0.nonneg s0.meas s0.intw s0.lew
  have hEnvn : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  have hX2 := Work.FTS.NonlinRows.Rl1.Xn_sq_le_Env f hα hα1
  have hfinal : ∀ {N : Fn}, Fa N ≤ ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
      * (Work.FTS.Nonlin.Xn α f) ^ 2) →
      Fa N ≤ ENNReal.ofReal ((12 * Real.sqrt (Real.pi / 2) + 1)
        * Work.FTS.NonlinRows.Rl1.Env α f) := by
    intro N hN
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    have h12 : 0 ≤ 12 * Real.sqrt (Real.pi / 2) := by positivity
    calc 12 * Real.sqrt (Real.pi / 2) * (Work.FTS.Nonlin.Xn α f) ^ 2
        ≤ 12 * Real.sqrt (Real.pi / 2) * Work.FTS.NonlinRows.Rl1.Env α f :=
          mul_le_mul_of_nonneg_left hX2 h12
      _ ≤ (12 * Real.sqrt (Real.pi / 2) + 1) * Work.FTS.NonlinRows.Rl1.Env α f := by
          nlinarith [hEnvn, Real.sqrt_nonneg (Real.pi / 2)]
  constructor
  · -- `N₄^{gg} = -(1/2)·FK f·D_θ f`
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_coef_slot
      (N := Work.FTS.Nonlin.N4gg α f)
      (A := fun r _ => 3 * Work.Construction.FK f r) (B := Work.Spaces.Dth f)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 f) (Zs := Work.Spaces.HkSq α 4 f)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 f)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s1.nonneg s1.meas hΦ1w.1 hΦ1w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s1.aesm r hr)
      (fun r hr => s1.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := Work.FTS.NonlinRows.Rl1.FK_sq_le_sixteen_Phi0 (g := f) hr
          (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK f r) ^ 2
            = 9 * (Work.Construction.FK f r) ^ 2 := by ring
        rw [h9]
        linarith [h])
      (fun r hr => (Work.FTS.NonlinRows.Rl1.slot_lintegral_eq (s1.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α f r θ|
            = |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK f r|
              * |Work.Spaces.Dth f r θ| := by
          rw [Work.FTS.Nonlin.N4gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        have h2 : |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK f r|
              * |Work.Spaces.Dth f r θ|
            ≤ 3 * (1 / 2) * |Work.Construction.FK f r| * |Work.Spaces.Dth f r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hK (by norm_num)
        have h3 : 3 * (1 / 2) * |Work.Construction.FK f r| * |Work.Spaces.Dth f r θ|
            ≤ |3 * Work.Construction.FK f r| * |Work.Spaces.Dth f r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          nlinarith [abs_nonneg (Work.Construction.FK f r),
            abs_nonneg (Work.Spaces.Dth f r θ)]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 f))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 f) = Work.FTS.Nonlin.Xn α f := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain
  · -- `N₅^{gg} = -sin²θ·FK f·f`
    have hmain := Work.FTS.NonlinRows.Rl1.Fa_le_coef_slot
      (N := Work.FTS.Nonlin.N5gg f)
      (A := fun r _ => 3 * Work.Construction.FK f r) (B := f)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 f) (Zs := Work.Spaces.HkSq α 4 f)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 f)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s0.nonneg s0.meas hΦ0w.1 hΦ0w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s0.aesm r hr)
      (fun r hr => s0.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := Work.FTS.NonlinRows.Rl1.FK_sq_le_sixteen_Phi0 (g := f) hr
          (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK f r) ^ 2
            = 9 * (Work.Construction.FK f r) ^ 2 := by ring
        rw [h9]
        linarith [h])
      (fun r hr => (Work.FTS.NonlinRows.Rl1.slot_lintegral_eq (s0.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := Work.FTS.NonlinRows.Rl1.K_abs_le_three' hθ
        have hs : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg f r θ|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK f r|
              * |f r θ| := by
          rw [Work.FTS.Nonlin.N5gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        have h2 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK f r|
              * |f r θ|
            ≤ 3 * 1 * |Work.Construction.FK f r| * |f r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul hK hs (sq_nonneg _) (by norm_num)
        have h3 : 3 * 1 * |Work.Construction.FK f r| * |f r θ|
            ≤ |3 * Work.Construction.FK f r| * |f r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), mul_one]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt (Work.Spaces.HkSq α 4 f))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α f) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 f) = Work.FTS.Nonlin.Xn α f := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain

/-! ## The three row groups and the assembly -/


end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The angular majorant -/

/-- The `γ`-weighted jet sum `Σ_{1 ≤ m ≤ 4} (dthU^[m] (Γ/c))² sin(2θ)^{-γ}`. -/
def VfsJetSum (α : ℝ) (θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 4,
    (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The angular majorant of the profile `Γ/c`:
`(Γ/c)² sin(2θ)^{-η} + α² (Γ/c)² sin(2θ)^{-γ} + VfsJetSum α θ`. -/
def VfsJetMaj (α : ℝ) (θ : ℝ) : ℝ :=
  (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    + VfsJetSum α θ

@[simp] theorem VfsJetMaj_apply (α θ : ℝ) : VfsJetMaj α θ =
    (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + VfsJetSum α θ := rfl

@[simp] theorem VfsJetSum_apply (α θ : ℝ) : VfsJetSum α θ =
    ∑ m ∈ Finset.Icc 1 4,
      (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl

/-! ## Elementary trigonometric and `rpow` facts -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Real.sin_two_mul]
  exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, Real.pi_pos]⟩))
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [h0, Real.pi_pos],
      by linarith [h1, Real.pi_pos]⟩)

/-- `sin(2θ) > 0` on `(0,π/2)`. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]
  have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-- Antitonicity in the exponent of `x ↦ x^p` on `(0,1]`. -/
theorem rpow_le_rpow_of_le_one {x a b : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hab : a ≤ b) :
    x ^ b ≤ x ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hab

/-- `η ≤ γ(α)` for `0 ≤ α`. -/
theorem eta_le_gam {α : ℝ} (hα : 0 ≤ α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  simp only [Work.Spaces.eta, Work.Spaces.gam]
  linarith

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ(α)}` on `(0,π/2)`. -/
theorem sin_two_rpow_eta_le_gam {α θ : ℝ} (hα : 0 ≤ α)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  rpow_le_rpow_of_le_one (x := Real.sin (2 * θ)) (a := -(Work.Spaces.gam α))
    (b := -(Work.Spaces.eta)) (sin_two_pos_Ioo hθ) (Real.sin_le_one _)
    (by linarith [eta_le_gam hα])



/-- Cauchy–Schwarz for the five-term sum: `(Σ_{m<5} a m)² ≤ 5 Σ_{m<5} (a m)²`. -/
theorem sum_five_sq_le (a : ℕ → ℝ) :
    (∑ m ∈ Finset.range 5, a m) ^ 2 ≤ 5 * ∑ m ∈ Finset.range 5, (a m) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 0 - a 3),
    sq_nonneg (a 0 - a 4), sq_nonneg (a 1 - a 2), sq_nonneg (a 1 - a 3),
    sq_nonneg (a 1 - a 4), sq_nonneg (a 2 - a 3), sq_nonneg (a 2 - a 4),
    sq_nonneg (a 3 - a 4)]

/-! ## Basic properties of `VfsJetMaj` -/

/-- `VfsJetSum` is nonnegative on `Iθ`. -/
theorem VfsJetSum_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ VfsJetSum α θ := by
  rw [VfsJetSum]
  exact Finset.sum_nonneg (fun m _ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))

/-- `VfsJetMaj` is nonnegative on `Iθ`. -/
theorem VfsJetMaj_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ VfsJetMaj α θ := by
  have hs := sin_two_nonneg_Iθ hθ
  rw [VfsJetMaj]
  exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _))
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)))
    (VfsJetSum_nonneg α hθ)

/-- The `η`-summand of `VfsJetMaj`. -/
theorem VfsJetMaj_ge_eta (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ VfsJetMaj α θ := by
  have h1 : 0 ≤ α ^ 2 * (VfsGc α θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  rw [VfsJetMaj]
  linarith [h1, VfsJetSum_nonneg α hθ]

/-- The `α²`-summand of `VfsJetMaj`. -/
theorem VfsJetMaj_ge_alpha (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ VfsJetMaj α θ := by
  have h0 : 0 ≤ (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  rw [VfsJetMaj]
  linarith [h0, VfsJetSum_nonneg α hθ]

/-- Every `γ`-weighted jet summand of `VfsJetMaj`. -/
theorem VfsJetMaj_ge_gam (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ VfsJetMaj α θ := by
  have hs := sin_two_nonneg_Iθ hθ
  have hmem : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hm1, hm4⟩
  have hle : (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ VfsJetSum α θ := by
    rw [VfsJetSum]
    exact Finset.single_le_sum
      (s := Finset.Icc 1 4)
      (f := fun i => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (fun i _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) hmem
  have h0 : 0 ≤ (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have h1 : 0 ≤ α ^ 2 * (VfsGc α θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg hs _)
  rw [VfsJetMaj]
  linarith

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Almost everywhere strong measurability of the radial slot sum `∑_{q ≤ 3} (D_z^q (L₁₂f·B))² w²`

The integrand of `VfsRadSlotBound` (the weighted slot bound for the radial product
`z ↦ L₁₂(f)(z)·B(z)`) is a finite sum of the four terms
`(D_z^q (fun z _ => L₁₂ f z * B z) z 0)² · (w z)²`, `q ≤ 3`.

Since the function `(z,θ) ↦ L₁₂f z · B z` is independent of `θ`, the slot operators act on
the radial profile `G z = L₁₂ f z · B z` as the one-dimensional operator `Zop u = z·u'`
(`Zop_slice`), so the `q`-th slot is `Zop^[q] G`.  Both `L₁₂ f` and `B` are `C⁴` on `(0,∞)`,
hence so is `G` (`ContDiffOn.mul`), and a `C^{b+k}` function has `C^k` `Zop`-iterates of
order `b`; in particular `Zop^[q] G` is continuous on the *open* half-line `(0,∞)` for
`q ≤ 3`.  A function continuous on `(0,∞)` is a.e. strongly measurable for the restriction
of Lebesgue measure, and `(0,∞)` and `Iz = [0,∞)` differ by the null set `{0}`
(`Measure.restrict_congr_set` and `Ioi_ae_eq_Ici`), which gives the statement for `Iz`.

Everything is proved from Mathlib alone (the workspace imports supply only the *definitions*
`L₁₂`, `Iz`, `w`, `DzIter`, `Zop`, and the identity `Zop_slice`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.VfsRadAux

/-- A `C^{n+1}` function on `(0,∞)` has `C^n` derivative there. -/
private theorem contDiffOn_deriv_of_succ {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (deriv u) (Set.Ioi (0 : ℝ)) := by
  have hfd : ContDiffOn ℝ n (fderiv ℝ u) (Set.Ioi (0 : ℝ)) :=
    hu.fderiv_of_isOpen isOpen_Ioi (by simp)
  have hev : ContDiffOn ℝ n (fun z : ℝ => (fderiv ℝ u z) 1) (Set.Ioi (0 : ℝ)) :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}` function on `(0,∞)` has `C^k` `Zop`-iterates of order `b`. -/
private theorem contDiffOn_Zop_iter {u : ℝ → ℝ} (b k : ℕ)
    (hu : ContDiffOn ℝ (b + k) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ k (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := by
  induction b generalizing k with
  | zero => simpa using hu
  | succ b ih =>
      have hu' : ContDiffOn ℝ (b + (k + 1)) u (Set.Ioi (0 : ℝ)) :=
        hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 : ContDiffOn ℝ (k + 1) (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) :=
        ih (k + 1) hu'
      have h2 : ContDiffOn ℝ k (deriv (Work.Spaces.Zop^[b] u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_deriv_of_succ h1
      have h3 : ContDiffOn ℝ k (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z)
          (Set.Ioi (0 : ℝ)) := (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      exact h3

/-- A `C^m` function on `(0,∞)` has a `C^{m-q}` `Zop`-iterate of order `q ≤ m`, hence a
continuous one. -/
private theorem contDiffOn_Zop_iter_le {u : ℝ → ℝ} {m q : ℕ}
    (hu : ContDiffOn ℝ m u (Set.Ioi (0 : ℝ))) (hq : q ≤ m) :
    ContDiffOn ℝ (m - q) (Work.Spaces.Zop^[q] u) (Set.Ioi (0 : ℝ)) := by
  refine contDiffOn_Zop_iter q (m - q) ?_
  refine hu.of_le ?_
  exact_mod_cast (by omega : q + (m - q) ≤ m)

theorem aestronglyMeasurable_slotSum {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ}
    (hL : ContDiffOn ℝ 4 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)))
    (hB : ContDiffOn ℝ 4 B (Set.Ioi (0 : ℝ))) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  let G : ℝ → ℝ := fun z => Work.Construction.L12 f z * B z
  have hG : ContDiffOn ℝ 4 G (Set.Ioi (0 : ℝ)) := hL.mul hB
  have hw : Measurable (Work.Spaces.w) := by
    unfold Work.Spaces.w
    fun_prop
  -- the `Zop`-iterates of the radial profile are continuous on `(0,∞)`
  have hZcont : ∀ q ≤ 3, ContinuousOn (Work.Spaces.Zop^[q] G) (Set.Ioi (0 : ℝ)) := by
    intro q _
    exact (contDiffOn_Zop_iter_le (u := G) (m := 4) hG (by omega)).continuousOn
  -- the slot sum built from the `Zop`-iterates is a.e. strongly measurable on `(0,∞)`
  have haesmZop : MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h' : MeasureTheory.AEStronglyMeasurable (∑ q ∈ Finset.range 4,
        fun z : ℝ => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Finset.aestronglyMeasurable_sum (Finset.range 4)
        (f := fun q z => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (fun q hq => by
          have hq3 : q ≤ 3 := by have := Finset.mem_range.mp hq; omega
          exact (((hZcont q hq3).aestronglyMeasurable measurableSet_Ioi).pow 2).mul
            (hw.aestronglyMeasurable.pow 2))
    refine h'.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.sum_apply]
  -- the slot operators of a `θ`-independent function are the `Zop`-iterates of its profile
  have hpt : ∀ q : ℕ, ∀ z : ℝ,
      Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = Work.Spaces.Zop^[q] G z := by
    intro q z
    have h1 := congrFun (Work.Spaces.Zop_slice q
      (fun z _ => Work.Construction.L12 f z * B z) 0) z
    rw [h1]
  have heq : (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    exact Finset.sum_congr rfl (fun q _ => by rw [hpt q z])
  rw [heq]
  -- `(0,∞)` and `Iz = [0,∞)` differ by the null set `{0}`
  have hIoi : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    show MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
    exact Measure.restrict_congr_set Ioi_ae_eq_Ici
  rw [← hIoi]
  exact haesmZop

end Work.FTS.StrongPersist.L3Rhs.VfsRadAux
end
end
