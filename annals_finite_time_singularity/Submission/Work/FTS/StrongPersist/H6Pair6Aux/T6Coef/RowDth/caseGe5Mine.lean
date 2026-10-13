/-
# `RowDth.caseGe5Mine` — the per-term summand of the `A · ∂_θ f` row, case `5 ≤ i + j`

This is the top case of the Leibniz remainder of the `D_θ`-row of the level-six coefficient
pairing: the summand

  `∫_z ∫_θ ρ · (D_z^j D_θ^i A) · (D_z^{b-j} D_θ^{a-i+1} f) · (D_z^b D_θ^a f)`

with `i + j ≥ 5`, `i ≤ a`, `j ≤ b`, `a + b ≤ 6`, and not the exceptional weight
(`i = 0` together with the `γ`-leaf weight, which is handled by `caseExc`).

At `i + j ≥ 5` the second `f`-slot has order `(a - i + 1) + (b - j) = a + b - (i + j) + 1 ≤ 2`,
so it is bounded *pointwise* by `C · |f|_{ℋ⁴} ≤ C · M` (`mixed_pointwise_le_Xn`); the
coefficient slot and the third `f`-slot are then paired by the iterated Cauchy–Schwarz
`cs_iterated`, giving `|A|_{ℋ⁶} · |f|_{ℋ⁶} ≤ K6 · X6`.  The weight `ρ` is one of the three leaf
weights, hence a canonical weight `canonW q` with `0 ≤ q ≤ γ` and `q ≤ η` whenever the slot is
a pure `D_z`-slot (`i = 0`); the latter is exactly why the exceptional case (`i = 0` with the
`γ`-leaf weight) has to be excluded.

The proof is assembled from `RowDth/Wgt.lean` (weight comparisons and continuity),
`RowDth/En.lean` (energy bounds), `RowDth/CS.lean` (iterated Cauchy–Schwarz) and
`RowDth/Integ.lean` (integrability from a pointwise majorant).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.CS
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem caseGe5Mine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b i j : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b → ¬(i = 0 ∧ j = 0) →
      5 ≤ i + j → ¬(i = 0 ∧ ρ = Work.FTS.TransportS.leafGam α) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨Cm, hCmpos, hCmsup⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cm, hCmpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hia hjb hne h5 hexc
  obtain ⟨hsmA, hA4, hA6, hvalA, hn4, hn6⟩ := hcoef
  obtain ⟨hsmf, hf6, hf7, hvanish, haxis, hbdd⟩ := hdat
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hf4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmf 4 (by norm_num) hf6
  have hK0nn : 0 ≤ K0 := le_trans (abs_nonneg (A 1 (Real.pi / 4)))
    (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hCmnn : 0 ≤ Cm := hCmpos.le
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  -- ## the canonical exponent carried by the leaf weight `ρ`
  have heta_gam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hcases : ∃ q : ℝ, ρ = canonW q ∧ 0 ≤ q ∧ q ≤ Work.Spaces.gam α
      ∧ (i = 0 → q ≤ Work.Spaces.eta) := by
    rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
    · refine ⟨Work.Spaces.eta, ?_, Work.Spaces.eta_pos.le, heta_gam, fun _ => le_rfl⟩
      rw [hρ]; exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1
    · refine ⟨0, ?_, le_rfl, hgam_nn, fun _ => Work.Spaces.eta_pos.le⟩
      rw [hρ]; exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1
    · refine ⟨Work.Spaces.gam α, ?_, hgam_nn, le_rfl, ?_⟩
      · rw [hρ]; exact Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α
      · intro hi0
        exact absurd ⟨hi0, hρ⟩ hexc
  obtain ⟨q, rfl, hq0, hqγ, hqiη⟩ := hcases
  -- ## index bookkeeping
  have hge : 1 ≤ a - i + 1 := by omega
  have hle : a - i + 1 + (b - j) ≤ 6 := by omega
  have hqy2 : a - i + 1 + (b - j) ≤ 2 := by omega
  -- ## the pointwise (sup) bound on the second `f`-slot
  have hYsup : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| ≤ Cm * M := by
    intro z θ hz hθ0 hθ2
    refine le_trans
      (hCmsup α f hα0 hα1 hsmf hf4 (b - j) (a - i + 1) hge hqy2 z θ hz hθ0 hθ2) ?_
    exact mul_le_mul_of_nonneg_left hbdd hCmnn
  -- ## the level-`6` energy of the coefficient slot `X = D_z^j D_θ^i A`
  have hEX : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 A := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [hi0, Work.Spaces.mixed_zero_right]
      exact canonW_energy_z6 hq0 hqη hsmA hA6 (by omega)
    · exact canonW_energy_mixed6 hα0 hq0 hqγ hsmA hA6 hipos (by omega)
  -- ## the level-`6` energy of the third `f`-slot `Z = D_z^b D_θ^a f`
  have hEZ : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f := by
    rcases Nat.eq_zero_or_pos a with ha0 | ha1
    · have hi0 : i = 0 := by omega
      have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [ha0, Work.Spaces.mixed_zero_right]
      exact canonW_energy_z6 hq0 hqη hsmf hf6 (by omega)
    · exact canonW_energy_mixed6 hα0 hq0 hqγ hsmf hf6 ha1 (by omega)
  -- ## iterated Cauchy–Schwarz on the coefficient slot and the third `f`-slot
  have hCS := cs_iterated (ρ := fun z θ => canonW q z θ)
    (A := fun z θ => Work.Spaces.mixed j i A z θ)
    (B := fun z θ => Work.Spaces.mixed b a f z θ)
    (fun z hz θ hθ => canonW_nonneg hθ) hEX.1 hEZ.1 hEX.2.1 hEZ.2.1
  have hCS' : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
      * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|)
      ≤ K6 * Work.Spaces.HkNorm α 6 f := by
    refine le_trans hCS ?_
    have h1 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed j i A z θ) ^ 2) ≤ K6 :=
      le_trans (Real.sqrt_le_sqrt hEX.2.2) hn6
    have h2 : Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkNorm α 6 f :=
      le_trans (Real.sqrt_le_sqrt hEZ.2.2) le_rfl
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hK6nn
  -- ## the pointwise domination of the coefficient slot
  have hX6le : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed j i A z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
    intro z θ _ hθ0 hθ2
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [hi0, Work.Spaces.mixed_zero_right]
      exact canonW_mul_z_le6 hq0 hqη (by omega) ⟨hθ0, hθ2⟩
    · exact canonW_mul_mixed_le6 hα0 hq0 hqγ hipos (by omega) ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  -- ## the pointwise domination of the third `f`-slot
  have hZle : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ _ hθ0 hθ2
    by_cases ha0 : a = 0
    · have hi0 : i = 0 := by omega
      have hqη : q ≤ Work.Spaces.eta := hqiη hi0
      rw [ha0, Work.Spaces.mixed_zero_right]
      exact canonW_mul_z_le6 hq0 hqη (by omega) ⟨hθ0, hθ2⟩
    · have ha1 : 1 ≤ a := by omega
      exact canonW_mul_mixed_le6 hα0 hq0 hqγ ha1 (by omega) ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  -- ## AM–GM for the weighted product of the two `L²`-slots
  have hXZ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hX2 := hX6le z θ hz hθ0 hθ2
    have hZ2 := hZle z θ hz hθ0 hθ2
    have hAM : 2 * (canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|))
        ≤ canonW q z θ * (Work.Spaces.mixed j i A z θ) ^ 2
          + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      have h := two_mul_le_add_sq |Work.Spaces.mixed j i A z θ|
        |Work.Spaces.mixed b a f z θ|
      calc 2 * (canonW q z θ * (|Work.Spaces.mixed j i A z θ|
            * |Work.Spaces.mixed b a f z θ|))
          = canonW q z θ * (2 * |Work.Spaces.mixed j i A z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
        _ ≤ canonW q z θ * (|Work.Spaces.mixed j i A z θ| ^ 2
              + |Work.Spaces.mixed b a f z θ| ^ 2) := mul_le_mul_of_nonneg_left h hcw
        _ = canonW q z θ * (Work.Spaces.mixed j i A z θ) ^ 2
              + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
            rw [sq_abs, sq_abs]; ring
    have h2 : canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|)
        ≤ Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
      have hleft : 0 ≤ canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|) :=
        mul_nonneg hcw (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      linarith [hAM, hX2, hZ2, hleft]
    calc canonW q z θ * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|
        = canonW q z θ * (|Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ _ := h2
  -- ## the pointwise bound of the full integrand
  have hptC : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        ≤ (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) := by
    intro z θ hz hθ0 hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hXs := hYsup z θ hz hθ0 hθ2
    have hXZ' := hXZ z θ hz hθ0 hθ2
    have hcst : 0 ≤ Cm * M := mul_nonneg hCmnn hMnn
    have hleft : 0 ≤ canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed b a f z θ| :=
      mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * (canonW q z θ
          * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ
            + Work.Spaces.HkIntegrand α 6 f z θ) := mul_le_mul hXs hXZ' hleft hcst
  -- ## the marginal of the pointwise majorant
  have hmargH : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
      Work.Spaces.Iz :=
    (hA6.2.add hf6.2).congr_fun
      (fun z hz => (MeasureTheory.integral_add (hA6.1 z hz) (hf6.1 z hz)).symm)
      measurableSet_Ici
  have hmargH' : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ))
      Work.Spaces.Iz := by
    have h0 : MeasureTheory.IntegrableOn (fun z : ℝ => (Cm * M) *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)))
        Work.Spaces.Iz :=
      hmargH.const_mul (Cm * M)
    refine MeasureTheory.IntegrableOn.congr_fun h0 ?_ measurableSet_Ici
    intro z hz
    exact (MeasureTheory.integral_const_mul (Cm * M)
      (fun θ => Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)).symm
  -- ## the integrability conjuncts of the full integrand
  have hint : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz :=
    integrableConjuncts
      (F := fun z θ => canonW q z θ * Work.Spaces.mixed j i A z θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ * Work.Spaces.mixed b a f z θ)
      (H := fun z θ => (Cm * M) * (Work.Spaces.HkIntegrand α 6 A z θ
        + Work.Spaces.HkIntegrand α 6 f z θ))
      ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (hsmA.mixed j i).continuousOn).mul
        (hsmf.mixed (b - j) (a - i + 1)).continuousOn).mul (hsmf.mixed b a).continuousOn)
      (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_const.mul
        ((hsmA.continuousOn_HkIntegrand α 6).add (hsmf.continuousOn_HkIntegrand α 6))))
      (fun θ => by rw [canonW_zero_z]; ring)
      (fun z hz => ((hA6.1 z hz).add (hf6.1 z hz)).const_mul _)
      hmargH' hptC
  -- ## the integrability of the absolute-value integrand
  have hGcont : ContinuousOn (Function.uncurry (fun z θ => canonW q z θ
      * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (hsmA.mixed j i).continuousOn.abs).mul (hsmf.mixed b a).continuousOn.abs)
  have hGboth : (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|)
        Work.Spaces.Iz :=
    integrableConjuncts
      (F := fun z θ => canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed b a f z θ|)
      (H := fun z θ => Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
      hGcont
      (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hsmA.continuousOn_HkIntegrand α 6).add (hsmf.continuousOn_HkIntegrand α 6)))
      (fun θ => by rw [canonW_zero_z]; ring)
      (fun z hz => (hA6.1 z hz).add (hf6.1 z hz))
      hmargH
      (fun z θ hz hθ0 hθ2 => by
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _))
          (abs_nonneg _))]
        exact hXZ z θ hz hθ0 hθ2)
  -- ## the slicewise bound
  have hptC' : ∀ z ∈ Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, |canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|)
      ≤ (Cm * M) * (∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    rw [← MeasureTheory.integral_const_mul]
    refine integral_Iθ_mono_ae (fun θ hθ => ?_) (fun θ hθ => abs_nonneg _)
      ((hGboth.1 z hzIz).const_mul _)
    have hθI : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hXs := hYsup z θ hz hθ.1 hθ.2
    have hleft : 0 ≤ canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed b a f z θ| :=
      mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)
    calc |canonW q z θ * Work.Spaces.mixed j i A z θ
          * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        = |Work.Spaces.mixed (b - j) (a - i + 1) f z θ| * (canonW q z θ
          * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]; ring
      _ ≤ (Cm * M) * (canonW q z θ * |Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed b a f z θ|) := mul_le_mul_of_nonneg_right hXs hleft
  -- ## the arithmetic at the target bracket
  have hbr : K6 * M * Work.Spaces.HkNorm α 6 f
      ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
    have h1 : (0 : ℝ) ≤ K4 + K6 := by linarith
    have hK6M : K6 * M ≤ (K4 + K6) * (1 + M) :=
      mul_le_mul (by linarith) (by linarith) hMnn h1
    have hstep : K6 * M * Work.Spaces.HkNorm α 6 f
        ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
      mul_le_mul hK6M (by linarith) hX6nn (by positivity)
    have hnn : (0 : ℝ) ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have htail : (Cm * M) * (K6 * Work.Spaces.HkNorm α 6 f)
      ≤ Cm * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
    have hnn2 : 0 ≤ K6 * M * Work.Spaces.HkNorm α 6 f :=
      mul_nonneg (mul_nonneg hK6nn hMnn) hX6nn
    have hα12 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_alpha_rpow_neg_half hα0 hα1
    calc (Cm * M) * (K6 * Work.Spaces.HkNorm α 6 f)
        = Cm * (K6 * M * Work.Spaces.HkNorm α 6 f) := by ring
      _ ≤ Cm * (α ^ (-(1 / 2 : ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnn2 hα12) hCmnn
      _ = Cm * α ^ (-(1 / 2 : ℝ)) * (K6 * M * Work.Spaces.HkNorm α 6 f) := by ring
      _ ≤ Cm * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
          mul_le_mul_of_nonneg_left hbr (mul_nonneg hCmnn hαnn)
  -- ## assembly
  refine ⟨hint.1, hint.2, ?_⟩
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ
        * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, (Cm * M) * (∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) := by
        refine integral_Iz_mono_ae (fun z hz => ?_) (fun z hz => abs_nonneg _)
          (hGboth.2.const_mul _)
        exact le_trans MeasureTheory.abs_integral_le_integral_abs (hptC' z hz)
    _ = (Cm * M) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ
        * |Work.Spaces.mixed j i A z θ| * |Work.Spaces.mixed b a f z θ|) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (Cm * M) * (K6 * Work.Spaces.HkNorm α 6 f) :=
        mul_le_mul_of_nonneg_left hCS' (mul_nonneg hCmnn hMnn)
    _ ≤ Cm * α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
             + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := htail

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
