import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1S.sbWordCubeIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1C.trimOffInteriorCube` — FS `eq:badset` at the **matched (single cube
# cutoff)** window

The cube-window twin of `Work.BoseFixB1B.trimOffInterior`: the interior `u`-integral
`∫_{I₋} sbWordCube` is dominated by the full one `∫_{ℝ³} sbWordCube`, at the cost of the a-priori
error `C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}‖Φ‖²`.

## Proof

The whole content is the *crude per-`u` lower bound* `hpb` (an input), the *band-cost absorption*
`habs` (an input) and the `u`-measure bookkeeping in between, which is the frozen argument of
`Work.BoseFixB1B.trimOffInterior_of_inputs` verbatim.  The three window-dependent ingredients are
replaced by their matched-window twins:

* the `u`-marginal integrability of the word — `Work.BoseFixB1S.sbWordCubeIntegrable` (PROVED,
  axiom-clean) in place of `integrable_sbKin_marginal` + `sbPot_integral_le_potWordU`;
* the pointwise lower bound *off* the sliding cube, where the potential slot vanishes identically
  (`Work.BoseFixB1B.sbPot_eq_zero_of_mem_farSet`) and the kinetic slot is nonnegative
  (`sbKinCube_nonneg` below, from `tBwordKinInd_nonneg` and `tbGapCoeff_nonneg`);
* the cube/slab geometry `(I₋)ᶜ ∩ cube ⊆ bandSet` and `cubeᶜ ⊆ farSet`
  (`Work.BoseFixB1B.compl_inter_cube_subset_bandSet`, `..._cube_compl_subset_farSet`), which is
  window-independent.

Nothing else is used — in particular neither the ball-window localisation nor any comparison of the
two windows appears, which is exactly the point of the matched chapter.
-/

namespace Work.BoseFixB1C

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1 Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `sbWordCube = sbKinCube + sbPot` (definitional). -/
theorem sbWordCube_eq_add {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (u : E3) (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB1B.sbWordCube v h μ u Φ
      = Work.BoseFixB1B.sbKinCube v μ u Φ + Work.BoseFixB1.sbPot h μ u Φ := rfl

/-- **The matched kinetic word is nonnegative at an admissible point**: its gap row
`bGapCoeff·n₊(B(u))` is nonnegative (`tbGapCoeff_nonneg`, `ε_T ≥ 0`) and its cube-windowed
spectral slot is nonnegative (`tBwordKinInd_nonneg`, which needs nothing). -/
theorem sbKinCube_nonneg {v : E3 → ℝ} {ε₀ μ : ℝ} (hadm : Adm v ε₀ μ) {n : ℕ}
    (u : E3) (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1B.sbKinCube v μ u Φ := by
  have heT : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hadm).1
  have hgap : 0 ≤ Work.BoseFixB1.bGapCoeff v μ *
      Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
        (Work.BoseFixB1.bV v μ u) Φ :=
    mul_nonneg (Work.SmallBoxTBWord.tbGapCoeff_nonneg heT) (by
      unfold Work.UBBInputs8.cnPlusBoxInd
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)
  have hspec : 0 ≤ Work.BoseFixB1B.cubeSpectral v μ Φ u :=
    Work.BoseFixB1.tBwordKinInd_nonneg Φ
  have hdef : Work.BoseFixB1B.sbKinCube v μ u Φ
      = Work.BoseFixB1.bGapCoeff v μ *
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
            (Work.BoseFixB1.bV v μ u) Φ
        + Work.BoseFixB1B.cubeSpectral v μ Φ u := rfl
  rw [hdef]
  exact add_nonneg hgap hspec

theorem trimOffInteriorCube {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    {ε₁ C₁ : ℝ} (hε₁ : 0 < ε₁) (hC₁ : 0 ≤ C₁)
    (hpb : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)), Work.BoseBoxFix.IsLowB v h J μ n Φ →
        -(C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v))) * Work.BoseBoxFix.normB v μ n Φ
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
    {ε₂ C₂ : ℝ} (hε₂ : 0 < ε₂) (hC₂ : 0 ≤ C₂)
    (habs : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₂ μ →
      C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                  Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            + μ * (_root_.BoseGases.a v)
              * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
        ≤ C₂ * (μ ^ 2 * (_root_.BoseGases.a v) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)))
    : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
            ≤ (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
              + C * (μ ^ 2 * (_root_.BoseGases.a v) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the `u`-marginal integrability of the matched word
  obtain ⟨εreg, hεreg, hIntCube⟩ :=
    Work.BoseFixB1S.sbWordCubeIntegrable h hv hv1 hvrad hR hv_supp hav
  -- FS's parameter regime (for the band-volume law)
  obtain ⟨ε_F, hε_F, hFS⟩ :=
    Work.BoseFixB1.fsRegimeAt (A := _root_.BoseGases.a v) (R := R) hav hR
  refine ⟨min (min (min ε₁ ε₂) εreg) (min ε_F 1), C₂,
    lt_min (lt_min (lt_min hε₁ hε₂) hεreg) (lt_min hε_F one_pos), hC₂, ?_⟩
  intro μ hAdm hJK n Φ hlow
  have hA1 : (min (min (min ε₁ ε₂) εreg) (min ε_F 1) : ℝ) ≤ ε₁ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hA2 : (min (min (min ε₁ ε₂) εreg) (min ε_F 1) : ℝ) ≤ ε₂ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAreg : (min (min (min ε₁ ε₂) εreg) (min ε_F 1) : ℝ) ≤ εreg :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hAF : (min (min (min ε₁ ε₂) εreg) (min ε_F 1) : ℝ) ≤ ε_F :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hAdm1 : Adm v ε₁ μ := Adm.mono hAdm hA1
  have hAdm2 : Adm v ε₂ μ := Adm.mono hAdm hA2
  have hAdmreg : Adm v εreg μ := Adm.mono hAdm hAreg
  have hAdmF : Adm v ε_F μ := Adm.mono hAdm hAF
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have hFSμ := hFS μ hμ (adm_dilute hAdmF)
  obtain ⟨_, _, _, _, _, _, _, _, hμinv, hA0, hM⟩ := hFSμ
  -- the `u`-marginal integrability of the word (matched-window, corpus lemma)
  have hIntW : Integrable (fun u : E3 => Work.BoseFixB1B.sbWordCube v h μ u
      (Φ : Submission.BoseGases.X n → ℝ)) :=
    hIntCube μ hAdmreg Φ
  have hImeas : MeasurableSet (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_interiorSet _ _ _
  have hsplit := integral_add_compl hImeas hIntW
  -- the pointwise crude bound (an input; it holds on all of `ℝ³`)
  have hpt : ∀ u : E3,
      -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
    fun u => hpb μ hAdm1 hJK n Φ u hlow
  -- the finiteness of the cube slice
  have hcube_meas : MeasurableSet (Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d) :=
    Work.BoseFixB1B.measurableSet_cube _ _
  have hslice_meas : MeasurableSet ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d) :=
    hImeas.compl.inter hcube_meas
  have hbmeas : MeasurableSet (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_bandSet _ _ _
  have hslice_fin : volume ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono
      Work.BoseFixB1B.compl_inter_cube_subset_bandSet) ?_
    refine lt_of_le_of_lt (bandSet_volume_le_d3 hℓ hd hμ
      (by simpa only [neg_div] using hμinv) (by simpa only [neg_div] using hA0))
      ENNReal.ofReal_lt_top
  -- the `bandSet`-restricted integrability of `chiMass`
  have hchi_int : Integrable (fun u : E3 =>
      chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    simpa only [chiMass_def] using integrable_chiSmallB_mass hM hℓ hd
  -- the truncated bound is integrable on the slice
  have h2b : Integrable (fun u : E3 =>
      μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u + μ * (a v))
      (volume.restrict ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d)) :=
    ((hchi_int.integrableOn).const_mul (μ ^ 2 * (a v))).add
      (integrableOn_const (s := (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d) (μ := volume)
        (C := μ * (a v)) (ne_of_lt hslice_fin))
  have hslice_int : Integrable (fun u : E3 =>
      -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      (volume.restrict ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d)) :=
    ((Integrable.const_mul h2b C₁).neg).mul_const (normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
  -- the monotonicity on the slice
  have hmono : (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
        -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
        Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
    integral_mono_ae hslice_int hIntW.integrableOn (Eventually.of_forall hpt)
  -- the value of the truncated integral, bounded by minus the band cost
  have hband : (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
        -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≥ -(C₁ * (μ ^ 2 * (a v)
            * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
                chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          + μ * (a v)
            * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal))
          * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    set nB := normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hnBdef
    set S := (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d with hSdef
    have hSfin : volume S < ⊤ := hslice_fin
    have hSmeas : MeasurableSet S := hslice_meas
    -- expand the slice integral
    have hval : (∫ u in S, -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) * nB)
        = -(C₁ * nB) * ((μ ^ 2 * (a v)) * (∫ u in S, chiMass (paramsAt μ (a v)).M
              (sideAt μ (a v)) (paramsAt μ (a v)).d u) + (μ * (a v)) * (volume S).toReal) := by
      rw [show (fun u : E3 =>
            -(C₁ * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u + μ * (a v))) * nB)
          = (fun u => (-(C₁ * nB)) * (μ ^ 2 * (a v) * chiMass (paramsAt μ (a v)).M
                (sideAt μ (a v)) (paramsAt μ (a v)).d u + μ * (a v))) from by
        funext u; ring_nf]
      rw [integral_const_mul, integral_add, integral_const_mul, setIntegral_const]
      all_goals first
        | (simp only [MeasureTheory.measureReal_def]; ring_nf)
        | exact (hchi_int.integrableOn).const_mul _
        | exact integrableOn_const (s := S) (μ := volume) (C := μ * (a v)) (ne_of_lt hSfin)
    have hχmono : (∫ u in S, chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u)
        ≤ ∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u := by
      refine setIntegral_mono_set (hchi_int.integrableOn) ?_ ?_
      · exact Eventually.of_forall fun u => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
      · exact Eventually.of_forall fun u hu =>
          Work.BoseFixB1B.compl_inter_cube_subset_bandSet hu
    have hvolmono : (volume S).toReal
        ≤ (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal := by
      refine ENNReal.toReal_mono ?_ (measure_mono Work.BoseFixB1B.compl_inter_cube_subset_bandSet)
      exact ne_of_lt (lt_of_le_of_lt (bandSet_volume_le_d3 hℓ hd hμ
        (by simpa only [neg_div] using hμinv) (by simpa only [neg_div] using hA0))
        ENNReal.ofReal_lt_top)
    -- assemble
    have hcomb : (μ ^ 2 * (a v)) * (∫ u in S, chiMass (paramsAt μ (a v)).M
            (sideAt μ (a v)) (paramsAt μ (a v)).d u) + (μ * (a v)) * (volume S).toReal
        ≤ (μ ^ 2 * (a v)) * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          + (μ * (a v)) * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal := by
      have h0 : 0 ≤ (μ ^ 2 * (a v)) := by positivity
      have h1 : 0 ≤ (μ * (a v)) := mul_nonneg hμ.le (le_of_lt hav)
      nlinarith [hχmono, hvolmono, h0, h1]
    rw [hval]
    have hC1nBnn : 0 ≤ C₁ * nB := mul_nonneg hC₁ (normB_nonneg _)
    nlinarith [hcomb, hC1nBnn]
  -- `sbWordCube ≥ 0` off the cube, hence the complement integral dominates the slice integral
  have hnonneg_off : 0 ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
      \ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
      Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem (hImeas.compl.diff hcube_meas)] with u hu
    have hc : u ∉ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d := hu.2
    have hfar : u ∈ farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ :=
      Work.BoseFixB1B.cube_compl_subset_farSet hc
    have hz := Work.BoseFixB1B.sbPot_eq_zero_of_mem_farSet (v := v) (h := h) (μ := μ) (n := n)
      hℓ hd hfar (Φ : Submission.BoseGases.X n → ℝ)
    rw [sbWordCube_eq_add, hz, add_zero]
    exact sbKinCube_nonneg hAdm1 u (Φ : Submission.BoseGases.X n → ℝ)
  have hdecomp : (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
        Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
      = (∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
            ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
            \ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    have hdisj : Disjoint ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
        ∩ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d)
        ((interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ
          \ Work.BoseFixB1B.cube (sideAt μ (a v)) (paramsAt μ (a v)).d) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    rw [← setIntegral_union hdisj (hImeas.compl.diff hcube_meas)
      (hIntW.integrableOn.mono_set Set.inter_subset_left)
      (hIntW.integrableOn.mono_set Set.sdiff_subset)]
    congr 1
    ext x
    simp [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
  have habsμ := habs μ hAdm2
  have hstep : -(C₁ * (μ ^ 2 * (a v)
          * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        + μ * (a v)
          * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal))
        * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≥ -(C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
          * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have h1 : C₁ * (μ ^ 2 * (a v)
          * (∫ u in bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        + μ * (a v)
          * (volume (bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)).toReal)
        ≤ C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
          * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := habsμ
    nlinarith [h1, normB_nonneg (v := v) (μ := μ) (Φ : Submission.BoseGases.X n → ℝ)]
  have hkey : -(C₂ * (μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * (paramsAt μ (a v)).KB ^ 3
        * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ ∫ u in (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    linarith [hdecomp, hmono, hband, hnonneg_off, hstep]
  linarith [hsplit, hkey]

end

end Work.BoseFixB1C
