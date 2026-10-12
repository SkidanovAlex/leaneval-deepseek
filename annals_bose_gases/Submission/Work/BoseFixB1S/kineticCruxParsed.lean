import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BoseFixR.FamForm.symA_tail_fsParams
import Submission.Work.OneBodyKin.Phi_far_nonneg
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symA_zero_small
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
import Submission.Work.OneBodyKin.symD_second_order
import Submission.Work.SmallBoxOneBody.chiNormSq_ge_pi_div_48
import Submission.Work.UBBInputs8.A.abox_pair_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.kineticCruxParsed` — the sliding spectral crux with the payment **outside** the
`q`-integral

This file contains the proof of the intended statement (★) of `FINDING_crux_payment_shape.md`,

    ∫_u (2π)⁻³·bsW (fsKinCoeff c_sb) (χ_{B(u)}·(g − ⨍_{B(u)}g))
      ≤ ((2π)⁻³ ∫_q [ (1−ε_T)·fsKinCoeff ((2sℓ)⁻¹)‖q‖ + ε_T·fsKinCoeff ((2dsℓ)⁻¹)‖q‖ ]
              · ‖kinFT (χ_ℓ·(g − ⨍_{acube ℓ}g)) (q)‖² dq)
        + (bValue/(2ℓ²)) · ∫_{acube ℓ} (g − ⨍_{acube ℓ}g)²

**with explicit parentheses around the `q`-integral.**  This matters: Lean's integral notation
binds the whole trailing sum, so the *unparenthesised* text
`... ∫ q, body q + payment` parses as `... ∫ q, (body q + payment)`, and since the payment
`(bValue/(2ℓ²))·∫_{acube ℓ}(g − M)²` is a `q`-independent constant, that integral is the Bochner
integral of a non-integrable function (an integrable function plus a nonzero constant on the
infinite measure `ℝ³`), which is `0` (`MeasureTheory.integral_undef`).  Hence the unparenthesised
form asserts `LHS ≤ 0` for every `g` with `∫_{acube ℓ}(g−M)² > 0`, which is false (the left side is
a nonnegative cut word, strictly positive e.g. for `g(x) = cos ⟨k,x⟩` with `‖k‖ > c_sb`).
See `Submission/Work/BoseFixB1S/FINDING_crux_payment_shape.md` §4 for the same warning.

The proof is the *unprojected route* (`FINDING_unprojected_route_B.md`): the delegated inputs
`Work.BoseFixB1S.cruxCorrB1` (the intersection-mean correction, flat payment `bValue/(4ℓ²)`,
`CorrInput`), `Work.BoseFixB1S.cruxUnprojB1` (the `fsKinCoeff`-instance of the unprojected
family-form identity, `UnprojInput`) and `Work.BoseFixB1.KH.symA_fsParams` (the two-cut symbol
comparison, `MixInput`), plus the proved tail bound
`Work.BoseFixR.FamForm.symA_tail_fsParams`, `Work.SmallBoxOneBody.chiNormSq_ge_inv_sixteen`,
`Submission.BoseGases.chiScale_abs_le_sup`, `Work.BSKinetic.plancherel_pconv`.
-/

noncomputable section

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open scoped Real Topology ContDiff

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The residual inputs of the route -/

/-- **The correction input** (`Work.BoseFixB1S.cruxCorrB1`): replacing the *intersection*-box mean
of the sliding window by the *anchored* mean costs at most `(bValue/(4ℓ²))` times the anchored
mean-free mass. -/
def CorrInput (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g →
      ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ u : E3, Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (g z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, g z')))
        ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            (∫ u : E3, Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
              (fun z : E3 =>
                Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z')))
          + (Work.BoseBox.bValue / (4 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
              (∫ z in Submission.BoseGases.acube
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z') ^ 2)

/-- **The unprojected family-form input** (`Work.BoseFixB1S.cruxUnprojB1`, or the FS-cutoff
instance `Work.BoseFixB1.bsFamilyFormUnproj_fsKinCoeff` of the proved `L¹`-identity
`Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol` by monotone convergence). -/
def UnprojInput : Prop :=
  ∀ (a c : ℝ), 0 < a → 0 ≤ c → ∀ ψ : E3 → ℝ, ContDiff ℝ (⊤ : ENat) ψ →
    HasCompactSupport ψ →
      Work.BSKinetic.bsFamilyFormUnproj a (Submission.BoseGases.fsKinCoeff c) ψ
        ≤ ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ q : E3, Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff c) q *
              ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2

/-- **The two-cut symbol comparison at FS's parameters**
(`Work.BoseFixB1.KH.symA_fsParams` = `Work.BoseFixB1S.symAMix_fsParams`). -/
def MixInput (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ q : E3,
    Work.OneBodyKin.symA (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) q
      ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
          * Submission.BoseGases.fsKinCoeff
              ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * Submission.BoseGases.fsKinCoeff
              ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
        + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
          * Work.OneBodyKin.symA 1
              (Submission.BoseGases.fsKinCoeff
                ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0

/-! ## 2. Elementary identifications -/

/-- The product window `χ_{B(u)}` times a state is the *translated* window at scale `ℓd` applied
to the box-windowed state: `χ_{B(u)}·h = bsWin (ℓd) u · (χ_ℓ·h)`. -/
lemma chiB_mul_eq_bsWin_mul (ℓ d : ℝ) (u : E3) (h : E3 → ℝ) :
    (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * h z)
      = fun z : E3 => Work.BSKinetic.bsWin (ℓ * d) u z *
          (Submission.BoseGases.chiScale ℓ z * h z) := by
  funext z
  simp only [Submission.BoseGases.chiB, Work.BSKinetic.bsWin]
  ring

/-- `(2π)⁻³ · bsW F (bsWin a u · ψ) = bsOneBodyUnproj a F u ψ`: the two spellings of the
localised one-body kinetic form. -/
lemma twoPi_inv_bsW_bsWin_eq_bsOneBodyUnproj (a : ℝ) (F : ℝ → ℝ) (u : E3) (ψ : E3 → ℝ) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        Work.BSKinetic.Decomp.bsW F (fun z : E3 => Work.BSKinetic.bsWin a u z * ψ z)
      = Work.BSKinetic.bsOneBodyUnproj a F u ψ := by
  have hff : (fun z : E3 => ((Work.BSKinetic.bsWin a u z * ψ z : ℝ) : ℂ))
      = fun z : E3 => (Work.BSKinetic.bsWin a u z : ℂ) * (ψ z : ℂ) := by
    funext z
    exact Complex.ofReal_mul _ _
  simp only [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi,
    Work.BSKinetic.bsOneBodyUnproj, hff]

/-! ## 3. The assembly: the crux from the three inputs -/

theorem kineticCruxParsed_of_inputs {v : E3 → ℝ} (hcorr : CorrInput v)
    (hunproj : UnprojInput) (hmix : MixInput v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g →
      (∫ u : E3, ((2 * Real.pi) ^ 3)⁻¹ *
          Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (g z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, g z')))
        ≤ (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ q : E3,
              ((1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) *
                  Submission.BoseGases.fsKinCoeff
                    ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s *
                      Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
                + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT *
                  Submission.BoseGases.fsKinCoeff
                    ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d *
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s *
                      Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖) *
                ‖Submission.BoseGases.kinFT (fun z : E3 =>
                  ((Submission.BoseGases.chiScale
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z : ℝ) : ℂ) *
                    ((g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                      ∫ z' in Submission.BoseGases.acube
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z' : ℝ) : ℂ)) q‖ ^ 2)
          + (Work.BoseBox.bValue /
                (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
              ∫ z in Submission.BoseGases.acube
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z') ^ 2 := by
  obtain ⟨ε₁, hε₁, hC⟩ := hcorr
  obtain ⟨ε₂, hε₂, hM⟩ := hmix
  obtain ⟨ε₃, hε₃, hT⟩ := Work.BoseFixR.FamForm.symA_tail_fsParams (v := v)
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro μ hAdm g hg
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hℓpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hspos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
    Work.BoseFixB1.adm_s_pos hAdm
  obtain ⟨heT0, heT1⟩ := Work.BoseFixB1.adm_eT_bounds hAdm
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set ss : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set ee : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heedef
  set cc : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hccdef
  set hf : E3 → ℝ :=
    fun z : E3 => g z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, g z' with hfdef
  set ψ : E3 → ℝ := fun z : E3 => Submission.BoseGases.chiScale ℓ z * hf z with hψdef
  set w : E3 → ℝ :=
    fun q : E3 => ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2 with hwdef
  set Q₂ : ℝ := ∫ z in Submission.BoseGases.acube ℓ, (hf z) ^ 2 with hQdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact hℓpos
  have hd : 0 < dd := by rw [hddef]; exact hdpos
  have hs : 0 < ss := by rw [hsdef]; exact hspos
  have hee0 : 0 ≤ ee := by rw [heedef]; exact heT0
  have hee1 : ee ≤ 1 := by rw [heedef]; exact heT1
  have hcc0 : 0 ≤ cc := by
    rw [hccdef, Work.BoseFixB1.sbCut]
    exact inv_nonneg.mpr (by positivity)
  have hw_nonneg : ∀ q : E3, 0 ≤ w q := by
    intro q
    rw [hwdef]
    positivity
  -- smoothness and compact support of the windowed state
  have hhf_sm : ContDiff ℝ (⊤ : ENat) hf := by
    rw [hfdef]
    exact hg.sub contDiff_const
  have hψ_sm : ContDiff ℝ (⊤ : ENat) ψ := by
    rw [hψdef]
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).mul hhf_sm
  have hψ_cs : HasCompactSupport ψ := by
    rw [hψdef]
    exact (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_right
  -- (1) the correction
  have step1 : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z *
            (g z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, g z')))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
            (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z * hf z))
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ :=
    hC μ hAdm₁ g hg
  -- (2) the middle term is the unprojected family form of `ψ`
  have step2 : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z * hf z))
      = Work.BSKinetic.bsFamilyFormUnproj (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) ψ := by
    rw [Work.BSKinetic.bsFamilyFormUnproj, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
        (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z * hf z)
      = Work.BSKinetic.bsOneBodyUnproj (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) u ψ
    rw [chiB_mul_eq_bsWin_mul]
    exact twoPi_inv_bsW_bsWin_eq_bsOneBodyUnproj (ℓ * dd)
      (Submission.BoseGases.fsKinCoeff cc) u ψ
  -- (3) the unprojected family-form bound
  have hA : 0 < ℓ * dd := mul_pos hℓ hd
  have step3 : Work.BSKinetic.bsFamilyFormUnproj (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) ψ
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : E3, Work.OneBodyKin.symA (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q :=
    hunproj (ℓ * dd) cc hA hcc0 ψ hψ_sm hψ_cs
  -- (4) the pointwise two-cut symbol comparison, with the tail replaced by its bound
  have htail : ((ℓ * dd) ^ 2)⁻¹ * Work.OneBodyKin.symA 1
      (Submission.BoseGases.fsKinCoeff ((2 * ss)⁻¹)) 0 ≤ 1 / (4096 * ℓ ^ 2) := by
    have h := hT μ hAdm₃
    rw [← hℓdef, ← hddef, ← hsdef] at h
    have hrew : (1 / 4096) * (ℓ⁻¹) ^ 2 = 1 / (4096 * ℓ ^ 2) := by
      rw [inv_pow]
      ring
    rwa [hrew] at h
  have hsym_pt : ∀ q : E3,
      Work.OneBodyKin.symA (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q
        ≤ (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            + 1 / (4096 * ℓ ^ 2)) * w q := by
    intro q
    have hm := hM μ hAdm₂ q
    have hw0 : 0 ≤ w q := hw_nonneg q
    refine mul_le_mul_of_nonneg_right ?_ hw0
    refine le_trans hm ?_
    linarith [htail]
  -- (5) the integral comparison
  have hmix_nn : ∀ q : E3, 0 ≤ ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
      + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) := by
    intro q
    have h1 : 0 ≤ Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    have h2 : 0 ≤ Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖ :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    nlinarith [hee0, hee1, h1, h2]
  have hmix_le : ∀ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
      + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) ≤ ‖q‖ ^ 2 := by
    intro q
    have hp1 : (0 : ℝ) ≤ (2 * (ss * ℓ))⁻¹ := by positivity
    have hp2 : (0 : ℝ) ≤ (2 * (dd * ss * ℓ))⁻¹ := by positivity
    have h1 : Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖ ≤ ‖q‖ ^ 2 := by
      unfold Submission.BoseGases.fsKinCoeff
      exact pow_le_pow_left₀ (le_max_right _ _)
        (max_le (sub_le_self _ hp1) (norm_nonneg q)) 2
    have h2 : Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖ ≤ ‖q‖ ^ 2 := by
      unfold Submission.BoseGases.fsKinCoeff
      exact pow_le_pow_left₀ (le_max_right _ _)
        (max_le (sub_le_self _ hp2) (norm_nonneg q)) 2
    nlinarith [hee0, hee1, h1, h2]
  have hw_int_sq : MeasureTheory.Integrable (fun q : E3 => ‖q‖ ^ 2 * w q) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt ψ hψ_sm hψ_cs
  have hw_int : MeasureTheory.Integrable w :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψ_sm hψ_cs
  have hcont_fsKin : ∀ c : ℝ, Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
    intro c
    unfold Submission.BoseGases.fsKinCoeff
    exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
  have hcont_mix : Continuous (fun q : E3 =>
      (1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
        + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) := by
    refine Continuous.add ?_ ?_
    · exact continuous_const.mul ((hcont_fsKin _).comp continuous_norm)
    · exact continuous_const.mul ((hcont_fsKin _).comp continuous_norm)
  have hmixw_int : MeasureTheory.Integrable (fun q : E3 =>
      ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
        + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q) := by
    refine hw_int_sq.mono (hcont_mix.aestronglyMeasurable.mul hw_int.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hmix_nn q) (hw_nonneg q)),
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg ‖q‖) (hw_nonneg q))]
    exact mul_le_mul_of_nonneg_right (hmix_le q) (hw_nonneg q)
  have hbig_int : MeasureTheory.Integrable (fun q : E3 =>
      (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
        + 1 / (4096 * ℓ ^ 2)) * w q) := by
    have h : (fun q : E3 => (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
        + 1 / (4096 * ℓ ^ 2)) * w q)
      = fun q : E3 => ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q
        + (1 / (4096 * ℓ ^ 2)) * w q := by
      funext q
      ring
    rw [h]
    exact hmixw_int.add (hw_int.const_mul (1 / (4096 * ℓ ^ 2)))
  have hsym_int : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ q : E3, Work.OneBodyKin.symA (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            + 1 / (4096 * ℓ ^ 2)) * w q) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hint : MeasureTheory.Integrable (fun q : E3 =>
        Work.OneBodyKin.symA (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q)
    · exact MeasureTheory.integral_mono_ae hint hbig_int
        (Filter.Eventually.of_forall hsym_pt)
    · rw [MeasureTheory.integral_undef hint]
      refine le_trans (le_of_eq rfl) ?_
      refine MeasureTheory.integral_nonneg fun q => ?_
      exact mul_nonneg (add_nonneg (hmix_nn q) (by positivity)) (hw_nonneg q)
  -- (6) splitting the integral and Plancherel
  have hsplit : (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
        + 1 / (4096 * ℓ ^ 2)) * w q)
      = (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
            + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (1 / (4096 * ℓ ^ 2)) * (∫ q : E3, w q) := by
    have hfun : (fun q : E3 => (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
          + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
        + 1 / (4096 * ℓ ^ 2)) * w q)
        = fun q : E3 => ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
            + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q
          + (1 / (4096 * ℓ ^ 2)) * w q := by
      funext q; ring
    rw [hfun, MeasureTheory.integral_add hmixw_int (hw_int.const_mul _),
      MeasureTheory.integral_const_mul]
  have hsplit' : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
            + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
          + 1 / (4096 * ℓ ^ 2)) * w q)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (1 / (4096 * ℓ ^ 2)) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, w q)) := by
    rw [hsplit]
    ring
  have hpl : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, w q) = ∫ z : E3, (ψ z) ^ 2 := by
    rw [hwdef]
    exact Work.BSKinetic.plancherel_pconv ψ hψ_sm hψ_cs
  -- (7) the windowed mass is controlled by the anchored mass
  have hchiSup : Submission.BoseGases.chiSupAbs ^ 2 ≤ 16 := by
    have h1 : (1 : ℝ) / 16 ≤ Submission.BoseGases.chiNormSq :=
      Work.SmallBoxOneBody.chiNormSq_ge_inv_sixteen
    have hcn : 0 < Submission.BoseGases.chiNormSq := lt_of_lt_of_le (by norm_num) h1
    have hpos : 0 < Real.sqrt Submission.BoseGases.chiNormSq := Real.sqrt_pos.mpr hcn
    rw [Submission.BoseGases.chiSupAbs, inv_pow, Real.sq_sqrt hcn.le]
    rw [inv_le_comm₀ hcn (by norm_num : (0 : ℝ) < 16)]
    norm_num
    exact h1
  have hψ2_le : ∀ z : E3, (ψ z) ^ 2 ≤ 16 * (Submission.BoseGases.acube ℓ).indicator
      (fun z : E3 => (hf z) ^ 2) z := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz, hψdef]
      have hb : |Submission.BoseGases.chiScale ℓ z| ≤ Submission.BoseGases.chiSupAbs :=
        Submission.BoseGases.chiScale_abs_le_sup ℓ z
      have hb2 : (Submission.BoseGases.chiScale ℓ z) ^ 2 ≤ 16 := by
        rw [← sq_abs]
        exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hb 2) hchiSup
      nlinarith [hb2, sq_nonneg (hf z)]
    · rw [Set.indicator_of_notMem hz]
      have h0 : Submission.BoseGases.chiScale ℓ z = 0 := by
        by_contra hc
        exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hc)
      have hψz : ψ z = 0 := by
        show Submission.BoseGases.chiScale ℓ z * hf z = 0
        rw [h0, zero_mul]
      rw [hψz]
      norm_num
  have hcompact : IsCompact (Submission.BoseGases.acube ℓ) :=
    Work.UBBInputs8.A.isCompact_acube ℓ
  have hIndInt : MeasureTheory.Integrable (fun z : E3 =>
      (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (hf z) ^ 2) z) :=
    (MeasureTheory.integrable_indicator_iff hcompact.measurableSet).mpr <|
      ((hhf_sm.continuous.pow 2).continuousOn).integrableOn_compact (μ := MeasureTheory.volume)
        hcompact
  have hψL2 : (∫ z : E3, (ψ z) ^ 2) ≤ 16 * Q₂ := by
    have h1 : (∫ z : E3, (ψ z) ^ 2)
        ≤ ∫ z : E3, 16 * (Submission.BoseGases.acube ℓ).indicator (fun z : E3 => (hf z) ^ 2) z := by
      by_cases hint : MeasureTheory.Integrable (fun z : E3 => (ψ z) ^ 2)
      · refine MeasureTheory.integral_mono_ae hint (hIndInt.const_mul 16)
          (Filter.Eventually.of_forall hψ2_le)
      · rw [MeasureTheory.integral_undef hint]
        refine MeasureTheory.integral_nonneg fun z => ?_
        exact mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => sq_nonneg _) z)
    have h2 : (∫ z : E3, 16 * (Submission.BoseGases.acube ℓ).indicator
        (fun z : E3 => (hf z) ^ 2) z) = 16 * Q₂ := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator hcompact.measurableSet, hQdef]
    linarith [h1, h2.le]
  -- (8) the target's first term in the shape of `w`
  have hw_target : ∀ q : E3, w q = ‖Submission.BoseGases.kinFT (fun z : E3 =>
      ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * ((hf z : ℝ) : ℂ)) q‖ ^ 2 := by
    intro q
    have hfun : (fun z : E3 => (ψ z : ℂ))
        = fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) * ((hf z : ℝ) : ℂ) := by
      funext z
      rw [hψdef]
      exact Complex.ofReal_mul _ _
    show ‖Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) q‖ ^ 2 = _
    rw [hfun]
  have hw_target' : ∀ q : E3, w q = ‖Submission.BoseGases.kinFT (fun z : E3 =>
      ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) *
        ((g z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, g z' : ℝ) : ℂ)) q‖ ^ 2 := by
    intro q
    rw [hw_target q]
  -- (9) the arithmetic
  have hQ₂_nonneg : 0 ≤ Q₂ := by
    rw [hQdef]
    exact MeasureTheory.integral_nonneg fun z => sq_nonneg _
  have hnum : (1 / (4096 * ℓ ^ 2)) * (16 * Q₂)
      + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ ≤ (Work.BoseBox.bValue / (2 * ℓ ^ 2)) * Q₂ := by
    have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
    rw [Work.BoseBox.bValue]
    have hcoef : (1 / (4096 * ℓ ^ 2)) * 16 + ((1 : ℝ) / 16) / (4 * ℓ ^ 2)
        ≤ ((1 : ℝ) / 16) / (2 * ℓ ^ 2) := by
      have hA : (1 / (4096 * ℓ ^ 2)) * 16 = 1 / (256 * ℓ ^ 2) := by field_simp; ring
      have hB : ((1 : ℝ) / 16) / (4 * ℓ ^ 2) = 1 / (64 * ℓ ^ 2) := by field_simp; ring
      have hC : ((1 : ℝ) / 16) / (2 * ℓ ^ 2) = 1 / (32 * ℓ ^ 2) := by field_simp; ring
      have h1 : (1 : ℝ) / (256 * ℓ ^ 2) + 1 / (64 * ℓ ^ 2) = 5 / (256 * ℓ ^ 2) := by
        field_simp; ring
      have h2 : (1 : ℝ) / (32 * ℓ ^ 2) = 8 / (256 * ℓ ^ 2) := by field_simp; ring
      rw [hA, hB, hC, h1, h2]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    nlinarith [hcoef, hQ₂_nonneg]
  -- assembly
  calc (∫ u : E3, ((2 * Real.pi) ^ 3)⁻¹ *
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z *
            (g z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, g z')))
      = ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
          (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z *
            (g z - (1 / Work.SmallBoxSliding.boxMass ℓ dd u) *
              ∫ z' in Submission.BoseGases.dlBox ℓ dd u, g z'))) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ u : E3, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff cc)
            (fun z : E3 => Submission.BoseGases.chiB ℓ dd u z * hf z))
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := step1
    _ = Work.BSKinetic.bsFamilyFormUnproj (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) ψ
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by rw [step2]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, Work.OneBodyKin.symA (ℓ * dd) (Submission.BoseGases.fsKinCoeff cc) q * w q)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by linarith [step3]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, (((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            + 1 / (4096 * ℓ ^ 2)) * w q)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by linarith [hsym_int]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (1 / (4096 * ℓ ^ 2)) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, w q))
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by rw [hsplit']
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (1 / (4096 * ℓ ^ 2)) * (∫ z : E3, (ψ z) ^ 2)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by rw [hpl]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (1 / (4096 * ℓ ^ 2)) * (16 * Q₂)
        + (Work.BoseBox.bValue / (4 * ℓ ^ 2)) * Q₂ := by
        have h := mul_le_mul_of_nonneg_left hψL2 (by positivity : (0 : ℝ) ≤ 1 / (4096 * ℓ ^ 2))
        linarith [h]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖) * w q)
        + (Work.BoseBox.bValue / (2 * ℓ ^ 2)) * Q₂ := by linarith [hnum]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ q : E3, ((1 - ee) * Submission.BoseGases.fsKinCoeff ((2 * (ss * ℓ))⁻¹) ‖q‖
              + ee * Submission.BoseGases.fsKinCoeff ((2 * (dd * ss * ℓ))⁻¹) ‖q‖)
            * ‖Submission.BoseGases.kinFT (fun z : E3 =>
                ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) *
                  ((g z - (1 / ℓ ^ 3) * ∫ z' in Submission.BoseGases.acube ℓ, g z' : ℝ) : ℂ)) q‖ ^ 2)
        + (Work.BoseBox.bValue / (2 * ℓ ^ 2)) * Q₂ := by
        simp only [hw_target']

/-! ## 4. The inputs from the delegated pieces, and the corrected crux -/

-- The three inputs above are exactly the delegated pieces:
--   `CorrInput v`  = `Work.BoseFixB1S.cruxCorrB1`             (file
--                    `Submission/Work/BoseFixB1S/cruxCorrB1.lean`),
--   `UnprojInput`  = `Work.BoseFixB1S.cruxUnprojB1`             (`cruxUnprojB1.lean`), and
--   `MixInput v`   = `Work.BoseFixB1.KH.symA_fsParams`          (`BoseFixB1/KH/symA_fsParams.lean`).
-- They are deliberately *not* imported here: their import cones
-- (`Work.BoseFixR.FamForm.symA_Ftrunc_integral_tendsto` and the `BoseFixB1.KH` chapter) are the
-- pieces still being proved, and one of them is currently mid-edit in the shared workspace.  Once
-- they are green, the corrected crux is

--   theorem kineticCruxParsed {v : E3 → ℝ} (h : Work.UBB.ScatSol v) : <the statement above> :=
--     kineticCruxParsed_of_inputs (Work.BoseFixB1S.cruxCorrB1 h)
--       (fun a c ha hc ψ hψ hcs => Work.BoseFixB1S.cruxUnprojB1 ha hc hψ hcs)
--       (Work.BoseFixB1.KH.symA_fsParams (v := v))

end Work.BoseFixB1S
