import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.sgBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

/-
The three `sg`-rows (coefficient a star coefficient, slot the datum's `g`, `∂_θg`, `D_zg`).
All coefficient bounds needed are *pointwise* and already in `Rl1/tools.lean`:
`star_Rop_le : |Rop(Φ̃_*)| ≤ max Cs 0·α`, `star_Vop_le : |Vop(Φ̃_*)| ≤ max Cs 0·α`,
`star_KUop_le : |K θ·Uop(Φ̃_*)| ≤ 6 max Cs 0·α` (via `K_mul_Uop`), and
`Work.FTS.NonlinRows.Rl1.starUopBound : |Uop(Φ̃_*)| ≤ C·max Cs 0·α`.

Route: pull the constant out of the `∫⁻_θ` (`lintegral_const_mul'`) after the pointwise bound
`|K θ·N| ≤ (const)·K θ·|slot|` and estimate the slot against its energy `Phi0 g`/`Phi1 g`/`Phi2 g`
with `Work.FTS.NonlinRows.Rl1.lintegral_abs_le_sqrt` (for the `D_θg`-slot of `N2sg`, where the
`K`-weight cannot be kept) together with `inner_lintegral_le`, then the `r`-step
`Work.FTS.Nonlinear.Pieces.outer_of_inner` with `∫ w·Phi_j ≤ HkSq α 4 g` (from
`Work.FTS.NonlinRows.Rl1.slot0/1/2`).  For `N2sg` one may also use `starUopBound` and
`|K θ·∂_θg| = 3cos²θ·|D_θg| ≤ 3|D_θg|`.
Rates: `C·max Cs 0·α·Xn α g` for rows 1,2 and `C·max Cs 0·α²·Xn α g` for row 3; both fit
`K·Env α g` since `α ≤ √α`.
CAUTION: do NOT try to prove an `Xn`-level bound (`HkMem α 4 (N1sg) ∧ Xn α (N1sg) ≤ …`);
`NonlinRows/NRow10.lean` documents that this is impossible from `StarPkgo`.  The `Fa`-level
statement above is the correct, provable one (the coefficient estimate is pointwise).

## The route implemented here

`Fa` *is* the `rl¹`-density `∫⁻_r r⁻¹ (∫⁻_θ |K θ·N r θ|)`, and for a pointwise *factorisation*
`K θ·N = (K θ·A)·B` with `|K θ·A| ≤ C` the whole estimate is already available as the generic
engine `Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le` (proved, sorry-free):

  `∫⁻_r r⁻¹ (∫⁻_θ |K θ·A·B|) ≤ ofReal (C·√(π/2)·Xn α g)`,

which performs the angular Cauchy–Schwarz against `(∫⁻_θ B²)^{1/2}` and the radial one against
the weighted energy `∫_r w(r)·∫⁻_θ HkIntegrand α 4 g`.  The three slots `B = g, D_θg, D_zg` are
compared with the `ℋ⁴`-integrand by `PsgAux.slot_g/slot_dth/slot_dz`, and `|K θ·A| ≤ C` comes
from `star_Rop_le`, `starUopBound` and `star_Vop_le` together with `|K θ| ≤ 3` and the exact
identities `K θ / sin 2θ = (3/2)cos θ`, `pth g = D_θg / sin 2θ`.

The only primed ingredient beyond that engine is the pointwise bound on `𝒰(Φ̃_*)`
(`Work.FTS.NonlinRows.Rl1.starUopBound`).
-/
noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)
open Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Row `N₁^{sg} = 2ℛ(Φ̃_*)·g` -/

theorem row1sg_primed {α Cs : ℝ} {g Φs : Fn} (hα : 0 < α)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hgal : Work.FTS.Nonlin.GalClass α g) :
    Fa (Work.FTS.Nonlin.N1sg α Φs g)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contOn_of_smoothQuad hreg.1
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := star_Rop_le hα hs r hr θ hθ
    calc |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
        = 2 * |Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ ≤ 2 * 3 * (max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
            (abs_nonneg _) (by positivity)
      _ = 6 * max Cs 0 * α := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable (fun θ => ENNReal.ofReal ((g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_g hα hr hθ g)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α)
    (A := fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := g) (g := g) (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|
      = |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) * g r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N1sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Row `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θg` -/

/-- Row 2 with the pointwise bound on `𝒰(Φ̃_*)` exposed. -/
theorem row2sg_primed {α MU : ℝ} {g Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hMU : 0 ≤ MU)
    (hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ MU)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    Fa (Work.FTS.Nonlin.N2sg α Φs g)
      ≤ ENNReal.ofReal (3 * MU * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth g) from
        Work.FTS.LocData.SmoothQuad.DthIter hreg.1 1)
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Real.sin (2 * θ)) r θ| ≤ 3 * MU := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos hθ)
    have hU0 := hU r θ hr hθI
    have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
      rw [Work.Spaces.K, Real.sin_two_mul]
      ring
    have hratio : Work.Spaces.K θ / Real.sin (2 * θ) = (3 / 2) * Real.cos θ := by
      rw [hK]
      field_simp
    have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have habs : |Work.Spaces.K θ
          * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ))|
        = 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
      have hsplit : Work.Spaces.K θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
                / Real.sin (2 * θ))
          = (Work.Spaces.K θ / Real.sin (2 * θ))
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) := by ring
      rw [hsplit, hratio]
      rw [show (3 / 2 : ℝ) * Real.cos θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          = (-3) * (Real.cos θ
            * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
        abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_mul]
      ring
    rw [habs]
    have h1 : (3 / 2) * |Real.cos θ| ≤ (3 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hcos (by norm_num)
    calc 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 2 * ((3 / 2) * 1) * MU := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hU0
            (abs_nonneg _) ?_
          positivity
      _ = 3 * MU := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dth g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dth hα hr hθ g)
  have hE := rl1_slot_le (α := α) (C := 3 * MU)
    (A := fun z θ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Real.sin (2 * θ))
    (B := Work.Spaces.Dth g) (g := g) (mul_nonneg (by norm_num) hMU)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|
        = |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ)) * Work.Spaces.Dth g r θ| := by
    intro r θ hθ
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos hθ)
    rw [Work.FTS.Nonlin.N2sg]
    congr 1
    simp only [Work.Spaces.Dth]
    field_simp
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [ae_Iθ_of_forall_Ioo
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun θ hθ => hθ)] with θ hθ
  rw [hid r θ hθ]

/-! ## Row `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zg` -/

theorem row3sg_primed {α Cs : ℝ} {g Φs : Fn} (hα : 0 < α)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hgal : Work.FTS.Nonlin.GalClass α g) :
    Fa (Work.FTS.Nonlin.N3sg α Φs g)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α ^ 2 * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) from
        Work.FTS.LocData.SmoothQuad.DzIter hreg.1 1)
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α ^ 2 := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := star_Vop_le hα hs r hr θ hθ
    calc |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
        = 2 * α * |Work.Spaces.K θ|
            * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
          rw [show Work.Spaces.K θ
                * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
              = (-(2 * α)) * (Work.Spaces.K θ
                * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
            abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hα.le), abs_mul]
          ring
      _ ≤ 2 * α * 3 * (max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1
            (mul_nonneg (by norm_num) hα.le)) hb2 (abs_nonneg _) (by positivity)
      _ = 6 * max Cs 0 * α ^ 2 := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dz g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dz hα hr hθ g)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α ^ 2)
    (A := fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := Work.Spaces.Dz g) (g := g)
    (mul_nonneg (mul_nonneg (by norm_num) hCs0) (sq_nonneg α))
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|
      = |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          * Work.Spaces.Dz g r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N3sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Assembly -/

/-- `α ≤ √α` for `0 < α ≤ 1`. -/
theorem alpha_le_sqrt_primed {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ≤ Real.sqrt α := by
  have h : α ^ 2 ≤ α := by nlinarith
  calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
    _ ≤ Real.sqrt α := Real.sqrt_le_sqrt h

theorem sgBounds {Cs : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.StarPkgo α Cs Φs →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1sg α Φs g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2sg α Φs g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3sg α Φs g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CU, hCUpos, hCUb⟩ := starUopBound
  have hCU0 : 0 ≤ CU := hCUpos.le
  have hP0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMC0 : 0 ≤ max Cs 0 + max Cs 0 * CU := by
    have := mul_nonneg hM0 hCU0
    linarith
  set Kc : ℝ := 1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    nlinarith [hP0, hMC0]
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hbig : 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) ≤ Kc := by
    rw [hKcdef]; linarith
  have hcoef : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * Real.sqrt (Real.pi / 2) ≤ 12 * Real.sqrt (Real.pi / 2)
        * (max Cs 0 + max Cs 0 * CU) := by
    intro c _hc0 hcle
    calc c * Real.sqrt (Real.pi / 2)
        ≤ 12 * (max Cs 0 + max Cs 0 * CU) * Real.sqrt (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right hcle hP0
      _ = 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) := by ring
  have h6 : (6 : ℝ) * max Cs 0 ≤ 12 * (max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  have h3 : 3 * CU * max Cs 0 ≤ 12 * (max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  refine ⟨Kc, hKcpos, ?_⟩
  intro α g Φs hα hα1 hGal hStar
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hEnv0 : 0 ≤ Env α g := Env_nonneg g hα.le
  have hαX : α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
    have h1 : α * Work.FTS.Nonlin.Xn α g ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right (alpha_le_sqrt_primed hα hα1) hX0
    have h2 : Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
      rw [Env]
      have h3 : 0 ≤ α ^ 2 := sq_nonneg α
      have h4 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
      linarith
    exact h1.trans h2
  have hα2X : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
    have h1 : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ α * Work.FTS.Nonlin.Xn α g := by
      refine mul_le_mul_of_nonneg_right ?_ hX0
      nlinarith [hα.le, hα1]
    exact h1.trans hαX
  have keyA : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g ≤ Kc * Env α g := by
    intro c hc0 hcle
    have h1 := hcoef c hc0 hcle
    calc c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        = (c * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU))
            * (α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul h1 le_rfl (mul_nonneg hα.le hX0) (by positivity)
      _ ≤ Kc * Env α g := mul_le_mul hbig hαX (mul_nonneg hα.le hX0) hKc0
  have keyB : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g ≤ Kc * Env α g := by
    intro c hc0 hcle
    have h1 := hcoef c hc0 hcle
    calc c * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        = (c * Real.sqrt (Real.pi / 2)) * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU))
            * (α ^ 2 * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul h1 le_rfl (mul_nonneg (sq_nonneg α) hX0) (by positivity)
      _ ≤ Kc * Env α g := mul_le_mul hbig hα2X (mul_nonneg (sq_nonneg α) hX0) hKc0
  refine ⟨?_, ?_, ?_⟩
  · have h1 := row1sg_primed hα hStar hGal
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact keyA (6 * max Cs 0) (mul_nonneg (by norm_num) hM0) h6
  · have hMU : 0 ≤ CU * max Cs 0 * α := mul_nonneg (mul_nonneg hCU0 hM0) hα.le
    have hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
          ≤ CU * max Cs 0 * α :=
      fun z θ hz hθ => hCUb hα hα1 hStar z hz θ hθ
    have h1 := row2sg_primed hα hα1 hMU hU hGal
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show 3 * (CU * max Cs 0 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        = (3 * CU * max Cs 0) * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g from by ring]
    exact keyA (3 * CU * max Cs 0) (mul_nonneg (mul_nonneg (by norm_num) hCU0) hM0) h3
  · have h1 := row3sg_primed hα hStar hGal
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact keyB (6 * max Cs 0) (mul_nonneg (by norm_num) hM0) h6

end

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.ssBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.NonlinRows.Rl1

/-
The five `ss` rows (both factors are star/concrete, none of them is the datum `g`).
Route (unprimed sibling: `Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss` +
`Work.FTS.Nonlinear.Pieces.Rl1.EssBound`):

* `N1ss = 2ℛ(Φ̃_*)F_*` and `N3ss = -2α𝒱(Φ̃_*)D_zF_*`: `star_Rop_le`/`star_Vop_le` give
  `|ℛ(Φ̃_*)|,|𝒱(Φ̃_*)| ≤ max Cs 0·α`, the profiles are bounded pointwise
  (`Fstar_pt`, `DzFstar_pt`), so the pointwise bound is `C·max Cs 0·α²·r/(1+r)²` and
  `Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep` gives `Fa ≤ ofReal (4C)`.
* `N2ss = -2𝒰(Φ̃_*)∂_θF_*`: `StarPkgo` bounds `K θ·𝒰(Φ̃_*)` but never `𝒰(Φ̃_*)`, so the
  factor `K θ` is paired with `∂_θF_*` through the *profile* bound
  `|∂_θF_*| ≤ 20α|Γ'|·r/(1+r)²` and the angular bound `|K θ|·|Γ'| ≤ 2α`; the coefficient
  factor is bounded by the mean-value bound `Work.FTS.NonlinRows.Rl1.starUopBound`.  Then
  `rowStep`.
* `N4ss = -(1/2)sin2θ FK(F_*) ∂_θF_*`: `FK_Fstar_pt` gives `FK(F_*) = α·2r/(1+r)²` and the
  same `∂_θF_*`-pairing as row `N₂`, so `|K θ·N4ss| ≤ 40α³·r/(1+r)²`; `rowStep`.
* `N5ss = -sin²θ FK(F_*) F_*`: `|K θ·N5ss| ≤ 3·(α2r/(1+r)²)(20αr/(1+r)²) ≤ 120α²r/(1+r)²`;
  `rowStep`.

All five rates are `≤ C·α² ≤ C·Env α g` (since `α ≤ 1` and `Env ≥ α²`).

Everything is *pointwise*: no `HkMem`-type hypothesis is needed, only the pointwise
coefficient bounds of `StarPkgo` (`star_Rop_le`, `star_Vop_le`, `starUopBound`) with the
explicit profile bounds of `F_*`, and the generic `L₁₂`-step `rl1Pieces.rowStep`.
-/

/-- `K θ·|Γ'(θ)| ≤ 2α` on `Iθ` (this is what lets the factor `K θ` be paired with the
angular derivative of the profile instead of with the profile itself). -/
theorem ss_K_deriv_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ| * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
  rw [abs_of_nonneg (Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_nonneg hθ)]
  exact Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_deriv_le hα hθ

/-- `|∂_θF_*| ≤ 20α|Γ'|·r/(1+r)²` (`hKer`-free form of `Pss_pth_Fstar_le`). -/
theorem ss_abs_pth_Fstar_le {α r θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 ≤ r) :
    |Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * (r / (1 + r) ^ 2) := by
  have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_pth_Fstar_le α r θ hα hα1 hr
  rwa [Work.Spaces.hKer_apply] at h

/-- `|FK(F_*)(r)| = α·2r/(1+r)²`. -/
theorem ss_abs_FK_Fstar {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) :
    |Work.Construction.FK (Work.Construction.Fstar α) r| = α * (2 * (r / (1 + r) ^ 2)) := by
  rw [FK_Fstar_pt hα hα1, abs_of_nonneg (mul_nonneg hα.le (by positivity))]
  ring

/-- `r/(1+r)² ≤ 1` for `r > 0` (`hKer`-free form of `Pss_hKer_le_one`). -/
theorem ss_hker_le_one {r : ℝ} (hr : 0 < r) : r / (1 + r) ^ 2 ≤ 1 := by
  have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_hKer_le_one hr.le
  rwa [Work.Spaces.hKer_apply] at h

/-! ## The five pointwise bounds -/

/-- Row `N₁^{ss} = 2ℛ(Φ̃_*)F_*`. -/
theorem ss_N1_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1ss α Φs r θ|
        ≤ 120 * max Cs 0 * α ^ 2 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
  have h1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have h2 := star_Rop_le hα hs r hr0 θ hθ
  have h3 := Fstar_pt hα hα1 hr0 hθI
  have hb1 : (0 : ℝ) ≤ max Cs 0 * α := mul_nonneg hm hα.le
  have hb3 : (0 : ℝ) ≤ 20 * α * r / (1 + r) ^ 2 := by positivity
  show |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Construction.Fstar α r θ)| ≤ 120 * max Cs 0 * α ^ 2 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Construction.Fstar α r θ)|
      = (|Work.Spaces.K θ|
          * (2 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|))
          * |Work.Construction.Fstar α r θ| := by
        simp only [abs_mul]
        norm_num
        ring
    _ ≤ (3 * (2 * (max Cs 0 * α))) * (20 * α * r / (1 + r) ^ 2) := by
        refine mul_le_mul (mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
          (by positivity) (by norm_num)) h3 (abs_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hb1))
    _ = 120 * max Cs 0 * α ^ 2 * r / (1 + r) ^ 2 := by ring

/-- Row `N₂^{ss} = -2𝒰(Φ̃_*)∂_θF_*`. -/
theorem ss_N2_pt {α Cs MU : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hα1 : α ≤ 1) (hMU : 0 ≤ MU)
    (hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ MU) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2ss α Φs r θ|
        ≤ 80 * MU * α ^ 2 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hU0 := hU r θ hr0 hθI
  have hP := ss_abs_pth_Fstar_le (α := α) (r := r) (θ := θ) hα hα1 hr0.le
  have hKΓ := ss_K_deriv_le (α := α) (θ := θ) hα hθI
  show |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      ≤ 80 * MU * α ^ 2 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      = (|Work.Spaces.K θ|
          * (2 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|))
          * |Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
        simp only [abs_mul]
        norm_num
        ring
    _ ≤ (|Work.Spaces.K θ| * (2 * MU))
          * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ| * (r / (1 + r) ^ 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hU0 (by norm_num)) (abs_nonneg _)) hP
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hMU))
    _ = (2 * MU * (20 * α * (r / (1 + r) ^ 2)))
          * (|Work.Spaces.K θ| * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|) := by ring
    _ ≤ (2 * MU * (20 * α * (r / (1 + r) ^ 2))) * (2 * α) := by
        refine mul_le_mul_of_nonneg_left hKΓ ?_
        exact mul_nonneg (mul_nonneg (by norm_num) hMU) (by positivity)
    _ = 80 * MU * α ^ 2 * r / (1 + r) ^ 2 := by ring_nf

/-- Row `N₃^{ss} = -2α𝒱(Φ̃_*)D_zF_*`. -/
theorem ss_N3_pt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N3ss α Φs r θ|
        ≤ 120 * max Cs 0 * α ^ 3 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
  have h1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have hV := star_Vop_le hα hs r hr0 θ hθ
  have hDz := DzFstar_pt hα hα1 hr0 hθI
  have hb1 : (0 : ℝ) ≤ max Cs 0 * α := mul_nonneg hm hα.le
  have hb3 : (0 : ℝ) ≤ 20 * α * (r / (1 + r) ^ 2) := by positivity
  show |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      ≤ 120 * max Cs 0 * α ^ 3 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ)|
      = (|Work.Spaces.K θ|
          * (2 * α * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|))
          * |Work.Spaces.Dz (Work.Construction.Fstar α) r θ| := by
        simp only [abs_mul, abs_of_nonneg hα.le]
        ring
    _ ≤ (3 * (2 * α * (max Cs 0 * α))) * (20 * α * (r / (1 + r) ^ 2)) := by
        refine mul_le_mul (mul_le_mul h1 (mul_le_mul_of_nonneg_left hV (by positivity))
          (by positivity) (by norm_num)) hDz (abs_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hα.le)
            (mul_nonneg hm hα.le)))
    _ = 120 * max Cs 0 * α ^ 3 * r / (1 + r) ^ 2 := by ring_nf

/-- Row `N₄^{ss} = -(1/2)sin2θ FK(F_*) ∂_θF_*`. -/
theorem ss_N4_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4ss α r θ|
        ≤ 40 * α ^ 3 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hker0 : 0 ≤ r / (1 + r) ^ 2 := by positivity
  have hker1 : r / (1 + r) ^ 2 ≤ 1 := ss_hker_le_one hr0
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact abs_le.mpr ⟨Real.neg_one_le_sin (2 * θ), Real.sin_le_one (2 * θ)⟩
  have hFK := ss_abs_FK_Fstar (α := α) (r := r) hα hα1 hr0
  have hP := ss_abs_pth_Fstar_le (α := α) (r := r) (θ := θ) hα hα1 hr0.le
  have hKΓ := ss_K_deriv_le (α := α) (θ := θ) hα hθI
  show |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
      * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      ≤ 40 * α ^ 3 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-(1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ)|
      = (1 / 2) * |Work.Construction.s2 θ|
          * |Work.Construction.FK (Work.Construction.Fstar α) r|
          * (|Work.Spaces.K θ| * |Work.Spaces.pth (Work.Construction.Fstar α) r θ|) := by
        simp only [abs_mul]
        norm_num
        ring
    _ ≤ (1 / 2) * 1 * (α * (2 * (r / (1 + r) ^ 2)))
          * (|Work.Spaces.K θ|
            * (20 * α * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|
              * (r / (1 + r) ^ 2))) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hFK.le
          (abs_nonneg _) (by norm_num)) (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    _ = 20 * α ^ 2 * (r / (1 + r) ^ 2) * (r / (1 + r) ^ 2)
          * (|Work.Spaces.K θ| * |deriv (fun t : ℝ => Work.Spaces.Gam α t) θ|) := by ring
    _ ≤ 20 * α ^ 2 * (r / (1 + r) ^ 2) * (r / (1 + r) ^ 2) * (2 * α) := by
        refine mul_le_mul_of_nonneg_left hKΓ ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hker0) hker0
    _ ≤ 20 * α ^ 2 * (r / (1 + r) ^ 2) * 1 * (2 * α) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hker1
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hker0)
    _ = 40 * α ^ 3 * r / (1 + r) ^ 2 := by ring_nf

/-- Row `N₅^{ss} = -sin²θ FK(F_*) F_*`. -/
theorem ss_N5_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N5ss α r θ|
        ≤ 120 * α ^ 2 * r / (1 + r) ^ 2 := by
  intro r hr θ hθ
  have hr0 : 0 < r := hr
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hker0 : 0 ≤ r / (1 + r) ^ 2 := by positivity
  have hker1 : r / (1 + r) ^ 2 ≤ 1 := ss_hker_le_one hr0
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩)
    (Real.sin_le_one θ)
  have hFK := ss_abs_FK_Fstar (α := α) (r := r) hα hα1 hr0
  have hK := Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le hθI
  have hF := Fstar_pt hα hα1 hr0 hθI
  show |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
      * Work.Construction.FK (Work.Construction.Fstar α) r
      * Work.Construction.Fstar α r θ)| ≤ 120 * α ^ 2 * r / (1 + r) ^ 2
  calc |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) r
        * Work.Construction.Fstar α r θ)|
      = (Real.sin θ) ^ 2 * |Work.Construction.FK (Work.Construction.Fstar α) r|
          * (|Work.Spaces.K θ| * |Work.Construction.Fstar α r θ|) := by
        simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        ring
    _ ≤ 1 * (α * (2 * (r / (1 + r) ^ 2))) * (3 * (20 * α * r / (1 + r) ^ 2)) := by
        refine mul_le_mul (mul_le_mul hsin hFK.le (abs_nonneg _) (by norm_num))
          (mul_le_mul hK hF (abs_nonneg _) (by norm_num))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg (by norm_num) (mul_nonneg hα.le (by positivity)))
    _ = 120 * α ^ 2 * (r / (1 + r) ^ 2) * (r / (1 + r) ^ 2) := by ring_nf
    _ ≤ 120 * α ^ 2 * (r / (1 + r) ^ 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hker1
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) hker0)
    _ = 120 * α ^ 2 * r / (1 + r) ^ 2 := by ring_nf

/-- **The five `ss` rows.**  All five `L₁₂`-densities are bounded by `K·Env α g` with a
single `K` depending only on `Cs` (and on the universal constant of `starUopBound`). -/
theorem ssBounds {Cs : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.StarPkgo α Cs Φs →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CU, hCUpos, hCUb⟩ := starUopBound
  set Kc : ℝ := (3000 + 700 * CU) * max Cs 0 + (3000 + 700 * CU) with hKcdef
  have hm : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hCU0 : 0 ≤ CU := hCUpos.le
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : 0 < 3000 + 700 * CU := by linarith
    have h2 : 0 ≤ (3000 + 700 * CU) * max Cs 0 := mul_nonneg h1.le hm
    linarith
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hKc3000 : 3000 ≤ Kc := by
    rw [hKcdef]
    have h1 : 0 ≤ 3000 + 700 * CU := by linarith
    have h2 : 0 ≤ (3000 + 700 * CU) * max Cs 0 := mul_nonneg h1 hm
    linarith
  have hKc480 : 480 * max Cs 0 ≤ Kc := by
    rw [hKcdef]
    have h2 : 0 ≤ 3000 * max Cs 0 := mul_nonneg (by norm_num) hm
    have h3 : 0 ≤ 700 * CU * max Cs 0 := mul_nonneg (by linarith) hm
    have h4 : 0 ≤ 3000 + 700 * CU := by linarith
    nlinarith [h2, h3, h4]
  have hKc320 : 320 * CU * max Cs 0 ≤ Kc := by
    rw [hKcdef]
    have h3 : 0 ≤ 700 * CU * max Cs 0 := mul_nonneg (by linarith) hm
    have h4 : 0 ≤ 3000 + 700 * CU := by linarith
    have h5 : 0 ≤ 3000 * max Cs 0 := mul_nonneg (by norm_num) hm
    nlinarith [h3, h4, h5]
  refine ⟨Kc, hKcpos, ?_⟩
  intro α g Φs hα hα1 hGal hStar
  have hEnv : α ^ 2 ≤ Env α g := by
    rw [Env]
    have h1 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 g)
    have h2 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  have hα3 : α ^ 3 ≤ α ^ 2 :=
    pow_le_pow_of_le_one hα.le hα1 (show (2 : ℕ) ≤ 3 by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hC1 : 0 ≤ 120 * max Cs 0 * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N1ss α Φs) (C := 120 * max Cs 0 * α ^ 2) hC1
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N1_pt hα hα1 hStar r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal ((4 : ℝ) * (120 * max Cs 0 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (480 : ℝ) * max Cs 0 * α ^ 2 ≤ Kc * α ^ 2 :=
      mul_le_mul_of_nonneg_right hKc480 (sq_nonneg α)
    have h3 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h4 : (4 : ℝ) * (120 * max Cs 0 * α ^ 2) = 480 * max Cs 0 * α ^ 2 := by ring
    linarith
  · have hMU : 0 ≤ CU * max Cs 0 * α := mul_nonneg (mul_nonneg hCU0 hm) hα.le
    have hC2 : 0 ≤ 80 * (CU * max Cs 0 * α) * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hMU) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N2ss α Φs) (C := 80 * (CU * max Cs 0 * α) * α ^ 2) hC2
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N2_pt (Cs := Cs) hα hα1 hMU
          (fun z θ' hz hθ'I => hCUb hα hα1 hStar z hz θ' hθ'I) r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal ((4 : ℝ) * (80 * (CU * max Cs 0 * α) * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (320 : ℝ) * CU * max Cs 0 * α ^ 3 ≤ 320 * CU * max Cs 0 * α ^ 2 :=
      mul_le_mul_of_nonneg_left hα3 (mul_nonneg (mul_nonneg (by norm_num) hCU0) hm)
    have h3 : (320 : ℝ) * CU * max Cs 0 * α ^ 2 ≤ Kc * α ^ 2 :=
      mul_le_mul_of_nonneg_right hKc320 (sq_nonneg α)
    have h4 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h5 : (4 : ℝ) * (80 * (CU * max Cs 0 * α) * α ^ 2)
        = 320 * CU * max Cs 0 * α ^ 3 := by ring
    linarith
  · have hC3 : 0 ≤ 120 * max Cs 0 * α ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N3ss α Φs) (C := 120 * max Cs 0 * α ^ 3) hC3
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N3_pt hα hα1 hStar r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal ((4 : ℝ) * (120 * max Cs 0 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (480 : ℝ) * max Cs 0 * α ^ 3 ≤ 480 * max Cs 0 * α ^ 2 :=
      mul_le_mul_of_nonneg_left hα3 (mul_nonneg (by norm_num) hm)
    have h3 : (480 : ℝ) * max Cs 0 * α ^ 2 ≤ Kc * α ^ 2 :=
      mul_le_mul_of_nonneg_right hKc480 (sq_nonneg α)
    have h4 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h5 : (4 : ℝ) * (120 * max Cs 0 * α ^ 3) = 480 * max Cs 0 * α ^ 3 := by ring
    linarith
  · have hC4 : 0 ≤ 40 * α ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N4ss α) (C := 40 * α ^ 3) hC4
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N4_pt hα hα1 r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal ((4 : ℝ) * (40 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (160 : ℝ) * α ^ 3 ≤ 160 * α ^ 2 := by nlinarith [hα3, hα.le]
    have h3 : (160 : ℝ) * α ^ 2 ≤ Kc * α ^ 2 := by
      have h160 : (160 : ℝ) ≤ Kc := by linarith [hKc3000]
      exact mul_le_mul_of_nonneg_right h160 (sq_nonneg α)
    have h4 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h5 : (4 : ℝ) * (40 * α ^ 3) = 160 * α ^ 3 := by ring
    linarith
  · have hC5 : 0 ≤ 120 * α ^ 2 := mul_nonneg (by norm_num) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N5ss α) (C := 120 * α ^ 2) hC5
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ss_N5_pt hα hα1 r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal ((4 : ℝ) * (120 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (480 : ℝ) * α ^ 2 ≤ Kc * α ^ 2 := by
      have h480 : (480 : ℝ) ≤ Kc := by linarith [hKc3000]
      exact mul_le_mul_of_nonneg_right h480 (sq_nonneg α)
    have h3 : Kc * α ^ 2 ≤ Kc * Env α g := mul_le_mul_of_nonneg_left hEnv hKc0
    have h4 : (4 : ℝ) * (120 * α ^ 2) = 480 * α ^ 2 := by ring
    linarith

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.abs_DthIter_four_VsW_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)
open Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
  (abs_le_of_singular_ode dthIter_four_Rop_le pz_dthIter_four_pthU_le)

/-- `𝒱(Ψ) = ∂_θΨ - tan θ·Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothQuad_Vop {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := by
  have hpth : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth Ψ) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hsm)
  have htan : Work.FTS.LocData.SmoothQuad (fun _ θ : ℝ => Real.tan θ) := by
    refine Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry ?_
    have hfun : Function.uncurry (fun _ θ : ℝ => Real.tan θ)
        = fun p : ℝ × ℝ => Real.tan p.2 := rfl
    rw [hfun]
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin p.2)
        (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.contDiff_sin.comp contDiff_snd).contDiffOn
    have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.cos p.2)
        (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.contDiff_cos.comp contDiff_snd).contDiffOn
    have hrew : (fun p : ℝ × ℝ => Real.tan p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
      funext p
      exact Real.tan_eq_sin_div_cos p.2
    rw [hrew]
    exact hsin.div hcos (fun p hp => ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩))
  have hprod : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => Real.tan θ * Ψ z θ) :=
    Work.FTS.LocData.smoothQuad_mul htan hsm
  exact Work.FTS.LocData.smoothQuad_sub hpth hprod

/-- `D_z` commutes with the `D_θ`-iterates on the open quadrant, for `SmoothQuad` data. -/
theorem dz_dthIter_comm_smoothQuad {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (i : ℕ) : ∀ z θ, -1 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DthIter i (Work.Spaces.Dz g) z θ
        = Work.Spaces.Dz (Work.Spaces.DthIter i g) z θ := by
  induction i with
  | zero => intro z θ _ _; rfl
  | succ n ih =>
    intro z θ hz hθ
    have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter n g)) (z, θ) :=
      ((hsm.DthIter n).contDiffAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds (show (z, θ) ∈
          Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hz, hθ⟩))).of_le
        (by simp [Work.Stability.smoothOrder])
    have heq : (fun θ' => Work.Spaces.DthIter n (Work.Spaces.Dz g) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.Dz (Work.Spaces.DthIter n g) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ih z θ' hz hθ'
    have h1 : Work.Spaces.Dth (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
        = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter n g)) z θ := by
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]
    rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, h1,
      (Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter n g) hcd).symm]

/-- The `z`-slice of a `D_θ`-iterate of a `SmoothQuad` function is differentiable on the open
quadrant. -/
theorem differentiableAt_slice_z_DthIter {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (b : ℕ) {t θ : ℝ} (ht : -1 < t) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun s => Work.Spaces.DthIter b G s θ) t :=
  (((hG.DthIter b).curry_z hθ).differentiableOn
    Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds ht)

/-- The `z`-slice of `D_θ^b G - D_θ^b G(0,·)` with its honest `deriv`. -/
theorem hasDerivAt_slice_z_DthIter_sub {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (b : ℕ) {θ t : ℝ} (ht : -1 < t) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s => Work.Spaces.DthIter b G s θ - Work.Spaces.DthIter b G 0 θ)
      (deriv (fun s => Work.Spaces.DthIter b G s θ - Work.Spaces.DthIter b G 0 θ) t) t := by
  have hd : DifferentiableAt ℝ (fun s => Work.Spaces.DthIter b G s θ) t :=
    differentiableAt_slice_z_DthIter hG b ht hθ
  have h2 : deriv (fun s : ℝ => Work.Spaces.DthIter b G s θ - Work.Spaces.DthIter b G 0 θ) t
      = deriv (fun s : ℝ => Work.Spaces.DthIter b G s θ) t := by
    change deriv ((fun s : ℝ => Work.Spaces.DthIter b G s θ)
      - fun _ : ℝ => Work.Spaces.DthIter b G 0 θ) t = _
    rw [deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero]
  rw [h2]
  exact (hd.hasDerivAt.sub (hasDerivAt_const (c := Work.Spaces.DthIter b G 0 θ) t)).congr_deriv
    (by rw [sub_zero])

/-- **The `D_θ^4`-form of the row-19 identity.**  For `Ψ` smooth on the open quadrant and
`(z,θ)` in it,

  `α z ∂_z(D_θ^4 𝒱) + 2 D_θ^4 𝒱 + D_θ^4(∂_θ𝒰) + D_θ^4 ℛ = 0`,

where `𝒰 = Uop α Ψ`, `𝒱 = Vop Ψ`, `ℛ = Rop α Ψ`. -/
theorem dthIter4_ident {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad Ψ)
    {z θ : ℝ} (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    α * z * Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ)) z θ
      + 2 * Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) z θ
      + Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) z θ
      + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) z θ = 0 := by
  have hV : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := smoothQuad_Vop hsm
  have hU : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsm
  have hpthU : Work.FTS.LocData.SmoothQuad
      (Work.Spaces.pth (Work.Construction.Uop α Ψ)) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hU)
  have hR : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) :=
    Work.FTS.Nonlinear.Pieces.RNP.smoothQuad_Rop hsm
  have hDzV : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz (Work.Construction.Vop Ψ)) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Dz hV
  have h2V : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => 2 * Work.Construction.Vop Ψ z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul 2 hV
  have hαDzV : Work.FTS.LocData.SmoothQuad
      (fun z θ : ℝ => α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul α hDzV
  have hRG : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ =>
      Work.Construction.Rop α Ψ z θ + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) :=
    Work.FTS.LocData.smoothQuad_add hR hαDzV
  have hG : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ =>
      2 * Work.Construction.Vop Ψ z θ
        + (Work.Construction.Rop α Ψ z θ
            + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ)) :=
    Work.FTS.LocData.smoothQuad_add h2V hRG
  -- the combined function vanishes on the open quadrant
  have hzero_on : ∀ z' θ', -1 < z' → 0 < θ' → θ' < Real.pi / 2 →
      (fun z θ => Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
          + (2 * Work.Construction.Vop Ψ z θ
              + (Work.Construction.Rop α Ψ z θ
                  + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ))) z' θ'
        = (fun _ _ : ℝ => (0 : ℝ)) z' θ' := by
    intro z' θ' hz' h1 h2
    have h := pth_Uop_eq_neg (α := α) hsm hz' (show θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      from ⟨h1, h2⟩)
    show Work.Spaces.pth (Work.Construction.Uop α Ψ) z' θ'
        + (2 * Work.Construction.Vop Ψ z' θ'
            + (Work.Construction.Rop α Ψ z' θ'
                + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z' θ')) = 0
    rw [h]
    ring
  have hkey : Work.Spaces.DthIter 4 (fun z θ => Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      + (2 * Work.Construction.Vop Ψ z θ
          + (Work.Construction.Rop α Ψ z θ
              + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ))) z θ = 0 := by
    rw [DthIter_congr_Ioi hzero_on 4 z θ hz hθ.1 hθ.2, DthIter_zero_fun 4 z θ]
  -- linearity of `D_θ^4` on the two sums
  have hsplit1 : Work.Spaces.DthIter 4 (fun z θ => Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ
      + (2 * Work.Construction.Vop Ψ z θ
          + (Work.Construction.Rop α Ψ z θ
              + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ))) z θ
      = Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) z θ
        + Work.Spaces.DthIter 4 (fun z θ => 2 * Work.Construction.Vop Ψ z θ
            + (Work.Construction.Rop α Ψ z θ
                + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ)) z θ :=
    DthIter_add_smoothQuad hpthU hG 4 z θ hz hθ.1 hθ.2
  have hsplit2 : Work.Spaces.DthIter 4 (fun z θ => 2 * Work.Construction.Vop Ψ z θ
      + (Work.Construction.Rop α Ψ z θ
          + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ)) z θ
      = Work.Spaces.DthIter 4 (fun z θ : ℝ => 2 * Work.Construction.Vop Ψ z θ) z θ
        + Work.Spaces.DthIter 4 (fun z θ => Work.Construction.Rop α Ψ z θ
            + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ :=
    DthIter_add_smoothQuad h2V hRG 4 z θ hz hθ.1 hθ.2
  have hsplit3 : Work.Spaces.DthIter 4 (fun z θ => Work.Construction.Rop α Ψ z θ
      + α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ
      = Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) z θ
        + Work.Spaces.DthIter 4 (fun z θ : ℝ =>
            α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ :=
    DthIter_add_smoothQuad hR hαDzV 4 z θ hz hθ.1 hθ.2
  have hcm2 : Work.Spaces.DthIter 4 (fun z θ : ℝ => 2 * Work.Construction.Vop Ψ z θ) z θ
      = 2 * Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) z θ := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul 4 2 (Work.Construction.Vop Ψ)]
  have hcmα : Work.Spaces.DthIter 4 (fun z θ : ℝ =>
        α * Work.Spaces.Dz (Work.Construction.Vop Ψ) z θ) z θ
      = α * Work.Spaces.DthIter 4 (Work.Spaces.Dz (Work.Construction.Vop Ψ)) z θ := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul 4 α
      (Work.Spaces.Dz (Work.Construction.Vop Ψ))]
  have hcomm : Work.Spaces.DthIter 4 (Work.Spaces.Dz (Work.Construction.Vop Ψ)) z θ
      = z * Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ)) z θ := by
    have h' := dz_dthIter_comm_smoothQuad hV 4 z θ hz hθ
    rw [h']
    rfl
  rw [hsplit1, hsplit2, hsplit3, hcm2, hcmα, hcomm] at hkey
  linarith [hkey]

/-- Lagrange mean-value bound in `z` on `[0,z]`: if `h` is continuous on `[0,z]`,
differentiable on `(0,z)` with `|h'| ≤ K` there, then `|h t - h 0| ≤ K t` for every
`t ∈ [0,z]`. -/
theorem abs_sub_le_mul_of_deriv_bound_Icc {h : ℝ → ℝ} {K z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn h (Set.Icc 0 z))
    (hdiff : ∀ t ∈ Set.Ioo 0 z, HasDerivAt h (deriv h t) t)
    (hK : ∀ t ∈ Set.Ioo 0 z, |deriv h t| ≤ K) :
    ∀ t ∈ Set.Icc 0 z, |h t - h 0| ≤ K * t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · rw [← h0, sub_self, abs_zero, mul_zero]
  · have hcont_t : ContinuousOn h (Set.Icc 0 t) := hcont.mono (Set.Icc_subset_Icc le_rfl ht.2)
    have hdiff_t : DifferentiableOn ℝ h (Set.Ioo 0 t) := fun x hx =>
      (hdiff x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope h hpos hcont_t hdiff_t
    have hcI : c ∈ Set.Ioo (0 : ℝ) z := ⟨hc.1, lt_of_lt_of_le hc.2 ht.2⟩
    have h1 : h t - h 0 = (t - 0) * deriv h c := by
      rw [hcd]; field_simp
    rw [h1, sub_zero, abs_mul, abs_of_pos hpos]
    calc t * |deriv h c| ≤ t * K := mul_le_mul_of_nonneg_left (hK c hcI) (le_of_lt hpos)
      _ = K * t := by ring

/-- A continuous function at `0` which is dominated by `C t` on `(0,1)` vanishes at `0`. -/
theorem eq_zero_of_continuousAt_of_abs_le {k : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hcont : ContinuousAt k 0) (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |k t| ≤ C * t) :
    k 0 = 0 := by
  have h1 : Filter.Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 (k 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (f := k) (a := fun t : ℝ => C * t) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
        with t ht hlt
      rw [Real.norm_eq_abs]
      exact h t hlt
    · have hc : Filter.Tendsto (fun t : ℝ => C * t) (𝓝 (0 : ℝ)) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto
      simpa using hc.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h1 h2

/-- **The singular-ODE step, abstractly.**  For `Ψ` smooth on the open quadrant, a point
`(z,θ)` with `z > 0`, and a constant `C ≥ 0` bounding the `(k=1,j=4)`-slot of `∂_θ𝒰` and the
`(k=0,j=4)`-slot of `ℛ` (by `C` and `C·t` respectively), the `z`-difference of `D_θ^4 𝒱`
is at most `2 C z`. -/
theorem dthIter_four_Vop_sub_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad Ψ) {z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {C : ℝ} (hC : 0 ≤ C)
    (hU_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) z, |deriv (fun s : ℝ =>
      Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) s θ) t| ≤ C)
    (hR_bound : ∀ t : ℝ, 0 < t →
      |Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ| ≤ C * t) :
    |Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) z θ
      - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ| ≤ 2 * C * z := by
  have hVsm : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop Ψ) := smoothQuad_Vop hsm
  have hSmU : Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Construction.Uop α Ψ)) :=
    Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU
        (Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsm))
  have hSmR : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) :=
    Work.FTS.Nonlinear.Pieces.RNP.smoothQuad_Rop hsm
  -- continuity of the slices on `[0,z]`
  have hcont_U : ContinuousOn (fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ) (Set.Icc 0 z) :=
    ((hSmU.DthIter 4).curry_z hθ).continuousOn.mono
      (fun t ht => Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hcont_R : ContinuousOn (fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Construction.Rop α Ψ) t θ) (Set.Icc 0 z) :=
    ((hSmR.DthIter 4).curry_z hθ).continuousOn.mono
      (fun t ht => Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hcont_u : ContinuousOn (fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Construction.Vop Ψ) t θ - Work.Spaces.DthIter 4
        (Work.Construction.Vop Ψ) 0 θ) (Set.Icc 0 z) :=
    (((hVsm.DthIter 4).curry_z hθ).continuousOn.mono
      (fun t ht => Set.mem_Ioi.mpr (by linarith [ht.1]))).sub continuousOn_const
  have hcont_W : ContinuousOn (fun t : ℝ => (Work.Spaces.DthIter 4
        (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
      - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)) (Set.Icc 0 z) :=
    (hcont_U.add hcont_R).sub continuousOn_const
  -- `D_θ^4 ℛ(0,·) = 0` (continuity plus the `t`-weight of the field)
  have hR_zero : Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ = 0 := by
    refine eq_zero_of_continuousAt_of_abs_le (k := fun t : ℝ => Work.Spaces.DthIter 4
      (Work.Construction.Rop α Ψ) t θ) hC ?_ ?_
    · exact ((hSmR.DthIter 4).curry_z hθ).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0))
    · intro t ht
      exact hR_bound t ht.1
  -- the source is `≤ 2 C t`
  have hW_bound : ∀ t ∈ Set.Icc 0 z, |(Work.Spaces.DthIter 4
        (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
      - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
        + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)| ≤ (2 * C) * t := by
    intro t ht
    have hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) z, HasDerivAt (fun u : ℝ => Work.Spaces.DthIter 4
        (Work.Spaces.pth (Work.Construction.Uop α Ψ)) u θ)
        (deriv (fun u : ℝ => Work.Spaces.DthIter 4
          (Work.Spaces.pth (Work.Construction.Uop α Ψ)) u θ) s) s :=
      fun s hs => (differentiableAt_slice_z_DthIter (hSmU.DthIter 4) 0
        (by linarith [hs.1]) hθ).hasDerivAt
    have hU_piece := abs_sub_le_mul_of_deriv_bound_Icc hz hcont_U hdiff hU_deriv t ht
    have hR_piece : |Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
        - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ| ≤ C * t := by
      rw [hR_zero, sub_zero]
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · rw [← h0, hR_zero]
        simp
      · exact hR_bound t hpos
    have hAB : (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
        - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)
        = (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
            - Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ)
          + (Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
            - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ) := by ring
    rw [hAB]
    calc |(Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
            - Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ)
          + (Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
            - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)|
        ≤ |Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
              - Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ|
            + |Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ
              - Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ| := abs_add_le _ _
      _ ≤ C * t + C * t := add_le_add hU_piece hR_piece
      _ = (2 * C) * t := by ring
  -- the singular ODE
  have hode : ∀ t ∈ Set.Ioo (0 : ℝ) z,
      α * t * deriv (fun s : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) s θ
          - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ) t
        + 2 * (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) t θ
          - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ)
        + ((Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
            + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
          - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
            + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ)) = 0 := by
    intro t ht
    have ht_quad : -1 < t := by linarith [ht.1]
    have hd : DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.DthIter 4
        (Work.Construction.Vop Ψ) s θ) t :=
      differentiableAt_slice_z_DthIter (hVsm.DthIter 4) 0 ht_quad hθ
    have h_g : deriv (fun s : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) s θ
        - Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ) t
        = Work.Spaces.pz (Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ)) t θ := by
      change deriv ((fun s : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) s θ)
        - fun _ : ℝ => Work.Spaces.DthIter 4 (Work.Construction.Vop Ψ) 0 θ) t = _
      rw [deriv_sub hd (differentiableAt_const _), deriv_const, sub_zero]
      rfl
    have h1 := dthIter4_ident (α := α) hsm ht_quad hθ
    have h2 := dthIter4_ident (α := α) hsm (show (-1 : ℝ) < 0 by norm_num) hθ
    simp only [mul_zero, zero_mul, zero_add, add_zero] at h2
    rw [h_g]
    linarith [h1, h2]
  have hbound := abs_le_of_singular_ode (u := fun t : ℝ => Work.Spaces.DthIter 4
        (Work.Construction.Vop Ψ) t θ - Work.Spaces.DthIter 4
          (Work.Construction.Vop Ψ) 0 θ)
      (W := fun t : ℝ => (Work.Spaces.DthIter 4
            (Work.Spaces.pth (Work.Construction.Uop α Ψ)) t θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) t θ)
        - (Work.Spaces.DthIter 4 (Work.Spaces.pth (Work.Construction.Uop α Ψ)) 0 θ
          + Work.Spaces.DthIter 4 (Work.Construction.Rop α Ψ) 0 θ))
      (C := 2 * C) hα hz (by positivity) hcont_u
      (fun t ht => hasDerivAt_slice_z_DthIter_sub hVsm 4 (by linarith [ht.1]) hθ)
      hode hcont_W hW_bound (by ring)
  exact hbound

/-- **The core estimate for `0 < z < 1`.** -/
theorem dthIter_four_VsW_le_near {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Set.Ioo (0 : ℝ) 1, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) < z := hz.1
  have hΨ : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hs.smooth
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hL0 : 0 ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_nonneg hM0 hΛ0
  have hU_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) z, |deriv (fun s : ℝ => Work.Spaces.DthIter 4
      (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) s θ) t|
      ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro t ht
    have htI : t ∈ Work.Spaces.Iz := le_of_lt ht.1
    have h := pz_dthIter_four_pthU_le (α := α) (Cs := Cs) (Φs := Φs) hα hs t htI θ hθI
    have ht1 : (0 : ℝ) < 1 + t := by linarith [ht.1]
    have hdiv : max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        / (1 + t) ≤ max Cs 0 * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      rw [div_le_iff₀ ht1]
      simpa using mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + t by linarith [ht.1]) hL0
    simpa only [Work.Spaces.pz] using h.trans hdiv
  have hR_bound : ∀ t : ℝ, 0 < t → |Work.Spaces.DthIter 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) t θ|
      ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * t := by
    intro t ht
    have h := dthIter_four_Rop_le (α := α) (Cs := Cs) (Φs := Φs) hα hs t ht θ hθI
    have ht1 : (0 : ℝ) < 1 + t := by linarith
    have hfac : t / (1 + t) ≤ t := by
      rw [div_le_iff₀ ht1]; nlinarith [ht]
    calc |Work.Spaces.DthIter 4 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) t θ|
        ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * (t / (1 + t)) := h
      _ ≤ max Cs 0 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * t :=
          mul_le_mul_of_nonneg_left hfac hL0
  have hmain := dthIter_four_Vop_sub_le (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) hΨ
    hα hz0 hθ hL0 hU_deriv hR_bound
  have heq : Work.Spaces.DthIter 4 (VsW α Φs) z θ
      = Work.Spaces.DthIter 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) z θ
        - Work.Spaces.DthIter 4
            (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) 0 θ :=
    DthIter_VsW_eq hα hs 4 z θ (by linarith [hz0]) hθ.1 hθ.2
  rw [heq]
  exact hmain.trans_eq (by ring_nf)

/-- **Row 19, the missing order.**  For a frozen `StarPkg α Cs Φs` and `0 < α ≤ 1`, the
`(k = 0, j = 4)`-slot of the `θ`-derivative of the split `VsW = 𝒱(Φ̃_*) - 𝒱(Φ̃_*)(0,·)` is
controlled by `(max Cs 0 · α)·((α + sin 2θ) sin(2θ)^{α/5})·min z 1`. -/
theorem abs_DthIter_four_VsW_le : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter 4 (Work.FTS.Nonlinear.Pieces.RNP.row19.VsW α Φs) z θ|
        ≤ C * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  refine ⟨2, by norm_num, ?_⟩
  intro α Cs Φs hs hα hα1 z hz θ hθ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, DthIter_VsW_zero]
    have hne : α / 5 ≠ 0 := ne_of_gt (by linarith)
    simp [Real.zero_rpow hne]
  by_cases hz1 : z < 1
  · have hnear := dthIter_four_VsW_le_near (α := α) (Cs := Cs) (Φs := Φs) hα hα1 hs
      z ⟨hzpos, hz1⟩ θ hθ
    rw [min_eq_left (le_of_lt hz1)]
    calc |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := hnear
      _ = 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * z := by ring
  · have hz1' : 1 ≤ z := le_of_not_gt hz1
    have hgl := abs_DthIter_VsW_le (α := α) (Cs := Cs) (Φs := Φs) hα hs 4
      (by norm_num) (by norm_num) z hz θ ⟨hθ.1.le, hθ.2.le⟩
    rw [min_eq_right hz1']
    calc |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
        ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := hgl
      _ = 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * 1 := by ring

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.EVDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The coefficients and the coefficient bundle -/

/-- The angular coefficient `cos²θ − 2 sin²θ` of `EVz`. -/
def EVphi : ℝ → ℝ → ℝ := fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2

/-- The angular coefficient `sin 2θ` of `EVz`. -/
def EVsin : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- The radial coefficient `z/(1+z)` of `EV`. -/
def EVrho : ℝ → ℝ → ℝ := fun z _ => z / (1 + z)

/-- The constant of the `Fb`-bounds of `EVz` and `EV`. -/
def EVC : ℝ := 4096

/-- **The coefficient data of `EVz` and `EV`.**  `EVCoef A` collects everything the flat
product calculus needs to bound `EVz Y` and `EV Y`: the flat bounds (`F0 6 A`) of the three
coefficient functions and of `cos 2θ`, the smoothness of the coefficients and of the two
angular derivatives, and the three pointwise derivative identities. -/
structure EVCoef (A : ℝ) : Prop where
  /-- `cos²θ − 2 sin²θ` is `C^∞` on the open quadrant -/
  smoothPhi : EllipticEst.SmoothOpen EVphi
  /-- `sin 2θ` is `C^∞` on the open quadrant -/
  smoothSin : EllipticEst.SmoothOpen EVsin
  /-- `z/(1+z)` is `C^∞` on the open quadrant -/
  smoothRho : EllipticEst.SmoothOpen EVrho
  /-- `cos 2θ` is `C^∞` on the open quadrant -/
  smoothCos2 : EllipticEst.SmoothOpen (fun _ θ => Real.cos (2 * θ))
  /-- `∂_θ(cos²θ − 2 sin²θ)` is `C^∞` on the open quadrant -/
  smoothDPhi : EllipticEst.SmoothOpen (Work.Spaces.pth EVphi)
  /-- `∂_θ(sin 2θ)` is `C^∞` on the open quadrant -/
  smoothDSin : EllipticEst.SmoothOpen (Work.Spaces.pth EVsin)
  /-- flat bound for `cos²θ − 2 sin²θ` -/
  f0Phi : F0 6 A EVphi
  /-- flat bound for `sin 2θ` -/
  f0Sin : F0 6 A EVsin
  /-- flat bound for `z/(1+z)` -/
  f0Rho : F0 6 A EVrho
  /-- flat bound for `cos 2θ` -/
  f0Cos2 : F0 6 A (fun _ θ => Real.cos (2 * θ))
  /-- `∂_θ(cos²θ − 2 sin²θ) = −3 sin 2θ` -/
  dPhi : ∀ z θ : ℝ, Work.Spaces.pth EVphi z θ = -3 * Real.sin (2 * θ)
  /-- `∂_θ(sin 2θ) = 2 cos 2θ` -/
  dSin : ∀ z θ : ℝ, Work.Spaces.pth EVsin z θ = 2 * Real.cos (2 * θ)
  /-- `∂_θ(z/(1+z)) = 0` -/
  dRho : ∀ z θ : ℝ, Work.Spaces.pth EVrho z θ = 0

/-! ## `SmoothOpen` closure -/

theorem SmoothOpen.const_mul {f : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f) (c : ℝ) :
    EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  simpa only [EllipticEst.SmoothOpen, h] using (contDiffOn_const.mul hf)

theorem SmoothOpen.add {f g : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f)
    (hg : EllipticEst.SmoothOpen g) :
    EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  simpa only [EllipticEst.SmoothOpen, h] using hf.add hg

theorem SmoothOpen.congr {f g : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    EllipticEst.SmoothOpen g := by
  refine (EllipticEst.smoothOpen_iff_forall g).mpr fun n => ?_
  refine ((EllipticEst.smoothOpen_iff_forall f).mp hf n).congr ?_
  intro p hp
  obtain ⟨hz, hθ, hθ'⟩ := EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ hθ').symm

theorem SmoothOpen.const (c : ℝ) : EllipticEst.SmoothOpen (fun _ _ : ℝ => c) := by
  have h : Function.uncurry (fun _ _ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  simpa only [EllipticEst.SmoothOpen, h] using contDiffOn_const

/-! ## Scalar multiples in the flat class -/

theorem pzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field c

theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.DthIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field c]
    ring

theorem F0_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ) (hf : F0 n K f) :
    F0 n (|c| * K) (fun z θ => c * f z θ) := by
  intro k i hki z θ hz hθ hθ'
  rw [DthIter_const_mul c f i, pzIter_const_mul c (Work.Spaces.DthIter i f) k]
  have h : (z + 1) ^ k * (c * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ)
      = c * ((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ) := by ring
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_left (hf k i hki z θ hz hθ hθ') (abs_nonneg c)

/-! ## `D_θ` raises the angular order by one -/

theorem DthIter_Dth (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (Work.Spaces.Dth g) = Work.Spaces.DthIter (i + 1) g := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ (n := n) (f := Work.Spaces.Dth g), ih,
      Work.Spaces.DthIter_succ (n := n + 1) (f := g)]

/-- `D_θ` is one more angular derivative: `F0 (n+1) K f` gives `F0 n K (D_θ f)`. -/
theorem F0_Dth {n : ℕ} {K : ℝ} {g : ℝ → ℝ → ℝ} (h : F0 (n + 1) K g) :
    F0 n K (Work.Spaces.Dth g) := by
  intro k i hki z θ hz hθ hθ'
  have h' := h k (i + 1) (by omega) z θ hz hθ hθ'
  rwa [← DthIter_Dth i g] at h'

/-! ## Locality and linearity of `∂_θ` on the open quadrant -/

theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

theorem pth_add_Q0 {f g : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f)
    (hg : EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
    ((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
    ((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hff : (fun θ' : ℝ => f z θ' + g z θ')
      = (fun θ' : ℝ => f z θ') + (fun θ' : ℝ => g z θ') := by
    funext θ'; rfl
  simp only [Work.Spaces.pth]
  rw [hff]
  exact deriv_add hd1 hd2

theorem pth_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real Topology
open Filter

/-! ## Two elementary closure facts -/

/-- `SmoothOpen` is closed under pointwise multiplication. -/
theorem Fbq_smoothOpen_mul {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [hfun]
  exact hf.mul hg

/-- `F0 n K f` forces `0 ≤ K`: evaluate the bound at the point `(1, π/4)` of the open
quadrant (`k = i = 0`). -/
theorem Fbq_nonneg_of_F0 {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (h : F0 n K f) : 0 ≤ K := by
  have h0 := h 0 0 (Nat.zero_le n) 1 (Real.pi / 4) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h0' : |f 1 (Real.pi / 4)| ≤ K := by
    simpa only [Work.Spaces.pzIter_zero, Work.Spaces.DthIter_zero, pow_zero, one_mul] using h0
  exact le_trans (abs_nonneg _) h0'

/-! ## Locality: the iterated operators depend only on the values on an open set

All three lemmas below are stated for data agreeing merely *pointwise on the open quadrant*
(no smoothness): every iterate of `∂_z`, `D_θ = sin(2·)∂_θ` is built from `deriv`, which is
local, and the quadrant is open (and its `θ`-slices `(0,π/2)` and `z`-slices `(0,∞)` are open
neighbourhoods of the relevant point). -/

/-- `∂_z^k` is local on the open quadrant. -/
theorem Fbq_pzIter_congr {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (k : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k F z θ = Work.Spaces.pzIter k G z θ := by
  induction k with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.pzIter n F z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      exact heq.deriv_eq

/-- `D_θ^i` is local on the open quadrant. -/
theorem Fbq_DthIter_congr {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-- **`F0` is local**: two functions agreeing on the open quadrant are in the same flat class. -/
theorem Fbq_F0_congr {n : ℕ} {K : ℝ} {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ)
    (hG : F0 n K G) : F0 n K F := by
  intro k i hki z θ hz h1 h2
  have hcongr := Fbq_pzIter_congr
    (F := Work.Spaces.DthIter i F) (G := Work.Spaces.DthIter i G)
    (fun z θ hz h1 h2 => Fbq_DthIter_congr h i z θ hz h1 h2) k z θ hz h1 h2
  rw [hcongr]
  exact hG k i hki z θ hz h1 h2

/-! ## The product rule for `∂_θ` on the open quadrant -/

/-- **The product rule for `∂_θ`**: for data which are `C^∞` on the open quadrant, the partial
`θ`-derivative of the pointwise product is the sum of the products. -/
theorem Fbq_pth_mul {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ * g z θ) z θ
        = Work.Spaces.pth f z θ * g z θ + f z θ * Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    ((hsf.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    ((hsg.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  show deriv (fun θ' => f z θ' * g z θ') θ
      = deriv (fun θ' => f z θ') θ * g z θ + f z θ * deriv (fun θ' => g z θ') θ
  rw [show (fun θ' => f z θ' * g z θ') = (fun θ' => f z θ') * (fun θ' => g z θ') from rfl]
  exact deriv_mul hd1 hd2

/-! ## The main theorem -/


end Work.FTS.PhiStar.CoreAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The angular derivative of `z ∂_z f`**, on the open quadrant, for a datum smooth there:

`∂_θ (z ∂_z f) = z · ∂_z (∂_θ f)`.

The `z` factors out of `deriv` (`deriv_const_mul`), and the remaining identity
`∂_θ ∂_z f = ∂_z ∂_θ f` is Clairaut's theorem (`Work.Spaces.pz_pth_comm`), applicable at
`(z,θ) ∈ Q0` because `SmoothOpen f` in particular makes `uncurry f` `C²` near that point. -/
theorem pth_zpz_smoothOpen {f : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => z * Work.Spaces.pz f z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := by
  intro z θ hz hθ hθ'
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsf 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hcomm : Work.Spaces.pth (Work.Spaces.pz f) z θ
      = Work.Spaces.pz (Work.Spaces.pth f) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  calc Work.Spaces.pth (fun z θ => z * Work.Spaces.pz f z θ) z θ
      = deriv (fun θ' => z * Work.Spaces.pz f z θ') θ := rfl
    _ = z * deriv (fun θ' => Work.Spaces.pz f z θ') θ := deriv_const_mul_field z
    _ = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := by rw [hcomm]

theorem Fb_zpz {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.Fb (n + 1) K f) : Work.FTS.PhiStar.Fb n (((n : ℝ) + 1) * K) (fun z θ => z * Work.Spaces.pz f z θ) := by
  refine ⟨F0_zpz hK hsf hf.f0, ?_⟩
  refine F0_congr (pth_zpz_smoothOpen hsf) ?_
  exact F0_zpz hK hsf.pth hf.fd

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.fields_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Closure of `SmoothOpen` under the pointwise operations

The curried forms of `ContDiffOn.add`, `ContDiffOn.sub`, `ContDiffOn.mul` and
`ContDiffOn.div`. -/

private theorem soMul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact hf.mul hg

private theorem soAdd {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact hf.add hg

private theorem soSub {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact hf.sub hg

/-- Division is legitimate on `Q0` as soon as the denominator does not vanish there. -/
private theorem soDiv {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hne : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ ≠ 0) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ / g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  refine hf.div hg ?_
  intro p hp
  obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact hne p.1 p.2 hz hθ hθ'

private theorem soConstMul (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-- A function of `θ` alone, globally `C^∞` on `ℝ`, is `C^∞` on the open quadrant. -/
private theorem soThetaOnly {a : ℝ → ℝ} (ha : ContDiff ℝ Work.Stability.smoothOrder a) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => a θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2) _
  exact (ha.comp contDiff_snd).contDiffOn

/-- `SmoothOpen` only sees the open quadrant: agreement there transfers the property. -/
private theorem soCongr {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  refine ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n).congr ?_
  intro p hp
  obtain ⟨hz, hθ, hθ'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ hθ').symm

/-! ## The elementary factors -/

/-- The radius `(z, θ) ↦ z`. -/
private theorem soZ : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1) _
  exact contDiffOn_fst

/-- The multiplier `(z+1)/z` of the witness; its only singularity `z = 0` is outside `Q0`. -/
private theorem soZp1divZ : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1) / z) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => (p.1 + 1) / p.1) _
  refine ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

private theorem soSin : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin θ) :=
  soThetaOnly Real.contDiff_sin

private theorem soCos : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos θ) :=
  soThetaOnly Real.contDiff_cos

/-- `tan θ = sin θ / cos θ` on the open quadrant, where `cos θ > 0`. -/
private theorem soTan : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.tan θ) := by
  refine soCongr (soDiv soSin soCos ?_) ?_
  · intro z θ _ _ hθ'
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ'⟩)
  · intro z θ _ _ _
    exact (Real.tan_eq_sin_div_cos θ).symm

private theorem soS2 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) :=
  soThetaOnly (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

/-- `cos θ ≠ 0` on the open quadrant. -/
private theorem so_C_ne (z θ : ℝ) (_ : 0 < z) (_ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ'⟩)

/-- `sin 2θ ≠ 0` on the open quadrant. -/
private theorem so_S_ne (z θ : ℝ) (_ : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ']))

/-! ## The three transport coefficients -/

/-- **`ℛ` is `C^∞` on the open quadrant** for a `C^∞` datum: `ℛ(Ψ)` is a sum of the three
terms `2 sinθ·Ψ`, `α sinθ·z∂_zΨ`, `cosθ·∂_θΨ` divided by `cos θ`, which is nonzero on `Q0`. -/
private theorem soRop {α : ℝ} {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * Real.sin θ * Ψ z θ) :=
    soMul (f := fun z θ : ℝ => 2 * Real.sin θ) (g := Ψ) (soConstMul 2 soSin) hΨ
  have h2a : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * Real.sin θ * z) :=
    soMul (f := fun z θ : ℝ => α * Real.sin θ) (g := fun z θ : ℝ => z)
      (soConstMul α soSin) soZ
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * Real.sin θ * z * Work.Spaces.pz Ψ z θ) :=
    soMul (f := fun z θ : ℝ => α * Real.sin θ * z) (g := Work.Spaces.pz Ψ) h2a hΨ.pz
  have h3 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.cos θ * Work.Spaces.pth Ψ z θ) :=
    soMul (f := fun z θ : ℝ => Real.cos θ) (g := Work.Spaces.pth Ψ) soCos hΨ.pth
  have h12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ) :=
    soAdd (f := fun z θ : ℝ => 2 * Real.sin θ * Ψ z θ)
      (g := fun z θ : ℝ => α * Real.sin θ * z * Work.Spaces.pz Ψ z θ) h1 h2
  have h123 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
        + Real.cos θ * Work.Spaces.pth Ψ z θ)) :=
    soAdd (f := fun z θ : ℝ => 2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ)
      (g := fun z θ : ℝ => Real.cos θ * Work.Spaces.pth Ψ z θ) h12 h3
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
        + Real.cos θ * Work.Spaces.pth Ψ z θ) / Real.cos θ) :=
    soDiv (f := fun z θ : ℝ => 2 * Real.sin θ * Ψ z θ + α * Real.sin θ * z * Work.Spaces.pz Ψ z θ
        + Real.cos θ * Work.Spaces.pth Ψ z θ)
      (g := fun z θ : ℝ => Real.cos θ) h123 soCos so_C_ne
  unfold Work.Construction.Rop
  exact hfin

/-- **`𝒱` is `C^∞` on the open quadrant**: `𝒱(Ψ) = ∂_θΨ - tan θ·Ψ`. -/
private theorem soVop {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    soMul (f := fun z θ : ℝ => Real.tan θ) (g := Ψ) soTan hΨ
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ) :=
    soSub (f := Work.Spaces.pth Ψ) (g := fun z θ : ℝ => Real.tan θ * Ψ z θ) hΨ.pth h2
  unfold Work.Construction.Vop
  exact hfin

/-- **`𝒰` is `C^∞` on the open quadrant**: `𝒰(Ψ) = -3Ψ - α(z∂_zΨ)`. -/
private theorem soUop (α : ℝ) {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -3 * Ψ z θ) := soConstMul (-3) hΨ
  have h2a : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => α * z) :=
    soConstMul (f := fun z θ : ℝ => z) α soZ
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * z * Work.Spaces.pz Ψ z θ) :=
    soMul (f := fun z θ : ℝ => α * z) (g := Work.Spaces.pz Ψ) h2a hΨ.pz
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ) :=
    soSub (f := fun z θ : ℝ => -3 * Ψ z θ) (g := fun z θ : ℝ => α * z * Work.Spaces.pz Ψ z θ)
      h1 h2
  unfold Work.Construction.Uop
  exact hfin

/-! ## The target -/

theorem fields_smooth {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen Φs) : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) ∧ Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)) ∧ Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) :=
    (smoothOpen_PhiTs hα hα1 hsm).1
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) :=
    soRop hΨ
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) :=
    soVop hΨ
  have hU : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs)) :=
    soUop α hΨ
  have hU2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) :=
    soDiv (f := Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs))
      (g := fun z θ : ℝ => Real.sin (2 * θ)) hU soS2 so_S_ne
  refine ⟨hΨ, ?_, hV, ?_, ?_, ?_, ?_⟩
  · exact soMul (f := fun z θ : ℝ => (z + 1) / z)
      (g := Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) soZp1divZ hR
  · exact soMul (f := fun z θ : ℝ => (z + 1) / z)
      (g := Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) soZp1divZ hV
  · exact hU2
  · exact soMul (f := fun z θ : ℝ => (z + 1) / z)
      (g := fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ) soZp1divZ hU2
  · exact hU.pth

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWApi.FlatW_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWApi

set_option autoImplicit false

/-! ## Locality of the iterated operators on the open quadrant

`∂_z`, `∂_θ`, `D_θ = sin(2·)·∂_θ` are all built from `deriv`, which only depends on the germ of
a function at the point; hence so are all their iterates.  No smoothness is needed for these
two lemmas, only that the open quadrant is a neighbourhood of the point in the relevant
variable. -/

/-- `∂_z^k` respects agreement on the open quadrant. -/
private theorem agree_pzIter {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (k : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k F z θ = Work.Spaces.pzIter k G z θ := by
  induction k with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' : ℝ => Work.Spaces.pzIter n F z' θ)
          =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.pzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      exact heq.deriv_eq

/-- `D_θ^i` respects agreement on the open quadrant. -/
private theorem agree_DthIter {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-! ## The `θ`-derivative of a sum -/

/-- **`∂_θ(f + g) = ∂_θf + ∂_θg` on the open quadrant** for `C^∞` data: the `θ`-slices are
differentiable at every interior angle, so `deriv_add` applies. -/
private theorem pth_add_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
    ((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
    ((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  simp only [Work.Spaces.pth]
  rw [show (fun θ' : ℝ => f z θ' + g z θ')
      = ((fun θ' : ℝ => f z θ') + (fun θ' : ℝ => g z θ')) from by funext θ'; rfl]
  exact deriv_add hd1 hd2

/-! ## Additivity of `∂_z^k D_θ^i ∂_θ` -/

/-- **Additivity of `∂_z^k D_θ^i (∂_θ ·)` on the open quadrant** for `C^∞` data.  The point is
that `∂_θ(f + g) = ∂_θf + ∂_θg` pointwise on `Q0` (`pth_add_Q0`), after which the additivity of
`∂_z^k D_θ^i` (`Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0`, applied to `∂_θf` and
`∂_θg`) is transferred to `∂_θ(f + g)` through the locality of `D_θ^i` and `∂_z^k`. -/
private theorem pzIter_DthIter_pth_add {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i k : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k (Work.Spaces.DthIter i
          (Work.Spaces.pth (fun z θ => f z θ + g z θ))) z θ
        = Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth f)) z θ
          + Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Spaces.pth g)) z θ := by
  have hpth := pth_add_Q0 hf hg
  intro z θ hz h1 h2
  -- transfer `∂_θ(f + g)` to `∂_θf + ∂_θg` under `∂_z^k D_θ^i`
  have hloc : Work.Spaces.pzIter k (Work.Spaces.DthIter i
        (Work.Spaces.pth (fun z θ => f z θ + g z θ))) z θ
      = Work.Spaces.pzIter k (Work.Spaces.DthIter i
          (fun z θ => Work.Spaces.pth f z θ + Work.Spaces.pth g z θ)) z θ :=
    agree_pzIter
      (F := Work.Spaces.DthIter i (Work.Spaces.pth (fun z θ => f z θ + g z θ)))
      (G := Work.Spaces.DthIter i (fun z θ => Work.Spaces.pth f z θ + Work.Spaces.pth g z θ))
      (fun z θ hz h1 h2 => agree_DthIter hpth i z θ hz h1 h2) k z θ hz h1 h2
  rw [hloc]
  exact Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0 (hf.pth) (hg.pth) i k z θ hz h1 h2

/-! ## The main theorem -/

theorem FlatW_add : ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (f g : ℝ → ℝ → ℝ) (K₁ K₂ : ℝ),
    0 ≤ K₁ → 0 ≤ K₂ →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.FTS.VocabO2.FlatW l f K₁ → Work.FTS.VocabO2.FlatW l g K₂ →
    Work.FTS.VocabO2.FlatW l (fun z θ => f z θ + g z θ) (C * (K₁ + K₂)) := by
  refine ⟨1, one_pos, ?_⟩
  intro l f g K₁ K₂ hK₁ hK₂ hf hg hF hG z θ hz h1 h2
  simp only [one_mul]
  obtain ⟨hF1, hF2⟩ := hF z θ hz h1 h2
  obtain ⟨hG1, hG2⟩ := hG z θ hz h1 h2
  refine ⟨?_, ?_⟩
  · intro k hk
    have hsplit := Work.FTS.PhiStar.CoreAux.pzIter_DthIter_add_Q0 hf hg 0 k z θ hz h1 h2
    simp only [Work.Spaces.DthIter_zero] at hsplit
    rw [hsplit, mul_add]
    exact le_trans (abs_add_le _ _) (add_le_add (hF1 k hk) (hG1 k hk))
  · intro k i hki
    have hsplit := pzIter_DthIter_pth_add hf hg i k z θ hz h1 h2
    rw [hsplit, mul_add]
    exact le_trans (abs_add_le _ _) (add_le_add (hF2 k i hki) (hG2 k i hki))

end Work.FTS.PhiStar.FlatWApi
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.tendstoIntegralCsrc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

/-- The partial sums `csrc` of the source series factor through the angular partial sums of the
model `ψ`:  `csrc α ψ N z θ = α² · 𝒜φ(z) · Σ_{m ≤ N} bmode m ψ · eFam m θ`.
(`cmode_RemSource` computes `cmode m (RemSource α ψ) z = α²𝒜φ(z)·bmode m ψ`.) -/
lemma csrc_eq_partialSum (α : ℝ) (ψ : ℝ → ℝ) (N : ℕ) (z θ : ℝ) :
    csrc α ψ N z θ = α ^ 2 * Work.FTS.VocabO.phiA α z *
      (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  simp only [csrc, Work.FTS.PhiStar.Series.cmode_RemSource]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/-- Pointwise convergence of the partial sums of the source series at a fixed angular point,
from the uniform convergence hypothesis on the angular model. -/
lemma tendsto_csrc (α : ℝ) (ψ : ℝ → ℝ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |(∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ| ≤ ε)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => csrc α ψ N z θ) Filter.atTop
      (nhds (Work.FTS.PhiStar.RemSource α ψ z θ)) := by
  have hS : Filter.Tendsto (fun n : ℕ => ∑ m ∈ Finset.range (n + 1),
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      Filter.atTop (nhds (ψ θ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by linarith)
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      have h := hN n hn θ hθ
      linarith⟩
  simp only [csrc_eq_partialSum, Work.FTS.PhiStar.RemSource]
  exact hS.const_mul (α ^ 2 * Work.FTS.VocabO.phiA α z)

theorem tendstoIntegralCsrc (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hbound : ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |(∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ| ≤ ε)
    {φ : ℝ → ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.Weil.csrc α ψ N p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  classical
  obtain ⟨M, hMpos, hbound⟩ := hbound
  -- a compact box containing the support of the test function
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcomp.isClosed.measurableSet
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hφ0 : ∀ p : ℝ × ℝ, p ∉ K → φ p.1 p.2 = 0 := by
    intro p hp
    refine hbox p ?_
    rintro ⟨h1, h2⟩
    exact hp ⟨⟨le_of_lt h1.1, le_of_lt h1.2⟩, ⟨le_of_lt h2.1, le_of_lt h2.2⟩⟩
  -- continuity of the individual factors on `K`
  have hphiK : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.VocabO.phiA α p.1) K := by
    intro p hp
    exact (Work.FTS.PhiStar.contDiffAt_phiA α (lt_of_lt_of_le ha hp.1.1)).continuousAt
      |>.comp_continuousWithinAt continuousWithinAt_fst
  have hφK : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) K :=
    (hφ 0).continuous.continuousOn
  have hwK : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ ((5 - α) / α) * Real.cos p.2) K :=
    (continuous_fst.continuousOn.rpow_const
        (fun p hp => Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
      (Real.continuous_cos.comp continuous_snd).continuousOn
  have hSNcont : ∀ N : ℕ, ContinuousOn (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) K :=
    fun N => continuousOn_finsetSum _ (fun m _ =>
      (continuous_const.mul ((continuous_eFam m).comp continuous_snd)).continuousOn)
  -- the dominated convergence theorem on the box
  have hmain : Filter.Tendsto
      (fun N : ℕ => ∫ p in K, csrc α ψ N p.1 p.2 * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in K, Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict K)
      (fun p : ℝ × ℝ => α ^ 2 * 20 * M * |φ p.1 p.2|
        * |p.1 ^ ((5 - α) / α) * Real.cos p.2|) ?_ ?_ ?_ ?_
    · intro N
      have hcont : ContinuousOn (fun p : ℝ × ℝ => α ^ 2 * Work.FTS.VocabO.phiA α p.1
          * (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) K :=
        ((continuousOn_const (c := α ^ 2)).mul hphiK |>.mul (hSNcont N) |>.mul hφK |>.mul hwK)
      exact (hcont.aestronglyMeasurable hKmeas).congr
        (Filter.Eventually.of_forall (fun p => by simp only [csrc_eq_partialSum]))
    · have hcontb : ContinuousOn (fun p : ℝ × ℝ => α ^ 2 * 20 * M * |φ p.1 p.2|
          * |p.1 ^ ((5 - α) / α) * Real.cos p.2|) K :=
        (continuousOn_const (c := α ^ 2 * 20 * M)).mul hφK.abs |>.mul hwK.abs
      exact ContinuousOn.integrableOn_compact hKcomp hcontb
    · intro N
      filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
      obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKsub hp)
      have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ1, le_of_lt hθ2⟩
      have hS : |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2| ≤ M := hbound N p.2 hθI
      have hphiA : |Work.FTS.VocabO.phiA α p.1| ≤ 20 :=
        Work.FTS.PhiStar.phiA_abs_le hα (by linarith) (le_of_lt hz)
      have hcs : |csrc α ψ N p.1 p.2| ≤ α ^ 2 * 20 * M := by
        rw [csrc_eq_partialSum, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg α)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hphiA (sq_nonneg α)) hS (abs_nonneg _)
          (by positivity)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcs (abs_nonneg _))
        (abs_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
      obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKsub hp)
      have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ1, le_of_lt hθ2⟩
      have hlim : Filter.Tendsto (fun N : ℕ => csrc α ψ N p.1 p.2) Filter.atTop
          (nhds (Work.FTS.PhiStar.RemSource α ψ p.1 p.2)) := tendsto_csrc α ψ hconv hθI
      exact (hlim.mul tendsto_const_nhds).mul tendsto_const_nhds
  -- restrict both integrals from the quadrant to the box
  have hrew : ∀ (g : ℝ × ℝ → ℝ), (∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, g p = 0) →
      (∫ p in Work.FTS.EllipticEst.Q0, g p) = ∫ p in K, g p := fun g hg =>
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet hKsub hg
  have hQK : (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = fun N : ℕ => ∫ p in K,
        csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
    funext N
    refine hrew (fun p => csrc α ψ N p.1 p.2 * φ p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) ?_
    intro p hp
    show csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
    rw [hφ0 p hp.2]
    ring
  have hQK' : (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
    refine hrew (fun p => Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) ?_
    intro p hp
    show Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
    rw [hφ0 p hp.2]
    ring
  rw [hQK, hQK']
  exact hmain

end Work.FTS.PhiStar.Series.Weil
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Construction Work.Spaces
open Work.FTS.Nonlinear.Pieces.rl1Tools (aesm_congr aesm_mul aesm_const_mul aesm_neg
  aesm_s2_mul aesm_sinsq_mul aesm_FK aesm_Uop_of_div aesm_of_contOn_Qd
  aesm_F_ops QdMeas pv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bridge `SmoothOpen ⟹` a.e. strong measurability of the atoms -/

/-- A function which is `C^∞` on the open quadrant has a.e. strongly measurable uncurried
form, together with its angular derivative, its radial weight derivative and its angular
weight derivative.  This is the `SmoothOpen` counterpart of `aesm_g_ops`. -/
theorem aesm_f_ops_open {f : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (Function.uncurry f) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.pth f)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dz f)) QdMeas ∧
    AEStronglyMeasurable (Function.uncurry (Work.Spaces.Dth f)) QdMeas :=
  ⟨aesm_of_contOn_Qd h.continuousOn,
    aesm_of_contOn_Qd h.pth.continuousOn,
    aesm_of_contOn_Qd h.Dz.continuousOn,
    aesm_of_contOn_Qd h.Dth.continuousOn⟩

/-! ## The target statement -/

theorem meas_open {α Ce Cs : ℝ} {f Φs Ξg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce f Ξg) :
    (∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : Fin 20,
        AEMeasurable (fun θ : ℝ => ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∀ k : Fin 20, AEMeasurable
        (fun r : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ
          * Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ|)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  obtain ⟨hf, hpthf, hDzf, hDthf⟩ := aesm_f_ops_open hso
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := Work.FTS.NonlinRows.Rl1.aesm_Tg_ops_open hell
  have hFKf : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK f z)) QdMeas := aesm_FK hf
  have hFKF : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z))
      QdMeas := aesm_FK hF
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ :=
    Work.FTS.NonlinRows.Rl1.aesm_star_ops_open hα hα1 hs
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α f Ξg) z θ * f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α f Ξg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α f Ξg) z θ * pth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α f Ξg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α f Ξg) z θ * Dz f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α f Ξg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK f z * Dth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKf hDthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK f z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKf hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth f z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthf)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK f z * f z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKf hf))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK f z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKf hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * f z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hf))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  -- the `ENNReal`-valued versions, with the angular weight `K`
  have hENN : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlinear.Pieces.rl1Tools.pv
        α f Φs Ξg k r θ|)) QdMeas := by
    intro k
    have hKcont : Continuous fun p : ℝ × ℝ => Work.Spaces.K p.2 := by
      simp only [Work.Spaces.K]; fun_prop
    have hK : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) QdMeas :=
      hKcont.aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.K p.2, Function.uncurry (fun r θ =>
          Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Ξg k r θ) p)) QdMeas :=
      hK.prodMk (hpiece k)
    have hcomp : Continuous (fun q : ℝ × ℝ => ENNReal.ofReal |q.1 * q.2|) :=
      ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_fst.mul continuous_snd))
    exact hcomp.comp_aestronglyMeasurable hpair
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_all.2 fun k => (hENN k).prodMk_left] with r hr
    intro k
    exact (hr k).aemeasurable
  · intro k
    exact (hENN k).aemeasurable.lintegral_prod_right

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.contN0_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 800000

/-- **Joint continuity of `N₀ α (F_*+g) g` on the open quadrant**, in the *open* datum class
`SmoothOpen g` + `HkMem α 4 g`.

`N₀` is a sum of six terms, each a product of the angular factors `sin(2θ)`, `cos 2θ - sin²θ`,
the radial factors `z ↦ L₁₂(g)(z)` (`Work.Construction.L12 g`) and `z ↦ L₁₂(F_*)(z)`, and the
fields `g`, `∂_θg`, `z∂_zg`, `∂_θ(F_*+g)`, `z∂_z(F_*+g)`.  Every factor is continuous on the
open quadrant:

* `g` and its `∂_θ`/`z∂_z` derivatives, because `SmoothOpen` is preserved by `pz`/`pth`/`Dz`
  (`EllipticEst.SmoothOpen.pz`, `.pth`, `.Dz`) and a `C^∞` function is continuous;
* `F_*` and its derivatives, from `LocData.Fstar_smoothQuad` (the open quadrant `Q0` sits inside
  the strip `quadU = (-1,∞) × (0,π/2)`), and hence the same for `F_* + g`;
* `L₁₂(F_*)(z) = 2α/(1+z)` (`continuousOn_L12_Fstar`);
* `z ↦ L₁₂(g)(z)`, by `OpenPkg.l12diff_field` (`Construction.L12` is *definitionally*
  `Elliptic.L12`, hence differentiable on `(0,∞)` for a `SmoothOpen` honest `ℋ⁴` datum, by
  `UopHk.contDiffOn_L12_of_smoothOpen_Hk`).

The assembly is the one of `Work.FTS.Nonlinear.Pieces.continuousOn_uncurry_N0` (the
stronger-class sibling of this statement), with the `SmoothQuad`-hypotheses replaced by the
`SmoothOpen` API. -/
theorem contN0_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ContinuousOn (Function.uncurry (Work.Construction.N0 α (Work.Construction.Ftot α g) g))
      (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  -- smoothness of the explicit profile `F_*` on the open quadrant
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    (Work.FTS.LocData.Fstar_smoothQuad α).mono (by
      intro p hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ⟨by show (-1 : ℝ) < p.1; linarith, hθ0, hθ1⟩)
  -- smoothness of the full profile `F = F_* + g`
  have hT : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α g) :=
    hF.add hso
  -- `z ↦ L₁₂(g)(z)` on `(0,∞)`, from the differentiability delivered by `l12diff_field`
  have hLg : ContinuousOn (fun z : ℝ => Work.Construction.L12 g z) (Set.Ioi 0) :=
    DifferentiableOn.continuousOn (fun z hz =>
      (Work.FTS.OpenPkg.l12diff_field α g hα hα1 ⟨hso, hmem⟩ z hz).differentiableWithinAt)
  -- `z ↦ L₁₂(F_*)(z) = 2α/(1+z)` on `(0,∞)`
  have hLF : ContinuousOn (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi 0) := Work.FTS.Nonlinear.Pieces.continuousOn_L12_Fstar hα hα1
  have hpthg : ContinuousOn (Function.uncurry (Work.Spaces.pth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hso.pth.continuousOn
  have hpzg : ContinuousOn (Function.uncurry (Work.Spaces.pz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hso.pz.continuousOn
  have hpthF : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF.pth.continuousOn
  have hpzF : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Fstar α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF.pz.continuousOn
  have hpthT : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Construction.Ftot α g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hT.pth.continuousOn
  have hpzT : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Construction.Ftot α g)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hT.pz.continuousOn
  have hg : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hso.continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.s2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.Construction.s2]
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hc2m : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    simp only [Work.Construction.c2m]
    exact (((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).sub
      ((Real.continuous_sin.comp continuous_snd).pow 2))).continuousOn
  have hLg' : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 g p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hLg.comp continuousOn_fst (fun p hp => hp.1)
  have hLF' : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 (Work.Construction.Fstar α) p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hLF.comp continuousOn_fst (fun p hp => hp.1)
  have h1 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
        * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).mul hsin).mul hLF').mul hpthF).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h2 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hc2m.mul hLF').mul (continuousOn_fst.mul hpzF)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have h3 : ContinuousOn (fun p : ℝ × ℝ =>
      (1 / α) * Work.Construction.L12 g p.1 * g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine (((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (1 / α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).mul hLg').mul hg).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h4 : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2 * Work.Construction.L12 g p.1
        * Work.Spaces.pth (Work.Construction.Ftot α g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (3 / (2 * α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))).mul hsin).mul hLg').mul hpthT).congr ?_
    intro p hp; simp only [Function.uncurry, Pi.mul_apply]
  have h5 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 g p.1
        * Work.Spaces.Dz (Work.Construction.Ftot α g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hc2m.mul hLg').mul (continuousOn_fst.mul hpzT)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have h6 : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
        * Work.Spaces.Dz g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((hc2m.mul hLF').mul (continuousOn_fst.mul hpzg)).congr ?_
    intro p hp; simp only [Function.uncurry, Work.Spaces.Dz, Pi.mul_apply]
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      (3 / (2 * α)) * Work.Construction.s2 p.2
          * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.pth (Work.Construction.Fstar α) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2
        + (1 / α) * Work.Construction.L12 g p.1 * g p.1 p.2
        + (3 / (2 * α)) * Work.Construction.s2 p.2 * Work.Construction.L12 g p.1
          * Work.Spaces.pth (Work.Construction.Ftot α g) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 g p.1
          * Work.Spaces.Dz (Work.Construction.Ftot α g) p.1 p.2
        - Work.Construction.c2m p.2 * Work.Construction.L12 (Work.Construction.Fstar α) p.1
          * Work.Spaces.Dz g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ((((h1.sub h2).add h3).add h4).sub h5).sub h6 |>.congr ?_
    intro p hp
    simp only [Pi.sub_apply, Pi.add_apply]
  refine key.congr ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

/-- The `ℋ^k`-integrand is a sum of squares, hence nonnegative. -/
lemma l12sup_hkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split
  · exact sq_nonneg _
  · exact le_refl 0

/-- The squared `ℋ^k`-norm is nonnegative. -/
lemma l12sup_hkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  exact integral_nonneg fun z => integral_nonneg fun θ => l12sup_hkIntegrand_nonneg α k f z θ

/-- **The pointwise slice bound.**  For `r > 0`, an integrable angular slice `θ ↦ f(r,θ)²` on
`Iθ`, and any `Φ` dominating the Hardy weighted angular energy
`(∫_θ f(r,θ)²)·((1+r)/r)² ≤ Φ` (which is the statement of `phiWeight_slice_le` for `Φ` the
`HkIntegrand`-slice), the `L₁₂`-density at `r` satisfies

`|L₁₂dens(f)(r)| ≤ √(3Φ)/(1+r)`.

The two Cauchy–Schwarz steps are `L12dens_sq_slice` (in `θ`) and the relation
`√(φ·((1+r)/r)²) ≤ √Φ` (which is exactly `Φ ≥ φ(1+r)²/r²`, i.e. the comparison of the Hardy
weight with the `ρ²`-weight of the `ℋ⁴`-norm). -/
lemma l12sup_dens_le {f : ℝ → ℝ → ℝ} {r Φ : ℝ} (hr : 0 < r)
    (hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f r θ) ^ 2) Work.Spaces.Iθ)
    (hW : (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ) :
    |Work.FM.L12dens Work.Spaces.K f r| ≤ Real.sqrt (3 * Φ) * (1 / (1 + r)) := by
  have hφ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
  have hΦ0 : 0 ≤ Φ := le_trans (mul_nonneg hφ0 (sq_nonneg _)) hW
  have hsq : (Work.FM.L12dens Work.Spaces.K f r) ^ 2
      ≤ 3 * (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r ^ 2 :=
    Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hr hsl
  have hb : |Work.FM.L12dens Work.Spaces.K f r|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r :=
    Work.FTS.H2.abs_le_sqrt_three_mul_sqrt_div hr hφ0 hsq
  refine hb.trans ?_
  have hkey1 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)
      ≤ Real.sqrt Φ := by
    have hsqφ : (Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)) ^ 2
        = (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hφ0]
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)
        = Real.sqrt ((Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r)) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (by linarith) hr.le))).symm
      _ = Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by rw [hsqφ]
      _ ≤ Real.sqrt Φ := Real.sqrt_le_sqrt hW
  have hkey2 : Real.sqrt 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r))
      ≤ Real.sqrt (3 * Φ) := by
    have h := mul_le_mul_of_nonneg_left hkey1 (Real.sqrt_nonneg 3)
    rwa [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) Φ] at h
  calc Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r
      = Real.sqrt 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r))
          * (1 / (1 + r)) := by
        have hr0 : r ≠ 0 := ne_of_gt hr
        have h1r : (1 : ℝ) + r ≠ 0 := by positivity
        field_simp
    _ ≤ Real.sqrt (3 * Φ) * (1 / (1 + r)) :=
        mul_le_mul_of_nonneg_right hkey2 (by positivity)

/-- **The uniform `L₁₂` bound in the open-quadrant class.**  For `SmoothOpen g` (interior
smoothness on the open quadrant) and `HkMem α 4 g`, the tail integral of the `L₁₂` density is
bounded by `3|g|_{ℋ⁴}` for every `z ≥ 0` — the zero-mode constant of
`Work.FTS.OpenPkg.l12zero_field`, valid uniformly in the radial variable.

See the module docstring for the proof: Cauchy–Schwarz on the tail `(z,∞)` against the
`ℋ⁴`-majorant `Φ` and the *decreasing* tail weight `1/(1+r)`, for which
`∫_{(z,∞)} 1/(1+r)² ≤ 2` requires `z ≥ 0`. -/
theorem l12_supAbs_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g := by
  intro z hz
  -- the tail `(z,∞)` sits inside the domain `Iz = [0,∞)` because `z ≥ 0`
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro r hr
    rw [Work.Spaces.Iz]
    exact le_trans hz (le_of_lt (Set.mem_Ioi.mp hr))
  have hΦnn : ∀ r : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r => integral_nonneg fun θ => l12sup_hkIntegrand_nonneg α 4 g r θ
  -- the `ℋ⁴`-majorant is integrable on the tail
  have hΦint : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) (Set.Ioi z) :=
    hmem.2.mono_set hsub
  -- `A = √(3Φ)` is a.e. strongly measurable (it is the composition of the integrable `3Φ`
  -- with the continuous `√`) …
  have hAmeas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ))
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable (hΦint.aestronglyMeasurable.const_mul 3)
  have hAcongr : (fun r : ℝ => 3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi z)]
      (fun r : ℝ =>
        Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2) :=
    Filter.Eventually.of_forall fun r => (Real.sq_sqrt (mul_nonneg (by norm_num) (hΦnn r))).symm
  -- … and `A² = 3Φ` is integrable
  have hA2int : MeasureTheory.Integrable
      (fun r : ℝ =>
        Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := (hΦint.const_mul 3).congr hAcongr
  have hAmem : MeasureTheory.MemLp
      (fun r : ℝ => Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)) 2
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hA2int
  -- the tail weight `B = 1/(1+r)` is in `L²(z,∞)` (by monotonicity from `InvOneAddSq`)
  have hBint : MeasureTheory.IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Set.Ioi z) :=
    (Work.FTS.H2.InvOneAddSq).1.mono_set (Set.Ioi_subset_Ioi hz)
  have hBmeas : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (by fun_prop : Measurable fun r : ℝ => 1 / (1 + r)).aestronglyMeasurable
  have hBmem : MeasureTheory.MemLp (fun r : ℝ => 1 / (1 + r)) 2
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  have hr_mem : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)), r ∈ Set.Ioi z :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- the two slicewise inputs, a.e. on the tail
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (g r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
      Work.FTS.OpenPkg.l12zero_slice_sq_integrableOn α hso hmem
        (lt_of_le_of_lt hz (Set.mem_Ioi.mp hr))
  have hWmem : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
      Work.FTS.H2.L12Q.phiWeight_slice_le α g hmem r (lt_of_le_of_lt hz (Set.mem_Ioi.mp hr))
  -- the pointwise bound `|L₁₂dens(g)(r)| ≤ A(r)·B(r)`
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      |Work.FM.L12dens Work.Spaces.K g r|
        ≤ Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
          * (1 / (1 + r)) := by
    filter_upwards [hr_mem, hsl, hWmem] with r hr hslr hWr
    exact l12sup_dens_le (lt_of_le_of_lt hz (Set.mem_Ioi.mp hr)) hslr hWr
  -- Cauchy–Schwarz on the tail
  have hcs := Work.FTS.H2.CS1D hAmem hBmem
    (Filter.Eventually.of_forall fun r => Real.sqrt_nonneg _)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr =>
      div_nonneg zero_le_one (by have h := Set.mem_Ioi.mp hr; linarith))
    hbd
  -- the two `L²`-norms: `∫_{(z,∞)} 3Φ ≤ 3 HkSq α 4 g` and `∫_{(z,∞)} B² ≤ 2`
  have hIntΦ : ∫ r in Set.Ioi z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      ≤ Work.Spaces.HkSq α 4 g := by
    have hmono := MeasureTheory.setIntegral_mono_set hmem.2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun r _ => hΦnn r)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
    exact hmono
  have hA2le : ∫ r, Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Ioi z)) ≤ 3 * Work.Spaces.HkSq α 4 g := by
    have h1 : ∫ r, Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) ^ 2
          ∂(MeasureTheory.volume.restrict (Set.Ioi z))
        = ∫ r, 3 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi z)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r =>
        Real.sq_sqrt (mul_nonneg (by norm_num) (hΦnn r)))
    rw [h1, MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hIntΦ (by norm_num)
  have hB2le : ∫ r, (1 / (1 + r)) ^ 2 ∂(MeasureTheory.volume.restrict (Set.Ioi z)) ≤ 2 := by
    have hmono := MeasureTheory.setIntegral_mono_set (Work.FTS.H2.InvOneAddSq).1
      (Filter.Eventually.of_forall fun r => sq_nonneg (1 / (1 + r)))
      (Filter.Eventually.of_forall fun x hx => Set.Ioi_subset_Ioi hz hx)
    exact hmono.trans (Work.FTS.H2.InvOneAddSq).2
  have hLHS : (∫ r, Work.FM.L12dens Work.Spaces.K g r
      ∂(MeasureTheory.volume.restrict (Set.Ioi z))) = Work.Construction.L12 g z := rfl
  have hstep1 : |Work.Construction.L12 g z|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 := by
    rw [← hLHS]
    exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- `√(3 HkSq)·√2 = √6·|g|_{ℋ⁴} ≤ 3|g|_{ℋ⁴}`
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsqXn : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (l12sup_hkSq_nonneg α 4 g)).symm
  calc |Work.Construction.L12 g z|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 g) * Real.sqrt 2 := hstep1
    _ = Real.sqrt 6 * Work.FTS.Nonlin.Xn α g := by
        have h6 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
          rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
          norm_num
        rw [hsqXn, Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)
          ((Work.FTS.Nonlin.Xn α g) ^ 2), Real.sqrt_sq hXn0, h6]
        ring
    _ ≤ 3 * Work.FTS.Nonlin.Xn α g := by
        refine mul_le_mul_of_nonneg_right ?_ hXn0
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.CoefBundle6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-!
# `FTS/StrongPersist/SP6/CoefBundle6` — the ten coefficient functions of `StarPkgo2` lie in `F0 6`

The flat class `Work.FTS.PhiStar.F0 n K f` bounds all the mixed weighted derivatives
`(z+1)^k ∂_z^k D_θ^i f` (`k + i ≤ n`) on the open quadrant.  The `SP6` assembly multiplies its
analytic data by ten coefficient functions: the four angular ones
`sin²θ, cos²θ - 2 sin²θ, sin 2θ, cos 2θ`, the four *derivatives* of the first four
(these are the angular coefficients of `∂_θ`-slots), and the two radial ones
`z/(1+z)`, `(1+z)⁻¹`.

`F0_theta_coefs` and `F0_z_coefs` already supply the first four and the last two, each with its
own positive constant.  The four derivative functions are *also* `θ`-only, so they are handled
by the same generic `θ`-only tool `CoreAux.exists_F0_of_theta_only_aux`: the derivative is first
identified with an explicit smooth trigonometric function (`deriv_sin_sq_prv`, `deriv_cos_sq_sub_prv`,
`deriv_sin_two_prv`, `deriv_cos_two_prv`), and `F0` is insensitive to replacing a function by another
one agreeing with it on the open quadrant (`CoreAux.F0_congr`).

Finally the finitely many positive constants are merged into a single `A ≥ 1`.  This is a pure
bookkeeping lemma: its value is that the `SP6` consumer gets one constant for all ten slots.
-/

/-- **A `θ`-only `C⁶` function lies in `F0 6`** with some positive constant.

This is the `m = 6` instance of the generic tool: for a `θ`-only datum every slot with a radial
derivative vanishes, and the purely angular slots are bounded by the suprema on the compact
interval `Iθ` of the continuous functions `Lop^[i] c`, `i ≤ 6`
(`LopIter_continuousOn_of_contDiff`). -/
private theorem F0_six_of_theta_smooth (c : ℝ → ℝ)
    (hc : ContDiff ℝ ((6 : ℕ∞) : WithTop ℕ∞) c) :
    ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 6 A (fun _ θ => c θ) :=
  Work.FTS.PhiStar.CoreAux.exists_F0_of_theta_only_aux 6 c
    (fun i hi => Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff 6 c hc i hi)

/-- **The `θ`-derivative of a `θ`-only function lies in `F0 6` as soon as the derivative is
identified with an explicit `C⁶` function.**

`F0` only sees the open quadrant (`CoreAux.F0_congr`), so the pointwise identity
`deriv c θ = d θ` transfers the `F0 6`-membership of the `θ`-only datum `d`. -/
private theorem F0_six_of_deriv {c d : ℝ → ℝ} (hd : ∀ θ, deriv c θ = d θ)
    (hs : ContDiff ℝ ((6 : ℕ∞) : WithTop ℕ∞) d) :
    ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv c θ) := by
  obtain ⟨A, hA, hAd⟩ := F0_six_of_theta_smooth d hs
  exact ⟨A, hA, Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => hd θ) hAd⟩

/-- `deriv (sin²) = 2 sin θ cos θ`. -/
private lemma deriv_sin_sq_prv (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  have h := (Real.hasDerivAt_sin θ).pow 2
  simpa using h.deriv

/-- `deriv (cos² - 2 sin²) = -6 sin θ cos θ`. -/
private lemma deriv_cos_sq_sub_prv (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = -(6 * Real.sin θ * Real.cos θ) := by
  have h1 := (Real.hasDerivAt_cos θ).pow 2
  have h2 := ((Real.hasDerivAt_sin θ).pow 2).const_mul 2
  have h := h1.sub h2
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = deriv ((Real.cos ^ 2) - fun y => 2 * (Real.sin ^ 2) y) θ := rfl
  rw [e, hd]
  ring_nf

/-- `deriv (sin 2θ) = 2 cos 2θ`. -/
private lemma deriv_sin_two_prv (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = deriv (Real.sin ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

/-- `deriv (cos 2θ) = -2 sin 2θ`. -/
private lemma deriv_cos_two_prv (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = -(2 * Real.sin (2 * θ)) := by
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = deriv (Real.cos ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

theorem CoefBundle6 : ∃ A : ℝ, 1 ≤ A ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.sin θ' ^ 2) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.sin (2 * θ')) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.cos (2 * θ')) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) := by
  obtain ⟨A₁, hA₁, h1, h2, h3, h4⟩ := Work.FTS.PhiStar.CoreAux.F0_theta_coefs 6
  obtain ⟨A₂, hA₂, h9, h10⟩ := Work.FTS.PhiStar.CoreAux.F0_z_coefs 6
  obtain ⟨A₃, hA₃, h5⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.sin θ' ^ 2)
      (fun θ => deriv_sin_sq_prv θ) (by fun_prop)
  obtain ⟨A₄, hA₄, h6⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)
      (fun θ => deriv_cos_sq_sub_prv θ) (by fun_prop)
  obtain ⟨A₅, hA₅, h7⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.sin (2 * θ')) (fun θ => deriv_sin_two_prv θ) (by fun_prop)
  obtain ⟨A₆, hA₆, h8⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.cos (2 * θ')) (fun θ => deriv_cos_two_prv θ) (by fun_prop)
  refine ⟨A₁ + A₂ + A₃ + A₄ + A₅ + A₆ + 1, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h1
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h2
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h4
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h3
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h5
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h6
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h7
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h8
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h9
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h10

end Work.FTS.StrongPersist.SP6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SupOpenH2Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts -/

theorem sin_two_pos_of_Q0 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
  nlinarith [sq_nonneg (1 + z), hz.le, sq_nonneg z]

theorem w_sq_mul_self_ge {z : ℝ} (hz : 0 < z) : (256 : ℝ) / 27 ≤ (Work.Spaces.w z) ^ 2 * z := by
  have hid : 27 * (1 + z) ^ 4 - 256 * z ^ 3 = (z - 3) ^ 2 * (27 * z ^ 2 + 14 * z + 3) := by ring
  have hnn : 0 ≤ (z - 3) ^ 2 * (27 * z ^ 2 + 14 * z + 3) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hkey : 256 * z ^ 3 ≤ 27 * (1 + z) ^ 4 := by
    have : 0 ≤ 27 * (1 + z) ^ 4 - 256 * z ^ 3 := by rw [hid]; exact hnn
    linarith
  rw [Work.Spaces.w, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (z ^ 2) ^ 2)]
  nlinarith [hkey, hz]

theorem sin_two_neg_eta_one_le {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hpos := sin_two_pos_of_Q0 hθ
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have heta : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  calc (1 : ℝ) = (Real.sin (2 * θ)) ^ (0 : ℝ) := (Real.rpow_zero _).symm
    _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by linarith)



/-! ## The derivative of `w z * √z` and its bounds -/

theorem hasDerivAt_sq (z : ℝ) : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * z ^ (2 - 1)) z := hasDerivAt_pow 2 z
  convert h using 1
  norm_num

theorem hasDerivAt_one_add_sq (z : ℝ) :
    HasDerivAt (fun z' : ℝ => (1 + z') ^ 2) (2 * (1 + z)) z := by
  have h0 : HasDerivAt (fun y : ℝ => 1 + y) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
  have h : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * (1 + z) ^ (2 - 1)) (1 + z) :=
    hasDerivAt_pow 2 (1 + z)
  have hc := h.comp z h0
  have h1 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 2)
      ((2 : ℕ) * (1 + z) ^ (2 - 1) * 1) z := by
    refine hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
    simp only [Function.comp_def]
  convert h1 using 1
  norm_num

/-- The derivative of `w z * √z`. -/
noncomputable def dWsq (z : ℝ) : ℝ := ((Work.Spaces.w z * Real.sqrt z) * (z - 3)) / (2 * z * (1 + z))

theorem hasDerivAt_dWsq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => Work.Spaces.w z' * Real.sqrt z') (dWsq z) z := by
  have hz2 : z ^ 2 ≠ 0 := by positivity
  have hA : HasDerivAt (fun z' : ℝ => (1 + z') ^ 2 / z' ^ 2)
      ((2 * (1 + z) * z ^ 2 - (1 + z) ^ 2 * (2 * z)) / (z ^ 2) ^ 2) z :=
    (hasDerivAt_one_add_sq z).div (hasDerivAt_sq z) hz2
  have hB : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt z)) z := Real.hasDerivAt_sqrt (ne_of_gt hz)
  have h := hA.mul hB
  have h1 : HasDerivAt (fun z' : ℝ => Work.Spaces.w z' * Real.sqrt z')
      ((2 * (1 + z) * z ^ 2 - (1 + z) ^ 2 * (2 * z)) / (z ^ 2) ^ 2 * Real.sqrt z
        + (1 + z) ^ 2 / z ^ 2 * (1 / (2 * Real.sqrt z))) z := by
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
    simp only [Pi.mul_apply, Work.Spaces.w]
  convert h1 using 1
  · rw [dWsq, Work.Spaces.w]
    field_simp
    nlinarith [Real.sq_sqrt hz.le]



theorem abs_div_ge_le {z : ℝ} (hz : 0 < z) :
    (z - 3) ^ 2 / (1 + z) ^ 2 ≤ 9 := by
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (z - 3), sq_nonneg (1 + z), hz.le]

/-! ## Continuity of the auxiliary factors -/

theorem continuousOn_w :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rw [Work.Spaces.w]
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1)

theorem continuousOn_w_mul_sqrt :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 * Real.sqrt p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  continuousOn_w.mul continuousOn_fst.sqrt

end Work.FTS.StrongPersist

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Nonnegativity of `HkIntegrand` -/


/-! ## The comparison `∫ u² ≤ 2 ∫ u² σ^{-η}` -/

theorem aesm_sq_slice_of_SmoothOpen {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (h z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (fun θ => (h z θ) ^ 2)
      (volume.restrict (Set.Ioo 0 (π / 2))) :=
    (((hso.curry_θ hz).continuousOn).aestronglyMeasurable measurableSet_Ioo).pow 2
  have hmeq : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))
  rwa [hmeq] at h1

theorem int_sq_le_two_weighted {u : ℝ → ℝ}
    (haesm : AEStronglyMeasurable (fun θ => (u θ) ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ,
          (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (u θ) ^ 2 ≤ (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
        (u θ) ^ 2 ≤ (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall fun θ hθ => by
        have hle := sin_two_neg_eta_one_le hθ
        nlinarith [sq_nonneg (u θ)]
    have hmeq : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))
    rwa [hmeq] at h1
  have hae' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖(u θ) ^ 2‖ ≤ (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [hae] with θ hθ
    rwa [Real.norm_of_nonneg (sq_nonneg (u θ))]
  have hu2 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    Integrable.mono' hint haesm hae'
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    setIntegral_nonneg measurableSet_Icc fun θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (sin_two_nonneg_of_Iθ hθ) _)
  calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.integral_mono_ae hu2 hint hae
    _ ≤ 2 * (∫ θ in Work.Spaces.Iθ,
          (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by linarith

/-! ## Slot integrability: inner (angular) and outer (radial) -/

theorem slot_inner {α : ℝ} {k : ℕ} {h S : ℝ → ℝ → ℝ}
    (hScont : ContinuousOn (Function.uncurry S) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α k h)
    (hSnn : ∀ z θ, 0 ≤ S z θ) (hSle : ∀ z θ, S z θ ≤ Work.Spaces.HkIntegrand α k h z θ) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => S z θ) Work.Spaces.Iθ := by
  intro z hz
  have haesm : AEStronglyMeasurable (fun θ => S z θ) (volume.restrict Work.Spaces.Iθ) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · rw [← h0]
      have hzero : (fun θ => S 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have h1 := hSle 0 θ
        rw [Work.Spaces.HkIntegrand_zero_z] at h1
        exact le_antisymm h1 (hSnn 0 θ)
      rw [hzero]; exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hScont hpos
  refine Integrable.mono' (hmem.1 z hz) haesm ?_
  rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
  exact Eventually.of_forall fun θ _ => by
    rw [Real.norm_of_nonneg (hSnn z θ)]
    exact hSle z θ

theorem slot_outer {α : ℝ} {k : ℕ} {h S : ℝ → ℝ → ℝ}
    (hScont : ContinuousOn (Function.uncurry S) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α k h)
    (hSnn : ∀ z θ, 0 ≤ S z θ) (hSle : ∀ z θ, S z θ ≤ Work.Spaces.HkIntegrand α k h z θ) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, S z θ) Work.Spaces.Iz := by
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, S z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h1 := (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry S) hScont).integral_prod_right'
    have heq : (fun z => ∫ θ, Function.uncurry S (z, θ) ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ, S z θ) := by
      funext z; rfl
    rwa [heq] at h1
  refine Integrable.mono' hmem.2 haesm ?_
  rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
  refine Eventually.of_forall fun z hz => ?_
  have h1 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, S z θ := integral_nonneg fun θ => hSnn z θ
  rw [Real.norm_of_nonneg h1]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => hSnn z θ) (hmem.1 z hz)
    (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => hSle z θ)

end Work.FTS.StrongPersist

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weighted-square identity -/

theorem sin_two_neg_half_sq_gen {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2 = (Real.sin (2 * θ)) ^ (-p) := by
  rw [pow_two, ← Real.rpow_add (sin_two_pos_of_Q0 hθ)]
  ring_nf

theorem sin_two_pos_half_sq_gen {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((Real.sin (2 * θ)) ^ (p / 2)) ^ 2 = (Real.sin (2 * θ)) ^ p := by
  rw [pow_two, ← Real.rpow_add (sin_two_pos_of_Q0 hθ)]
  ring_nf

theorem div_sin_half_sq_gen {z θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (p / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h1 : (0 : ℝ) ^ (p / 2) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    have h2 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h1, h2]
    ring
  · have hθ' : θ ∈ Set.Ioo 0 (π / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; rw [← h] at hspos; rw [mul_zero, Real.sin_zero] at hspos
        exact absurd hspos (lt_irrefl 0)
      · intro h; rw [h] at hspos; rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi] at hspos
        exact absurd hspos (lt_irrefl 0)
    rw [div_pow, sin_two_pos_half_sq_gen hθ', div_eq_mul_inv, ← Real.rpow_neg hspos.le]


end Work.FTS.StrongPersist

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem eta_ne_zero : Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num

/-- `(x · σ^{-p/2})² = x² · σ^{-p}` on `Iθ`. -/
theorem mul_sin_neg_half_sq {x θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (x * (Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2
      = x ^ 2 * (Real.sin (2 * θ)) ^ (-p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h1 : (0 : ℝ) ^ (-(p / 2)) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    have h2 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h1, h2]; ring
  · have hθ' : θ ∈ Set.Ioo 0 (π / 2) := by
      refine ⟨lt_of_le_of_ne hθ.1 ?_, lt_of_le_of_ne hθ.2 ?_⟩
      · intro h; rw [← h] at hspos; rw [mul_zero, Real.sin_zero] at hspos
        exact absurd hspos (lt_irrefl 0)
      · intro h; rw [h] at hspos; rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi] at hspos
        exact absurd hspos (lt_irrefl 0)
    rw [mul_pow, sin_two_neg_half_sq_gen (p := p) hθ']

theorem slot0_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter 0 h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  show (h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = _
  rw [mul_pow, div_sin_half_sq_gen hθ eta_ne_zero]
  ring

theorem slot1_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter 1 h z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z ^ 2
          * ((Work.Spaces.pz h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  show (Work.Spaces.Dz h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = _
  rw [show Work.Spaces.Dz h z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = (z * Work.Spaces.pz h z θ) * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      from rfl]
  rw [show ((z * Work.Spaces.pz h z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.pz h z θ) ^ 2
        * (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 from by ring]
  rw [mul_pow, div_sin_half_sq_gen hθ eta_ne_zero]
  ring

theorem dWsq_sq_id {z : ℝ} (hz : 0 < z) :
    (dWsq z) ^ 2 = (Work.Spaces.w z) ^ 2 * ((z - 3) ^ 2 / (4 * z * (1 + z) ^ 2)) := by
  rw [dWsq, Work.Spaces.w]
  field_simp
  nlinarith [Real.sq_sqrt hz.le]

theorem PhiA_sq_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (h z θ * (Work.Spaces.w z * Real.sqrt z)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z * ((h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [mul_sin_neg_half_sq (x := h z θ * (Work.Spaces.w z * Real.sqrt z)) hθ eta_ne_zero,
      show (h z θ * (Work.Spaces.w z * Real.sqrt z)) ^ 2
        = (h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hz.le]; ring]
  ring

theorem pz_term_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z
          * ((Work.Spaces.pz h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [mul_sin_neg_half_sq (x := Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)) hθ
        eta_ne_zero,
      show (Work.Spaces.pz h z θ * (Work.Spaces.w z * Real.sqrt z)) ^ 2
        = (Work.Spaces.pz h z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hz.le]; ring]
  ring

theorem d_term_unfold (h : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (h z θ * dWsq z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((z - 3) ^ 2 / (4 * z * (1 + z) ^ 2))
          * ((h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  rw [mul_sin_neg_half_sq (x := h z θ * dWsq z) hθ eta_ne_zero,
      show (h z θ * dWsq z) ^ 2 = (h z θ) ^ 2 * (dWsq z) ^ 2 from by ring,
      dWsq_sq_id hz]
  ring

theorem continuousOn_sin_pow (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ q) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
  intro p hp
  exact Or.inl (ne_of_gt (sin_two_pos_of_Q0 (Set.mem_prod.mp hp).2))

theorem continuousOn_dWsq :
    ContinuousOn (fun p : ℝ × ℝ => dWsq p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfun : (fun p : ℝ × ℝ => dWsq p.1)
      = fun p : ℝ × ℝ => ((Work.Spaces.w p.1 * Real.sqrt p.1) * (p.1 - 3)) / (2 * p.1 * (1 + p.1)) := by
    funext p; rw [dWsq]
  rw [hfun]
  refine ContinuousOn.div (continuousOn_w_mul_sqrt.mul (continuousOn_fst.sub continuousOn_const))
    ((continuousOn_const.mul continuousOn_fst).mul (continuousOn_const.add continuousOn_fst)) ?_
  intro p hp
  have hz : (0:ℝ) < p.1 := (Set.mem_prod.mp hp).1
  positivity


theorem gam_ne_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

theorem Wt_eq (α z θ : ℝ) :
    Work.Spaces.Wt α z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]

theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  rw [show (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) from by
    funext p; rw [Wt_eq]]
  exact continuousOn_w.mul (continuousOn_sin_pow _)

theorem sqmul_unfold (X : ℝ) {z θ p : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (X * (Work.Spaces.w z * Real.sqrt z) * (Real.sin (2 * θ)) ^ (-(p / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * z * (X ^ 2 * (Real.sin (2 * θ)) ^ (-p)) := by
  rw [mul_sin_neg_half_sq (x := X * (Work.Spaces.w z * Real.sqrt z)) hθ hp,
      show (X * (Work.Spaces.w z * Real.sqrt z)) ^ 2 = X ^ 2 * (Work.Spaces.w z) ^ 2 * z from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hz.le]; ring]
  ring

theorem slot_unfold_gen (X : ℝ) {z θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 0) :
    (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (p / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (X ^ 2 * (Real.sin (2 * θ)) ^ (-p)) := by
  rw [mul_pow, div_sin_half_sq_gen hθ hp]
  ring



theorem sm_unfold_gen (X : ℝ) {z θ α : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hγ : Work.Spaces.gam α ≠ 0) :
    (X * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (X ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [Wt_eq]
  rw [show (X * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
      = ((X * Work.Spaces.w z) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      from by ring]
  rw [mul_sin_neg_half_sq (x := X * Work.Spaces.w z) hθ hγ, mul_pow]
  ring


theorem gam_lt_two {α : ℝ} (hα1 : α ≤ 1) : Work.Spaces.gam α < 2 := by
  rw [Work.Spaces.gam]; linarith

theorem gam_ne_two {α : ℝ} (hα1 : α ≤ 1) : Work.Spaces.gam α ≠ 2 :=
  ne_of_lt (gam_lt_two hα1)


/-- `σ^2 · σ^{-p} = σ^{2-p}` on `Iθ`. -/
theorem sin_two_sq_mul_neg_Iθ {θ p : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hp : p ≠ 2) :
    (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-p)
      = (Real.sin (2 * θ)) ^ (2 - p) := by
  have hs := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]
    have h2 : (0 : ℝ) ^ (2 - p) = 0 := Real.zero_rpow (fun h => hp (by linarith))
    rw [h2]; ring
  · rw [show (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ (2 : ℝ) from
      (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_add hspos]; ring_nf

/-- Inner (angular) integrability of a mixed slot of the `ℋ²`-integrand. -/
theorem slot_mixed_inner {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn
      (fun θ => (Work.Spaces.mixed j i h z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i h p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (((hso.mixed j i).continuousOn).mul (continuousOn_Wt α)).pow 2
  exact slot_inner hcont hmem (fun _ _ => sq_nonneg _)
    (fun z θ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 h z θ i j hi hij)

theorem slot_z_inner {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) (i : ℕ) (hi : i ≤ 2) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn
      (fun θ => (Work.Spaces.DzIter i h z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ :=
  fun z hz => Work.FTS.EllipticEst.integrableOn_zSummand α 2 hso hmem i hi hz

/-- `∫_θ h² σ^{-η}` is finite on the angular slice. -/
theorem integrableOn_hsq_sEta {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => (h z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hslot := slot_z_inner hso hmem 0 (by norm_num) z (Set.mem_Ici.mpr hz.le)
  have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt (w_pos_of_pos hz))
  have heq : ∀ θ ∈ Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2)⁻¹
        * (Work.Spaces.DzIter 0 h z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    rw [show Work.Spaces.DzIter 0 h z θ = h z θ from rfl]
    rw [slot_unfold_gen (h z θ) hθ eta_ne_zero]
    exact inv_mul_cancel_left₀ hw2 _
  exact IntegrableOn.congr_fun (hslot.const_mul _) heq measurableSet_Icc

/-- `∫_θ h²` is finite on the angular slice. -/
theorem integrableOn_hsq {α : ℝ} {h : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen h)
    (hmem : Work.Spaces.HkMem α 2 h) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => (h z θ) ^ 2) Work.Spaces.Iθ := by
  refine Integrable.mono' (integrableOn_hsq_sEta hso hmem hz)
    (aesm_sq_slice_of_SmoothOpen hso hz) ?_
  have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ‖(h z θ) ^ 2‖ ≤ (h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hle := sin_two_neg_eta_one_le hθ
      nlinarith [sq_nonneg (h z θ)]
  have hmeq : volume.restrict (Set.Ioo 0 (π / 2)) = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))
  rwa [hmeq] at h1

/-- `∫_θ (∂_θ h)² σ^{2-γ}` is finite on the angular slice. -/
theorem integrableOn_pth_sq {α : ℝ} {h : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α 2 h) {z : ℝ}
    (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => (Work.Spaces.pth h z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hγ0 : Work.Spaces.gam α ≠ 0 := gam_ne_zero hα
  have hγ2 : Work.Spaces.gam α ≠ 2 := gam_ne_two hα1
  have hslot := slot_mixed_inner hso hmem 0 1 (by norm_num) (by norm_num) z
    (Set.mem_Ici.mpr hz.le)
  have hw2 : ((Work.Spaces.w z) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt (w_pos_of_pos hz))
  have heq : ∀ θ ∈ Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2)⁻¹
        * (Work.Spaces.mixed 0 1 h z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    intro θ hθ
    rw [show Work.Spaces.mixed 0 1 h z θ = Work.Spaces.Dth h z θ from rfl]
    rw [show Work.Spaces.Dth h z θ
        = Real.sin (2 * θ) * Work.Spaces.pth h z θ from rfl]
    rw [sm_unfold_gen (Real.sin (2 * θ) * Work.Spaces.pth h z θ) hθ hγ0]
    rw [inv_mul_cancel_left₀ hw2]
    rw [mul_pow]
    rw [show (Real.sin (2 * θ)) ^ 2 * (Work.Spaces.pth h z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.pth h z θ) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        from by ring]
    rw [sin_two_sq_mul_neg_Iθ (p := Work.Spaces.gam α) hθ hγ2]
  exact IntegrableOn.congr_fun (hslot.const_mul _) heq measurableSet_Icc


end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.angmul6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! # `angmul6` — angular multiplication in `ℋ⁶`, with the `HkNorm`-shaped conclusion

Multiplication of an `ℋ⁶`-function by an angular profile `a : ℝ → ℝ` which is `C^∞` on the
open quadrant, bounded by `Ca` on `Iθ` and whose `D_θ`-iterates up to order `6` decay like
`Ca · sin 2θ`, is honest and costs `C · Ca` in the `ℋ⁶`-norm, with `C` universal in
`α ∈ (0,1]`.

The `HkSq`-form of this statement at every order `k` is
`Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le` (proved via the unit-profile pointwise bound
`Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int`, the rescaling `a = B · a'`,
`closed_of_interior`, `HkSq_le_of_integrand_le` and `HkMem_of_majorant`).  Here we

* feed it `k = 6` in the case `Ca > 0`, and take square roots (`HkNorm = √HkSq`), which is
  where the norm-shape `C · Ca` comes from (the squared estimate carries `Ca²`);
* dispose of the degenerate case `Ca = 0`: the hypothesis `|a θ| ≤ Ca = 0` on the nonempty
  `Iθ` forces `a` to vanish on `Iθ`, so `HkIntegrand` of `a · f` vanishes on `Iz ×ˢ Iθ`
  (the angular iterates are killed by `DthIter_angmul_eq_zero`) and both conjuncts collapse
  to `0`.
-/

theorem angmul6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (a : ℝ → ℝ) (f : Work.FTS.Galerkin.Fn) (Ca : ℝ),
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 6 (fun z θ => a θ * f z θ) ∧
    Work.Spaces.HkNorm α 6 (fun z θ => a θ * f z θ)
      ≤ C * Ca * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L3Rhs.ang_mul_HkSq_le 6
  refine ⟨Real.sqrt C₁, Real.sqrt_pos.mpr hC₁pos, ?_⟩
  intro α hα0 hα1 a f Ca hSO haB haIt hf hmem
  -- the nonemptiness of `Iθ` forces `0 ≤ Ca`
  have hCa : 0 ≤ Ca := le_trans (abs_nonneg (a 0)) (haB 0 Work.Spaces.zero_mem_Iθ)
  rcases eq_or_lt_of_le hCa with hCa0 | hCapos
  · -- ## `Ca = 0`: the profile vanishes on `Iθ`
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0 := by
      intro θ hθ
      have h1 := haB θ hθ
      rw [← hCa0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * f z θ) z θ = 0 := by
      intro z θ hθ
      rw [Work.Spaces.HkIntegrand]
      have h1 : (∑ i ∈ Finset.range (6 + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
        simp [ha0 θ hθ]
      have h2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hc
        · rw [Work.Spaces.mixed]
          rw [Work.Coercivity.DzIter_eq_zero_of_forall_eq_zero
            (Work.Spaces.DthIter i (fun z θ => a θ * f z θ)) θ
            (fun z' => Work.FTS.Nonlinear.N4Fields.DthIter_angmul_eq_zero a f ha0 i hc.1
              z' θ hθ)
            j z,
            zero_mul, sq, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    have hmem' : Work.Spaces.HkMem α 6 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant (M := fun _ _ => (0 : ℝ)) α 6 ?_ ?_ ?_ ?_
      · have h0 : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
          continuousOn_const
        refine h0.congr ?_
        intro p hp
        exact hzero p.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      · intro z hz; exact integrableOn_zero
      · have hthis : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (fun _ _ => (0 : ℝ)) z θ)
            = fun _ => (0 : ℝ) := by
          funext z; simp
        rw [hthis]
        exact integrableOn_zero
      · intro z hz θ hθ; rw [hzero z θ hθ]
    refine ⟨hmem', ?_⟩
    have hsq : Work.Spaces.HkSq α 6 (fun z θ => a θ * f z θ) = 0 := by
      rw [Work.Spaces.HkSq]
      have hinner : ∀ z : ℝ,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * f z θ) z θ)
            = 0 := by
        intro z
        rw [MeasureTheory.integral_eq_zero_of_ae]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hzero z θ hθ)
      simp only [hinner, integral_zero]
    rw [Work.Spaces.HkNorm, hsq, Real.sqrt_zero, ← hCa0]
    simp
  · -- ## `Ca > 0`: the `HkSq`-estimate of `ang_mul_HkSq_le 6`, then take square roots
    obtain ⟨hmem', hsq⟩ := hC₁ α hα0 hα1 a Ca hCapos hSO haB haIt f hf hmem
    refine ⟨hmem', ?_⟩
    have hCnn : 0 ≤ C₁ * Ca ^ 2 := by positivity
    have h1 : Real.sqrt (C₁ * Ca ^ 2) = Real.sqrt C₁ * Ca := by
      rw [Real.sqrt_mul hC₁pos.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hCa]
    calc Work.Spaces.HkNorm α 6 (fun z θ => a θ * f z θ)
        = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => a θ * f z θ)) := rfl
      _ ≤ Real.sqrt (C₁ * Ca ^ 2 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (C₁ * Ca ^ 2) * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
            Real.sqrt_mul hCnn _
      _ = Real.sqrt C₁ * Ca * Work.Spaces.HkNorm α 6 f := by
            rw [h1, Work.Spaces.HkNorm]

end

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.Rl2Open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK.Rows

set_option autoImplicit false

theorem Rl2Open : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ K * Work.FTS.Nonlin.Xn α f := by
  refine ⟨9, by norm_num, ?_⟩
  intro α g hα hα1 hso hmem
  set f : ℝ → ℝ → ℝ := fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z) with hf
  have hc : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hso.Dth.continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => 3 / (1 + p.1))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine ContinuousOn.div continuousOn_const
        (continuousOn_const.add continuous_fst.continuousOn) ?_
      intro p hp
      have hp1 : 0 < p.1 := hp.1
      exact ne_of_gt (by positivity)
    have h3 : ContinuousOn (fun p : ℝ × ℝ =>
        (3 / (1 + p.1)) * Function.uncurry (Work.Spaces.Dth g) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h2.mul h1
    refine h3.congr (fun p hp => ?_)
    simp only [Function.uncurry, hf]
    ring
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => f r θ ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f r θ ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => f p.1 p.2 ^ 2)
        (by change ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2) _
            exact hc.pow 2) hr
    refine MeasureTheory.Integrable.mono'
      ((hmem.1 r (Set.mem_Ici.mpr (le_of_lt hr))).const_mul 9) haesm ?_
    have hIoo2 : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
    rw [hIoo2]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hsqle : (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
      Work.FTS.Nonlinear.Pieces.dth_sq_le_HkIntegrand α g hα hr hθ
    have hfe : f r θ = (3 / (1 + r)) * Work.Spaces.Dth g r θ := by rw [hf]; ring
    have h3 : (3 / (1 + r)) ^ 2 ≤ 9 := by
      have hr' : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
      rw [div_pow, div_le_iff₀ (pow_pos hr' 2)]
      nlinarith [sq_nonneg r, le_of_lt (Set.mem_Ioi.mp hr)]
    rw [Real.norm_of_nonneg (sq_nonneg _), hfe, mul_pow]
    exact mul_le_mul h3 hsqle (sq_nonneg _) (by norm_num)
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2
        ≤ 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => ?_)
    have hslice := (Work.FTS.Nonlinear.Pieces.slice_energy_le_HkIntegrand α g hα hα1 hmem).1 r hr
    have hint : (∫ θ in Work.Spaces.Iθ, f r θ ^ 2)
        = (3 / (1 + r)) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [hf]; ring
    have h3 : (3 / (1 + r)) ^ 2 ≤ 9 := by
      have hr' : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
      rw [div_pow, div_le_iff₀ (pow_pos hr' 2)]
      nlinarith [sq_nonneg r, le_of_lt (Set.mem_Ioi.mp hr)]
    have hnn : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ
    calc (∫ θ in Work.Spaces.Iθ, f r θ ^ 2) * ((1 + r) / r) ^ 2
        = (3 / (1 + r)) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
            * ((1 + r) / r) ^ 2) := by rw [hint]; ring
      _ ≤ (3 / (1 + r)) ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
          mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
      _ ≤ 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
          mul_le_mul_of_nonneg_right h3 hnn
  have hΦint : MeasureTheory.IntegrableOn
      (fun z => 9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioi (0 : ℝ)) :=
    (hmem.2.mono_set Set.Ioi_subset_Ici_self).const_mul 9
  have hmain := Work.FTS.Nonlinear.Pieces.L12_zero_le_of_weight_bound hsl
    (Work.FTS.Nonlinear.Pieces.aesm_weighted_energy_of_continuousOn hc) hΦint hbd
  have hsqeval : (∫ r in Set.Ioi (0 : ℝ),
        9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = 9 * Work.Spaces.HkSq α 4 g := by
    rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]
    congr 1
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  have hsqrt : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = 3 * Work.FTS.Nonlin.Xn α g := by
    rw [hsqeval, Work.FTS.Nonlin.Xn]
    congr 1
    have h1 : (3 * Work.Spaces.HkNorm α 4 g) ^ 2 = 9 * Work.Spaces.HkSq α 4 g := by
      rw [Work.Spaces.HkNorm, mul_pow, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
      norm_num
    rw [← h1]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) (Work.Spaces.HkNorm_nonneg α 4 g))
  calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
      = |Work.Construction.L12 f 0| := by rw [hf]
    _ ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          9 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := hmain
    _ = 3 * (3 * Work.FTS.Nonlin.Xn α g) := by rw [hsqrt]
    _ = 9 * Work.FTS.Nonlin.Xn α g := by ring

end Work.FTS_MuLamOK.Rows
end
end
