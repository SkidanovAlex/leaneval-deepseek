import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkPairingSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.FK_abs_le_of_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FK_abs_le_of_classC` — the angular moment of a `ClassC` profile

`FK f z = ∫_θ f(z,θ) K(θ) dθ` with `K(θ) = 3 sinθ cos²θ`.  On the class `ClassC α` the
angular moment is dominated, **uniformly in `α ∈ (0,1]` and in `z > 0`**, by the level-`6`
`ℋ`-size:

  `|FK f z| ≤ 7 · Xn6 α f`   whenever `ClassC α f`.

The two inputs are

* `FKAbsLeSqrtEta` — the weighted angular Cauchy–Schwarz
  `|FK Y z| ≤ 4 √(∫_θ sin(2θ)^{-η} Y(z,θ)²)`;
* `fkSliceSup_sliceSupGraded` — the uniform-in-`z` slice bound
  `∫_θ sin(2θ)^{-η} (D_z^jD_θ^i f z θ)² ≤ 3 HkSq α k f` for `i + j + 1 ≤ k`
  (the window form of the radial Hardy inequality, which is what removes the
  degeneracy of the angular Hardy constant `1/√(γ-1)` as `α → 0`).

Taking `(j,i) = (0,0)`, `k = 6` turns the angular moment into `√48 · Xn6 α f`, and `√48 ≤ 7`.
-/

namespace Work.FTS.StrongEps

open MeasureTheory

theorem FK_abs_le_of_classC :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α Ce : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α f → Work.FTS.StrongGlobal.Xn6 α f ≤ Ce →
      ∀ z ∈ Set.Ioi 0, |Work.Construction.FK f z| ≤ C * Ce := by
  refine ⟨7, by norm_num, ?_⟩
  intro α Ce hα f hf hXn z hz
  have hα0 : 0 < α := hα.1
  -- `ClassC` is `ℋ⁷`-honest; descend to `ℋ⁶`
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 6 (by norm_num) hf.mem
  -- integrability of the weighted squared slice of `f` at the fixed `z > 0`
  have hint : MeasureTheory.IntegrableOn
      (fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_slice_integrable
      (α := α) hα0 hf.reg hmem6 (j := 0) (i := 0) (by norm_num) hz
  -- the weighted angular Cauchy–Schwarz
  have hFK := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKAbsLeSqrtEta
    (z := z) (Y := f) hint
  -- the uniform-in-`z` slice bound, at the top slot `(j,i) = (0,0)`
  have hslice := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup_sliceSupGraded
    (α := α) hα0 hf.reg hmem6 0 0 (by norm_num) z hz
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
  have hCe0 : 0 ≤ Ce := le_trans hXnn hXn
  have hstep : Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2)
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hslice
  have hsqrt48 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
    rw [show (48 : ℝ) = (4 * Real.sqrt 3) ^ 2 from by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have h48 : Real.sqrt 48 ≤ 7 := by
    rw [show (7 : ℝ) = Real.sqrt 49 from by
      rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc |Work.Construction.FK f z|
      ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (f z θ) ^ 2) := hFK
    _ ≤ 4 * Real.sqrt (3 * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = Real.sqrt 48 * Work.FTS.StrongGlobal.Xn6 α f := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        rw [show Work.FTS.StrongGlobal.Xn6 α f
            = Real.sqrt (Work.Spaces.HkSq α 6 f) from rfl]
        rw [hsqrt48]
        ring
    _ ≤ 7 * Ce := by
        calc Real.sqrt 48 * Work.FTS.StrongGlobal.Xn6 α f
            ≤ Real.sqrt 48 * Ce := mul_le_mul_of_nonneg_left hXn (Real.sqrt_nonneg _)
          _ ≤ 7 * Ce := mul_le_mul_of_nonneg_right h48 hCe0

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.RowFKfAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-- Almost every `θ ∈ Iθ` lies in the open interval. -/
private theorem ae_Ioo_Iθ_row :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## §1. Monotonicity of the `ℋᵏ`-integrand in the level -/





/-! ## §3. Prices of the radial slots `D_z^k (FK f)` -/

/-- The one-variable and two-variable iterates agree on radial functions. -/
theorem dzdIter_fk_eq {f : ℝ → ℝ → ℝ} {k : ℕ} {z θ : ℝ} :
    Work.Spaces.DzIter k (fun z _ => Work.Construction.FK f z) z θ
      = Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z :=
  Work.Elliptic.DzIter_rad _ k z θ

/-- **Pointwise price of the radial slots of the angular moment** (a.e. in `z`). -/
theorem fkPt_row : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 7 f → ∀ k : ℕ, k ≤ 6 →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ C * Work.Spaces.HkSq α (k + 1) f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  refine ⟨C, hCpos, ?_⟩
  intro α f hα hO hmem6 hmem7 k hk
  filter_upwards [hC hα hO hmem6 hmem7 k hk] with z hz
  simpa only [dzdIter_fk_eq] using hz

/-- **The angular moment is bounded by `C·M` pointwise on `(0,∞)`.** -/
theorem fkAbs_row : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      ∀ z : ℝ, 0 < z → |Work.Construction.FK f z| ≤ C * M := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  refine ⟨4 * Real.sqrt C₀, by positivity, ?_⟩
  intro α hαmem f M hQ h7 hM z hz
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hQ.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hQ.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hO 4 (by norm_num) hmem6
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hO.continuousOn hz
  have hsqint : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
    have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
      one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
    refine MeasureTheory.Integrable.mono' (hmem6.1 z (Set.mem_Ici.mpr hz.le))
      (haesm.pow 2) ?_
    filter_upwards [ae_Ioo_Iθ_row] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hWhzWm := Work.FTS.H2.Whz_Wm_sq α hα z θ ⟨hθ.1.le, hθ.2.le⟩
    have hsin1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
    calc (f z θ) ^ 2 = 1 * (f z θ) ^ 2 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (f z θ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact le_mul_of_one_le_right (sq_nonneg _) hsin1
      _ = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            * (f z θ) ^ 2 := by ring
      _ = (Work.FTS.H2.Whz z θ) ^ 2 * (f z θ) ^ 2 := by rw [hWhzWm.1]
      _ = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.H2.Whz_eq]; ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
          have hh := Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 0 (by norm_num)
          simpa only [Work.Spaces.DzIter_zero] using hh
  have hslice := hC₀ α f 0 hα hα1 hO hmem4 (by norm_num) z hz
  have hFK := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le hz hsqint haesm
  have hXn : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
  have h1 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      ≤ Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hslice
  have h2 : Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f)
      = Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f := by
    rw [Real.sqrt_mul hC₀pos.le, hXn]
  calc |Work.Construction.FK f z|
      ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) := hFK
    _ ≤ 4 * (Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 4 * (Real.sqrt C₀ * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM
          (Real.sqrt_nonneg _)) (by norm_num)
    _ = (4 * Real.sqrt C₀) * M := by ring

/-! ## §4. Auxiliary: the `sin²θ`-shift of the `D_θ`-iterates -/

/-- `D_θ`-iterates commute with the shift `f ↦ D_θf`. -/
theorem dthIter_succ_shift (a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter a (Work.Spaces.Dth f) = Work.Spaces.DthIter (a + 1) f := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, ← Work.Spaces.DthIter_succ]

end

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthZeroSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fkRowDthZeroSlot` — integrability of the `(FK f)·ρ·(D_z^6D_θ f)·(D_z^6 f)` slot

This is the integrability side-condition of the level-six `(f,K)`-row at the slot
`(a,b) = (1,6)`: for a datum `f` in the level-six class `T6Coef.DatData α f M` and a leaf
weight `ρ` of the order-zero slot (`IsLeafW α 0 ρ`, i.e. `ρ` is `w²sin(2θ)^{-η}` or `w²`),

  `p ↦ FK f p.1 · (ρ p.1 p.2 · D_z^6D_θf p.1 p.2 · D_z^6f p.1 p.2)`

is integrable for the product of the restrictions of Lebesgue measure to `Iz` and `Iθ`.

The content is a pointwise domination: `|FK f| ≤ CM` (`fkSliceSup`) and, by AM–GM,
`ρ·|D_z^6D_θf|·|D_z^6f| ≤ ρ(D_z^6D_θf)²/2 + ρ(D_z^6f)²/2 ≤ HkIntegrand α 7 f`, because the
leaf weight `ρ` is dominated both by the `η`-block weight `w²sin(2θ)^{-η}` (which is the
weight of the pure `D_z^6`-slot of `ℋ^6`) and by the `γ`-block weight `Wt²` (the weight of
the mixed `D_z^6D_θ`-slot of `ℋ^7`), and `HkIntegrand α 6 f ≤ HkIntegrand α 7 f`.  The
result follows from `Integrable.mono'` once the joint integrability of `uncurry
(HkIntegrand α 7 f)` is available — that is the Tonelli bookkeeping of
`HkIntegrand_prod_integrable_open` below.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- Almost everywhere with respect to `(volume|Iz).prod (volume|Iθ)`, a point lies in the open
quadrant.  (`Iz = [0,∞)` and `Iθ = [0,π/2]` agree with the open half-line/interval up to the
null coordinate hyperplanes.) -/
private theorem ae_mem_openQuadrant :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have hprod : ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet

/-- **Joint integrability of the uncurried `ℋ^k`-integrand.**  For a datum which is `C^∞` on
the open quadrant and honestly in `ℋ^k`, the `ℋ^k`-integrand is integrable for the product of
the restrictions of Lebesgue measure to `Iz` and `Iθ`.  Routed through
`Work.Spaces.integrable_prod_of_iterated` (nonnegative Tonelli): the integrand is nonnegative,
a.e. strongly measurable (continuous on the open quadrant), its angular slices are integrable
(`HkMem.1`) and its radial marginal is integrable (`HkMem.2`). -/
private theorem HkIntegrand_prod_integrable_open (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ}
    (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  haveI : MeasureTheory.SFinite (MeasureTheory.volume.restrict Work.Spaces.Iz) := inferInstance
  haveI : MeasureTheory.SFinite (MeasureTheory.volume.restrict Work.Spaces.Iθ) := inferInstance
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Spaces.HkIntegrand α k g))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hsg.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => hmg.1 z hz
  exact (Work.Spaces.integrable_prod_of_iterated
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ) haesm hslice hmg.2).1

/-- Every leaf weight is continuous on the open quadrant (it is one of the canonical weights
`w²sin(2θ)^{-q}`, `q ∈ {0, η, γ}`). -/
private theorem leaf_continuousOn_openQuadrant {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rcases hρ with rfl | rfl | ⟨_ha, rfl⟩
  · simpa only [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.SlotT2.canonW]
      using Work.FTS.TransportS.SlotT2.continuousOn_canonW Work.Spaces.eta
  · have h : Work.FTS.TransportS.leafOne = Work.FTS.TransportS.SlotT2.canonW 0 := by
      funext z θ
      simp [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.SlotT2.canonW]
    rw [h]
    exact Work.FTS.TransportS.SlotT2.continuousOn_canonW 0
  · simpa only [Work.FTS.TransportS.leafGam, Work.FTS.TransportS.SlotT2.canonW]
      using Work.FTS.TransportS.SlotT2.continuousOn_canonW (Work.Spaces.gam α)

/-- The angular moment `z ↦ FK f z` is continuous on the open quadrant as a function of
`(z,θ)` (it only depends on `z`). -/
private theorem fk_continuousOn_openQuadrant {f : ℝ → ℝ → ℝ}
    (h : ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.FK f p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  h.comp continuous_fst.continuousOn (fun _ hp => hp.1)

/-- `|a·b| ≤ (a² + b²)/2`. -/
private theorem abs_mul_le_half_sq_add (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  rw [abs_mul]
  linarith

/-! ## The two pointwise slot dominations -/

/-- The leaf weights of the order-zero slot are dominated by the square of the `η`-block weight
`Whz = w/sin(2θ)^{η/2}` on the open quadrant.  (`leafGam` is excluded by `IsLeafW α 0`.) -/
private theorem leaf_le_Whz_sq_prv {α : ℝ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α 0 ρ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha, _⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Whz_sq z θ hs]
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
  · exact absurd ha (by omega)

/-- Every leaf weight is dominated by the square of the `γ`-block weight `Wt` on the open
quadrant. -/
private theorem leaf_le_Wt_sq {α : ℝ} (hα : 0 < α) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α 0 ρ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  have h1 : ρ z θ ≤ Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    (leaf_le_Whz_sq_prv hρ hθ).trans (le_of_eq (Work.FTS.H2.hbi_Whz_sq z θ hs))
  rw [Work.Spaces.bt_Wt_sq α z θ hα hθI]
  exact h1.trans (mul_le_mul_of_nonneg_left (fkSliceSup_sin_rpow_le hα hθ) (sq_nonneg _))

/-! ## The target -/

theorem fkRowDthZeroSlot : ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.Construction.FK f p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
  intro α hα f M ρ hD hρ
  have hα0 : 0 < α := hα.1
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hD.bdd
  have hCM : 0 ≤ C * M := mul_nonneg hCpos.le hM0
  have hfkbd : ∀ z : ℝ, 0 < z → |Work.Construction.FK f z| ≤ C * M :=
    (hC α hα f M hD).1
  have hfkcont : ContinuousOn (fun z => Work.Construction.FK f z) (Set.Ioi 0) :=
    (hC α hα f M hD).2.1
  refine MeasureTheory.Integrable.mono'
    (g := fun p : ℝ × ℝ => (C * M) * Work.Spaces.HkIntegrand α 7 f p.1 p.2) ?_ ?_ ?_
  · -- the majorant is integrable
    exact (HkIntegrand_prod_integrable_open α 7 hD.sm hD.h7).const_mul (C * M)
  · -- a.e. strong measurability of the slot
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    exact (fk_continuousOn_openQuadrant hfkcont).mul
      (((leaf_continuousOn_openQuadrant hρ).mul
        (hD.sm.mixed 6 1).continuousOn).mul (hD.sm.mixed 6 0).continuousOn)
  · -- the pointwise domination, a.e.
    filter_upwards [ae_mem_openQuadrant] with p hp
    obtain ⟨hz, hθ⟩ := hp
    have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hs : 0 ≤ Real.sin (2 * p.2) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
    have hρnn : 0 ≤ ρ p.1 p.2 :=
      (Work.FTS.TransportS.IsLeafW_le α hα0 hρ).1 p.1 p.2 hz hθ.1 hθ.2
    -- the mixed slot `D_z^6D_θf` against the `γ`-weight
    have hb1 : ρ p.1 p.2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
      have hle := leaf_le_Wt_sq (α := α) hα0 hρ hz hθ
      have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α 7 f p.1 p.2 1 6 (le_refl 1)
        (by norm_num)
      calc ρ p.1 p.2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
          ≤ (Work.Spaces.Wt α p.1 p.2) ^ 2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed 6 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := hsq
    -- the pure radial slot `D_z^6f` against the `η`-weight
    have hb0 : ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
      have hle := leaf_le_Whz_sq_prv hρ (z := p.1) (θ := p.2) hθ
      have hsq := fkSliceSup_dz_slot_le α 7 f hz hθ (j := 6) (by norm_num)
      rw [Work.Spaces.mixed_zero_right]
      calc ρ p.1 p.2 * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2
          ≤ (Work.FTS.H2.Whz p.1 p.2) ^ 2 * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
            rw [Work.FTS.H2.hbi_Whz_sq p.1 p.2 hs]; ring
        _ ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := hsq
    -- AM–GM and the two slot bounds
    have hmain : |ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2|
        ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
      have habs : |ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
            * Work.Spaces.mixed 6 0 f p.1 p.2|
          = ρ p.1 p.2 * |Work.Spaces.mixed 6 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2| := by
        simp only [abs_mul, abs_of_nonneg hρnn]
        ring
      rw [habs]
      calc ρ p.1 p.2 * |Work.Spaces.mixed 6 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2|
          ≤ ρ p.1 p.2 * (((Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
                + (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left (abs_mul_le_half_sq_add _ _) hρnn
        _ = (ρ p.1 p.2 * (Work.Spaces.mixed 6 1 f p.1 p.2) ^ 2
              + ρ p.1 p.2 * (Work.Spaces.mixed 6 0 f p.1 p.2) ^ 2) / 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by linarith [hb1, hb0]
    rw [Real.norm_eq_abs]
    calc |Work.Construction.FK f p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)|
        = |Work.Construction.FK f p.1| * |ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
            * Work.Spaces.mixed 6 0 f p.1 p.2| := by rw [abs_mul]
      _ ≤ (C * M) * Work.Spaces.HkIntegrand α 7 f p.1 p.2 :=
          mul_le_mul (hfkbd p.1 hz) hmain (abs_nonneg _) hCM

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `fkShiftHigh_shiftF` — the `F²`-energy of the shifted `D_z`-row of `FK f`

For a level-six datum (`DatData α f M`), `4 ≤ b₁ ≤ 6` and a leaf weight
`ρ` of the angular slot `0`, the product-measure integral of

  `(D_z^{b₁}(FK f) z)² · ρ z θ · (D_z^{6-b₁}D_θ f z θ)²`

is finite and bounded by `C · HkSq α 4 f · (1 + HkSq α 6 f)` with a universal `C`.

The two analytic ingredients (both already in the tree) are

* the *uniform in `z`* angular slice bound `fkSliceSup_sliceSupGraded` at level `4`:
  `∫_θ sin(2θ)^{-η}(D_z^{6-b₁}D_θ f z θ)² ≤ 3 |f|²_{ℋ⁴}` for every `z > 0` — this is
  exactly where `b₁ ≥ 4` is used (`1 + (6-b₁) + 1 ≤ 4`);
* the *integrated* radial bound `fkMomentJetSq`: `∫_z (D_z^{b₁}(FK f) z)² w(z)² ≤ C|f|²_{ℋ⁶}`.

Since `ρ ≤ w² sin(2θ)^{-η}` on the quadrant and the radial factor `(D_z^{b₁}(FK f))²`
is constant in `θ`, Fubini turns the double integral into `∫_z (D_z^{b₁}(FK f) z)² ·
(∫_θ ρ z θ (D_z^{6-b₁}D_θ f z θ)²)`, whose inner factor is `≤ w(z)²·3|f|²_{ℋ⁴}`.
-/

/-- The `D_z`-jet of the angular moment, lifted to the product space, is a.e. strongly
measurable: it agrees a.e. with the angular moment of the `D_z`-jet, which is the
`θ`-marginal of a function continuous on the open quadrant. -/
private theorem aesm_fst_dzdIter_FK {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f)
    {k : ℕ} (hk : k ≤ 6) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) p.1)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter k f p.1 p.2 * Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hF.DzIter k).continuousOn).mul (by unfold Work.Spaces.K; fun_prop)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    simpa only [Work.Construction.FK] using hjoint.integral_prod_right'
  have hae : (fun z : ℝ => Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => Work.Construction.FK (Work.Spaces.DzIter k f) z) := by
    have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hF hmem k hk
    filter_upwards [h] with z hz
    rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.FK f z) k z 0]
    exact hz 0
  exact (h2.congr hae.symm).comp_fst

theorem fkShiftHigh_shiftF : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (M : ℝ) (b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      4 ≤ b₁ → b₁ ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
            * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
            * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ C * Work.Spaces.HkSq α 4 f * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := fkMomentJetSq
  refine ⟨3 * C₁, mul_pos (by norm_num) hC₁pos, ?_⟩
  intro α hαI f M b₁ ρ hD hb₁lo hb₁hi hρ
  obtain ⟨hα0, hα1⟩ := hαI
  obtain ⟨hsm, h6, h7, hvanish, haxis, hbdd⟩ := hD
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) h6
  have hS4 : (0 : ℝ) ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hS6 : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  obtain ⟨hMJint, hMJval⟩ := hC₁ α ⟨hα0, hα1⟩ f hsm h6 b₁ hb₁hi
  -- a.e. strong measurability of the three factors
  have haesm_g : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (aesm_fst_dzdIter_FK hsm h6 hb₁hi).pow 2
  have haesm_A : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_mixed hsm (6 - b₁) 1).pow 2
  have haesm_H : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (haesm_g.mul
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_canonW Work.Spaces.eta)).mul haesm_A
  have haesm_G : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    (haesm_g.mul (Work.FTS.StrongPersist.H6Rows.Npair6BWork.aesm_leafW hρ)).mul haesm_A
  -- nonnegativity of the dominating integrand on the angular interval
  have hHnn : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2 := by
    intro z θ hθ
    have hσ : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    refine mul_nonneg (mul_nonneg (sq_nonneg _) ?_) (sq_nonneg _)
    rw [Work.FTS.TransportS.SlotT2.canonW]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ _)
  -- the uniform-in-`z` angular slice bound, with the radial factor pulled out
  have hslice_bd : ∀ z : ℝ, 0 < z →
      (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f) := by
    intro z hz
    have hbase := fkSliceSup_sliceSupGraded hα0 hsm hmem4 (j := 6 - b₁) (i := 1)
      (by omega) z hz
    have hfac : (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (∫ θ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hcongr : (fun θ => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
            * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
            * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)
          = (fun θ => ((Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
              * (Work.Spaces.w z) ^ 2) * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)) := by
        funext θ
        rw [Work.FTS.TransportS.SlotT2.canonW]
        ring
      rw [hcongr, MeasureTheory.integral_const_mul]
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hbase (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- integrability of the angular slices of the dominating integrand
  have hsliceH : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne hzI
    have hz : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
    have hbase := fkSliceSup_slice_integrable hα0 hsm hmem4 (j := 6 - b₁) (i := 1)
      (by omega) hz
    have heq : (fun θ => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)
        = (fun θ => ((Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
            * (Work.Spaces.w z) ^ 2) * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2)) := by
      funext θ
      rw [Work.FTS.TransportS.SlotT2.canonW]
      ring
    rw [heq]
    exact hbase.const_mul _
  -- the dominating radial majorant is integrable
  have hdomint : MeasureTheory.Integrable
      (fun z => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hMJint.mul_const (3 * Work.Spaces.HkSq α 4 f)
  -- integrability of the norm-marginal (`integrable_prod_iff` needs the norm)
  have hmargnn : ∀ z : ℝ, 0 ≤ ∫ θ,
      ‖(Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2‖
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun z => MeasureTheory.integral_nonneg (fun θ => norm_nonneg _)
  have hOutNorm : MeasureTheory.Integrable
      (fun z => ∫ θ,
        ‖(Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2‖
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hdomint ?_ ?_
    · exact (haesm_H.norm).integral_prod_right'
    · rw [MeasureTheory.ae_restrict_iff'
        (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne hzI
      have hz : 0 < z := lt_of_le_of_ne hzI (Ne.symm hne)
      rw [Real.norm_of_nonneg (hmargnn z)]
      rw [MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Real.norm_of_nonneg (hHnn z θ hθ))]
      exact hslice_bd z hz
  -- Fubini for the dominating integrand
  have hIntH : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM := by
    rw [MeasureTheory.integrable_prod_iff haesm_H]
    exact ⟨hsliceH, hOutNorm⟩
  have hOutMarg : MeasureTheory.Integrable
      (fun z => ∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz →
        (∫ θ, ‖(Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      filter_upwards with z _
      exact MeasureTheory.setIntegral_congr_fun
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ hθ => Real.norm_of_nonneg (hHnn z θ hθ))
    exact hOutNorm.congr ((MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)).mpr hae)
  have hmarg_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f) := by
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hne hzI
    exact hslice_bd z (lt_of_le_of_ne hzI (Ne.symm hne))
  have hvalH : (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
        * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integral_prod
      (fun p : ℝ × ℝ => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
        * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2) hIntH
  have hboundH : (∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ 3 * C₁ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 6 f := by
    calc (∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ≤ ∫ z, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
            * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) :=
          MeasureTheory.integral_mono_ae hOutMarg hdomint hmarg_le
      _ = (3 * Work.Spaces.HkSq α 4 f)
            * (∫ z, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
                * (Work.Spaces.w z) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) := by
          rw [show (fun z => (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
                * (Work.Spaces.w z) ^ 2 * (3 * Work.Spaces.HkSq α 4 f))
              = (fun z => (3 * Work.Spaces.HkSq α 4 f)
                * ((Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
                  * (Work.Spaces.w z) ^ 2)) from by
            funext z; ring]
          rw [MeasureTheory.integral_const_mul]
      _ ≤ (3 * Work.Spaces.HkSq α 4 f) * (C₁ * Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left hMJval (mul_nonneg (by norm_num) hS4)
      _ = 3 * C₁ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 6 f := by ring
  -- the target integrand is dominated by the `canonW η` one
  have hpt_le : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM,
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ≤ (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2 := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_PM_Q0] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    have hρle := Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_le_canonW_eta
      hρ p.1 p.2 hz hθ0 hθ1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρle (sq_nonneg _)) (sq_nonneg _)
  have hGnn : ∀ᵐ p ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM, 0 ≤
      (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2 := by
    filter_upwards [Work.FTS.StrongPersist.H6Rows.Npair6BWork.ae_PM_Q0] with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.leafW_nonneg hρ p.1 p.2 hz hθ0 hθ1))
      (sq_nonneg _)
  have hIntG : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2)
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    MeasureTheory.Integrable.mono' hIntH haesm_G
      (by filter_upwards [hpt_le, hGnn] with p h1 h2
          rw [Real.norm_of_nonneg h2]; exact h1)
  have hvalG : (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM)
      ≤ ∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
        * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
        * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
      ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM :=
    MeasureTheory.integral_mono_ae hIntG hIntH hpt_le
  constructor
  · exact hIntG
  · calc (∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * ρ p.1 p.2 * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
        ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM)
        ≤ ∫ p, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta p.1 p.2
          * (Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2) ^ 2
        ∂Work.FTS.StrongPersist.H6Rows.Npair6BWork.PM := hvalG
      _ = ∫ z, (∫ θ, (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z) ^ 2
          * Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
          * (Work.Spaces.mixed (6 - b₁) 1 f z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := hvalH
      _ ≤ 3 * C₁ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 6 f := hboundH
      _ ≤ 3 * C₁ * Work.Spaces.HkSq α 4 f * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg (by norm_num) hC₁pos.le) hS4)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
