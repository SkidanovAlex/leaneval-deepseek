import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.EllPkgAux.Slots
import Submission.Work.FTS.EllSol.EllPkgAux.uopSlotCore
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrder
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.StatResidual
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkStarPieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.SolutionDelivery.DatumOdd
-- ===== merged: Submission.Work.FTS.ClassC.VopAux.vopTracesPointwise_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The angular traces of the radial iterates of `Ξ`**, pointwise in `z`. -/
theorem vopTracesPointwise_classC (j : ℕ) (hj : j ≤ 6) :
    ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.ClassC.ClassC α g → Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α g Ψ hα hα4 hC hO z hz
  have hzpos : 0 < z := hz
  -- the straight unknown `Ψ̂ = shiftSing α g Ψ` and its level-`7` weak class
  have hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g Ψ) := hO.2.2
  have hshift := ellWeakPos_dzIter_shift_classC (α := α) (F := Work.Elliptic.orthSource g)
    (Ψ := Work.FTS.EllExist.shiftSing α g Ψ) (k := 7) (by norm_num) hweak j (by omega)
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllExist.shiftSing α g Ψ) :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen hweak
  have hCsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) := by
    have hL := Work.FTS.ClassC.smoothOpen_GbarSin_classC (α := α) (g := g) hα hC.reg hC.fsm
      hC.mem
    refine Work.FTS.EllipticEst.SmoothOpen.congr (hL.const_mul' (-1)) ?_
    intro z θ _ _ _
    ring
  -- the functional identity `Ξ = Ψ̂ - Ḡ(α,g)·sin 2θ`
  have hfun : Work.Elliptic.EllResid α g Ψ
      = fun z θ => Work.FTS.EllExist.shiftSing α g Ψ z θ
          + (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ) := by
    funext z θ
    rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
    simp only [Work.FTS.EllExist.shiftSing]
    ring
  -- the pointwise decomposition of the radial iterates on the open quadrant
  have hdecomp : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ) := by
    intro z θ hz h1 h2
    rw [hfun]
    rw [DzIter_add_on_Q0 j hPsm hCsm z θ hz h1 h2]
    rw [Work.FTS.EllipticEst.DzIter_mul_of_radial j (fun z => -(Work.Elliptic.Gbar α g z))
      (fun θ => Real.sin (2 * θ)) z θ]
  -- continuity of the slice of `D_z^j Ψ̂` on the closed interval, and its endpoint values
  have hkj : 1 ≤ 7 - j := by omega
  have hcont := Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts (7 - j) hkj α
    (Work.Spaces.DzIter j (Work.Elliptic.orthSource g))
    (Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ)) hα hshift z hzpos
  have h0 : Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z 0 = 0 := hshift.zero z
  have hp : Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z (Real.pi / 2) = 0 :=
    hshift.pi_half z
  have htl : Filter.Tendsto (fun θ : ℝ =>
      Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_zero_nhdsGT_of_continuousOn_Icc hcont h0
  have htr : Filter.Tendsto (fun θ : ℝ =>
      Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    tendsto_zero_nhdsLT_pi_half_of_continuousOn_Icc hcont hp
  obtain ⟨hcl, hcr⟩ := tendsto_zero_const_mul_sin_two
    (Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z)
  -- the two eventual equalities, on the two one-sided filters
  have hev0 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hzpos hθmem hθ
  have hev1 : (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ)
      =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
        + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
            * Real.sin (2 * θ)) := by
    change ∀ᶠ θ : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Ψ) z θ
        = Work.Spaces.DzIter j (Work.FTS.EllExist.shiftSing α g Ψ) z θ
          + Work.FTS.EllipticEst.rDzIter j (fun z => -(Work.Elliptic.Gbar α g z)) z
              * Real.sin (2 * θ)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity)] with θ hθ hθmem
    exact hdecomp z θ hzpos hθ hθmem
  exact ⟨Filter.Tendsto.congr' hev0.symm (by simpa using htl.add hcl),
    Filter.Tendsto.congr' hev1.symm (by simpa using htr.add hcr)⟩

end Work.FTS.ClassC.VopAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.uopSlotLe4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

-- The U/sin 2θ-slot at level 4 over EllClassOk 7, from the level-4 elliptic estimate and the
-- trace-class interpolation.  Route: the wall `Work.FTS.EllSol.PkgK5.wall_of_interp 4` applied to
-- the straightened unknown `EllSol.ellShift α g Ψ` (via `interpFamOfTrace_exists`), the layer
-- transfer `α‖D_z∂_θΞ‖ ≤ C(α‖D_z∂_θ(ellShift)‖ + ‖g‖)`, `divSinK5`, `thetaPoincareOpenTrace`,
-- `HkNorm_Dz_le_open` and `EllEstUnif 4` (with `orthSource_HkNorm_le`-type bounds).
theorem uopSlotLe4
    (hEst : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C)
    (hI : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.UopSlotLe4 C := by
  obtain ⟨Ce, hCepos, hEst'⟩ := hEst
  obtain ⟨K, hKpos, hcore⟩ := uopSlot_core
    (Work.FTS.EllSol.PkgK5.wall_of_interp 4 (by norm_num)
      (Work.FTS.EllSol.EllPkgAux.interpFamOfTrace_exists hI 4))
  obtain ⟨Cos, hCosp, hos⟩ := Work.FTS.EllSol.EllPkgAux.orthSourceHkNormClassC 4 (by norm_num)
  refine ⟨K * (Ce * Cos + 1), by positivity, ?_⟩
  intro α g Ψ hα hα4 hC hOk
  obtain ⟨hQ, hcore'⟩ := hcore α g Ψ hα hα4 hC hOk
  refine ⟨hQ, ?_⟩
  have hα1 : α ≤ 1 := by linarith
  -- the descended weak class of the straightened unknown, and the elliptic closure
  have hweak7 : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g)
      (Work.FTS.EllSol.ellShift α g Ψ) := by
    have hshift : Work.FTS.EllExist.shiftSing α g Ψ = Work.FTS.EllSol.ellShift α g Ψ := rfl
    rw [← hshift]
    exact hOk.2.2
  have hOsSm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) :=
    Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth hC.reg hC.fsm
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Ψ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (by
      intro n
      have h := hweak7.smooth n
      simpa only [Work.FTS.EllipticEst.Q0] using h)
  have hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (Work.FTS.EllSol.ellShift α g Ψ) :=
    Work.FTS.ClassC.ellWeakPos_descend (α := α) (k := 4) (l := 7)
      (F := Work.Elliptic.orthSource g) (Ψ := Work.FTS.EllSol.ellShift α g Ψ)
      (by norm_num) hOsSm hXsm hweak7
  have hgnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  have hle : α ^ 2 * Work.Spaces.HkNorm α 4
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
        + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
        + Work.Spaces.HkNorm α 4 g
      ≤ (Ce * Cos + 1) * Work.Spaces.HkNorm α 4 g := by
    have h1 := hEst' α (Work.Elliptic.orthSource g) (Work.FTS.EllSol.ellShift α g Ψ)
      hα hα4 hweak
    have h2 := hos α g hα hα1 hC
    have h3 : Ce * Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g)
        ≤ Ce * (Cos * Work.Spaces.HkNorm α 4 g) :=
      mul_le_mul_of_nonneg_left h2 hCepos.le
    nlinarith [h1, h3, hgnn, mul_nonneg hCepos.le hCosp.le]
  calc Work.Spaces.HkNorm α 4 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
      ≤ K * (α ^ 2 * Work.Spaces.HkNorm α 4
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
          + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
          + Work.Spaces.HkNorm α 4 g) := hcore'
    _ ≤ K * ((Ce * Cos + 1) * Work.Spaces.HkNorm α 4 g) :=
        mul_le_mul_of_nonneg_left hle hKpos.le
    _ = K * (Ce * Cos + 1) * Work.Spaces.HkNorm α 4 g := by ring

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Asm.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Asm

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The clamp congruence of the convergence package -/

/-- **The quadrant clamp does not change the convergence package.**  `clampQ F g₀` agrees with `F`
on the open quadrant — and `Q0` is open, so every `mixed`-slot of the two agrees at every point of
`Q0` (locality of `deriv`), while the slot-convergence clause of `ConvLocUnifH6` is uniform on
compacts of `Q0` and the `ℋᵏ`-integrals only see the quadrant (`clampQ_hkNorm`). -/
theorem ConvLocUnifH6.clampQ_congr {α B : ℝ} {G : ℕ → Fn} {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : ConvLocUnifH6 α B G (F τ)) :
    ConvLocUnifH6 α B G (slice (clampQ F g₀) τ) := by
  refine ⟨?_, clampQ_contDiffOn h.2.1, ?_⟩
  · intro K hK hKQ j i hji
    refine (h.1 K hK hKQ j i hji).congr_right ?_
    intro p hp
    exact (Work.FTS.StrongEps.mixed_congr_of_isOpen (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0
      (f := F τ) (g := slice (clampQ F g₀) τ)
      (fun q hq => (clampQ_of_mem hq.1 ⟨hq.2.1, hq.2.2⟩).symm) j i) (hKQ hp)
  · rw [clampQ_hkNorm]
    exact h.2.2

/-! ## The assembly data -/

/-- **The data of the E5 assembly**: the extraction output at the horizon `T`, its interface
properties (the extraction's own clauses, all read off `EpsUniformMem`), and the six supply
clauses of the module header. -/
structure EpsAsmData (α C₀ K B Cd T : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (ε : ℕ → ℝ) (G : ℕ → Fam) (φ : ℕ → ℕ) (F : ℝ → Fn) : Prop where
  /-- the horizon is positive. -/
  hT : 0 < T
  /-- the exponent range of the interface's energy estimates. -/
  hα : α ∈ Set.Ioc 0 1
  /-- the mollifier is admissible. -/
  hρ : IsSmoothKernel ρ
  /-- the datum vanishes on the two angular boundary lines (a *necessary* interface clause). -/
  hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0
  /-- the `ℋ⁶`-bound is non-negative. -/
  hB0 : 0 ≤ B
  /-- the mollification parameters are positive. -/
  hεpos : ∀ k : ℕ, 0 < ε k
  /-- and bounded by `1`. -/
  hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1
  /-- and tend to `0`. -/
  hε0 : Tendsto ε atTop (nhds 0)
  /-- the sub-sequence index is strictly increasing. -/
  hφ : StrictMono φ
  /-- the `ε`-solutions of the projected scheme. -/
  hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k)
  /-- their τ-regularity. -/
  hreg : ∀ k : ℕ, EpsRegP α ρ (ε k) T (G k)
  /-- all-order smoothness of the slices. -/
  hsmcd : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ,
    ContDiffOn ℝ n (Function.uncurry (slice (G k) τ)) Quad
  /-- honest `ℋ⁶`-membership of the slices. -/
  hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice (G k) τ)
  /-- the uniform `ℋ⁶`-bound of the slices. -/
  hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ B
  /-- the *projected* slices are class `C`. -/
  hC : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T,
    Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε k) (G k)) τ)
  /-- the uniform `ℋ⁴`-bound of the *projected* slices. -/
  hb4 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T,
    Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε k) (G k)) τ) ≤ C₀ * α ^ 2
  /-- the convergence package of the extraction. -/
  hconv : ∀ τ ∈ Set.Icc 0 T, ConvLocUnifH6 α B (fun n : ℕ => slice (G (φ n)) τ) (F τ)
  /-- the level-`1` τ-Lipschitz property of the approximants (from `EpsSlotLipP`). -/
  hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Quad → ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
      ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
        |Work.Spaces.mixed j i (slice (G (φ n)) τ) p.1 p.2
          - Work.Spaces.mixed j i (slice (G (φ n)) τ') p.1 p.2| ≤ C * |τ - τ'|
  /-- **(supply, Gap 1)** the elliptic image of the limit slice is `C²` on the open quadrant. -/
  hE2 : ∀ τ ∈ Set.Icc 0 T,
    ContDiffOn ℝ 2 (Function.uncurry (E (slice (clampQ F g₀) τ))) Quad
  /-- **(supply)** the `L₁₂`-zero mode of the mollified slice vanishes in the limit. -/
  hl12 : ∀ τ ∈ Set.Icc 0 T, Tendsto (fun n : ℕ => Work.Construction.L12
      (Jeps ρ (ε (φ n)) (slice (G (φ n)) τ)) 0) atTop (nhds 0)
  /-- **(supply, Gap 2)** the pointwise identification of the scheme's right-hand side. -/
  hlim : ∀ p : ℝ × ℝ, p ∈ Quad → ∀ s ∈ Set.Icc 0 T, Tendsto
    (fun n : ℕ => epsRHSP α ρ (ε (φ n)) Φs E (G (φ n)) s p.1 p.2) atTop
      (nhds (rhsFun α Φs E (clampQ F g₀) s p.1 p.2))
  /-- **(supply)** joint continuity of the limiting right-hand side on the interior, up to the
  horizon (`Icc 0 T` in the fake time, so that the `eqT` row can restrict it to a fixed point). -/
  hWc : ContinuousOn (fun p : ℝ × ℝ × ℝ => rhsFun α Φs E (clampQ F g₀) p.2.2 p.1 p.2.1)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)
  /-- **(supply)** the `ℋ³`-bound of the fake-time derivative at the limit. -/
  hdbd : ∀ τ : ℝ, 0 < τ → τ < T →
    Work.Spaces.HkMem α 3 (gdot (clampQ F g₀) τ) ∧
      Work.Spaces.HkNorm α 3 (gdot (clampQ F g₀) τ) ≤ Cd
  /-- **(supply)** the G2 approximation clause at the clamped family. -/
  hapx : ∀ T' : ℝ, 0 < T' → T' ≤ T → LimApproxOn α C₀ T' Φs E (clampQ F g₀)

end Work.FTS.StrongEps.E5Asm
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The horizon of the `n`-th piece: `Tn n = n + 1`.  (A local copy of `Assembly.Tn`, so that the
new chapter does not import the old E5 cone.) -/
def Tn (n : ℕ) : ℝ := (n : ℝ) + 1

theorem Tn_pos (n : ℕ) : 0 < Tn n := by
  simp only [Tn]
  exact lt_of_lt_of_le zero_lt_one (by norm_num)

theorem Tn_mono : Monotone Tn := fun m n h => by
  simp only [Tn]
  exact add_le_add (Nat.cast_le.mpr h) le_rfl

/-- The piece index of a fake time: `⌊τ⌋₊`. -/
def pidx (τ : ℝ) : ℕ := Nat.floor τ

theorem lt_Tn_pidx (τ : ℝ) (_hτ : 0 ≤ τ) : τ < Tn (pidx τ) := by
  have h := Nat.lt_floor_add_one τ
  simpa only [Tn, pidx] using h

/-- **The per-horizon solution data of the tower**.  `TowerAt α C₀ ρ Φs E g₀ n ε K' g` bundles
everything that `EpsUniformMem` provides at the horizon `Tn n` for the datum `ε`: the scheme's
solution, its τ-regularity and, at every fake time of `[0, Tn n]`, the interface clauses (smoothness,
the two `ℋ⁴`/`ℋ⁶`-memberships, the two ball bounds, the class-`C` clause and the joint `C¹`). -/
structure TowerAt (α C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (n : ℕ) (ε K' : ℝ) (g : Fam) : Prop where
  hsol : IsEpsSolP α ρ ε (Tn n) Φs E g₀ g
  hsm : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.EllipticEst.SmoothOpen (slice g τ)
  hmem4p : ∀ τ ∈ Set.Icc 0 (Tn n), Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ)
  hmem6 : ∀ τ ∈ Set.Icc 0 (Tn n), Work.Spaces.HkMem α 6 (slice g τ)
  hb4 : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2
  hb6 : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K'
  hC : ∀ τ ∈ Set.Icc 0 (Tn n), Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ)
  hjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 (Tn n))

/-- `TowerAt` restricts to a shorter fake-time interval. -/
theorem TowerAt.mono {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {ε K' T : ℝ} {g : Fam} (h : TowerAt α C₀ ρ Φs E g₀ n ε K' g) (hT : T ≤ Tn n) :
    IsEpsSolP α ρ ε (Tn n) Φs E g₀ g ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g τ)) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ)) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice g τ)) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K') ∧
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ)) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) :=
  ⟨h.hsol, fun τ hτ => h.hsm τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hmem4p τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hmem6 τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hb4 τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hb6 τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    fun τ hτ => h.hC τ ⟨hτ.1, le_trans hτ.2 hT⟩,
    h.hjoint.mono (by
      intro q hq
      exact ⟨hq.1, hq.2.1, hq.2.2.1, le_trans hq.2.2.2 hT⟩)⟩

/-- **`TowerAt` gives the τ-regularity class `EpsRegP`** used by the extraction: the joint `C¹` is
`hjoint`, and every slice is an `EpsDatumP` (its class-`C` conjunct is the *projected* slice, which
is `TowerAt.hC` after `slice_JfamP`). -/
theorem TowerAt.toEpsRegP {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {ε K' : ℝ} {g : Fam} (h : TowerAt α C₀ ρ Φs E g₀ n ε K' g) :
    EpsRegP α ρ ε (Tn n) g :=
  ⟨h.hjoint, fun τ hτ =>
    ⟨h.hsm τ hτ, h.hmem6 τ hτ, by simpa only [slice_JfamP] using h.hC τ hτ⟩⟩

/-- **The class-`C` clause of `TowerAt` as `EpsClass`** (the input of the fixed-`ε` uniqueness D1):
at the same datum `ε` and with the horizon-`n` level-`6` bound, every slice of a tower solution
lies in `EpsClass α ρ ε C₀ B` for any `B` dominating `K'`. -/
theorem TowerAt.epsClass {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {ε K' B T : ℝ} {g : Fam} (h : TowerAt α C₀ ρ Φs E g₀ n ε K' g)
    (hB : K' ≤ B) (hT : T ≤ Tn n) :
    ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₀ B (slice g τ) := by
  intro τ hτ
  have hτ' : τ ∈ Set.Icc 0 (Tn n) := ⟨hτ.1, le_trans hτ.2 hT⟩
  exact ⟨h.hsm τ hτ', h.hmem6 τ hτ', le_trans (h.hb6 τ hτ') hB,
    by simpa only [slice_JfamP] using h.hC τ hτ', h.hb4 τ hτ'⟩

end Work.FTS.StrongEps.E5G
end
end
