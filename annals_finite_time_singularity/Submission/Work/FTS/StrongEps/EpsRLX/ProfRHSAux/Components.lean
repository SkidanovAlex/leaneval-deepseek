import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Basic
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.gRHS_tendsto
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXR5L.mubarData
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.vopPert_theta_holder
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.SmHm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.SmHm` — the smoothness and `ℋ⁶`-honesty of the `N`-block `blkN`

The first two fields of `BData α w K (blkN α Φs w Φg)`, for the hypotheses of
`blocks/N_BData`:

* `SmoothOpen (blkN α Φs w Φg)`, from `ClassCRHS.SmoothOpenRHS` (open-quadrant `C^∞` of `N`);
* `HkMem α 6 (blkN α Φs w Φg)`, from `Apriori4Proofs.nMem6_of_parts`.

The only bridges needed are the repackaging `ClassC.EllPkgK → StrongPersist.EllPkgK` (the two
structures carry the two copies of `IsBslSolPos`) and the extraction of `H6Adm α w` from
`ClassC α w` plus the off-quadrant vanishing hypothesis (`H6Adm_of_classC_of_eqzero`).
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The two copies of the elliptic package at order `k` agree (they differ only in the copy of
`IsBslSolPos` they carry). -/
theorem ellPkgK_toStrongPersist {α : ℝ} {k : ℕ} {Ce : ℝ} {g Φg : Fn}
    (h : Work.FTS.ClassC.EllPkgK α k Ce g Φg) :
    Work.FTS.StrongPersist.EllPkgK α k Ce g Φg where
  sol := Work.FTS.StrongEps.isBslSolPos_toStrongPersist h.sol
  smooth := h.smooth
  R := h.R
  U := h.U
  V := h.V

/-- **`SmoothOpen` of the `N`-block.** -/
theorem smoothOpen_blkN {α Ce Cs : ℝ} {Φs w Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hw : Work.FTS.ClassC.ClassC α w)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg) :=
  Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα hα1 hw hgo hstar.toStarPkgo2 |>.2.2.2.2

/-- **`HkMem α 6` of the `N`-block.** -/
theorem hkMem_blkN {α Ce Cs : ℝ} {Φs w Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hw : Work.FTS.ClassC.ClassC α w)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hK : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg)
    (hstar : Work.FTS.StrongPersist.StarPkg6 α Cs Φs) :
    Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg) :=
  (Work.FTS.StrongEps.E4R3.Apriori4Proofs.nMem6_of_parts hα hα1
    (Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hw hzero) hw.mem hgo.smooth
    hstar.smooth (ellPkgK_toStrongPersist hK) hstar).2

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ZTrunc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.ZTrunc` — the truncation `w ↦ ztrunc w` and its `ℋᵏ`-invariance

The target `blocks/N_BData` states its vanishing hypothesis in the **weak** form
`0 < z → θ ∉ Ioo 0 (π/2) → w z θ = 0` (nothing is assumed for `z ≤ 0`), whereas the tree's
`H6Adm`-based machinery (`H6Adm_of_classC_of_eqzero` and hence every `H6Adm` producer) needs the
**strong** form `¬ (0 < z ∧ θ ∈ Ioo 0 (π/2)) → w z θ = 0`.

The remedy is the truncation `ztrunc w z θ = if 0 < z then w z θ else 0`, which

* agrees with `w` on the open half-plane `z > 0` — in particular on the open quadrant, so all the
  `ℋᵏ`-quantities (which are integrals over `{z ≥ 0} × [0,π/2]`, with the weight
  `w(z) = (1+z)²/z²` vanishing at `z = 0`) are unchanged
  (`HkSq_congr_open`, `H6Pair6Aux.HkMem_congr_Qd`), and
* satisfies the strong vanishing form as soon as `w` satisfies the weak one.

Everything the estimates need about `w` (`ClassC`, the elliptic packages, `HkMem`, `HkSq`) can
therefore be transported to `ztrunc w`; the transfer lemmas for `ClassC` and the two elliptic
packages live in `N_aux.ZTruncClassC` and `N_aux.ZTruncPkgs`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The truncation of `w` to the half-plane `z > 0` (zero elsewhere). -/
noncomputable def ztrunc (w : Fn) : Fn := fun z θ => if 0 < z then w z θ else 0

@[simp] theorem ztrunc_of_pos {w : Fn} {z θ : ℝ} (hz : 0 < z) : ztrunc w z θ = w z θ := by
  simp [ztrunc, hz]

theorem ztrunc_of_nonpos {w : Fn} {z θ : ℝ} (hz : ¬ 0 < z) : ztrunc w z θ = 0 := by
  simp [ztrunc, hz]



/-! ## The strong vanishing form -/

/-- If `w` satisfies the weak vanishing hypothesis (only for `z > 0`) then `ztrunc w` satisfies
the strong one. -/
theorem ztrunc_strong_zero {α : ℝ} {w : Fn} (_hw : Work.FTS.ClassC.ClassC α w)
    (hz : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) :
    ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → ztrunc w z θ = 0 := by
  intro z θ hzq
  by_cases hpos : 0 < z
  · have hθ : θ ∉ Set.Ioo 0 (Real.pi / 2) := fun hc => hzq ⟨hpos, hc⟩
    rw [ztrunc_of_pos hpos]
    exact hz z θ hpos hθ
  · exact ztrunc_of_nonpos hpos

/-! ## Invariance of the `ℋᵏ`-quantities -/

/-- `HkSq` is unchanged by the truncation. -/
theorem HkSq_ztrunc (α : ℝ) (k : ℕ) (w : Fn) :
    Work.Spaces.HkSq α k (ztrunc w) = Work.Spaces.HkSq α k w :=
  Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ hz _ _ => ztrunc_of_pos hz)

/-- `HkNorm` is unchanged by the truncation. -/
theorem HkNorm_ztrunc (α : ℝ) (k : ℕ) (w : Fn) :
    Work.Spaces.HkNorm α k (ztrunc w) = Work.Spaces.HkNorm α k w := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_ztrunc]

/-- `Xn` is unchanged by the truncation. -/
theorem Xn_ztrunc (α : ℝ) (w : Fn) :
    Work.FTS.Nonlin.Xn α (ztrunc w) = Work.FTS.Nonlin.Xn α w :=
  HkNorm_ztrunc α 4 w

/-- `HkMem` transfers to the truncation. -/
theorem HkMem_ztrunc {α : ℝ} {k : ℕ} {w : Fn} (h : Work.Spaces.HkMem α k w) :
    Work.Spaces.HkMem α k (ztrunc w) :=
  Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (fun z θ hzθ => (ztrunc_of_pos hzθ.1).symm) h


/-- `SmoothOpen` transfers to the truncation. -/
theorem smoothOpen_ztrunc {w : Fn} (h : Work.FTS.EllipticEst.SmoothOpen w) :
    Work.FTS.EllipticEst.SmoothOpen (ztrunc w) :=
  Work.FTS.EllipticEst.RPFresh.smoothOpen_congr h
    (fun z θ hz _ _ => ztrunc_of_pos hz)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN4a =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem rowsN4a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N4gg α g) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨Cdth, hCdth0, hDthW⟩ := Work.FTS.Nonlin.DthFstar_W
  have hCi0 : 0 < Ci := hN.pos.1
  have hCt0 : 0 < Ct := hE.pos.1
  -- the two row constants
  have hKpos : 0 < (Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1) := by
    nlinarith [hCi0, hCt0, hCdth0]
  refine ⟨(Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1), hKpos, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hctx.hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ## the reference coefficient `D_θF_*`
  have hDthF_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)).Dth
  have hDthF_mem : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (hDthW α hα hα1).1
  have hDthF_bnd : Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
      ≤ Cdth * α ^ 2 := (hDthW α hα hα1).2
  -- ## `FK(g)` is smooth on the open quadrant (the field `ClassC.fsm`) and honest
  have hFKsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.so_FKw hctx.hg
  have hfk := hN.fkH α hIoc g hctx.hqo4 hctx.hL12
  -- ## the radial coefficient `r = -(1/2)·FK(g)`
  set r : ℝ → ℝ := fun z => -(1 / 2) * Work.Construction.FK g z with hrdef
  have hrsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
    rw [hrdef]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2)) hFKsm
  have hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z) := by
    rw [hrdef]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) hfk.1
  have hXr : Work.FTS.Nonlin.Xn α (fun z _ => r z)
      ≤ (1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [hrdef, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      show |(-(1 / 2) : ℝ)| = (1 / 2) by norm_num]
    exact mul_le_mul_of_nonneg_left hfk.2 (by norm_num)
  have hqo : Work.FTS.VocabO.HQo α 4 (fun z _ => r z) := ⟨hrsm, hrmem⟩
  -- ## row 20
  have ht1 := hE.t1 α hIoc (fun z _ => r z) g hqo hctx.hSmoothOpen hctx.hkMem4 hctx.hdecay
  have heq20 : Work.FTS.Nonlin.N4gg α g
      = fun z θ => r z * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4gg, hrdef]
  have h20 : |IP α (Work.FTS.Nonlin.N4gg α g) g|
      ≤ (Ct * Ci / 2) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
    rw [heq20]
    refine ht1.trans ?_
    have hstep : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α (fun z _ => r z)
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hXr
          (mul_nonneg hCt0.le (Real.rpow_nonneg hα.le _)))
        (pow_nonneg hX0 2)
    refine hstep.trans ?_
    have harith : Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
          * Work.FTS.Nonlin.Xn α g ^ 2
        = (Ct * Ci / 2) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
    rw [harith]
  -- ## row 21
  have hαpow : α ^ (-(1 / 2 : ℝ)) * (α : ℝ) ^ 2 = α ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα]
    norm_num
  have heq21 : Work.FTS.Nonlin.N4gs α g
      = fun z θ => -(1 / 2) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * Work.Construction.FK g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4gs, Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hw := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z _ => Work.Construction.FK g z) hDthF_sm hDthF_mem ⟨hFKsm, hfk.1⟩
  have h21 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
      ≤ (Ci * Ci * Cdth / 2) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
    rw [heq21, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      show |(-(1 / 2) : ℝ)| = (1 / 2) by norm_num]
    have hb2 : Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
            * Work.Construction.FK g z)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdth * α ^ 2) * (Ci * Work.FTS.Nonlin.Xn α g) := by
      refine hw.2.trans ?_
      have h1 : Ci * α ^ (-(1 / 2 : ℝ))
            * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
            * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdth * α ^ 2)
            * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDthF_bnd
            (mul_nonneg hCi0.le (Real.rpow_nonneg hα.le _)))
          (Work.Spaces.HkNorm_nonneg α 4 _)
      exact h1.trans (mul_le_mul_of_nonneg_left hfk.2 (by positivity))
    refine (mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ (1 / 2))).trans ?_
    have harith : (1 / 2) * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdth * α ^ 2)
          * (Ci * Work.FTS.Nonlin.Xn α g))
        = (Ci * Ci * Cdth / 2) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
      rw [← hαpow]
      ring
    rw [harith]
  -- ## the two bounds with the common constant
  have hK1 : Ct * Ci / 2 ≤ (Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1) := by
    nlinarith [hCi0, hCdth0]
  have hK2 : Ci * Ci * Cdth / 2 ≤ (Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1) := by
    nlinarith [hCi0, hCt0, hCdth0]
  exact ⟨h20.trans (mul_le_mul_of_nonneg_right hK1
      (mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 3))),
    h21.trans (mul_le_mul_of_nonneg_right hK2
      (mul_nonneg (Real.rpow_nonneg hα.le _) hX0))⟩

end Work.FTS.StrongEps.E4R3.N4C.rows
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The endpoint data** for the trace argument at a fixed `z > 0`: the filter is one of the
two endpoint filters (so that eventually `0 < θ < π/2`), `Γ → 0`, `D_θΓ → 0`, and all the mixed
derivatives `D_z^bD_θ^a W` (`a + b ≤ 6`) vanish at the endpoint (from `BdryTraces α 6 W`). -/
structure TraceCtx (α : ℝ) (W : Fn) (l : Filter ℝ) (z : ℝ) : Prop where
  hz : 0 < z
  hquad : ∀ᶠ θ in l, θ ∈ Set.Ioo 0 (Real.pi / 2)
  gam : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) l (𝓝 0)
  dth_gam : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) l (𝓝 0)
  slot : ∀ a b : ℕ, a + b ≤ 6 → Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed b a W z θ) l (𝓝 0)

/-! ## The traces of the profile `F_*` and of `F = F_* + W` -/

/-- `F_* → 0`: it is `Γ(θ)·(α φ(z)/c)`. -/
theorem tendsto_Fstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.Fstar α z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.Fstar α z θ)
      = fun θ => Work.Spaces.Gam α θ * (α * Work.FM.Fstar z / Work.Spaces.c α) := by
    funext θ
    exact (FstarDerivs α z θ).1
  rw [hfun]
  simpa using hc.gam.mul_const _

/-- `D_θF_* → 0`: it is `D_θΓ(θ)·(α φ(z)/c)`. -/
theorem tendsto_Dth_Fstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      = fun θ => (α * Work.FM.Fstar z / Work.Spaces.c α)
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) := by
    funext θ
    exact (FstarDerivs α z θ).2.2
  rw [hfun]
  simpa using hc.dth_gam.const_mul _

/-- `D_zF_* → 0`: it is `Γ(θ)·(α z ∂_zφ(z)/c)`. -/
theorem tendsto_Dz_Fstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      = fun θ => Work.Spaces.Gam α θ * (α * (z * deriv Work.FM.Fstar z) / Work.Spaces.c α) := by
    funext θ
    exact (FstarDerivs α z θ).2.1
  rw [hfun]
  simpa using hc.gam.mul_const _

/-- `F = F_* + W → 0`. -/
theorem tendsto_Ftot {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.Ftot α W z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.Ftot α W z θ)
      = fun θ => Work.Construction.Fstar α z θ + Work.Spaces.mixed 0 0 W z θ := rfl
  rw [hfun]
  simpa using (tendsto_Fstar hc).add (hc.slot 0 0 (by norm_num))

/-- `D_θF → 0`, by additivity of `D_θ` over `F = F_* + W`. -/
theorem tendsto_Dth_Ftot {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W)
    {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hev : (fun θ : ℝ => Work.Spaces.Dth (Work.Construction.Ftot α W) z θ)
      =ᶠ[l] fun θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        + Work.Spaces.mixed 0 1 W z θ := by
    filter_upwards [hc.hquad] with θ hθ
    have h := Work.FTS.EllipticEst.SmoothOpen.mixed_add hFso hW.reg 0 1 z θ hc.hz hθ.1 hθ.2
    have h2 : Work.Spaces.mixed 0 1 (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.mixed 0 1 W z θ := by
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
        using h
    rw [← h2]
    rfl
  simpa using Filter.Tendsto.congr' hev.symm
    ((tendsto_Dth_Fstar hc).add (hc.slot 1 0 (by norm_num)))

/-- `D_zF → 0`, by additivity of `D_z` over `F = F_* + W`. -/
theorem tendsto_Dz_Ftot {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W)
    {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hev : (fun θ : ℝ => Work.Spaces.Dz (Work.Construction.Ftot α W) z θ)
      =ᶠ[l] fun θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + Work.Spaces.mixed 1 0 W z θ := by
    filter_upwards [hc.hquad] with θ hθ
    have h := Work.FTS.EllipticEst.SmoothOpen.mixed_add hFso hW.reg 1 0 z θ hc.hz hθ.1 hθ.2
    have h2 : Work.Spaces.mixed 1 0 (fun z θ => Work.Construction.Fstar α z θ + W z θ) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.mixed 1 0 W z θ := by
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using h
    rw [← h2]
    rfl
  simpa using Filter.Tendsto.congr' hev.symm
    ((tendsto_Dz_Fstar hc).add (hc.slot 0 1 (by norm_num)))


/-! ## The linear part `𝓛_Γ^T W` -/

/-- **`𝓛_Γ^T W → 0`.**  Expanding `𝓛_Γ^T W = W + D_zW - 2W/(1+z) - (2zΓ/(c(1+z)²))L₁₂(W)
- 3D_θW/(1+z) + (Γ/c)(2z²/(1+z)³)L₁₂(3D_θW/(1+z))`, every summand carries either a mixed
derivative of `W` (which vanishes by `BdryTraces`) or the factor `Γ` (which vanishes). -/
theorem tendsto_LGammaT {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Coercivity.LGammaT α W z θ) l (𝓝 0) := by
  have hW0 : Filter.Tendsto (fun θ : ℝ => W z θ) l (𝓝 0) := by
    simpa using hc.slot 0 0 (by norm_num)
  have hWz : Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed 1 0 W z θ) l (𝓝 0) :=
    hc.slot 0 1 (by norm_num)
  have hWth : Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed 0 1 W z θ) l (𝓝 0) :=
    hc.slot 1 0 (by norm_num)
  have p1 : Filter.Tendsto (fun θ : ℝ => (W z θ + Work.Spaces.mixed 1 0 W z θ)
      + (-(2 * W z θ / (1 + z)))) l (𝓝 0) := by
    have h3 : Filter.Tendsto (fun θ : ℝ => -(2 * W z θ / (1 + z))) l (𝓝 0) := by
      simpa using ((hW0.const_mul 2).div_const (1 + z)).neg
    simpa using (hW0.add hWz).add h3
  have p2 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ
      * (-(2 * z * Work.Construction.L12 W z / (Work.Spaces.c α * (1 + z) ^ 2)))) l (𝓝 0) := by
    simpa using hc.gam.mul_const (-(2 * z * Work.Construction.L12 W z
      / (Work.Spaces.c α * (1 + z) ^ 2)))
  have p3 : Filter.Tendsto (fun θ : ℝ => -(3 * Work.Spaces.mixed 0 1 W z θ / (1 + z)))
      l (𝓝 0) := by
    simpa using ((hWth.const_mul 3).div_const (1 + z)).neg
  have p4 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ
      * ((2 * z ^ 2 / (1 + z) ^ 3)
          * Work.Construction.L12 (Work.Coercivity.Transport W) 0 / Work.Spaces.c α)) l (𝓝 0) := by
    simpa using hc.gam.mul_const ((2 * z ^ 2 / (1 + z) ^ 3)
      * Work.Construction.L12 (Work.Coercivity.Transport W) 0 / Work.Spaces.c α)
  have hsum : Filter.Tendsto (fun θ : ℝ =>
      ((W z θ + Work.Spaces.mixed 1 0 W z θ) + (-(2 * W z θ / (1 + z))))
      + Work.Spaces.Gam α θ * (-(2 * z * Work.Construction.L12 W z
          / (Work.Spaces.c α * (1 + z) ^ 2)))
      + (-(3 * Work.Spaces.mixed 0 1 W z θ / (1 + z)))
      + Work.Spaces.Gam α θ * ((2 * z ^ 2 / (1 + z) ^ 3)
          * Work.Construction.L12 (Work.Coercivity.Transport W) 0 / Work.Spaces.c α)) l (𝓝 0) := by
    simpa using ((p1.add p2).add p3).add p4
  refine Filter.Tendsto.congr (fun θ => ?_) hsum
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.L,
    Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Coercivity.L12f,
    Work.Construction.L12, Work.Spaces.Dth, Work.Spaces.Dz, Work.Spaces.pz,
    Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, div_eq_mul_inv]
  ring

/-! ## The projector term `AK` -/

/-- **`AK α z θ → 0`**: it is `(Γ(θ)/c)·2z²/(1+z)³`. -/
theorem tendsto_AK {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.AK α z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.AK α z θ)
      = fun θ => Work.Spaces.Gam α θ * (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) := by
    funext θ
    simp only [Work.Construction.AK]
    ring
  rw [hfun]
  simpa using hc.gam.mul_const _

/-! ## The linear-in-`g` term `N_*` -/

/-- **`N_*(μ,λ)(W) → 0`** for any constants `μ, λ`: it is `-μW - (μ+λ+μλ)D_zW`. -/
theorem tendsto_Nstar {α : ℝ} {W : Fn} {l : Filter ℝ} {z : ℝ} (hc : TraceCtx α W l z)
    (mu lam : ℝ) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.Nstar mu lam W z θ) l (𝓝 0) := by
  have hfun : (fun θ : ℝ => Work.Construction.Nstar mu lam W z θ)
      = fun θ => (-mu) * W z θ - (mu + lam + mu * lam) * Work.Spaces.mixed 1 0 W z θ := by
    funext θ
    simp only [Work.Construction.Nstar, Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, Work.Spaces.mixed_zero_right,
      Work.Spaces.mixed_zero_left]
  rw [hfun]
  have h1 : Filter.Tendsto (fun θ : ℝ => (-mu) * W z θ) l (𝓝 0) := by
    simpa using (show Filter.Tendsto (fun θ : ℝ => W z θ) l (𝓝 0) from by
      simpa using hc.slot 0 0 (by norm_num)).const_mul (-mu)
  have h2 : Filter.Tendsto (fun θ : ℝ => (mu + lam + mu * lam) * Work.Spaces.mixed 1 0 W z θ)
      l (𝓝 0) := by
    simpa using (hc.slot 0 1 (by norm_num)).const_mul (mu + lam + mu * lam)
  simpa using h1.sub h2

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
