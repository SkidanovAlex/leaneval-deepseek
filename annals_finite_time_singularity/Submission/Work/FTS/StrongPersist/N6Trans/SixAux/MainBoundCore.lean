import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.H4N_GammaTerm_le
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkJets
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.identity_local =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/identity_local` — the chain identity, using `radial_identity2`

A copy of `AeI1Fts.identity`'s proof in which the radial half is the (fresh, complete)
`AeI1Fts.radial_identity2`; this keeps the target `I1Paper_mixed` free of the `sorry` of
`AeI1Fts.radial_identity`.  All the auxiliary lemmas (`IP_self_eq`, `integral_Iz_eq_Ioi`, the
slicewise integrability facts, ...) are the ones of `AeI1Fts.identity`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)



end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.N0_split_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real

/-- **The `N₀`-split on the open quadrant**, for the local hypothesis `SmoothOpen w` alone.

`N₀ α (F_* + w) w` is a sum of six products, and the only place where `F = F_* + w` enters is
through `∂_θF` (in `N₀₄`) and `D_zF` (in `N₀₅`).  On the open quadrant both operators are
*additive* (`Rl1.openSlice_pth_add`, `Rl1.openSlice_pz_add` via `Pieces.Dz_add_of_diff`),
because the slices of `F_*` and `w` are differentiable there; splitting them turns `N₀₄` into
`N₀₄ᵃ + N₀₄ᵇ` and `N₀₅` into `N₀₅ᵃ + N₀₅ᵇ`, while `N₀₁ + N₀₂` (which involve only `F_*`) is
`N0fix`.  This is the first conjunct of `Work.FTS.NonlinRows.SplitsAll`, with the `ClassC`
context of that statement replaced by the bare smoothness of `w` that its proof actually uses. -/
theorem N0_split_open {α : ℝ} (hα : 0 < α) {w : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α w) w z θ
        = Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ
                    + Work.FTS.Nonlin.N06F α w z θ))))) := by
  have _ := hα
  intro z θ hq
  have hz : 0 < z := hq.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  -- `F_*` is `C^∞` on the open quadrant, for every real `α`
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  -- additivity of `∂_θ` and of `D_z` on `F = F_* + w`
  have hpth : Work.Spaces.pth (Work.Construction.Ftot α w) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth w z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hw hz hθ
  have hDz : Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz w z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hw hz hθ)
  simp only [Work.Construction.N0, Work.FTS.Nonlin.N0fix, Work.FTS.Nonlin.N03g,
    Work.FTS.Nonlin.N04aF, Work.FTS.Nonlin.N04bF, Work.FTS.Nonlin.N05aF,
    Work.FTS.Nonlin.N05bF, Work.FTS.Nonlin.N06F, Work.Construction.N01,
    Work.Construction.N02, Work.Construction.N03, Work.Construction.N04a,
    Work.Construction.N04b, Work.Construction.N05a, Work.Construction.N05b,
    Work.Construction.N06]
  rw [hpth, hDz]
  ring

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.WordTransfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The two shift identities for the canonical slot words -/

/-- **The `D_θ`-shift is free**: `D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
theorem mixed_Dth_shift (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f :=
  congrArg (fun g : ℝ → ℝ → ℝ => Work.Spaces.DzIter j g)
    (Work.Spaces.DthIter_add_right i 1 f)

/-- Iterates of `D_z` are local: if two profiles agree on an open set, so do their `D_z`-iterates
(any order). -/
theorem DzIter_eqOn_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro p hp
      have hz : Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DzIter j g') p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Function.uncurry]
      rw [hz]

/-- **The `D_z`-shift on the open quadrant**: for `f` smooth on `Q0`,
`D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` there.  This is the only place where the commutation
of `D_θ` with the iterates of `D_z` is needed. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
        = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 (Work.FTS.EllipticEst.smoothOpen_iff_forall f |>.1 hf) 1 i
  intro z θ hq
  have h2 : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.mixed 1 i f) z θ :=
    DzIter_eqOn_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcomm j hq
  have h3 : Work.Spaces.DzIter j (Work.Spaces.mixed 1 i f) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ :=
    congrArg (fun g : ℝ → ℝ → ℝ => g z θ)
      (Work.Spaces.DzIter_add_right j 1 (Work.Spaces.DthIter i f)).symm
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [h2, h3]

/-! ## The structural induction -/


/-! ## The two instances consumed by `AprioriP` -/



end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.L5of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.Spaces
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-`5` bundle of an atom, from its level-`5` `ℋ⁵`-data.** -/
theorem L5_of_HQo5 {α : ℝ} (hα : 0 < α) {A : Fn} {a : ℝ}
    (h : Work.FTS.VocabO.HQo α 5 A) (hb : Work.Spaces.HkNorm α 5 A ≤ a) :
    L5 α A a := by
  have hmem4 : Work.Spaces.HkMem α 4 A :=
    Work.FTS.OpenPkg.HkMem_mono_open h.1 4 (by norm_num) h.2
  have hbd4 : Work.FTS.Nonlin.Xn α A ≤ a :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 5) (k' := 4)
      (by norm_num) h.2) hb
  have hDz5 : Work.Spaces.HkNorm α 4 (Work.Spaces.Dz A) ≤ Work.Spaces.HkNorm α 5 A :=
    Real.sqrt_le_sqrt (Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 4
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen h.1 5) h.2)
  have hDth5 : Work.Spaces.HkNorm α 4 (Work.Spaces.Dth A) ≤ Work.Spaces.HkNorm α 5 A :=
    Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα 4 h.2)
  exact ⟨⟨h.1, hmem4⟩, hbd4,
    ⟨h.1.Dz, Work.FTS.IPGen.HkMem_Dz_le h.1 h.2⟩, le_trans hDz5 hb,
    ⟨h.1.Dth, Work.FTS.IPGen.HkMem_Dth_le (by linarith) h.1 h.2⟩, le_trans hDth5 hb⟩

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.Facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Smoothness of `Lhat` -/

/-- `Lhat g` is `C^∞` on the open quadrant whenever `g` is. -/
theorem smoothOpen_Lhat {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.Lhat g) := by
  have hloc := Work.FTS.StrongPersist.locOp_smoothOpen hg
  have hneg : Work.FTS.CoercivityFix.Lhat g = fun z θ => -(Work.FTS.StrongPersist.locOp g z θ) := by
    funext z θ
    simp only [Work.FTS.CoercivityFix.Lhat, Work.FTS.StrongPersist.locOp, Pi.sub_apply,
      Pi.neg_apply]
    ring
  rw [hneg]
  rw [Work.FTS.EllipticEst.SmoothOpen] at hloc ⊢
  have hfun : Function.uncurry (fun z θ => -(Work.FTS.StrongPersist.locOp g z θ))
      = fun p : ℝ × ℝ => -(Function.uncurry (Work.FTS.StrongPersist.locOp g) p) := rfl
  rw [hfun]
  exact hloc.neg

/-- `Lhat g` is `C^m` on the open quadrant for every `m`. -/
theorem q0Sm_Lhat {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm m (Work.FTS.CoercivityFix.Lhat g) :=
  Work.FTS.StrongPersist.q0Sm_of_smoothOpen (smoothOpen_Lhat hg) m

/-! ## Monotonicity and shift dominations of `HkSq` -/

/-- **Monotonicity of `HkSq` in the order.** -/
theorem HkSq_mono_order (α : ℝ) {m k : ℕ} (hmk : m ≤ k) {f : Fn}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m f z θ) hf.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m f z θ)
    (hf.1 z hz) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => ?_
  exact Work.FTS.StrongPersist.HkIntegrand_le_of_le α hmk f z θ

/-- **The `D_θ`-shift domination**: `|D_θ f|²_{ℋ^m} ≤ |f|²_{ℋ^{m+1}}`. -/
theorem HkSq_Dth_le_succ' (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (m : ℕ) {f : Fn}
    (hm : Work.Spaces.HkMem α (m + 1) f) :
    Work.Spaces.HkSq α m (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (m + 1) f :=
  Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α hα m hm

/-- **The `D_z`-shift domination**: `|D_z f|²_{ℋ^m} ≤ |f|²_{ℋ^{m+1}}`. -/
theorem HkSq_Dz_le_succ' (α : ℝ) (m : ℕ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α (m + 1) f) :
    Work.Spaces.HkSq α m (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (m + 1) f :=
  Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α m
    (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (m + 1)) hm

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `B1f` (the group of slots with at most four `D_z`-derivatives on the radial coefficient) is
continuous on the open quadrant.  Same proof as `B2f_continuousOn`. -/
private theorem B1f_continuousOn {α : ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => B1f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  simp only [B1f]
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases h4 : k ≤ 4
  · simp only [if_pos h4]
    exact continuousOn_const.mul
      (((continuousOn_leaf hleaf).mul ((hso.mixed (b - k) a).continuousOn).abs).mul
        ((hso.mixed b a).continuousOn).abs)
  · simp only [if_neg h4]; exact continuousOn_const

/-- **The level-six transport row with the coefficient `L₁₂(f)·f`, pointwise in `z`.**

The radial coefficient `L₁₂(f)` is `C^6` on `(0,∞)`; its `D_z`-jets are bounded by
`C₄|f|_{ℋ⁴}` (order `≤ 4`) and `C₆|f|_{ℋ⁶}` (order `≤ 6`), supplied here as hypotheses.
Leibniz expands the slot `D_z^bD_θ^a(L₁₂(f)·f)`; the `k ≤ 4` slots are absorbed into
`448·∫_θ HkIntegrand α 6 f` by the pointwise AM–GM bound `leaf_slice_le6`/`group_sum_le`,
and the `k ≥ 5` slots are left as the explicit remainder `∫_θ B2f a b ρ f`. -/
theorem T3RowTheta (C4 C6 : ℝ) (hC4 : 0 < C4) (hC6 : 0 < C6) :
    ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
          ≤ C4 * Work.Spaces.HkNorm α 4 f) →
      (∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
          ≤ C6 * Work.Spaces.HkNorm α 6 f) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |∫ θ in Work.Spaces.Iθ, ρ z θ
            * Work.Spaces.mixed b a (fun z θ => Work.Construction.L12 f z * f z θ) z θ
            * Work.Spaces.mixed b a f z θ|
          ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
  intro α hα f a b ρ hso hm6 hm7 hl12 hab hleaf hs4 hs6
  have hα0 : 0 < α := hα.1
  -- ## the radial coefficient is `C^6` on `(0,∞)`
  have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
      (by norm_num : 2 ≤ 7)).1
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h
  -- ## the uniform bounds on the derivative tower of `L₁₂(f)`
  have hsup : ∀ k : ℕ, k ≤ b → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
            else C6 * Work.Spaces.HkNorm α 6 f) := by
    intro k hk z hz
    by_cases h4 : k ≤ 4
    · rw [if_pos h4]; exact hs4 k h4 z hz
    · rw [if_neg h4]; exact hs6 k (by omega) z hz
  -- ## continuity of the slot factors on the open quadrant
  have hcontPsi : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed (b - k) a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun k => (hso.mixed (b - k) a).continuousOn
  have hcontY : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hso.mixed b a).continuousOn
  have hcontρ : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    continuousOn_leaf hleaf
  have hcontB1 : ContinuousOn (fun p : ℝ × ℝ => B1f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    B1f_continuousOn hso hleaf
  have hcontB2 : ContinuousOn (fun p : ℝ × ℝ => B2f a b ρ f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    B2f_continuousOn hso hleaf
  -- ## the defining equations of the two groups
  have hB1def : ∀ z θ : ℝ, B1f a b ρ f z θ = ∑ k ∈ Finset.range (b + 1), (if k ≤ 4 then
      (b.choose k : ℝ)
      * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
      else 0) := fun z θ => rfl
  have hB2def : ∀ z θ : ℝ, B2f a b ρ f z θ = ∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then
      (b.choose k : ℝ)
      * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
      else 0) := fun z θ => rfl
  -- ## slice integrability of the two groups
  have hB1_slice : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => B1f a b ρ f z θ) Work.Spaces.Iθ := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hz
    refine MeasureTheory.Integrable.mono' ((hm6.1 z hzI).const_mul 448) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontB1 hz
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
      have hterm : ∀ k ∈ Finset.range (b + 1),
          0 ≤ (if k ≤ 4 then (b.choose k : ℝ)
              * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
              else 0) := by
        intro k _
        by_cases h4 : k ≤ 4
        · rw [if_pos h4]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        · rw [if_neg h4]
      rw [hB1def, Real.norm_eq_abs, Finset.abs_sum_of_nonneg hterm]
      exact group_sum_le hα0 hleaf hab (fun k => k ≤ 4) hz ⟨h1, h2⟩
  have hB2_slice : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => B2f a b ρ f z θ) Work.Spaces.Iθ := by
    intro z hz
    have hzI : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hz
    refine MeasureTheory.Integrable.mono' ((hm6.1 z hzI).const_mul 448) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcontB2 hz
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
      have hterm : ∀ k ∈ Finset.range (b + 1),
          0 ≤ (if 5 ≤ k then (b.choose k : ℝ)
              * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
              else 0) := by
        intro k _
        by_cases h5 : 5 ≤ k
        · rw [if_pos h5]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        · rw [if_neg h5]
      rw [hB2def, Real.norm_eq_abs, Finset.abs_sum_of_nonneg hterm]
      exact group_sum_le hα0 hleaf hab (fun k => 5 ≤ k) hz ⟨h1, h2⟩
  -- ## the pointwise (a.e. in `z`) bound for the `θ`-integral
  filter_upwards [ae_restrict_Iz_of_pos (fun z hz => hz)] with z hz
  have hzI : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
        ≤ (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
    -- Leibniz
    have hleibθ : Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.mixed (b - k) a f z θ) :=
      leibniz_radial_mul hXsm hso b a (by omega) z θ hz h1 h2
    have hXp : |Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
        ≤ ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * |Work.Spaces.mixed (b - k) a f z θ| := by
      rw [hleibθ]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun k _ => ?_
      have hc : (0 : ℝ) ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_mul, abs_of_nonneg hc]
      exact le_of_eq (by ring)
    have hYnn : 0 ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
    have hstep1 : ρ z θ * |Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
      calc ρ z θ * |Work.Spaces.mixed b a
            (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
            * |Work.Spaces.mixed b a f z θ|
          ≤ ρ z θ * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
              * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.mixed (b - k) a f z θ|) * |Work.Spaces.mixed b a f z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXp hρ0) hYnn
        _ = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
              * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by ring
    have hstep2 : (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|))
        ≤ (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ := by
      have hsplit : ∀ k ∈ Finset.range (b + 1),
          (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|)
          ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (if k ≤ 4 then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (if 5 ≤ k then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0) := by
        intro k hk
        have hk' : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hkK := hsup k hk' z hz
        have hψ : 0 ≤ ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _)
        have hc : 0 ≤ (b.choose k : ℝ) := Nat.cast_nonneg _
        by_cases h4 : k ≤ 4
        · have h5 : ¬ 5 ≤ k := by omega
          rw [if_pos h4, if_neg h5, mul_zero, add_zero]
          rw [if_pos h4] at hkK
          calc (b.choose k : ℝ)
                * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|)
              ≤ (b.choose k : ℝ) * (C4 * Work.Spaces.HkNorm α 4 f)
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hc) hψ
            _ = (C4 * Work.Spaces.HkNorm α 4 f)
                * ((b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|)) := by ring
        · have h5 : 5 ≤ k := by omega
          rw [if_neg h4, mul_zero, zero_add, if_pos h5]
          rw [if_neg h4] at hkK
          calc (b.choose k : ℝ)
                * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|)
              ≤ (b.choose k : ℝ) * (C6 * Work.Spaces.HkNorm α 6 f)
                * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hc) hψ
            _ = (C6 * Work.Spaces.HkNorm α 6 f)
                * ((b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|)) := by ring
      calc (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
              * |Work.Spaces.mixed b a f z θ|))
          ≤ ∑ k ∈ Finset.range (b + 1), ((C4 * Work.Spaces.HkNorm α 4 f)
              * (if k ≤ 4 then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (if 5 ≤ k then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)) :=
            Finset.sum_le_sum hsplit
        _ = (C4 * Work.Spaces.HkNorm α 4 f)
              * (∑ k ∈ Finset.range (b + 1), (if k ≤ 4 then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0))
            + (C6 * Work.Spaces.HkNorm α 6 f)
              * (∑ k ∈ Finset.range (b + 1), (if 5 ≤ k then (b.choose k : ℝ)
                  * (ρ z θ * |Work.Spaces.mixed (b - k) a f z θ|
                    * |Work.Spaces.mixed b a f z θ|) else 0)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
            + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ := by
            rw [hB1def, hB2def]
    have habs : |ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
          * Work.Spaces.mixed b a f z θ|
        = ρ z θ * |Work.Spaces.mixed b a
            (fun z θ => Work.Construction.L12 f z * f z θ) z θ|
          * |Work.Spaces.mixed b a f z θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact le_trans (le_of_eq habs) (le_trans hstep1 hstep2)
  -- ## integrate the `θ`-bound
  have hDslice : IntegrableOn (fun θ : ℝ => (C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
      + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ) Work.Spaces.Iθ :=
    ((hB1_slice z hz).const_mul _).add ((hB2_slice z hz).const_mul _)
  have h2 : (∫ θ in Work.Spaces.Iθ, |ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        * Work.Spaces.mixed b a f z θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, ((C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hDslice hpt
  have h3 : (∫ θ in Work.Spaces.Iθ, ((C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ))
      = (C4 * Work.Spaces.HkNorm α 4 f) * (∫ θ in Work.Spaces.Iθ, B1f a b ρ f z θ)
        + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
    rw [MeasureTheory.integral_add ((hB1_slice z hz).const_mul _)
      ((hB2_slice z hz).const_mul _), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have h4 : (∫ θ in Work.Spaces.Iθ, B1f a b ρ f z θ)
      ≤ 448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ((hm6.1 z hzI).const_mul 448) ?_
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα0 hleaf).1 z θ hz h1 h2
      rw [hB1def]
      exact Finset.sum_nonneg fun k _ => by
        by_cases h4 : k ≤ 4
        · rw [if_pos h4]
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _))
        · rw [if_neg h4]
    · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      rw [hB1def]
      exact group_sum_le hα0 hleaf hab (fun k => k ≤ 4) hz ⟨h1, h2⟩
  calc |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * f z θ) z θ
          * Work.Spaces.mixed b a f z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, ((C4 * Work.Spaces.HkNorm α 4 f) * B1f a b ρ f z θ
          + (C6 * Work.Spaces.HkNorm α 6 f) * B2f a b ρ f z θ) := h2
    _ = (C4 * Work.Spaces.HkNorm α 4 f) * (∫ θ in Work.Spaces.Iθ, B1f a b ρ f z θ)
          + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := h3
    _ ≤ (C4 * Work.Spaces.HkNorm α 4 f)
          * (448 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ))
          + (C6 * Work.Spaces.HkNorm α 6 f) * (∫ θ in Work.Spaces.Iθ, B2f a b ρ f z θ) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left h4
          (mul_nonneg hC4.le (Work.Spaces.HkNorm_nonneg α 4 f))

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers

These are the (slightly generalised) slot facts needed for the `L₁₂(f)·D_θ f` row: the two
factors that occur after the Leibniz expansion carry the slot indices `a` and `a + 1`, while
the leaf weight `ρ` belongs to the slot `a`. -/

/-- A leaf weight of the slot `a` is dominated by the slot weight of any slot index `a' ≥ a`. -/
theorem leaf_le_slotW_of_le {α : ℝ} (hα : 0 < α) {a a' : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a ≤ a') :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      ρ z θ ≤ Work.FTS.TransportS.slotW α a' z θ := by
  rcases hleaf with rfl | rfl | ⟨ha1, rfl⟩
  · exact fun z θ _ hθ => Work.FTS.TransportS.leafEta_le_slotW α hα hθ
  · exact fun z θ _ hθ => Work.FTS.TransportS.leafOne_le_slotW α hα hθ
  · exact fun z θ _ hθ => Work.FTS.TransportS.leafGam_le_slotW α hα (by omega) hθ

/-- A single slot of `f` is dominated by the level-`m` integrand. -/
theorem slotW_slot_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b m : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hab : a + b ≤ m) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m f z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ, Work.Spaces.mixed_zero_right]
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have heq : (Work.Spaces.DzIter b f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter b f z θ) ^ 2 := by
      rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ hs (ne_of_gt Work.Spaces.eta_pos)]
      ring
    have h := Work.Spaces.sq_le_HkIntegrand_z α m f z θ b (by omega)
    rwa [heq] at h
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    have heq : (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      ring
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α m f z θ a b ha1 (by omega)
    rwa [heq] at h

/-- The `ρ`-weighted product of two slots of `f` (of indices `a₁ ≥ a`, `a₂ ≥ a`, both of
order at most `m`) is dominated by the level-`m` integrand. -/
theorem leaf_mixed_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a a₁ a₂ b₁ b₂ m : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (ha₁ : a ≤ a₁) (ha₂ : a ≤ a₂) (hb₁ : a₁ + b₁ ≤ m) (hb₂ : a₂ + b₂ ≤ m)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|
      ≤ Work.Spaces.HkIntegrand α m f z θ := by
  have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz hθ.1 hθ.2
  have h1 : ρ z θ * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m f z θ :=
    (mul_le_mul_of_nonneg_right (leaf_le_slotW_of_le hα hleaf ha₁ z θ hz hθ)
      (sq_nonneg _)).trans (slotW_slot_le hα hθ hb₁)
  have h2 : ρ z θ * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m f z θ :=
    (mul_le_mul_of_nonneg_right (leaf_le_slotW_of_le hα hleaf ha₂ z θ hz hθ)
      (sq_nonneg _)).trans (slotW_slot_le hα hθ hb₂)
  have h3 : |Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|
      ≤ (1 / 2) * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2
        + (1 / 2) * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2 := by
    rw [← abs_mul]
    exact abs_mul_le_half _ _
  calc ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|
      = ρ z θ * (|Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|) := by
        ring
    _ ≤ ρ z θ * ((1 / 2) * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2
          + (1 / 2) * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hρ0
    _ = (1 / 2) * (ρ z θ * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2)
          + (1 / 2) * (ρ z θ * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2) := by ring
    _ ≤ Work.Spaces.HkIntegrand α m f z θ := by linarith

/-- The mixed angular derivative of the second factor: `D_z^jD_θ^a (D_θ f) = D_z^jD_θ^{a+1} f`. -/
theorem mixed_Dth_eq (j a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j a (Work.Spaces.Dth f) = Work.Spaces.mixed j (a + 1) f := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.Dth f))
      = Work.Spaces.DzIter j (Work.Spaces.DthIter (a + 1) f)
  rw [show Work.Spaces.Dth f = Work.Spaces.DthIter 1 f from rfl,
    Work.Spaces.DthIter_add_right a 1 f]

/-- A property holding for every `z > 0` holds a.e. for the measure restricted to `Iz`. -/
theorem ae_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), p z := by
  rw [Work.Spaces.Iz]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => h z hz)

/-- The restriction of Lebesgue measure to `Iz = [0,∞)` and to `(0,∞)` agree. -/
theorem Iz_restrict_eq : volume.restrict Work.Spaces.Iz
    = volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm

/-! ## Measurability and integrability of the `θ`-slices of one slot of the expansion -/

/-- The `z`-jets of the radial coefficient `L₁₂(f)` are a.e. strongly measurable on `Iz`. -/
theorem aesm_DzdIter_L12 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm7 : Work.Spaces.HkMem α 7 f)
    (k : ℕ) (hk : k ≤ 6) :
    AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      (volume.restrict Work.Spaces.Iz) := by
  have hCd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
      (by norm_num : 2 ≤ 7)).1
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h
  have hEq : (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      = fun z => (Work.Spaces.Zop^[k] (fun z => Work.Construction.L12 f z)) z := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  have hcont : ContinuousOn
      (Work.Spaces.Zop^[k] (fun z => Work.Construction.L12 f z)) (Set.Ioi 0) :=
    (Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' k (6 - k) (by
      have h : k + (6 - k) = 6 := by omega
      rw [← Nat.cast_add, h]
      exact hCd)).continuousOn
  have h1 : AEStronglyMeasurable
      (fun z => (Work.Spaces.Zop^[k] (fun z => Work.Construction.L12 f z)) z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  rw [hEq, Iz_restrict_eq]
  exact h1

/-- The `θ`-slice of a single slot pairing of the expansion is integrable. -/
theorem Psi_slice_int {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    Integrable (fun θ => ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
      * Work.Spaces.mixed b a f z θ) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed (b - k) (a + 1) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_leaf hleaf).mul
      ((hso.mixed (b - k) (a + 1)).continuousOn)).mul ((hso.mixed b a).continuousOn)
  refine MeasureTheory.Integrable.mono' (hm7.1 z (le_of_lt hz)) ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show ‖ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ‖ ≤ Work.Spaces.HkIntegrand α 7 f z θ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact leaf_mixed_le hα hleaf (by omega) (le_refl a) (by omega) (by omega)
      hz ⟨h1, h2⟩

/-- The `θ`-integral of a single slot pairing of the expansion is dominated by the level-seven
slice integrand. -/
theorem Psi_le_int {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ := by
  refine le_trans abs_integral_le_integral_abs ?_
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hm7.1 z (le_of_lt hz)) ?_
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show (0 : ℝ) ≤ |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _)
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 7 f z θ
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact leaf_mixed_le hα hleaf (by omega) (le_refl a) (by omega) (by omega)
      hz ⟨h1, h2⟩

/-- The `θ`-integral of a single slot pairing of the expansion is integrable in `z`. -/
theorem Psi_intz {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ
      * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      Work.Spaces.Iz := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed (b - k) (a + 1) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_leaf hleaf).mul
      ((hso.mixed (b - k) (a + 1)).continuousOn)).mul ((hso.mixed b a).continuousOn)
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ
      * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  refine MeasureTheory.Integrable.mono' hm7.2 haesm ?_
  filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
  rw [Real.norm_eq_abs]
  exact Psi_le_int hα hso hleaf hm7 hab hz

/-- The `z`-integrand `D_z^k(L₁₂f)·(θ-slot integral)` is integrable. -/
theorem DzdX_Psi_int {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ} {K : ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) (hk : k ≤ 6) (hK : 0 ≤ K)
    (hbound : ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ K) :
    IntegrableOn (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
      * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ)) Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' (hm7.2.const_mul K) ?_ ?_
  · exact (aesm_DzdIter_L12 hso hm7 k hk).mul (Psi_intz (k := k) hα hso hleaf hm7 hab).aestronglyMeasurable
  · filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    have h2 := Psi_le_int (k := k) hα hso hleaf hm7 hab hz
    have h1 := hbound z hz
    have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ :=
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 7 f z θ
    exact mul_le_mul h1 h2 (abs_nonneg _) hK

theorem Psi_le_int6 {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm6 : Work.Spaces.HkMem α 6 f)
    (hab : a + b ≤ 6) (hk : 1 ≤ k) (hkb : k ≤ b) {z : ℝ} (hz : 0 < z) :
    |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  refine le_trans abs_integral_le_integral_abs ?_
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hm6.1 z (le_of_lt hz)) ?_
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show (0 : ℝ) ≤ |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _)
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact leaf_mixed_le hα hleaf (by omega) (le_refl a) (by omega) (by omega)
      hz ⟨h1, h2⟩

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

theorem HkMem_radial_mul6 :
    ∀ (α B : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ), 0 < α → 0 ≤ B →
      ContDiffOn ℝ 6 X (Set.Ioi 0) →
      (∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j X z| ≤ B) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 6 (fun z θ => X z * f z θ) := by
  intro α B X f _hα hB hX hbnd hf hmem
  obtain ⟨K, hKpos, hmaj⟩ := radialMaj6 α B X f hB hX hf hbnd
  exact HkMemOfContMajorant α 6 hKpos.le (radialMul6Cont α X f hX hf) hmem hmaj

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkMem_X_close6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ⁶`-membership of the `(1+z)/(2α)`-scaled `close6` row

`close6 α (z,θ) = 8α² c2m(θ) z² Γ(θ)/(c(α)(1+z)⁴)` is the collapsed `I₁+I₂` combination of
`N₀` (the separable datum `Kfac α · ρ(z) · ψ(θ)` with `ρ = rhoR`, `ψ = psiA α`), and
`Work.FTS.StrongPersist.H6Rows.FstarI12H6` proves `close6 α ∈ ℋ⁶` with the pointwise majorant
`(Kfac α)²(M/(1+z)²)²·gammaAngMaj6 α D θ`.

Here we prove that the *scaled* row

`X α (z,θ) = (1+z)/(2α) · close6 α z θ = (Kfac α/(2α)) · ((1+z)ρ(z)) · ψ(θ)`

is still in `ℋ⁶`.  The factor `(1+z)/(2α)` is *not* a bounded radial multiplier
(`HkMem_radial_mul6` needs a uniform bound on the `Zop`-iterates, which `(1+z)/(2α)` does not
have), so the estimate is redone: the new radial factor `(1+z)·rhoR` satisfies only the weaker
bound
`|Zop^j ((1+z)ρ)(z)·w(z)| ≤ 64M/(1+z)`
(`zopIter_one_add_rhoR_bound`, from the Leibniz rule and the known `rhoR`-bound), and the
generalised separable majorant `HkN_sepF_le` turns such a bound into
`HkIntegrand α 6 X z θ ≤ (M'/(1+z))² · gammaAngMaj6 α D θ`.  Since `∫_0^∞ dz/(1+z)² < ∞`
(`Work.Elliptic.WtoH_IntZ`), the majorant is integrable and
`Work.FTS.LocData.HkMem_of_majorant` gives the membership.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem HkMem_X_close6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 6 (fun z θ =>
      (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ) := by
  obtain ⟨M, hM, hMr⟩ := Work.Construction.H6N_GammaTerm_rho_bound
  obtain ⟨D, hD, hDl⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  have hKfac_pos : 0 < Work.Construction.Kfac α := by
    rw [Work.Construction.Kfac]
    have hc : 0 < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    positivity
  -- the radial factor of the target, relative to the angular profile `psiA α`
  set a : ℝ → ℝ := fun z =>
    Work.Construction.Kfac α / (2 * α) * ((1 + z) * Work.Construction.rhoR z) with ha
  have hafn : a = fun z : ℝ =>
      Work.Construction.Kfac α / (2 * α) * ((1 + z) * Work.Construction.rhoR z) := by
    funext z; rw [ha]
  -- the target function, named
  let F0 : ℝ → ℝ → ℝ := fun z θ =>
    (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ
  change Work.Spaces.HkMem α 6 F0
  -- the pointwise identification of the target with the separable shape `a(z)·psiA α θ`
  have hpc : ∀ z θ : ℝ, F0 z θ = a z * Work.Construction.psiA α θ := by
    intro z θ
    show (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ
      = a z * Work.Construction.psiA α θ
    rw [show a z = Work.Construction.Kfac α / (2 * α)
        * ((1 + z) * Work.Construction.rhoR z) from congrFun hafn z]
    simp only [Work.FTS.StrongPersist.H6Rows.close6, Work.Construction.Kfac,
      Work.Construction.rhoR, Work.Construction.psiA]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hfun : F0 = Work.Construction.sepF a (Work.Construction.psiA α) := by
    funext z θ; exact hpc z θ
  rw [hfun]
  -- the price of the radial factor: `M' = (Kfac α/(2α))·64M`
  set M' : ℝ := Work.Construction.Kfac α / (2 * α) * (64 * M) with hM'def
  have hM'pos : 0 < M' := by rw [hM'def]; positivity
  have hKr : 0 ≤ Work.Construction.Kfac α / (2 * α) := le_of_lt (by positivity)
  have hMr' : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] a) z * Work.Spaces.w z| ≤ M' / (1 + z) := by
    intro j hj z hz
    have hb : |(Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
        * Work.Spaces.w z| ≤ (64 * M) / (1 + z) :=
      zopIter_one_add_rhoR_bound hM hMr j hj z hz
    rw [hafn, Work.Construction.Zop_iter_const_mul]
    simp only []
    calc |(Work.Construction.Kfac α / (2 * α)
            * (Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z)
            * Work.Spaces.w z|
        = (Work.Construction.Kfac α / (2 * α))
            * |(Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
                * Work.Spaces.w z| := by
          rw [show (Work.Construction.Kfac α / (2 * α)
                  * (Work.Spaces.Zop^[j]
                      (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z)
                  * Work.Spaces.w z
                = (Work.Construction.Kfac α / (2 * α))
                  * ((Work.Spaces.Zop^[j]
                      (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
                    * Work.Spaces.w z) from by ring,
            abs_mul, abs_of_nonneg hKr]
      _ ≤ (Work.Construction.Kfac α / (2 * α)) * ((64 * M) / (1 + z)) :=
          mul_le_mul_of_nonneg_left hb hKr
      _ = M' / (1 + z) := by rw [hM'def]; ring
  -- the majorant
  set Mmaj : ℝ → ℝ → ℝ := fun z θ =>
    (M' / (1 + z)) ^ 2 * Work.FTS.StrongPersist.H6Rows.gammaAngMaj6 α D θ with hMmaj
  -- continuity of the integrand on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6
      (Work.Construction.sepF a (Work.Construction.psiA α)) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α (n := 6) (k := 6) le_rfl ?_
    have h1 : ContDiffOn ℝ (6 : ℕ) (fun p : ℝ × ℝ => (1 + p.1) / (2 * α))
        Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div (contDiffOn_const.add contDiffOn_fst)
        (contDiffOn_const : ContDiffOn ℝ (6 : ℕ) (fun _ : ℝ × ℝ => 2 * α)
          Work.FTS.EllipticEst.Q0) ?_
      intro p hp
      exact ne_of_gt (by linarith : (0 : ℝ) < 2 * α)
    have h2 : ContDiffOn ℝ (6 : ℕ) (Function.uncurry (Work.FTS.StrongPersist.H6Rows.close6 α))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongPersist.H6Rows.contDiffOn_uncurry_sep6 α).congr
        (fun p _ => (Work.FTS.StrongPersist.H6Rows.sep6_eq_close6 α p.1 p.2).symm)
    have h3 : ContDiffOn ℝ (6 : ℕ) (Function.uncurry F0) Work.FTS.EllipticEst.Q0 :=
      (h1.mul h2).congr (fun p _ => rfl)
    rw [← hfun]
    exact h3
  refine Work.FTS.LocData.HkMem_of_majorant
    (f := Work.Construction.sepF a (Work.Construction.psiA α)) (M := Mmaj) α 6 hcont ?_ ?_ ?_
  · -- the angular slices of the majorant are integrable
    intro z hz
    rw [hMmaj]
    have hbase := Work.FTS.StrongPersist.H6Rows.integrableOn_gammaAngMaj6 (α := α) (D := D) hα hα1
    exact hbase.const_mul ((M' / (1 + z)) ^ 2)
  · -- the `z`-integral of the majorant is integrable
    rw [hMmaj]
    have hbase : IntegrableOn (fun z : ℝ =>
        ((M' ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.gammaAngMaj6 α D θ))
          * (1 / (1 + z) ^ 2)) Work.Spaces.Iz := Work.Elliptic.WtoH_IntZ.1.const_mul _
    refine hbase.congr_fun (fun z hz => ?_) measurableSet_Ici
    dsimp only
    have hkey : (1 : ℝ) / (1 + z) ^ 2 = (1 / (1 + z)) ^ 2 := by
      rw [div_pow, one_pow]
    rw [MeasureTheory.integral_const_mul, hkey]
    ring
  · -- the pointwise domination by the separable majorant
    intro z hz θ hθ
    rw [hMmaj]
    have hle := HkN_sepF_le (a := a) (M := M') (D := D) hα hα1 hM'pos hD 6 hMr'
      (fun i hi1 hi6 θ' hθ' => hDl α hα hα1 i hi1 hi6 θ' hθ') z hz θ hθ
    refine hle.trans (le_of_eq ?_)
    simp only [Work.FTS.StrongPersist.H6Rows.gammaAngMaj6]
    ring

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZaux.FKle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `NZaux/FKle` — the angular moment `FK (F_* + f)`

`|FK (F_* + f)(z)| ≤ 100(1+Cag)α^{-1/2}(1+M)` on `z > 0`, from the pointwise bound on `f` and
`|F_*| ≤ 20α·z/(1+z)² ≤ 5α` (via the `ℝ≥0∞`-form of the triangle inequality for the Bochner
integral and `volume Iθ = π/2`).
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The angular moment `FK (F_* + f)` is bounded by `100(1+Cag)α^{-1/2}(1+M)`. -/
theorem FK_le {α M Cag : ℝ} {f : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M)
    (hCag0 : 0 < Cag)
    (hX : Work.FTS.Nonlin.Xn α f ≤ M)
    (hsupf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f)
    {z : ℝ} (hz : 0 < z) :
    |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
      ≤ 100 * (1 + Cag) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hp0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0.le _
  have hC0 : 0 ≤ Cag * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCag0.le hp0
  have hc0 : 0 ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := by
    have : 0 ≤ Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := mul_nonneg hC0 hX0
    linarith
  -- the integral bound, in `ℝ≥0∞`
  have hstep : ENNReal.ofReal |Work.Construction.FK
        (fun z θ => Work.Construction.Fstar α z θ + f z θ) z|
      ≤ ENNReal.ofReal (3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f)
          * (Real.pi / 2)) := by
    have hFK : Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
        = ∫ θ in Work.Spaces.Iθ, (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
            * Work.Spaces.K θ := rfl
    rw [hFK]
    refine (Work.FTS.Nonlinear.Pieces.ofReal_abs_integral_le _ _ _).trans ?_
    have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
            * Work.Spaces.K θ|
          ≤ ENNReal.ofReal (3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α f)) := by
      filter_upwards [Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
        (fun θ hθ => hθ)] with θ hθ
      refine ENNReal.ofReal_le_ofReal ?_
      have hK : |Work.Spaces.K θ| ≤ 3 :=
        Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_K_abs_le ⟨hθ.1.le, hθ.2.le⟩
      have hF : |Work.Construction.Fstar α z θ| ≤ 5 * α := by
        refine le_trans (Work.FTS.NonlinRows.Rl1.Fstar_pt hα0 hα1 hz
          ⟨hθ.1.le, hθ.2.le⟩) ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (1 - z), hα0]
      have hf := hsupf z θ hz hθ.1 hθ.2
      have h1 : |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ| ≤ 5 * α
          + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f :=
        le_trans (abs_add_le _ _) (add_le_add hF hf)
      calc |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ * Work.Spaces.K θ|
          = |Work.Spaces.K θ| * |(fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ| := by
            rw [abs_mul]; ring
        _ ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :=
            mul_le_mul hK h1 (abs_nonneg _) (by norm_num)
    refine (MeasureTheory.lintegral_mono_ae hpt).trans ?_
    rw [MeasureTheory.setLIntegral_const, Work.Spaces.Iθ, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul hc0]
  rw [ENNReal.ofReal_le_ofReal_iff] at hstep
  · refine le_trans hstep ?_
    have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_le_four]
    have hp1 : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_rpow_neg_half hα0 hα1
    have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := by linarith
    have hM1 : (0 : ℝ) ≤ 1 + M := by linarith
    have hA0 : (0 : ℝ) ≤ 5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by
      have := mul_nonneg hC0 hX0
      linarith
    have h1 : 30 * α ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by nlinarith
    have h2 : 6 * (Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f)
        ≤ 100 * Cag * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
      have h := mul_le_mul_of_nonneg_left hX1 hC0
      have h3 := mul_nonneg hC0 hM1
      nlinarith [h, h3]
    calc 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) * (Real.pi / 2)
        ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) * 2 :=
          mul_le_mul_of_nonneg_left hpi (by linarith)
      _ = 30 * α + 6 * (Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ 100 * α ^ (-(1 / 2 : ℝ)) + 100 * Cag * α ^ (-(1 / 2 : ℝ)) * (1 + M) :=
          add_le_add h1 h2
      _ ≤ 100 * α ^ (-(1 / 2 : ℝ)) * (1 + M)
            + 100 * Cag * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
          have h4 : 100 * α ^ (-(1 / 2 : ℝ)) ≤ 100 * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by
            nlinarith [hp0, hM0]
          linarith
      _ = 100 * (1 + Cag) * α ^ (-(1 / 2 : ℝ)) * (1 + M) := by ring
  · have : 0 ≤ 3 * (5 * α + Cag * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := hc0
    positivity
end Work.FTS.StrongPersist.H6Rows
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the assembly

`main_bound_core` assembles the three pieces — the Leibniz remainder (`leibR_bound`), the
exceptional term (`main_bound_E`) and the signed radial IBP at the top slot (`fluxSix`, passed in
as `hflux`) — into the bound for the `canonW q`-weighted pairing of
`D_z^bD_θ^a(f·D_z g)` with `D_z^bD_θ^a g`, for `0 ≤ q ≤ γ` and `a + b ≤ 6`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 3200000


end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
