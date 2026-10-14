import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairBranches
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
-- ===== merged: Submission.Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 The nonlocal tail integral: order `4` from `ℋ⁵` -/

/-- **`L₁₂ f ∈ C⁴((0,∞))`** for a datum smooth on the open quadrant and honest in `ℋ⁵`.

`ℋ⁵` descends to `ℋ⁴` (`HkMem_of_le_of_smoothOpen`), and `contDiffOn_L12_k` with `k = 4`
gives the order-`4` regularity of the elliptic tail integral `Work.Elliptic.L12`; the
identification `Work.Construction.L12 = Work.Elliptic.L12` transfers it to the form used by
the radial profile `radA`. -/
theorem L12f_contDiffOn_four_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem
  have hEll : ContDiffOn ℝ 4 (Work.Elliptic.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem4 (by norm_num)
  have hCon : ContDiffOn ℝ 4 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact hEll
  have hfun : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
  rw [hfun]
  exact hCon

/-! ## §2 The radial profile `radA` -/

/-- **`radA α f ∈ C⁴((0,∞))`**: the two rational `z`-factors `a`, `b` are `C⁴` there (because
`c(α) ≠ 0` and `1 + z > 0`), and the only analytic input is `L₁₂ f ∈ C⁴((0,∞))`. -/
theorem radA_contDiffOn_four_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
  have h12 : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    L12f_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
      = fun z => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
    simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  exact ((((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1).of_le
      (by norm_num)).mul h12).neg).add
    (((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampB_div α).of_le
      (by norm_num)).mul contDiffOn_const)

/-! ## §3 The transfer defect `Corr` -/

/-- **`Corr α f ∈ C⁴` on the open quadrant.**  By `Corr_eq_sep` the defect is the separated
product `Γ(θ)·radA α f z`; writing `Γ α = c(α)·gamCoef α` turns it into the product of the
constant `c(α)` with the separated product `gamCoef α θ · radA α f z`, for which
`linMem_sep_mul` gives joint `C⁴`-regularity from the `C⁴`-regularity of `radA α f` alone. -/
theorem Corr_contDiffOn_four_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α f))
      Work.FTS.EllipticEst.Q0 := by
  have hradA : ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
    radA_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem
  have hsep := Work.FTS.StrongPersist.linMem_sep_mul (α := α) (n := 4)
    (B := Work.FTS.CoercivityFix.Transfer.radA α f) hradA
  have hfun : Work.FTS.CoercivityFix.Corr α f
      = fun z θ => Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z) := by
    funext z θ
    rw [Work.FTS.StrongPersist.H6Aux.Corr_eq_sep α f]
    show Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radA α f z
      = Work.Spaces.c α * (Work.FTS.StrongPersist.gamCoef α θ
          * Work.FTS.CoercivityFix.Transfer.radA α f z)
    rw [congrFun (Work.FTS.StrongPersist.H6Aux.Gam_eq_c_mul_gamCoef hα hα1) θ]
    ring
  rw [hfun]
  have hconst : ContDiffOn ℝ 4 (fun _ : ℝ × ℝ => Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 := contDiffOn_const
  refine (hconst.mul hsep).congr (fun p _ => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair]

/-! ## §4 The requested conjunction -/

theorem radA_Corr_contDiffOn_four {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) ∧
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.CoercivityFix.Corr α f))
        Work.FTS.EllipticEst.Q0 :=
  ⟨radA_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem,
    Corr_contDiffOn_four_of_smoothOpen hα hα1 hsm hmem⟩

end Work.FTS.GalFields.Norm
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integrable_pairing_Jeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Integrability of the leaf pairings against the mollifier `J_ε`

The three integrands of `integrable_pairing_Jeps` are, on the open quadrant,

* `w · J_ε(D_z^bD_θ^a u) · D_z^bD_θ^a v`,
* `w · (D_z^bD_θ^a u)²`,
* `w · (D_z^bD_θ^a v)²`

with `w` a leaf weight of the `IP4`-unfolding (`IsLeafW α a w`) and `(a,b)` a slot of order
`a + b ≤ 1`.  Each is dominated pointwise on the open quadrant by a sum of two
`ℋ¹`-integrands, which are integrable there:

* `w · (D_z^bD_θ^a f)² ≤ HkIntegrand α 1 f` for every `f` (`H6Pair6Aux.domLeaf_all`), so the
  second and third integrands are dominated by `HkIntegrand α 1 u` respectively
  `HkIntegrand α 1 v`;
* for the first one, `D_z^bD_θ^a (J_ε u) = J_ε (D_z^bD_θ^a u)` on the open quadrant
  (`mixed_Jeps`), and then AM–GM gives the bound `(HkIntegrand α 1 (J_ε u) + HkIntegrand α 1 v)/2`.

The only non-pointwise inputs are that those `ℋ¹`-integrands are integrable on the quadrant
(`integrable_HkIntegrand`, from `HkMem` and the continuity furnished by `SmoothOpen`) and that a
leaf weight is continuous there (`continuousOn_uncurry_leafW`, used exactly once, for the a.e.
strong measurability of the first integrand; for the other two the a.e. strong measurability is
read off from the pointwise domination).
-/


/-- The pointwise AM–GM estimate `|x| |y| ≤ (x² + y²)/2`. -/
private theorem abs_mul_le_half_sq (x y : ℝ) : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have h : 0 ≤ (|x| - |y|) ^ 2 := sq_nonneg _
  have h2 : (|x| - |y|) ^ 2 = |x| ^ 2 - 2 * |x| * |y| + |y| ^ 2 := by ring
  rw [h2] at h
  simp only [sq_abs] at h
  linarith

/-- **The `ℋ^k`-integrand is integrable on the open quadrant.**  `HkMem` supplies the angular
integrability at each `z` and the integrability of the outer integral; `SmoothOpen` supplies the
joint a.e. strong measurability (continuity on the open quadrant, the boundary being null); the
product-measure form is `Work.Spaces.integrable_prod_of_iterated`, and the restriction to the
open quadrant only lowers the measure (`Iz ×ˢ Iθ ⊇ Quad`). -/
private theorem integrable_HkIntegrand {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α k (fun n => hsm.forall n)
  have haesm : AEStronglyMeasurable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hprod : MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
      (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) haesm
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Eventually.of_forall fun z hz => hmem.1 z hz))
      hmem.2).1
  refine hprod.mono_measure ?_
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_mono
    (Set.prod_mono Set.Ioi_subset_Ici_self Set.Ioo_subset_Icc_self) le_rfl


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `α`-uniform jet bound of the radial factor `L₁₂(F_*)`

`H6N0Aux.nzl12Fstar_zop` bounds the `Zop`-iterates of `L₁₂(F_*)` by `(2α/3)·K₃ + 1`, a constant
which the proof obtains for a *fixed* `α`.  The level-six estimate of `NP6` needs one constant
that works for **every** `α ∈ (0,1]`: since `L₁₂(F_*) = 2α/(1+z)` on `(0,∞)` and only the factor
`α ≤ 1` matters, the same argument gives the `α`-free constant `(2/3)·K₃ + 1`. -/
theorem l12Fstar_dzdIter_uniform :
    ∃ Kφ : ℝ, 0 < Kφ ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z|
        ≤ Kφ := by
  obtain ⟨K3, hK3pos, hK3⟩ := Work.FTS.StrongPersist.L6Aux.PhiZopBound6
  refine ⟨(2 / 3) * K3 + 1, by linarith, ?_⟩
  intro α hαI b hb z hz
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hcongr : Work.Elliptic.DzdIter b
        (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z
      = Work.Elliptic.DzdIter b (fun y => 2 * α / (1 + y)) z :=
    Work.FTS.StrongPersist.DzdIter_congr_Ioi
      (fun y hy => Work.Construction.L12_Fstar_eq hα0 hα1 hy.le) b z hz
  rw [hcongr, ← Work.FTS.StrongPersist.H6Pair6Aux.Zop_iter_eq_DzdIter]
  rw [show (fun y : ℝ => 2 * α / (1 + y))
      = fun y : ℝ => (2 * α / 3) * (3 / (1 + y)) from by
    funext y; ring]
  rw [Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzZop_iter_const_mul]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α / 3)]
  have h := hK3 b hb z (le_of_lt hz)
  have hmono : (2 * α / 3) * |Work.Spaces.Zop^[b] (fun z => 3 / (1 + z)) z|
      ≤ (2 * α / 3) * K3 := mul_le_mul_of_nonneg_left h (by positivity)
  have hstep : (2 * α / 3) * K3 ≤ (2 / 3) * K3 := by nlinarith
  linarith [hmono, hstep]

/-!
Route hint.  `NP5b α w = (-1) • (c₂ₘ(θ) · (Lᵢ·D_z w))` and `NP6 α w = (-1) • (c₂ₘ(θ) · (L⋆·D_z w))`
with `Lᵢ z = L₁₂ w z` and `L⋆ z = L₁₂ (F_* α) z` (radial).  Use
`L3Rhs.ang_mul_HkSq_le 6` with `a := Work.Construction.c2m` (its hypotheses: `SmoothOpen` of
the angular profile, `|c2m| ≤ Cc` on `Iθ`, and `|D_θ^i c2m| ≤ Cc·sin(2θ)` for `1 ≤ i ≤ 6`; all
three are the bundle `H6Pair6Aux.T5bAux.c2mJets`), which reduces the claim to
`HkMem α 6 (L·D_z w)` (obtain it with `H6Rows.N0pair6Aux.HkMem_radial_mul6` for `NP5b`, and for
`NP6` with the same tool applied to the *bounded* radial factor `L⋆` — its jets are bounded by
a constant independent of α, see `H6Pair6Aux.H6N0Aux.nzl12Fstar_zop`).
Then the engine `Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split` at `X := L`,
`f := D_z w` gives `HkSq α 6 (L·D_z w) ≤ C (Blo² HkSq α 6 (D_z w) + Bhi² HkSq α 2 (D_z w))`,
with `Blo := CL4·Xn α w ≤ CL4·C₀·α²` (`L12Sup4`; for `NP6` take the constant jet bound `Kφ`
instead) and `Bhi := CL6·HkNorm α 6 w` (`L12Sup6`).  Finish with
`HkSq α 6 (D_z w) ≤ HkSq α 7 w`, `HkSq α 2 (D_z w) ≤ HkSq α 3 w ≤ HkSq α 4 w = (Xn α w)² ≤ C₀²α⁴`
(`H6Aux.HkSq_Dz_le_succ'`, `H6Aux.HkSq_mono_order`) and `HkSq_const_mul` for the scalar `-1`.

Note on the exact bracketing used here: the angular factor `c₂ₘ` is *commuted past* the radial
factor, so the engine is applied to `X z = L(z)` and the honest (angular × `D_z w`) field
`f z θ = -c₂ₘ(θ)·D_z w(z,θ)`.  This is what makes `SmoothOpen f` (needed by `ang_mul_HkSq_le`)
available from the open-quadrant smoothness of `w` alone: the radial factor `z ↦ L₁₂ w z` is
a priori only `C⁶` on `(0,∞)` (its `C^k`-regularity is bought with `HkMem α k w`, and the class
supplies that only up to `k = 10`).  The price is that the level-`2` angular estimate must be
run separately, at level `2`, where the small factor `|D_z w|_{ℋ²} ≤ C₀²` is available.
-/
theorem NP5b_NP6_HkSq6 : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) ∧
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmaj, hCmajpos, hCmaj⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 6
  obtain ⟨Cang2, hCang2pos, hCang2⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 2
  obtain ⟨Cc, hCcpos, hCcsm, hCcabs, hCcjet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨CL4, hCL4pos, hCL4⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨CL6, hCL6pos, hCL6⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  obtain ⟨Kφ, hKφpos, hKφ⟩ := l12Fstar_dzdIter_uniform
  intro C₀
  have hKbpos : 0 < Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1 := by
    have h : 0 ≤ Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 := by positivity
    linarith
  refine ⟨max (Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1)
    (Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) + 1), lt_max_of_lt_left hKbpos, ?_⟩
  intro α hαI w hcls hXw
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hL12zero : Work.Construction.L12 w 0 = 0 := hcls.l12
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsmw.Dz
  have hm6Dz : Work.Spaces.HkMem α 6 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 6 hsmw hm7
  have hm2Dz : Work.Spaces.HkMem α 2 (Work.Spaces.Dz w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmDz 2 (by norm_num) hm6Dz
  have hm3 : Work.Spaces.HkMem α 3 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 3 (by norm_num) hm7
  -- the side bounds on `D_z w`
  have hS6 : Work.Spaces.HkSq α 6 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 6 hsmw hm7
  have hS2a : Work.Spaces.HkSq α 2 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 3 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 2 hsmw hm3
  have h34 : Work.Spaces.HkSq α 3 w ≤ Work.Spaces.HkSq α 4 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm4
  have h4eq : Work.Spaces.HkSq α 4 w = (Work.FTS.Nonlin.Xn α w) ^ 2 := by
    change Work.Spaces.HkSq α 4 w = (Work.Spaces.HkNorm α 4 w) ^ 2
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 w)]
  have hx2 : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    have h0 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 := pow_le_pow_left₀ h0 hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ hα0.le hα1
  have hx2' : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 :=
    hx2.trans (by simpa using mul_le_of_le_one_right (sq_nonneg C₀) hα4le)
  have hS2 : Work.Spaces.HkSq α 2 (Work.Spaces.Dz w) ≤ C₀ ^ 2 := by
    have h : Work.Spaces.HkSq α 3 w ≤ (Work.FTS.Nonlin.Xn α w) ^ 2 := by
      rw [← h4eq]; exact h34
    exact hS2a.trans (h.trans hx2')
  -- the angular profile `c₂ₘ`
  have hCcjet6 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ Cc * Real.sin (2 * θ) :=
    fun i hi1 hi6 θ hθ => hCcjet i hi1 (by omega) 0 θ hθ
  have hCcjet2 : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ Cc * Real.sin (2 * θ) :=
    fun i hi1 hi2 θ hθ => hCcjet i hi1 (by omega) 0 θ hθ
  -- the angular factor, at levels `6` and `2`
  obtain ⟨hfa_mem, hfa_bd⟩ := hCang α hα0 hα1 Work.Construction.c2m Cc hCcpos hCcsm hCcabs
    hCcjet6 (Work.Spaces.Dz w) hsmDz hm6Dz
  obtain ⟨-, hfb_bd⟩ := hCang2 α hα0 hα1 Work.Construction.c2m Cc hCcpos hCcsm hCcabs
    hCcjet2 (Work.Spaces.Dz w) hsmDz hm2Dz
  set f : ℝ → ℝ → ℝ := fun z θ => (-1) * (Work.Construction.c2m θ * Work.Spaces.Dz w z θ)
    with hfdef
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hfdef]
    exact Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
        hsmDz)
  have hfmem : Work.Spaces.HkMem α 6 f := by
    rw [hfdef]
    exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) hfa_mem
  have hS6f : Work.Spaces.HkSq α 6 f ≤ Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w := by
    have hval : Work.Spaces.HkSq α 6 f
        = Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz w z θ) := by
      rw [hfdef, Work.FTS.StrongEps.HkSq_const_mul]
      ring
    rw [hval]
    exact hfa_bd.trans (mul_le_mul_of_nonneg_left hS6 (by positivity))
  have hS2f : Work.Spaces.HkSq α 2 f ≤ Cang2 * Cc ^ 2 * C₀ ^ 2 := by
    have hval : Work.Spaces.HkSq α 2 f
        = Work.Spaces.HkSq α 2 (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz w z θ) := by
      rw [hfdef, Work.FTS.StrongEps.HkSq_const_mul]
      ring
    rw [hval]
    exact hfb_bd.trans (mul_le_mul_of_nonneg_left hS2 (by positivity))
  -- smoothness of the radial factor `z ↦ L₁₂(w)(z)`
  have hL12cd10 : ContDiffOn ℝ 10 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 10 w hα0 hα1 hsmw hcls.mem10
      (by norm_num)
    refine h.congr (fun z _ => ?_)
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 w) z
  have hL12cd6 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) :=
    hL12cd10.of_le (by exact_mod_cast (by norm_num : 6 ≤ 10))
  have hnn7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hB6eq : (Work.Spaces.HkNorm α 6 w) ^ 2 = Work.Spaces.HkSq α 6 w := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 w)]
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm7
  have hBlon : 0 ≤ CL4 * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCL4pos.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hBhin : 0 ≤ CL6 * Work.Spaces.HkNorm α 6 w :=
    mul_nonneg hCL6pos.le (Work.Spaces.HkNorm_nonneg α 6 w)
  have hLo6 : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL4 * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hCL4 α w hα0 hα1 hsmw hm6 hL12zero j hj z hz
  have hHi6 : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL6 * Work.Spaces.HkNorm α 6 w :=
    fun j hj z hz => hCL6 α w hα0 hα1 hsmw hm6 hm7 hL12zero j hj z hz
  constructor
  · -- ## `NP5b`
    have heq : Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w
        = fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ := by
      rw [hfdef]
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5b]
      ring
    have hmain := hCmaj α (fun z => Work.Construction.L12 w z) f
      (CL4 * Work.FTS.Nonlin.Xn α w) (CL6 * Work.Spaces.HkNorm α 6 w)
      hL12cd6 hfsm hfmem hBlon hBhin hLo6 hHi6
    have hfin : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
        ≤ (Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
      have hstep : (CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
          + (CL6 * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f
          ≤ (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * Cc ^ 2 * C₀ ^ 2
              * Work.Spaces.HkSq α 7 w := by
        have t1 : (CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
            ≤ CL4 ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) * C₀ ^ 2 := by
          have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hx2' (sq_nonneg CL4)) hS6f
            (Work.Spaces.HkSq_nonneg α 6 f) (mul_nonneg (sq_nonneg CL4) (sq_nonneg C₀))
          calc (CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
              = (CL4 ^ 2 * (Work.FTS.Nonlin.Xn α w) ^ 2) * Work.Spaces.HkSq α 6 f := by ring
            _ ≤ (CL4 ^ 2 * C₀ ^ 2) * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) := hmul
            _ = CL4 ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) * C₀ ^ 2 := by ring
        have t2 : (CL6 * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f
            ≤ CL6 ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) * Work.Spaces.HkSq α 7 w := by
          rw [mul_pow, hB6eq]
          have hmul := mul_le_mul (mul_le_mul_of_nonneg_left h67 (sq_nonneg CL6)) hS2f
            (Work.Spaces.HkSq_nonneg α 2 f) (mul_nonneg (sq_nonneg CL6) hnn7)
          calc CL6 ^ 2 * Work.Spaces.HkSq α 6 w * Work.Spaces.HkSq α 2 f
              ≤ (CL6 ^ 2 * Work.Spaces.HkSq α 7 w) * (Cang2 * Cc ^ 2 * C₀ ^ 2) := hmul
            _ = CL6 ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) * Work.Spaces.HkSq α 7 w := by ring
        have hsum := add_le_add t1 t2
        have hnn1 : 0 ≤ CL4 ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) * C₀ ^ 2 := by
          positivity
        have hnn2 : 0 ≤ CL6 ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) * Work.Spaces.HkSq α 7 w := by
          positivity
        nlinarith [hsum, hnn1, hnn2]
      have hlast : Cmaj * ((CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * Cc ^ 2 * C₀ ^ 2
            * Work.Spaces.HkSq α 7 w)
          ≤ (Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
        have hcoef : 0 ≤ Cmaj * Cc ^ 2 * (CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * C₀ ^ 2 := by
          positivity
        nlinarith [hcoef, hnn7]
      calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
          = Work.Spaces.HkSq α 6 (fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ) :=
            by rw [heq]
        _ ≤ Cmaj * ((CL4 * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 6 f
              + (CL6 * Work.Spaces.HkNorm α 6 w) ^ 2 * Work.Spaces.HkSq α 2 f) := hmain
        _ ≤ Cmaj * ((CL4 ^ 2 * Cang + CL6 ^ 2 * Cang2) * Cc ^ 2 * C₀ ^ 2
              * Work.Spaces.HkSq α 7 w) := mul_le_mul_of_nonneg_left hstep hCmajpos.le
        _ ≤ _ := hlast
    exact hfin.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hnn7]))
  · -- ## `NP6`
    have heq6 : Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w
        = fun z θ =>
            (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z * f z θ := by
      rw [hfdef]
      funext z θ
      simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP6,
        Work.FTS.StrongPersist.H6Pair6Aux.NA6]
      ring
    have hFjet : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Elliptic.DzdIter j
          (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z| ≤ Kφ :=
      fun j hj z hz => hKφ α hαI j hj z hz
    have hFjet4 : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
        |Work.Elliptic.DzdIter j
          (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z| ≤ Kφ :=
      fun j hj z hz => hKφ α hαI j (by omega) z hz
    have hL12Fcd : ∀ n : ℕ,
        ContDiffOn ℝ n (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
          (Set.Ioi 0) := by
      intro n
      have hnum : ContDiffOn ℝ n (fun _ : ℝ => 2 * α) (Set.Ioi 0) := contDiffOn_const
      have hden : ContDiffOn ℝ n (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
        (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add contDiffOn_id
      have hbase : ContDiffOn ℝ n (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) :=
        hnum.div hden (fun z hz => by
          have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
          positivity)
      exact hbase.congr (fun z hz =>
        Work.Construction.L12_Fstar_eq hα0 hα1 (le_of_lt (Set.mem_Ioi.mp hz)))
    have hL12Fcd6 : ContDiffOn ℝ 6
        (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) :=
      hL12Fcd 6
    have hmain6 := hCmaj α (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) f
      Kφ Kφ hL12Fcd6 hfsm hfmem hKφpos.le hKφpos.le hFjet4 hFjet
    have hfin6 : Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
        ≤ (Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
      have hstep6 : Kφ ^ 2 * Work.Spaces.HkSq α 6 f + Kφ ^ 2 * Work.Spaces.HkSq α 2 f
          ≤ Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2)
              * (1 + Work.Spaces.HkSq α 7 w) := by
        have h1 : Kφ ^ 2 * Work.Spaces.HkSq α 6 f
            ≤ Kφ ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 7 w) :=
          mul_le_mul_of_nonneg_left hS6f (by positivity)
        have h2 : Kφ ^ 2 * Work.Spaces.HkSq α 2 f ≤ Kφ ^ 2 * (Cang2 * Cc ^ 2 * C₀ ^ 2) :=
          mul_le_mul_of_nonneg_left hS2f (by positivity)
        have hnn1 : 0 ≤ Kφ ^ 2 * Cc ^ 2 * Cang := by positivity
        have hnn2 : 0 ≤ Kφ ^ 2 * Cc ^ 2 * Cang2 * C₀ ^ 2 * Work.Spaces.HkSq α 7 w := by
          positivity
        nlinarith [h1, h2, hnn1, hnn2]
      have hlast : Cmaj * (Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2)
            * (1 + Work.Spaces.HkSq α 7 w))
          ≤ (Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) + 1)
            * (1 + Work.Spaces.HkSq α 7 w) := by
        have hcoef : 0 ≤ Cmaj * Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2) := by positivity
        nlinarith [hcoef, hnn7]
      calc Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
          = Work.Spaces.HkSq α 6 (fun z θ =>
              (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z * f z θ) :=
            by rw [heq6]
        _ ≤ Cmaj * (Kφ ^ 2 * Work.Spaces.HkSq α 6 f
              + Kφ ^ 2 * Work.Spaces.HkSq α 2 f) := hmain6
        _ ≤ Cmaj * (Kφ ^ 2 * Cc ^ 2 * (Cang + Cang2 * C₀ ^ 2)
              * (1 + Work.Spaces.HkSq α 7 w)) := mul_le_mul_of_nonneg_left hstep6 hCmajpos.le
        _ ≤ _ := hlast
    exact hfin6.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith [hnn7]))

end

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.GainMem.HkMem_Jeps_of_pointwise_gain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.GainMem

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `HkMem_Jeps_of_pointwise_gain`.
The integrated membership step of the `m`-order gain, with the *reference level* `k` decoupled
from the target level `M` (in `EpsE4Thr/StepMembership.lean`, `HkMem_Jeps_of_pointwise` forces the
reference level to be `m - 1`).  The proof is the same chain with `(m - 1) ↦ k` and the density
`Ψ = StepFacts.Psi ρ ε` replaced by the abstract `Λ`: `hP` gives per-slice finiteness
(`MeasureTheory.lintegral_lintegral_swap` with `hΛmeas`, `JepsHkMem.lintegral_thShift_le`,
`hΛcomp`, and `hMem.1` for the finiteness of the shifted slices), then the double-integral
finiteness (`MeasureTheory.setLIntegral_prod`, `HkSqAux.integral_shift_le`, `hΛmass`), then the two
`HkMem` clauses (`JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top`,
`JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps` / `…_slice`); `hΛjoint` is the pair measurability
for the double integral.  Read `StepMembership.lean` first: this is that file with `(m-1) ↦ k` and
the five density facts about `Ψ` replaced by the hypotheses `hΛ*` (the `hP` there uses the density
`Kd = ofReal (Ψ p) * ofReal (exp (2c|p|))`, so the intended instantiation is
`Λ p = Ψ ρ ε p * exp (2*c*(|p.1|+|p.2|))`). -/
theorem HkMem_Jeps_of_pointwise_gain {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {M k : ℕ} {ε c₀ : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {Λ : ℝ × ℝ → ℝ} (hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p) (hΛc : Continuous Λ)
    (hΛs : ∀ p : ℝ × ℝ, Λ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2)
    (hΛmeas : ∀ z : ℝ, 0 < z → AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Λ q.2) * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift z q.2.1) (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume))
    (hΛjoint : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Λ q.2) * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift q.1.1 q.2.1) (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume))
    (hΛcomp : ∀ z : ℝ, 0 < z → ∀ δ : ℝ, 0 ≤ δ → ∀ G : ℝ → ENNReal,
        AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume →
        (∫⁻ z' in Set.Ioi (0 : ℝ), G z') < ⊤ →
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * G (z * Real.exp (-(p.1)))) < ⊤)
    (hΛmass : ∀ δ : ℝ, 0 ≤ δ → (∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤)
    (hMem : Work.Spaces.HkMem α k f)
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
        ≤ ENNReal.ofReal c₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) :
    Work.Spaces.HkMem α M (Work.FTS.StrongEps.Jeps ρ ε f) := by
  obtain ⟨δ, hδ0, hJac0⟩ := HkSqAux.logJac_shift_le
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α k hf
  -- the `f`-side mass, as an `ℝ≥0∞`-integral
  have hGs_fin : (∫⁻ u' in Set.Ioi 0,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f u' θ)) < ⊤ := by
    have hHz : ENNReal.ofReal (Work.Spaces.HkSq α k f)
        = ∫⁻ u' in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f u' θ) := by
      rw [Work.Spaces.HkSq]
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMem.2
        (Eventually.of_forall fun z' => integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α k f z' θ)]
    have hIoi : (∫⁻ u' in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f u' θ))
        = ∫⁻ u' in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f u' θ) :=
      MeasureTheory.setLIntegral_congr
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
    rw [hIoi, ← hHz]
    exact ENNReal.ofReal_lt_top
  -- the angular slice of `J_ε f` is finite for every `z`
  have hslice_fin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
        < ⊤ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) 0 θ))
          = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      simp
    · have hGsz : ∀ p : ℝ × ℝ,
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
              (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))
            = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
        fun p => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hMem.1 _ (Work.FTS.StrongEps.zShift_pos hzpos).le)
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k f _ θ)).symm
      have hstep1 : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
          ≤ ENNReal.ofReal c₀
            * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))) := by
        calc (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
            ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2))) :=
              MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
                (fun θ hθ => hP z hz θ hθ)
          _ = ENNReal.ofReal c₀
                * (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2))) :=
              MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ = ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2)))) := by
              congr 1
              rw [MeasureTheory.lintegral_lintegral_swap
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (ν := MeasureTheory.volume) (hΛmeas z hzpos)]
              refine lintegral_congr fun p => ?_
              exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Λ p))
                (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))
                ENNReal.ofReal_ne_top
      have hstep2 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))) := by
        refine lintegral_mono fun p => mul_le_mul_of_nonneg_left ?_ zero_le
        exact JepsHkMem.lintegral_thShift_le
          (fun θ => ENNReal.ofReal
            (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)) p.2
      have hstep3 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))))
          = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)) := by
        refine lintegral_congr fun p => ?_
        rw [hGsz p]
      have hstep4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) := by
        refine lintegral_mono fun p => ?_
        have hexp : ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|))) := by
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have h2 : |p.2| ≤ |p.1| + |p.2| := le_add_of_nonneg_left (abs_nonneg _)
          linarith
        calc ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))
            = (ENNReal.ofReal (Λ p) * ENNReal.ofReal (Real.exp (3 * |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
              (mul_assoc _ _ _).symm
          _ ≤ (ENNReal.ofReal (Λ p)
                * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|))))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le) zero_le
          _ = ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) := rfl
      have hchain : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
        hstep2.trans ((le_of_eq hstep3).trans hstep4)
      -- the a.e. measurability of the slice mass, needed by `hΛcomp`
      have hGmeas : AEMeasurable (fun p₁ : ℝ => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k f (z * Real.exp (-p₁)) θ)) MeasureTheory.volume := by
        have hbase : AEMeasurable (fun p₁ : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (z * Real.exp (-p₁)) θ)) MeasureTheory.volume :=
          (JepsHkMem.aemeasurable_shift_z_pair
            (H := fun z' θ' => Work.Spaces.HkIntegrand α k f z' θ') hcont hzpos
            ).lintegral_prod_right
        refine hbase.congr (Eventually.of_forall fun p₁ => ?_)
        have hz' : z * Real.exp (-p₁) ∈ Work.Spaces.Iz :=
          (mul_pos hzpos (Real.exp_pos _)).le
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hMem.1 _ hz')
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k f _ θ)).symm
      have hfin_int : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
            * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)) < ⊤ := by
        have h := hΛcomp z hzpos 3 (by norm_num)
          (fun z' => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z' θ)) hGmeas hGs_fin
        simpa only [Work.FTS.StrongEps.zShift] using h
      exact lt_of_le_of_lt (hstep1.trans (mul_le_mul_of_nonneg_left hchain zero_le))
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_int)
  -- the double `z`,`θ`-integral is finite
  have hdouble : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)) < ⊤ := by
    have hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Λ q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := hΛjoint
    have hstep1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
        ≤ ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Λ p)
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2))) := by
      calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
          ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2))) :=
            MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
              (fun z hz => MeasureTheory.setLIntegral_mono'
                (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => hP z hz θ hθ))
        _ = ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
                ENNReal.ofReal (Λ p)
                  * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                      (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2))) := by
            rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun z => ?_
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have htriple : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)))
        = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2))) := by
      have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)))
          = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2))
              ∂MeasureTheory.volume ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
                (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
        exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
            ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2)))
          (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
            rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
              (ν := MeasureTheory.volume) _ _]
            exact hAe.lintegral_prod_right')).symm
      rw [hL]
      rw [MeasureTheory.lintegral_lintegral_swap
        (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (ν := MeasureTheory.volume) hAe]
      refine lintegral_congr fun p => ?_
      rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Λ p)) _
        ENNReal.ofReal_ne_top]
      congr 1
      rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
      exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
            (Work.FTS.StrongEps.zShift q.1 p.1)
            (Work.FTS.StrongEps.thShift q.2 p.2)))
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume) _ _]
          exact HkSqAux.aemeasurable_shift_slice hcont p)
    have hstep2 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
          * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2))))
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f)) :=
      lintegral_mono fun p => mul_le_mul_of_nonneg_left
        (HkSqAux.integral_shift_le (δ := δ) (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂) hMem hcont p)
        zero_le
    have hstep3 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f)))
        = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p
            * Real.exp (δ * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
      rw [← MeasureTheory.lintegral_mul_const'
        (ENNReal.ofReal (Work.Spaces.HkSq α k f)) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun p => ?_
      have hone : ENNReal.ofReal (Λ p) * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          = ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|))) :=
        (ENNReal.ofReal_mul (hΛ0 p)).symm
      calc ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f))
          = (ENNReal.ofReal (Λ p) * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.Spaces.HkSq α k f) := (mul_assoc _ _ _).symm
        _ = ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by rw [hone]
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
        ≤ ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Λ p)
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2))) := hstep1
      _ = ENNReal.ofReal c₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))) := by rw [htriple]
      _ ≤ ENNReal.ofReal c₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f))) :=
          mul_le_mul_of_nonneg_left hstep2 zero_le
      _ = ENNReal.ofReal c₀ * ((∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p
            * Real.exp (δ * (|p.1| + |p.2|))))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f)) := by rw [hstep3]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (hΛmass δ hδ0.le) ENNReal.ofReal_lt_top)
  -- the first `HkMem` component
  have hSliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ =>
        Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ =>
          Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) 0 θ) = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      exact integrableOn_zero
    · refine ⟨JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps_slice hρ.moll hε hf hzpos, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun θ => ?_) (hslice_fin z hz)
      rw [Real.enorm_eq_ofReal
        (Work.Spaces.HkIntegrand_nonneg α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)]
  exact ⟨hSliceInt, JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
    hSliceInt (JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps hρ.moll hε hf) hdouble⟩

end Work.FTS.StrongEps.EpsE4Thr.GainMem
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var_ioo =====
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

/-! ## The `L²`-route derivative with *interior* continuity only

`hasDerivAt_integral_diag_var` asks for the a.e. continuity of the time slices on the *closed*
interval `[0,T]`.  That hypothesis is **not** a consequence of the interior differentiability
(nothing controls the *values* of the slices at `0` and `T`: take `u s p = sin (log (1/s))` for
`s > 0`, which is differentiable on `(0,T)` with continuous derivative but has no limit at `0⁺`).
The difference-quotient argument, however, only uses a window `(τ-δ, τ+δ) ⊆ (0,T)` around the base
time, so the interior version is what the mathematics actually needs.

The reduction below is a *shift of the fake time*: put `s₀ = τ/2 > 0` and apply the `Icc`-version to
the family `(s, p) ↦ u (s + s₀) p` on the smaller interval `[0, T/2]`.  There the closed-interval
continuity *is* available (the shifted slices map a closed interval into the interior `(0,T)`), all
the other hypotheses transport because `s ↦ s + s₀` maps `[0,T/2]` into `[0,T]`, and the conclusion
is transported back by the chain rule with the inverse translation `s ↦ s - s₀`.

The two measure-theoretic inputs (translation is measure preserving for `volume.prod ν`, hence
preserves a.e.-strong measurability) are proved first. -/






end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSq_Jeps_step_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **One-order smoothing of `J_ε` at the price of `ε⁻²`** (the regularising property of the
log-coordinate mollifier, in the paper's weighted norm `HkSq`).

For `2 ≤ m ≤ 8`, a profile `u` smooth on the open quadrant with `HkMem α (m-1) u` has
`HkMem α m (J_ε u)` and `HkSq α m (J_ε u) ≤ C (ε⁻¹)² HkSq α (m-1) u`, with `C` absolute.

*Proof route.*  Per slot: for `(j,i)` with `i + j = m`,
* if `j ≥ 1`: route exactly *one* `z`-derivative onto the kernel,
  `D_z^jD_θ^i (J_ε u) = ∫ (∂_{p₁}Jker)(p) · (D_z^{j-1}D_θ^i u)(shift) dp`, leaving the order-`m-1`
  slot `(j-1,i)` of `u` (same weight type: the `η`-weight if `i = 0`, the `Wt`-weight if `i ≥ 1`);
* if `j = 0`, `i ≥ 2`: route exactly *one* `θ`-derivative,
  `D_θ^i (J_ε u) = 2 ∫ (∂_{p₂}Jker)(p) · (D_θ^{i-1}u)(shift) dp`, leaving `(0,i-1)`, `i-1 ≥ 1`
  (the `Wt`-weight on both sides);
* the only slot with `j = 0`, `i = 1` occurs at `m = 1` and is excluded by `m ≥ 2`; at `m = 2` the
  slots are `(2,0)`, `(1,1)` and `(0,2)`, all covered by the two rules above.

Each routed derivative costs `ε⁻¹` twice: once in `(∫|∂Jker|)^{1/2}` (since
`∫|∂_{p₁}Jker| = ε⁻¹∫|∂_{p₁}ρ|`) and once in `∫ |∂Jker| e^{c|p|} dp` after the change of
variables; the *unrouted* slots are Jensen with the probability kernel (`∫ Jker = 1`, no `ε`).
Then Jensen/`slot_sq_bound`, the two shift comparisons of the `HkIntegrand` weights
(`wdiv_shift_le`, `Wt_shift_le`), the log-coordinate Jacobian (`logJac_shift_le`) and
`HkIntegrand_mono`-type monotonicity `HkSq α 1 ≤ HkSq α (m-1)` finish it -- the *same* chain as
the proved `HkSqAux/HkIntegrand_Jeps_le_integral`.  The per-slot identity is
`mixed_Jeps_kernel_partial` with `(j',i') = (j-1,i)` resp. `(0,i-1)`.

Do **not** state this with `HkSq α 0` on the right, nor for `m = 1`: every `Wt`-weighted slot can
only be routed onto a leftover of `u` that still carries a `θ`-derivative (the `ℋ⁰`-version is
false: a profile oscillating in `θ` at frequency `≫ 1/ε` has
`HkSq α 1 (J_ε u) / HkSq α 0 u → ∞`). -/
theorem HkSq_Jeps_step_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (m : ℕ), 2 ≤ m → m ≤ 8 →
      ∀ (ε : ℝ), ε ∈ Set.Ioc 0 1 → ∀ u : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α (m - 1) u →
        Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) ∧
          Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u)
            ≤ C * (ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u :=
  Work.FTS.StrongEps.StepFacts.step_le_aux ρ hρ

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm =====
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

open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §1 The jet bound for `ampA` at order six -/

theorem Alt_ampA_dzdIter_bound6 : ∃ K : ℝ, 0 ≤ K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ j ≤ 6,
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K := by
  obtain ⟨K₀, hK₀, hK₀b⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 6
  refine ⟨20 * K₀, by positivity, ?_⟩
  intro α hαIoc j hj z hz
  have hcpos : 0 < Work.Spaces.c α := Work.FTS.StrongPersist.L3Aux.c_pos hαIoc.1 hαIoc.2
  have h2c : 2 / Work.Spaces.c α ≤ 20 := by
    rw [div_le_iff₀ hcpos]
    have h := (Work.Spaces.c_bounds α hαIoc.1 hαIoc.2).1
    linarith
  have hphi : |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ :=
    hK₀b j hj z hz
  calc |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z|
      = |Work.Spaces.Zop^[j] (Work.FTS.CoercivityFix.Transfer.ampA α) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[j] (fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2)) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c α)
          * Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
    _ = (2 / Work.Spaces.c α)
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c α) * K₀ := mul_le_mul_of_nonneg_left hphi (by positivity)
    _ ≤ 20 * K₀ := mul_le_mul_of_nonneg_right h2c hK₀

/-! ## §2 The pointwise decomposition of the radial slot sum -/

theorem Alt_SlotSum_radA_ptwise {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f)
    {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z
      ≤ 2 * (∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
            (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
              * Work.Coercivity.L12f f z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2)
          * (∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
              (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
  have hu6 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z' => Work.Coercivity.L12f f z') = fun z' => Work.Construction.L12 f z' :=
      rfl
    rw [hfun]
    exact h
  have hA6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_six_ampA hα hα1).mul hu6
  have hnegA6 : ContDiffOn ℝ 6 (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z')) (Set.Ioi (0 : ℝ)) := hA6.neg
  have hB6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z'
      / Work.Spaces.c α) (Set.Ioi (0 : ℝ)) := contDiffOn_six_ampB_div α
  have hBC6 : ContDiffOn ℝ 6 (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z'
      / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      (Set.Ioi (0 : ℝ)) := by
    have hconst : ContDiffOn ℝ 6 (fun _ : ℝ =>
        Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const
    have h1 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
        * (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α))
        (Set.Ioi (0 : ℝ)) := hconst.mul hB6
    refine h1.congr (fun z' _ => ?_)
    ring
  have hSlotEq : Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z
      = ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by
    rw [Work.FTS.StrongPersist.SlotSum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
  rw [hSlotEq]
  have hterm : ∀ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 2 * ((Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
                * Work.Coercivity.L12f f z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2)
            * ((Work.Elliptic.DzdIter q (fun z' =>
                  Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
                * (Work.Spaces.w z) ^ 2) := by
    intro q hq
    have hq6 : q ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
    -- the two summands of `radA` and their `D_z`-additivity
    have hcongr : Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z
        = Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z := by
      refine Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _
        (fun z' _ => ?_) q z hz
      rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
      simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
      ring
    have hdiff1 : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b
          (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z'))) z' := by
      intro b hb z' hz'
      have hb6 : b + 1 ≤ 6 := by omega
      have hcont : ContDiffOn ℝ (b + 1)
          (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')) (Set.Ioi (0 : ℝ)) :=
        hnegA6.of_le (by exact_mod_cast hb6)
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        hcont hz'
    have hdiff2 : ∀ b < q, ∀ z' ∈ Set.Ioi (0 : ℝ),
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b
          (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z' := by
      intro b hb z' hz'
      have hb6 : b + 1 ≤ 6 := by omega
      have hcont : ContDiffOn ℝ (b + 1)
          (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi (0 : ℝ)) :=
        hBC6.of_le (by exact_mod_cast hb6)
      rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
        hcont hz'
    have hadd : Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)) z
        = Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z')) z
          + Work.Elliptic.DzdIter q (fun z' =>
              (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
                * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff q _ _ hdiff1 hdiff2 z hz
    have hneg : Work.Elliptic.DzdIter q (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
          * Work.Coercivity.L12f f z')) z
        = - Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z') z := by
      have h1 : (fun z' => -(Work.FTS.CoercivityFix.Transfer.ampA α z'
            * Work.Coercivity.L12f f z'))
          = fun z' => (-1) * (Work.FTS.CoercivityFix.Transfer.ampA α z'
              * Work.Coercivity.L12f f z') := by
        funext z'; ring
      rw [h1, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
      ring
    have hbc : Work.Elliptic.DzdIter q (fun z' =>
          (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z
        = Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
          * Work.Elliptic.DzdIter q (fun z' =>
              Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z := by
      have h1 : (fun z' => (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
          = fun z' => Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              * (Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) := by
        funext z'; ring
      rw [h1, Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
        Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul,
        ← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    have hsq : (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        ≤ 2 * (Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
              * Work.Coercivity.L12f f z') z) ^ 2
          + 2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
              * Work.Elliptic.DzdIter q (fun z' =>
                  Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2 := by
      rw [hcongr, hadd, hneg, hbc]
      nlinarith [sq_nonneg (Work.Elliptic.DzdIter q (fun z' =>
            Work.FTS.CoercivityFix.Transfer.ampA α z' * Work.Coercivity.L12f f z') z
          + Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
            * Work.Elliptic.DzdIter q (fun z' =>
                Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z)]
    calc (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ (2 * (Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
                * Work.Coercivity.L12f f z') z) ^ 2
            + 2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
                * Work.Elliptic.DzdIter q (fun z' =>
                    Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2)
              * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = 2 * ((Work.Elliptic.DzdIter q (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
                * Work.Coercivity.L12f f z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (2 * (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2)
              * ((Work.Elliptic.DzdIter q (fun z' =>
                    Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
                  * (Work.Spaces.w z) ^ 2) := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## §3 Helpers for the end-to-end radial bound -/

theorem Alt_SlotSum_eq (B : ℝ → ℝ) (z : ℝ) :
    Work.FTS.StrongPersist.SlotSum B z
      = ∑ q ∈ Finset.range 7,
          (Work.Elliptic.DzdIter q B z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  rw [Work.FTS.StrongPersist.SlotSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Work.Elliptic.DzIter_rad]

theorem Alt_continuousOn_w : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (0 : ℝ)) := by
  have hEq : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hEq]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

theorem Alt_continuousOn_slotSum {A : ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n A (Set.Ioi (0 : ℝ))) :
    ContinuousOn (fun z => ∑ q ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter q A z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z => ∑ q ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter q A z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = fun z => ∑ q ∈ Finset.range (n + 1),
          ((Work.Spaces.Zop^[q] A) z * Work.Spaces.w z) ^ 2 := by
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    ring
  rw [hfun]
  refine continuousOn_finsetSum _ (fun q hq => ?_)
  have hq' : q ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
  refine ContinuousOn.pow ?_ 2
  refine ContinuousOn.mul ?_ Alt_continuousOn_w
  have hiter : ContinuousOn (Work.Spaces.Zop^[q] A) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
      (b := q) (n := n - q)
      (h.of_le (by exact_mod_cast (le_of_eq (Nat.add_sub_cancel' hq') : q + (n - q) ≤ n)))
  exact hiter

/-! ## §4 The end-to-end radial bound -/

theorem Alt_SlotSum_radA_le
    (hZop : ∃ C : ℝ, 0 < C ∧ ∀ (φ u : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ j ≤ 6, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j φ z| ≤ K) →
      ContDiffOn ℝ 6 φ (Set.Ioi (0 : ℝ)) → ContDiffOn ℝ 6 u (Set.Ioi (0 : ℝ)) →
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (∑ q ∈ Finset.range 7,
            (Work.Elliptic.DzdIter q (fun z' => φ z' * u z') z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ C * (1 + K) ^ 2
            * (∑ q ∈ Finset.range 7,
                (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
        MeasureTheory.IntegrableOn
          (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
          Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          ≤ C * Work.Spaces.HkSq α 6 f := by
  obtain ⟨Czop, hCzop, hzopb⟩ := hZop
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := Work.FTS.StrongPersist.L6Aux.L12SlotSum6
  obtain ⟨Cc0, hCc0pos, hC0b⟩ := Alt_C0_sq_le_HkSq6
  obtain ⟨Cb, hCbpos, hBb⟩ := Alt_slotSum_ampB_div_le
  obtain ⟨KA, hKA, hKAb⟩ := Alt_ampA_dzdIter_bound6
  refine ⟨2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb), ?_, ?_⟩
  · have h1 : 0 < Czop * (1 + KA) ^ 2 * C₁ := by
      have hK1 : 0 < 1 + KA := by linarith
      exact mul_pos (mul_pos hCzop (pow_pos hK1 2)) hC₁pos
    have h2 : 0 < Cc0 * Cb := mul_pos hCc0pos hCbpos
    linarith
  intro α hαIoc f hf hmem7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm hmem7
  have hu6 : ContDiffOn ℝ 6 (fun z' => Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) := by
    have h := Work.FTS.StrongPersist.contDiffOn6_L12_of (α := α) (f := f) hsm hmem7
    have hfun : (fun z' => Work.Coercivity.L12f f z')
        = fun z' => Work.Construction.L12 f z' := rfl
    rw [hfun]
    exact h
  have hA6 : ContDiffOn ℝ 6 (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z'
      * Work.Coercivity.L12f f z') (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_six_ampA hα hα1).mul hu6
  -- abbreviations
  set u : ℝ → ℝ := fun z' => Work.Coercivity.L12f f z' with hu
  set C0 : ℝ := Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 with hC0
  set S1 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z' * u z') z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS1
  set S2 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7, (Work.Elliptic.DzdIter q
      (fun z' => Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS2
  set Su : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q u z) ^ 2 * (Work.Spaces.w z) ^ 2 with hSu
  set S3 : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 7,
      (Work.Elliptic.DzdIter q (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2 with hS3
  have hSnn : ∀ S : ℝ → ℝ, (∀ z, 0 ≤ S z) → 0 ≤ ∫ z in Set.Ioi (0 : ℝ), S z :=
    fun S hS => integral_nonneg hS
  -- `L₁₂f`-slots: integrability and bound
  have hL12i := hC₁b α hα hα1 f hsm hmem6 hf.l12
  have hExp_eq : (fun z => ∑ q ∈ Finset.range 7,
      (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2) = Su := by
    rw [hSu, hu]
    funext z
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Work.Elliptic.DzIter_rad]
    rfl
  have hIzIoi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hIoiIz : Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz :=
    MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))
  have hUint : MeasureTheory.IntegrableOn Su (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := hL12i.1
    rw [hExp_eq] at h2
    exact h2.congr_set_ae hIoiIz
  have hUbd : (∫ z in Set.Ioi (0 : ℝ), Su z) ≤ C₁ * Work.Spaces.HkSq α 6 f := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ C₁ * Work.Spaces.HkSq α 6 f := hL12i.2
    rw [hExp_eq] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the z-multiplier bound
  have hZp : ∀ z ∈ Set.Ioi (0 : ℝ), S1 z ≤ Czop * (1 + KA) ^ 2 * Su z := by
    intro z hz
    have h := hzopb (fun z' => Work.FTS.CoercivityFix.Transfer.ampA α z') u KA hKA
      (fun j hj z' hz' => hKAb α hαIoc j hj z' hz') (contDiffOn_six_ampA hα hα1) hu6 z hz
    rwa [hS1, hSu]
  have hS1nn : ∀ z, 0 ≤ S1 z := by
    intro z
    rw [hS1]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS2nn : ∀ z, 0 ≤ S2 z := by
    intro z
    rw [hS2]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS3nn : ∀ z, 0 ≤ S3 z := by
    intro z
    rw [hS3]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS1int : MeasureTheory.IntegrableOn S1 (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (hUint.const_mul (Czop * (1 + KA) ^ 2)) ?_ ?_
    · rw [hS1]
      exact (Alt_continuousOn_slotSum (n := 6) hA6).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hS1nn z)]
      exact hZp z hz
  have hS1bd : (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ (Czop * (1 + KA) ^ 2) * (∫ z in Set.Ioi (0 : ℝ), Su z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall hS1nn) (hUint.const_mul (Czop * (1 + KA) ^ 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hZp)
    rwa [MeasureTheory.integral_const_mul] at h
  have hS2int : MeasureTheory.IntegrableOn S2 (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun z => ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := (hBb α hαIoc).1
    rw [← hS2] at h2
    exact h2.congr_set_ae hIoiIz
  have hS2bd : (∫ z in Set.Ioi (0 : ℝ), S2 z) ≤ Cb := by
    have h2 : (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
        (Work.Elliptic.DzdIter q (fun z' =>
          Work.FTS.CoercivityFix.Transfer.ampB α z' / Work.Spaces.c α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ Cb := (hBb α hαIoc).2
    rw [← hS2] at h2
    rwa [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm] at h2
  -- the pointwise majorant
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), S3 z ≤ 2 * S1 z + (2 * C0 ^ 2) * S2 z := by
    intro z hz
    rw [hS3, hS1, hS2, hC0]
    simp only
    rw [← Alt_SlotSum_eq (Work.FTS.CoercivityFix.Transfer.radA α f) z]
    exact Alt_SlotSum_radA_ptwise hα hα1 f hsm hmem7 hz
  have hMono : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hS3nn)
      ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2)))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
  have hSplit : (∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z))
      = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
        + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := by
    rw [MeasureTheory.integral_add (hS1int.const_mul 2) (hS2int.const_mul (2 * C0 ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hC0sq : C0 ^ 2 ≤ Cc0 * Work.Spaces.HkSq α 6 f := by
    rw [hC0]
    exact hC0b α hαIoc f hf hmem7
  have hCz : 0 ≤ Czop * (1 + KA) ^ 2 := mul_nonneg hCzop.le (sq_nonneg _)
  have hS2nnint : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), S2 z := integral_nonneg hS2nn
  have hstep1 : 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
      ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact hS1bd.trans (mul_le_mul_of_nonneg_left hUbd hCz)
  have hstep2 : (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z)
      ≤ (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := by
    have hb0 : 0 ≤ 2 * (Cc0 * Work.Spaces.HkSq α 6 f) :=
      le_trans (by positivity)
        (mul_le_mul_of_nonneg_left hC0sq (by norm_num))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hC0sq (by norm_num)) hS2bd
      hS2nnint hb0
  have hchain : (∫ z in Set.Ioi (0 : ℝ), S3 z)
      ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
    calc (∫ z in Set.Ioi (0 : ℝ), S3 z)
        ≤ ∫ z in Set.Ioi (0 : ℝ), (2 * S1 z + (2 * C0 ^ 2) * S2 z) := hMono
      _ = 2 * (∫ z in Set.Ioi (0 : ℝ), S1 z)
            + (2 * C0 ^ 2) * (∫ z in Set.Ioi (0 : ℝ), S2 z) := hSplit
      _ ≤ 2 * (Czop * (1 + KA) ^ 2 * (C₁ * Work.Spaces.HkSq α 6 f))
            + (2 * (Cc0 * Work.Spaces.HkSq α 6 f)) * Cb := add_le_add hstep1 hstep2
      _ = (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
          ring
  have hS3_eq : Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f)
      = S3 := by
    rw [hS3]
    funext z
    exact Alt_SlotSum_eq _ z
  refine ⟨?_, ?_⟩
  · have h2 : MeasureTheory.IntegrableOn S3 (Set.Ioi (0 : ℝ)) := by
      refine Integrable.mono' ((hS1int.const_mul 2).add (hS2int.const_mul (2 * C0 ^ 2))) ?_ ?_
      · rw [hS3]
        exact (Alt_continuousOn_slotSum (n := 6)
          (contDiffOn_six_radA hα hα1 hsm hmem7)).aestronglyMeasurable measurableSet_Ioi
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hS3nn z)]
        exact hpt z hz
    have h3 : MeasureTheory.IntegrableOn S3 Work.Spaces.Iz := h2.congr_set_ae hIzIoi
    rwa [← hS3_eq] at h3
  · have h2 : (∫ z in Work.Spaces.Iz, S3 z)
        ≤ (2 * (Czop * (1 + KA) ^ 2 * C₁) + 2 * (Cc0 * Cb)) * Work.Spaces.HkSq α 6 f := by
      rw [(MeasureTheory.setIntegral_congr_set (μ := volume) hIoiIz).symm]
      exact hchain
    rwa [← hS3_eq] at h2

/-- **The radial slot bound, end to end** (the `ZopSlotMul_le` multiplier estimate of the
sibling module instantiated in `Alt_SlotSum_radA_le`). -/
theorem Alt_SlotSum_radA_le' : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      MeasureTheory.IntegrableOn
        (Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          Work.FTS.StrongPersist.SlotSum (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        ≤ C * Work.Spaces.HkSq α 6 f :=
  Alt_SlotSum_radA_le Work.FTS.StrongPersist.H6Aux.ZopSlotMul_le

end Work.FTS.StrongPersist.H6Aux
end
end
