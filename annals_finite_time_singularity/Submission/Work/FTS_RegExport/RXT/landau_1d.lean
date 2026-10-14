import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_MuLipC.RowN0.DiffPointwise
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR1.pzIter_bound_weighted
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.VPDefs
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpAux.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.Sharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000


end Work.FTS.GalFields.RHS.Sharp
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rowsSplitsT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-- **The algebraic collapse of `N_*` at `λ = lamfun μ`** (the third conjunct of
`Work.FTS.NonlinRows.SplitsData`): for `μ ≠ -1` the coefficient
`μ + lamfun μ + μ·lamfun μ` equals `-μ`, so `N_* μ (lamfun μ) g = μ (D_z g - g) = NstarLam μ g`.

This is hypothesis-free (a polynomial identity in `μ`). -/
theorem nstar_lamfun_collapse (μ : ℝ) (hμ : μ ≠ -1) (g : Fn) (z θ : ℝ) :
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
      = Work.FTS.Nonlin.NstarLam μ g z θ := by
  have hμ1 : (1 : ℝ) + μ ≠ 0 := by intro h; exact hμ (by linarith)
  have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
    rw [Work.Construction.lamfun]
    field_simp
    ring
  simp only [Work.Construction.Nstar, Work.FTS.Nonlin.NstarLam, Work.Spaces.Dz]
  rw [hcoef]
  ring

/-- **The `L₁₂`/`FK`-additivity and the differentiability of `z ↦ L₁₂ g z` on `(0,∞)`**, in the
honest class (`SmoothOpen` + `HkMem α 4`) of the `ClassC` profile of `CtxT`.

Both are the open-quadrant (`SmoothOpen`) forms of the standing inputs of the split: `L₁₂` is
additive above `0` by `NZeroAux.L12add` (its two densities are integrable there, and the slices
are integrable by `SmoothOpen` + `HkMem`), the angular moment `FK` by
`EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem`, and the differentiability of `z ↦ L₁₂(g)(z)` is the
second conjunct of `NZeroAux.L12add`. -/
theorem l12FK_add_of_classC {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z) ∧
    (∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z) ∧
    (∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) := by
  have h := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hso hmem
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => h.2.1 z hz⟩
  · exact h.1 z hz.le
  · exact Work.FTS.StrongEps.EpsWPLim.FK_Fstar_add_of_SmoothOpen_HkMem hso hmem hz

theorem rowsSplitsT {α₂ Cs Ce : ℝ} :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.NonlinRows.SplitsData α g Φs Φg := by
  intro α g Φs Φg hctx
  obtain ⟨hα, hα1, _hαα₂, hg, _hco, hs, hell⟩ := hctx
  have hsmg : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 4 (by norm_num) hg.mem
  have hΦs : Work.FTS.EllipticEst.SmoothOpen Φs := hs.smooth
  have hΦg : Work.FTS.EllipticEst.SmoothOpen Φg := hell.smooth
  obtain ⟨hL, hFK, hL12⟩ := l12FK_add_of_classC hα hα1 hsmg hmem4
  refine ⟨?_, ?_, ?_⟩
  · -- ## the split of `N₀` (additivity of `∂_θ` and of `D_z` on `F = F_* + g`)
    intro z θ hq
    simpa only [add_assoc] using
      Work.FTS.StrongEps.ClassCRHS.N0_split_open hα hsmg z θ hq
  · -- ## the four-way split of `N`
    intro z θ hq
    exact Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hsmg hΦs hΦg hL hFK hL12 z θ hq
  · -- ## the collapse of `N_*` at `λ = lamfun μ`
    intro μ hμ z θ
    exact nstar_lamfun_collapse μ hμ g z θ

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.PT.Fstar_quad_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `open scoped Real` is needed for the notation `π` (= `Real.pi`) of the statement below:
-- the workspace sets `autoImplicit = false`, so without this scope `π` is not a name at all.
open scoped Real

namespace Work.FTS.StrongEps.E5Aux2.PT

/-!
# The quadrant bounds for the reference profile `F_*`

`F_*(z,θ) = α (Γ(θ)/c(α)) · 2z/(1+z)²` (`Work.Construction.Fstar α`) is the fixed profile of
Elgindi's self-similar solution.  This module records the three elementary facts about it on
the open quadrant `Q0 = (0,∞) × (0,π/2)`:

* `F_*` is `C²` there (it is `C^∞`, `SmoothQuad_Fstar`);
* `|F_*(z,θ)| ≤ α/c(α)`;
* `|∂_zF_*(z,θ)| ≤ 2α/c(α)`.

## Mathematics

All three are consequences of the separation of variables
`F_* = (2α/c) · Γ ⊗ h`, `h(z) = z/(1+z)²` (`FstarPkg.Fstar_eq_factored`), of the sharp
radial bound `h(z) ≤ 1/4` (the maximum of `z/(1+z)²`, attained at `z = 1`) for `z > 0`, and
of the *global* angular bound `|Γ(θ)| ≤ 1` for every real `θ`.

The last one is what the second and third conjuncts need, and it does **not** need
`θ ∈ Iθ`: the base of the real power is `u(θ) = sinθ cos²θ`, which lies in `[-1,1]` for every
`θ` (both factors are bounded by `1` in absolute value), and for the real power
`|x ^ y| ≤ |x| ^ y ≤ 1` whenever `0 ≤ y` and `|x| ≤ 1`
(`Real.abs_rpow_le_abs_rpow`, `Real.rpow_le_rpow`, `Real.rpow_le_one`; recall that for a
*negative* base Lean's `Real.rpow` is `|x|^y cos (πy)`, again of absolute value `≤ |x|^y`).

The radial derivative is handled through `D_zF_* = (α/c)(Γ · H)`,
`H(z) = 2z(1-z)/(1+z)³ = 2z h'(z)` (`FstarPkg.Dz_Fstar_eq_Hz`), together with the sharp
radial bound `|H(z)| ≤ 2h(z)` of `FstarSlotBounds` (`Hz_abs_le_hKer`); dividing by
`z > 0` turns `|z ∂_zF_*| ≤ (2α/c) z` into `|∂_zF_*| ≤ 2α/c`.

The normalisation constant only enters through its positivity `0 < c(α)`
(`L12fAux.c_pos`, valid for every `α > 0`): the constants `α/c` and `2α/c` are the sharp ones
of the paper and do *not* use the numerical range `1/10 ≤ c ≤ 10` of the `α ≤ 1` regime.
-/

/-- `|Γ(θ)| ≤ 1` for every real angle and every `α ≥ 0`: the base `sinθ cos²θ` of the real
power lies in `[-1,1]`, and `|x^y| ≤ |x|^y ≤ 1` for `0 ≤ y`, `|x| ≤ 1`. -/
lemma abs_Gam_le_one_quad {α θ : ℝ} (hα : 0 ≤ α) : |Work.Spaces.Gam α θ| ≤ 1 := by
  have hbase : |Real.sin θ * Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_mul]
    have hcos : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.cos θ)]
    calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one θ) hcos (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  rw [Work.Spaces.Gam]
  calc |(Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)| ≤ |Real.sin θ * Real.cos θ ^ 2| ^ (α / 3) :=
        Real.abs_rpow_le_abs_rpow _ _
    _ ≤ 1 ^ (α / 3) := Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)
    _ = 1 := Real.one_rpow _

/-- The radial factor `h(z) = z/(1+z)²` is at most `1/4` on `z > 0` (its maximum, at `z = 1`):
equivalently `(1+z)² ≥ 4z`. -/
lemma hKer_le_quarter_quad {z : ℝ} (hz : 0 < z) : Work.Spaces.hKer z ≤ 1 / 4 := by
  rw [Work.Spaces.hKer_apply, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z), hz]

theorem Fstar_quad_bounds {α : ℝ} (hα : 0 < α) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Fstar α z θ| ≤ α / Work.Spaces.c α) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz (Work.Construction.Fstar α) z θ| ≤ 2 * α / Work.Spaces.c α) := by
  have hcpos : 0 < Work.Spaces.c α := Work.FTS_RegExport.RXR5L.L12fAux.c_pos hα
  have hc0 : 0 ≤ Work.Spaces.c α := hcpos.le
  refine ⟨?_, ?_, ?_⟩
  · -- `F_*` is `C^∞` on the strip `(-1,∞) × (0,π/2)`, hence `C²` on the smaller quadrant `Q0`
    refine ((Work.FTS.LocData.SmoothQuad_Fstar α).mono ?_).of_le
      (by simp [Work.Stability.smoothOrder])
    intro p hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  · -- `|F_*| = (2α/c) |Γ| h ≤ (2α/c)·(1/4) = α/(2c) ≤ α/c`
    intro z θ hz hθ0 hθ1
    have hGam : |Work.Spaces.Gam α θ| ≤ 1 := abs_Gam_le_one_quad hα.le
    have hker : Work.Spaces.hKer z ≤ 1 / 4 := hKer_le_quarter_quad hz
    have hker0 : 0 ≤ Work.Spaces.hKer z := Work.FTS.StrongEps.E5Aux2.hKer_nonneg_of_pos hz
    have hcoef0 : 0 ≤ 2 * α / Work.Spaces.c α := div_nonneg (by linarith) hc0
    have hF : Work.Construction.Fstar α z θ
        = 2 * α / Work.Spaces.c α * Work.Spaces.Gam α θ * Work.Spaces.hKer z := by
      rw [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α]
    rw [hF, abs_mul, abs_mul, abs_of_pos (div_pos (by linarith) hcpos), abs_of_nonneg hker0]
    calc 2 * α / Work.Spaces.c α * |Work.Spaces.Gam α θ| * Work.Spaces.hKer z
        = (2 * α / Work.Spaces.c α) * (|Work.Spaces.Gam α θ| * Work.Spaces.hKer z) := by ring
      _ ≤ (2 * α / Work.Spaces.c α) * (1 * (1 / 4)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hGam hker hker0 (by norm_num)) hcoef0
      _ = (α / Work.Spaces.c α) * (1 / 2) := by ring
      _ ≤ (α / Work.Spaces.c α) * 1 :=
          mul_le_mul_of_nonneg_left (by norm_num) (div_nonneg hα.le hc0)
      _ = α / Work.Spaces.c α := by ring
  · -- `D_zF_* = (α/c)(Γ·H)` with `|H(z)| ≤ 2h(z)`, so `|z∂_zF_*| ≤ (2α/c)z`
    intro z θ hz hθ0 hθ1
    have hGam : |Work.Spaces.Gam α θ| ≤ 1 := abs_Gam_le_one_quad hα.le
    have hHz : |Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ 2 * Work.Spaces.hKer z :=
      Work.FTS.StrongEps.E5Aux2.Hz_abs_le_hKer hz
    have hker0 : 0 ≤ Work.Spaces.hKer z := Work.FTS.StrongEps.E5Aux2.hKer_nonneg_of_pos hz
    have hcoef0 : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hc0
    have hDz : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ (2 * α / Work.Spaces.c α) * z := by
      have hEq : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          = α / Work.Spaces.c α * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z) :=
        Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith)
      rw [hEq, abs_mul, abs_of_pos (div_pos hα hcpos), abs_mul]
      calc α / Work.Spaces.c α * (|Work.Spaces.Gam α θ| * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
          ≤ α / Work.Spaces.c α * (1 * (2 * Work.Spaces.hKer z)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hGam hHz (abs_nonneg _) (by norm_num)) hcoef0
        _ = 2 * α / Work.Spaces.c α * Work.Spaces.hKer z := by ring
        _ = 2 * α / Work.Spaces.c α * (z / (1 + z) ^ 2) := by rw [Work.Spaces.hKer_apply]
        _ ≤ 2 * α / Work.Spaces.c α * z := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) hc0)
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
            nlinarith [sq_nonneg z, hz]
    have hzpz : z * |Work.Spaces.pz (Work.Construction.Fstar α) z θ|
        = |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := by
      rw [show Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            = z * Work.Spaces.pz (Work.Construction.Fstar α) z θ from rfl, abs_mul,
        abs_of_pos hz]
    have hmain : z * |Work.Spaces.pz (Work.Construction.Fstar α) z θ|
        ≤ z * (2 * α / Work.Spaces.c α) := by
      rw [hzpz]
      linarith [hDz]
    exact le_of_mul_le_mul_left hmain hz

end Work.FTS.StrongEps.E5Aux2.PT
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TauZero =====
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
set_option linter.unusedVariables false

/-! ## Three small closure facts for the `ℋ^k`-machinery (as in the certificate module) -/

/-- `SmoothOpen` of a pointwise negation. -/
private theorem smoothOpen_neg {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have hfun : Function.uncurry (fun z θ => -f z θ) = -(Function.uncurry f) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.neg

/-- `HkMem` of a pointwise negation: the `ℋ^k`-integrand of `-f` *equals* that of `f`. -/
private theorem hkMem_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have hI : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    exact (hf.1 z hz).congr_fun (fun θ _ => (hI z θ).symm) measurableSet_Icc
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hI z θ)
    rw [h]
    exact hf.2

/-- `ℋ^k` is closed under subtraction for profiles smooth on the open quadrant. -/
private theorem hkMem_sub {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + -g z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.HkMem_add_open hf (smoothOpen_neg hg) hmf (hkMem_neg hmg)

/-- `HkNorm` only sees the pointwise values of the profile. -/
private theorem hkNorm_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) : Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => h z θ)]

/-! ## The `τ = 0` obligation of `EpsE4Thr` -/

/-- **The fake-time-`0` obligation of `EpsE4Thr` for `1 < C₀`.**

For a datum of the `hd`-class with `Xn α g₀ ≤ α²`, the projected mollified profile `J_ε g₀` lies in
the `C₀ α²`-ball for all sufficiently small `ε`.  (The statement is the *converse* of
`EpsE4Work/epsUniformMem_Jeps_bound.lean`, which extracts the same clause *from* the conclusion of
`EpsE4Thr`.)

*Proof.*  `J_ε g₀ = g₀ + (J_ε g₀ − g₀)`; the sharp triangle inequality `HkNorm_triangle` gives
`Xn α (J_ε g₀) ≤ Xn α g₀ + Xn α (J_ε g₀ − g₀)`, and the approximation estimate bounds the second
summand by `C ε Xn₅ α g₀`; the linear error is absorbed by the gap `C₀ − 1 > 0` once
`ε ≤ (C₀ − 1) α² / (C (Xn₅ α g₀ + 1))`. -/
theorem Jeps_smallBall_one_lt {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hρ : IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 1 < C₀)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (h4 : Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ C₀ * α ^ 2 := by
  -- the datum-side regularity of `hd`
  have hsm : Work.FTS.EllipticEst.SmoothOpen g₀ := (hd 1 one_pos).1
  have h6 : Work.Spaces.HkMem α 6 g₀ := (hd 1 one_pos).2.1
  have h5 : Work.Spaces.HkMem α 5 g₀ :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm h6
  have hm4 : Work.Spaces.HkMem α 4 g₀ := Work.FTS.OpenPkg.HkMem_four_of_five hsm h5
  -- the mollifier-approximation estimate
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le ρ hρ.moll
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  -- the gap produced by `1 < C₀`
  have hgap : 0 < C₀ - 1 := sub_pos.mpr hC₀
  have hden : 0 < C * (Work.Spaces.HkNorm α 5 g₀ + 1) :=
    mul_pos hCpos (by linarith [Work.Spaces.HkNorm_nonneg α 5 g₀])
  refine ⟨min 1 ((C₀ - 1) * α ^ 2 / (C * (Work.Spaces.HkNorm α 5 g₀ + 1))),
    lt_min one_pos (div_pos (mul_pos hgap hα2) hden), ?_⟩
  intro ε hε
  have hε1 : ε ≤ 1 := le_trans hε.2 (min_le_left _ _)
  have hεb : ε ≤ (C₀ - 1) * α ^ 2 / (C * (Work.Spaces.HkNorm α 5 g₀ + 1)) :=
    le_trans hε.2 (min_le_right _ _)
  have hεIoc : ε ∈ Set.Ioc 0 1 := ⟨hε.1, hε1⟩
  -- the two summands
  set J : ℝ → ℝ → ℝ := Jeps ρ ε g₀ with hJdef
  have hJsm : Work.FTS.EllipticEst.SmoothOpen J := (hd ε hε.1).2.2.reg
  have hJ7 : Work.Spaces.HkMem α 7 J := (hd ε hε.1).2.2.mem
  have hJmem : Work.Spaces.HkMem α 4 J :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hJsm hJ7
  have hDsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => J z θ - g₀ z θ) :=
    Work.FTS.EllipticEst.smoothOpen_sub hJsm hsm
  have hDmem : Work.Spaces.HkMem α 4 (fun z θ => J z θ - g₀ z θ) :=
    hkMem_sub hJsm hsm hJmem hm4
  -- the *sharp* triangle inequality for `J = g₀ + (J - g₀)`
  have htri : Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ + (J z θ - g₀ z θ))
      ≤ Work.Spaces.HkNorm α 4 g₀
          + Work.Spaces.HkNorm α 4 (fun z θ => J z θ - g₀ z θ) :=
    HkNorm_triangle α 4
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g₀).mp hsm)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hDsm) hm4 hDmem
  have hcongr : Work.Spaces.HkNorm α 4 J
      = Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ + (J z θ - g₀ z θ)) :=
    hkNorm_congr_pt (fun z θ => by ring)
  -- the approximation error
  have happ : Work.Spaces.HkNorm α 4 (fun z θ => J z θ - g₀ z θ)
      ≤ C * ε * Work.Spaces.HkNorm α 5 g₀ :=
    hC α hαIoc 4 ε hεIoc g₀ ((Work.FTS.EllipticEst.smoothOpen_iff_forall g₀).mp hsm) h5 hJmem
  -- the datum's bound
  have hg0 : Work.Spaces.HkNorm α 4 g₀ ≤ α ^ 2 := by
    simpa only [Work.FTS.Nonlin.Xn] using h4
  -- assembling
  have hstep : Work.Spaces.HkNorm α 4 J
      ≤ α ^ 2 + C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) := by
    rw [hcongr]
    refine htri.trans ?_
    have hN5' : C * ε * Work.Spaces.HkNorm α 5 g₀ ≤ C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) := by
      have : Work.Spaces.HkNorm α 5 g₀ ≤ Work.Spaces.HkNorm α 5 g₀ + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this (mul_nonneg hCpos.le hε.1.le)
    linarith [add_le_add hg0 (happ.trans hN5')]
  -- the error term is small: `C ε (‖g₀‖₅ + 1) ≤ (C₀ - 1) α²`
  have hεC : C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) ≤ (C₀ - 1) * α ^ 2 := by
    have h2 : ε * (C * (Work.Spaces.HkNorm α 5 g₀ + 1))
        ≤ ((C₀ - 1) * α ^ 2 / (C * (Work.Spaces.HkNorm α 5 g₀ + 1)))
          * (C * (Work.Spaces.HkNorm α 5 g₀ + 1)) :=
      mul_le_mul_of_nonneg_right hεb hden.le
    rw [div_mul_cancel₀ _ hden.ne'] at h2
    have h3 : C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1)
        = ε * (C * (Work.Spaces.HkNorm α 5 g₀ + 1)) := by
      ring
    rw [h3]; exact h2
  calc Work.FTS.Nonlin.Xn α J = Work.Spaces.HkNorm α 4 J := rfl
    _ ≤ α ^ 2 + C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) := hstep
    _ ≤ α ^ 2 + (C₀ - 1) * α ^ 2 := add_le_add le_rfl hεC
    _ = C₀ * α ^ 2 := by ring


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.Gf_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- **Global bound for the radial density `Gf`.**  For `0 < α ≤ 1` (so `β = 3/α - 1 ≥ 2 > 0`) and
`U ∈ ℋ⁰`, the radial density
`Gf α U z = w(z)² ∫₀¹ v^β M₁(zv) dv` (with `M₁ = mom U`,
`M₁(z) = ∫_θ U(z,θ)² sin(2θ)^{-η}`) is integrable on `(0,∞)`, and

  `∫_{(0,∞)} Gf α U z dz ≤ (1/β) · HkSq α 0 U`.

Route (one interval substitution plus one Tonelli on a *product*; `M₁` never has to be composed
with `t ↦ zt`):

1. `∫₀¹ v^β M₁(zv) dv = z^{-(β+1)} ∫₀^z t^β M₁(t) dt` for `z > 0`
   (`Work.FTS_EllLimOK.ProducerH.mom_subst`, from
   `Work.FTS.PhiStar.RadialWAux.integral_zero_one_rpow`).
2. On `t > 0`, `M₁(t) = A(t)/w(t)²` where `A = mass α U z = ∫_θ HkIntegrand α 0 U z θ`
   (`mass_eq_w2_mom`), so `t^β M₁(t) = t^{β+4} A(t) / (1+t)^4` (as `w(t)² = (1+t)^4/t^4`,
   `w_sq_mul_z4`); the inner integral `∫₀^z …` is `∫_{t∈(0,∞)} … · 1_{t<z} dt` (interval integral
   `0..z` = set integral over `Ioc 0 z` = set integral over `(0,∞)` of the indicator).
3. Tonelli on `(0,∞) × (0,∞)`: `∫_z w(z)²z^{-(β+1)}∫_t t^{β+4}A(t)/(1+t)^4 1_{t<z} dt dz =
   ∫_t t^{β+4}A(t)/(1+t)^4 [∫_{z>t} w(z)²z^{-(β+1)} dz] dt`;
   use `Work.FTS.H2.swap_iterated_integral_of_nonneg` with the *`t`-variable as the outer one*
   (so that the integrability of the `z`-outer partially integrated function, i.e. of `Gf`, is a
   *conclusion*, not a hypothesis).  The joint a.e. strong measurability is assembled from
   `mass_aesm`/`AEStronglyMeasurable.comp_fst` (the `t`-factor), the continuous `z`-factor
   (`AEStronglyMeasurable.comp_snd`) and the Borel set `{(t,z) : t < z}`; the `z`-slice is
   integrable because `∫_{z>t} w(z)²z^{-(β+1)} dz ≤ w(t)² ∫_{z>t} z^{-(β+1)} dz = w(t)² t^{-β}/β`
   (using `(1+z)^4/z^4 ≤ (1+t)^4/t^4` for `z ≥ t` and `β > 0`), and the `t`-outer function is
   integrable because `t^{β+4}/(1+t)^4 · w(t)² t^{-β}/β = 1/β`, so it is dominated by `A(t)/β`,
   which is integrable by `hU` (`mass_integrableOn`).
4. `∫_{(0,∞)} A = HkSq α 0 U` (`mass_Ioi_eq_HkSq`). -/
theorem Gf_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.IntegrableOn (Work.FTS_EllLimOK.ProducerH.Gf α U) (Set.Ioi 0) ∧
      ∫ z in Set.Ioi (0 : ℝ), Work.FTS_EllLimOK.ProducerH.Gf α U z
        ≤ (1 / Work.FTS_EllLimOK.ProducerH.beta α) * Work.Spaces.HkSq α 0 U := by
  -- The Tonelli kernel and its three defining facts.
  have hnn : ∀ t z : ℝ, 0 ≤ GfKer α U t z := fun t z => GfKer_nonneg α U t z
  have haesm : AEStronglyMeasurable (Function.uncurry (GfKer α U))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    (GfKer_aesm_slices hα hα1 hU).1
  have hsliceAll : ∀ t ∈ Set.Ioi (0 : ℝ),
      Integrable (fun z => GfKer α U t z) (volume.restrict (Set.Ioi 0)) :=
    (GfKer_aesm_slices hα hα1 hU).2
  have hslice : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      Integrable (fun z => GfKer α U t z) (volume.restrict (Set.Ioi 0)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi hsliceAll
  have htz : ∀ t ∈ Set.Ioi (0 : ℝ),
      ∫ z in Set.Ioi 0, GfKer α U t z ≤ mass α U t / beta α :=
    fun t ht => GfKer_touter_le hα hα1 ht
  -- Integrability of the `t`-outer function, by domination by `A(t)/β`.
  have haesmOut : AEStronglyMeasurable
      (fun t => ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      (volume.restrict (Set.Ioi 0)) := by
    have h := haesm.integral_prod_right'
    simpa only [Function.uncurry] using h
  have hIntMass : Integrable (fun t => mass α U t / beta α)
      (volume.restrict (Set.Ioi 0)) :=
    (mass_integrableOn α U hU).div_const _
  have hbnd : (fun t => ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      ≤ᵐ[volume.restrict (Set.Ioi 0)] (fun t => mass α U t / beta α) :=
    ae_restrict_of_forall_mem measurableSet_Ioi htz
  have hnorm : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ‖∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0))‖ ≤ mass α U t / beta α := by
    filter_upwards [hbnd] with t ht
    have hpos : 0 ≤ ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)) :=
      integral_nonneg (fun z => GfKer_nonneg α U t z)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact ht
  have houter : Integrable (fun t => ∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      (volume.restrict (Set.Ioi 0)) := hIntMass.mono' haesmOut hnorm
  -- Tonelli, with the `t`-variable outermost.
  obtain ⟨hswap, hIntZ, _⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := volume.restrict (Set.Ioi 0)) (ν := volume.restrict (Set.Ioi 0))
      (g := GfKer α U) hnn haesm hslice houter
  -- The `z`-slices of the kernel integrate back to `Gf`.
  have hzid : (fun z => ∫ t, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
      =ᵐ[volume.restrict (Set.Ioi 0)] Gf α U :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => GfKer_zslice (α := α) (U := U) hz)
  refine ⟨hIntZ.congr hzid, ?_⟩
  have hzid_int : ∫ z, Gf α U z ∂(volume.restrict (Set.Ioi 0))
      = ∫ z, (∫ t, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
          ∂(volume.restrict (Set.Ioi 0)) := (integral_congr_ae hzid).symm
  rw [hzid_int]
  calc ∫ z, (∫ t, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
        ∂(volume.restrict (Set.Ioi 0))
      = ∫ t, (∫ z, GfKer α U t z ∂(volume.restrict (Set.Ioi 0)))
          ∂(volume.restrict (Set.Ioi 0)) := hswap
    _ ≤ ∫ t, mass α U t / beta α ∂(volume.restrict (Set.Ioi 0)) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun t =>
            integral_nonneg (fun z => GfKer_nonneg α U t z))) hIntMass hbnd
    _ = (∫ t, mass α U t ∂(volume.restrict (Set.Ioi 0))) / beta α := integral_div _ _
    _ = (1 / beta α) * Work.Spaces.HkSq α 0 U := by
        rw [mass_Ioi_eq_HkSq α U, div_eq_mul_inv, one_div]
        exact mul_comm _ _

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.pzIterTwo_PhiTil_eq_psiP_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Topology

set_option linter.unusedVariables false

/-- The second iterated derivative at `1` of the power function `z ↦ z ^ p`:
`∂_z²(z^p)(1) = p(p-1)`.  (`Real.deriv_rpow_const` twice.) -/
private lemma iteratedDeriv_two_rpow_one (p : ℝ) :
    iteratedDeriv 2 (fun z : ℝ => z ^ p) 1 = p * (p - 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (fun z : ℝ => z ^ p) = fun z => p * z ^ (p - 1) := by
    funext z; exact Real.deriv_rpow_const z p
  rw [h1, deriv_const_mul_field, Real.deriv_rpow_const, Real.one_rpow]
  ring

/-- **The second `z`-derivative of `PhiTil` at `z = 1` splits along the gauge decomposition.**
Given the pointwise identity `PhiTil α g Ψ = psiP α (PhiTil α g Ψ) + κ · gaugeMode α` on the open
quadrant (`Qd = Ioi 0 ×ˢ Ioo 0 (π/2)`, the SB1′ decomposition), we have at `z = 1`

`∂_z²(PhiTil) = ∂_z²(psiP) + κ · ((3/α)(3/α+1)/cos θ)`,

since `∂_z² (z^{-3/α}/cos θ) = (−3/α)(−3/α−1)·z^{-3/α−2}/cos θ`, which at `z = 1` equals
`(3/α)(3/α+1)/cos θ`.
Route: for fixed `θ ∈ (0,π/2)` the slice `{z | z > 0}` lies in `Qd`, so `hdec` gives equality of
the two `z`-slices on the neighbourhood `Ioi 0` of `1`; transfer `∂_z²` with
`Filter.EventuallyEq.deriv_eq` (twice), then split with `GalApprox.pzIter_add` (needs
`ContDiffAt ℝ 2` of the `z`-slice of `psiP` — from `hP` — and of the gauge slice, from the
analyticity of `z^{-3/α}/cos θ` on `Qd`, `SB25.contDiffOn_uncurry_gaugeMode`) and
`PhiStar.pzIter_const_mul` (constant `κ`); finish with two derivative computations for
`z ↦ z^{-3/α}/cos θ` (`Real.hasDerivAt_rpow_const`, `deriv_const_mul`).
Consumed by `Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem pzIterTwo_PhiTil_eq_psiP_add {α : ℝ} {g Ψ : ℝ → ℝ → ℝ} {κ : ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ))
    (hP : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ)))
    (hdec : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.PhiTil α g Ψ z θ
        = Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (Work.Construction.PhiTil α g Ψ) 1 θ
      = Work.Spaces.pzIter 2
          (Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ)) 1 θ
        + κ * ((3 / α) * (3 / α + 1) / Real.cos θ) := by
  -- The two `z`-slices agree on the neighbourhood `Ioi 0` of `1`, by `hdec` on `Qd`.
  have hXeq : (fun z => Work.Construction.PhiTil α g Ψ z θ)
      =ᶠ[nhds (1 : ℝ)]
        (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) := by
    refine Filter.eventually_of_mem
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)) ?_
    intro z hz
    exact hdec z θ (by
      simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hz, hθ.1, hθ.2⟩)
  -- `C²` of the `psiP` slice, from `SmoothOpen`.
  have hPc : ContDiffAt ℝ 2
      (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ) 1 :=
    ((hP.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))).of_le (by decide)
  -- `C²` of the gauge slice, from analyticity on the open quadrant.
  have hGm : ContDiffAt ℝ 2 (fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ) 1 := by
    have hmem : (1, θ) ∈ Work.Construction.Qd := by
      simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨by norm_num, hθ.1, hθ.2⟩
    have h1 : ContDiffAt ℝ 2
        (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode α)) (1, θ) :=
      ((Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode α).of_le le_top).contDiffAt
        (Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds hmem)
    have h2 : ContDiffAt ℝ 2 (fun z : ℝ => (z, θ)) 1 :=
      (contDiffAt_id (x := (1 : ℝ))).prodMk (contDiffAt_const (c := θ))
    have h3 := h1.comp 1 h2
    have hfun : (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode α))
          ∘ (fun z : ℝ => (z, θ))
        = fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ := rfl
    rwa [hfun] at h3
  have hGmc : ContDiffAt ℝ 2 (fun z => κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) 1 :=
    (contDiffAt_const (c := κ)).mul hGm
  -- `∂_z² (z^{-3/α}/cos θ)_1 = (3/α)(3/α+1)/cos θ`.
  have hGm2 : iteratedDeriv 2 (fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ) 1
      = (3 / α) * (3 / α + 1) / Real.cos θ := by
    have hslice : (fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ)
        = fun z => (Real.cos θ)⁻¹ * z ^ (-(3 / α)) := by
      funext z
      rw [Work.FTS.StreamBdryIface.gaugeMode, div_eq_inv_mul, mul_comm]
    rw [hslice,
      iteratedDeriv_const_mul ((Real.cos θ)⁻¹)
        (Real.contDiffAt_rpow_const_of_ne (x := 1) (p := -(3 / α)) (n := 2) (by norm_num)),
      iteratedDeriv_two_rpow_one]
    have hp : (-(3 / α)) * (-(3 / α) - 1) = (3 / α) * (3 / α + 1) := by ring
    rw [hp]
    ring
  have hsum : (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ
        + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ)
      = (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ)
        + (fun z => κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) := rfl
  have hPit : iteratedDeriv 2
      (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ) 1
      = Work.Spaces.pzIter 2
          (Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ)) 1 θ :=
    (Work.Spaces.pzIter_eq_iteratedDeriv 2 _ 1 θ).symm
  rw [Work.Spaces.pzIter_eq_iteratedDeriv 2 _ 1 θ,
    Filter.EventuallyEq.iteratedDeriv_eq 2 hXeq, hsum,
    iteratedDeriv_add hPc hGmc, iteratedDeriv_const_mul κ hGm, hPit, hGm2]

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.SnPol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Homogeneity in a constant

The primitive slots (`∂_z`, `∂_θ`, the angular moment `FK`, and the three operators `ℛ`, `𝒰`,
`𝒱` built from them) commute with multiplication by a constant.  All of them are
unconditional: `deriv_const_mul_field` has no differentiability hypothesis, and the angular
moment is an integral. -/

/-- `∂_z` commutes with multiplication by a constant. -/
theorem pz_csmul (c : ℝ) (f : Fn) (z θ : ℝ) :
    Work.Spaces.pz (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pz f z θ :=
  Work.FTS.GalLimit.GalWeak.pz_const_mul c f z θ

/-- `∂_θ` commutes with multiplication by a constant. -/
theorem pth_csmul (c : ℝ) (f : Fn) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pth f z θ :=
  Work.FTS.GalLimit.GalWeak.pth_const_mul c f z θ

/-- `D_z = z ∂_z` commutes with multiplication by a constant. -/
theorem Dz_csmul (c : ℝ) (f : Fn) (z θ : ℝ) :
    Work.Spaces.Dz (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.Dz f z θ :=
  congrFun (congrFun (Work.FTS.EllipticEst.Dz_smul c f) z) θ

/-- The angular moment `FK` is homogeneous. -/
theorem FK_csmul (c : ℝ) (f : Fn) (z : ℝ) :
    Work.Construction.FK (fun z θ => c * f z θ) z = c * Work.Construction.FK f z := by
  simp only [Work.Construction.FK]
  rw [show (fun θ => (c * f z θ) * Work.Spaces.K θ)
      = (fun θ => c * (f z θ * Work.Spaces.K θ)) from by funext θ; ring]
  rw [MeasureTheory.integral_const_mul]

/-- `ℛ` is homogeneous. -/
theorem Rop_csmul (α c : ℝ) (Ψ : Fn) (z θ : ℝ) :
    Work.Construction.Rop α (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Construction.Rop α Ψ z θ := by
  simp only [Work.Construction.Rop, pz_csmul, pth_csmul]
  ring

/-- `𝒰` is homogeneous. -/
theorem Uop_csmul (α c : ℝ) (Ψ : Fn) (z θ : ℝ) :
    Work.Construction.Uop α (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Construction.Uop α Ψ z θ := by
  simp only [Work.Construction.Uop, pz_csmul]
  ring

/-- `𝒱` is homogeneous. -/
theorem Vop_csmul (c : ℝ) (Ψ : Fn) (z θ : ℝ) :
    Work.Construction.Vop (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Construction.Vop Ψ z θ := by
  simp only [Work.Construction.Vop, pth_csmul]
  ring

/-- The perturbative stream function `U_g = E g − (1/(4α))·sin 2θ·L₁₂(g)` is homogeneous in the
profile (this is where the `ℝ`-homogeneity of `E` and the homogeneity of `L₁₂` enter). -/
theorem Ug_csmul_fun {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) :
    Ug α E (fun z' θ' => c * g z' θ') = fun z θ => c * Ug α E g z θ := by
  funext z θ
  have hE : E (fun z' θ' => c * g z' θ') z θ = c * E g z θ :=
    congrFun (congrFun (hEsmul c g) z) θ
  have hL := Work.FTS.GalBasis.L12_const_mul c g z
  simp only [Ug, hE, hL]
  ring

/-! ## Homogeneity of the graded pieces of `Sn` -/

/-- `Lin1` is homogeneous in the profile. -/
theorem Lin1_csmul {α : ℝ} (Φs : Fn) (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) (z θ : ℝ) :
    Lin1 α Φs E (fun z' θ' => c * g z' θ') z θ = c * Lin1 α Φs E g z θ := by
  have hUg := Ug_csmul_fun (α := α) E hEsmul c g
  have hR : Work.Construction.Rop α (Ug α E (fun z' θ' => c * g z' θ')) z θ
      = c * Work.Construction.Rop α (Ug α E g) z θ := by
    rw [hUg]; exact Rop_csmul α c (Ug α E g) z θ
  have hU : Work.Construction.Uop α (Ug α E (fun z' θ' => c * g z' θ')) z θ
      = c * Work.Construction.Uop α (Ug α E g) z θ := by
    rw [hUg]; exact Uop_csmul α c (Ug α E g) z θ
  have hV : Work.Construction.Vop (Ug α E (fun z' θ' => c * g z' θ')) z θ
      = c * Work.Construction.Vop (Ug α E g) z θ := by
    rw [hUg]; exact Vop_csmul c (Ug α E g) z θ
  have hfk := FK_csmul c g z
  have hpt := pth_csmul c g z θ
  have hDz := Dz_csmul c g z θ
  simp only [Lin1, hR, hU, hV, hfk, hpt, hDz]
  ring

/-- `Bil1` is homogeneous in its **first** argument. -/
theorem Bil1_csmul_left {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (u d : Fn) (z θ : ℝ) :
    Bil1 α E (fun z' θ' => c * u z' θ') d z θ = c * Bil1 α E u d z θ := by
  have hUg := Ug_csmul_fun (α := α) E hEsmul c u
  have hR : Work.Construction.Rop α (Ug α E (fun z' θ' => c * u z' θ')) z θ
      = c * Work.Construction.Rop α (Ug α E u) z θ := by
    rw [hUg]; exact Rop_csmul α c (Ug α E u) z θ
  have hU : Work.Construction.Uop α (Ug α E (fun z' θ' => c * u z' θ')) z θ
      = c * Work.Construction.Uop α (Ug α E u) z θ := by
    rw [hUg]; exact Uop_csmul α c (Ug α E u) z θ
  have hV : Work.Construction.Vop (Ug α E (fun z' θ' => c * u z' θ')) z θ
      = c * Work.Construction.Vop (Ug α E u) z θ := by
    rw [hUg]; exact Vop_csmul c (Ug α E u) z θ
  have hfk := FK_csmul c u z
  simp only [Bil1, hR, hU, hV, hfk]
  ring

/-- `Bil1` is homogeneous in its **second** argument (pure pointwise algebra: the second
argument occurs only through `d`, `∂_θd`, `D_zd`). -/
theorem Bil1_csmul_right {α : ℝ} (E : Fn → Fn) (u : Fn) (c : ℝ) (d : Fn) (z θ : ℝ) :
    Bil1 α E u (fun z' θ' => c * d z' θ') z θ = c * Bil1 α E u d z θ := by
  have hpt := pth_csmul c d z θ
  have hDz := Dz_csmul c d z θ
  simp only [Bil1, hpt, hDz]
  ring

/-- `Quad1` is homogeneous of degree two. -/
theorem Quad1_csmul {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) (z θ : ℝ) :
    Quad1 α E (fun z' θ' => c * g z' θ') z θ = c ^ 2 * Quad1 α E g z θ := by
  have hQ : Quad1 α E (fun z' θ' => c * g z' θ') z θ
      = Bil1 α E (fun z' θ' => c * g z' θ') (fun z' θ' => c * g z' θ') z θ := rfl
  have hQ' : Quad1 α E g z θ = Bil1 α E g g z θ := rfl
  rw [hQ, hQ', Bil1_csmul_left E hEsmul c g (fun z' θ' => c * g z' θ') z θ,
    Bil1_csmul_right E g c g z θ]
  ring

/-! ## Function-level forms -/

/-- Function-level homogeneity of `Lin1`. -/
theorem Lin1_smul {α : ℝ} (Φs : Fn) (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) :
    Lin1 α Φs E (c • g) = fun z θ => c * Lin1 α Φs E g z θ := by
  funext z θ; exact Lin1_csmul Φs E hEsmul c g z θ

/-- Function-level homogeneity of `Quad1`. -/
theorem Quad1_smul {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) :
    Quad1 α E (c • g) = fun z θ => c ^ 2 * Quad1 α E g z θ := by
  funext z θ; exact Quad1_csmul E hEsmul c g z θ

/-- Function-level homogeneity of `Bil1` in its first argument. -/
theorem Bil1_smul_left {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (u d : Fn) :
    Bil1 α E (c • u) d = fun z θ => c * Bil1 α E u d z θ := by
  funext z θ; exact Bil1_csmul_left E hEsmul c u d z θ

/-- Function-level homogeneity of `Bil1` in its second argument. -/
theorem Bil1_smul_right {α : ℝ} (E : Fn → Fn) (u : Fn) (c : ℝ) (d : Fn) :
    Bil1 α E u (c • d) = fun z θ => c * Bil1 α E u d z θ := by
  funext z θ; exact Bil1_csmul_right E u c d z θ

/-! ## The graded pieces at a general linear combination -/

/-- `Lin1` is linear: `Lin1 (s•u + e•d) = s·Lin1 u + e·Lin1 d` on the open quadrant. -/
theorem Lin1_lin {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {u d : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (s e : ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Lin1 α Φs E (s • u + e • d) z θ = s * Lin1 α Φs E u z θ + e * Lin1 α Φs E d z θ := by
  intro z θ hz hθ0 hθ1
  have hsu : Work.FTS.ClassC.ClassC α (s • u) := Work.FTS.ClassC.classC_smul s hu
  have hed : Work.FTS.ClassC.ClassC α (e • d) := Work.FTS.ClassC.classC_smul e hd
  have hnp := (Work.FTS_MuLipC.Poly1.n_poly hα hα1 hsu hed hEadd hEsmul hstar hell).2.1
    z θ hz hθ0 hθ1
  rw [Lin1_smul Φs E hEsmul s u, Lin1_smul Φs E hEsmul e d] at hnp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hnp
  exact hnp

/-- `Quad1` is a quadratic form: at the linear combination `s•u + e•d`,
`Quad1 = s²·Quad1 u + s·e·(Bil1 u d + Bil1 d u) + e²·Quad1 d` on the open quadrant. -/
theorem Quad1_lin {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {u d : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (s e : ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Quad1 α E (s • u + e • d) z θ
        = s ^ 2 * Quad1 α E u z θ + s * e * (Bil1 α E u d z θ + Bil1 α E d u z θ)
          + e ^ 2 * Quad1 α E d z θ := by
  intro z θ hz hθ0 hθ1
  have hsu : Work.FTS.ClassC.ClassC α (s • u) := Work.FTS.ClassC.classC_smul s hu
  have hed : Work.FTS.ClassC.ClassC α (e • d) := Work.FTS.ClassC.classC_smul e hd
  have hnp := (Work.FTS_MuLipC.Poly1.n_poly hα hα1 hsu hed hEadd hEsmul hstar hell).2.2
    z θ hz hθ0 hθ1
  rw [Quad1_smul E hEsmul s u, Quad1_smul E hEsmul e d,
    Bil1_smul_left E hEsmul s u (e • d), Bil1_smul_right E u e d,
    Bil1_smul_left E hEsmul e d (s • u), Bil1_smul_right E d s u] at hnp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hnp
  ring_nf at hnp ⊢
  exact hnp

/-! ## The value of the field at a linear combination -/

/-- **The `N`-field at a linear combination of two `ClassC` profiles.**  Combining the three
conjuncts of `Poly1.n_poly` with `Lin1_lin` and `Quad1_lin`. -/
theorem Sn_comb {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {u d : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (s e : ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Sn α Φs E (s • u + e • d) z θ
        = C1 α Φs z θ + s * Lin1 α Φs E u z θ + e * Lin1 α Φs E d z θ
          + s ^ 2 * Quad1 α E u z θ
          + s * e * (Bil1 α E u d z θ + Bil1 α E d u z θ)
          + e ^ 2 * Quad1 α E d z θ := by
  intro z θ hz hθ0 hθ1
  have hsd : Work.FTS.ClassC.ClassC α (s • u + e • d) :=
    Work.FTS.ClassC.classC_add (Work.FTS.ClassC.classC_smul s hu)
      (Work.FTS.ClassC.classC_smul e hd)
  have h1 := (Work.FTS_MuLipC.Poly1.n_poly hα hα1 hsd (Work.FTS.ClassC.classC_zero α)
    hEadd hEsmul hstar hell).1 z θ hz hθ0 hθ1
  have h2 := Lin1_lin hα hα1 hEadd hEsmul hstar hell hu hd s e z θ hz hθ0 hθ1
  have h3 := Quad1_lin hα hα1 hEadd hEsmul hstar hell hu hd s e z θ hz hθ0 hθ1
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2, h3]
  ring

/-! ## The polarization identity -/

theorem SnPol {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {f f' : Work.FTS.Galerkin.Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hf' : Work.FTS.ClassC.ClassC α f') {t : ℝ} (ht : t ≠ 0) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Sn α Φs E f z θ - Work.FTS_MuLipC.Sn α Φs E f' z θ
        = (1 / (4 * t)) * (Work.FTS_MuLipC.Sn α Φs E (f + f' + t • (f - f')) z θ
            - Work.FTS_MuLipC.Sn α Φs E (f + f' - t • (f - f')) z θ
            + Work.FTS_MuLipC.Sn α Φs E (t • (f - f')) z θ
            - Work.FTS_MuLipC.Sn α Φs E (-(t • (f - f'))) z θ) := by
  -- the *subtractive* form of the linearity of `E` gives the additive one
  have hE0 : E 0 = 0 := by
    have h := hEadd 0 0
    rw [sub_self] at h
    simpa using h
  have hEneg : ∀ b : Fn, E (-b) = - E b := by
    intro b
    have h := hEadd 0 b
    rw [zero_sub, hE0] at h
    simpa using h
  have hEadd' : ∀ a b : Fn, E (a + b) = E a + E b := by
    intro a b
    have h := hEadd a (-b)
    rw [sub_neg_eq_add, hEneg] at h
    simpa using h
  intro z θ hz hθ0 hθ1
  -- the six values of the field, read off from `Sn_comb`
  have hF : Sn α Φs E f z θ
      = C1 α Φs z θ + Lin1 α Φs E f z θ + Quad1 α E f z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (1 : ℝ) 0 z θ hz hθ0 hθ1
    rw [show (1 : ℝ) • f + (0 : ℝ) • f' = f from by funext z θ; simp] at h
    simpa using h
  have hF' : Sn α Φs E f' z θ
      = C1 α Φs z θ + Lin1 α Φs E f' z θ + Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (0 : ℝ) 1 z θ hz hθ0 hθ1
    rw [show (0 : ℝ) • f + (1 : ℝ) • f' = f' from by funext z θ; simp] at h
    simpa using h
  have hP1 : Sn α Φs E (f + f' + t • (f - f')) z θ
      = C1 α Φs z θ + (1 + t) * Lin1 α Φs E f z θ + (1 - t) * Lin1 α Φs E f' z θ
        + (1 + t) ^ 2 * Quad1 α E f z θ
        + (1 + t) * (1 - t) * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + (1 - t) ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (1 + t) (1 - t) z θ hz hθ0 hθ1
    rwa [show (1 + t) • f + (1 - t) • f' = f + f' + t • (f - f') from by
      funext z θ; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring] at h
  have hP2 : Sn α Φs E (f + f' - t • (f - f')) z θ
      = C1 α Φs z θ + (1 - t) * Lin1 α Φs E f z θ + (1 + t) * Lin1 α Φs E f' z θ
        + (1 - t) ^ 2 * Quad1 α E f z θ
        + (1 - t) * (1 + t) * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + (1 + t) ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (1 - t) (1 + t) z θ hz hθ0 hθ1
    rwa [show (1 - t) • f + (1 + t) • f' = f + f' - t • (f - f') from by
      funext z θ; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring] at h
  have hP3 : Sn α Φs E (t • (f - f')) z θ
      = C1 α Φs z θ + t * Lin1 α Φs E f z θ + (-t) * Lin1 α Φs E f' z θ
        + t ^ 2 * Quad1 α E f z θ
        + t * (-t) * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + (-t) ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' t (-t) z θ hz hθ0 hθ1
    rwa [show t • f + (-t) • f' = t • (f - f') from by
      funext z θ; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring] at h
  have hP4 : Sn α Φs E (-(t • (f - f'))) z θ
      = C1 α Φs z θ + (-t) * Lin1 α Φs E f z θ + t * Lin1 α Φs E f' z θ
        + (-t) ^ 2 * Quad1 α E f z θ
        + (-t) * t * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + t ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (-t) t z θ hz hθ0 hθ1
    rwa [show (-t) • f + t • f' = -(t • (f - f')) from by
      funext z θ
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring] at h
  rw [hF, hF', hP1, hP2, hP3, hP4]
  field_simp
  ring

end Work.FTS_MuLipC.RowN
end
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN0.DiffEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN0

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "L12" => Work.Construction.L12
local notation "Sn0" => Work.FTS_MuLipC.Sn0
local notation "Xn" => Work.FTS.Nonlin.Xn
local notation "Hk" => Work.Spaces.HkIntegrand

/-- The `d`-slot coefficient of the majorant. -/
def A1const (C₀ α : ℝ) : ℝ :=
  (351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4 + 32 * α ^ 2

/-- The `f'`-slot coefficient of the majorant. -/
def A2const (Xd α : ℝ) : ℝ := (351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2

/-- The integrable majorant of the Hardy-weighted angular energy of the difference field. -/
def PhiC (α C₀ Xd : ℝ) (d f' : Fn) : ℝ → ℝ :=
  fun r => 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
    + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
    + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2)

/-- The unfolding of `PhiC` as an explicit three-term sum. -/
theorem PhiC_unfold (α C₀ Xd : ℝ) (d f' : Fn) :
    PhiC α C₀ Xd d f' = fun r => 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
      + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
      + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := rfl

/-- A.e. strong measurability of the `L₁₂`-density on `(0,∞)` from continuity of the datum on
the open quadrant. -/
theorem aesm_L12dens_of_continuousOn {F : Fn}
    (hc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens F)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcontK : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hcontK.comp continuous_snd).continuousOn
  have hdiv : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hK.mul hc).div continuousOn_fst (fun p hp => ne_of_gt (Set.mem_prod.mp hp).1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F p.1 p.2 / p.1) hdiv
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  have h3 : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens F)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    convert h using 1
    funext z
    rfl
  have hset : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Work.Spaces.Iz :=
    MeasureTheory.Ioi_ae_eq_Ici
  rw [MeasureTheory.Measure.restrict_congr_set hset]
  exact h3

/-- **The energy bound for the difference field**: for a.e. `r > 0` the Hardy-weighted angular
energy of `Sn0 α f - Sn0 α f'` is dominated by `PhiC`. -/
theorem diff_energy_le {α C₀ Xd : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 ≤ C₀)
    (hXdnn : 0 ≤ Xd) {f f' d : Fn} (hXf : Xn α f ≤ C₀ * α ^ 2) (hXd : Xn α d = Xd)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f')
    (hmd : Work.Spaces.HkMem α 4 d)
    (hddef : ∀ z θ, d z θ = f z θ - f' z θ) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * Work.Spaces.w r
        ≤ PhiC α C₀ Xd d f' r := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
  have hw1 : 1 ≤ Work.Spaces.w r := one_le_w hr
  have hw0 : 0 ≤ Work.Spaces.w r := le_trans zero_le_one hw1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r ≤ DiffMaj α C₀ Xd d f' r θ :=
    fun θ hθ => diff_pointwise_le hα hα1 hC₀ hXd hf hf' hd hmf hmf' hmd hddef hXf hr hθ
  have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
  have hzr : r ∈ Work.Spaces.Iz := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hr.le
  have hHkd : MeasureTheory.IntegrableOn (fun θ => Hk α 4 d r θ) Work.Spaces.Iθ := hmd.1 r hzr
  have hHkf : MeasureTheory.IntegrableOn (fun θ => Hk α 4 f' r θ) Work.Spaces.Iθ := hmf'.1 r hzr
  have hconstI : ∀ c : ℝ, MeasureTheory.IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ := fun c =>
    MeasureTheory.integrableOn_const (by
      rw [Work.Spaces.Iθ, Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have hDM : DiffMaj α C₀ Xd d f' r = fun θ => 3 * (A1const C₀ α * Hk α 4 d r θ
      + A2const Xd α * Hk α 4 f' r θ + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
    funext θ
    rw [DiffMaj, A1const, A2const]
  have h3c : MeasureTheory.IntegrableOn
      (fun _ : ℝ => 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) Work.Spaces.Iθ :=
    hconstI _
  have hInt : MeasureTheory.IntegrableOn (fun θ => DiffMaj α C₀ Xd d f' r θ) Work.Spaces.Iθ := by
    rw [hDM]
    exact (((hHkd.const_mul (A1const C₀ α)).add
      (hHkf.const_mul (A2const Xd α))).add h3c).const_mul 3
  have hIoo : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  have hbd : (fun θ => (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => DiffMaj α C₀ Xd d f' r θ) := by
    rw [hIoo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => by simpa only [Work.Spaces.Iθ] using hpt θ hθ)
  have hstep : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        * Work.Spaces.w r) ≤ ∫ θ in Work.Spaces.Iθ, DiffMaj α C₀ Xd d f' r θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) hw0) hInt hbd
  have hleft : (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2
        * Work.Spaces.w r)
      = (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * Work.Spaces.w r :=
    MeasureTheory.integral_mul_const _ _
  -- the `θ`-integral of the majorant
  have h1 : MeasureTheory.IntegrableOn (fun θ => A1const C₀ α * Hk α 4 d r θ) Work.Spaces.Iθ :=
    hHkd.const_mul (A1const C₀ α)
  have h2 : MeasureTheory.IntegrableOn (fun θ => A2const Xd α * Hk α 4 f' r θ) Work.Spaces.Iθ :=
    hHkf.const_mul (A2const Xd α)
  have f1 : (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
        + A2const Xd α * Hk α 4 f' r θ))
      = (∫ θ in Work.Spaces.Iθ, A1const C₀ α * Hk α 4 d r θ)
        + (∫ θ in Work.Spaces.Iθ, A2const Xd α * Hk α 4 f' r θ) :=
    MeasureTheory.integral_add h1 h2
  have f2 : (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
        + A2const Xd α * Hk α 4 f' r θ + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
          + A2const Xd α * Hk α 4 f' r θ))
        + (∫ θ in Work.Spaces.Iθ, 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) :=
    MeasureTheory.integral_add (h1.add h2) h3c
  have f3 : (∫ θ in Work.Spaces.Iθ, A1const C₀ α * Hk α 4 d r θ)
      = A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ) :=
    MeasureTheory.integral_const_mul _ _
  have f4 : (∫ θ in Work.Spaces.Iθ, A2const Xd α * Hk α 4 f' r θ)
      = A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ) :=
    MeasureTheory.integral_const_mul _ _
  have f5 : (∫ θ in Work.Spaces.Iθ, 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2)
      = 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2) :=
    Work.FTS.Nonlinear.Pieces.integral_const_Iθ_ra _
  have hTheta : (∫ θ in Work.Spaces.Iθ, (A1const C₀ α * Hk α 4 d r θ
        + A2const Xd α * Hk α 4 f' r θ + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2))
      = A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2) := by
    rw [f2, f1, f3, f4, f5]
  have hTheta' : (∫ θ in Work.Spaces.Iθ, DiffMaj α C₀ Xd d f' r θ)
      = 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
          + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
          + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2)) := by
    rw [hDM, MeasureTheory.integral_const_mul, hTheta]
  have hfin : 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2))
      ≤ 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 3)
    have hpi : Real.pi / 2 ≤ 2 := by
      have := Real.pi_lt_four; linarith
    have hc : 0 ≤ α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 := by positivity
    nlinarith [hpi, hc]
  calc (∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2) * Work.Spaces.w r
      = ∫ θ in Work.Spaces.Iθ, (Sn0 α f r θ - Sn0 α f' r θ) ^ 2 * Work.Spaces.w r :=
        hleft.symm
    _ ≤ ∫ θ in Work.Spaces.Iθ, DiffMaj α C₀ Xd d f' r θ := hstep
    _ = 3 * (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
          + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
          + 352800 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2 * (Real.pi / 2)) := hTheta'
    _ ≤ PhiC α C₀ Xd d f' r := hfin

/-- The majorant `PhiC` is integrable on `(0,∞)`. -/
theorem integrableOn_PhiC {α C₀ Xd : ℝ} {d f' : Fn}
    (hmd : Work.Spaces.HkMem α 4 d) (hmf' : Work.Spaces.HkMem α 4 f') :
    MeasureTheory.IntegrableOn (PhiC α C₀ Xd d f') (Set.Ioi (0 : ℝ)) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun r => A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
      (Set.Ioi (0 : ℝ)) :=
    (hmd.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have h2 : MeasureTheory.IntegrableOn
      (fun r => A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
      (Set.Ioi (0 : ℝ)) :=
    (hmf'.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have h3 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  rw [PhiC_unfold α C₀ Xd d f']
  exact ((h1.add h2).add h3).const_mul 3

/-- The explicit constant `M` with `∫ Φ ≤ M·|d|²_{ℋ⁴}`. -/
def Mconst (C₀ α : ℝ) : ℝ :=
  3 * (180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4 + 1412000 * α ^ 2) + 1

theorem Mconst_nonneg (C₀ α : ℝ) : 0 ≤ Mconst C₀ α := by
  rw [Mconst]
  have h1 : (0 : ℝ) ≤ 180 * C₀ ^ 2 * α ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 220 * C₀ ^ 2 * α ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ 1412000 * α ^ 2 := by positivity
  linarith

/-- **The integral of the majorant** is bounded by `Mconst C₀ α · |d|²_{ℋ⁴}`. -/
theorem int_PhiC_le {α C₀ Xd : ℝ} (hXd : 0 ≤ Xd) {f' d : Fn}
    (hmd : Work.Spaces.HkMem α 4 d) (hmf' : Work.Spaces.HkMem α 4 f')
    (hXdd : Xn α d = Xd) (hXf' : Xn α f' ≤ C₀ * α ^ 2) (hC₀ : 0 ≤ C₀) (hα : 0 < α) :
    (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd d f' r) ≤ Mconst C₀ α * Xd ^ 2 := by
  have hPsid : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)) = Xd ^ 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
        = Work.Spaces.HkSq α 4 d := by
      rw [Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : Xd ^ 2 = Work.Spaces.HkSq α 4 d := by
      rw [← hXdd, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 d)]
    rw [h1, h2]
  have hPsif : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
      ≤ C₀ ^ 2 * α ^ 4 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
        = Work.Spaces.HkSq α 4 f' := by
      rw [Work.Spaces.HkSq, Work.Spaces.Iz]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    have h2 : Work.Spaces.HkSq α 4 f' = (Xn α f') ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f')]
    have h3 : (Xn α f') ^ 2 ≤ (C₀ * α ^ 2) ^ 2 := by
      have h0 : 0 ≤ Xn α f' := Work.Spaces.HkNorm_nonneg α 4 f'
      nlinarith [hXf', h0]
    rw [h1, h2]
    calc (Xn α f') ^ 2 ≤ (C₀ * α ^ 2) ^ 2 := h3
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hInv : (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
  have hInt1 : MeasureTheory.IntegrableOn (fun r => A1const C₀ α
      * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)) (Set.Ioi (0 : ℝ)) :=
    (hmd.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have hInt2 : MeasureTheory.IntegrableOn (fun r => A2const Xd α
      * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)) (Set.Ioi (0 : ℝ)) :=
    (hmf'.2.mono_set Set.Ioi_subset_Ici_self).const_mul _
  have hInt3 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.InvOneAddSq.1.const_mul _
  have e1 : (∫ r in Set.Ioi (0 : ℝ), (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)))
      = (∫ r in Set.Ioi (0 : ℝ), A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
        + (∫ r in Set.Ioi (0 : ℝ), A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)) :=
    MeasureTheory.integral_add hInt1 hInt2
  have e2 : (∫ r in Set.Ioi (0 : ℝ), (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
        + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)
        + 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2))
      = (∫ r in Set.Ioi (0 : ℝ), (A1const C₀ α * (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ)
          + A2const Xd α * (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ)))
        + (∫ r in Set.Ioi (0 : ℝ), 705600 * α ^ 2 * Xd ^ 2 * (1 / (1 + r)) ^ 2) :=
    MeasureTheory.integral_add (hInt1.add hInt2) hInt3
  have hval : (∫ r in Set.Ioi (0 : ℝ), PhiC α C₀ Xd d f' r)
      = 3 * (A1const C₀ α
            * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
          + A2const Xd α
            * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
          + 705600 * α ^ 2 * Xd ^ 2
            * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)) := by
    rw [PhiC_unfold α C₀ Xd d f', MeasureTheory.integral_const_mul, e2, e1,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hval]
  have hbInv : 705600 * α ^ 2 * Xd ^ 2 * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      ≤ 705600 * α ^ 2 * Xd ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hInv (by positivity)
  have hb2 : A2const Xd α * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
      ≤ ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2 := by
    rw [A2const]
    have h0 : 0 ≤ (351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2 := by positivity
    calc ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2)
          * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
        ≤ ((351 : ℝ) / 4 * (Xd ^ 2 / α ^ 2) + 108 * Xd ^ 2) * (C₀ ^ 2 * α ^ 4) :=
          mul_le_mul_of_nonneg_left hPsif h0
      _ = ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2 := by
          first | (field_simp; ring) | field_simp
  have hfin : 3 * (A1const C₀ α * Xd ^ 2
        + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2
        + 705600 * α ^ 2 * Xd ^ 2 * 2) ≤ Mconst C₀ α * Xd ^ 2 := by
    rw [Mconst]
    have hfact : 3 * (A1const C₀ α * Xd ^ 2
          + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2
          + 705600 * α ^ 2 * Xd ^ 2 * 2)
        = 3 * Xd ^ 2 * (A1const C₀ α + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2
            + 108 * C₀ ^ 2 * α ^ 4) + 1411200 * α ^ 2) := by ring
    rw [hfact]
    have hb : A1const C₀ α + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4)
          + 1411200 * α ^ 2 ≤ 180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4
          + 1412000 * α ^ 2 := by
      rw [A1const]
      have h1 : (0 : ℝ) ≤ C₀ ^ 2 * α ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ C₀ ^ 2 * α ^ 4 := by positivity
      have h3 : (0 : ℝ) ≤ α ^ 2 := by positivity
      linarith
    calc 3 * Xd ^ 2 * (A1const C₀ α + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2
            + 108 * C₀ ^ 2 * α ^ 4) + 1411200 * α ^ 2)
        ≤ 3 * Xd ^ 2 * (180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4 + 1412000 * α ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (3 * (180 * C₀ ^ 2 * α ^ 2 + 220 * C₀ ^ 2 * α ^ 4 + 1412000 * α ^ 2) + 1)
            * Xd ^ 2 := by nlinarith [sq_nonneg Xd]
  calc 3 * (A1const C₀ α * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 d r θ))
        + A2const Xd α * (∫ r in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Hk α 4 f' r θ))
        + 705600 * α ^ 2 * Xd ^ 2 * (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2))
      ≤ 3 * (A1const C₀ α * Xd ^ 2
        + ((351 : ℝ) / 4 * C₀ ^ 2 * α ^ 2 + 108 * C₀ ^ 2 * α ^ 4) * Xd ^ 2
        + 705600 * α ^ 2 * Xd ^ 2 * 2) := by
        rw [hPsid]
        linarith [hb2, hbInv]
    _ ≤ Mconst C₀ α * Xd ^ 2 := hfin

end Work.FTS_MuLipC.RowN0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.landau_1d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.landau_1d` — the one-dimensional Landau inequality on an interval

For `h : ℝ → ℝ` twice differentiable (in the pointwise `HasDerivAt` sense, with the second
derivative of `h` given as `deriv (deriv h)`) on `[x, x + δ]`, with `|h| ≤ M₀` and
`|deriv (deriv h)| ≤ M₂` on that interval,

  `|deriv h x| ≤ 2 * M₀ / δ + M₂ * δ / 2`     (`0 < δ`).

The argument is the second-order Taylor expansion at the *left* endpoint:

  `h (x + δ) - h x - deriv h x * δ = R`,   `|R| ≤ M₂ * δ ^ 2 / 2`,

which is obtained from the monotonicity of the two auxiliary functions

  `G s = h (x+δ) - h s - deriv h s * (x+δ-s) - (M₂/2) * (x+δ-s)^2`,
  `H s = h (x+δ) - h s - deriv h s * (x+δ-s) + (M₂/2) * (x+δ-s)^2`,

whose derivatives `(x+δ-s) * (M₂ - deriv (deriv h) s)` and `-(x+δ-s) * (M₂ + deriv (deriv h) s)`
have constant sign (on `[x, x+δ]`, `x+δ-s ≥ 0`).  Since `G (x+δ) = H (x+δ) = 0`, this gives
`-(M₂/2) δ² ≤ R ≤ (M₂/2) δ²`.  Finally `deriv h x * δ = (h (x+δ) - h x) - R`, so the triangle
inequality together with `|h| ≤ M₀` gives `|deriv h x| * δ ≤ 2 M₀ + M₂ δ²/2`, and dividing by
`δ > 0` yields the claim.

## Main statements

* `Work.FTS_RegExport.RXT.landau_1d` — the target inequality;
* the auxiliary Taylor lemmas `landau_taylor2_upper`, `landau_taylor2_lower`,
  `landau_taylor2_remainder` (public, reusable): a second-order Taylor bound with the Lagrange remainder
  for a function whose iterated derivatives are only known to exist pointwise, which is what the
  hypotheses of `landau_1d` provide (Mathlib's `taylor_mean_remainder_*` require `ContDiffOn`,
  hence continuity of the second derivative, which is *not* assumed here).
-/

namespace Work.FTS_RegExport.RXT

/-- `|p - q| ≤ |p| + |q|`, the form of the triangle inequality used below. -/
private theorem landau_abs_sub_le (p q : ℝ) : |p - q| ≤ |p| + |q| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self p, neg_le_abs p, le_abs_self q, neg_le_abs q]

/-- **Second-order Taylor bound, upper sign.**  If `f` is differentiable with derivative `f'`
on `[a, b]`, `f'` is differentiable with derivative `f''` there, `a ≤ b` and `f'' ≤ A` on
`[a, b]`, then the Taylor remainder at the left endpoint is bounded above:
`f b - f a - f' a * (b - a) ≤ A * (b - a)^2 / 2`.

Only pointwise `HasDerivAt` hypotheses are used; no continuity of `f''` is needed. -/
theorem landau_taylor2_upper {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, f'' y ≤ A) :
    f b - f a - f' a * (b - a) ≤ A * (b - a) ^ 2 / 2 := by
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hfc : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hf'c : ContinuousOn f' (Set.Icc a b) := fun t ht => (hf' t ht).continuousAt.continuousWithinAt
  -- the auxiliary function `G` is continuous on `[a,b]`
  have hGcont : ContinuousOn (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
      (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s : ℝ => f b - f s) (Set.Icc a b) :=
      (continuousOn_const (s := Set.Icc a b) (c := f b)).sub hfc
    have h2 : ContinuousOn (fun s : ℝ => f' s * (b - s)) (Set.Icc a b) :=
      hf'c.mul ((continuousOn_const (s := Set.Icc a b) (c := b)).sub continuousOn_id)
    have h3 : ContinuousOn (fun s : ℝ => A / 2 * (b - s) ^ 2) (Set.Icc a b) :=
      (continuousOn_const (s := Set.Icc a b) (c := A / 2)).mul
        (((continuousOn_const (s := Set.Icc a b) (c := b)).sub continuousOn_id).pow 2)
    exact (h1.sub h2).sub h3
  -- its derivative on the interior is `(b - t) * (A - f'' t)`
  have hderiv : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
        ((b - t) * (A - f'' t)) (interior (Set.Icc a b)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hb : HasDerivAt (fun s : ℝ => b - s) (0 - 1) t :=
      (hasDerivAt_const t b).sub (hasDerivAt_id t)
    have h1 : HasDerivAt (fun s : ℝ => f b - f s) (0 - f' t) t :=
      (hasDerivAt_const t (f b)).sub (hf t htI)
    have h2 : HasDerivAt (fun s : ℝ => f' s * (b - s)) (f'' t * (b - t) + f' t * (0 - 1)) t :=
      (hf' t htI).mul hb
    have h3 : HasDerivAt (fun s : ℝ => A / 2 * (b - s) ^ 2)
        (A / 2 * (2 * (b - t) ^ (2 - 1) * (0 - 1))) t :=
      (hb.pow 2).const_mul (A / 2)
    have h4 : HasDerivAt (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2)
        ((0 - f' t) - (f'' t * (b - t) + f' t * (0 - 1))
          - A / 2 * (2 * (b - t) ^ (2 - 1) * (0 - 1))) t :=
      (h1.sub h2).sub h3
    convert h4.hasDerivWithinAt using 1
    norm_num
    ring
  -- and that derivative is nonnegative on `(a,b)`
  have hnonneg : ∀ t ∈ interior (Set.Icc a b), 0 ≤ (b - t) * (A - f'' t) := by
    intro t ht
    rw [interior_Icc] at ht
    have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h1 : 0 ≤ b - t := by linarith [ht.2]
    have h2 : 0 ≤ A - f'' t := by linarith [hA t htI]
    exact mul_nonneg h1 h2
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hGcont hderiv hnonneg
  have h := hmono haI hbI hab
  have hG0 : (fun s : ℝ => f b - f s - f' s * (b - s) - A / 2 * (b - s) ^ 2) b = 0 := by
    simp only [sub_self, mul_zero, zero_pow (show (2:ℕ) ≠ 0 by norm_num)]
  rw [hG0] at h
  linarith [h]

/-- **Second-order Taylor bound, lower sign.**  Same as `landau_taylor2_upper` with `f'' ≥ -A`:
the Taylor remainder at the left endpoint is bounded below by `-A * (b - a)^2 / 2`. -/
theorem landau_taylor2_lower {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, -A ≤ f'' y) :
    -(A * (b - a) ^ 2 / 2) ≤ f b - f a - f' a * (b - a) := by
  have h := landau_taylor2_upper (f := fun y => -f y) (f' := fun y => -f' y)
    (f'' := fun y => -f'' y) (a := a) (b := b) (A := A) hab
    (fun y hy => (hf y hy).neg) (fun y hy => (hf' y hy).neg)
    (fun y hy => by have := hA y hy; linarith)
  linarith [h]

/-- **Second-order Taylor bound with the Lagrange remainder** for a function whose first two
derivatives are only known to exist pointwise on `[a, b]`: if `|f''| ≤ A` there, then
`|f b - f a - f' a * (b - a)| ≤ A * (b - a)^2 / 2`. -/
theorem landau_taylor2_remainder {f f' f'' : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b)
    (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc a b, HasDerivAt f' (f'' y) y)
    (hA : ∀ y ∈ Set.Icc a b, |f'' y| ≤ A) :
    |f b - f a - f' a * (b - a)| ≤ A * (b - a) ^ 2 / 2 := by
  have h1 := landau_taylor2_upper (f := f) (f' := f') (f'' := f'') (A := A) hab hf hf'
    (fun y hy => (abs_le.mp (hA y hy)).2)
  have h2 := landau_taylor2_lower (f := f) (f' := f') (f'' := f'') (A := A) hab hf hf'
    (fun y hy => (abs_le.mp (hA y hy)).1)
  rw [abs_le]
  exact ⟨h2, h1⟩

theorem landau_1d {h : ℝ → ℝ} {x δ M₀ M₂ : ℝ} (hδ : 0 < δ)
    (hd : ∀ y ∈ Set.Icc x (x + δ), HasDerivAt h (deriv h y) y)
    (hd2 : ∀ y ∈ Set.Icc x (x + δ), HasDerivAt (deriv h) (deriv (deriv h) y) y)
    (h0 : ∀ y ∈ Set.Icc x (x + δ), |h y| ≤ M₀)
    (h2 : ∀ y ∈ Set.Icc x (x + δ), |deriv (deriv h) y| ≤ M₂) :
    |deriv h x| ≤ 2 * M₀ / δ + M₂ * δ / 2 := by
  have hxδ : x ≤ x + δ := by linarith
  -- the Lagrange remainder of the second-order Taylor expansion at `x`, evaluated at `x + δ`
  have hrem := landau_taylor2_remainder (f := h) (f' := deriv h) (f'' := deriv (deriv h))
    (a := x) (b := x + δ) (A := M₂) hxδ hd hd2 h2
  have hsub : x + δ - x = δ := by ring
  rw [hsub] at hrem
  have hmemx : x ∈ Set.Icc x (x + δ) := ⟨le_rfl, hxδ⟩
  have hmemδ : x + δ ∈ Set.Icc x (x + δ) := ⟨hxδ, le_rfl⟩
  -- `|h (x+δ) - h x| ≤ 2 M₀`
  have hb : |h (x + δ) - h x| ≤ 2 * M₀ := by
    have h1 : |h (x + δ) - h x| ≤ |h (x + δ)| + |h x| := landau_abs_sub_le _ _
    have h2' : |h (x + δ)| + |h x| ≤ M₀ + M₀ := add_le_add (h0 (x + δ) hmemδ) (h0 x hmemx)
    linarith [h1, h2']
  have key : |deriv h x| * δ ≤ 2 * M₀ + M₂ * δ ^ 2 / 2 := by
    have h1 : |deriv h x| * δ = |deriv h x * δ| := by rw [abs_mul, abs_of_pos hδ]
    rw [h1]
    -- `deriv h x * δ = (h (x+δ) - h x) - R`
    have htri : |deriv h x * δ| ≤ |h (x + δ) - h x| + |h (x + δ) - h x - deriv h x * δ| := by
      have he : deriv h x * δ = (h (x + δ) - h x) - (h (x + δ) - h x - deriv h x * δ) := by ring
      calc |deriv h x * δ|
          = |(h (x + δ) - h x) - (h (x + δ) - h x - deriv h x * δ)| := congrArg abs he
        _ ≤ |h (x + δ) - h x| + |h (x + δ) - h x - deriv h x * δ| := landau_abs_sub_le _ _
    linarith [htri, hb, hrem]
  have hdone : |deriv h x| ≤ (2 * M₀ + M₂ * δ ^ 2 / 2) / δ := (le_div_iff₀ hδ).mpr key
  have harith : (2 * M₀ + M₂ * δ ^ 2 / 2) / δ = 2 * M₀ / δ + M₂ * δ / 2 := by
    field_simp
  rw [harith] at hdone
  exact hdone

end Work.FTS_RegExport.RXT
end
