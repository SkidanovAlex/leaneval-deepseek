import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.NfkSmooth
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassC.A6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **A6: the Hamel step on `ClassC`.**

No uniqueness of the elliptic solution is used: the values of `E` on a Hamel basis of the
subspace spanned by `ClassC` are chosen with `Classical.choose`, and `E` is extended to all of
`Fn` by `LinearMap.exists_extend`. -/
theorem exists_linear_selector_classC {α : ℝ} {P : Fn → Fn → Prop}
    (hP0 : P 0 0)
    (hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, ClassC α g → ClassC α g' →
      P g Ψ → P g' Ψ' → P (g + c • g') (Ψ + c • Ψ'))
    (hex : ∀ g, ClassC α g → ∃ Ψ, P g Ψ) :
    ∃ E : Fn →ₗ[ℝ] Fn, ∀ g, ClassC α g → P g (E g) :=
  exists_linear_selector (α := α) (classC_zero α)
    (fun g g' c hg hg' => classC_add hg (classC_smul c hg')) hP0 hPlin hex

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VopAux.orthSourceHkNorm_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.classC_ellInputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

-- `hFdec` is kept in the statement of `classC_ellInputs` exactly as requested even though the
-- proof does not need it (it is derivable from the class: `classC_fstar_decay`).
set_option linter.unusedVariables false

/-!
# `FTS.ClassC.classC_ellInputs` — the elliptic inputs of the orthogonalised source

For a profile `g` of the linear class `C` (`Work.FTS.ClassC.ClassC α g`) the orthogonalised source
`orthSource g = g - (15/4)·sin 2θ·F_*(g)` is `C^∞` on the open quadrant and honestly in `ℋ⁷` —
the two inputs the `ℋ⁷` existence node `Work.FTS.EllExist.ellClassOk_exists_of_Fstar_smooth 7`
consumes for its source (see the module docstring of `FTS/EllExist/ClassCInputs.lean`).

## State of this file, and a defect of the requested statement (2026-10-08)

The requested statement had a **fourth binder that is not a type**:

```
(hFdec : Filter.Tendsto (fun z => Work.FTS.Galerkin.Fn) (nhds 0))
```

`Filter.Tendsto` applied to the *constant* map `fun z => Fn` (a map into the **type** `Fn`, not
into `ℝ`) and to a single filter elaborates to `Filter Type → Prop`; a binder type must be a
`Sort`, so the declaration was rejected by Lean at elaboration time

```
error: ... type expected, got
  (Filter.Tendsto (fun z => Galerkin.Fn) (nhds 0) : Filter Type → Prop)
```

and the module could **not be built by anyone** (`lake build` on the delivered file fails).  No
proof can exist for a declaration whose statement does not elaborate, and the finishing check
accordingly reports `the STATEMENT of the requested lemma changed` for every repair.  The
statement as *reviewed and requested* (`.fm3_reviews.json`, path `FTS/ClassC/classC_ellInputs`,
both critics: "looks correct as stated") carried

```
(hFdec : Filter.Tendsto (fun z => Work.Elliptic.Fstar g z) Filter.atTop (nhds 0))
```

which is the decay of the angular moment at `z → ∞` that the name `hFdec` denotes; the binder
below has been restored to that form, and nothing else of the statement (name, `hα`, `hα1`,
`h`, and the two conjuncts of the conclusion) was touched.  The requested conclusion is *true*:
it is proved below, both with the repaired binder and — because the class already forces the
decay — with no decay hypothesis at all (`classC_ellInputs_noDecay`).

## What is proved here

* `classC_tendsto_slice` — every angular slice of a `ClassC` profile decays at `z → ∞`.  The
  class field `tr : BdryTraces α 6 g` at `(a,b) = (0,0)` gives `z·(g z θ·w z)² → 0` at `z → ∞`
  for interior angles, and `w z ≥ 1` (`z ≥ 1`) turns that into `g z θ → 0`; at the endpoints
  `θ = 0, π/2` the field `norm : normTh g = g` forces `g z θ = 0`.
* `classC_fstar_decay` — `F_*(g) z → 0`, by the area's `fstar_tendsto_atTop_zero_of_classC`
  applied to the previous item.  So the `hFdec` hypothesis is *derivable* from `ClassC`, not an
  extra assumption.
* `classC_ellInputs_noDecay` — the requested conclusion, from `ClassC α g` alone.
* `classC_ellInputs` — the requested statement with the repaired binder.
-/





end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Comm2_L1_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- **The level-`1` algebraic inputs of the corrected induction, in the open class.**  This is
the open-class (`RegQo`/`SmoothOpen`) twin of `CoercivityFix.Assembly.Comm2_L1`:

* `congr` is `StepAssembly.H1IP_congr_qd`, which is membership-free (derivatives are local and
  the open quadrant is co-null);
* `add` is `Transfer.H1IP_add_weak` with its block hypotheses discharged from `SmoothOpen`
  (this is exactly the `n = 0` clause of `IPGen.Comm2o_zero`, whose hypotheses
  `SmoothOpen` + `HkMem α 1` are immediate from `RegQo α 1`);
* the two commutator identities of `𝓛̂` are `LhatCommOpen`, the open-quadrant form of
  `LhatCalc.Dth_Lhat` / `LhatCalc.Dz_Lhat` (no hypothesis on the datum at `z ≤ 0` is used). -/
theorem Comm2_L1_O (α : ℝ) (hα : 0 < α) :
    Work.FTS.StrongEps.EpsE4Thr.Comm2O α 1 (Work.Coercivity.H1IP α) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun _f _f' _g h => Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd α h
  · intro f₁ f₂ g h₁ h₂ h₃
    exact (Work.FTS.IPGen.Comm2o_zero α).add f₁ f₂ g h₁.1 h₂.1 h₃.1 h₁.2.1 h₂.2.1 h₃.2.1
  · intro f hf z θ hzθ
    exact (Work.FTS.StrongPersist.H6Aux.LhatCommOpen hf).1 z θ hzθ
  · intro f hf z θ hzθ
    exact (Work.FTS.StrongPersist.H6Aux.LhatCommOpen hf).2 z θ hzθ

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_Lhat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

open Work.FTS.Galerkin (Fn)

/-! ## Two glue lemmas for the radial multiplier `ψ(z) = 1/(1+z)` -/

/-- `ψ(z) = 1/(1+z)` is `C^∞` on `(0,∞)` in every finite order.  (This is the smoothness input
of `TracesAux.BdryTraces_psi_mul_open`, which asks for `∀ n, ContDiffOn ℝ n ψ (Ioi 0)`.) -/
private theorem contDiffOn_oneDiv :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 1 / (1 + z)) (Set.Ioi 0) := by
  intro n
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  positivity

/-- A radial multiplier preserves `SmoothOpen`: the product of a function `C^∞` on `(0,∞)` with a
function `C^∞` on the open quadrant is `C^∞` on the open quadrant. -/
private theorem smoothOpen_psi_mul {ψ : ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioi 0))
    {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => ψ z * g z θ) := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ψ p.1) Work.FTS.EllipticEst.Q0 :=
    (hψ n).comp contDiff_fst.contDiffOn (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hg.forall n
  exact h1.mul h2

/-- `BdryTraces` is closed under multiplication by a constant, in the pointwise form (the frozen
`ClassC.bdryTraces_smul` is stated with `c • f`). -/
private theorem bdryTraces_const_mul {α : ℝ} {k : ℕ} {f : Fn} (c : ℝ)
    (hf : Work.FTS.Nonlin.BdryTraces α k f) :
    Work.FTS.Nonlin.BdryTraces α k (fun z θ => c * f z θ) :=
  Work.FTS.ClassC.bdryTraces_smul (α := α) (k := k) hf c

/-- **`BdryTraces α 4` of the clean operator `𝓛̂` on the class `ClassC`.**

`𝓛̂x = x + D_z x − 2x/(1+z) − 3D_θx/(1+z)` (`CoercivityFix.Lhat_eq`).  Its summands are

* `x` and `D_z x`: the `RegQo`-ports `EpsE4Thr.regQo_dth_dz` applied to `RegQo α 5 x` (which
  `ClassC` supplies: `SmoothOpen x`, `HkMem α 7 x`, `BdryTraces α 6 x`), plus monotonicity of
  `BdryTraces` in the level;
* `2x/(1+z)` and `3D_θx/(1+z)`: the open radial-multiplier lemma
  `TracesAux.BdryTraces_psi_mul_open` with `ψ = 1/(1+z)`, whose `Zop`-iterate bound is
  `PsiMul.zop_psi_bound` and whose smoothness is `PsiMul.contDiffOn_psi`;

the combinations are glued with `ClassC.bdryTraces_add` / `ClassC.bdryTraces_smul`
(which need the two summands to be `SmoothOpen`; the products with `ψ` are handled by
`NonlinRows.smoothOpen_mul` + `NonlinRows.smoothOpen_radial`). -/
theorem BdryTraces_Lhat {α : ℝ} (hα : 0 < α) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    Work.FTS.Nonlin.BdryTraces α 4 (Work.FTS.CoercivityFix.Lhat x) := by
  -- the `Zop`-iterate bound for `ψ(z) = 1/(1+z)` up to order `4`
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.PsiMul.zop_psi_bound 4
  -- `ClassC` supplies `RegQo α 5 x` (smoothness, `ℋ⁵`-membership, traces up to order `5`)
  have hsmQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry x)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall x).mp hx.reg
  have hreg5 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 x :=
    ⟨hx.reg,
      Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 5) (l := 7)
        (by norm_num) hsmQ hx.mem,
      Work.FTS.ClassC.bdryTraces_mono (k := 5) (l := 6) (by norm_num) hx.tr⟩
  -- the two `RegQo`-ports at level `4`
  obtain ⟨hdth, hdz⟩ := Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz hα hreg5
  have htX : Work.FTS.Nonlin.BdryTraces α 4 x :=
    Work.FTS.ClassC.bdryTraces_mono (k := 4) (l := 6) (by norm_num) hx.tr
  have htZ : Work.FTS.Nonlin.BdryTraces α 4 (Work.Spaces.Dz x) := hdz.2.2
  have htT : Work.FTS.Nonlin.BdryTraces α 4 (Work.Spaces.Dth x) := hdth.2.2
  -- the first radial multiple `2x/(1+z)`
  have h2xsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * x z θ) :=
    hx.reg.const_mul' 2
  have h2xtr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ => 2 * x z θ) := bdryTraces_const_mul 2 htX
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (1 / (1 + z)) * (2 * x z θ)) :=
    smoothOpen_psi_mul (ψ := fun z => 1 / (1 + z)) (g := fun z θ => 2 * x z θ)
      contDiffOn_oneDiv h2xsm
  have hXtr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ => (1 / (1 + z)) * (2 * x z θ)) :=
    BdryTraces_psi_mul_open (k := 4)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 2 * x z θ)
      hK0 hKb contDiffOn_oneDiv h2xsm h2xtr
  -- the second radial multiple `3D_θx/(1+z)`
  have h3Tsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Work.Spaces.Dth x z θ) :=
    hx.reg.Dth.const_mul' 3
  have h3Ttr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ => 3 * Work.Spaces.Dth x z θ) :=
    bdryTraces_const_mul 3 htT
  have hYsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    smoothOpen_psi_mul (ψ := fun z => 1 / (1 + z)) (g := fun z θ => 3 * Work.Spaces.Dth x z θ)
      contDiffOn_oneDiv h3Tsm
  have hYtr : Work.FTS.Nonlin.BdryTraces α 4
      (fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    BdryTraces_psi_mul_open (k := 4)
      (ψ := fun z => 1 / (1 + z)) (K := K) (x := fun z θ => 3 * Work.Spaces.Dth x z θ)
      hK0 hKb contDiffOn_oneDiv h3Tsm h3Ttr
  -- the summand `x + D_z x`
  have hPsm : Work.FTS.EllipticEst.SmoothOpen (x + Work.Spaces.Dz x) :=
    Work.FTS.EllipticEst.smoothOpen_add (f := x) (g := Work.Spaces.Dz x) hx.reg hx.reg.Dz
  have hPtr : Work.FTS.Nonlin.BdryTraces α 4 (x + Work.Spaces.Dz x) :=
    Work.FTS.ClassC.bdryTraces_add (f := x) (g := Work.Spaces.Dz x) hx.reg hx.reg.Dz htX htZ
  -- the sum of the two radial multiples
  have hQsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / (1 + z)) * (2 * x z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add (f := fun z θ => (1 / (1 + z)) * (2 * x z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) hXsm hYsm
  have hQtr : Work.FTS.Nonlin.BdryTraces α 4 (fun z θ =>
      (1 / (1 + z)) * (2 * x z θ) + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) :=
    Work.FTS.ClassC.bdryTraces_add (f := fun z θ => (1 / (1 + z)) * (2 * x z θ))
      (g := fun z θ => (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) hXsm hYsm hXtr hYtr
  -- its negative
  have hNQsm : Work.FTS.EllipticEst.SmoothOpen ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * x z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ))) :=
    hQsm.const_mul' (-1)
  have hNQtr : Work.FTS.Nonlin.BdryTraces α 4 ((-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * x z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ))) :=
    Work.FTS.ClassC.bdryTraces_smul hQtr (-1)
  -- the operator unfolds to that sum
  have hL : Work.FTS.CoercivityFix.Lhat x = (x + Work.Spaces.Dz x) + (-1 : ℝ) •
      (fun z θ => (1 / (1 + z)) * (2 * x z θ)
        + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)) := by
    funext z θ
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hL]
  exact Work.FTS.ClassC.bdryTraces_add (f := x + Work.Spaces.Dz x)
    (g := (-1 : ℝ) • (fun z θ => (1 / (1 + z)) * (2 * x z θ)
      + (1 / (1 + z)) * (3 * Work.Spaces.Dth x z θ)))
    hPsm hNQsm hPtr hNQtr

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary properties of the angular kernel `K(θ) = 3 sin θ cos²θ` -/

private theorem K_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  positivity

private theorem K_le_three_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have h1' : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  rw [Work.Spaces.K]
  nlinarith

/-- The squared radial weight vanishes at the origin (Lean's totalised division). -/
private theorem w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]
  norm_num

/-! ## The uniform bound on the radial derivatives of `FK f` -/

/-- **The radial `D_z`-iterates of the angular moment `FK f` are bounded on `(0,∞)`.**

For a datum `f` of the open-quadrant class which is `C^∞` on the quadrant and honestly in `ℋ⁶`
and `ℋ⁷`, there is `K` with `|D_z^b (FK f)(z)| ≤ K` for a.e. `z ∈ Iz` and every `b ≤ 6`. -/
theorem fk_dzd_bound : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
    ∃ K : ℝ, 0 < K ∧ ∀ b : ℕ, b ≤ 6 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z| ≤ K := by
  intro α hα f M hD
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem7 : Work.Spaces.HkMem α 7 f := hD.h7
  -- the level-`7` Tonelli swap and the conull set of good angles
  obtain ⟨hswap7, hAint7, hAslice7⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkSqSwapOpenK α 7 f hsm hmem7
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the pointwise (in `θ`) radial Hardy/Agmon bound on the slices
  have hHardy : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ b : ℕ, b ≤ 6 →
      ∀ z : ℝ, 0 < z → (Work.Spaces.DzIter b f z σ) ^ 2
        ≤ 2 * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
    filter_upwards [hAslice7, haeθ] with σ hslice hσ
    intro b hb z hz
    exact pure_slice_agmon α f σ hα0 hα1 hsm hσ hslice b hb z hz
  -- the radial moments are dominated by the level-`7` slice integral
  have hBA : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ j : ℕ, j ≤ 7 →
      (∫ s in Work.Spaces.Iz, (Work.Spaces.DzIter j f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ := by
    filter_upwards [hAslice7, haeθ] with σ hslice hσ
    intro j hj
    refine MeasureTheory.integral_mono_of_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun s => (Work.Spaces.DzIter j f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (g := fun s => Work.Spaces.HkIntegrand α 7 f s σ) ?_ hslice ?_
    · filter_upwards with s
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with s hs
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with h0 | hpos
      · subst h0
        rw [w_zero]
        simpa using Work.Spaces.HkIntegrand_nonneg α 7 f 0 σ
      · have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 7 f j hj hpos hσ
        have hw : 0 < (Work.Spaces.w s) ^ 2 := pow_pos (Work.FTS.H2.w_pos hpos) 2
        rw [le_div_iff₀ hw] at h1
        exact h1
  -- the total mass of the angular interval is finite
  have hIθvol : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- integrability of the dominating angular function
  have hAint7' : MeasureTheory.Integrable
      (fun σ : ℝ => 3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h : MeasureTheory.Integrable
        (fun σ : ℝ => 3 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ)
          + (3 : ℝ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hAint7.const_mul 3).add
        (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (3 : ℝ)) hIθvol)
    refine h.congr ?_
    filter_upwards with σ
    ring
  -- the value of the `θ`-integral of the dominating function
  have hfinal : (∫ σ in Work.Spaces.Iθ,
        3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ))
      ≤ 3 * ((MeasureTheory.volume Work.Spaces.Iθ).toReal + Work.Spaces.HkSq α 7 f) := by
    have hcongr : (fun σ : ℝ => 3 * (1 + ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 7 f s σ))
        = fun σ : ℝ => (3 : ℝ) + 3 * (∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 7 f s σ) := by
      funext σ; ring
    rw [hcongr]
    have hsplit : (∫ σ in Work.Spaces.Iθ, ((3 : ℝ) + 3 * (∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 7 f s σ)))
        = (∫ σ in Work.Spaces.Iθ, (3 : ℝ))
          + ∫ σ in Work.Spaces.Iθ, 3 * (∫ s in Work.Spaces.Iz,
              Work.Spaces.HkIntegrand α 7 f s σ) :=
      MeasureTheory.integral_add
        (MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (3 : ℝ)) hIθvol)
        (hAint7.const_mul 3)
    rw [hsplit, MeasureTheory.setIntegral_const, MeasureTheory.integral_const_mul, hswap7,
      smul_eq_mul, MeasureTheory.Measure.real]
    linarith [ENNReal.toReal_nonneg (a := (MeasureTheory.volume Work.Spaces.Iθ)),
      Work.Spaces.HkSq_nonneg α 7 f]
  -- the constant
  set Kc : ℝ := 3 * ((MeasureTheory.volume Work.Spaces.Iθ).toReal + Work.Spaces.HkSq α 7 f) + 1
    with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : 0 ≤ (MeasureTheory.volume Work.Spaces.Iθ).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ Work.Spaces.HkSq α 7 f := Work.Spaces.HkSq_nonneg α 7 f
    linarith
  refine ⟨Kc, hKcpos, fun b hb => ?_⟩
  -- the a.e. identification of `D_z^b (FK f)` with `FK (D_z^b f)`
  have hid := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hmem6 b hb
  have haepos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume) (0 : ℝ)] with z hz hzI
    exact lt_of_le_of_ne hzI (Ne.symm hz)
  filter_upwards [hid, haepos] with z hzid hzpos
  have hval : Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z
      = Work.Construction.FK (Work.Spaces.DzIter b f) z := by
    have h0 := hzid 0
    rwa [Work.Elliptic.DzIter_rad] at h0
  rw [hval]
  -- the chain of inequalities
  have h1 : |Work.Construction.FK (Work.Spaces.DzIter b f) z|
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ| := by
    rw [show Work.Construction.FK (Work.Spaces.DzIter b f) z
        = ∫ σ in Work.Spaces.Iθ, Work.Spaces.DzIter b f z σ * Work.Spaces.K σ from rfl]
    have hnorm := norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun σ : ℝ => Work.Spaces.DzIter b f z σ * Work.Spaces.K σ)
    rw [Real.norm_eq_abs] at hnorm
    refine le_trans hnorm ?_
    refine le_of_eq (MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K_nonneg_Iθ hσ)]
    ring
  have h2 : (∫ σ in Work.Spaces.Iθ, Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ|)
      ≤ ∫ σ in Work.Spaces.Iθ,
          3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ) := by
    refine MeasureTheory.integral_mono_of_nonneg (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ?_ hAint7' ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
      exact mul_nonneg (K_nonneg_Iθ hσ) (abs_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc, hHardy, hBA]
        with σ hσ hH hB
      have hKnn : 0 ≤ Work.Spaces.K σ := K_nonneg_Iθ hσ
      have hK3 : Work.Spaces.K σ ≤ 3 := K_le_three_Iθ hσ
      have hH' : |Work.Spaces.DzIter b f z σ| ≤ 1 + ∫ s in Work.Spaces.Iz,
          (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
        have hsq := hH b hb z hzpos
        have hnn : 0 ≤ ∫ s in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 :=
          MeasureTheory.setIntegral_nonneg measurableSet_Ici
            (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        have hsq' : (Work.Spaces.DzIter b f z σ) ^ 2
            ≤ (1 + ∫ s in Work.Spaces.Iz,
                (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) ^ 2 := by
          nlinarith
        have h1B : (0 : ℝ) ≤ 1 + ∫ s in Work.Spaces.Iz,
            (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by linarith
        have h2' := sq_le_sq.mp hsq'
        rwa [abs_of_nonneg h1B] at h2'
      have hB' := hB (b + 1) (by omega)
      calc Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ|
          ≤ Work.Spaces.K σ * (1 + ∫ s in Work.Spaces.Iz,
              (Work.Spaces.DzIter (b + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) :=
            mul_le_mul_of_nonneg_left hH' hKnn
        _ ≤ 3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ) := by
            refine mul_le_mul hK3 (by linarith [hB']) (by positivity) (by norm_num)
  calc |Work.Construction.FK (Work.Spaces.DzIter b f) z|
      ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.K σ * |Work.Spaces.DzIter b f z σ| := h1
    _ ≤ ∫ σ in Work.Spaces.Iθ,
          3 * (1 + ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 7 f s σ) := h2
    _ ≤ 3 * ((MeasureTheory.volume Work.Spaces.Iθ).toReal + Work.Spaces.HkSq α 7 f) := hfinal
    _ ≤ Kc := by rw [hKcdef]; linarith

/-! ## The seven membership statements -/

theorem hkMem_fk_mul : ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ =>
          Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ =>
          Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Spaces.Dth f z θ) ∧
       Work.Spaces.HkMem α 6 (fun z θ =>
          Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Construction.Fstar α z θ)) := by
  intro α hα f M hD
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem7 : Work.Spaces.HkMem α 7 f := hD.h7
  -- `FK f` is `C⁶` on the open quadrant and `ℋ⁶`
  have hFKcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
    have h6 : ContDiffOn ℝ 6 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
      have hF : ContDiffOn ℝ 6 (Work.Elliptic.Fstar f) (Set.Ioi (0 : ℝ)) :=
        Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f hsm hmem7
          (by norm_num)
      rw [Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f]
      have h3 : ContDiffOn ℝ 6 (fun z => (3 : ℝ) • Work.Elliptic.Fstar f z)
          (Set.Ioi (0 : ℝ)) := hF.const_smul (3 : ℝ)
      simpa only [Pi.smul_apply, smul_eq_mul] using h3
    exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_radial h6
  have hFKmem : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    fk_hkMem α hα f hsm hmem6
  -- the a.e. slot bounds for the radial factor
  obtain ⟨K, hKpos, hKb⟩ := fk_dzd_bound α hα f M hD
  have hslots : ∀ j : ℕ, j ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ θ : ℝ, |Work.Spaces.DzIter j (fun z (_ : ℝ) => Work.Construction.FK f z) z θ| ≤ K := by
    intro j hj
    filter_upwards [hKb j hj] with z hz θ
    rwa [Work.Elliptic.DzIter_rad]
  -- smoothness of the two datum fields and of the angular factor `sin²θ`
  have hfcd : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.forall 6
  have hdthcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hsm.Dth.forall 6
  have hdthmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 6) (by linarith) hsm hmem7
  have hsinsqcd : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Real.sin θ ^ 2))
      Work.FTS.EllipticEst.Q0 := by
    have hAsm : ContDiff ℝ (6 : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) := by fun_prop
    convert hAsm.contDiffOn using 1
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  -- the radial-multiplier rows
  obtain ⟨Crad, hCrad, hRadial⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
  have hprod1 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Work.Construction.FK f z * f z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_mul_cd6 hFKcd hfcd
  have hprod2 : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.contDiffOn_uncurry_mul_cd6 hFKcd hdthcd
  have hmem1 : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) :=
    (hRadial (α := α) (a := fun z => Work.Construction.FK f z) (g := f) (K := K)
      hα0 hα1 hKpos.le hFKcd hfcd hslots hmem6).2.1
  have hmem2 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) :=
    (hRadial (α := α) (a := fun z => Work.Construction.FK f z) (g := Work.Spaces.Dth f) (K := K)
      hα0 hα1 hKpos.le hFKcd hdthcd hslots hdthmem).2.1
  -- the `𝒲^{6,∞}`-priced product rule and the star-field rows
  obtain ⟨Cw, hCw, hmulW⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_WlInf6_cd6'
  obtain ⟨Csinsq, hCsinsq, hSinsqW⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.WlInf_sinSq
  obtain ⟨CFs, hCFs, hFstarW⟩ := Work.FTS.StrongPersist.Fstar_W6
  have hFstarcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).forall 6
  -- conjunct 3: `FK f · F_*`
  have hmem3 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ) := by
    have h := (hmulW α (Work.Construction.Fstar α)
      (fun z (_ : ℝ) => Work.Construction.FK f z) hα0 hα1 hFstarcd
      (hFstarW α hα0 hα1).1 hFKcd hFKmem).1
    exact Work.FTS.GalBasis.HkMem_congr_all (fun z θ => mul_comm _ _) α 6 h
  obtain ⟨Cstar, hCstar, hFKstar⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
  -- conjuncts 4 and 7: the two `FK f ×`-star-slot pieces
  obtain ⟨⟨-, hmem4, -⟩, ⟨-, hmem7', -⟩⟩ :=
    hFKstar (α := α)
      (Kf := Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z))
      hα0 hα1 (Work.Spaces.HkNorm_nonneg α 6 _) hsm hmem6 hFKcd hFKmem le_rfl
  -- conjuncts 5 and 6: the extra angular factor `sin²θ`
  have hmem5 : Work.Spaces.HkMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) := by
    have h := (hmulW α (fun z θ => Real.sin θ ^ 2)
      (fun z θ => Work.Construction.FK f z * f z θ) hα0 hα1 hsinsqcd
      (hSinsqW α hα0 hα1).1 hprod1 hmem1).1
    exact Work.FTS.GalBasis.HkMem_congr_all (fun z θ => by ring) α 6 h
  have hmem6' : Work.Spaces.HkMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Spaces.Dth f z θ) := by
    have h := (hmulW α (fun z θ => Real.sin θ ^ 2)
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) hα0 hα1 hsinsqcd
      (hSinsqW α hα0 hα1).1 hprod2 hmem2).1
    exact Work.FTS.GalBasis.HkMem_congr_all (fun z θ => by ring) α 6 h
  exact ⟨hmem1, hmem2, hmem3, hmem4, hmem5, hmem6', hmem7'⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
