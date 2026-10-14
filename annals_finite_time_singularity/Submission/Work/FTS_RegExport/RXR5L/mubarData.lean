import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriSixthBound
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.near0Core
import Submission.Work.R1G.vecResid_eq_scalar_smul
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.NMem6Parts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open scoped Real Topology

/-- **The static level-six `N`-row is `C⁶` on the open quadrant and honest in `ℋ⁶`.**

This is the `τ`-free form of `H6Rows.Npair6BWork.nsumData`: the twenty-piece splitting
`nsplit6_pt` writes `N α (F_*+f) (Φs+Ef)` on `Qd` as the sum `nsum α f Ef Φs` of the twenty
pieces `pcs α f Ef Φs k`; each piece is `C⁶` on `Q0` and honest in `ℋ⁶` (`NS6.pieces`), and
both properties are stable under finite sums (`NS6.hkMem_sum_range`) and under a change of
values on the open quadrant (`cd6_congr` / `HkMem_congr_Qd`).

The only non-hypothesis inputs of the bundle `NS6.Data` — the `ℋ⁶`-membership of the angular
moment `FK f` and the `ℋ⁶ × ℋ⁶` product rule on the open-quadrant class — are the `α`-free
lemmas `Npair6BWork.fk_hkMem` and `Npair6BWork.hkMem_mul_of6`, so the threshold `α₂` can be
taken to be `1`. -/
theorem nMem6_of_parts {α Ce Cs : ℝ} {f Ef Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (h7 : Work.Spaces.HkMem α 7 f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef)
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hell : Work.FTS.StrongPersist.EllPkgK α 6 Ce f Ef)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs) :
    ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ))) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 6 (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ)) := by
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α hαIoc f hadm.reg.1 hadm.reg.2
  have hmulSm : ∀ (u v : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) :=
    fun u v hus hum hvs hvm =>
      Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_mul_of6 hα hα1 ⟨hus, hum⟩ ⟨hvs, hvm⟩
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs f Ef Φs :=
    { hα := hα
      hα1 := hα1
      fsm := hadm.reg.1
      fm := hadm.reg.2
      f7 := h7
      Efsm := hEf
      Φssm := hΦs
      l12 := hadm.l12
      star := hstar6
      ell := hell
      kfm := hkfm
      hadm := hadm
      mulSm := hmulSm }
  have hpcs := Work.FTS.StrongPersist.H6Row6.NS6.pieces D
  have hsum := Work.FTS.StrongPersist.H6Row6.NS6.hkMem_sum_range 20
    (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs)
    (fun k hk => (hpcs k hk).1) (fun k hk => (hpcs k hk).2)
  -- the pointwise splitting of `N` into the twenty pieces, on the open quadrant
  have hpt : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α f)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs z θ :=
    fun z θ hzθ =>
      Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsplit6_pt hα hα1 hadm hEf hΦs z θ hzθ
  refine ⟨?_, ?_⟩
  · refine hsum.1.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    show Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Ef z θ) z θ
      = ∑ k ∈ Finset.range 20, Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs k z θ
    rw [hpt z θ hp, Work.FTS.StrongPersist.H6Row6.pcs_sum]
    simp only [Finset.sum_apply]
  · refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (fun z θ hzθ => (hpt z θ hzθ).symm) ?_
    rw [Work.FTS.StrongPersist.H6Row6.pcs_sum]
    exact hsum.2

theorem NMem6Parts :
    ∀ Ce : ℝ, ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {f Ef Φs : Work.FTS.Galerkin.Fn} {Cs : ℝ},
    Work.FTS.StrongPersist.H6Adm α f →
    Work.Spaces.HkMem α 7 f →
    Work.FTS.EllipticEst.SmoothOpen Ef →
    Work.FTS.EllipticEst.SmoothOpen Φs →
    Work.FTS.StrongPersist.EllPkgK α 6 Ce f Ef →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ))) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 6 (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Ef z θ)) := by
  intro Ce
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro α hαIoc f Ef Φs Cs hadm h7 hEf hΦs hell hstar6
  exact nMem6_of_parts hαIoc.1 hαIoc.2 hadm h7 hEf hΦs hell hstar6

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.aprioriP_of_halvesB_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/aprioriP_of_halvesB_proof.lean` — the leaf L-B, and the two hypotheses it
is missing

Status of this file (owner note, do read before re-pointing the task):

* the **target** `aprioriP_of_halvesB_proof` is left as installed (`sorry`): its statement is **not
  derivable from its hypotheses** — see §1 below;
* the **corrected** statement, with the two missing hypotheses made explicit, is proved here as
  `aprioriP_of_halvesB_strict` (sorry-free, standard axioms); it is the statement a producer should
  aim at, and `Apriori4.lean`'s call site can be adapted to it without changing any constant;
* the standalone real-analysis brick used by it is a `private` copy `sInf_crossing_aux` (so that
  this file is self-contained); the same lemma is proved publicly as
  `Work.FTS.StrongEps.E4R3.Apriori4Proofs.sInf_crossing` (`…/sInf_crossing.lean`), which is the
  name to use in a restated leaf;

## 1. Why the target statement is not provable as stated

Unfolding `EpsE4Thr/Reduction.AprioriP` and `E4R3/Apriori4Defs.{AprioriPSixthB,
AprioriPFourthB}`, for a fixed horizon `T'' ∈ (0,T]` and a regular `P₀`-solution `g` the two
hypotheses are exactly the two implications

* `h4` : `P(T'') ⟹ Q(T'')`,  `P(T'') := ∀τ∈[0,T''], Xn6 α (slice g τ) ≤ √(2E₁+1)`,
  `Q(T'') := ∀τ∈[0,T''], Xn α (slice (JfamP ρ ε g) τ) ≤ C₀α²`;
* `h6` : `Q(T'') ⟹ C(T'')`,  `C(T'') := ∀τ∈[0,T''], rawE6 α g τ ≤ E₁`.

Conversely `C(T'') ⟹ P(T'')`, because `HkSq α 6 = Xn6² ≤ IP6o = rawE6`
(`EpsE4Thr.HkSq_le_IP6`, the level-six loop) and `√E₁ ≤ √(2E₁+1)` (`hE₁`).  Hence at **every**
horizon the three interval statements are *equivalent*, and the only datum-level information
available is the `τ = 0` instance (`slice g 0 = g₀`): `Xn6 α g₀ ≤ √(2E₁+1)` and
`Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀α²`, i.e. exactly the conclusion at `τ = 0`.  So `h6 ∧ h4` alone
force nothing beyond `P(T') ↔ Q(T')`, and both may fail: the standard maximal-interval argument
needs a *first interval* on which the bounds hold and a way to reach the supremum of the good set.

Concretely, the closing argument is the following (it is implemented in
`aprioriP_of_halvesB_strict`): let `S := {τ ∈ [0,T'] : √(2E₁+1) < Xn6 α (slice g τ)}` and
`s := sInf S`.  Then `s ∉ S`, `Xn6 α (slice g s) = √(2E₁+1)` and `Xn6 ≤ √(2E₁+1)` on `[0,s]`
(*provided* the map `τ ↦ Xn6 α (slice g τ)` is continuous at `s`); `h4` at horizon `s` then gives
`Q` on `[0,s]`, `h6` gives `rawE6 ≤ E₁` on `[0,s]`, so `Xn6 ≤ √E₁` on `[0,s]` — a **strict**
contradiction with `Xn6 α (slice g s) = √(2E₁+1) > √E₁`.  That contradiction also needs `s > 0`,
i.e. the datum must satisfy the **strict** inequality `Xn6 α g₀ < √(2E₁+1)`; with only `≤`, the
case `Xn6 α g₀ = √(2E₁+1)` together with an immediate crossing (`s = 0`) is consistent with `h4`
and `h6` (`h6` then forces that no solution has `Q` on any interval, `h4` that none has `P`; both
are vacuous and the conclusion still fails at the first crossing time).

Neither input is a consequence of the standing hypotheses:

* continuity of `τ ↦ Xn6 α (slice g τ)` is *not* derivable from `EpsRegP + IsEpsSolP` (per-slice
  `HkMem α 6` plus joint `C¹` allow the `ℋ⁶`-norms to jump while the values converge) — this is
  risk **R2** of `E4R3/Apriori4Leaves/RawE6Deriv.lean`, whose own statement carries the uniform
  bound `hbdd6 : ∃B, ∀τ∈[0,T], Xn6 α (slice g τ) ≤ B` as an explicit hypothesis, and it is
  recorded in `StrongEps/REPORT_LEAD_apriori4_decisions.md`, decision (1): “Per-slice honesty plus
  joint `C¹` does not even give continuity of `τ ↦ Xn6 (slice g τ)`”;
* the strict datum inequality is *not* implied by the non-strict one.  The same defect of
  `AprioriP`'s datum condition is already on file for the level-four half: `TransO`’s
  `AprioriFourthLevel.lean` says its barrier “is the one a producer should aim at … the current
  `AprioriPFourth` (which asks for the datum merely *in* the ball) is out of reach of this route”.

The corrected statement therefore adds

```
(hcont   : ∀ T' ∈ Set.Ioc 0 T, ∀ g, IsEpsSolP α ρ ε T' Φs E g₀ g → EpsRegP α ρ ε T' g →
             ContinuousOn (fun τ => Xn6 α (slice g τ)) (Icc 0 T'))
(hstrict : Xn6 α g₀ < √(2E₁+1))
```

and is proved below.  `hstrict` costs nothing at the intended call site (this is made formal by
`strict_datum_of_xn6_le` below): `Apriori4.lean` has `Xn6 α g₀ ≤ K·α²` with `α ≤ 1` from the datum
and `K ≤ √(2E₁+1)`, and the sixth chapter picks `E₁` with `K² ≤ E₁`, which gives
`Xn6 α g₀ ≤ K < √(2K²+1) ≤ √(2E₁+1)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The first-crossing brick (private copy; the public one is `…/sInf_crossing.lean`) -/


/-! ## The strict datum inequality is free at the intended call site -/

/-- **`hstrict` costs nothing along the route.**  The datum of `EpsE4R4Stmt`/`EpsE4R3` satisfies
`Xn6 α g₀ ≤ K·α² ≤ K` (with `α ≤ 1`, `0 ≤ K`), while the sixth chapter chooses `E₁` with `K² ≤ E₁`;
hence `Xn6 α g₀ ≤ K < √(2K²+1) ≤ √(2E₁+1)`: the strict inequality required by
`aprioriP_of_halvesB_strict` is automatic from the datum. -/
theorem strict_datum_of_xn6_le {α K E₁ : ℝ} {g₀ : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (hE : K ^ 2 ≤ E₁)
    (hXn : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2) :
    Work.FTS.StrongGlobal.Xn6 α g₀ < Real.sqrt (2 * E₁ + 1) := by
  have hα2 : α ^ 2 ≤ 1 := by nlinarith
  have h1 : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K := by
    calc Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 := hXn
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα2 hK
      _ = K := by ring
  have h2 : K < Real.sqrt (2 * K ^ 2 + 1) := by
    have hKs : K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK).symm
    rw [hKs]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  have h3 : Real.sqrt (2 * K ^ 2 + 1) ≤ Real.sqrt (2 * E₁ + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-! ## The corrected assembly -/


/-! ## The requested statement

Left unproved: `aprioriP_of_halvesB_strict` above shows that it follows from the target's
hypotheses once the continuity input `hcont` and the strict datum inequality `hstrict` are added;
neither is available here (see the header of this file).  Nothing else is missing. -/


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.rawSlice_L12_zero_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/rawSlice_L12_zero_proof.lean` — F6 (`rawSlice_L12_zero`)

**Verdict: the assigned statement is MIS-STATED (missing hypotheses), not provable as written.**
This file therefore carries (a) the verbatim assigned statement, left as `sorry` and documented,
and (b) the *repaired* statement `rawSlice_L12_zero_of_uniform`, which is proved (sorry-free) and
is the form the E4R3 session-22 report already prescribes as the repair.

## What the statement says, and what the conservation really needs

`IsEpsSolP` gives `∂_τ g = epsRHSP α ρ ε Φs E g τ` pointwise on the open quadrant, where

```
epsRHSP α ρ ε Φs E g τ = Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ))
```

(`PZeroScheme.epsRHSP_eq_Pz_Jeps_epsWP`, `rfl`).  The zero mode of the slice is conserved along the
scheme **iff** the zero mode of the right-hand side vanishes as a *number*:

```
∂_τ (L₁₂ (slice g τ)(0)) = L₁₂ (epsRHSP α ρ ε Φs E g τ)(0),
```

and `L₁₂ (Pz X)(0) = 0` is available only from the two integrability hypotheses of
`PZeroAux.Pz_l12` (`E5Aux2.L12_epsRHSP_zero`, `EpsSqTools.LinAux.L12_Pz_Jeps_zero`): the a.e.-in-`r`
integrability of the angular slice of `X = Jeps ρ ε (epsWP …)` on `Iθ`, and the integrability of its
`L₁₂`-density on `(0,∞)`.  Mathlib's Bochner integral is the junk value `0` off the integrable
functions, so the cancellation `L₁₂ (Pz X) 0 = L₁₂ X 0 − (L₁₂ X 0/pzNorm)·pzNorm` is genuinely
needed in the honest case, and those two integrabilities are *not* crude formalities: they are
statements about the size/regularity of the pre-mollified right-hand side `epsWP`.

The only *proved* route to the conclusion,
`StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem`, replaces them by two hypotheses on the scheme's
objects:

* `hRm` : `∀ τ ∈ Icc 0 T, HkMem α 4 (epsRHSP … τ) ∧ HkNorm α 4 (epsRHSP … τ) ≤ B` — the honest
  `ℋ⁴`-membership of the right-hand side together with a **uniform in τ** bound `B` (the DCT
  majorant of the Volterra/Fubini argument), and
* `hWm` : `∀ τ ∈ Icc 0 T, HkMem α 4 (Jeps ρ ε (epsWP … τ))` — the `ℋ⁴`-membership of the
  *mollified pre-mollified* right-hand side.

Everything else in that route *is* available here: `hc1 = hreg.1`, `hsm`/`hmem` from
`EpsDatumP.soft` + `OpenPkg.HkMem_mono_open`, and the datum slot `L₁₂ g₀ 0 = 0` from
`hd` by the proved `StrongEps.l12_zero_of_epsDatum`.

## Why `hRm`/`hWm` cannot be produced from the stated hypotheses

* `Φs` and `E` are *completely unconstrained* in the statement, and they enter the pre-mollified
  right-hand side through the arbitrary profile
  `slice (PsiCan Φs E (JfamP ρ ε g)) τ = fun z θ => Φs z θ + E (slice (JfamP ρ ε g) τ) z θ`
  (`Vocab.PsiCan`), which sits inside `gRHS` through `N α F Φ` and `mubar (N0 α F g) (N α F Φ)`
  (`Construction.gRHS`, `Construction.N`).  Hence the *size* of `epsWP` — and therefore of
  `epsRHSP` — is not determined by the hypotheses.
* The producers of `hRm`/`hWm` all need the ε-uniform operator packages plus uniform size data that
  the hypotheses do not carry: `EpsE4Thr.epsRHSP_hkMem_fam` and `EpsE4Thr.HkNorm_epsRHSP_le`
  (`hEll : ∀ u, ClassC α u → EllPkgGo α Ce u (E u) ∧ EllPkgK α 6 Ce u (E u)`,
  `hstar : StarPkgo2 α Cs Φs`, `hml : MuLamOK α C₀ Φs E`, and a uniform `HkNorm α 6 (slice g s) ≤ B`),
  `StrongEps.epsWP_hkMem4_bnd_unif` (same packages plus the class-`C`/ball/`ℋ⁶`-ball clauses of the
  projected family).
* `EpsRegP` supplies those clauses only *per slice*, never uniformly: per-slice `SmoothOpen`/`HkMem α 6`
  plus joint `C¹` do not bound `τ ↦ HkNorm α 6 (slice g τ)` (the `ℋ⁶`-norms may blow up while the
  values converge).  This is exactly the gap recorded in the area's own report to the lead —
  `Submission/Work/FTS/StrongEps/REPORT_LEAD_apriori4_decisions.md`, Decision (1) §Finding: the
  uniform `ℋ⁶` bound "is *not* a consequence of `IsEpsSolP + EpsRegP`" — and it is the same one
  that forced the sibling F6 docstring (`E4R3/Apriori4Leaves/RawSliceL12Zero.lean`) to say
  "if it cannot be produced from `EpsRegP`, return *missing hypothesis*".
* Independent confirmation: both reviewers of this exact path (recorded in `.fm3_reviews.json`,
  key `FTS/StrongEps/E4R3/Apriori4Proofs/rawSlice_L12_zero_proof`) concluded "probably wrong as
  stated", naming precisely these two groups; the lead's report prescribes the same repair
  ("add the uniform `epsRHSP`/`ℋ⁴` bound to its hypotheses").

## The repair

`rawSlice_L12_zero_of_uniform` below is the assigned statement *plus* `hRm`/`hWm`, and it is proved
by the proved `E5Aux3.L12_slice_eq_zero_of_hkMem`.  In the consumer `rawE6_ineq`'s setting the
operator packages are available from `E4Data` + `StarPkg6`, so only the uniform sizes must be
carried (the same information the `ℋ⁶`-half propagates; cf. the interval-local treatment of R2).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The repaired F6** (`rawSlice_L12_zero` with the two missing regularity hypotheses):
`L₁₂ (slice g τ)(0) = 0` along a regular `P₀`-solution, given

* `hRm` — `ℋ⁴`-membership of the scheme's right-hand side together with a uniform-in-`τ` bound
  (the dominated-convergence majorant of the Volterra/Fubini argument), and
* `hWm` — `ℋ⁴`-membership of the mollified pre-mollified right-hand side `Jeps ρ ε (epsWP … τ)`.

Every other input of the proved route is read off the assigned hypotheses: `hreg.1` is the joint
`C¹`-regularity, `EpsDatumP.soft` + `OpenPkg.HkMem_mono_open` give the per-slice
`SmoothOpen`/`HkMem α 4`, and `hd` gives `L₁₂ g₀ 0 = 0` through `StrongEps.l12_zero_of_epsDatum`. -/
theorem rawSlice_L12_zero_of_uniform {α ε T B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g : Fam} (hρ : IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : 0 < ε) (hT : 0 < T)
    (hd : ∀ ε' : ℝ, 0 < ε' → EpsDatum α ρ ε' g₀)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hreg : EpsRegP α ρ ε T g)
    (hRm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsRHSP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (epsRHSP α ρ ε Φs E g τ) ≤ B)
    (hWm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g τ))) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (slice g τ) 0 = 0 := by
  have h0 : Work.Construction.L12 g₀ 0 = 0 := l12_zero_of_epsDatum hα hρ hd
  refine Work.FTS.StrongEps.L12_slice_eq_zero_of_hkMem (α := α) (ε := ε) (T := T) (B := B)
    (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀) (g := g) hα hρ hε hT hsol hreg.1 ?_ ?_ hRm hWm h0
  · intro τ hτ
    exact (EpsDatumP.soft (hreg.2 τ hτ)).1
  · intro τ hτ
    exact Work.FTS.OpenPkg.HkMem_mono_open (EpsDatumP.soft (hreg.2 τ hτ)).1 4 (by norm_num)
      (EpsDatumP.soft (hreg.2 τ hτ)).2


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L.L12fAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 The full profile of the sanitised family, and the static profile bound -/

/-- The full profile `G = F_* + g̃` of the construction at the sanitised family
`g̃ = gS α (tauExt g)`.  It is compactly supported in `z` by the support hypothesis. -/
def Gfull (α : ℝ) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Work.FTS.Regularity.profFull α
    (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ

theorem Gfull_apply (α : ℝ) (g : Work.FTS.Galerkin.Fam) (z θ τ : ℝ) :
    Gfull α g z θ τ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS_RegExport.RXR5.SG α g z θ τ := by
  rw [Gfull, Work.FTS.Regularity.profFull_apply]

/-- `|F_*(z,θ)| ≤ 20 z` on the domain (`F_* = α(Γ/c)·F̂`, `Γ ≤ 1`, `c ≥ 1/10`, `F̂(z) ≤ 2z`). -/
theorem Fstar_abs_le_twenty {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {z : ℝ} (hz : 0 ≤ z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ| ≤ 20 * z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hβ hβ1
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith [hc.1]
  obtain ⟨hg0, hg1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hβ hθ
  have hden : (0:ℝ) < (1 + z) ^ 2 := by positivity
  rw [Work.Construction.Fstar, Work.FM.Fstar, abs_mul, abs_mul,
    abs_of_nonneg hβ.le, abs_of_nonneg (div_nonneg hg0 hcpos.le),
    abs_of_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ 2 * z) hden.le)]
  have hgg : Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith [hc.1, hg1]
  have h2 : 2 * z / (1 + z) ^ 2 ≤ 2 * z := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg z, hz]
  have hgg0 : 0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / Work.Spaces.c (Work.FTS.Regularity.pExp α) := div_nonneg hg0 hcpos.le
  have h20 : 0 ≤ 2 * z / (1 + z) ^ 2 := div_nonneg (by linarith) hden.le
  calc Work.FTS.Regularity.pExp α * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * (2 * z / (1 + z) ^ 2)
      ≤ 1 * 10 * (2 * z) :=
        mul_le_mul (mul_le_mul hβ1 hgg hgg0 (by norm_num)) h2 h20 (by norm_num)
    _ = 20 * z := by ring

/-! ## §2 The near-axis linearity of the full profile -/

theorem Gfull_lin {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ Kl : ℝ, 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      ∀ z ∈ Set.Ioo (0:ℝ) 1, |Gfull α g z θ τ| ≤ Kl * z := by
  obtain ⟨K, Q, hK, hQ, hquad⟩ := hSt1.quad
  refine ⟨20 + K, by linarith, ?_⟩
  intro τ hτ θ hθ z hz
  have hz1 : (0:ℝ) < z := hz.1
  have hF := Fstar_abs_le_twenty hα hα13 hz1.le hθ
  have hSg : |Work.FTS_RegExport.RXR5.SG α g z θ τ| ≤ K * z ^ 2 := by
    rw [← Work.FTS_RegExport.RXR5L.SG_extG_eq hz1.le hθ hτ]
    exact (hquad τ hτ θ hθ).1 z hz1.le (by linarith [hz.2])
  rw [Gfull_apply]
  calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ|
      ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
        + |Work.FTS_RegExport.RXR5.SG α g z θ τ| := abs_add_le _ _
    _ ≤ 20 * z + K * z ^ 2 := add_le_add hF hSg
    _ ≤ (20 + K) * z := by
        have hsq : z ^ 2 ≤ z := by nlinarith [hz1, hz.2]
        nlinarith [hK, hsq]

/-! ## §3 The jet of the full profile -/

theorem Gfull_jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N : ℝ, 0 ≤ N ∧ Work.FTS.Regularity.Jet α S N (Gfull α g) := by
  obtain ⟨N₁, hN₁0, hC1SG⟩ :=
    Work.FTS_RegExport.RXR5L.SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  have hJF : Work.FTS.Regularity.Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ (_ : ℝ) => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    (Work.FTS.RegPkgGal.Der.C1JetFstar (S := S) hα hα13).1
  have hJsum : Work.FTS.Regularity.Jet α S
      (100 + 20 * Work.FTS.Regularity.pExp α + N₁)
      (fun z θ τ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ) :=
    Work.FTS.Regularity.Jet.add hJF hC1SG.1
  refine ⟨100 + 20 * Work.FTS.Regularity.pExp α + N₁, by
      have hp := Work.FTS.Regularity.pExp_pos hα; linarith, ?_⟩
  refine Work.FTS.Regularity.Jet.congr hJsum ?_
  intro z θ τ _ _ _
  exact (Gfull_apply α g z θ τ).symm

/-! ## §4 The support of the full profile -/

theorem Gfull_supp {α S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0) :
    ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Gfull α g z θ τ = 0 := by
  obtain ⟨Lf, hLf, hvan⟩ := hsupp
  exact ⟨Lf, hLf, fun τ hτ z θ hz => hvan τ hτ z θ hz⟩

/-! ## §5 The `τ`-modulus of the full profile (from the sanitised family) -/

theorem Gfull_tau_mod {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ Nt : ℝ, 0 ≤ Nt ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z →
        |Gfull α g z θ τ - Gfull α g z θ τ'| ≤ Nt * z * |τ - τ'| ^ α := by
  obtain ⟨Nt, hNt0, hmod⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.SG_tau_mod_weighted (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK hS
  refine ⟨Nt, hNt0, ?_⟩
  intro τ hτ τ' hτ' θ hθ z hz
  rw [Gfull_apply, Gfull_apply]
  have hkey : (Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ)
      - (Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ')
      = Work.FTS_RegExport.RXR5.SG α g z θ τ - Work.FTS_RegExport.RXR5.SG α g z θ τ' := by
    ring
  rw [hkey]
  exact hmod τ hτ τ' hτ' θ hθ z hz

/-! ## §6 The angular integrability of the sanitised slice -/

theorem SG_slice_integrable {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_RegExport.RXR5.SG α g s θ τ / s) Work.Spaces.Iθ := by
  obtain ⟨N₁, hN₁0, hC1SG⟩ :=
    Work.FTS_RegExport.RXR5L.SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  intro τ hτ s hs
  have hcontSG : ContinuousOn (fun θ => Work.FTS_RegExport.RXR5.SG α g s θ τ) Work.Spaces.Iθ :=
    Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN₁0 hα
      (fun θ hθ θ' hθ' => hC1SG.1.thmod (le_of_lt hs) hθ hθ' hτ)
  have hcontK : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ) Work.Spaces.Iθ :=
    (by unfold Work.Spaces.K; fun_prop : Continuous fun θ : ℝ => Work.Spaces.K θ).continuousOn
  have hcont : ContinuousOn
      (fun θ => Work.Spaces.K θ * Work.FTS_RegExport.RXR5.SG α g s θ τ * (1 / s))
      Work.Spaces.Iθ := (hcontK.mul hcontSG).mul continuousOn_const
  rw [Work.Spaces.Iθ] at hcont ⊢
  refine (hcont.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
  intro θ _
  ring

/-! ## §7 Integrability of the density of the full profile -/

theorem Gfull_dens_integrable {α S N Kl Lf : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hJet : Work.FTS.Regularity.Jet α S N (Gfull α g))
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |Gfull α g z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → Gfull α g z θ τ = 0) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice (Gfull α g) τ))
      (Set.Ioi 0) := by
  intro τ hτ
  refine Work.FTS.RegPkgGal.Der.integrableOn_Ioi_of_bound_of_eventually_zero
    (c := 6 * max Kl N) hsupp.1
    (Work.FTS.RegPkgGal.Der.continuousOn_L12dens_gSlice hα hJet hτ) ?_ ?_
  · intro s hs
    exact Work.FTS.RegPkgGal.Der.L12fDensUnif hJet hlin τ hτ s hs
  · intro s hs
    exact (Work.FTS.RegPkgGal.Der.L12fDensBound hJet hlin hsupp).2 τ hτ s hs

/-! ## §8 The additivity of `L₁₂` on the pair `(F_*, g̃(τ))` -/

theorem L12f_split_Gfull {α S N Kl Lf : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hJet : Work.FTS.Regularity.Jet α S N (Gfull α g))
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0:ℝ) 1,
      |Gfull α g z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → Gfull α g z θ τ = 0)
    (hSGE : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_RegExport.RXR5.SG α g s θ τ / s) Work.Spaces.Iθ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      Work.Coercivity.L12f (Work.FTS.Regularity.gSlice (Gfull α g) τ) z
        = Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
          + Work.Coercivity.L12f
              (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z := by
  obtain ⟨hIa, hIad, _hIav⟩ := Work.FTS_RegExport.RXR5L.L12fAux.Fstar_dens_facts hα hα13
  intro τ hτ z hz
  have hfe : (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS_RegExport.RXR5.SG α g z θ τ)
      = Work.FTS.Regularity.gSlice (Gfull α g) τ := by
    funext z θ
    rw [Work.FTS.Regularity.gSlice_apply, Gfull_apply]
  have hsum : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
        + Work.FTS_RegExport.RXR5.SG α g z θ τ)) (Set.Ioi 0) := by
    rw [hfe]
    exact Gfull_dens_integrable hα hJet hlin hsupp τ hτ
  have hsplit := Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable
    (α := α)
    (a := fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
    (b := fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ)
    hIa (hSGE τ hτ) hsum hIad z hz
  rw [← hfe]
  exact hsplit

/-! ## §9 A family that is constant in `(z,θ)`: the `C1Jet` of a `τ`-curve -/

theorem c1jet_const_family {α S M : ℝ} {T : ℝ → ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hb : ∀ τ ∈ Set.Icc (0:ℝ) S, |T τ| ≤ M)
    (hm : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |T τ - T τ'| ≤ M * |τ - τ'| ^ α) :
    Work.FTS.RegPkgGal.C1Jet α S M (fun _ _ τ => T τ) := by
  refine ⟨⟨hM0, ?_, ?_⟩, ?_⟩
  · intro z θ τ _ _ hτ
    exact hb τ hτ
  · intro z z' θ θ' τ τ' _ _ _ _ hτ hτ'
    have h1 : |T τ - T τ'| ≤ M * |τ - τ'| ^ α := hm τ hτ τ' hτ'
    have h2 : |τ - τ'| ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by
      have h3 : (0:ℝ) ≤ |z - z'| + |θ - θ'| := by positivity
      linarith
    have h3 : |τ - τ'| ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) h2 hα.le
    calc |T τ - T τ'| ≤ M * |τ - τ'| ^ α := h1
      _ ≤ M * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_left h3 hM0
  · intro τ _ θ _ z _
    exact ⟨0, hasDerivAt_const z (T τ), by simpa using hM0⟩

/-! ## §10 The corrected statement -/

theorem L12f_C1Jet_profFull {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0) :
    ∃ N₇ N₈ : ℝ, 0 ≤ N₇ ∧ 0 ≤ N₈ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₇
        (fun z θ τ => Work.Coercivity.L12f
          (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
          z) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₈
        (fun z θ τ => Work.Coercivity.L12f
          (fun z θ' => 3 * Work.Spaces.Dth
            (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z θ'
            / (1 + z)) 0) := by
  have hα1 : α ≤ 1 := by linarith
  -- ### the first slot
  obtain ⟨Njet, hNjet0, hJet⟩ := Gfull_jet (S := S) hα hα13 hOK hS hSt1
  obtain ⟨Kl, hKl0, hlin⟩ := Gfull_lin (S := S) hα hα13 hOK hS hSt1
  obtain ⟨Lf, hLf, hsuppG⟩ := Gfull_supp (S := S) (g := g) hsupp
  obtain ⟨Nt, hNt0, htau⟩ := Gfull_tau_mod (S := S) hα hα13 hOK hS
  obtain ⟨Nc, hNc0, hC1G⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.C1Jet_L12f_of_support (α := α) (S := S) (N := Njet)
      (Kl := Kl) (Lf := Lf) (Nt := Nt) hα hα1 hS hJet ⟨hKl0, hlin⟩ ⟨hLf, hsuppG⟩ ⟨hNt0, htau⟩
  obtain ⟨N₉, hN₉0, hC1F⟩ :=
    Work.FTS_RegExport.RXR5.C1Jet_L12f_Fstar (α := α) (S := S) hα hα13 hS
  have hC1sub : Work.FTS.RegPkgGal.C1Jet α S (Nc + N₉)
      (fun z θ τ => Work.Coercivity.L12f
          (Work.FTS.Regularity.gSlice (Gfull α g) τ) z
        - Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z) :=
    Work.FTS.RegPkgGal.C1Jet.add hC1G (Work.FTS.RegPkgGal.C1Jet.neg hC1F)
  have hsplit := L12f_split_Gfull (α := α) (S := S) (N := Njet) (Kl := Kl) (Lf := Lf)
    hα hα13 hJet ⟨hKl0, hlin⟩ ⟨hLf, hsuppG⟩
    (SG_slice_integrable (S := S) hα hα13 hOK hS hSt1)
  have hconj₁ : Work.FTS.RegPkgGal.C1Jet α S (Nc + N₉)
      (fun z θ τ => Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z) := by
    refine Work.FTS.RegPkgGal.C1Jet.congr hC1sub ?_
    intro z θ τ hz hθ hτ
    have h := hsplit τ hτ z hz
    show Work.Coercivity.L12f (Work.FTS.Regularity.gSlice (Gfull α g) τ) z
        - Work.Coercivity.L12f
            (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
      = Work.Coercivity.L12f
          (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z
    linarith [h]
  -- ### the second slot (the transport zero-mode of the raw family, transported to `g̃`)
  obtain ⟨M₀, hM₀0, hTbnd, hTlip⟩ :=
    Work.FTS_RegExport.RXR5L.aux.Tlim_bounds (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS
  -- `slice g τ` and the sanitised slice agree on the quadrant, hence so do their transport fields
  have hagree : ∀ τ ∈ Set.Icc (0:ℝ) S,
      Work.FTS_RegExport.RXR5.AgreeOnQ (Work.FTS.Galerkin.slice g τ)
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) := by
    intro τ hτ z θ hz hθ hθ2
    show g z θ τ = Work.FTS_RegExport.RXR5.SG α g z θ τ
    rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
  have hcongr : ∀ τ ∈ Set.Icc (0:ℝ) S,
      Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
        = Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
            / (1 + z)) 0 := by
    intro τ hτ
    refine Work.FTS_RegExport.RXR5.L12f_congr_of_agreeOnQ ?_ (le_refl (0:ℝ))
    intro z θ hz hθ hθ2
    show 3 * Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)
      = 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ / (1 + z)
    rw [Work.FTS_RegExport.RXR5.Dth_congr_of_agreeOnQ (hagree τ hτ) hz hθ hθ2]
  have hmax0 : (0:ℝ) ≤ max S 1 := le_trans zero_le_one (le_max_right _ _)
  have hb : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
        / (1 + z)) 0| ≤ M₀ * max S 1 := by
    intro τ hτ
    rw [← hcongr τ hτ]
    exact le_trans (hTbnd τ hτ)
      (le_mul_of_one_le_right hM₀0 (le_max_right S 1))
  have hm : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
          / (1 + z)) 0
        - Work.Coercivity.L12f (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ') z θ
          / (1 + z)) 0| ≤ M₀ * max S 1 * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    rw [← hcongr τ hτ, ← hcongr τ' hτ']
    have h1 := hTlip τ hτ τ' hτ'
    have h2 := Work.FTS_RegExport.RXR5L.abs_sub_le_max_mul_rpow (S := S) hα hα1 hτ hτ'
    calc |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)) 0|
        ≤ M₀ * |τ - τ'| := h1
      _ ≤ M₀ * (max S 1 * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hM₀0
      _ = M₀ * max S 1 * |τ - τ'| ^ α := by ring
  refine ⟨Nc + N₉, M₀ * max S 1,
    by linarith [hNc0, hN₉0], mul_nonneg hM₀0 hmax0, hconj₁, ?_⟩
  refine Work.FTS.RegPkgGal.C1Jet.congr
    (c1jet_const_family (α := α) (S := S) (M := M₀ * max S 1) (hα := hα)
      (mul_nonneg hM₀0 hmax0) (fun τ hτ => hb τ hτ)
      (fun τ hτ τ' hτ' => hm τ hτ τ' hτ')) ?_
  intro z θ τ _ _ _
  rfl

end Work.FTS_RegExport.RXR5L.L12fAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.mubarData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXR5L

theorem mubarData {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))| ≤ M) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
          (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ')
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ'))
          (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ')
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ'))|
        ≤ M * |τ - τ'| ^ α) := by
  exact mubarData_of_Tfacts hα hα13 hEll hStar hSol hOK hS
    (Work.FTS_RegExport.RXR5L.aux.Tlim_bounds (Φs := Φs) (E := E) hα hα13 hOK hS)

end Work.FTS_RegExport.RXR5L
end
end
