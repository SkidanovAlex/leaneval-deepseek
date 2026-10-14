import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.rawE6_ineq_proof
import Submission.Work.FTS.StrongPersist.H6Pair_ones3
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_StreamBdry.Assembly.hid9_of_slot
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.FTS_StreamBdry.SB5.sb5_decay
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Leaves.RawE6IneqFlow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawE6IneqFlow.lean` — leaf **L-A over the flow class** `EpsFlowP`

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §5 step 3 + the lead's
message): the leaf L-A `rawE6_ineq`/`rawE6_ineq_ones3` (`E4R3/Apriori4Leaves/RawE6Ineq.lean`)
carries `IsEpsSolP + EpsRegP + ball`, which is *per-slice* data and does not determine the
uniform-in-`τ` `ℋ⁶`-bound `hb6` that the route needs (six children returned the leaf FALSE for
exactly this reason).  The flow class `EpsFlowP` supplies it: by
`E4R5.xn6_continuousOn_of_flow` the map `τ ↦ Xn6 α (slice g τ)` is continuous on the *compact*
`Icc 0 T`, hence bounded — which is `hb6` with a constant `B` depending on the solution.

So the present lemma is the repaired leaf, **proved** by combining

* the proved sibling `Apriori4Proofs.rawE6_ineq_uniform` (the route, with `hb6` as an explicit
  input and the S1/S5 leaves discharged), whose only remaining hypothesis is the semi-tame leaf
  S2 `epsWP_semitame` (carried here as `hS2`), and
* the proved `E4R5.xn6_continuousOn_of_flow` (`hflow : EpsFlowP`),

with the kernel symmetry `hρs` and the proved pairing estimate `StrongPersist.H6Pair_ones3`
(instantiated at `Ce`).  This is the exact shape the `ℋ⁶`-half `E4R5.SixthChapterBF` consumes.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Leaf L-A over `EpsFlowP`** — the raw level-six energy inequality with the `ε`-small
superlinear defect, for `EpsFlowP` flows.  The uniform-in-`τ` `ℋ⁶`-bound `hb6` of
`rawE6_ineq_uniform` is produced here from the flow's `ℋ⁶`-continuity. -/
theorem rawE6_ineq_flow
    (hS2 : ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, Work.FTS.StrongEps.IsSmoothKernel ρ →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ),
        Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
        Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
        Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) ∧
        Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ∧
        Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
            + Ct * (1 + Work.Spaces.HkNorm α 6 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ^ 2)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) {Ce : ℝ} (hCe : 0 < Ce) :
    ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Λ C₁ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧
    ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    Work.FTS.StrongEps.EpsE4Thr.E4Data α C₀ K Ce Cs ρ Φs E g₀ →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g → Work.FTS.StrongEps.EpsRegP α ρ ε T g →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.EpsFlowP α ρ ε T Φs E g →
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Set.Ioo 0 T,
        2 * IP6o α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (slice g τ)
          ≤ Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 := by
  obtain ⟨α₂, Cp, _hCp, _hα₂, hpair⟩ := Work.FTS.StrongPersist.H6Pair_ones3 Ce hCe
  intro C₀ Cs
  obtain ⟨α₀, hα₀, h⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.rawE6_ineq_uniform (ρ := ρ) hS2 hρ hρs hpair C₀ Cs
  refine ⟨α₀, hα₀, fun α hα => ?_⟩
  obtain ⟨Λ, C₁, hΛ, hC₁, H⟩ := h α hα
  refine ⟨Λ, C₁, hΛ, hC₁, ?_⟩
  intro K Φs E g₀ hdat hstar ε hε T hT g hsol hreg hflow hball τ hτ
  -- the uniform-in-`τ` `ℋ⁶`-bound of the flow, from its continuity on the compact `[0,T]`
  have hcont : ContinuousOn (fun σ => Xn6 α (slice g σ)) (Set.Icc 0 T) :=
    Work.FTS.StrongEps.EpsE4Thr.E4R5.xn6_continuousOn_of_flow hreg hflow
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  exact H hdat hstar ε hε T hT g hsol hreg hball (fun σ hσ => hB ⟨σ, hσ, rfl⟩) τ hτ

end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.sixthChapterB_leaf_of_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/sixthChapterB_leaf_of_uniform.lean` — H6 with the uniform `ℋ⁶` bound as a
hypothesis

**Verdict: the assigned statement is MIS-STATED (the missing hypothesis it carries is not the one
that the leaf actually lacks); it is not provable from its hypotheses.**  This file therefore
carries (a) the verbatim assigned statement, left as `sorry` and documented below, and (b) the
*sharpest repair* `sixthChapterB_of_uniformBound` (proved, `sorry`-free) together with the
Cauchy–Schwarz constant `exists_IP6o_cs_uniform` it uses.  The full analysis is in
`NOTES_sixthChapterB_leaf_of_uniform.md`.

## What the statement asks

`SixthChapterB Ce Cs C₀ ρ` demands, for every admissible datum `E4Data α' C₀ K Ce Cs ρ Φs E g₀`
(`α' ∈ (0,1]`, `K` the datum's `ℋ⁶`-size, `Ce/Cs` the two operator packages, plus `StarPkg6`) and
every horizon `T > 0`, a **single** constant `E₁ ≥ K²` and a threshold `ε₆ ∈ (0,1]` such that for
**every** `ε ∈ (0,ε₆]` and **every** regular `ε`-solution `g` whose projected mollified slices stay
in the `C₀α'²`-ball,

```
∀ τ ∈ Icc 0 T, rawE6 α' g τ ≤ E₁,      rawE6 α g τ = IP6o α (slice g τ) (slice g τ).
```

So `E₁` must be uniform in `ε` **and uniform over the whole solution family**.

The added hypothesis `hb` is the uniform-in-`τ` *value* bound of the raw slices,
`∃ B, ∀ τ ∈ Icc 0 T, Xn6 α (slice g τ) ≤ B` — literally the `hbdd6` of the S4 leaf
(`E4R3/Apriori4Leaves/RawE6Deriv.lean`, risk R2) and the `hb6` that repairs L-A
(`Apriori4Proofs/rawE6_ineq_proof.lean`, `rawE6_ineq_uniform_of_leaves`).  It is therefore the
hypothesis the *leaf-level* design prescribed.

## Why it does not suffice

**(1) `hb` is a per-`(ε, solution)` bound.**  Its witness `B` may depend on `ε`, on the horizon, on
the datum and on the solution `g` itself.  The conclusion needs one `E₁` for all `ε ∈ (0,ε₆]` and
all solutions.  The only available conversion of a *value* bound into a *pairing* bound is
Cauchy–Schwarz for `IP6o` (`exists_IP6o_cs_uniform` below, from the proved
`StrongPersist.IP6_cs_coeffs`),

```
rawE6 α g τ ≤ CC · Xn6 α (slice g τ)² ≤ CC · B²,
```

which keeps the dependence on `B = B(ε,g)`.  So the statement is *equivalent to* the assertion
that the family `{Xn6 α (slice g τ)}` is bounded uniformly in `ε` and in the solution — which is
exactly the chapter's mathematical content, not a consequence of the hypothesis as written.

**(2) The design's route to that content is broken at S4.**  The ε-uniformity of the intended
estimate comes from L-A — `rawE6_ineq_uniform_of_leaves` (proved), which uses `hb6` (which we have)
and produces **ε-uniform** `Λ, C₁` with

```
2 · IP6o α (epsRHSP … τ) (slice g τ) ≤ Λ (1 + rawE6 α g τ) + ε C₁ (1 + rawE6 α g τ)²
```

— followed by L-C (`gronwall_absorb`, proved).  Between them sits the level-six **energy identity
S4**,

```
ContinuousOn (rawE6 α g) (Icc 0 T) ∧
  ∀ τ ∈ Ioo 0 T, HasDerivAt (rawE6 α g) (2 · IP6o α (epsRHSP … τ) (slice g τ)) τ,
```

which is precisely what licenses the Grönwall comparison.  S4 is **not a consequence of
`IsEpsSolP + EpsRegP + hb`**, and the tree's own verdict (`rawE6_deriv` returned FALSE; see
`Apriori4Proofs/rawE6_deriv_proof.lean`, `rawE6_deriv_local_proof.lean`) records why:

* `EpsRegP` supplies *joint `C¹`* of `g` on the open quadrant and per-slice `SmoothOpen`; `C¹` does
  not give `∂_τ∂_θ = ∂_θ∂_τ`, so the a.e. **slot chain rule**
  `∂_τ (D_z^b D_θ^a (slice g ·))(p) = (D_z^b D_θ^a (epsRHSP … τ))(p)` (for slot words of length
  `≤ 6`) is not available.  The tree's producers of it (`EpsE4Thr.mixed_slice_deriv,
  mixed_slice_deriv_at`) take — as an explicit hypothesis — the *slot-level fake-time continuity of
  the scheme's right-hand side*, `∀ z θ ∈ Q0, ContinuousOn (fun s => mixed j i (epsRHSP … s) z θ)`;
  this is interface item (IV) (`hcontUAll`) of `EpsE4Thr.DiagCurveI_data_of_solution`, listed there
  as producible nowhere in the tree (`EpsLocalPStar.EpsRHSPLipX` gives only *weighted-`L²`*
  continuity in the fake time, not pointwise slot continuity; `hmeas` for the higher slots is
  similarly only obtainable from the slot continuity).  A machine-checked analysis of the
  consequences is in the S4 notes (groups (M1)–(M4)); the same conclusion was reached
  independently for the level-four siblings D1 (`energyDeriv_JfamP_ball`) and D2
  (`energyCont_JfamP_ball`), for F6 (`rawSlice_L12_zero`) and for L-B (`aprioriP_of_halvesB`).
* the **domination** for the differentiation (uniform bound of the level-six slots of the derivative
  family) is likewise not what a bound on the *slices* gives: by AM–GM the majorant splits into
  `HkIntegrand α 6 (slice g σ)` (bounded by `hb`) plus the same quantity for `epsRHSP … σ`, whose
  fake-time behaviour is the missing item above.
* equivalently: `hb` is exactly S4's `hbdd6`, and S4's prover established that `hbdd6` is *not* the
  missing hypothesis — so a leaf whose only added hypothesis is `hbdd6` inherits the same gap.

**(3) The alternative (norm propagation) route cannot be ε-uniform.**  The Volterra identity
`slice g τ − slice g 0 = ∫₀^τ epsRHSP α ρ ε Φs E g s ds` together with the `ℋ⁶`-valued Minkowski
inequality gives `N(τ) ≤ N(0) + ∫₀^τ ‖epsRHSP … s‖₆ ds`, and the semi-tame bound
(`epsWP_semitame`, `Apriori4Leaves/EpsWPSemitame.lean`) combined with the mollifier *gain*
`‖J_ε u‖₇ ≤ (Cg/ε)‖u‖₆` produces a **linear coefficient `Ct·Cg/ε`**.  The resulting Riccati
comparison blows up at a time `≍ ε/C'` and is genuinely `ε`-dependent, so it cannot produce a
threshold `ε₆` and a constant `E₁` valid for all `ε ≤ ε₆`.  (This is the analysis of
`NOTES_sixthChapterB_leaf_proof.md` §3b.)  The `ε`-uniform content of the chapter rests on the
*energy* formulation, i.e. on S4.

## The repair

The exact missing hypothesis, in the strongest usable form, is the ε- **and solution-uniform**
`ℋ⁶` bound: **one** `B` with `Xn6 α (slice g τ) ≤ B` for all admissible `(α, ε, T, Φs, E, g₀, g)`
and all `τ ∈ [0,T]`.  From it the conclusion is immediate by `exists_IP6o_cs_uniform` (proved
below): `E₁ := max (K²) (CC·B²)`, `ε₆ := 1`.  That is
`sixthChapterB_of_uniformBound` below, `sorry`-free.  (Equivalently one may carry the level-six
energy identity S4 — or, better, the pointwise slot continuity of `epsRHSP`, interface item (IV) —
and then the route L-A + L-C closes as prescribed by the two reviewers of this path; compare the
repaired siblings `rawE6_ineq_uniform_of_leaves`, `rawE6_deriv_of_diagData`,
`aprioriP_of_halvesB_strict`.)
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## The assigned statement (verbatim, mis-stated: see the header) -/


/-! ## The Cauchy–Schwarz constant of the level-six pairing

`IP6o` is the concrete level-six pairing `IP6 1 … 1`; the proved `StrongPersist.IP6_cs_coeffs`
gives its Cauchy–Schwarz bound on the honest `ℋ⁶`-class (`HQo α 6`), with a single `α`-free
constant.  This is what converts the *value* bound `Xn6 α (slice g τ) ≤ B` into the raw-energy
bound `rawE6 α g τ ≤ CC·B²`. -/

/-- Cauchy–Schwarz for the concrete level-six pairing `IP6o` on the honest `ℋ⁶`-class. -/
theorem exists_IP6o_cs_uniform :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      |Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α f g|
        ≤ CC * Work.FTS.StrongGlobal.Xn6 α f * Work.FTS.StrongGlobal.Xn6 α g := by
  obtain ⟨CC, hCC, h⟩ :=
    Work.FTS.StrongPersist.IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 (1 : ℝ) one_pos
  exact ⟨CC, hCC, fun α hα f g hf hg => h α hα f g hf hg⟩

/-! ## The sharpest repair: one `ℋ⁶` bound for the whole family

The hypothesis below is the assigned `hb` with its existential *outside* the `∀`-block: a single
`B` valid for every admissible datum, every `ε ∈ (0,1]` and every solution.  This is exactly the
information that the conclusion needs and that `hb` does not supply; with it the conclusion follows
immediately, with `E₁ = max (K²) (CC·B²)` and `ε₆ = 1`. -/


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.hid9_of_parts_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hid9''_of_parts_proved` — the frozen assembly `StreamBdryIface.hid9''_of_parts`

The (9″) producer: for the firing data of the strong route, the physical velocity built from the
vorticity `physOmega a A B (extG g)` agrees on `Uax` with `Cyl.psiField` of the meridian field of
the firing stream function `psiFire Φs E g`.

Assembly (see `Assembly/hid9_of_slot`): SB0 (`sb0_psiField_proved`) rewrites the field to
`BSIdent.merPsi a A B (psiHatP (pExp a) Φs E g)`; the BSIdent port `hid_of_corrected'_slim`
(delivered by `FTS_BSIdentP` and already wired into the frozen interface) is applied at
`Φ := psiHatP`, `g := extG G`; `hlaw` comes from `Sol` + `bslOp gaugeMode = 0`
(`SB25.gaugeMode_facts`) + `hG`; `hΦsm` is `sb2_c2_proved`; the plane/axis values come from
`oddPerS`; the rates are `sb6_rates_proved` fed by `Inputs.slice_inputs` (frozen, now proved by the
`RXT.velVanish2` route rather than `VelPkg.dbnd`) and `sb4_near0_proved`; the final rewrite
`physOmega (extG G) = physOmega (extG g)` uses `hG`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

set_option autoImplicit false

/-- **(9″) proved** (frozen type `hid9''_of_parts`). -/
theorem hid9''_of_parts_proved {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs) :
    ∀ (g G : Work.FTS.Galerkin.Fam) (A B : ℝ → ℝ) (C : Work.FTS.Physical.PhysClock),
      Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g →
      Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g →
      Work.FTS.Final.ClockData (Work.FTS.Regularity.pExp a)
        (Work.FTS.Nonlin.PsiCan Φs E g) g A B C →
      (∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G)) →
      (∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
                (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x := by
  intro g G A B C hSol hOK hClock hreg hG
  refine Assembly.hid9_of_slot ha ha13 hEll hEL hStar g G A B C hSol hOK hClock hreg ?_ hG
  intro τ hτ
  obtain ⟨M, L, Mf, _hC3, hslot, _hsrc⟩ :=
    Work.FTS_StreamBdry.Inputs.slice_inputs ha ha13 hEll hEL hStar hSol hOK hreg hG τ hτ
  exact ⟨M, hslot⟩

end Work.FTS_StreamBdry
end
end
