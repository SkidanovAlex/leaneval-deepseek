import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Agree.VkCharts
import Submission.Work.Agree.S4Bundle
import Submission.Work.Agree.gaugeDefs
import Submission.Work.Agree.gaugeProps
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The splitting of the tangent bundle of the disc bundle `D(ξ) = Vk (-2)`

This file proves `Work.Agree.GeometryB`.

## Infrastructure developed here

* the identification of the two distinguished charts of the glueing (`chartAt (ιX 0)`,
  `chartAt (ιY 0)`) and of the two base sets of `vkTangent h`;
* `Work.Agree.bundleIso_of_coordChange_eq` — two presentations of a bundle (same base sets, same
  transition functions, possibly different `indexAt`) are isomorphic;
* `Work.Agree.continuous_totalSpaceMap_clm_at` — a *local* criterion for the continuity of the
  total-space map of a fibrewise-linear family: it suffices that at each point the chart expression
  evaluated in the *point's own* pair of charts be continuous there.
-/

open scoped Manifold ContDiff Topology
open Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses
open Submission.Glue

noncomputable section

/-! ## Two presentations of a bundle with the same base sets and transition functions -/

/-- **Two gluing data with the same base sets and the same transition functions are isomorphic**,
even if they carry different `indexAt` maps.  The isomorphism is the coordinate-change gauge
`Z.coordChange (Z.indexAt b) (Z'.indexAt b) b`. -/
theorem bundleIso_coordChange_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*}
    [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*}
    (Z Z' : VectorBundleCore 𝕜 B F ι) (hbase : Z.baseSet = Z'.baseSet)
    (hcoord : ∀ i j x, Z.coordChange i j x = Z'.coordChange i j x) :
    Nonempty (Work.Thom.BundleIso Z Z') := by
  have key1 : ∀ b : B, b ∈ Z.baseSet (Z'.indexAt b) := fun b => by
    rw [hbase]; exact Z'.mem_baseSet_at b
  have key2 : ∀ b : B, b ∈ Z.baseSet (Z.indexAt b) := fun b => Z.mem_baseSet_at b
  refine ⟨{ hom := fun b => (Z.coordChange (Z.indexAt b) (Z'.indexAt b) b).toLinearMap
            inv := fun b => (Z.coordChange (Z'.indexAt b) (Z.indexAt b) b).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    show Z.coordChange (Z'.indexAt b) (Z.indexAt b) b
        (Z.coordChange (Z.indexAt b) (Z'.indexAt b) b x) = x
    have h := Z.coordChange_comp (Z.indexAt b) (Z'.indexAt b) (Z.indexAt b) b
      ⟨⟨key2 b, key1 b⟩, key2 b⟩ x
    rw [Z.coordChange_self (Z.indexAt b) b (key2 b) x] at h
    exact h
  · intro b y
    show Z.coordChange (Z.indexAt b) (Z'.indexAt b) b
        (Z.coordChange (Z'.indexAt b) (Z.indexAt b) b y) = y
    have h := Z.coordChange_comp (Z'.indexAt b) (Z.indexAt b) (Z'.indexAt b) b
      ⟨⟨key1 b, key2 b⟩, key1 b⟩ y
    rw [Z.coordChange_self (Z'.indexAt b) b (key1 b) y] at h
    exact h
  · have hc := Work.Thom.continuous_totalSpaceMap_clm_gen Z Z' (ContinuousMap.id B)
      (fun b => Z.coordChange (Z.indexAt b) (Z'.indexAt b) b) ?_
    · exact hc
    · intro i₁ i₂
      rw [ContinuousMap.coe_id, Set.preimage_id]
      have hcont : ContinuousOn (fun b => Z.coordChange i₁ i₂ b) (Z.baseSet i₁ ∩ Z'.baseSet i₂) :=
        (Z.continuousOn_coordChange i₁ i₂).mono
          (fun b hb => ⟨hb.1, by rw [hbase]; exact hb.2⟩)
      refine hcont.congr (fun b hb => ?_)
      ext v
      simp only [ContinuousLinearMap.comp_apply, id_eq]
      rw [← hcoord (Z'.indexAt b) i₂ b]
      rw [Z.coordChange_comp i₁ (Z.indexAt b) (Z'.indexAt b) b ⟨⟨hb.1, key2 b⟩, key1 b⟩ v]
      rw [Z.coordChange_comp i₁ (Z'.indexAt b) i₂ b
        ⟨⟨hb.1, key1 b⟩, by rw [hbase]; exact hb.2⟩ v]
  · have hc := Work.Thom.continuous_totalSpaceMap_clm_gen Z' Z (ContinuousMap.id B)
      (fun b => Z.coordChange (Z'.indexAt b) (Z.indexAt b) b) ?_
    · exact hc
    · intro i₁ i₂
      rw [ContinuousMap.coe_id, Set.preimage_id]
      have hcont : ContinuousOn (fun b => Z.coordChange i₁ i₂ b) (Z'.baseSet i₁ ∩ Z.baseSet i₂) :=
        (Z.continuousOn_coordChange i₁ i₂).mono
          (fun b hb => ⟨by rw [hbase]; exact hb.1, hb.2⟩)
      refine hcont.congr (fun b hb => ?_)
      ext v
      simp only [ContinuousLinearMap.comp_apply, id_eq]
      rw [← hcoord i₁ (Z'.indexAt b) b]
      rw [Z.coordChange_comp i₁ (Z'.indexAt b) (Z.indexAt b) b
        ⟨⟨by rw [hbase]; exact hb.1, key1 b⟩, key2 b⟩ v]
      rw [Z.coordChange_comp i₁ (Z.indexAt b) i₂ b
        ⟨⟨by rw [hbase]; exact hb.1, key2 b⟩, hb.2⟩ v]



/-! ## The exponential interpolation of a gauge -/

/-- **Continuity of the exponential interpolation `b ↦ A b * exp (κ b • Y b)`** of a continuous
`GL`-valued family `A` towards the family `A * exp Y`.  Since `exp (κ b • Y b)` is invertible for
every `b` (`NormedSpace.isUnit_exp`), this is a continuous interpolation within the units: the
`κ = 0` end is `A`, the `κ = 1` end is `A * exp Y`.  This is the tool that lets one avoid a linear
interpolation between two `GL`-valued functions whose determinants have opposite signs. -/
theorem continuous_exp_interpolant {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAlgebra ℚ 𝔸] [IsScalarTower ℚ ℝ 𝔸] [CompleteSpace 𝔸] {X : Type*} [TopologicalSpace X]
    (A Y : X → 𝔸) (k : X → ℝ) (hA : Continuous A) (hY : Continuous Y) (hk : Continuous k) :
    Continuous fun b => A b * NormedSpace.exp (k b • Y b) := by
  refine hA.mul ?_
  exact NormedSpace.exp_continuous.comp (hk.smul hY)

/-- The exponential interpolation of matrices is a unit at every point. -/
theorem isUnit_exp_interpolant_matrix {n : ℕ} {X : Type*}
    (A Y : X → Matrix (Fin n) (Fin n) ℝ) (k : X → ℝ) (b : X)
    (hA : IsUnit (A b)) : IsUnit (A b * NormedSpace.exp (k b • Y b)) :=
  hA.mul (Matrix.isUnit_exp _)


/-! ## The cocycle identities carried by the two presentations -/

section Cocycle

variable (h : ∀ x : Vk, ∃ i : Fin 2,
    x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i))

/-- On the overlap of the two charts of the disc bundle, the two transition functions of
`vkTangent h` are mutually inverse (the cocycle condition `cc(0,1) ∘ cc(1,0) = cc(0,0) = 1`). -/
theorem vkTangent_coordChange_one_zero_comp (b : Vk)
    (hb : b ∈ (vkTangent h).baseSet 0 ∩ (vkTangent h).baseSet 1) :
    ((vkTangent h).coordChange 0 1 b).comp ((vkTangent h).coordChange 1 0 b) = 1 := by
  have hb0 : b ∈ (vkTangent h).baseSet 0 := hb.1
  have hb1 : b ∈ (vkTangent h).baseSet 1 := hb.2
  apply ContinuousLinearMap.ext
  intro v
  show (vkTangent h).coordChange 0 1 b ((vkTangent h).coordChange 1 0 b v) = v
  rw [(vkTangent h).coordChange_comp 1 0 1 b ⟨⟨hb1, hb0⟩, hb1⟩ v,
    (vkTangent h).coordChange_self 1 b hb1 v]

/-- The same, in the other order. -/
theorem vkTangent_coordChange_zero_one_comp (b : Vk)
    (hb : b ∈ (vkTangent h).baseSet 0 ∩ (vkTangent h).baseSet 1) :
    ((vkTangent h).coordChange 1 0 b).comp ((vkTangent h).coordChange 0 1 b) = 1 := by
  have hb0 : b ∈ (vkTangent h).baseSet 0 := hb.1
  have hb1 : b ∈ (vkTangent h).baseSet 1 := hb.2
  apply ContinuousLinearMap.ext
  intro v
  show (vkTangent h).coordChange 1 0 b ((vkTangent h).coordChange 0 1 b v) = v
  rw [(vkTangent h).coordChange_comp 0 1 0 b ⟨⟨hb0, hb1⟩, hb0⟩ v,
    (vkTangent h).coordChange_self 0 b hb0 v]

end Cocycle

/-- The transition functions of the target presentation `π^*(L¹R¹ ⊞ L²R⁻¹)` between the charts
`(false,false)` and `(true,true)` are mutually inverse on their common base set. -/
theorem target_coordChange_ff_tt_comp {b : Vk}
    (hb : b ∈ (Work.Thom.bundleComap
        (RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1))) discProj).baseSet (false, false) ∩
      (Work.Thom.bundleComap
        (RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1))) discProj).baseSet (true, true)) :
    ((Work.Thom.bundleComap (RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1)))
        discProj).coordChange (false, false) (true, true) b).comp
      ((Work.Thom.bundleComap (RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1)))
        discProj).coordChange (true, true) (false, false) b) = 1 := by
  set Z := Work.Thom.bundleComap (RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1)))
    discProj with hZ
  apply ContinuousLinearMap.ext
  intro v
  show Z.coordChange (false, false) (true, true) b
      (Z.coordChange (true, true) (false, false) b v) = v
  rw [Z.coordChange_comp (true, true) (false, false) (true, true) b ⟨⟨hb.2, hb.1⟩, hb.2⟩ v,
    Z.coordChange_self (true, true) b hb.2 v]

/-! ## Notes towards the proof of `geometryB` (work in progress)

**This block records the reduction worked out in the session of the first proof attempt.  Read it
before touching the target: several plausible-looking ansätze below are provably dead.**

Write

* `π := Work.TangentClasses.discProj : C(Vk, S4)` (this is `Work.Milnor.vBaseMap (-2)`),
* `Z := vkTangent h` (fibre `MSpace8 = ℝ⁴ × ℍ`, cover `Fin 2`),
* `W := Work.Thom.bundleComap (RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1))) π`
  (fibre `ℝ⁴ × ℝ⁴`, cover `Bool × Bool`).

### 1. The two covers agree

`Work.Agree.clutchBundle a b` has base sets `hemi0 = {p ≠ ∞}` (`false`) and `hemi1 = {p ≠ ↑0}`
(`true`).  Since `π (ιX p) = ↑p.1` and `π (ιY p) = baseChart2 p.1`, and `baseChart2 0 = ∞`
(`Submission.Work.Milnor.Base.baseChart2_zero`), one has `π(Vk) = {↑x} ∪ {∞}` and hence

* `Z.baseSet 0 = range ιX = π ⁻¹' hemi0 = W.baseSet (false,false) =: U₀`,
* `Z.baseSet 1 = range ιY = π ⁻¹' hemi1 = W.baseSet (true,true)  =: U₁`,
* `W.baseSet (false,true) = W.baseSet (true,false) = U₀ ∩ U₁`,
* `U₀ \ U₁ = π ⁻¹' {↑0} =: Z₀` and `U₁ \ U₀ = π ⁻¹' {∞} =: Z∞` are **disjoint** codimension-`4`
  copies of `ℍ` (the "fibres over `↑0` and over `∞`"); in the X-chart they are `{x = 0}` and the
  locus `‖x‖ → ∞`.  `Vk ∖ (Z₀ ∪ Z∞) = U₀ ∩ U₁ = π ⁻¹'(hemi0 ∩ hemi1)`.

In particular `U₀ ∪ U₁ = Vk` and, for `b = ιX (x,y)`, the X-chart coordinate is `x`, the Y-chart
coordinate is `vMap (-2) (x,y)`, and `uDir (π b) = unitDir x`.

### 2. The fibre change

`ψ : MSpace8 ≃L[ℝ] (ℝ⁴ × ℝ⁴)`, `ψ = id × Work.Agree.ofQ`, transports `W` to a core `W'` with fibre
`MSpace8` and the same cover (`Work.Thom.exists_coreMapFibre`), which is isomorphic to `W`.  All the
transitions below are written in `MSpace8`-coordinates, so it suffices to prove
`Nonempty (BundleIso Z W')`.  Concretely `W'.cc (false,false) (true,true) b = D b` where

`D b = diag (qTwist 1 1 (uDir (π b)), fun v => unitDir x * ... )`, i.e. the second block is just
`v ↦ u v u⁻¹` in `ℍ`-coordinates, and `W'.cc (false,false) (false,true) = diag (1, that)`,
`W'.cc (false,false) (true,false) = diag (qTwist 1 1 (uDir (π b)), 1)`.

### 3. The transition functions of the source

`Work.Agree.vkTangent_coordChange_zero_one` (delegated, statement below) identifies

`Z.cc 0 1 b = fderiv ℝ (vMap (-2)) x =: α b`  (`x = chartOfX 0 b`),

a block-triangular `[[A,0],[B,C]]` with (`Work.Agree.fderiv_vMap_apply`, delegated)
`A = fderiv invBase x = ‖x‖⁻² • s_{u x}` (`s_v` = reflection in `v^⊥`),
`C = (v ↦ u x · v · (u x)⁻¹)`, `B = ∂/∂x (u²yu⁻¹)` and `Z.cc 1 0 b = β b := (α b)⁻¹`.
The (2,2)-block of `α` and of `D` are the *same* function of `b`.

### 4. The gauge (via `Work.Thom.nonempty_bundleIso_of_gauge`)

`Submission/Work/Gen/EulerToolkit.lean` has the tool: to build `BundleIso Z Z'` it suffices to
provide `Φ : ι → ι' → B → (F →L F')` (the chart expressions) with `hcont` (continuity of `Φ i i'` on
`Z.baseSet i ∩ Z'.baseSet i'`), `htgt` (`Z'.cc t t' ∘ Φ i t = Φ i t'`), `hsrc`
(`Φ i t ∘ Z.cc i' i = Φ i' t`), their `Φinv` analogues, and the pointwise inverse laws.  The
resulting `hom` is `fun b => Φ (Z.indexAt b) (Z'.indexAt b) b`.

Take `σ₀ = (false,false)`, `σ₁ = (true,true)` (identifying `Fin 2` with these target charts) and

`Φ i i' b := W'.cc (σ i) i' b ∘ H i b`

for functions `H 0 : U₀ → GL(MSpace8)`, `H 1 : U₁ → GL(MSpace8)`.  Then `htgt` is the cocycle and
the remaining conditions become

* `H 0` continuous and invertible on `U₀` (in particular *at* every point of `Z₀`),
* `H 1` continuous and invertible on `U₁` (in particular *at* every point of `Z∞`),
* `H 1 = D · H 0 · β` on `U₀ ∩ U₁` (the source factor is `Z.cc 1 0 = β`),
* the inverse family `Φinv i i' b := (H i b)⁻¹ ∘ W'.cc i' (σ i) b` with `hcontinv`, `hsrcinv`,
  `htgtinv`; note `Work.Agree.continuousOn_inv_of_comp_eq_one`
  (`Submission/Work/Agree/presentation_independence.lean`) gives continuity of the pointwise
  inverse, so it suffices to build `Φ` for `H` and `H⁻¹` and check `hcont`/`hcontinv`.

Since `Z'.cc (σ₀,σ₁) = D` and `Z.cc 1 0 = β = α⁻¹`, the only real work is the pair `(H 0, H 1)`.

### 5. The asymptotics (why the naive choices fail)

In the X-chart, for `b = ιX (x,y)`, `x → 0` is `Z₀` and `‖x‖ → ∞` is `Z∞`.  With `u = unitDir x`:

* `α = [[‖x‖⁻² s_u, 0],[B, C]]` with `B = O(‖x‖⁻¹)`: it blows up as `x → 0` and degenerates as
  `‖x‖ → ∞`;
* `β = α⁻¹ = [[‖x‖² s_u, 0],[*, C⁻¹]]`: it *degenerates* (`→` a matrix of rank `4`) as `x → 0` and
  *blows up* like `‖x‖²` as `‖x‖ → ∞`; in both regimes the block `C⁻¹ = qTwist (-2,1)(u)` **spins**
  (it has no limit, because `u` ranges over all of `S³` as `b → Z₀` or `b → Z∞`).
* `D = diag (qTwist 1 1 (uDir (π b)), …)` likewise spins near `Z₀` and near `Z∞`.

Consequences (all verified by hand in the failed attempts; do not redo them):

* `H 0 := 1` or `H 0 := D⁻¹` fail: `D H 0 β` is then unbounded/spinning at `Z∞ ∈ U₁`.
* `H 0 := α · (constant)` fails: `α` blows up at `Z₀ ∈ U₀`.
* `H 0 := β⁻¹ · (constant)` fails: `β⁻¹ = α` again, and even the "spinning tracking" version
  `‖x'‖⁻² (R_u⁻¹ L_u⁻¹ M s_u)` blows up at `Z₀` (the X- and Y-chart radii are reciprocal, so a
  formula that decays at `Z∞` blows up at `Z₀`).
* What is needed is an interpolation in the radial variable between a formula valid near `Z∞` and
  one valid at `Z₀`, *preserving invertibility*.  `GL(8,ℝ) ≃ O(8)` is connected, so only `π₃` can
  obstruct; and there is no obstruction here:
  - `s_v = -L_v R_v J` for every unit `v` (where `J` is quaternion conjugation `v ↦ \bar v`, a
    **fixed** matrix, `J² = 1`), hence `L = A · (-‖x‖² J)`: the `TS⁴`-projection of `α` and the
    `TS⁴`-summand of `D` differ by the **constant** gauge `-‖x‖² J`, i.e. by a scalar times a fixed
    matrix (equivalently: `qTwist 1 1 (unitDir x) = ‖x‖⁻² s_u · (-‖x‖² J)`, both loops represent the
    same class `(e,p₁) = (2,0)`);
  - `class (α) = class (D) = 3` in `π₃ (GL(8,ℝ)) = ℤ` (the off-diagonal block `B` is a unipotent
    block, homotopic to `1`, so the class adds over the diagonal blocks, `class (s_u) = 2` and
    `class (C) = 1`); hence `class (D⁻¹ α) = 0` and there is **no** class obstruction to the
    interpolation.
* A clean shape that should work: choose `H 0 := Φ₀` for `‖x‖ ≤ 1` (any continuous invertible
  function of the `Z₀`-side variables) and `H 0 := α · Ψ` for `‖x‖` large, glued by a homotopy of
  loops in `GL(8)` (possible because the classes agree), and `H 1 := D H 0 β`.  The tricky part is
  making the glued family continuous *and* invertible; the involution `J` above makes the two
  boundary loops `u ↦ L_u R_u M (u)` and `u ↦ M (u)`-type loops explicitly cancel.

### 6. Available tools (checked)

* `Work.Thom.nonempty_bundleIso_of_gauge`, `Submission/Work/Gen/EulerToolkit.lean` (namespace
  `Work.Thom`) — the criterion of §4; `Submission/Work/Gen/cp4ChernPresentation.lean` works through
  an instance of it and is the best worked example.
* `Work.Thom.exists_coreMapFibre` (`Submission/Work/Thom/exists_coreMapFibre.lean`) — the fibre
  change `ψ` of §2.
* `Work.Thom.continuous_totalSpaceMap_clm_gen`, and its pointwise variant
  `Work.Agree.continuous_totalSpaceMap_at` (`Submission/Work/Agree/continuous_totalSpaceMap_at.lean`,
  PROVED) — the low-level continuity criteria, if one prefers to build the `BundleIso` directly.
* `Work.Agree.continuousOn_inv_of_comp_eq_one`
  (`Submission/Work/Agree/presentation_independence.lean`) — continuity of a pointwise inverse;
  removes the need to prove `hcontinv` from scratch.
* `Work.Agree.bundleIso_coordChange_eq` (this file) — the special case where the two cores have the
  same base sets *and the same* transition functions; it only lets one change `indexAt`.  It does
  **not** apply to `GeometryB` (the transition functions differ), but it is what makes the choice of
  `indexAt` of both cores free.
* `Work.Gen.nonempty_bundleIso_reindexCore`
  (`Submission/Work/Gen/TangentPresentation.lean`) and `Work.Agree.presentation_independence`.

### 7. Delegated / outstanding

* `Agree/vkTangent_coordChange_zero_one` and `Agree/fderiv_vMap_apply` were written and reviewed
  (both verdicts "looks correct as stated") in the session of the first attempt; the fleet was at
  capacity when they were requested, so re-request them first: they are the two computational bricks
  of §3.  (`Work.Agree.continuous_totalSpaceMap_at`, requested in the same session, *was* proved and
  is on disk.)
* Cautions: `fderiv_vMap_apply` is **false** at `x.1 = 0` (there `unitDir` is a junk value while
  `fderiv (vMap (-2))` is `0`), hence the hypothesis `x.1 ≠ 0`, which is exactly what
  `b ∈ U₀ ∩ U₁` supplies.  `coordChange` is only meaningful on the overlap.  `ext v` at the
  `ContinuousLinearMap` level over-desugars `MSpace8 = ℝ⁴ × ℍ`; use
  `apply ContinuousLinearMap.ext; intro v` followed by `show`.
-/

/-! ## The target -/

open Work.TangentClasses in
/-- **GEOMETRY B.**

The proof is the application of `Work.Thom.nonempty_bundleIso_of_gauge` to `Z = vkTangent h` and
`W' = targetCore`; the two gauges are `gaugeH0` (chart `0`) and `gaugeH1 h` (chart `1`) and the
inverses `gaugeH0inv`, `gaugeH1inv h`.  All the ingredients are proved:

* `Work.Agree.gauge_continuous` : `ContinuousOn gaugeH0 gaugeUX ∧ ContinuousOn gaugeH0inv gaugeUX`;
* `Work.Agree.gaugeH1_props`-equivalents in `gaugeProps.lean` : `continuousOn_gaugeH1`,
  `continuousOn_gaugeH1inv`, `gaugeH1_comp_gaugeH1inv`, `gaugeH1inv_comp_gaugeH1`, `gaugeH1_eq`,
  `gaugeH1inv_eq`, `gaugeH1_expr_eq_one`, `gaugeH1inv_expr_eq_one`;
* `gaugeProps.lean` : `gaugeH0_comp_gaugeH0inv`, `gaugeH0inv_comp_gaugeH0`, the bookkeeping
  (`gaugeUX_subset_targetCore_ff`, `gaugeUY_subset_targetCore_tt`, `gaugeX_ne_zero_of_mem`,
  `gaugeUX_of_mem_gaugeUY`, `gaugeYNorm_eq_inv_norm`), the block forms `targetCore_blk`,
  `vkTangent_blk`, and the key identity `gaugeKey_all`.

The remaining work is purely bookkeeping with `Work.Thom.nonempty_bundleIso_of_gauge` (a first
draft of it is in `GEOMETRYB_ASSEMBLY.lean.txt`), then composing with the isomorphism
`Work.Agree.nonempty_bundleIso_targetC_targetCore` (reversed) given by `exists_coreMapFibre`.
-/
theorem geometryB : Work.Agree.GeometryB := by
  intro h
  have hsub0 : (vkTangent h).baseSet 0 = gaugeUX := vkTangent_baseSet_zero h
  have hsub1 : (vkTangent h).baseSet 1 = gaugeUY := vkTangent_baseSet_one h
  have key : Nonempty (Work.Thom.BundleIso (vkTangent h) targetC) := by
    have hcore : Nonempty (Work.Thom.BundleIso (vkTangent h) targetCore) := by
      refine Work.Thom.nonempty_bundleIso_of_gauge (vkTangent h) targetCore
        (fun i i' b => (targetCore.coordChange (if i = 0 then (false,false) else (true,true)) i' b).comp
          (if i = 0 then gaugeH0 b else gaugeH1 h b))
        (fun i i' b => (if i = 0 then gaugeH0inv b else gaugeH1inv h b).comp
          (targetCore.coordChange i' (if i = 0 then (false,false) else (true,true)) b))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · -- hcont
        intro i i'
        by_cases hi : i = 0
        · simp only [if_pos hi]
          subst hi
          have h1 : ContinuousOn (fun b => targetCore.coordChange (false,false) i' b)
              ((vkTangent h).baseSet 0 ∩ targetCore.baseSet i') := by
            rw [hsub0]
            exact (targetCore.continuousOn_coordChange _ _).mono
              (fun b hb => ⟨gaugeUX_subset_targetCore_ff hb.1, hb.2⟩)
          have h2 : ContinuousOn (fun b => gaugeH0 b)
              ((vkTangent h).baseSet 0 ∩ targetCore.baseSet i') := by
            rw [hsub0]
            exact gauge_continuous.1.mono Set.inter_subset_left
          exact h1.clm_comp h2
        · simp only [if_neg hi]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl hi
            · rfl
          subst hi1
          have h1 : ContinuousOn (fun b => targetCore.coordChange (true,true) i' b)
              ((vkTangent h).baseSet 1 ∩ targetCore.baseSet i') := by
            rw [hsub1]
            exact (targetCore.continuousOn_coordChange _ _).mono
              (fun b hb => ⟨gaugeUY_subset_targetCore_tt hb.1, hb.2⟩)
          have h2 : ContinuousOn (fun b => gaugeH1 h b)
              ((vkTangent h).baseSet 1 ∩ targetCore.baseSet i') := by
            rw [hsub1]
            exact (continuousOn_gaugeH1 h).mono Set.inter_subset_left
          exact h1.clm_comp h2
      · -- hcontinv
        intro i i'
        by_cases hi : i = 0
        · simp only [if_pos hi]
          subst hi
          have h2 : ContinuousOn (fun b => gaugeH0inv b)
              ((vkTangent h).baseSet 0 ∩ targetCore.baseSet i') := by
            rw [hsub0]
            exact gauge_continuous.2.mono Set.inter_subset_left
          have h1 : ContinuousOn (fun b => targetCore.coordChange i' (false,false) b)
              ((vkTangent h).baseSet 0 ∩ targetCore.baseSet i') := by
            refine (targetCore.continuousOn_coordChange i' (false,false)).mono ?_
            intro b hb
            exact ⟨hb.2, gaugeUX_subset_targetCore_ff (hsub0 ▸ hb.1)⟩
          exact h2.clm_comp h1
        · simp only [if_neg hi]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl hi
            · rfl
          subst hi1
          have h2 : ContinuousOn (fun b => gaugeH1inv h b)
              ((vkTangent h).baseSet 1 ∩ targetCore.baseSet i') := by
            rw [hsub1]
            exact (continuousOn_gaugeH1inv h).mono Set.inter_subset_left
          have h1 : ContinuousOn (fun b => targetCore.coordChange i' (true,true) b)
              ((vkTangent h).baseSet 1 ∩ targetCore.baseSet i') := by
            refine (targetCore.continuousOn_coordChange i' (true,true)).mono ?_
            intro b hb
            exact ⟨hb.2, gaugeUY_subset_targetCore_tt (hsub1 ▸ hb.1)⟩
          exact h2.clm_comp h1
      · -- htgt
        intro i t t' b hi ht ht'
        by_cases h0 : i = 0
        · simp only [if_pos h0]
          subst h0
          have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff (hsub0 ▸ hi)
          apply ContinuousLinearMap.ext; intro v
          simp only [ContinuousLinearMap.comp_apply]
          exact targetCore.coordChange_comp (false,false) t t' b ⟨⟨hff, ht⟩, ht'⟩ (gaugeH0 b v)
        · simp only [if_neg h0]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl h0
            · rfl
          subst hi1
          have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt (hsub1 ▸ hi)
          apply ContinuousLinearMap.ext; intro v
          simp only [ContinuousLinearMap.comp_apply]
          exact targetCore.coordChange_comp (true,true) t t' b ⟨⟨htt, ht⟩, ht'⟩ (gaugeH1 h b v)
      · -- hsrc
        intro i t i' b hi hi' ht
        by_cases h0 : i = 0
        · simp only [if_pos h0]
          subst h0
          have hUX : b ∈ gaugeUX := hsub0 ▸ hi
          have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff hUX
          by_cases h1 : i' = 0
          · simp only [if_pos h1]
            subst h1
            apply ContinuousLinearMap.ext; intro v
            simp only [ContinuousLinearMap.comp_apply, (vkTangent h).coordChange_self 0 b hi]
          · simp only [if_neg h1]
            have hi1' : i' = 1 := by
              fin_cases i'
              · exact absurd rfl h1
              · rfl
            subst hi1'
            have hUY : b ∈ gaugeUY := hsub1 ▸ hi'
            have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt hUY
            have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hUX, hUY⟩
            have hg1 : gaugeH1 h b = (targetCore.coordChange (false,false) (true,true) b).comp
                ((gaugeH0 b).comp ((vkTangent h).coordChange 1 0 b)) := gaugeH1_eq h b hb'
            apply ContinuousLinearMap.ext; intro v
            rw [hg1]
            simp only [ContinuousLinearMap.comp_apply]
            exact (targetCore.coordChange_comp (false,false) (true,true) t b
              ⟨⟨hff, htt⟩, ht⟩ (gaugeH0 b ((vkTangent h).coordChange 1 0 b v))).symm
        · simp only [if_neg h0]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl h0
            · rfl
          subst hi1
          have hUY : b ∈ gaugeUY := hsub1 ▸ hi
          have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt hUY
          by_cases h1 : i' = 0
          · simp only [if_pos h1]
            subst h1
            have hUX : b ∈ gaugeUX := hsub0 ▸ hi'
            have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff hUX
            have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hUX, hUY⟩
            have hg1 : gaugeH1 h b = (targetCore.coordChange (false,false) (true,true) b).comp
                ((gaugeH0 b).comp ((vkTangent h).coordChange 1 0 b)) := gaugeH1_eq h b hb'
            have hαβ : ∀ w, (vkTangent h).coordChange 1 0 b ((vkTangent h).coordChange 0 1 b w) = w :=
              fun w => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f w)
                (gauge_cc_identities h b hb').1
            apply ContinuousLinearMap.ext; intro v
            rw [hg1]
            simp only [ContinuousLinearMap.comp_apply, hαβ]
            exact targetCore.coordChange_comp (false,false) (true,true) t b
              ⟨⟨hff, htt⟩, ht⟩ (gaugeH0 b v)
          · simp only [if_neg h1]
            have hi1' : i' = 1 := by
              fin_cases i'
              · exact absurd rfl h1
              · rfl
            subst hi1'
            apply ContinuousLinearMap.ext; intro v
            simp only [ContinuousLinearMap.comp_apply, (vkTangent h).coordChange_self 1 b hi]
      · -- htgtinv
        intro i t t' b hi ht ht'
        by_cases h0 : i = 0
        · simp only [if_pos h0]
          subst h0
          have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff (hsub0 ▸ hi)
          apply ContinuousLinearMap.ext; intro v
          simp only [ContinuousLinearMap.comp_apply]
          exact congrArg (fun u => gaugeH0inv b u)
            (targetCore.coordChange_comp t' t (false,false) b ⟨⟨ht', ht⟩, hff⟩ v)
        · simp only [if_neg h0]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl h0
            · rfl
          subst hi1
          have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt (hsub1 ▸ hi)
          apply ContinuousLinearMap.ext; intro v
          simp only [ContinuousLinearMap.comp_apply]
          exact congrArg (fun u => gaugeH1inv h b u)
            (targetCore.coordChange_comp t' t (true,true) b ⟨⟨ht', ht⟩, htt⟩ v)
      · -- hsrcinv
        intro i t i' b hi hi' ht
        by_cases h0 : i = 0
        · simp only [if_pos h0]
          subst h0
          have hUX : b ∈ gaugeUX := hsub0 ▸ hi
          have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff hUX
          by_cases h1 : i' = 0
          · simp only [if_pos h1]
            subst h1
            apply ContinuousLinearMap.ext; intro v
            simp only [ContinuousLinearMap.comp_apply, (vkTangent h).coordChange_self 0 b hi]
          · simp only [if_neg h1]
            have hi1' : i' = 1 := by
              fin_cases i'
              · exact absurd rfl h1
              · rfl
            subst hi1'
            have hUY : b ∈ gaugeUY := hsub1 ▸ hi'
            have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt hUY
            have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hUX, hUY⟩
            have hgi : gaugeH1inv h b = ((vkTangent h).coordChange 0 1 b).comp
                ((gaugeH0inv b).comp (targetCore.coordChange (true,true) (false,false) b)) :=
              gaugeH1inv_eq h b hb'
            apply ContinuousLinearMap.ext; intro v
            rw [hgi]
            simp only [ContinuousLinearMap.comp_apply]
            rw [targetCore.coordChange_comp t (true,true) (false,false) b ⟨⟨ht, htt⟩, hff⟩]
        · simp only [if_neg h0]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl h0
            · rfl
          subst hi1
          have hUY : b ∈ gaugeUY := hsub1 ▸ hi
          have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt hUY
          by_cases h1 : i' = 0
          · simp only [if_pos h1]
            subst h1
            have hUX : b ∈ gaugeUX := hsub0 ▸ hi'
            have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff hUX
            have hb' : b ∈ gaugeUX ∩ gaugeUY := ⟨hUX, hUY⟩
            have hgi : gaugeH1inv h b = ((vkTangent h).coordChange 0 1 b).comp
                ((gaugeH0inv b).comp (targetCore.coordChange (true,true) (false,false) b)) :=
              gaugeH1inv_eq h b hb'
            have hαβ : ∀ w, (vkTangent h).coordChange 1 0 b ((vkTangent h).coordChange 0 1 b w) = w :=
              fun w => congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f w)
                (gauge_cc_identities h b hb').1
            apply ContinuousLinearMap.ext; intro v
            rw [hgi]
            simp only [ContinuousLinearMap.comp_apply]
            rw [hαβ]
            rw [targetCore.coordChange_comp t (true,true) (false,false) b ⟨⟨ht, htt⟩, hff⟩]
          · simp only [if_neg h1]
            have hi1' : i' = 1 := by
              fin_cases i'
              · exact absurd rfl h1
              · rfl
            subst hi1'
            apply ContinuousLinearMap.ext; intro v
            simp only [ContinuousLinearMap.comp_apply, (vkTangent h).coordChange_self 1 b hi]
      · -- hleft
        intro i i' b x hb
        by_cases h0 : i = 0
        · simp only [if_pos h0]
          subst h0
          have hUX : b ∈ gaugeUX := hsub0 ▸ hb.1
          have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff hUX
          have hp : gaugeH0inv b (gaugeH0 b x) = x := by
            simpa using congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f x)
              (gaugeH0inv_comp_gaugeH0 b)
          have hstep : targetCore.coordChange i' (false,false) b
              (targetCore.coordChange (false,false) i' b (gaugeH0 b x)) = gaugeH0 b x := by
            rw [targetCore.coordChange_comp (false,false) i' (false,false) b ⟨⟨hff, hb.2⟩, hff⟩]
            exact targetCore.coordChange_self (false,false) b hff (gaugeH0 b x)
          simp only [ContinuousLinearMap.comp_apply, hstep, hp]
        · simp only [if_neg h0]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl h0
            · rfl
          subst hi1
          have hUY : b ∈ gaugeUY := hsub1 ▸ hb.1
          have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt hUY
          have hp : gaugeH1inv h b (gaugeH1 h b x) = x := by
            simpa using congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f x)
              (gaugeH1inv_comp_gaugeH1 h b hUY)
          have hstep : targetCore.coordChange i' (true,true) b
              (targetCore.coordChange (true,true) i' b (gaugeH1 h b x)) = gaugeH1 h b x := by
            rw [targetCore.coordChange_comp (true,true) i' (true,true) b ⟨⟨htt, hb.2⟩, htt⟩]
            exact targetCore.coordChange_self (true,true) b htt (gaugeH1 h b x)
          simp only [ContinuousLinearMap.comp_apply, hstep, hp]
      · -- hright
        intro i i' b y hb
        by_cases h0 : i = 0
        · simp only [if_pos h0]
          subst h0
          have hUX : b ∈ gaugeUX := hsub0 ▸ hb.1
          have hff : b ∈ targetCore.baseSet (false,false) := gaugeUX_subset_targetCore_ff hUX
          have hp : ∀ w, gaugeH0 b (gaugeH0inv b w) = w := fun w => by
            simpa using congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f w)
              (gaugeH0_comp_gaugeH0inv b)
          have hstep : targetCore.coordChange (false,false) i' b
              (targetCore.coordChange i' (false,false) b y) = y := by
            rw [targetCore.coordChange_comp i' (false,false) i' b ⟨⟨hb.2, hff⟩, hb.2⟩]
            exact targetCore.coordChange_self i' b hb.2 y
          simp only [ContinuousLinearMap.comp_apply, hp, hstep]
        · simp only [if_neg h0]
          have hi1 : i = 1 := by
            fin_cases i
            · exact absurd rfl h0
            · rfl
          subst hi1
          have hUY : b ∈ gaugeUY := hsub1 ▸ hb.1
          have htt : b ∈ targetCore.baseSet (true,true) := gaugeUY_subset_targetCore_tt hUY
          have hp : ∀ w, gaugeH1 h b (gaugeH1inv h b w) = w := fun w => by
            simpa using congrArg (fun f : Submission.Milnor.MSpace8 →L[ℝ] Submission.Milnor.MSpace8 => f w)
              (gaugeH1_comp_gaugeH1inv h b hUY)
          have hstep : targetCore.coordChange (true,true) i' b
              (targetCore.coordChange i' (true,true) b y) = y := by
            rw [targetCore.coordChange_comp i' (true,true) i' b ⟨⟨hb.2, htt⟩, hb.2⟩]
            exact targetCore.coordChange_self i' b hb.2 y
          simp only [ContinuousLinearMap.comp_apply, hp, hstep]
    obtain ⟨e1⟩ := hcore
    obtain ⟨e2⟩ := nonempty_bundleIso_targetC_targetCore
    exact ⟨e1.trans e2.symm⟩
  exact key


end

end Work.Agree
