/-
# Area LC (`Submission/Work/LeviCivita/`) — the Levi-Civita connection

This file is the **interface** of the area: it defines the Levi-Civita connection `lcConn` of a
Riemannian manifold in the framework variable block of the project (the same block the vendored
`RiemLib` library and the areas `CH`, `CURV`, `SPACE` use), and records its three defining
properties.

## The framework variable block

    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

(`Smooth` means `ContDiff ℝ ∞`, `∞ = ((⊤ : ℕ∞) : ℕ∞ω)`; **not** `⊤`, which is analytic.)

## Contents

* `lcConn` — the Levi-Civita connection, as a bundled `CovariantDerivative`.  We take Mathlib's
  `CovariantDerivative.leviCivitaConnection` (the abstract Koszul construction), so that
  torsion-freeness is a Mathlib theorem;
* `lcConn_torsion : lcConn.torsion = 0`;
* `lcConn_apply_inner` — the intrinsic **Koszul formula** for `lcConn`;
* `lcConn_compat : IsMetricCompatible lcConn` — the *challenge's* `IsMetricCompatible`
  (`LeanEval.Geometry.SphereTheorem`), proved here from the Koszul formula.

Note on instances: Mathlib's *bundle* predicate `CovariantDerivative.IsMetricCompatible` is stated
with the `NormedAddCommGroup`-derived `AddCommGroup` instances on the fibres, which are **not** the
`AddCommGroup` instances of the tangent bundle; the term `(lcConn …).IsMetricCompatible` therefore
does not even elaborate (see NOTES.md §3).  We prove the challenge's pointwise predicate instead,
which is the form `CH` and `CURV` consume, directly from the Koszul formula `lcConn_apply_inner`.

## Names a caller should use

    import Submission.Work.LeviCivita.Main
    -- Work.LeviCivita.lcConn            : CovariantDerivative I E (TangentSpace I)
    -- Work.LeviCivita.lcConn_torsion    : lcConn.torsion = 0
    -- Work.LeviCivita.lcConn_compat     : IsMetricCompatible lcConn
    -- Work.LeviCivita.lcConn_contMDiff  : ContMDiffCovariantDerivative lcConn ∞   (instance)
    -- Work.LeviCivita.chartGram_chrB_eq_koszul  (Koszul in charts, any smooth torsion-free
    --                                            metric-compatible cov)

The same four names are re-exported under the lead blueprint's namespace `Work.LC` in
`Submission/Work/LeviCivita/LC.lean`.
-/
import Submission.Work.RiemLib.ChartConnection
import Submission.Work.RiemLib.ChartCurv
import Submission.Work.Curvature.Bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.LeviCivita

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **The Levi-Civita connection** of the Riemannian manifold `M` in the framework variable block.

It is Mathlib's abstract Koszul construction `CovariantDerivative.leviCivitaConnection`; the
instance arguments `IsManifold I 2 M` and `IsContMDiffRiemannianBundle I 1 E _` are obtained from
the framework's `IsManifold I ∞ M` and `IsContMDiffRiemannianBundle I ∞ E _`.

The mathematical content of this area is that this connection is *smooth*
(`lcConn_contMDiff`, in `Submission.Work.LeviCivita.Smooth`). -/
def lcConn : CovariantDerivative I E (TangentSpace I (M := M)) :=
  CovariantDerivative.leviCivitaConnection I M

lemma lcConn_apply (σ : Π x : M, TangentSpace I x) :
    lcConn (I := I) (M := M) σ = CovariantDerivative.leviCivitaConnection I M σ := rfl

/-- **`lcConn` is torsion-free.** -/
theorem lcConn_torsion : (lcConn (I := I) (M := M)).torsion = 0 :=
  CovariantDerivative.torsion_leviCivitaConnection_eq_zero (M := M) I

/-- **The Koszul formula** for `lcConn`, in the intrinsic form of Mathlib's
`IsLeviCivitaConnection.apply_eq`: for fields `X`, `Y`, `Z` differentiable at `x`,

`⟪∇_X Y, Z⟫ = ½ (X⟪Y,Z⟫ + Y⟪Z,X⟫ − Z⟪X,Y⟫ − ⟪Y,[X,Z]⟫ − ⟪Z,[Y,X]⟫ + ⟪X,[Z,Y]⟫)`.

It is the input for `lcConn_compat` and for the smoothness proof in
`Submission.Work.LeviCivita.Smooth` (which uses it to *avoid* computing Christoffel symbols). -/
theorem lcConn_apply_inner {x : M} {X Y Z : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (lcConn (I := I) (M := M) Y x (X x)) (Z x) =
      (d% (fun x ↦ inner ℝ (Y x) (Z x)) x (X x)
        + d% (fun x ↦ inner ℝ (Z x) (X x)) x (Y x)
        - d% (fun x ↦ inner ℝ (X x) (Y x)) x (Z x)
        - inner ℝ (Y x) (mlieBracket I X Z x)
        - inner ℝ (Z x) (mlieBracket I Y X x)
        + inner ℝ (X x) (mlieBracket I Z Y x)) / 2 :=
  CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (M := M) hX hY hZ

/-- **`lcConn` is compatible with the metric**, in the challenge's sense
(`LeanEval.Geometry.SphereTheorem.IsMetricCompatible`), which is the form the areas `CH` and
`CURV` consume: for globally `C^∞` fields `Y`, `Z` and any `v : TangentSpace I x`,

`v ⟪Y,Z⟫ = ⟪∇_v Y, Z⟫ + ⟪Y, ∇_v Z⟫`.

This is proved directly from `lcConn_apply_inner`: adding the Koszul identities for the triples
`(X,Y,Z)` and `(X,Z,Y)`, the three bracket terms cancel in pairs (`mlieBracket_swap`) and the
middle derivative terms cancel in pairs (`real_inner_comm`), leaving exactly twice
`X⟪Y,Z⟫ / 2`. -/
theorem lcConn_compat :
    LeanEval.Geometry.SphereTheorem.IsMetricCompatible (lcConn (I := I) (M := M)) := by
  intro Y Z hY hZ x v
  have hY' : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  set Xv : Π x : M, TangentSpace I x := FiberBundle.extend E v with hXv
  have hX' : MDiffAt (T% Xv) x := by
    rw [hXv]; exact FiberBundle.mdifferentiableAt_extend (I := I) (F := E) v
  have hXxv : Xv x = v := FiberBundle.extend_apply_self E v
  have k1 := lcConn_apply_inner (I := I) (M := M) (X := Xv) (Y := Y) (Z := Z) hX' hY' hZ'
  have k2 := lcConn_apply_inner (I := I) (M := M) (X := Xv) (Y := Z) (Z := Y) hX' hZ' hY'
  rw [hXxv] at k1 k2
  -- align the derivative terms of the second Koszul identity with those of the first
  have eC : (fun x' : M ↦ inner ℝ (Z x') (Y x')) = fun x' : M ↦ inner ℝ (Y x') (Z x') :=
    funext fun x' ↦ real_inner_comm _ _
  have eA : (fun x' : M ↦ inner ℝ (Xv x') (Z x')) = fun x' : M ↦ inner ℝ (Z x') (Xv x') :=
    funext fun x' ↦ real_inner_comm _ _
  have eB : (fun x' : M ↦ inner ℝ (Xv x') (Y x')) = fun x' : M ↦ inner ℝ (Y x') (Xv x') :=
    funext fun x' ↦ real_inner_comm _ _
  rw [eC, eA, ← eB] at k2
  -- cancel the three bracket terms in pairs
  rw [mlieBracket_swap (V := Xv) (W := Z), mlieBracket_swap (V := Y) (W := Xv),
    mlieBracket_swap (V := Z) (W := Y)] at k1
  simp only [Pi.neg_apply, inner_neg_right] at k1
  rw [real_inner_comm (Y x) (lcConn (I := I) (M := M) Z x v)] at k2
  linarith [k1, k2]

end

end Work.LeviCivita
