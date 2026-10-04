import Mathlib
import Submission.Work.OddBound.PolygonChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Design (revision 2): the mountain pass on the polygon space `P = Fin (N-1) → M`

The statement delegated in session 7 (`Work.OddBound.mountainPass.exists_critical_index_le_one_manifold`,
the module `design/MountainPassManifold.lean`) was **declared FALSE by its prover**, for a real reason
that this module records together with the repair.

## What was wrong

The old statement quantified over an arbitrary model-with-corners
`{I' : ModelWithCorners ℝ H' H'}` and assumed `[IsManifold I' 2 P]`.  Its proof — a port of the
*proved* Euclidean theorem `Work.OddBound.mountainPass.exists_critical_index_le_one` — must, in the
by-contra world, transfer the "no negative-definite plane" conclusion from the chart `e₀` supplied by
`hsm` to an *arbitrary* atlas chart `e₂` (because `¬ HasNegDefPlane` is a `∀`-charts statement).
The change-of-charts step needs the **second-order** chain rule for `f ∘ e₂.symm`, i.e. it needs the
transition `e₂ ∘ e₀.symm` to be `C²` in the **standard** sense (Euclidean on the model space `H'`).
`IsManifold I' 2 P` only gives that the transition is `C²` *in the `I'`-calculus*
(`I' ∘ (e₂ ∘ e₀.symm) ∘ I'.symm` is `C²`), which for a general model-with-corners `I'` is strictly
weaker and does not compose with the standard-`C²` hypothesis `ContDiffOn ℝ 2 (f ∘ e₀.symm)`.

## The repair

Pin the model to the **self model** `𝓘(ℝ, H')`:

* `IsManifold (𝓘(ℝ, H')) 2 P` says exactly that the atlas charts are **standard**-`C²`-compatible
  (`contDiffGroupoid 2 𝓘(ℝ, H')` is the groupoid of `C²` partial homeomorphisms of `H'`).
* Hence, from `hsm` at `z`, the chart expression `f ∘ e.symm` is `C²` at `e z` for **every** chart
  `e ∈ atlas H' P` with `z ∈ e.source` (compose with the standard-`C²` transition).
* The Hessian of `f` at a point is then a chart-independent quadratic form up to an invertible linear
  substitution, so "no negative-definite plane" transfers between charts exactly as in the Euclidean
  proof.

The application is planned for `H' := Fin (N-1) → E` (the product of the **extended** charts
`extChartAt I (w i) : M → E`, which are `E`-valued — the chart codomain must be a *normed* space for
`HasNegDefPlane` to make sense, and the `H`-valued `piChartedSpace` model is only a topological space).
`IsManifold 𝓘(ℝ, E) ∞ M` for the extended-chart structure follows from
`ContMDiffAt I 𝓘(ℝ,E) n (extChartAt I x)` and `ContMDiffOn 𝓘(ℝ,E) I n (extChartAt I x).symm`
(`Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean`), composed through the mixed-model chain rule; the
`Fin (N-1)`-product then follows from `Work.piManifold.isManifold_pi`, applied to that structure.

## The statement to prove

```lean
theorem exists_critical_index_le_one_manifold
    {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H'] [FiniteDimensional ℝ H']
    {P : Type*} [TopologicalSpace P] [T2Space P] [CompactSpace P]
    [ChartedSpace H' P] [IsManifold (𝓘(ℝ, H')) 2 P]
    {f : P → ℝ} (hf : Continuous f)
    (hsm : ∀ z : P, ∃ e : OpenPartialHomeomorph P H', e ∈ atlas H' P ∧ z ∈ e.source ∧
      ContDiffOn ℝ 2 (fun x : H' => f (e.symm x)) e.target)
    {a b : P} (hpath : ∃ σ : ℝ → P, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b)
    {Λ : ℝ}
    (hΛ : Λ = sInf {m : ℝ | ∃ σ : ℝ → P, ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = a ∧ σ 1 = b ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, f (σ t) ≤ m})
    (hlt : max (f a) (f b) < Λ) :
    ∃ z : P, f z = Λ ∧ Work.OddBound.IsCriticalChart H' f z ∧
      ¬ Work.OddBound.HasNegDefPlane H' f z
```

## Proof (port of the proved Euclidean theorem)

`Work.OddBound.mountainPass.exists_critical_index_le_one` is proved in
`Submission/Work/OddBound/mountainPass/exists_critical_index_le_one.lean`, with the local lemmas
`local_joinedIn_of_negDefPlane`, `local_joinedIn_of_fderiv_ne_zero` and the supporting
`taylor2_bound`, `hedge_negDef_local`, `exists_sublevel_near_of_negDefPlane`,
`isConnected_iInter_of_antitone`, `le_of_second_deriv_nonpos_along_segment`.  The port replaces:

1. the ambient Euclidean space by the chart image in `H'`: the local lemmas are applied to the
   `C²` function `fun x : H' => f (e.symm x)` at `e z` and transported along the chart homeomorphism
   `e` (a homeomorphism transports `JoinedIn` and sublevel sets);
2. Fermat's rule: proved in a chart from `z ∈ e.source`;
3. `convex_ball` path-connectedness: replaced by the local path-connectedness of the atlas images
   (a small Euclidean ball inside `e.target` pulls back to a path-connected neighbourhood);
4. `IsCompact {x | f x ≤ c}`: automatic from `P` compact and `f` continuous.

The local lemmas currently assume `[InnerProductSpace ℝ E]`; the model `H'` here is an arbitrary
finite-dimensional real normed space (the application is `Fin (N-1) → E` with the **sup** norm, which
is not induced by an inner product), so they must be generalised — their content (the second-order
Taylor expansion at the point, the negative cone `{Q < 0}`, the connectivity of
`{Q < 0} ∩ S^{n-1}` for a negative-definite plane) uses only the norm and finite dimension.
-/

namespace Work.OddBound

end Work.OddBound
