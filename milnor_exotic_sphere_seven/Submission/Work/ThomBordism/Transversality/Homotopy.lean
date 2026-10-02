import Submission.Work.ThomBordism.Transversality.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The transversality homotopy theorem

This file contains item 2 (first half) of the **Transversality** chapter: the statement that a smooth
map from a compact manifold with boundary into a `CoreTarget`, already transverse to the core near
the boundary, can be homotoped (relative to the boundary) to one transverse to the core everywhere.

## The statement

`Work.ThomBordism.Transversality.TransversalApproximation` is the theorem, in the exact form in
which the chapter uses it:

> for every compact `T2` smooth manifold `M` (modelled on `I`) with boundary, every `CoreTarget`
> `X`, and every `F : M → X.E` which is `C^∞` and transverse to the core on a neighbourhood of
> `∂M`, there are `F' : M → X.E`, `C^∞` and transverse to the core everywhere, and a `C^∞` homotopy
> `H : M × ℝ → X.E` from `F` to `F'` which is constant on `∂M`.

It is stated as a named `Prop` and is **proved**: see
`Work.ThomBordism.Transversality.TransversalApproximation.transversalApproximation`
(`TransversalApproximation/transversalApproximation.lean`, axioms ⊆
`{propext, Classical.choice, Quot.sound}`), whose analytic half is
`Work.ThomBordism.Transversality.TransverseSard.regularValue_ae` (Sard's theorem in the rectangular
case, `Sard/`, and the manifold-level parametric form) and whose realisation step is built through
the `VerticalFamily` interface (`TransversalApproximation/verticalFamily.lean`).  The unconditional
corollaries are `transversalApproximation_uncond` and `transversalApproximation_cylinder_uncond`
(`Unconditional.lean`).  `ParametricTransversality` below records the Sard-based parametric form
that is the standard route to the theorem.

## The case of the cylinder `Sⁿ × [0,1]`

`TransversalApproximation.cylinder` specialises the statement to `M × [0,1]` with `M` boundaryless
(the case named in the deliverable: `Sⁿ × [0,1]`, whose boundary `M × {0,1}` consists of the two
ends).

## Main definitions

* `Work.ThomBordism.Transversality.HomotopicRelBoundary`
* `Work.ThomBordism.Transversality.IsTransverseNearBoundary`
* `Work.ThomBordism.Transversality.TransversalApproximation`
* `Work.ThomBordism.Transversality.ParametricTransversality`
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality

noncomputable section

variable {n k : ℕ}

/-- **A smooth homotopy of maps `M → E`, relative to the boundary of `M`.**

`H : M × ℝ → E` is `C^∞`, `H (·, 0) = F`, `H (·, 1) = F'`, and `H (x, t) = F x` for every
`x ∈ ∂M` and every `t`.  (The homotopy is not required to be constant outside `[0,1]`; we only ever
use it on `[0,1]`, so no manifold with corners is needed on the parameter.) -/
def HomotopicRelBoundary {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) (X : CoreTarget n k) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (F F' : M → X.E) : Prop :=
  ∃ Hh : M × ℝ → X.E,
    ContMDiff (I.prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ Hh ∧
      (∀ x : M, Hh (x, 0) = F x) ∧ (∀ x : M, Hh (x, 1) = F' x) ∧
      (∀ x ∈ I.boundary M, ∀ t : ℝ, Hh (x, t) = F x)

theorem homotopicRelBoundary_refl {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) (X : CoreTarget n k) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {F : M → X.E}
    (hF : ContMDiff I (𝓡 n) ∞ F) : HomotopicRelBoundary I X F F :=
  ⟨fun p => F p.1, hF.comp contMDiff_fst, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- **`F` is transverse to the core near the boundary**: `F` is transverse to the core on some open
neighbourhood of `∂M`.  This is the hypothesis of the homotopy theorem. -/
def IsTransverseNearBoundary {E' : Type*} {H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) (X : CoreTarget n k) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] (F : M → X.E) : Prop :=
  ∃ U : Set M, I.boundary M ⊆ U ∧ IsOpen U ∧ IsTransverseOn X I F U

/-- Transversality on the boundary implies transversality near the boundary (for continuous
`Φ ∘ F`): `IsTransverseOn` on `∂M` is the same condition as `IsTransverseNearBoundary`. -/
theorem isTransverseNearBoundary_of_isTransverseOn_boundary {E' : Type*} {H : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E' H} {X : CoreTarget n k} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {F : M → X.E} (hF : Continuous fun y => X.Φ (F y))
    (h : IsTransverseOn X I F (I.boundary M)) : IsTransverseNearBoundary I X F := by
  obtain ⟨U, hU, hUopen, hUtr⟩ := h.exists_isOpen_superset I hF
  exact ⟨U, hU, hUopen, hUtr⟩

/-- **The transversality homotopy theorem** (item 2, first half of the chapter).

`M` is a compact `T2` smooth manifold with boundary, `X` a `CoreTarget` (the manifold part of the
Thom space of the universal oriented `k`-plane bundle, with its zero section as core), `F : M → X.E`
a `C^∞` map which is transverse to the core on a neighbourhood of `∂M`.  Then `F` is homotopic,
relative to `∂M`, to a map which is transverse to the core everywhere.

The proof (see `TransversalApproximation/` and §9.2 of the `README.md`) is the standard one: Sard's
theorem applied to the derivative of `Φ ∘ F` produces a regular value near `0`; a vertical
perturbation supported off `∂M` (built through the `VerticalFamily` interface) makes `Φ ∘ F'`
transverse to `0`, i.e. `F'` transverse to the core.  The statement below is the `Prop` itself; its
proof is the theorem of the same name in the namespace
`Work.ThomBordism.Transversality.TransversalApproximation`. -/
def TransversalApproximation : Prop :=
  ∀ (n k : ℕ) (E' : Type) (H : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) (X : CoreTarget n k) (M : Type) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] (F : M → X.E),
    ContMDiff I (𝓡 n) ∞ F → IsTransverseNearBoundary I X F →
      ∃ F' : M → X.E,
        ContMDiff I (𝓡 n) ∞ F' ∧ IsTransverse X I F' ∧ HomotopicRelBoundary I X F F'

/-- **Parametric transversality** (the Sard-based form of the input of item 2).

If a smooth family `H : M × P → E` is transverse to the core *as a map on the product* (with `M`
compact), then the set of parameters `p` for which the slice `H (·, p)` is transverse to the core is
dense in `P`: this is Sard's theorem applied to the (projection of the) critical set of `H`.

This is the standard route to `TransversalApproximation`, and the form in which the deliverable
allows item 1 to be replaced by "a parametric transversality theorem strong enough for 2". -/
def ParametricTransversality : Prop :=
  ∀ (n k p : ℕ) (E' : Type) (H : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) (X : CoreTarget n k) (M : Type) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    (P : Type) [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]
    (Hm : M × P → X.E),
    ContMDiff (I.prod (𝓡 p)) (𝓡 n) ∞ Hm → IsTransverseOn X (I.prod (𝓡 p)) Hm univ →
      Dense {q : P | IsTransverse X I (fun x => Hm (x, q))}

/-- **The boundary of the cylinder `M × [0,1]` is the two ends `M × {0}` and `M × {1}`.**

This is the concrete setting named in the deliverable: for `M` a compact boundaryless smooth
manifold (in the application `M = Sⁿ`) the domain `M × [0,1]`, modelled on
`(𝓡 n).prod (𝓡∂ 1)`, is a compact smooth manifold whose boundary consists of the two ends, and
`TransversalApproximation` applies to it verbatim, the homotopy being constant on the ends. -/
theorem boundary_cylinder {n : ℕ} (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ((𝓡 n).prod (𝓡∂ 1)).boundary (M × Icc (0 : ℝ) 1) = Set.prod univ {⊥, ⊤} :=
  boundary_product (𝓡 n)


/-- **The homotopy theorem for the cylinder `Sⁿ × [0,1]`** — the concrete form named in the
deliverable.

`M` is a compact boundaryless smooth `n`-manifold (in the application `M = Sⁿ`), the domain
`M × [0,1]` is modelled on `(𝓡 n).prod (𝓡∂ 1)` and its boundary is the two ends `M × {0}`,
`M × {1}` (`boundary_cylinder`).  A smooth map `F` from the cylinder into the manifold part of the
Thom space which is transverse to the zero section on a neighbourhood of the two ends is homotopic,
relative to the ends, to a map transverse to the zero section everywhere. -/
theorem transversalApproximation_cylinder (h : TransversalApproximation) {n k : ℕ}
    (X : CoreTarget (n + 1) k) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    [T2Space M] (F : M × Icc (0 : ℝ) 1 → X.E)
    (hF : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 (n + 1)) ∞ F)
    (htr : IsTransverseNearBoundary ((𝓡 n).prod (𝓡∂ 1)) X F) :
    ∃ F' : M × Icc (0 : ℝ) 1 → X.E,
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡 (n + 1)) ∞ F' ∧
        IsTransverse X ((𝓡 n).prod (𝓡∂ 1)) F' ∧
        HomotopicRelBoundary ((𝓡 n).prod (𝓡∂ 1)) X F F' :=
  h (n + 1) k _ _ ((𝓡 n).prod (𝓡∂ 1)) X (M × Icc (0 : ℝ) 1) F hF htr


/-- **`ParametricTransversality` in the form in which transversality arguments use it**: a transverse
slice exists (a regular value of the family). -/
theorem ParametricTransversality.exists_isTransverse (h : ParametricTransversality) {n k p : ℕ}
    {E' : Type} {H : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E' H} {X : CoreTarget n k} {M : Type} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    {P : Type} [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P] [Nonempty P]
    {Hm : M × P → X.E} (hHm : ContMDiff (I.prod (𝓡 p)) (𝓡 n) ∞ Hm)
    (htr : IsTransverseOn X (I.prod (𝓡 p)) Hm univ) :
    ∃ q : P, IsTransverse X I (fun x => Hm (x, q)) :=
  (h n k p E' H I X M P Hm hHm htr).nonempty


/-- **The conclusion of `TransversalApproximation` when the map is already transverse** (with the
constant homotopy): the theorem's conclusion is inhabited, and the hypothesis "transverse near the
boundary" is all that ever needs adjusting. -/
theorem exists_transverse_homotopic_self {E' : Type} {H : Type} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {X : CoreTarget n k}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {F : M → X.E}
    (hF : ContMDiff I (𝓡 n) ∞ F) (htr : IsTransverse X I F) :
    ∃ F' : M → X.E,
      ContMDiff I (𝓡 n) ∞ F' ∧ IsTransverse X I F' ∧ HomotopicRelBoundary I X F F' :=
  ⟨F, hF, htr, homotopicRelBoundary_refl I X hF⟩

end

end Work.ThomBordism.Transversality
