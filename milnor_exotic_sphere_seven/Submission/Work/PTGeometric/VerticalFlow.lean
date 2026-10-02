import Submission.Work.PTGeometric.Defs
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the vertical flow of a `LocalCoreTarget`, and G3

The perturbation step of the Pontryagin–Thom construction (G3 of the project lead's blueprint) makes a
smooth map `F : M → E`, already transverse to the core near the boundary, transverse *everywhere*, by
translating it in the **normal** direction of the core and applying the parametric Sard theorem.

`Work.PTGeometric.VerticalFlow X` records exactly the translation data needed: for each local
trivialisation `i` of the normal bundle of the core, a partial map `Ψ i : E × ℝ^k → E` translating a
point of `E` by the amount `t` in the normal direction, with the **exact identity**

`Phi i (Ψ i y t) = Phi i y + t`

on the open set `valid i` where it is defined and smooth, the identity outside `valid i`, and a *box*
around every point of the core on which it is available for all small amounts and stays inside
`locU i` (`VerticalFlow.box`).

Mathematically this is the tubular structure of the zero section — for the genuine target
`E = {(P, v) : P ∈ Gr_k(ℝⁿ), v ∈ im P}` it is `(P, v) ↦ (P, v + frame_i(P) s)` in a chart `i` of the
Grassmannian.  It is *not* a consequence of the local defining functions alone (a local submersion has
no canonical inverse), which is why it is an input of `LocalTransversalApproximation` rather than a
field of `LocalCoreTarget`.

The main result of the file is the statement of G3, `LocalTransversalApproximation`: a smooth `F`
transverse to the core on a neighbourhood of `∂M` is homotopic — in fact equal on a neighbourhood of
`∂M` — to a smooth map transverse to the core everywhere.  Its proof is
`Work.PTGeometric.ptPerturbation`.

## Main definitions

* `Work.PTGeometric.VerticalFlow`
* `Work.PTGeometric.LocalTransversalApproximation` — G3, as a named `Prop`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-- **The vertical (normal) translations of a `LocalCoreTarget`.**

For each local trivialisation `i` of the normal bundle of the core, `Ψ i` translates a point of `E` in
the normal direction by the amount `t`:

* `valid i` is the open set of pairs `(y, t)` on which `Ψ i` satisfies the *exact* identity
  `Phi i (Ψ i y t) = Phi i y + t`;
* `Ψ i` is **globally** smooth (`contMDiff` — this is what the gadget iteration of the
  Transversality chapter produces) and the amount `0` gives back the point (`zero_apply`);
* `box` is the local availability: at every point `y` of the core, in a trivialisation `i` containing
  it, there is a box `W ∋ y` (inside `locU i`) and a radius `δ > 0` such that for `y' ∈ W` and
  `‖t‖ ≤ δ` the pair is in `valid i` and the translated point is still in `locU i`. -/
structure VerticalFlow (X : LocalCoreTarget n k) where
  /-- the vertical translation of the trivialisation `i`, applied to a point of `E` -/
  Ψ : X.locIx → X.E → EuclideanSpace ℝ (Fin k) → X.E
  /-- it is **globally** `C^∞` (the gadget iteration produces such a map) -/
  contMDiff : ∀ i : X.locIx, ContMDiff ((𝓡 n).prod (𝓡 k)) (𝓡 n) ∞
    (fun p : X.E × EuclideanSpace ℝ (Fin k) => Ψ i p.1 p.2)
  /-- the open set of pairs on which it satisfies the exact identity -/
  valid : X.locIx → Set (X.E × EuclideanSpace ℝ (Fin k))
  /-- it is open -/
  isOpen_valid : ∀ i : X.locIx, IsOpen (valid i)
  /-- the amount `0` gives back the point -/
  zero_apply : ∀ (i : X.locIx) (y : X.E), Ψ i y 0 = y
  /-- **the exact vertical translation in the trivialisation `i`** -/
  Phi_apply : ∀ (i : X.locIx) (y : X.E) (t : EuclideanSpace ℝ (Fin k)),
    (y, t) ∈ valid i → X.Phi i (Ψ i y t) = X.Phi i y + t
  /-- **local availability**: a box at every point of the core, in the trivialisations containing it,
  on which the translation is valid for all small amounts and stays in the trivialisation -/
  box : ∀ (i : X.locIx) (y : X.E), y ∈ X.locU i → X.Phi i y = 0 →
    ∃ (W : Set X.E) (δ : ℝ), IsOpen W ∧ y ∈ W ∧ 0 < δ ∧ W ⊆ X.locU i ∧
      ∀ y' ∈ W, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ ≤ δ →
        (y', t) ∈ valid i ∧ Ψ i y' t ∈ X.locU i

/-- **The local transversality (perturbation) theorem** — G3 of the blueprint, as a named `Prop`.

For a compact `T2` smooth `(9+k)`-manifold `M` with boundary, a `LocalCoreTarget` `X` carrying a
vertical flow (the tubular structure of the core) and a smooth `F : M → X.E` which is transverse to
the core on a *neighbourhood of the boundary*, there is a smooth `F' : M → X.E` which is transverse to
the core everywhere and agrees with `F` on a neighbourhood of `∂M`.

The proof is the one of `Work.ThomBordism.Transversality.TransversalApproximation` (proved for a
`CoreTarget`, i.e. for a globally trivial normal bundle), with the global `Φ ∘ F` replaced by the
local defining functions: the set of points where `F` is not yet transverse is compact, the vertical
flow gives a chart `i` and a box at each of its points, and the parametric Sard theorem
`Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero` — applied to
`Phi i ∘ F` with a cut-off supported in the box — produces a parameter `t` outside a null set for
which the perturbed map `x ↦ Ψ i (F x) (χ x • t)` is transverse at every point at which it meets the
core; iterating over the finitely many charts of a cover of the (compact) bad set terminates. -/
def LocalTransversalApproximation : Prop :=
  ∀ (n k : ℕ) (X : LocalCoreTarget n k), Nonempty (VerticalFlow X) →
  ∀ (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M] (F : M → X.E),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 n) ∞ F →
    IsCoreTransverseNearBoundary X F →
      ∃ F' : M → X.E,
        ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 n) ∞ F' ∧
        IsCoreTransverse X (𝓡∂ ((8 + k) + 1)) F' ∧
        ∃ U : Set M, (𝓡∂ ((8 + k) + 1)).boundary M ⊆ U ∧ IsOpen U ∧ ∀ x ∈ U, F' x = F x

/-- **Transversality to the core is an open condition in the source.**

The set of points at which `F` is transverse to the core is the union of `{F x ∉ core}` (open, the core
being closed) with, over the local trivialisations, `{F x ∈ locU i} ∩ {Phi i ∘ F submersive at x}`
(open: `Matrix`-free, `IsSubmersionAt` is a local condition in `x`). -/
theorem isOpen_setOf_isCoreTransverseAt (X : LocalCoreTarget n k) {E' : Type*} {H : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : M → X.E} (hF : Continuous F) :
    IsOpen {x : M | IsCoreTransverseAt X I F x} := by
  have h1 : IsOpen {x : M | F x ∉ X.core} := X.isClosed_core.isOpen_compl.preimage hF
  have h2 : ∀ i : X.locIx, IsOpen ({x : M | F x ∈ X.locU i} ∩
      {x : M | IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Phi i (F y)) x}) :=
    fun i => ((X.isOpen_locU i).preimage hF).inter isOpen_isSubmersionAt
  have h_eq : {x : M | IsCoreTransverseAt X I F x} =
      {x : M | F x ∉ X.core} ∪ ⋃ i, ({x : M | F x ∈ X.locU i} ∩
        {x : M | IsSubmersionAt I (𝓡 k) ∞ (fun y => X.Phi i (F y)) x}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases hx : F x ∈ X.core
      · obtain ⟨i, hi, hsub⟩ := h hx
        exact Or.inr ⟨i, hi, hsub⟩
      · exact Or.inl hx
    · rintro (hx | ⟨i, hi, hsub⟩)
      · exact fun hc => absurd hc hx
      · exact fun _ => ⟨i, hi, hsub⟩
  rw [h_eq]
  exact h1.union (isOpen_iUnion h2)

/-- **Transversality on a set extends to a neighbourhood of it** (the set of transverse points being
open, `isOpen_setOf_isCoreTransverseAt`). -/
theorem IsCoreTransverseOn.exists_isOpen_superset (X : LocalCoreTarget n k) {E' : Type*} {H : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : M → X.E} (hF : Continuous F)
    {A : Set M} (h : IsCoreTransverseOn X I F A) :
    ∃ U : Set M, A ⊆ U ∧ IsOpen U ∧ IsCoreTransverseOn X I F U :=
  ⟨{x : M | IsCoreTransverseAt X I F x}, h, isOpen_setOf_isCoreTransverseAt X I hF, fun _ hx => hx⟩

end

end Work.PTGeometric
