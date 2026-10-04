/-
# Joint smoothness of the coefficient/coordinate jets of the Galerkin family

The pair of spatial `2`-jets

  `W (c, y) = jetPairOf g₀ D ε x₀ c (flatToE x₀ y)`

is *affine* in the coefficients `c` (`Work.Diff.STE.D.psi.jetPairOf_eq_pair`): its first
(background) component is the chart jet of `g₀` and is independent of `c`, and its second
component is that same chart jet plus the finite linear combination

  `Σ_z c z • (chart jet of the spanning vector jSym D ε z)`.

Since `flatToE x₀` is `C^∞` and the chart `2`-jet of a section with smooth chart matrix is `C^∞`
in the chart coordinate (`Work.Diff.STE.D.psi.contDiffOn_chartJetOf`), the whole expression is
`C^∞` in the pair `(c, y)` on the set where `flatToE x₀ y` stays in the chart target.  This is
what this module records: the abstract form
(`Work.Diff.STE.D.psi.contDiffOn_affine_combination`, affine dependence on a finite-dimensional
coefficient vector and smooth dependence on the chart coordinate), and its instantiation for the
jet pair of the Galerkin family.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.JetAffine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set

namespace Work.Diff.STE.D.psi

/-- **Affine dependence on the coefficients.**  If `A` and the `B z` are `C^∞` functions of the
chart coordinate `y` on the set `T`, then

  `(c, y) ↦ (A y, A y + Σ_z c z • B z y)`

is `C^∞` on the set of pairs whose chart coordinate lies in `T`.  No closedness, openness or
non-emptiness assumption on `T` is needed: `ContDiffOn` only constrains the behaviour *inside*
`T`. -/
lemma contDiffOn_affine_combination
    {ι : Type*} [Fintype ι] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : P → Y) (B : ι → P → Y) (T : Set P)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A T)
    (hB : ∀ z, ContDiffOn ℝ (⊤ : ℕ∞) (B z) T) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (ι → ℝ) × P => (A q.2, A q.2 + ∑ z, q.1 z • B z q.2))
      {q | q.2 ∈ T} := by
  have hEval : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ι → ℝ) × P => q.2) {q | q.2 ∈ T} :=
    contDiff_snd.contDiffOn
  have hA' : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ι → ℝ) × P => A q.2) {q | q.2 ∈ T} :=
    hA.comp hEval (fun q hq => hq)
  have hB' (z : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ι → ℝ) × P => B z q.2) {q | q.2 ∈ T} :=
    (hB z).comp hEval (fun q hq => hq)
  have hc (z : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ι → ℝ) × P => q.1 z) {q | q.2 ∈ T} := by
    have hclm : (fun q : (ι → ℝ) × P => q.1 z) =
        ((ContinuousLinearMap.proj z : (ι → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.fst ℝ (ι → ℝ) P)) := rfl
    rw [hclm]
    exact (ContinuousLinearMap.contDiff _).contDiffOn
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (ι → ℝ) × P => ∑ z, q.1 z • B z q.2) {q | q.2 ∈ T} := by
    have h := ContDiffOn.sum (s := Finset.univ) (t := {q : (ι → ℝ) × P | q.2 ∈ T})
      (f := fun z q => q.1 z • B z q.2) (fun z _ => (hc z).smul (hB' z))
    simpa using h
  exact hA'.prodMk (hA'.add hsum)

/-- **The joint jet pair of the Galerkin family is `C^∞`** on the set of coefficient vectors and
chart coordinates for which the chart coordinate stays inside the target of the chart at `x₀`. -/
theorem contDiffOn_joint_jetPairOf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ q.1
          (Work.Diff.STE.flatToE (I := I) x₀ q.2))
      {q : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
          (Fin (Module.finrank ℝ E) → ℝ) |
        Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} := by
  classical
  have hgen := contDiffOn_affine_combination
    (ι := Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (P := Fin (Module.finrank ℝ E) → ℝ)
    (Y := Work.Diff.STE.D.psi.Tri (E := E))
    (A := fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀
        (Work.Diff.STE.flatToE (I := I) x₀ y))
    (B := fun z y => Work.Diff.STE.D.chartJetOf (I := I) (M := M)
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀
      (Work.Diff.STE.flatToE (I := I) x₀ y))
    (T := {y : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target})
    (contDiffOn_chartJetOf_inner_flatToE (I := I) (M := M) hg x₀)
    (fun z => contDiffOn_chartJetOf_jSym_flatToE (I := I) (M := M) D x₀ z)
  refine hgen.congr (fun q hq => ?_)
  exact Work.Diff.STE.D.psi.jetPairOf_eq_pair (I := I) (M := M) hg D x₀ q.1 hq

end Work.Diff.STE.D.psi
