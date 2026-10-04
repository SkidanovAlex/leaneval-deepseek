import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.D.Galerkin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer D: every element of the Galerkin space is a symmetric section

`Work.Diff.STE.D.genMap D ε c` is the coefficient-to-section map of the Galerkin scheme,

  `genMap D ε c = Σ_z c z • jSym D ε z`,

where `jSym D ε z = jFamily D ε z + jFamily D ε (idxSwap z)` is the *symmetrisation* of the
spanning vector `jFamily D ε z` of the range of the Friedrichs mollifier `J ρ ε`.

The content of this file is that the symmetrisation really works: each `jSym D ε z` is a symmetric
section (`jSym_symm`), hence so is every finite linear combination of them (`isSymm_genMap`).
This is what makes the Galerkin ODE `c' = ψ(c)` a flow on symmetric sections.

The key pointwise computation (`jVec_symm`) is that the elementary form
`jVec D ε i a b q = (jWgt · modeFun) • (e_i^a ♭ ⊗ e_i^b ♭)` is the *transpose* of
`jVec D ε i b a q`: exchanging the two frame indices exchanges the two arguments.
-/

namespace Work.Diff.STE.D

set_option autoImplicit false

/-- **Transposition of the elementary forms.**  The spanning vector at the frame indices `(a,b)` is
the transpose of the spanning vector at the frame indices `(b,a)`: pointwise the bilinear form is
`c · ⟪e_a, X⟫ · ⟪e_b, Y⟫` with the scalar `c = jWgt · modeFun` independent of the frame indices, so
exchanging `a b` and the two arguments leaves it unchanged. -/
lemma jVec_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E))
    (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε) (p : M) (X Y : TangentSpace I p) :
    Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q p X Y
      = Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i b a q p Y X := by
  simp only [Work.Diff.STE.B3.jVec, Work.Diff.STE.B3.jWgt, Work.Diff.STE.B3.jForm,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  ring

/-- **The symmetrised spanning family is symmetric.**  `jSym D ε z` is `jFamily D ε z` plus its
transpose (`jFamily D ε (idxSwap z)`), hence a symmetric section. -/
lemma jSym_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.D.IsSymm (I := I) (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) := by
  obtain ⟨i, a, b, q⟩ := z
  intro p X Y
  simp only [Work.Diff.STE.D.jSym, Work.Diff.STE.B3.jFamily, Work.Diff.STE.D.idxSwap_apply,
    Pi.add_apply, add_apply]
  rw [jVec_symm D ε i a b q p X Y, jVec_symm D ε i b a q p X Y]
  ring

theorem isSymm_genMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.IsSymm (I := I)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) := by
  intro p X Y
  simp only [Work.Diff.STE.D.genMap, Finset.sum_apply, Pi.smul_apply, smul_apply, sum_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [jSym_symm D ε z p X Y]

end Work.Diff.STE.D
