import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

/-- A smooth cut-off times a locally smooth map is smooth: if `φ : M → ℝ` is `C^n` and `f : M → E'`
is `C^n` on an open set `s`, and the topological support of `φ` is contained in `s`, then
`x ↦ φ x • f x` is `C^n`. -/
theorem contMDiff_smul_of_contMDiffOn_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {φ : M → ℝ} {f : M → E'} {s : Set M} {n : WithTop ℕ∞}
    (hs : IsOpen s) (hφ : ContMDiff I (modelWithCornersSelf ℝ ℝ) n φ)
    (hf : ContMDiffOn I (modelWithCornersSelf ℝ E') n f s)
    (hsub : tsupport φ ⊆ s) :
    ContMDiff I (modelWithCornersSelf ℝ E') n (fun x => φ x • f x) := by
  -- On `s` both factors are smooth, so the product is.
  have hsmul : ContMDiffOn I (modelWithCornersSelf ℝ E') n (fun x => φ x • f x) s :=
    hφ.contMDiffOn.smul hf
  -- Outside the (closed) support of `φ`, the function `φ • f` vanishes.
  have hzero : ContMDiffOn I (modelWithCornersSelf ℝ E') n (fun x => φ x • f x) (tsupport φ)ᶜ := by
    refine (contMDiffOn_const (I := I) (I' := modelWithCornersSelf ℝ E') (n := n)
      (c := (0 : E')) (s := (tsupport φ)ᶜ)).congr (fun y hy => ?_)
    simp [image_eq_zero_of_notMem_tsupport hy]
  -- `s` and the complement of the support are open and cover `M`.
  refine contMDiff_of_contMDiffOn_union_of_isOpen hsmul hzero ?_ hs
    (isClosed_tsupport φ).isOpen_compl
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ s
  · exact Or.inl hx
  · exact Or.inr fun h => hx (hsub h)

end Work.PTGeometric
