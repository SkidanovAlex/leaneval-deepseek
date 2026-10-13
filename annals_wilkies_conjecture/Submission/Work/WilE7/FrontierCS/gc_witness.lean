/-
  WilE7 / CS-slice, node **N5 pointwise form** (`gc_witness`).

  The `grid_cover` node produces, for `τ` near `0`, a Boolean matrix `b` with
  `(τ, 0) ∈ closure (sliceSet G W (sliceChart γ B (gridMat b)))`.  This file proves the
  *pointwise* form of the underlying linear-algebra/calculus step, valid at an arbitrary point
  `q = (τ, e)` of the ambient space rather than only on the zero slice: if `γ q.1 + B q.2 ∈ W`,
  `fderiv ℝ G` is surjective at that point, and the straight chart
  `(t,e) ↦ γ t + B e` has surjective derivative at `q.1`, then some grid chart `sliceChart γ B Λ`
  already puts the point `(q.1 - Λ q.2, q.2)` into `sliceSet G W`.

  Why this is the right statement.  `sliceChart γ B Λ (q.1 - Λ q.2, q.2) = γ q.1 + B q.2`, so the
  first half of the slice condition is automatic; the second half asks for surjectivity of

      `e ↦ fderiv ℝ G w ∘ (fderiv ℝ γ q.1 ∘ Λ + B)`,

  `w = γ q.1 + B q.2`.  Writing `F = fderiv ℝ G w` and `A = fderiv ℝ γ q.1`, the composite is
  surjective as soon as `F ∘ (A ∘ Λ + B)` is, and its matrix is `mat F * mat A * Λ + mat F * mat B`
  (`mat_comp_add_matCLM`).  Since `(t,e) ↦ A t + B e` is surjective and `F` is surjective, the pair
  `(mat F * mat A, mat F * mat B)` satisfies the hypothesis `hsurj` of the grid lemma N2
  (`exists_grid_det_ne_zero`), which supplies the `0/1` matrix `b` making the determinant nonzero.

  So the mathematical content of `grid_cover` that is not pure topology is now just N2 plus one
  chain-rule computation; the file records both as reusable lemmas
  (`fderiv_sliceChart_snd`, `sliceDeriv_surj_grid`).
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.gc_defs
import Submission.Work.WilE7.FrontierCS.exists_grid_det_ne_zero

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-! ## The chain rule for the slice chart -/

/-- Derivative of `e' ↦ G (sliceChart γ B Λ (t, e'))`: the chain rule for
`e' ↦ γ (t + Λ e') + B e'` followed by `G`.  The derivative of the inner map at `e` is
`fderiv ℝ γ (t + Λ e) ∘ Λ + B`. -/
lemma fderiv_sliceChart_snd {N d j : ℕ} {G : (Fin N → ℝ) → (Fin j → ℝ)}
    {γ : (Fin d → ℝ) → (Fin N → ℝ)} (hG : AnalyticOnNhd ℝ G Set.univ)
    (hγ : AnalyticOnNhd ℝ γ Set.univ) (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ))
    (Λ : Matrix (Fin d) (Fin j) ℝ) (t : Fin d → ℝ) (e : Fin j → ℝ) :
    fderiv ℝ (fun e' : Fin j → ℝ => G (sliceChart γ B Λ (t, e'))) e =
      (fderiv ℝ G (sliceChart γ B Λ (t, e))).comp
        ((fderiv ℝ γ (t + Λ.mulVec e)).comp (matCLM Λ) + B) := by
  have h1 : HasFDerivAt (fun e' : Fin j → ℝ => t + Λ.mulVec e') (matCLM Λ) e :=
    (matCLM Λ).hasFDerivAt.const_add t
  have h2 : HasFDerivAt γ (fderiv ℝ γ (t + Λ.mulVec e)) (t + Λ.mulVec e) :=
    (hγ _ (Set.mem_univ _)).hasStrictFDerivAt.hasFDerivAt
  have h3 : HasFDerivAt (fun e' : Fin j → ℝ => B e') B e := B.hasFDerivAt
  have h4 : HasFDerivAt (fun e' : Fin j → ℝ => γ (t + Λ.mulVec e') + B e')
      ((fderiv ℝ γ (t + Λ.mulVec e)).comp (matCLM Λ) + B) e :=
    (h2.comp e h1).add h3
  have h5 : HasFDerivAt G (fderiv ℝ G (sliceChart γ B Λ (t, e))) (sliceChart γ B Λ (t, e)) :=
    (hG _ (Set.mem_univ _)).hasStrictFDerivAt.hasFDerivAt
  exact (h5.comp e h4).fderiv

/-! ## Surjectivity transfer to the grid matrices -/

/-- If `fderiv ℝ G` is surjective at `γ q.1 + B q.2` and the straight chart
`(t,e) ↦ fderiv ℝ γ q.1 t + B e` is surjective at `q.1`, then the pair of matrices
`(mat F * mat A, mat F * mat B)` (with `F = fderiv ℝ G (γ q.1 + B q.2)`, `A = fderiv ℝ γ q.1`)
satisfies the hypothesis of the grid lemma `exists_grid_det_ne_zero`: every `y` is hit by
`(mat F * mat A) t + (mat F * mat B) e`. -/
lemma sliceDeriv_surj_grid {N d j : ℕ} {G : (Fin N → ℝ) → (Fin j → ℝ)} {W : Set (Fin N → ℝ)}
    {γ : (Fin d → ℝ) → (Fin N → ℝ)} {B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)}
    {q : (Fin d → ℝ) × (Fin j → ℝ)}
    (hWrk : ∀ w ∈ W, (fderiv ℝ G w).range = ⊤) (hWq : γ q.1 + B q.2 ∈ W)
    (hT : (sliceDeriv γ B q.1).range = ⊤) :
    ∀ y : Fin j → ℝ, ∃ t : Fin d → ℝ, ∃ e : Fin j → ℝ,
      (mat (fderiv ℝ G (γ q.1 + B q.2)) * mat (fderiv ℝ γ q.1)).mulVec t +
      (mat (fderiv ℝ G (γ q.1 + B q.2)) * mat B).mulVec e = y := by
  intro y
  have hFs : Function.Surjective (fderiv ℝ G (γ q.1 + B q.2)) :=
    LinearMap.range_eq_top.mp (hWrk _ hWq)
  have hTs : Function.Surjective (sliceDeriv γ B q.1) := LinearMap.range_eq_top.mp hT
  obtain ⟨z, hz⟩ := hFs y
  obtain ⟨p, hp⟩ := hTs z
  refine ⟨p.1, p.2, ?_⟩
  have hp' : fderiv ℝ γ q.1 p.1 + B p.2 = z := by
    simpa [sliceDeriv_apply] using hp
  rw [← mat_comp (fderiv ℝ G (γ q.1 + B q.2)) (fderiv ℝ γ q.1),
      ← mat_comp (fderiv ℝ G (γ q.1 + B q.2)) B, mat_mulVec, mat_mulVec]
  show fderiv ℝ G (γ q.1 + B q.2) (fderiv ℝ γ q.1 p.1) +
      fderiv ℝ G (γ q.1 + B q.2) (B p.2) = y
  rw [← map_add, hp', hz]

/-! ## The pointwise grid witness -/

/-- **N5, pointwise.**  At a point `q` with `γ q.1 + B q.2 ∈ W` where `fderiv ℝ G` is surjective and
the straight chart has surjective derivative at `q.1`, some grid chart puts `(q.1 - Λ q.2, q.2)`
into the slice set. -/
theorem gc_witness {N d j : ℕ} {G : (Fin N → ℝ) → (Fin j → ℝ)}
    (hG : AnalyticOnNhd ℝ G Set.univ) {W : Set (Fin N → ℝ)}
    (hWrk : ∀ w ∈ W, (fderiv ℝ G w).range = ⊤)
    {γ : (Fin d → ℝ) → (Fin N → ℝ)} (hγ : AnalyticOnNhd ℝ γ Set.univ)
    {B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)} {q : (Fin d → ℝ) × (Fin j → ℝ)}
    (hWq : γ q.1 + B q.2 ∈ W)
    (hT : (Work.WilE7.FrontierCS.sliceDeriv γ B q.1).range = ⊤) :
    ∃ b : Fin d → Fin j → Bool,
      (q.1 - (Work.WilE7.FrontierCS.gridMat b).mulVec q.2, q.2) ∈
        Work.WilE7.FrontierCS.sliceSet G W
          (Work.WilE7.FrontierCS.sliceChart γ B (Work.WilE7.FrontierCS.gridMat b)) := by
  obtain ⟨b, hb⟩ := exists_grid_det_ne_zero
    (mat (fderiv ℝ G (γ q.1 + B q.2)) * mat (fderiv ℝ γ q.1))
    (mat (fderiv ℝ G (γ q.1 + B q.2)) * mat B) (sliceDeriv_surj_grid hWrk hWq hT)
  refine ⟨b, ?_, ?_⟩
  · -- the chart value is `γ q.1 + B q.2`, which lies in `W`
    show sliceChart γ B (gridMat b) (q.1 - (gridMat b).mulVec q.2, q.2) ∈ W
    have h : (q.1 - (gridMat b).mulVec q.2) + (gridMat b).mulVec q.2 = q.1 :=
      sub_add_cancel _ _
    simp only [sliceChart, h]
    exact hWq
  · -- the slice Jacobian is `F ∘ (A ∘ Λ + B)`, surjective by the grid lemma
    show (fderiv ℝ (fun e' : Fin j → ℝ =>
      G (sliceChart γ B (gridMat b) (q.1 - (gridMat b).mulVec q.2, e'))) q.2).range = ⊤
    rw [fderiv_sliceChart_snd hG hγ B (gridMat b) (q.1 - (gridMat b).mulVec q.2) q.2]
    have h : (q.1 - (gridMat b).mulVec q.2) + (gridMat b).mulVec q.2 = q.1 :=
      sub_add_cancel _ _
    have hp : sliceChart γ B (gridMat b) (q.1 - (gridMat b).mulVec q.2, q.2) =
        γ q.1 + B q.2 := by
      simp only [sliceChart, h]
    rw [hp, h]
    exact range_top_of_mat_det_ne_zero _
      (by rw [mat_comp_add_matCLM]; exact hb)

end Work.WilE7.FrontierCS
