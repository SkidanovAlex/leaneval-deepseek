import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.V_open_one

namespace Work.EKLComp

/-- The displacement neighbourhoods `V δ` of the identity form a neighbourhood basis of `1` in
`SL₃(ℝ)`.

`SL₃(ℝ) = {A : Mat₃(ℝ) | det A = 1}` carries the subspace topology of the product topology on
`Mat₃(ℝ) ≅ ℝ^{3×3}`, and `V δ = {A | ∀ i j, |A i j - (1) i j| < δ}` is the box of matrices whose
entries are within `δ` of the corresponding entries of the identity matrix.  On a finite product
of copies of `ℝ` the sup-metric balls with centre `(1) i j` are exactly these boxes, so the family
`{V δ}_{δ>0}` is a neighbourhood basis. -/
lemma V_hasBasis_nhds_one :
    (nhds (1 : Work.EKLContract.SL3)).HasBasis (fun δ : ℝ => 0 < δ) Work.EKLContract.V := by
  -- The identity matrix viewed as a function `Fin 3 → Fin 3 → ℝ`.
  let m1 : Fin 3 → Fin 3 → ℝ := (1 : Matrix (Fin 3) (Fin 3) ℝ)
  -- On the Pi type `ℝ^{3×3}` the sup-metric balls around the identity matrix are exactly the
  -- boxes appearing in the definition of `V`.
  have hfun : (nhds m1).HasBasis (fun δ : ℝ => 0 < δ)
      (fun δ => {A : Fin 3 → Fin 3 → ℝ | ∀ i j, |A i j - m1 i j| < δ}) := by
    refine (Metric.nhds_basis_ball (x := m1)).congr (fun δ => Iff.rfl) (fun δ hδ => ?_)
    ext A
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    simp only [dist_pi_lt_iff hδ, Real.dist_eq]
    exact Iff.rfl
  -- Transport to the matrix type: same points (definitionally), same topology.
  have hmat : (nhds (1 : Matrix (Fin 3) (Fin 3) ℝ)).HasBasis (fun δ : ℝ => 0 < δ)
      (fun δ => {A : Matrix (Fin 3) (Fin 3) ℝ |
        ∀ i j, |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ}) := hfun
  -- `SL₃(ℝ)` is the topological subspace of matrices with determinant `1`.
  have hnh : nhds (1 : Work.EKLContract.SL3) =
      Filter.comap (Subtype.val : Work.EKLContract.SL3 → Matrix (Fin 3) (Fin 3) ℝ)
        (nhds (↑(1 : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) :=
    nhds_subtype ({A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1}) (1 : Work.EKLContract.SL3)
  rw [hnh]
  -- Pull the basis back along `SL₃(ℝ) → Mat₃(ℝ)`: the preimage is `V δ` by definition.
  refine (hmat.comap (Subtype.val : Work.EKLContract.SL3 → Matrix (Fin 3) (Fin 3) ℝ)).to_hasBasis
    (fun i hi => ⟨i, hi, ?_⟩) (fun i hi => ⟨i, hi, ?_⟩)
  · intro g hg; exact hg
  · intro g hg; exact hg

end Work.EKLComp
