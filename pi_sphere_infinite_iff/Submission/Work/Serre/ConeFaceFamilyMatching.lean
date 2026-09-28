import Mathlib
import Submission.Work.Serre.E0ConeBdd

set_option maxHeartbeats 800000

namespace Work.Serre

/-- **The matching condition of `exists_simplexFiller` for the degree-`1` cone faces.**

For `s : Simp X 1` the family `coneFaceFamily H0 s : Fin 3 → C(Δ¹,X)` is the triangle boundary
with faces `H0 (δ₀ s)`, `H0 (δ₁ s)` and `s`.  The statement says that these three `1`-simplices
agree on the three vertices of `Δ²`, which is exactly the matching condition (`hx`) required by
`Work.Serre.exists_simplexFiller 0`:
`(x j).comp (coface 0 ⟨i.val, _⟩) = (x i).comp (coface 0 ⟨j.val - 1, _⟩)` for `i < j` in `Fin 3`.

Proof sketch: case on `i` and `j`; the three non-trivial cases are `(i,j) = (0,1), (0,2), (1,2)`.
After `simp only [Fin.val_castSucc, coneFaceFamily_castSucc, coneFaceFamily_last]` and the
conversions `rw [← concretize_face ...]` (or `Work.Serre.concretize_injective`), the cases reduce
respectively to `hconst0`, `hlast0`, `hlast0`.  Useful existing lemmas: `concretize_face`,
`concretize_injective`, `coneFaceFamily_castSucc`, `coneFaceFamily_last`, `Fin.lastCases_last`,
`Fin.lastCases_castSucc`, `Fin.eq_castSucc_or_eq_last`, `Fin.val_castSucc`, `Fin.val_last`. -/
theorem ConeFaceFamilyMatching {X : Type} [TopologicalSpace X]
    (H0 : Work.Serre.Simp X 0 → Work.Serre.Simp X 1)
    (hlast0 : ∀ (i : Fin 2) (s : Work.Serre.Simp X 0), i.val = 1 →
      Work.Serre.simFace X 0 i (H0 s) = s)
    (hconst0 : ∀ (a b : Fin 2) (s t : Work.Serre.Simp X 0), a.val = 0 → b.val = 0 →
      Work.Serre.simFace X 0 a (H0 s) = Work.Serre.simFace X 0 b (H0 t))
    (s : Work.Serre.Simp X 1) (i j : Fin 3) (hij : i < j) :
    (Work.Serre.coneFaceFamily H0 s j).comp
        (Work.RatHurewicz.Bridge.coface 0 ⟨i.val, Work.Serre.fin3_lt2 i j hij⟩) =
      (Work.Serre.coneFaceFamily H0 s i).comp
        (Work.RatHurewicz.Bridge.coface 0 ⟨j.val - 1, Work.Serre.fin3_pred_lt2 j⟩) := by
  -- Split off the two possibilities `i = castSucc i'` and `i = last`, and likewise for `j`.
  obtain ⟨i', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · obtain ⟨j', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    · -- `i = i'.castSucc`, `j = j'.castSucc` with `i' < j'` in `Fin 2`, so `i' = 0`, `j' = 1`.
      -- Both relevant vertices are the first vertex of the two edges: `hconst0` identifies them.
      rw [Work.Serre.coneFaceFamily_castSucc, Work.Serre.coneFaceFamily_castSucc,
        ← Work.Serre.concretize_face, ← Work.Serre.concretize_face]
      have hlt : i'.val < j'.val := hij
      have hi0 : i'.val = 0 := by have := j'.isLt; omega
      have hj0 : j'.val - 1 = 0 := by have := i'.isLt; omega
      congr 1
      exact hconst0 i' ⟨j'.val - 1, by have := j'.isLt; omega⟩
        (Work.Serre.simFace X 0 j' s) (Work.Serre.simFace X 0 i' s) hi0 hj0
    · -- `i = i'.castSucc`, `j = last`: the second vertex of `H0 (δᵢ s)` is the vertex of `s`,
      -- which is `hlast0`.
      rw [Work.Serre.coneFaceFamily_castSucc, Work.Serre.coneFaceFamily_last,
        ← Work.Serre.concretize_face, ← Work.Serre.concretize_face]
      congr 1
      change Work.Serre.simFace X 0 i' s =
        Work.Serre.simFace X 0 (1 : Fin 2) (H0 (Work.Serre.simFace X 0 i' s))
      exact (hlast0 (1 : Fin 2) (Work.Serre.simFace X 0 i' s) rfl).symm
  · -- `i = last` forces `i = 2 ≥ j`, contradicting `i < j`.
    have h : (Fin.last 2 : Fin 3).val < j.val := hij
    rw [Fin.val_last] at h
    have := j.isLt
    omega

end Work.Serre
