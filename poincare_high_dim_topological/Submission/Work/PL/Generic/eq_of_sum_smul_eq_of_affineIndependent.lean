import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Hull

namespace Work.PL.Generic

/-- Uniqueness of barycentric coordinates with respect to an affinely independent vertex set.
Mathlib has `AffineIndependent.eq_of_sum_eq_sum` (over an arbitrary index type); transport along
`Finset.sum_attach`.  The workspace also has `Work.PL.Subdiv.Simplex.sum_smul_unique`. -/
theorem eq_of_sum_smul_eq_of_affineIndependent {n : ℕ} {ι : Type*} {y : ι → PL.E n} {s : Finset ι}
    (hind : AffineIndependent ℝ (fun v : ↥s => y v)) {a b : ι → ℝ}
    (ha : ∑ v ∈ s, a v = 1) (hb : ∑ v ∈ s, b v = 1)
    (h : ∑ v ∈ s, a v • y v = ∑ v ∈ s, b v • y v) : ∀ v ∈ s, a v = b v := by
  intro v hv
  have h1 : ∑ i ∈ s.attach, a ↑i = ∑ i ∈ s.attach, b ↑i := by
    rw [Finset.sum_attach, Finset.sum_attach, ha, hb]
  have h2 := h
  rw [← Finset.sum_attach s (fun i => a i • y i),
    ← Finset.sum_attach s (fun i => b i • y i)] at h2
  exact AffineIndependent.eq_of_sum_eq_sum hind h1 h2 ⟨v, hv⟩ (Finset.mem_attach s ⟨v, hv⟩)

end Work.PL.Generic
