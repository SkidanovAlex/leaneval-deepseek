import Mathlib
import Submission.Work.DSCOH.LocBasisDefs

namespace Work.DSCOH

theorem lmb_support_degree {A : Type*} [CommRing A] {n : ℕ} {e : ℕ} {m : Poly A n}
    (hm : m ∈ homSub A n e) {v : Fin n →₀ ℕ} (hv : v ∈ m.support) : (∑ i, v i) = e := by
  have h := hm.degree_eq_sum_deg_support hv
  have h1 : v.sum (fun _ c => c) = ∑ i, v i :=
    Finsupp.sum_fintype v (fun _ c => c) (fun _ => rfl)
  have h2 : v.sum (fun _ c => c) = ∑ i ∈ v.support, v i :=
    Finsupp.sum_of_support_subset v (Finset.Subset.refl v.support) (fun _ c => c)
      (fun _ _ => rfl)
  rw [← h1, h2, ← h]

end Work.DSCOH
