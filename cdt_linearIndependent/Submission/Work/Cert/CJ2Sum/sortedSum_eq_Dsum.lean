import Mathlib
import Submission.Work.Cert.CJ2.Gen

namespace Work.Cert.CJ2Sum

open Work.Cert.CJ2

/-- If `x.1 ≤ y.1` for every `y` in the tail `l` (in particular for `x` the head of a list
sorted by first component), the inner sum appearing in the recursion of `Dsum` collapses
to `Vsum l`. -/
lemma sum_max_eq_Vsum (x : ℤ × ℤ) (l : List (ℤ × ℤ)) (h : ∀ y ∈ l, x.1 ≤ y.1) :
    (l.map (fun y => y.2 * max x.1 y.1)).sum = Vsum l := by
  induction l with
  | nil => simp [Vsum]
  | cons y t ih =>
    have hy : x.1 ≤ y.1 := h y (by simp)
    rw [List.map_cons, List.sum_cons, Vsum_cons, max_eq_right hy,
        ih (fun z hz => h z (by simp [hz]))]
    ring

/-- Evaluating the cumulative-weight sum `sortedSum` on a list sorted by value: the sum
`Σ_i v_i ((c_i)² - (c_{i-1})²)` equals `Dsum l` (the `c = 0` case) plus the shift correction
`2 c · Vsum l`. -/
theorem sortedSum_eq_Dsum (l : List (ℤ × ℤ)) (c acc : ℤ)
    (hs : List.Pairwise (fun a b : ℤ × ℤ => a.1 ≤ b.1) l) :
    Work.Cert.CJ2.sortedSum l c acc = acc + Work.Cert.CJ2.Dsum l + 2 * c * Work.Cert.CJ2.Vsum l := by
  induction l generalizing c acc with
  | nil => simp [Work.Cert.CJ2.sortedSum, Work.Cert.CJ2.Dsum, Work.Cert.CJ2.Vsum]
  | cons x l ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hhead, htail⟩ := hs
    have hsum := sum_max_eq_Vsum x l hhead
    simp only [Work.Cert.CJ2.sortedSum, Work.Cert.CJ2.Dsum_cons, Work.Cert.CJ2.Vsum_cons, hsum,
      ih (c + x.2) (acc + x.1 * ((c + x.2) * (c + x.2) - c * c)) htail]
    ring

end Work.Cert.CJ2Sum
