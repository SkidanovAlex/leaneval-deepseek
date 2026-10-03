import Mathlib
import Submission.Work.ORLyndon.cosetFinsetDefs

namespace Work.ORLyndon

/-- If `w ^ l = 1` (`1 ≤ l`), every element `u : G` falls into one of two cases for a coefficient
family `a : K[G]` whose support is covered by right `⟨w⟩`-cosets `g i · ⟨w⟩`:

* either `u` itself lies in one of the covering cosets `g i · ⟨w⟩`, in which case its coset finset
  coincides with `cosetFinset w l (g i)` and the coset sum vanishes by hypothesis;
* or `u`'s coset is disjoint from `supp a`, so all coefficients in it are zero.

Hence the vanishing of the coset sums on the covering representatives propagates to every `u`. -/
theorem coset_sums_eq_zero_of_cover {G : Type*} [Group G] [DecidableEq G] {K : Type*} [Field K]
    (w : G) (l : ℕ) (hpos : 1 ≤ l) (hw : w ^ l = 1) (a : MonoidAlgebra K G)
    {n : ℕ} (g : Fin n → G)
    (hcover : ∀ h ∈ a.coeff.support, ∃ i, ∃ m : ℤ, h = g i * w ^ m)
    (hzero : ∀ i, (∑ h ∈ cosetFinset w l (g i), a.coeff h) = 0) :
    ∀ u : G, (∑ h ∈ cosetFinset w l u, a.coeff h) = 0 := by
  classical
  intro u
  have hl : 0 < l := by omega
  by_cases hcase : ∃ i, ∃ m : ℤ, u = g i * w ^ m
  · -- `u` lies in one of the covering cosets: reuse the hypothesis.
    obtain ⟨i, m, hm⟩ := hcase
    rw [cosetFinset_eq_of_sameCoset (w := w) (g := g i) (t := u) hl hw ⟨m, hm⟩]
    exact hzero i
  · -- `u`'s coset meets no covering coset, hence misses the support.
    push Not at hcase
    refine Finset.sum_eq_zero ?_
    intro h hh
    by_contra hne
    have hsupp : h ∈ a.coeff.support := Finsupp.mem_support_iff.mpr hne
    obtain ⟨i, m, hm⟩ := hcover h hsupp
    obtain ⟨k, hk, hk'⟩ := mem_cosetFinset.mp hh
    -- `h = u * w ^ k = g i * w ^ m` forces `u = g i * w ^ (m - k)`, contradicting `hcase`.
    refine hcase i (m - (k : ℤ)) ?_
    have h1 : u * w ^ (k : ℕ) = g i * w ^ m := by rw [← hk', hm]
    calc u = u * w ^ (k : ℕ) * (w ^ (k : ℕ))⁻¹ := by group
      _ = g i * w ^ m * (w ^ (k : ℕ))⁻¹ := by rw [h1]
      _ = g i * w ^ m * (w ^ (k : ℤ))⁻¹ := by rw [zpow_natCast]
      _ = g i * (w ^ m * (w ^ (k : ℤ))⁻¹) := by rw [mul_assoc]
      _ = g i * w ^ (m - (k : ℤ)) := by rw [zpow_sub]

end Work.ORLyndon
