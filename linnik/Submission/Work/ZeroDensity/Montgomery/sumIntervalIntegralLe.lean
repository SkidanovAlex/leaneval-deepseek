import Mathlib

open MeasureTheory intervalIntegral

namespace Work.ZeroDensity.Montgomery

lemma sumIntervalIntegralLe {f : ℝ → ℝ} {h A B : ℝ} (hh : 0 < h) (hAB : A ≤ B)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) {S : Finset ℝ}
    (hsub : ∀ s ∈ S, A ≤ s - h ∧ s + h ≤ B)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 2 * h ≤ |s - s'|) :
    ∑ s ∈ S, (∫ x in (s - h)..(s + h), f x) ≤ ∫ x in A..B, f x := by
  -- The half-open intervals `(s - h, s + h]` are pairwise disjoint.
  have hdisj : (S : Set ℝ).Pairwise
      (Function.onFun Disjoint fun i => Set.Ioc (i - h) (i + h)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    rw [Set.mem_Ioc] at hz1 hz2
    obtain ⟨hz1a, hz1b⟩ := hz1
    obtain ⟨hz2a, hz2b⟩ := hz2
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have habs : |x - y| = y - x := by
        rw [abs_of_neg (show x - y < 0 by linarith)]; ring
      have hle := hsep x hx y hy hxy
      rw [habs] at hle
      linarith
    · have habs : |x - y| = x - y := by
        rw [abs_of_pos (show 0 < x - y by linarith)]
      have hle := hsep x hx y hy hxy
      rw [habs] at hle
      linarith
  -- The union of the intervals is contained in `(A, B]`.
  have hsub' : ∀ x, x ∈ (⋃ i ∈ S, Set.Ioc (i - h) (i + h)) → x ∈ Set.Ioc A B := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hiS, hix⟩ := hx
    rw [Set.mem_Ioc] at hix ⊢
    obtain ⟨h1, h2⟩ := hsub i hiS
    exact ⟨lt_of_le_of_lt h1 hix.1, le_trans hix.2 h2⟩
  calc ∑ s ∈ S, (∫ x in (s - h)..(s + h), f x)
      = ∑ s ∈ S, ∫ x in Set.Ioc (s - h) (s + h), f x :=
        Finset.sum_congr rfl (fun s _ => intervalIntegral.integral_of_le (by linarith))
    _ = ∫ x in (⋃ i ∈ S, Set.Ioc (i - h) (i + h)), f x :=
        (integral_biUnion_finset S (fun i _ => measurableSet_Ioc) hdisj
          (fun i _ => hf.integrableOn_Ioc)).symm
    _ ≤ ∫ x in Set.Ioc A B, f x :=
        setIntegral_mono_set hf.integrableOn_Ioc
          (ae_of_all _ hf0) (ae_of_all _ hsub')
    _ = ∫ x in A..B, f x := (intervalIntegral.integral_of_le hAB).symm

end Work.ZeroDensity.Montgomery
