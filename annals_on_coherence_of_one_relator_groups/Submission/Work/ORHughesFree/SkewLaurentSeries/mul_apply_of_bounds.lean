import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries

namespace Work.ORHughesFree.SkewLaurentSeries

/-- A sum over an integer interval of a function vanishing outside a second interval only
sees the intersection of the two intervals. -/
theorem sum_Icc_eq_of_eq_zero_outside {M : Type*} [AddCommMonoid M] (φ : ℤ → M) (a b c d : ℤ)
    (hc : ∀ x : ℤ, x < c → φ x = 0) (hd : ∀ x : ℤ, x > d → φ x = 0) :
    ∑ k ∈ Finset.Icc a b, φ k = ∑ k ∈ Finset.Icc (max a c) (min b d), φ k := by
  have hinter : Finset.Icc a b ∩ Finset.Icc c d = Finset.Icc (max a c) (min b d) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_Icc, max_le_iff, le_min_iff]
    tauto
  calc ∑ k ∈ Finset.Icc a b, φ k
      = ∑ k ∈ Finset.Icc a b ∩ Finset.Icc c d, φ k := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left ?_
        intro x hx hxnot
        have hx' : x ∉ Finset.Icc c d := fun h => hxnot (Finset.mem_inter.mpr ⟨hx, h⟩)
        rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx'
        rcases hx' with h | h
        · exact hc x h
        · exact hd x h
    _ = ∑ k ∈ Finset.Icc (max a c) (min b d), φ k := by rw [hinter]

theorem mul_apply_of_bounds {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g : SkewLaurentSeries A) (Nf Ng : ℤ)
    (hf : ∀ n : ℤ, n < Nf → f.1 n = 0) (hg : ∀ n : ℤ, n < Ng → g.1 n = 0) (n : ℤ) :
    (f * g).1 n = ∑ k ∈ Finset.Icc Nf (n - Ng),
      f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)) := by
  rw [mul_apply]
  have hmid : ∑ k ∈ Finset.Icc (lo f) (n - lo g),
        f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))
      = ∑ k ∈ Finset.Icc (max (lo f) Nf) (min (n - lo g) (n - Ng)),
        f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)) :=
    sum_Icc_eq_of_eq_zero_outside _ _ _ Nf (n - Ng)
      (fun x hx => by rw [hf x hx, zero_mul])
      (fun x hx => by
        have h : n - x < Ng := by omega
        rw [hg (n - x) h, smul_zero, mul_zero])
  have hmid₂ : ∑ k ∈ Finset.Icc Nf (n - Ng),
        f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))
      = ∑ k ∈ Finset.Icc (max Nf (lo f)) (min (n - Ng) (n - lo g)),
        f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)) :=
    sum_Icc_eq_of_eq_zero_outside _ _ _ (lo f) (n - lo g)
      (fun x hx => by rw [lt_lo (f := f) hx, zero_mul])
      (fun x hx => by
        have h : n - x < lo g := by omega
        rw [lt_lo (f := g) h, smul_zero, mul_zero])
  rw [hmid, hmid₂, max_comm (lo f) Nf, min_comm (n - lo g) (n - Ng)]

end Work.ORHughesFree.SkewLaurentSeries
