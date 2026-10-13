import Mathlib

namespace Work.DSEQ0

universe u

/-- Telescoping sum over an integer interval: summing the consecutive differences
`f (i + 1) - f i` for `i` running from `a` to `b` gives `f (b + 1) - f a`.

This is the `ℤ`-interval analogue of `Finset.sum_range_sub`. -/
theorem sum_Icc_sub_shift {M : Type u} [AddCommGroup M] (f : ℤ → M) (a b : ℤ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, (f (i + 1) - f i)) = f (b + 1) - f a := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = b - a := ⟨(b - a).toNat, Int.toNat_sub_of_le hab⟩
  have himg : (Finset.range (n + 1)).image (fun j : ℕ => a + (j : ℤ)) = Finset.Icc a b := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ?_⟩ <;> omega
    · intro hi
      refine ⟨(i - a).toNat, ?_, ?_⟩
      · have : (i - a).toNat ≤ n := by omega
        omega
      · have : ((i - a).toNat : ℤ) = i - a := Int.toNat_of_nonneg (by omega)
        omega
  rw [← himg]
  rw [Finset.sum_image]
  · rw [show (∑ x ∈ Finset.range (n + 1), (f (a + ↑x + 1) - f (a + ↑x)))
        = ∑ x ∈ Finset.range (n + 1), (f (a + ↑(x + 1)) - f (a + ↑x)) from
      Finset.sum_congr rfl (fun x _ => by
        rw [show a + (x : ℤ) + 1 = a + ((x + 1 : ℕ) : ℤ) by push_cast; ring])]
    have key : (∑ x ∈ Finset.range (n + 1), (f (a + ↑(x + 1)) - f (a + ↑x)))
        = f (a + ↑(n + 1)) - f (a + ↑(0 : ℕ)) :=
      Finset.sum_range_sub (fun j : ℕ => f (a + (j : ℤ))) (n + 1)
    rw [key]
    have h1 : a + ((n + 1 : ℕ) : ℤ) = b + 1 := by push_cast; omega
    have h2 : a + ((0 : ℕ) : ℤ) = a := by push_cast; ring
    rw [h1, h2]
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_range] at hx hy
    change a + (x : ℤ) = a + (y : ℤ) at hxy
    omega

theorem sum_Icc_mul_add_succ (A : Type u) [CommRing A]
    (s : ℤ → A) (hs : ∀ m : ℤ, s (m + 1) = - s m) (L : ℤ → A) (a b : ℤ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, s i * (L i + L (i + 1))) = s a * L a - s (b + 1) * L (b + 1) := by
  have hterm : ∀ i : ℤ,
      s i * (L i + L (i + 1)) =
        (fun i => -(s i * L i)) (i + 1) - (fun i => -(s i * L i)) i := by
    intro i
    have hsi : s i = - s (i + 1) := by rw [hs i, neg_neg]
    simp only []
    rw [hsi]
    ring
  have hcongr : (∑ i ∈ Finset.Icc a b, s i * (L i + L (i + 1)))
      = ∑ i ∈ Finset.Icc a b,
          ((fun i => -(s i * L i)) (i + 1) - (fun i => -(s i * L i)) i) :=
    Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hcongr, sum_Icc_sub_shift (fun i => -(s i * L i)) a b hab]
  ring

end Work.DSEQ0
