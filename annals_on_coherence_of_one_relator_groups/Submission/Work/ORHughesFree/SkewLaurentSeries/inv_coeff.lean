import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow

namespace Work.ORHughesFree.SkewLaurentSeries

theorem inv_coeff {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {f g : Work.ORHughesFree.SkewLaurentSeries A} {m : ℤ} {ainv : A}
    (hinv : f.1 m * ainv = 1) (hinv' : ainv * f.1 m = 1)
    (hm : ∀ j : ℤ, j < m → f.1 j = 0)
    (hvw : Work.ORHughesFree.SkewLaurentSeries.VanishesBelow g (-m)) (hfg : f * g = 1) (n : ℤ) :
    (Multiplicative.ofAdd m) • g.1 (n - m) =
      ainv * ((if n = 0 then (1 : A) else 0) -
        ∑ i ∈ Finset.Icc (m + 1) (n + m), f.1 i * ((Multiplicative.ofAdd i) • g.1 (n - i))) := by
  classical
  -- The master equation: the `n`-th coefficient of `f * g = 1` is the skew convolution, which
  -- only sees `k ∈ [m, n + m]` because `f` vanishes below `m` and `g` below `-m`.
  have hprod : ∑ k ∈ Finset.Icc m (n + m),
      f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)) = (if n = 0 then (1 : A) else 0) := by
    have h := mul_apply_of_bounds f g m (-m) hm hvw n
    rw [hfg, one_apply, sub_neg_eq_add] at h
    exact h.symm
  by_cases hn : n < 0
  · -- `n < 0`: both sides vanish.  The left-hand side because `g` vanishes below `-m`, the
    -- right-hand side because the sum is empty and `n ≠ 0`.
    have hg0 : g.1 (n - m) = 0 := hvw (n - m) (by omega)
    have hsum0 : ∑ i ∈ Finset.Icc (m + 1) (n + m),
        f.1 i * ((Multiplicative.ofAdd i) • g.1 (n - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [hvw (n - i) (by omega), smul_zero, MulZeroClass.mul_zero]
    rw [hg0, smul_zero, hsum0, sub_zero, if_neg (by omega : n ≠ 0), MulZeroClass.mul_zero]
  · -- `n ≥ 0`: isolate the `k = m` term of the convolution, which carries the unknown
    -- coefficient `g.1 (n - m)`, and solve for it using `ainv * f.1 m = 1`.
    rw [not_lt] at hn
    have hIcc : Finset.Icc m (n + m) = insert m (Finset.Icc (m + 1) (n + m)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor
      · intro h
        rcases eq_or_lt_of_le h.1 with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr ⟨h', h.2⟩
      · intro h
        rcases h with h' | ⟨h1, h2⟩
        · omega
        · omega
    have hsplit : ∑ k ∈ Finset.Icc m (n + m),
        f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))
        = f.1 m * ((Multiplicative.ofAdd m) • g.1 (n - m))
          + ∑ i ∈ Finset.Icc (m + 1) (n + m),
            f.1 i * ((Multiplicative.ofAdd i) • g.1 (n - i)) := by
      rw [hIcc, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
    have hfm : f.1 m * ((Multiplicative.ofAdd m) • g.1 (n - m))
        = (if n = 0 then (1 : A) else 0)
          - ∑ i ∈ Finset.Icc (m + 1) (n + m),
            f.1 i * ((Multiplicative.ofAdd i) • g.1 (n - i)) := by
      have h1 : f.1 m * ((Multiplicative.ofAdd m) • g.1 (n - m))
          + ∑ i ∈ Finset.Icc (m + 1) (n + m),
            f.1 i * ((Multiplicative.ofAdd i) • g.1 (n - i))
          = (if n = 0 then (1 : A) else 0) := by
        rw [← hsplit]; exact hprod
      exact eq_sub_of_add_eq h1
    calc (Multiplicative.ofAdd m) • g.1 (n - m)
        = 1 * ((Multiplicative.ofAdd m) • g.1 (n - m)) := (_root_.one_mul _).symm
      _ = (ainv * f.1 m) * ((Multiplicative.ofAdd m) • g.1 (n - m)) := by rw [hinv']
      _ = ainv * (f.1 m * ((Multiplicative.ofAdd m) • g.1 (n - m))) := by rw [_root_.mul_assoc]
      _ = ainv * ((if n = 0 then (1 : A) else 0) -
            ∑ i ∈ Finset.Icc (m + 1) (n + m),
              f.1 i * ((Multiplicative.ofAdd i) • g.1 (n - i))) := by rw [hfm]

end Work.ORHughesFree.SkewLaurentSeries
