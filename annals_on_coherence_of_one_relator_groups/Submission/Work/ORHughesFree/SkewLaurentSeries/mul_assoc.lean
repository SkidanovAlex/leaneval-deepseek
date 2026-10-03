import Mathlib
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds

namespace Work.ORHughesFree.SkewLaurentSeries

/-- Shifting the index of a sum over an integer interval: substituting `j = k + l`. -/
theorem sum_Icc_sub_shift {M : Type*} [AddCommMonoid M] (φ : ℤ → M) (k x y : ℤ) :
    (∑ j ∈ Finset.Icc x y, φ j) = ∑ l ∈ Finset.Icc (x - k) (y - k), φ (k + l) := by
  refine Finset.sum_bij (fun j _ => j - k) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    exact ⟨by omega, by omega⟩
  · intro j₁ _ j₂ _ h
    omega
  · intro b hb
    rw [Finset.mem_Icc] at hb
    refine ⟨b + k, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    · omega
  · intro j _
    congr 1
    omega

theorem mul_assoc {A : Type} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    (f g h : SkewLaurentSeries A) : f * g * h = f * (g * h) := by
  refine Subtype.ext (funext (fun n => ?_))
  set a : ℤ := lo f with ha
  set b : ℤ := lo g with hb
  set c : ℤ := lo h with hc
  have hf : ∀ m : ℤ, m < a → f.1 m = 0 := by intro m hm; rw [ha] at hm; exact lt_lo hm
  have hg : ∀ m : ℤ, m < b → g.1 m = 0 := by intro m hm; rw [hb] at hm; exact lt_lo hm
  have hh : ∀ m : ℤ, m < c → h.1 m = 0 := by intro m hm; rw [hc] at hm; exact lt_lo hm
  have hfg : ∀ m : ℤ, m < a + b → (f * g).1 m = 0 := by
    intro m hm
    rw [mul_apply_of_bounds f g a b hf hg m,
        Finset.Icc_eq_empty_of_lt (show m - b < a by omega), Finset.sum_empty]
  have hgh : ∀ m : ℤ, m < b + c → (g * h).1 m = 0 := by
    intro m hm
    rw [mul_apply_of_bounds g h b c hg hh m,
        Finset.Icc_eq_empty_of_lt (show m - c < b by omega), Finset.sum_empty]
  -- The coefficient of the left-associated triple product, in a symmetric form.
  have hL : (f * g * h).1 n =
      ∑ k ∈ Finset.Icc a (n - b - c), ∑ l ∈ Finset.Icc b (n - k - c),
        (f.1 k * ((Multiplicative.ofAdd k) • g.1 l)) *
          ((Multiplicative.ofAdd (k + l)) • h.1 (n - k - l)) := by
    rw [mul_apply_of_bounds (f * g) h (a + b) c hfg hh n]
    have step1 : (∑ j ∈ Finset.Icc (a + b) (n - c),
          (f * g).1 j * ((Multiplicative.ofAdd j) • h.1 (n - j)))
        = ∑ j ∈ Finset.Icc (a + b) (n - c), ∑ k ∈ Finset.Icc a (n - b - c),
            (f.1 k * ((Multiplicative.ofAdd k) • g.1 (j - k))) *
              ((Multiplicative.ofAdd j) • h.1 (n - j)) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [mul_apply_of_bounds f g a b hf hg j, Finset.sum_mul]
      apply Finset.sum_subset
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        exact ⟨hx.1, by omega⟩
      · intro x hx hxnot
        rw [Finset.mem_Icc] at hx
        have hxb : j - b < x := by
          by_contra hcon
          exact hxnot (by rw [Finset.mem_Icc]; exact ⟨hx.1, not_lt.mp hcon⟩)
        rw [hg (j - x) (by omega), smul_zero, mul_zero, zero_mul]
    rw [step1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    rw [sum_Icc_sub_shift (fun j =>
        (f.1 k * ((Multiplicative.ofAdd k) • g.1 (j - k))) *
          ((Multiplicative.ofAdd j) • h.1 (n - j))) k (a + b) (n - c)]
    have hext : (∑ l ∈ Finset.Icc b (n - k - c),
          (f.1 k * ((Multiplicative.ofAdd k) • g.1 ((k + l) - k))) *
            ((Multiplicative.ofAdd (k + l)) • h.1 (n - (k + l))))
        = ∑ l ∈ Finset.Icc (a + b - k) (n - c - k),
          (f.1 k * ((Multiplicative.ofAdd k) • g.1 ((k + l) - k))) *
            ((Multiplicative.ofAdd (k + l)) • h.1 (n - (k + l))) := by
      apply Finset.sum_subset
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        exact ⟨by omega, by omega⟩
      · intro x hx hxnot
        rw [Finset.mem_Icc] at hx
        have hxb : x < b := by
          by_contra hcon
          refine hxnot (by rw [Finset.mem_Icc]; exact ⟨not_lt.mp hcon, by omega⟩)
        rw [show (k + x) - k = x from by ring, hg x hxb, smul_zero, mul_zero, zero_mul]
    rw [← hext]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (k + l) - k = l from by ring, show n - (k + l) = n - k - l from by ring]
  -- The coefficient of the right-associated triple product, in the same shape.
  have hR : (f * (g * h)).1 n =
      ∑ k ∈ Finset.Icc a (n - b - c), ∑ l ∈ Finset.Icc b (n - k - c),
        f.1 k * (((Multiplicative.ofAdd k) • g.1 l) *
          ((Multiplicative.ofAdd (k + l)) • h.1 (n - k - l))) := by
    rw [mul_apply_of_bounds f (g * h) a (b + c) hf hgh n,
        show n - (b + c) = n - b - c from by ring]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_apply_of_bounds g h b c hg hh (n - k)]
    simp_rw [Finset.smul_sum, Finset.mul_sum]
    simp only [MulSemiringAction.smul_mul, smul_smul, ← ofAdd_add]
  rw [hL, hR]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact _root_.mul_assoc _ _ _

end Work.ORHughesFree.SkewLaurentSeries
