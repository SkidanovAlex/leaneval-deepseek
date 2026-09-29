import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Scale

/-- For a real number `α` and a bound `N`, only finitely many rationals with
denominator at most `N` are good approximations to `α` (within `1/den²`).
This is the quantitative content behind the unboundedness of the denominators
of the good approximations to an irrational number. -/
private lemma finite_den_le (α : ℝ) (N : ℕ) :
    {q : ℚ | q.den ≤ N ∧ |α - (q : ℝ)| < 1 / ((q.den : ℝ) ^ 2)}.Finite := by
  set M : ℤ := ⌈(N : ℝ) * |α|⌉ + 1 with hMdef
  set s : Set ℚ := {q : ℚ | q.den ≤ N ∧ |α - (q : ℝ)| < 1 / ((q.den : ℝ) ^ 2)} with hs
  have hkey : ∀ q ∈ s, |(q.den : ℝ) * α - (q.num : ℝ)| < 1 := by
    intro q hq
    obtain ⟨hqd, hqapprox⟩ := hq
    have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hqcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    have heq : (q.den : ℝ) * α - (q.num : ℝ) = (q.den : ℝ) * (α - (q : ℝ)) := by
      rw [hqcast]; field_simp
    rw [heq, abs_mul, abs_of_pos hden]
    have h1 : (q.den : ℝ) * (1 / ((q.den : ℝ) ^ 2)) = 1 / (q.den : ℝ) := by field_simp
    calc (q.den : ℝ) * |α - (q : ℝ)| < (q.den : ℝ) * (1 / ((q.den : ℝ) ^ 2)) :=
          mul_lt_mul_of_pos_left hqapprox hden
      _ = 1 / (q.den : ℝ) := h1
      _ ≤ 1 := by rw [div_le_one hden]; exact_mod_cast q.pos
  have hbounds : ∀ q ∈ s, q.num ∈ Set.Icc (-M) M ∧ q.den ∈ Set.Icc 1 N := by
    intro q hq
    have hk := hkey q hq
    obtain ⟨hqd, hqapprox⟩ := hq
    have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
    have hdenN : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqd
    have habs : |(q.num : ℝ)| < (M : ℝ) := by
      have h1 : |(q.num : ℝ)| ≤ |(q.num : ℝ) - (q.den : ℝ) * α| + |(q.den : ℝ) * α| := by
        simpa using abs_add_le ((q.num : ℝ) - (q.den : ℝ) * α) ((q.den : ℝ) * α)
      have h2 : |(q.num : ℝ) - (q.den : ℝ) * α| < 1 := by rw [abs_sub_comm]; exact hk
      have h3 : |(q.den : ℝ) * α| = (q.den : ℝ) * |α| := by rw [abs_mul, abs_of_pos hden]
      have h4 : (q.den : ℝ) * |α| ≤ (N : ℝ) * |α| :=
        mul_le_mul_of_nonneg_right hdenN (abs_nonneg α)
      have hM : (M : ℝ) = ((⌈(N : ℝ) * |α|⌉ : ℤ) : ℝ) + 1 := by simp [M]
      have h5 : (N : ℝ) * |α| ≤ ((⌈(N : ℝ) * |α|⌉ : ℤ) : ℝ) := Int.le_ceil _
      calc |(q.num : ℝ)| ≤ |(q.num : ℝ) - (q.den : ℝ) * α| + |(q.den : ℝ) * α| := h1
        _ = |(q.num : ℝ) - (q.den : ℝ) * α| + (q.den : ℝ) * |α| := by rw [h3]
        _ < 1 + (N : ℝ) * |α| := add_lt_add_of_lt_of_le h2 h4
        _ ≤ (M : ℝ) := by rw [hM]; linarith
    rw [abs_lt] at habs
    obtain ⟨hlo, hhi⟩ := habs
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have : ((-M : ℤ) : ℝ) < (q.num : ℝ) := by rw [Int.cast_neg]; exact hlo
      exact le_of_lt (Int.cast_lt.mp this)
    · exact le_of_lt (Int.cast_lt.mp hhi)
    · exact q.pos
    · exact hqd
  have hinj : Set.InjOn (fun q : ℚ => (q.num, q.den)) s := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  have hbox : ((fun q : ℚ => (q.num, q.den)) '' s) ⊆ (Set.Icc (-M) M ×ˢ Set.Icc 1 N) := by
    rintro ⟨n, d⟩ ⟨q, hq, heq2⟩
    simp only [Prod.mk.injEq] at heq2
    obtain ⟨hn, hd⟩ := heq2
    rw [← hn, ← hd]
    exact hbounds q hq
  exact Set.Finite.of_finite_image
    ((Set.Finite.prod (Set.finite_Icc (-M) M) (Set.finite_Icc 1 N)).subset hbox) hinj

/-- **Dirichlet approximation, unbounded denominators.** For an irrational real `α`
and any bound `N`, there is a rational `q` with denominator exceeding `N` that
approximates `α` to within `1/q.den²`. -/
private lemma exists_den_gt (α : ℝ) (hα : Irrational α) (N : ℕ) :
    ∃ q : ℚ, |α - (q : ℝ)| < 1 / ((q.den : ℝ) ^ 2) ∧ N < q.den := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  apply (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hα)
  exact (finite_den_le α N).subset (fun q hq => ⟨h q hq, hq⟩)

theorem exists_approx_seq (α : ℝ) (hα : Irrational α) : ∃ (a : ℕ → ℤ) (q : ℕ → ℕ), (∀ n, 1 ≤ q n) ∧ Filter.Tendsto q Filter.atTop Filter.atTop ∧ (∀ n, Nat.Coprime (Int.natAbs (a n)) (q n)) ∧ ∀ n, |α - (a n : ℝ) / (q n : ℝ)| < 1 / ((q n : ℝ) ^ 2) := by
  choose f hf using exists_den_gt α hα
  refine ⟨fun n => (f n).num, fun n => (f n).den, ?_, ?_, ?_, ?_⟩
  · intro n; exact (f n).pos
  · rw [Filter.tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun a ha => le_of_lt (lt_of_le_of_lt ha (hf a).2)⟩
  · intro n; exact (f n).reduced
  · intro n
    have h := (hf n).1
    rwa [Rat.cast_def] at h

end Work.TMC7Core.Scale
