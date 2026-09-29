import Mathlib

/-! Guidance from the project lead (the requester):

# Shared arc certificate, part 2: the sorted evaluation of Σ_{a,b} μ_a μ_b max(v_a, v_b)
Reindex by σ; since v∘σ is monotone, max(v(σ i), v(σ j)) = v(σ (max i j)). Then
Σ_{i,j} μ_i μ_j v_{max(i,j)} = Σ_i v_i (μ_i² + 2 μ_i Σ_{j<i} μ_j) = Σ_i v_i (c_i² − c_{i−1}²),
c_i = Σ_{j ≤ i} μ_j. No sign hypotheses needed. This turns the N²-term certificate sum of
`rearrInt_arc_bound` into an O(N) sum after an in-kernel (or certificate-supplied) sort: the
certificate supplies σ as data and the kernel checks monotonicity of v∘σ by `decide` on rationals.
-/

namespace Work.ArcCert

/-- Splitting the inner sum at the index `a`: for `b ≤ a` the monotonicity of `y` gives
`max (y a) (y b) = y a`, and for `a < b` it gives `max (y a) (y b) = y b`. -/
private theorem sum_max_split {M : ℕ} (x y : Fin M → ℝ) (hy : Monotone y) (a : Fin M) :
    (∑ b, x a * x b * max (y a) (y b)) =
      x a * y a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≤ a), x b)
        + x a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), x b * y b) := by
  have hfilt : Finset.univ.filter (fun b : Fin M => ¬ b ≤ a)
      = Finset.univ.filter (fun b : Fin M => a < b) := by
    simp only [not_le]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin M => b ≤ a)
        (fun b => x a * x b * max (y a) (y b)), hfilt]
  congr 1
  · have h1 : ∀ b ∈ Finset.univ.filter (fun b : Fin M => b ≤ a),
        x a * x b * max (y a) (y b) = (x a * y a) * x b := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [max_eq_left (hy hb)]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  · have h2 : ∀ b ∈ Finset.univ.filter (fun b : Fin M => a < b),
        x a * x b * max (y a) (y b) = x a * (x b * y b) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [max_eq_right (hy (le_of_lt hb))]
      ring
    rw [Finset.sum_congr rfl h2, Finset.mul_sum]

/-- Exchange of summation order over the strictly upper triangular pairs `a < b`. -/
private theorem sum_lt_swap {M : ℕ} (F : Fin M → Fin M → ℝ) :
    (∑ a, ∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), F a b) =
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a : Fin M => a < b), F a b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A sum over the initial segment `{j | j ≤ a}` is the sum over `{j | j < a}` plus the top term. -/
private theorem sum_filter_le_eq_sum_filter_lt_add {M : ℕ} (x : Fin M → ℝ) (a : Fin M) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin M => j ≤ a), x j)
      = (∑ j ∈ Finset.univ.filter (fun j : Fin M => j < a), x j) + x a := by
  have hset : Finset.univ.filter (fun j : Fin M => j ≤ a)
      = insert a (Finset.univ.filter (fun j : Fin M => j < a)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rintro (h | h)
      · exact le_of_eq h
      · exact le_of_lt h
  rw [hset, Finset.sum_insert]
  · ring
  · simp

/-- The sorted evaluation identity, in the "generic monotone" form: for a monotone `y`,
`∑_{a,b} x_a x_b max(y_a, y_b) = ∑_i y_i (c_i² − c_{i−1}²)` where `c_i = ∑_{j ≤ i} x_j`
(the case `i = 0` here has `c_{-1} = 0`). -/
private theorem sorted_double_sum {M : ℕ} (x y : Fin M → ℝ) (hy : Monotone y) :
    ∑ a, ∑ b, x a * x b * max (y a) (y b) =
      ∑ i, y i * ((∑ j ∈ Finset.univ.filter (fun j : Fin M => j ≤ i), x j) ^ 2 -
        (∑ j ∈ Finset.univ.filter (fun j : Fin M => j < i), x j) ^ 2) := by
  have h1 : (∑ a, ∑ b, x a * x b * max (y a) (y b))
      = ∑ a, (x a * y a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≤ a), x b)
          + x a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), x b * y b)) := by
    apply Finset.sum_congr rfl
    intro a _
    exact sum_max_split x y hy a
  have hswap : (∑ a, x a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), x b * y b))
      = ∑ a, x a * y a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => b < a), x b) := by
    have hs : (∑ a, x a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), x b * y b))
        = ∑ a, ∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), x a * (x b * y b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    rw [hs, sum_lt_swap (fun a b => x a * (x b * y b))]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_mul]
    ring
  have h2 : (∑ a, (x a * y a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≤ a), x b)
          + x a * (∑ b ∈ Finset.univ.filter (fun b : Fin M => a < b), x b * y b)))
      = ∑ a, x a * y a * ((∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≤ a), x b)
          + (∑ b ∈ Finset.univ.filter (fun b : Fin M => b < a), x b)) := by
    rw [Finset.sum_add_distrib, hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h3 : (∑ a, x a * y a * ((∑ b ∈ Finset.univ.filter (fun b : Fin M => b ≤ a), x b)
          + (∑ b ∈ Finset.univ.filter (fun b : Fin M => b < a), x b)))
      = ∑ i, y i * ((∑ j ∈ Finset.univ.filter (fun j : Fin M => j ≤ i), x j) ^ 2 -
        (∑ j ∈ Finset.univ.filter (fun j : Fin M => j < i), x j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [sum_filter_le_eq_sum_filter_lt_add x a]
    ring
  exact h1.trans (h2.trans h3)

theorem sum_mul_max_eq_sorted {M : ℕ} (v μ : Fin M → ℝ) (σ : Equiv.Perm (Fin M))
    (hmono : Monotone (v ∘ σ)) :
    ∑ a, ∑ b, μ a * μ b * max (v a) (v b) =
      ∑ i, v (σ i) * ((∑ j ∈ Finset.univ.filter (· ≤ i), μ (σ j)) ^ 2 -
        (∑ j ∈ Finset.univ.filter (· < i), μ (σ j)) ^ 2) := by
  have hL : (∑ a, ∑ b, μ a * μ b * max (v a) (v b))
      = ∑ a, ∑ b, μ (σ a) * μ (σ b) * max (v (σ a)) (v (σ b)) := by
    rw [← Equiv.sum_comp σ (fun a => ∑ b, μ a * μ b * max (v a) (v b))]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Equiv.sum_comp σ (fun b => μ (σ a) * μ b * max (v (σ a)) (v b))]
  rw [hL]
  rw [sorted_double_sum (fun i => μ (σ i)) (fun i => v (σ i)) hmono]

end Work.ArcCert
