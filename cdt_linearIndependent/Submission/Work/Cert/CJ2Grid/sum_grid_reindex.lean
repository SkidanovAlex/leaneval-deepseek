import Mathlib

namespace Work.Cert.CJ2Grid

open Finset

/-- The grid map `(k,j) ↦ m*k+j` maps `range n ×ˢ range m` onto `range (n*m)` (for `m > 0`). -/
lemma image_grid_prod (n m : ℕ) (hm : 0 < m) :
    (Finset.range n ×ˢ Finset.range m).image (fun p : ℕ × ℕ => m * p.1 + p.2)
      = Finset.range (n * m) := by
  ext a
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
    have h1 : p.1 + 1 ≤ n := hp1
    have h2 : m * (p.1 + 1) ≤ m * n := Nat.mul_le_mul_left m h1
    have h3 : m * p.1 + p.2 < m * (p.1 + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_lt_add_left hp2 (m * p.1)
    calc m * p.1 + p.2 < m * (p.1 + 1) := h3
      _ ≤ m * n := h2
      _ = n * m := Nat.mul_comm m n
  · intro ha
    refine ⟨(a / m, a % m), ⟨?_, ?_⟩, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul hm).mpr ha
    · exact Nat.mod_lt a hm
    · exact Nat.div_add_mod a m

/-- Reindexing a double sum over the `n × m` grid as a sum over `range (n*m)`. -/
lemma sum_prod_range_mul_add (n m : ℕ) (hm : 0 < m) (u : ℕ → ℤ) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, u (m * k + j))
      = ∑ a ∈ Finset.range (n * m), u a := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => m * p.1 + p.2)
      ↑(Finset.range n ×ˢ Finset.range m) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hq
    change m * p.1 + p.2 = m * q.1 + q.2 at hpq
    have h1 : p.1 = q.1 := by
      have hp' : (m * p.1 + p.2) / m = p.1 := by
        rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hp.2, Nat.add_zero]
      have hq' : (m * q.1 + q.2) / m = q.1 := by
        rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hq.2, Nat.add_zero]
      rw [← hp', hpq, hq']
    have h2 : p.2 = q.2 := by
      rw [h1] at hpq
      exact Nat.add_left_cancel hpq
    exact Prod.ext h1 h2
  have h1 : (∑ a ∈ Finset.range (n * m), u a)
      = ∑ p ∈ Finset.range n ×ˢ Finset.range m, u (m * p.1 + p.2) := by
    rw [← image_grid_prod n m hm, Finset.sum_image hinj]
  have h2 : (∑ p ∈ Finset.range n ×ˢ Finset.range m, u (m * p.1 + p.2))
      = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, u (m * k + j) := by
    rw [Finset.sum_product]
  exact h2.symm.trans h1.symm

/-- Reindexing a double double sum over the `n × m` grid as a double sum over `range (n*m)`. -/
lemma sum_grid_core (n m : ℕ) (hm : 0 < m) (T : ℕ → ℕ → ℤ) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k' ∈ Finset.range n,
        ∑ j' ∈ Finset.range m, T (m * k + j) (m * k' + j'))
      = ∑ a ∈ Finset.range (n * m), ∑ b ∈ Finset.range (n * m), T a b := by
  have hinner : ∀ k j : ℕ,
      (∑ k' ∈ Finset.range n, ∑ j' ∈ Finset.range m, T (m * k + j) (m * k' + j'))
        = ∑ b ∈ Finset.range (n * m), T (m * k + j) b :=
    fun k j => sum_prod_range_mul_add n m hm (fun b => T (m * k + j) b)
  calc (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k' ∈ Finset.range n,
          ∑ j' ∈ Finset.range m, T (m * k + j) (m * k' + j'))
      = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m,
          ∑ b ∈ Finset.range (n * m), T (m * k + j) b :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => hinner k j))
    _ = ∑ a ∈ Finset.range (n * m), ∑ b ∈ Finset.range (n * m), T a b :=
        sum_prod_range_mul_add n m hm (fun a => ∑ b ∈ Finset.range (n * m), T a b)

theorem sum_grid_reindex (n m : ℕ) (μ f : ℕ → ℤ) (hm : 0 < m) :
    (∑ k ∈ Finset.range n, ∑ k' ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ j' ∈ Finset.range m,
        μ k * μ k' * max (f (m*k+j)) (f (m*k'+j')))
      = ∑ a ∈ Finset.range (n*m), ∑ b ∈ Finset.range (n*m),
        μ (a/m) * μ (b/m) * max (f a) (f b) := by
  set T : ℕ → ℕ → ℤ := fun a b => μ (a/m) * μ (b/m) * max (f a) (f b) with hT
  have hterm : ∀ k ∈ Finset.range n, ∀ k' ∈ Finset.range n, ∀ j ∈ Finset.range m,
      ∀ j' ∈ Finset.range m,
      μ k * μ k' * max (f (m*k+j)) (f (m*k'+j')) = T (m*k+j) (m*k'+j') := by
    intro k _ k' _ j hj j' hj'
    rw [hT]
    simp only []
    rw [Nat.mul_add_div hm, Nat.div_eq_of_lt (Finset.mem_range.mp hj), Nat.add_zero,
        Nat.mul_add_div hm, Nat.div_eq_of_lt (Finset.mem_range.mp hj'), Nat.add_zero]
  have hstep1 : (∑ k ∈ Finset.range n, ∑ k' ∈ Finset.range n, ∑ j ∈ Finset.range m,
        ∑ j' ∈ Finset.range m, μ k * μ k' * max (f (m*k+j)) (f (m*k'+j')))
      = (∑ k ∈ Finset.range n, ∑ k' ∈ Finset.range n, ∑ j ∈ Finset.range m,
        ∑ j' ∈ Finset.range m, T (m*k+j) (m*k'+j')) := by
    apply Finset.sum_congr rfl; intro k hk
    apply Finset.sum_congr rfl; intro k' hk'
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro j' hj'
    exact hterm k hk k' hk' j hj j' hj'
  have hstep2 : (∑ k ∈ Finset.range n, ∑ k' ∈ Finset.range n, ∑ j ∈ Finset.range m,
        ∑ j' ∈ Finset.range m, T (m*k+j) (m*k'+j'))
      = (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range m, ∑ k' ∈ Finset.range n,
        ∑ j' ∈ Finset.range m, T (m*k+j) (m*k'+j')) := by
    apply Finset.sum_congr rfl; intro k _
    exact Finset.sum_comm
  rw [hstep1, hstep2, sum_grid_core n m hm T]

end Work.Cert.CJ2Grid
