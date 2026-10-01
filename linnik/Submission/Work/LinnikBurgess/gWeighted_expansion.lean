import Mathlib

/-!
# The `g`-weighted divisor expansion

For `0 < g` we compare two sums over triples.

The left-hand side sums `∏_l √(gcd m (v l))` over those `v : Fin 3 → Fin H` that are
pointwise non-zero and satisfy `g ∣ ∏_l v l`.  The right-hand side sums, over all
factorisations `g = a 0 * a 1 * a 2` into divisors `a l` of `g`, the product over `l` of the
single-coordinate sums `∑_{u ≠ 0, a l ∣ u} √(gcd m u)`.

The point of the inequality is that every admissible `v` admits *some* factorisation of `g`
with `a l ∣ v l` for all `l` (`exists_fin3_decomp_aux` below); distributing the indicator of
that existence over the factorisations and expanding the resulting product of sums
(`Fintype.prod_sum`) gives the estimate.  This is the divisor expansion used in the
Linnik/Burgess argument bounding the weighted count of triples of residues with `g ∣ v 0 v 1 v 2`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- `√(gcd m u)`, as a function of the natural number `u`. -/
private noncomputable def gwSqrt (m u : ℕ) : ℝ := Real.sqrt ((Nat.gcd m u : ℕ) : ℝ)

/-- The single-coordinate weight attached to a pair `(d, u)`: it equals `√(gcd m u)` when
`d ∣ u` and `u ≠ 0`, and `0` otherwise. -/
private noncomputable def gwTerm (m d u : ℕ) : ℝ :=
  if d ∣ u then (if u ≠ 0 then gwSqrt m u else 0) else 0

private lemma gwTerm_nonneg (m d u : ℕ) : 0 ≤ gwTerm m d u := by
  rw [gwTerm]; split_ifs <;> simp [gwSqrt, Real.sqrt_nonneg]

/-- Cancellation of `gcd`: if `0 < d` and `d ∣ x * y`, then the part of `d` coprime to `x`
divides `y`. -/
private lemma dvd_div_gcd_of_dvd_mul_aux {d x y : ℕ} (hd : 0 < d) (h : d ∣ x * y) :
    d / d.gcd x ∣ y := by
  have hgpos : 0 < d.gcd x := Nat.gcd_pos_of_pos_left x hd
  have h1 : d.gcd x * (d / d.gcd x) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d x)
  have h2 : d.gcd x * (x / d.gcd x) = x := Nat.mul_div_cancel' (Nat.gcd_dvd_right d x)
  have h3 : d.gcd x * (d / d.gcd x) ∣ d.gcd x * ((x / d.gcd x) * y) := by
    rw [h1, ← mul_assoc, h2]
    exact h
  have h4 : d / d.gcd x ∣ (x / d.gcd x) * y := (Nat.mul_dvd_mul_iff_left hgpos).mp h3
  exact (Nat.coprime_div_gcd_div_gcd hgpos).dvd_of_dvd_mul_left h4

/-- Every `v : Fin 3 → ℕ` whose product is a multiple of `0 < g` splits: there is an ordered
factorisation `g = a 0 * a 1 * a 2` of `g` with `a l ∣ v l` for each `l`. -/
private lemma exists_fin3_decomp_aux {g : ℕ} (hg : 0 < g) (v : Fin 3 → ℕ)
    (h : g ∣ ∏ l : Fin 3, v l) :
    ∃ a : Fin 3 → ℕ, (∏ l : Fin 3, a l = g) ∧ ∀ l : Fin 3, a l ∣ v l := by
  rw [Fin.prod_univ_three, mul_assoc] at h
  have hA : g / g.gcd (v 0) ∣ v 1 * v 2 := dvd_div_gcd_of_dvd_mul_aux hg h
  have hggpos : 0 < g.gcd (v 0) := Nat.gcd_pos_of_pos_left (v 0) hg
  have hggle : g.gcd (v 0) ≤ g := Nat.gcd_le_left (v 0) hg
  have hg1pos : 0 < g / g.gcd (v 0) := Nat.div_pos hggle hggpos
  have hB : (g / g.gcd (v 0)) / (g / g.gcd (v 0)).gcd (v 1) ∣ v 2 :=
    dvd_div_gcd_of_dvd_mul_aux hg1pos hA
  refine ⟨![g.gcd (v 0), (g / g.gcd (v 0)).gcd (v 1),
      (g / g.gcd (v 0)) / (g / g.gcd (v 0)).gcd (v 1)], ?_, ?_⟩
  · rw [Fin.prod_univ_three, mul_assoc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left (g / g.gcd (v 0)) (v 1)),
        Nat.mul_div_cancel' (Nat.gcd_dvd_left g (v 0))]
  · intro l
    fin_cases l <;> simp [Nat.gcd_dvd_right, hB]

theorem gWeighted_expansion {m g H : ℕ} (hg : 0 < g) : (∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ)) then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ) : ℕ)) : ℝ) else (0:ℝ))) ≤ ∑ a ∈ (Fintype.piFinset fun _ : Fin 3 => g.divisors).filter (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g), ∏ l : Fin 3, ∑ u : Fin H, (if (a l) ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ) : ℕ)) : ℝ) else 0) else 0) := by
  classical
  set A : Finset (Fin 3 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter
      (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g) with hA
  have key : ∀ v : Fin 3 → Fin H,
      (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
        then ∏ l : Fin 3, gwSqrt m (v l : ℕ) else (0:ℝ))
      ≤ ∑ a ∈ A, ∏ l : Fin 3, gwTerm m (a l) (v l : ℕ) := by
    intro v
    by_cases hc : (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
    · rw [if_pos hc]
      obtain ⟨a0, hprod, hdvd⟩ := exists_fin3_decomp_aux hg (fun l => (v l : ℕ)) hc.2
      have ha0A : a0 ∈ A := by
        rw [hA]
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
        exact ⟨fun l => ⟨hprod ▸ Finset.dvd_prod_of_mem a0 (Finset.mem_univ l), hg.ne'⟩, hprod⟩
      have hle : ∏ l : Fin 3, gwTerm m (a0 l) (v l : ℕ)
          ≤ ∑ a ∈ A, ∏ l : Fin 3, gwTerm m (a l) (v l : ℕ) :=
        Finset.single_le_sum
          (fun a _ => Finset.prod_nonneg (fun l _ => gwTerm_nonneg m (a l) (v l : ℕ))) ha0A
      refine le_trans (le_of_eq ?_) hle
      apply Finset.prod_congr rfl
      intro l _
      simp [gwTerm, hdvd l, hc.1 l]
    · rw [if_neg hc]
      exact Finset.sum_nonneg
        (fun a _ => Finset.prod_nonneg (fun l _ => gwTerm_nonneg m (a l) (v l : ℕ)))
  change (∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
        then ∏ l : Fin 3, gwSqrt m (v l : ℕ) else (0:ℝ)))
      ≤ ∑ a ∈ A, ∏ l : Fin 3, ∑ u : Fin H, gwTerm m (a l) (u : ℕ)
  calc (∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
          then ∏ l : Fin 3, gwSqrt m (v l : ℕ) else (0:ℝ)))
      ≤ ∑ v : Fin 3 → Fin H, ∑ a ∈ A, ∏ l : Fin 3, gwTerm m (a l) (v l : ℕ) :=
        Finset.sum_le_sum (fun v _ => key v)
    _ = ∑ a ∈ A, ∑ v : Fin 3 → Fin H, ∏ l : Fin 3, gwTerm m (a l) (v l : ℕ) := by
        rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∏ l : Fin 3, ∑ u : Fin H, gwTerm m (a l) (u : ℕ) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (Fintype.prod_sum (fun l : Fin 3 => fun u : Fin H => gwTerm m (a l) (u : ℕ))).symm

end Work.LinnikBurgess
