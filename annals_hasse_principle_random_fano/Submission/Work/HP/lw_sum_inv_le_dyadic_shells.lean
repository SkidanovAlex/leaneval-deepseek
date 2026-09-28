import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs

/-!
# Dyadic shell comparison for `∑ 1/‖a‖`

Let `P` be a finite set of integer vectors all of whose Euclidean norms `eNorm a = ‖a‖`
satisfy `1 ≤ ‖a‖ ≤ T`, where `T ≥ 1` and `T < 2^(J+1)`.  The main estimate of this file
bounds the harmonic-type sum `∑_{a ∈ P} 1/‖a‖` by the weighted dyadic shell counts

`∑_{a ∈ P} 1/‖a‖ ≤ ∑_{j ≤ J} (2^(j+1)/T) · #{a ∈ P : ‖a‖ ≤ T/2^j}`.

The proof splits into two independent halves.

* `lw_inv_le_dyadic_shell_weight` is the purely real pointwise inequality: for
  `1 ≤ x ≤ T` and `T < 2^(J+1)`, the shells `j ≤ J` containing `x` (i.e. those with
  `x ≤ T/2^j`) charge it a total weight of at least `1/x`.  Indeed the shells containing
  `x` are an initial segment `{0, …, k}` of `{0, …, J}`; the single shell `j = k`
  already contributes `2^(k+1)/T`, and `k` being maximal forces `2^(k+1) > T/x`
  (either `k = J`, where `T/x ≤ T < 2^(J+1)`, or `k < J`, where `k+1` is a shell
  *not* containing `x`).

* `lw_dyadic_shell_sum_rewrite` exchanges the double sum: the shell sum of the counts
  `#{a ∈ P : ‖a‖ ≤ T/2^j}` becomes the sum over `a ∈ P` of the total shell weight
  charged to `a`.

The main theorem is then the pointwise application of the first fact inside the
reindexed sum, after rewriting the `finsum` over the finite set `P` as a `Finset` sum.
-/

namespace Work.HP

open Finset

/-- **Dyadic shell weight.**  If `1 ≤ x ≤ T`, `1 ≤ T` and `T < 2^(J+1)`, then the total
weight `∑_{j ≤ J} [x ≤ T/2^j] · 2^(j+1)/T` of the dyadic shells containing `x` is at
least `1/x`. -/
theorem lw_inv_le_dyadic_shell_weight {x T : ℝ} (hx1 : 1 ≤ x) (hxT : x ≤ T) (hT : 1 ≤ T)
    {J : ℕ} (hJ : T < (2:ℝ) ^ (J + 1)) :
    1 / x ≤ ∑ j ∈ Finset.range (J + 1),
      (if x ≤ T / (2:ℝ) ^ j then (2:ℝ) ^ (j + 1) / T else 0) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  -- the shells in `{0, …, J}` containing `x`
  let K : Finset ℕ := (Finset.range (J + 1)).filter (fun j => x ≤ T / (2:ℝ)^j)
  have hmem : ∀ j, j ∈ K ↔ j ≤ J ∧ x ≤ T / (2:ℝ)^j := by
    intro j
    show j ∈ (Finset.range (J + 1)).filter (fun j => x ≤ T / (2:ℝ)^j) ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact ⟨by omega, h.2⟩
    · intro h; exact ⟨by omega, h.2⟩
  have h0 : 0 ∈ K := by
    rw [hmem]; exact ⟨Nat.zero_le _, by simpa using hxT⟩
  have hne : K.Nonempty := ⟨0, h0⟩
  -- `K` is nonempty, and the shells containing `x` form an initial segment
  let m : ℕ := K.max' hne
  have hmK : m ∈ K := Finset.max'_mem K hne
  have hmJ : m ≤ J := ((hmem m).mp hmK).1
  have hsum_eq : ∑ j ∈ Finset.range (J + 1),
        (if x ≤ T / (2:ℝ) ^ j then (2:ℝ) ^ (j + 1) / T else 0)
      = ∑ j ∈ K, (2:ℝ) ^ (j + 1) / T := by
    show _ = ∑ j ∈ (Finset.range (J + 1)).filter (fun j => x ≤ T / (2:ℝ)^j), _
    exact (Finset.sum_filter (fun j => x ≤ T / (2:ℝ) ^ j)
      (fun j => (2:ℝ) ^ (j + 1) / T)).symm
  rw [hsum_eq]
  -- the single shell `j = m` already suffices
  have hsingle : (2:ℝ)^(m+1)/T ≤ ∑ j ∈ K, (2:ℝ)^(j+1)/T :=
    Finset.single_le_sum (f := fun j => (2:ℝ)^(j+1)/T)
      (fun i _ => div_nonneg (by positivity) hT0.le) hmK
  -- maximality of `m`: `2^(m+1) > T/x`
  have hkey : T / x < (2:ℝ)^(m+1) := by
    rcases lt_or_eq_of_le hmJ with hlt | heq
    · have hnotK : m + 1 ∉ K := by
        intro h
        have hle : m + 1 ≤ m := Finset.le_max' K (m+1) h
        omega
      have hnot : ¬ (x ≤ T / (2:ℝ)^(m+1)) := by
        intro h
        exact hnotK ((hmem (m+1)).mpr ⟨by omega, h⟩)
      have hlt2 : T / (2:ℝ)^(m+1) < x := not_le.mp hnot
      have hpos : (0:ℝ) < (2:ℝ)^(m+1) := by positivity
      have hx2 : T < x * (2:ℝ)^(m+1) := (div_lt_iff₀ hpos).mp hlt2
      rw [div_lt_iff₀ hx0]
      linarith
    · rw [heq]
      have hle : T / x ≤ T := by
        rw [div_le_iff₀ hx0]; nlinarith
      linarith
  have hfinal : 1 / x ≤ (2:ℝ)^(m+1)/T := by
    have h1 : T / x ≤ (2:ℝ)^(m+1) := le_of_lt hkey
    have h2 : (T/x)/T ≤ (2:ℝ)^(m+1)/T := div_le_div_of_nonneg_right h1 hT0.le
    have h3 : (T / x) / T = 1 / x := by
      rw [div_div, mul_comm x T, ← div_div, div_self (ne_of_gt hT0)]
    rwa [h3] at h2
  linarith

/-- **Shell reindexing.**  The dyadic shell sum of the counts `#{a ∈ P : eNorm a ≤ T/2^j}`
equals the sum over `a ∈ P` of the total shell weight charged to `a`; both sides are the
same double sum, read in the two possible orders. -/
theorem lw_dyadic_shell_sum_rewrite {ι : Type} [Fintype ι] (P : Set (ι → ℤ)) (hP : P.Finite)
    (T : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), ((2:ℝ) ^ (j + 1) / T) *
        (({a ∈ P | eNorm a ≤ T / (2:ℝ) ^ j} : Set (ι → ℤ)).ncard : ℝ))
      = ∑ a ∈ hP.toFinset, ∑ j ∈ Finset.range (J + 1),
          (if eNorm a ≤ T / (2:ℝ) ^ j then (2:ℝ) ^ (j + 1) / T else 0) := by
  classical
  -- the shell is a subset of the finite set `P`, so its `ncard` is a `Finset` cardinality
  have hnc : ∀ j, (({a ∈ P | eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
      = ((hP.toFinset.filter (fun a => eNorm a ≤ T / (2:ℝ)^j)).card : ℝ) := by
    intro j
    have hset : ({a ∈ P | eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ))
        = ↑(hP.toFinset.filter (fun a => eNorm a ≤ T / (2:ℝ)^j)) := by
      ext a
      simp [Set.Finite.mem_toFinset hP]
    rw [hset, Set.ncard_coe_finset]
  calc ∑ j ∈ Finset.range (J + 1), ((2:ℝ)^(j+1)/T) *
          (({a ∈ P | eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
      = ∑ j ∈ Finset.range (J + 1), ((2:ℝ)^(j+1)/T) *
          ((hP.toFinset.filter (fun a => eNorm a ≤ T / (2:ℝ)^j)).card : ℝ) := by
        apply Finset.sum_congr rfl; intro j _; rw [hnc j]
    _ = ∑ j ∈ Finset.range (J + 1),
          ∑ a ∈ hP.toFinset.filter (fun a => eNorm a ≤ T / (2:ℝ)^j), (2:ℝ)^(j+1)/T := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ = ∑ j ∈ Finset.range (J + 1), ∑ a ∈ hP.toFinset,
          (if eNorm a ≤ T / (2:ℝ)^j then (2:ℝ)^(j+1)/T else 0) := by
        apply Finset.sum_congr rfl; intro j _
        exact Finset.sum_filter _ _
    _ = ∑ a ∈ hP.toFinset, ∑ j ∈ Finset.range (J + 1),
          (if eNorm a ≤ T / (2:ℝ)^j then (2:ℝ)^(j+1)/T else 0) := Finset.sum_comm

theorem lw_sum_inv_le_dyadic_shells {ι : Type} [Fintype ι] (P : Set (ι → ℤ)) (hP : P.Finite) {T : ℝ}
    (hT : 1 ≤ T) (h1 : ∀ a ∈ P, 1 ≤ eNorm a) (h2 : ∀ a ∈ P, eNorm a ≤ T) (J : ℕ)
    (hJ : T < (2:ℝ) ^ (J + 1)) :
    (∑ᶠ a ∈ P, 1 / eNorm a)
      ≤ ∑ j ∈ Finset.range (J + 1), ((2:ℝ) ^ (j + 1) / T) *
          (({a ∈ P | eNorm a ≤ T / (2:ℝ) ^ j} : Set (ι → ℤ)).ncard : ℝ) := by
  have hL : (∑ᶠ a ∈ P, 1 / eNorm a) = ∑ a ∈ hP.toFinset, 1 / eNorm a :=
    finsum_mem_eq_finite_toFinset_sum (fun a => 1 / eNorm a) hP
  rw [hL, lw_dyadic_shell_sum_rewrite P hP T J]
  apply Finset.sum_le_sum
  intro a ha
  have haP : a ∈ P := (Set.Finite.mem_toFinset hP).mp ha
  exact lw_inv_le_dyadic_shell_weight (h1 a haP) (h2 a haP) hT hJ

end Work.HP
