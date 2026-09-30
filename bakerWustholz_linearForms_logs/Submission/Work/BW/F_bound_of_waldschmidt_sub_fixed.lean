import Mathlib
import Submission.Work.BW.aligned_defs
import Submission.Work.BW.F_bound_wn_supported
import Submission.Work.BW.F_bound_Q_lower
import Submission.Work.BW.F_bound_arith_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Each modified height is at least `1 / [K : ℚ]`, hence positive. -/
private lemma hmod_pos_fixed {K : Type*} [Field K] [NumberField K] (β : K) (ℓ : ℂ) :
    0 < hmod β ℓ := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have h1 : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) := by positivity
  refine lt_of_lt_of_le h1 ?_
  rw [hmod]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem F_bound_of_waldschmidt_sub_fixed {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (α : Fin m → K) (ℓ : Fin m → ℂ) (J : Finset (Fin m)) (hJ : J.Nonempty)
    (hJm : J.card ≤ m - 1)
    (t : Fin m → ℤ) (hsupp : ∀ i, i ∉ J → t i = 0)
    (ht : ∀ j ∈ J, |((t j : ℤ) : ℝ)| ≤
      (9 * ((J.card : ℝ)) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (J.card) *
        (2 * Real.pi / (Module.finrank ℚ K : ℝ)) *
          ∏ i ∈ J.erase j, hmod (α i) (ℓ i))
    (r : Fin m → ℤ)
    (hr : wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m *
        (∏ i, hmod (α i) (ℓ i)) / (9 * (Module.finrank ℚ K : ℝ) ^ 2)) :
    2 * wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) t +
      2 * wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i) := by
  classical
  let d : ℝ := (Module.finrank ℚ K : ℝ)
  let P : ℝ := ∏ i ∈ J, hmod (α i) (ℓ i)
  let Q : ℝ := ∏ i ∈ Finset.univ \ J, hmod (α i) (ℓ i)
  let R : ℝ := ∏ i, hmod (α i) (ℓ i)
  let A : ℝ := (9 * (m : ℝ) * d ^ 3) ^ m
  let c : ℝ := 9 * d ^ 2
  have hd1 : 1 ≤ d := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2 : (1 : ℕ) ≤ Module.finrank ℚ K := by omega
    have h3 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast h2
    exact h3
  have hcpos : 0 < c := by
    have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
    show 0 < 9 * d ^ 2
    positivity
  have hn : 1 ≤ J.card := by
    have h := Finset.card_pos.mpr hJ
    omega
  have hQ' : (1 / d) ^ (m - J.card) ≤ Q := by
    show (1 / (Module.finrank ℚ K : ℝ)) ^ (m - J.card) ≤
      ∏ i ∈ Finset.univ \ J, hmod (α i) (ℓ i)
    exact F_bound_Q_lower α ℓ J
  have hpq : Q * P = R := by
    show (∏ i ∈ Finset.univ \ J, hmod (α i) (ℓ i)) * (∏ i ∈ J, hmod (α i) (ℓ i)) =
      ∏ i, hmod (α i) (ℓ i)
    exact Finset.prod_sdiff (Finset.subset_univ J)
  have hPnn : 0 ≤ P := by
    show 0 ≤ ∏ i ∈ J, hmod (α i) (ℓ i)
    exact Finset.prod_nonneg (fun i _ => (hmod_pos_fixed (α i) (ℓ i)).le)
  have hcore : 4 * Real.pi * (J.card : ℝ) * (9 * (J.card : ℝ) * d ^ 3) ^ (J.card) ≤
      A * Q * (1 - 2 / c) :=
    F_bound_arith_core (m := m) (n := J.card) (d := d) (Q := Q) hd1 hn hJm hQ'
  have hwns : 2 * wn (fun i => d * hmod (α i) (ℓ i)) t ≤
      4 * Real.pi * (J.card : ℝ) * (9 * (J.card : ℝ) * d ^ 3) ^ (J.card) * P :=
    F_bound_wn_supported α ℓ J t hsupp ht
  have hrr : wn (fun i => d * hmod (α i) (ℓ i)) r ≤ A * R / c := by
    show wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) r ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m *
        (∏ i, hmod (α i) (ℓ i)) / (9 * (Module.finrank ℚ K : ℝ) ^ 2)
    exact hr
  have h1 : 2 * wn (fun i => d * hmod (α i) (ℓ i)) t ≤ A * R * (1 - 2 / c) := by
    have hmul := mul_le_mul_of_nonneg_right hcore hPnn
    have heq : A * Q * (1 - 2 / c) * P = A * R * (1 - 2 / c) := by
      calc A * Q * (1 - 2 / c) * P = A * (Q * P) * (1 - 2 / c) := by ring
        _ = A * R * (1 - 2 / c) := by rw [hpq]
    linarith [hwns, hmul, heq]
  have h2 : 2 * wn (fun i => d * hmod (α i) (ℓ i)) r ≤ 2 * (A * R / c) :=
    mul_le_mul_of_nonneg_left hrr (by norm_num)
  have hkey : A * R * (1 - 2 / c) + 2 * (A * R / c) = A * R := by
    have hc : c ≠ 0 := hcpos.ne'
    field_simp
    ring
  calc 2 * wn (fun i => d * hmod (α i) (ℓ i)) t + 2 * wn (fun i => d * hmod (α i) (ℓ i)) r
      ≤ A * R * (1 - 2 / c) + 2 * (A * R / c) := add_le_add h1 h2
    _ = A * R := hkey

end Work.BW
