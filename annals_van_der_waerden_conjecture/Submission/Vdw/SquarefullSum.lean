import Mathlib
import Submission.Commons.NumberTheory.Nat.squarefull_iff_exists_sq_mul_cube
import Submission.Vdw.CaseI
import Submission.Vdw.Omega

open scoped BigOperators

set_option autoImplicit false

/-!
# Case-I tail sums over squarefull discriminants (CI-4, discrete part)

The Case-I per-discriminant bound (`CaseIExact.perDiscriminant_exact_le`) is
`O(c^(ω(D)) · H^n / D)`; the Case-I assembly must sum this over the squarefull
`D` in the tail range.  This module carries the *purely discrete* content of
that summation (no real analysis — the analytic tail estimates come later):

* the parametrization bridge (`squarefull_iff_sq_mul_cube`,
  `squarefull_of_sq_mul_cube`) between the local `Squarefull` predicate and
  the commons representation `D = a²·b³`;
* the pointwise bound `cpow_omega_sq_mul_cube_le`
  (`c^(ω(a²b³)) ≤ c^(ω a)·c^(ω b)`) built on `omega_sq_mul_cube_le`;
* **`squarefull_sum_le_paramSum`**: for nonnegative `g`, the sum of `g D`
  over squarefull `D` with `Y < D ≤ Z` is at most the sum of `g (a²b³)` over
  all pairs `a,b ≤ Z` with `Y < a²b³ ≤ Z` — i.e. the squarefull sum is
  bounded by the corresponding `(a,b)`-parametrized double sum (each
  squarefull `D` has at least one representation, so it is counted at least
  once, with a nonnegative weight).

Everything here is in `namespace Submission.Vdw`.
-/

namespace Submission.Vdw

/-- Decidability of the local `Squarefull` predicate (classical). -/
noncomputable instance sqfullDecidable (N : ℕ) : Decidable (Squarefull N) := by
  classical
  infer_instance

/-- Local `Squarefull` (2-powerful) iff the commons parametrization
`∃ a b, Squarefree b ∧ N = a²b³` (for `N ≠ 0`). -/
theorem squarefull_iff_sq_mul_cube (N : ℕ) (hN : N ≠ 0) :
    Squarefull N ↔ ∃ a b : ℕ, Squarefree b ∧ N = a ^ 2 * b ^ 3 := by
  have h := Commons.NumberTheory.Nat.squarefull_iff_exists_sq_mul_cube N hN
  simpa [Squarefull, Powerful] using h

/-- `a²·b³` is squarefull (no condition on `a,b`). -/
theorem squarefull_of_sq_mul_cube (a b : ℕ) : Squarefull (a ^ 2 * b ^ 3) := by
  unfold Squarefull Powerful
  intro p pp hpd
  rcases (pp.dvd_mul.mp hpd) with hpa | hpb
  · have hpa' : p ∣ a := pp.dvd_of_dvd_pow hpa
    have hpsq : p ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd hpa' 2
    exact dvd_trans hpsq ⟨b ^ 3, by ring⟩
  · have hpb' : p ∣ b := pp.dvd_of_dvd_pow hpb
    have hpsq : p ^ 2 ∣ b ^ 3 := by
      exact dvd_trans (pow_dvd_pow_of_dvd hpb' 2) ⟨b, by ring⟩
    exact dvd_trans hpsq ⟨a ^ 2, by ring⟩

/-- `c^ω(a²·b³) ≤ c^ω(a) · c^ω(b)` for a real base `c ≥ 1`. -/
theorem cpow_omega_sq_mul_cube_le (c : ℝ) (hc : 1 ≤ c) (a b : ℕ) :
    c ^ (omega (a ^ 2 * b ^ 3)) ≤ c ^ omega a * c ^ omega b := by
  have hle : omega (a ^ 2 * b ^ 3) ≤ omega a + omega b := omega_sq_mul_cube_le a b
  calc
    c ^ (omega (a ^ 2 * b ^ 3)) ≤ c ^ (omega a + omega b) := pow_le_pow_right₀ hc hle
    _ = c ^ omega a * c ^ omega b := by rw [pow_add]

/-- If `a²·b³ ∈ Icc (Y+1) Z` then `a, b ∈ Icc 1 Z`. -/
lemma mem_Icc_sq_mul_cube {a b Y Z : ℕ} (hY : 1 ≤ Y)
    (h : a ^ 2 * b ^ 3 ∈ Finset.Icc (Y + 1) Z) :
    a ∈ Finset.Icc 1 Z ∧ b ∈ Finset.Icc 1 Z := by
  have h1 : a ^ 2 * b ^ 3 ≥ Y + 1 := (Finset.mem_Icc.mp h).1
  have h2 : a ^ 2 * b ^ 3 ≤ Z := (Finset.mem_Icc.mp h).2
  have hab_ne : a ^ 2 * b ^ 3 ≠ 0 := by omega
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hab_ne
    simp [ha0]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hab_ne
    simp [hb0]
  have ha1 : 1 ≤ a := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha0)
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb0)
  have hb3 : 1 ≤ b ^ 3 := le_trans hb1 (Nat.le_self_pow (by norm_num : (3 : ℕ) ≠ 0) b)
  have ha2 : 1 ≤ a ^ 2 := le_trans ha1 (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) a)
  have ha_sq_le : a ^ 2 ≤ a ^ 2 * b ^ 3 := by
    simpa using (Nat.mul_le_mul_left (a ^ 2) hb3)
  have hb_cb_le : b ^ 3 ≤ a ^ 2 * b ^ 3 := by
    simpa using (Nat.mul_le_mul_right (b ^ 3) ha2)
  have ha_le : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) a
  have hb_le : b ≤ b ^ 3 := Nat.le_self_pow (by norm_num : (3 : ℕ) ≠ 0) b
  refine ⟨Finset.mem_Icc.mpr ⟨ha1, le_trans ha_le (le_trans ha_sq_le h2)⟩,
    Finset.mem_Icc.mpr ⟨hb1, le_trans hb_le (le_trans hb_cb_le h2)⟩⟩

/-- A single term in the pair sum is nonnegative when `g` is nonnegative. -/
lemma sqMulCube_summand_nonneg (g : ℕ → ℝ) (hg : ∀ D : ℕ, 0 ≤ g D)
    (a b Y Z : ℕ) : 0 ≤ (if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then g (a ^ 2 * b ^ 3) else 0) := by
  classical
  by_cases h : Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z
  · simp [h, hg]
  · simp [h]

/-- **Squarefull sum ≤ parametrized double sum.**  For nonnegative `g`, the sum of
`g D` over squarefull `D` in the interval `(Y, Z]` is at most the sum of
`g (a²·b³)` over pairs `(a,b)` with `1 ≤ a, b ≤ Z` and `Y < a²·b³ ≤ Z`.  Each
squarefull `D ∈ (Y, Z]` is counted at least once on the right (its `a²b³`
parametrization), and the right-hand side is a sum of nonnegative terms. -/
theorem squarefull_sum_le_paramSum (Y Z : ℕ) (hY : 1 ≤ Y) (g : ℕ → ℝ)
    (hg : ∀ D : ℕ, 0 ≤ g D) :
    (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then g D else 0) ≤
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then g (a ^ 2 * b ^ 3) else 0) := by
  classical
  let P : Finset (ℕ × ℕ) := (Finset.Icc 1 Z).product (Finset.Icc 1 Z)
  have hpt : ∀ D ∈ Finset.Icc (Y + 1) Z, (if Squarefull D then g D else 0) ≤
      (∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
    intro D hD
    by_cases hsq : Squarefull D
    · have hD0 : D ≠ 0 := by
        have hDge : Y + 1 ≤ D := (Finset.mem_Icc.mp hD).1
        omega
      rcases (squarefull_iff_sq_mul_cube D hD0).mp hsq with ⟨a, b, hb, hDab⟩
      have hprod_in : a ^ 2 * b ^ 3 ∈ Finset.Icc (Y + 1) Z := by
        rw [← hDab]
        exact hD
      have habB : a ∈ Finset.Icc 1 Z ∧ b ∈ Finset.Icc 1 Z := mem_Icc_sq_mul_cube hY hprod_in
      let p0 : ℕ × ℕ := (a, b)
      have hp0 : p0 ∈ P := Finset.mem_product.mpr habB
      have hpd : p0.1 ^ 2 * p0.2 ^ 3 = D := by
        dsimp [p0]
        exact hDab.symm
      have hnonneg : ∀ p ∈ P,
          0 ≤ (if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
        intro p hp
        by_cases hpp : p.1 ^ 2 * p.2 ^ 3 = D
        · simp [hpp, hg]
        · simp [hpp]
      calc
        (if Squarefull D then g D else 0) = g D := by simp [hsq]
        _ = (if p0.1 ^ 2 * p0.2 ^ 3 = D then g D else 0) := by simp [hpd]
        _ ≤ (∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
          exact Finset.single_le_sum hnonneg hp0
    · calc
        (if Squarefull D then g D else 0) = 0 := by simp [hsq]
        _ ≤ (∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
          exact Finset.sum_nonneg (by
            intro p hp
            by_cases hpp : p.1 ^ 2 * p.2 ^ 3 = D
            · simp [hpp, hg]
            · simp [hpp])
  have hsum_le : (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then g D else 0) ≤
      (∑ D ∈ Finset.Icc (Y + 1) Z, ∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
    exact Finset.sum_le_sum hpt
  have hswap : (∑ D ∈ Finset.Icc (Y + 1) Z, ∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) =
      (∑ p ∈ P, ∑ D ∈ Finset.Icc (Y + 1) Z, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
    rw [Finset.sum_comm]
  have hstep1 : (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then g D else 0) ≤
      (∑ p ∈ P, ∑ D ∈ Finset.Icc (Y + 1) Z, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) := by
    rw [← hswap]
    exact hsum_le
  have hint : ∀ p ∈ P,
      (∑ D ∈ Finset.Icc (Y + 1) Z, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) =
        (if p.1 ^ 2 * p.2 ^ 3 ∈ Finset.Icc (Y + 1) Z then g (p.1 ^ 2 * p.2 ^ 3) else 0) := by
    intro p hp
    let m := p.1 ^ 2 * p.2 ^ 3
    have hrew : ∀ D : ℕ, (if m = D then g D else 0) = (if m = D then g m else 0) := by
      intro D
      by_cases h : m = D
      · simp [h]
      · simp [h]
    calc
      (∑ D ∈ Finset.Icc (Y + 1) Z, if m = D then g D else 0)
          = (∑ D ∈ Finset.Icc (Y + 1) Z, if m = D then g m else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        exact hrew D
      _ = (if m ∈ Finset.Icc (Y + 1) Z then g m else 0) := by
        rw [Finset.sum_ite_eq]
  have hstep2 : (∑ p ∈ P, ∑ D ∈ Finset.Icc (Y + 1) Z, if p.1 ^ 2 * p.2 ^ 3 = D then g D else 0) =
      (∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 ∈ Finset.Icc (Y + 1) Z then g (p.1 ^ 2 * p.2 ^ 3) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hint p hp
  have hstep3 :
      (∑ p ∈ P, if p.1 ^ 2 * p.2 ^ 3 ∈ Finset.Icc (Y + 1) Z then g (p.1 ^ 2 * p.2 ^ 3) else 0) =
        (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
          if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then g (a ^ 2 * b ^ 3) else 0) := by
    rw [← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro p hp
    have hmem_iff {m Y Z : ℕ} : m ∈ Finset.Icc (Y + 1) Z ↔ Y < m ∧ m ≤ Z := by
      constructor
      · intro h
        exact ⟨Nat.lt_of_succ_le (Finset.mem_Icc.mp h).1, (Finset.mem_Icc.mp h).2⟩
      · intro h
        exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt h.1, h.2⟩
    have hif : (if p.1 ^ 2 * p.2 ^ 3 ∈ Finset.Icc (Y + 1) Z then g (p.1 ^ 2 * p.2 ^ 3) else 0) =
        (if Y < p.1 ^ 2 * p.2 ^ 3 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ Z then g (p.1 ^ 2 * p.2 ^ 3) else 0) := by
      by_cases hc : p.1 ^ 2 * p.2 ^ 3 ∈ Finset.Icc (Y + 1) Z
      · have hc' : Y < p.1 ^ 2 * p.2 ^ 3 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ Z := (hmem_iff).mp hc
        simp [hc, hc']
      · have hc' : ¬(Y < p.1 ^ 2 * p.2 ^ 3 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ Z) := fun h => hc (hmem_iff.mpr h)
        simp [hc, hc']
    exact hif
  exact le_trans (le_trans hstep1 (le_of_eq hstep2)) (le_of_eq hstep3)


/-- Nonnegativity of the per-`D` weight `c^ω(D)/D` for `c ≥ 1`. -/
lemma cpow_omega_div_nonneg (c : ℝ) (hc : 1 ≤ c) (D : ℕ) : 0 ≤ c ^ omega D / (D : ℝ) := by
  positivity

/-- Pointwise: under the pair condition, replacing `c^ω(a²b³)` by `c^ω(a)·c^ω(b)`
only increases the term (same denominator). -/
lemma sqMulCube_pair_term_le (c : ℝ) (hc : 1 ≤ c) (a b Y Z : ℕ) :
    (if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then c ^ (omega (a ^ 2 * b ^ 3)) / ((a ^ 2 * b ^ 3 : ℕ) : ℝ) else 0)
      ≤ (if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          c ^ omega a * c ^ omega b / ((a ^ 2 * b ^ 3 : ℕ) : ℝ) else 0) := by
  classical
  by_cases h : Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z
  · have hden_pos : 0 < (a ^ 2 * b ^ 3 : ℝ) := by
      have hprod : 0 < a ^ 2 * b ^ 3 := by
        rcases h with ⟨hYp, _⟩
        omega
      exact_mod_cast hprod
    have hnle : c ^ (omega (a ^ 2 * b ^ 3)) ≤ c ^ omega a * c ^ omega b :=
      cpow_omega_sq_mul_cube_le c hc a b
    simp [h, div_le_div_of_nonneg_right hnle (le_of_lt hden_pos)]
  · simp [h]

/-- **CI-4 discrete core**: with weight `g(D) = c^ω(D)/D`, the squarefull sum over
`(Y, Z]` is at most the parametrized pair double-sum with the separated weights
`c^ω(a)·c^ω(b)/(a²b³)`. -/
theorem squarefull_tail_cpow_le_pairWeight (c : ℝ) (hc : 1 ≤ c) (Y Z : ℕ) (hY : 1 ≤ Y) :
    (∑ D ∈ Finset.Icc (Y + 1) Z, if Squarefull D then c ^ omega D / (D : ℝ) else 0) ≤
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          c ^ omega a * c ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) := by
  have h1 := squarefull_sum_le_paramSum (Y := Y) (Z := Z) hY (fun D => c ^ omega D / (D : ℝ))
    (cpow_omega_div_nonneg c hc)
  have h2 : (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          c ^ (omega (a ^ 2 * b ^ 3)) / ((a ^ 2 * b ^ 3 : ℕ) : ℝ) else 0) ≤
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          c ^ omega a * c ^ omega b / ((a ^ 2 * b ^ 3 : ℕ) : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact sqMulCube_pair_term_le c hc a b Y Z
  have hcast : ∀ a b : ℕ, (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) = (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by
    intro a b
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  have h3 : (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          c ^ omega a * c ^ omega b / ((a ^ 2 * b ^ 3 : ℕ) : ℝ) else 0) ≤
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z then
          c ^ omega a * c ^ omega b / ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) else 0) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    by_cases hc1 : Y < a ^ 2 * b ^ 3 ∧ a ^ 2 * b ^ 3 ≤ Z
    · rw [if_pos hc1, if_pos hc1]
      rw [hcast a b]
    · simp [hc1]
  exact le_trans (le_trans h1 h2) h3

end Submission.Vdw

