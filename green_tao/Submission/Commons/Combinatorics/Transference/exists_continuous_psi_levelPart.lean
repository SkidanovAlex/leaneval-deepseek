import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- A trapezoid bump: equals `1` on `[a+δ, b-δ]`, `0` outside `[a,b]`, and is linear
(hence continuous) on the two transition intervals. -/
private noncomputable def trap (a b δ : ℝ) (t : ℝ) : ℝ :=
  min 1 (max 0 ((t - a) / δ)) * min 1 (max 0 ((b - t) / δ))

private lemma continuous_trap (a b δ : ℝ) : Continuous (trap a b δ) := by
  unfold trap
  apply Continuous.mul
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const ((continuous_id.sub continuous_const).div_const δ))
  · exact Continuous.min continuous_const
      (Continuous.max continuous_const ((continuous_const.sub continuous_id).div_const δ))

private lemma trap_nonneg (a b δ : ℝ) (t : ℝ) : 0 ≤ trap a b δ t := by
  unfold trap
  apply mul_nonneg <;> exact le_min zero_le_one (le_max_left 0 _)

private lemma trap_le_one (a b δ : ℝ) (t : ℝ) : trap a b δ t ≤ 1 := by
  unfold trap
  have h1 : min 1 (max 0 ((t - a) / δ)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (max 0 ((b - t) / δ)) ≤ 1 := min_le_left _ _
  have h1' : 0 ≤ min 1 (max 0 ((t - a) / δ)) := le_min zero_le_one (le_max_left 0 _)
  have h2' : 0 ≤ min 1 (max 0 ((b - t) / δ)) := le_min zero_le_one (le_max_left 0 _)
  calc min 1 (max 0 ((t - a) / δ)) * min 1 (max 0 ((b - t) / δ))
      ≤ 1 * 1 := mul_le_mul h1 h2 h2' zero_le_one
    _ = 1 := by norm_num

private lemma trap_eq_one {a b δ t : ℝ} (hδ : 0 < δ) (h1 : a + δ ≤ t) (h2 : t ≤ b - δ) :
    trap a b δ t = 1 := by
  have hx : 1 ≤ (t - a) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hy : 1 ≤ (b - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [trap, max_eq_right (le_trans zero_le_one hx), max_eq_right (le_trans zero_le_one hy),
    min_eq_left hx, min_eq_left hy, mul_one]

private lemma trap_eq_zero_of_le {a b δ t : ℝ} (hδ : 0 < δ) (h : t ≤ a) : trap a b δ t = 0 := by
  have h1 : (t - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [trap, max_eq_left h1, min_eq_right zero_le_one, zero_mul]

private lemma trap_eq_zero_of_ge {a b δ t : ℝ} (hδ : 0 < δ) (h : b ≤ t) : trap a b δ t = 0 := by
  have h1 : (b - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [trap, max_eq_left h1, min_eq_right zero_le_one, mul_zero]

/-- Core approximation step, with the level index of the target point passed as a real `c`. -/
private lemma approx_levelPart {X : Type*} [Fintype X] [DecidableEq X]
    (G : X → ℝ) (ν : X → ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hν : ∀ x, 0 ≤ ν x) {α : ℝ} {T : Finset X}
    (hT : ∀ y, (∃ n : ℤ, |(G y - α) / ε - n| ≤ η) → y ∈ T) (c : ℝ) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ t, 0 ≤ φ t) ∧ (∀ t, φ t ≤ 1) ∧
      ∑ y, (ν y + 1) * |(if ⌊(G y - α) / ε⌋ = ⌊(c - α) / ε⌋ then (1 : ℝ) else 0) - φ (G y)|
        ≤ ∑ y ∈ T, (ν y + 1) := by
  set k : ℤ := ⌊(c - α) / ε⌋ with hk
  set δ : ℝ := η * ε with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  set a : ℝ := α + (k : ℝ) * ε - δ with hadef
  set b : ℝ := α + (k : ℝ) * ε + ε + δ with hbdef
  refine ⟨trap a b δ, continuous_trap a b δ, fun t => trap_nonneg a b δ t,
    fun t => trap_le_one a b δ t, ?_⟩
  have hT_off : ∀ y, y ∉ T → ∀ n : ℤ, η < |(G y - α) / ε - n| := by
    intro y hy n
    exact lt_of_not_ge (fun h => hy (hT y ⟨n, h⟩))
  have hon : ∀ y, ⌊(G y - α) / ε⌋ = k → trap a b δ (G y) = 1 := by
    intro y hyk
    apply trap_eq_one hδ
    · rw [hadef]
      have h := Int.floor_le ((G y - α) / ε)
      rw [hyk, le_div_iff₀ hε] at h
      linarith
    · rw [hbdef]
      have h := Int.lt_floor_add_one ((G y - α) / ε)
      rw [hyk, div_lt_iff₀ hε] at h
      nlinarith
  have hoff : ∀ y, y ∉ T →
      trap a b δ (G y) = (if ⌊(G y - α) / ε⌋ = k then (1 : ℝ) else 0) := by
    intro y hyT
    by_cases hyk : ⌊(G y - α) / ε⌋ = k
    · rw [if_pos hyk]; exact hon y hyk
    · rw [if_neg hyk]
      rcases lt_or_gt_of_ne hyk with hlt | hgt
      · apply trap_eq_zero_of_le hδ
        have hτ : (G y - α) / ε < (k : ℝ) := by
          have hj1 : (⌊(G y - α) / ε⌋ : ℝ) + 1 ≤ (k : ℝ) := by
            have : ⌊(G y - α) / ε⌋ + 1 ≤ k := by omega
            exact_mod_cast this
          exact lt_of_lt_of_le (Int.lt_floor_add_one _) hj1
        have hk' : (G y - α) / ε < (k : ℝ) - η := by
          have h := hT_off y hyT k
          rw [abs_of_neg (by linarith)] at h
          linarith
        have h2 : G y - α < ((k : ℝ) - η) * ε := by
          rw [div_lt_iff₀ hε] at hk'; exact hk'
        rw [hadef, hδdef]
        nlinarith [h2]
      · apply trap_eq_zero_of_ge hδ
        have hτ : (k : ℝ) + 1 ≤ (G y - α) / ε := by
          have hj1 : (k : ℝ) + 1 ≤ (⌊(G y - α) / ε⌋ : ℝ) := by
            have : k + 1 ≤ ⌊(G y - α) / ε⌋ := by omega
            exact_mod_cast this
          exact le_trans hj1 (Int.floor_le _)
        have hk' : (k : ℝ) + 1 + η < (G y - α) / ε := by
          have h := hT_off y hyT (k + 1)
          push_cast at h
          rw [abs_of_nonneg (by linarith)] at h
          linarith
        have h2 : ((k : ℝ) + 1 + η) * ε < G y - α := by
          rw [lt_div_iff₀ hε] at hk'; exact hk'
        rw [hbdef, hδdef]
        nlinarith [h2]
  have hle : ∀ y, (ν y + 1) * |(if ⌊(G y - α) / ε⌋ = k then (1 : ℝ) else 0) - trap a b δ (G y)|
      ≤ (if y ∈ T then (ν y + 1) else 0) := by
    intro y
    by_cases hy : y ∈ T
    · rw [if_pos hy]
      apply mul_le_of_le_one_right (by linarith [hν y])
      have h1 : (0 : ℝ) ≤ trap a b δ (G y) := trap_nonneg _ _ _ _
      have h2 : trap a b δ (G y) ≤ 1 := trap_le_one _ _ _ _
      by_cases hyk : ⌊(G y - α) / ε⌋ = k
      · rw [if_pos hyk, abs_of_nonneg (by linarith)]
        linarith
      · rw [if_neg hyk, zero_sub, abs_neg, abs_of_nonneg h1]
        exact h2
    · rw [if_neg hy, hoff y hy, sub_self, abs_zero, mul_zero]
  calc ∑ y, (ν y + 1) * |(if ⌊(G y - α) / ε⌋ = k then (1 : ℝ) else 0) - trap a b δ (G y)|
      ≤ ∑ y, (if y ∈ T then (ν y + 1) else 0) := Finset.sum_le_sum (fun y _ => hle y)
    _ = ∑ y ∈ T, (ν y + 1) := by
        rw [Finset.sum_ite_mem]
        simp

/-- Strengthening of `exists_psi_levelPart`: the approximating function `Ψ` can be taken to
be a global continuous function `φ` composed with `G`
(`Ψ y = φ (G y)`), as in the construction of the generalised Bohr `σ`-algebras. -/
theorem exists_continuous_psi_levelPart {X : Type*} [Fintype X] [DecidableEq X] (G : X → ℝ)
    (ν : X → ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hν : ∀ x, 0 ≤ ν x)
    {α : ℝ} {T : Finset X} (hT : ∀ y, (∃ n : ℤ, |(G y - α) / ε - n| ≤ η) → y ∈ T) :
    ∀ x : X, ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ t, 0 ≤ φ t) ∧ (∀ t, φ t ≤ 1) ∧
      ∑ y, (ν y + 1) * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(G y - α) / ε⌋ = ⌊(G x - α) / ε⌋) then (1 : ℝ) else 0) - φ (G y)|
        ≤ ∑ y ∈ T, (ν y + 1) := by
  intro x
  obtain ⟨φ, hc, h0, h1, hbound⟩ := approx_levelPart G ν hε hη hη1 hν hT (G x)
  refine ⟨φ, hc, h0, h1, ?_⟩
  calc ∑ y, (ν y + 1) * |(if y ∈ Finset.univ.filter
          (fun y => ⌊(G y - α) / ε⌋ = ⌊(G x - α) / ε⌋) then (1 : ℝ) else 0) - φ (G y)|
      = ∑ y, (ν y + 1) *
          |(if ⌊(G y - α) / ε⌋ = ⌊(G x - α) / ε⌋ then (1 : ℝ) else 0) - φ (G y)| := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ ≤ ∑ y ∈ T, (ν y + 1) := hbound

end Commons.Combinatorics.Transference