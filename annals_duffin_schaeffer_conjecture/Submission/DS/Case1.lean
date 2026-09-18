import Submission.DS.Structure

open scoped Nat ENNReal NNReal
open Set MeasureTheory
open DuffinSchaefferConjecture

/-!
# Theorem 2(b), Case 1 of the paper's §2 (Catlin's divergence theorem, easy regime)

If `ψ(q) ≥ 1/2` for infinitely many `q`, then every `α ∈ [0,1]` is within `ψ(q)/q` of
`a/q` for some `0 ≤ a ≤ q` for each of those `q`, so `𝒦 ψ = [0,1]`.
-/

namespace Submission.DS

/-- Dirichlet-style: every `x ∈ [0,1]` is within `1/(2q)` of `a/q` for some `0 ≤ a ≤ q`. -/
lemma near_frac (x : ℝ) (q : ℕ+) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ a : ℕ, a ≤ (q : ℕ) ∧ |x - (a : ℝ) / (q : ℝ)| ≤ (1 / 2 : ℝ) / (q : ℝ) := by
  let z : ℤ := ⌊x * (q : ℝ) + (1 / 2 : ℝ)⌋
  have hxq_pos : 0 < (q : ℝ) := by exact_mod_cast PNat.pos q
  have hz0 : 0 ≤ z := by
    dsimp [z]
    rw [Int.floor_nonneg]
    have hxq : 0 ≤ x * (q : ℝ) := mul_nonneg hx0 (le_of_lt hxq_pos)
    linarith
  have hz_le : z ≤ x * (q : ℝ) + (1 / 2 : ℝ) := by dsimp [z]; exact Int.floor_le _
  have hz_lt : x * (q : ℝ) + (1 / 2 : ℝ) < (z : ℝ) + 1 := by dsimp [z]; exact Int.lt_floor_add_one _
  have h1 : x * (q : ℝ) + (1 / 2 : ℝ) ≤ (q : ℝ) + (1 / 2 : ℝ) := by
    have hxq : x * (q : ℝ) ≤ 1 * (q : ℝ) := mul_le_mul_of_nonneg_right hx1 (le_of_lt hxq_pos)
    linarith
  have h2 : (q : ℝ) + (1 / 2 : ℝ) < (q : ℝ) + 1 := by linarith
  have hz_lt_q1 : (z : ℝ) < (q : ℝ) + 1 := lt_of_le_of_lt (le_trans hz_le h1) h2
  have hzltI : z < ((q : ℕ) : ℤ) + 1 := by exact_mod_cast hz_lt_q1
  have hzqI : z ≤ (q : ℕ) := Int.le_of_lt_add_one hzltI
  let a := z.toNat
  have hztoNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hztoNatR : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast hztoNat
  refine ⟨a, ?_, ?_⟩
  · have hgoal : (a : ℤ) ≤ ((q : ℕ) : ℤ) := by
      dsimp [a]
      rw [hztoNat]
      exact hzqI
    exact_mod_cast hgoal
  · have hA : x * (q : ℝ) - (a : ℝ) < 1 / 2 := by
      have hh : x * (q : ℝ) + (1 / 2 : ℝ) < (a : ℝ) + 1 := by
        simpa [a, hztoNatR] using hz_lt
      linarith
    have hB : (a : ℝ) - x * (q : ℝ) ≤ 1 / 2 := by
      have hh : (a : ℝ) ≤ x * (q : ℝ) + (1 / 2 : ℝ) := by
        simpa [a, hztoNatR] using hz_le
      linarith
    have hmain : |x * (q : ℝ) - (a : ℝ)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |x - (a : ℝ) / (q : ℝ)| = |(x * (q : ℝ) - (a : ℝ)) / (q : ℝ)| := by
        congr 1
        field_simp [hxq_pos.ne']
      _ = |x * (q : ℝ) - (a : ℝ)| / (q : ℝ) := by
        rw [abs_div]
        rw [abs_of_pos hxq_pos]
      _ ≤ (1 / 2 : ℝ) / (q : ℝ) := by
        exact div_le_div_of_nonneg_right hmain (le_of_lt hxq_pos)

/-- If `ψ(q) ≥ 1/2` then every `x ∈ [0,1]` satisfies inequality (1.7) for some `a ≤ q`. -/
lemma mem_Kfib_of_half (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψq : (1 / 2 : ℝ≥0) ≤ ψ q) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (Kfib ψ x q).Nonempty := by
  rcases near_frac x q hx0 hx1 with ⟨a, haq, habs⟩
  refine ⟨a, haq, ?_⟩
  unfold inequality_1_7
  have hψqR : (1 / 2 : ℝ) ≤ (ψ q : ℝ) := by exact_mod_cast hψq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast PNat.pos q
  have hrhs : (1 / 2 : ℝ) / (q : ℝ) ≤ ((ψ q / q : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_div]
    exact div_le_div_of_nonneg_right hψqR (le_of_lt hqpos)
  exact le_trans habs hrhs

/-- If `ψ(q) ≥ 1/2` then `[0,1] ⊆ Bq ψ q`. -/
lemma Icc_subset_Bq_of_half (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψq : (1 / 2 : ℝ≥0) ≤ ψ q) :
    Set.Icc (0 : ℝ) 1 ⊆ Bq ψ q := by
  intro x hx
  exact mem_Kfib_of_half ψ q hψq x hx.1 hx.2

/-- Paper §2, Case 1: if `ψ(q) ≥ 1/2` infinitely often, then `𝒦 ψ = [0,1]`. -/
lemma K_eq_Icc_of_half_infinite (ψ : ℕ+ → ℝ≥0)
    (hBig : {q : ℕ+ | (1 / 2 : ℝ≥0) ≤ ψ q}.Infinite) : 𝒦 ψ = Set.Icc (0 : ℝ) 1 := by
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ limsupDenoms (Bq ψ) := by
    intro x hx
    have hBigsub : {q : ℕ+ | (1 / 2 : ℝ≥0) ≤ ψ q} ⊆ {q : ℕ+ | x ∈ Bq ψ q} := by
      intro q hq
      exact Icc_subset_Bq_of_half ψ q hq hx
    change {q : ℕ+ | x ∈ Bq ψ q}.Infinite
    exact Set.Infinite.mono hBigsub hBig
  rw [K_eq_Icc_inter_limsup]
  exact Set.inter_eq_left.mpr hsub

/-- Theorem 2(b), Case 1 (paper §2): if `ψ(q) ≥ 1/2` infinitely often then `𝒦 ψ` is
measurable of full Lebesgue measure. -/
theorem theorem_2_b_case1 (ψ : ℕ+ → ℝ≥0) (_hψ : (∑' q : ℕ+, ψ_star ψ q) = ∞)
    (hBig : {q : ℕ+ | (1 / 2 : ℝ≥0) ≤ ψ q}.Infinite) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 1 := by
  constructor
  · rw [K_eq_Icc_of_half_infinite ψ hBig]
    exact isClosed_Icc.measurableSet
  · rw [K_eq_Icc_of_half_infinite ψ hBig]
    rw [Real.volume_Icc]
    norm_num

end Submission.DS
