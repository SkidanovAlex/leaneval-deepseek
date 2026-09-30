import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- One-sided dyadic tiling of the half-line: for `R > 0` the half-open intervals
`(2^k R, 2^(k+1) R]` cover `(R, ∞)`. -/
theorem half_line_cover (R : ℝ) (hR : 0 < R) :
    (⋃ k : ℕ, Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)) = Set.Ioi R := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨k, hk1, hk2⟩ := hx
    rw [Set.mem_Ioi]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    nlinarith [hR, hpow, hk1]
  · intro hx
    rw [Set.mem_Ioi] at hx
    rw [Set.mem_iUnion]
    classical
    obtain ⟨n, hn⟩ :=
      pow_unbounded_of_one_lt (x / R) (show (1 : ℝ) < 2 by norm_num)
    rw [div_lt_iff₀ hR] at hn
    have hex : ∃ k : ℕ, x ≤ (2 : ℝ) ^ (k + 1) * R := by
      refine ⟨n, ?_⟩
      have hle2 : (2 : ℝ) ^ n * R ≤ (2 : ℝ) ^ (n + 1) * R :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hR.le
      linarith
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hkpos
    · rw [hk0, pow_zero, one_mul]; exact hx
    · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      have hsub : (Nat.find hex - 1) + 1 = Nat.find hex := Nat.sub_add_cancel hkpos
      rw [hsub] at hmin
      exact lt_of_not_ge hmin

/-- One-sided dyadic annuli are pairwise disjoint. -/
theorem half_line_disjoint (R : ℝ) (hR : 0 < R) :
    Pairwise (fun i j : ℕ => Disjoint (Set.Ioc ((2 : ℝ) ^ i * R) ((2 : ℝ) ^ (i + 1) * R))
                                      (Set.Ioc ((2 : ℝ) ^ j * R) ((2 : ℝ) ^ (j + 1) * R))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact Set.Ioc_disjoint_Ioc_of_le (by
      apply mul_le_mul_of_nonneg_right _ hR.le
      exact pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hlt))
  · exact (Set.Ioc_disjoint_Ioc_of_le (by
      apply mul_le_mul_of_nonneg_right _ hR.le
      exact pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hgt))).symm

/-- The two-sided annulus is exactly the preimage under `|·|` of the one-sided annulus. -/
theorem annulus_eq_abs (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R)))
      = {t : ℝ | |t| ∈ Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)} := by
  ext t
  change ((2 : ℝ) ^ k * R < t ∧ t ≤ (2 : ℝ) ^ (k + 1) * R)
      ∨ (-((2 : ℝ) ^ (k + 1) * R) ≤ t ∧ t < -((2 : ℝ) ^ k * R))
      ↔ (2 : ℝ) ^ k * R < |t| ∧ |t| ≤ (2 : ℝ) ^ (k + 1) * R
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have ha : (0 : ℝ) < (2 : ℝ) ^ k * R := mul_pos (pow_pos (by norm_num) k) hR
      rw [abs_of_pos (lt_trans ha h1)]
      exact ⟨h1, h2⟩
    · have ht : t < 0 := by
        have : (0 : ℝ) < (2 : ℝ) ^ k * R := mul_pos (pow_pos (by norm_num) k) hR
        linarith
      rw [abs_of_neg ht]
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    rcases le_or_gt 0 t with ht | ht
    · left
      rw [abs_of_nonneg ht] at h1 h2
      exact ⟨h1, h2⟩
    · right
      rw [abs_of_neg ht] at h1 h2
      exact ⟨by linarith, by linarith⟩

/-- The two-sided dyadic annuli `2^k R < |t| ≤ 2^(k+1) R` cover `{t | R < |t|}` and are pairwise
disjoint, for `R > 0`.  (The negative pieces use `Ico` so that the point `-R` is excluded, which
is exactly the endpoint convention that makes the covering identity exact.) -/
theorem dyadic_cover (R : ℝ) (hR : 0 < R) :
    (⋃ k : ℕ, (Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R)))) = {t : ℝ | R < |t|} ∧
    Pairwise (Function.onFun Disjoint
      (fun k : ℕ => Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R)))) := by
  have hmem : ∀ k : ℕ,
      (Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)
          ∪ Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R)))
        = {t : ℝ | |t| ∈ Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)} :=
    fun k => annulus_eq_abs R hR k
  constructor
  · ext t
    change (t ∈ ⋃ k : ℕ, (Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (k + 1) * R)) (-((2 : ℝ) ^ k * R)))) ↔ R < |t|
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩

      rw [hmem k] at hk
      change |t| ∈ Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R) at hk
      rw [Set.mem_Ioc] at hk
      have hle : R ≤ (2 : ℝ) ^ k * R := by
        have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        nlinarith [hR, hpow]
      linarith [hk.1, hle]
    · intro hRt
      have hmem2 : |t| ∈ ⋃ k : ℕ, Set.Ioc ((2 : ℝ) ^ k * R) ((2 : ℝ) ^ (k + 1) * R) := by
        rw [half_line_cover R hR]; exact hRt
      rw [Set.mem_iUnion] at hmem2
      obtain ⟨k, hk⟩ := hmem2
      exact ⟨k, by rw [hmem k]; exact hk⟩
  · intro i j hij
    change Disjoint (Set.Ioc ((2 : ℝ) ^ i * R) ((2 : ℝ) ^ (i + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (i + 1) * R)) (-((2 : ℝ) ^ i * R)))
      (Set.Ioc ((2 : ℝ) ^ j * R) ((2 : ℝ) ^ (j + 1) * R)
        ∪ Set.Ico (-((2 : ℝ) ^ (j + 1) * R)) (-((2 : ℝ) ^ j * R)))
    rw [hmem i, hmem j]
    rw [Set.disjoint_left]
    intro t ht1 ht2
    change |t| ∈ Set.Ioc ((2 : ℝ) ^ i * R) ((2 : ℝ) ^ (i + 1) * R) at ht1
    change |t| ∈ Set.Ioc ((2 : ℝ) ^ j * R) ((2 : ℝ) ^ (j + 1) * R) at ht2
    exact (Set.disjoint_left.mp (half_line_disjoint R hR hij)) ht1 ht2

end Work.BMF
