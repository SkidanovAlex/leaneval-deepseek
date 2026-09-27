import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLRelCross.exists_Ucl_bound`

Uniform bounds for the closed `U`-balls
`Ucl U R = {g ∈ U | ∀ i j, |g i j - δ i j| ≤ R}`:
a *single* `R` controls inversion, multiplication, and multiplication by an inverse, for
elements of the ball of radius `1`.

The estimates are entrywise and do not use anything about `U` beyond closure under the group
operations (so no topology/compactness is needed):

* entries of `g ∈ Ucl U a` are bounded by `1 + a`;
* `x * y - 1 = (x - 1)(y - 1) + (x - 1) + (y - 1)`, hence
  `Ucl U a · Ucl U b ⊆ Ucl U (a + b + 3ab)`;
* `g⁻¹` is the adjugate of `g`, whose entries are `2 × 2` minors
  (`Work.EKLProd.abs_adjugate_entry_le`), hence `Ucl U a ⊆ Ucl U (2(1+a)² + 1)` under inversion.

With `LamU 1 = 9` and `1 + 9 + 3·1·9 = 37`, the value `R = 37` satisfies all three clauses.
-/

open Work.EKLContract

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

/-! ## The inverse bound -/

/-- The constant governing the inverse of an element of `Ucl U a`. -/
def LamU (a : ℝ) : ℝ := 2 * (1 + a) ^ 2 + 1

theorem LamU_nonneg (a : ℝ) : 0 ≤ LamU a := by
  have h : (0 : ℝ) ≤ 2 * (1 + a) ^ 2 := by positivity
  simp only [LamU]; linarith

theorem LamU_pos (a : ℝ) : 0 < LamU a := by
  have h : (0 : ℝ) ≤ 2 * (1 + a) ^ 2 := by positivity
  simp only [LamU]; linarith

/-- Every entry of an element of the closed ball `Ucl U a` is bounded by `1 + a`. -/
theorem Ucl_entries_le {U : Subgroup SL3} {a : ℝ} {g : SL3} (hg : g ∈ Ucl U a) (i j : Fin 3) :
    |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + a := by
  have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |((g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by rw [sub_add_cancel]
    _ ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ a + 1 := add_le_add (hg.2 i j) h1
    _ = 1 + a := by ring

/-- **Inversion stays in a closed ball**: the inverse of an element of `Ucl U a` (`a ≥ 0`) lies
in `Ucl U (LamU a)`.  Uses that `g⁻¹` is the adjugate of `g`, whose entries are `2 × 2` minors. -/
theorem Ucl_inv_mem {U : Subgroup SL3} {a : ℝ} (ha : 0 ≤ a) {g : SL3} (hg : g ∈ Ucl U a) :
    g⁻¹ ∈ Ucl U (LamU a) := by
  refine ⟨U.inv_mem hg.1, fun i j => ?_⟩
  have hcoe : ((g⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = (g : Matrix (Fin 3) (Fin 3) ℝ).adjugate := Matrix.SpecialLinearGroup.coe_inv g
  rw [hcoe, Matrix.one_apply]
  have hb : |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| ≤ 2 * (1 + a) ^ 2 :=
    Work.EKLProd.abs_adjugate_entry_le (by linarith : (0 : ℝ) ≤ 1 + a)
      (fun p q => Ucl_entries_le hg p q) i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i - 1|
        ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i| + |(1 : ℝ)| := abs_sub _ _
      _ = |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i| + 1 := by rw [abs_one]
      _ ≤ 2 * (1 + a) ^ 2 + 1 := by linarith
      _ = LamU a := by simp only [LamU]
  · rw [if_neg hij]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j - 0|
        = |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| := by rw [sub_zero]
      _ ≤ 2 * (1 + a) ^ 2 := hb
      _ ≤ 2 * (1 + a) ^ 2 + 1 := by linarith
      _ = LamU a := by simp only [LamU]

/-! ## The multiplication bound -/

/-- **Multiplicativity of the closed balls**: `Ucl U a * Ucl U b ⊆ Ucl U (a + b + 3ab)`
for `a, b ≥ 0`. -/
theorem Ucl_mul_mem {U : Subgroup SL3} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : SL3}
    (hx : x ∈ Ucl U a) (hy : y ∈ Ucl U b) : x * y ∈ Ucl U (a + b + 3 * a * b) := by
  refine ⟨U.mul_mem hx.1 hy.1, fun i j => ?_⟩
  have hx' : ∀ k l, |(x : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
      ≤ a := fun k l => hx.2 k l
  have hy' : ∀ k l, |(y : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l|
      ≤ b := fun k l => hy.2 k l
  have hid : ((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1
      = ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) + ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
  have hB : |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ b := hy' i j
  have hprod : |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j|
      ≤ 3 * (a * b) := by
    rw [Matrix.mul_apply]
    calc |∑ k : Fin 3, ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k
            * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j|
        ≤ ∑ k : Fin 3, |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k
            * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k|
            * |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j| := by simp [abs_mul]
      _ ≤ ∑ _k : Fin 3, a * b :=
          Finset.sum_le_sum (fun k _ => mul_le_mul (hx' i k) (hy' k j) (abs_nonneg _) ha)
      _ = 3 * (a * b) := by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hsum : |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ 3 * (a * b) + a := by
    have hq : |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ a := hx' i j
    have h := abs_add_le ((((x : Matrix (Fin 3) (Fin 3) ℝ) - 1)
      * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j) (((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)
    linarith
  have hmain : |(((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ 3 * (a * b) + a + b := by
    rw [hid, Matrix.add_apply, Matrix.add_apply]
    calc |((((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
            + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j + ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)|
        ≤ |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
            + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j|
          + |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| := abs_add_le _ _
      _ ≤ (3 * (a * b) + a) + b := add_le_add hsum hB
      _ = 3 * (a * b) + a + b := by ring
  rw [show ((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j from rfl]
  linarith

/-- Monotonicity of the closed balls in the radius. -/
theorem Ucl_mono_le {U : Subgroup SL3} {a b : ℝ} (h : a ≤ b) : Ucl U a ⊆ Ucl U b :=
  fun _ hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

/-! ## The target -/

theorem exists_Ucl_bound (U : Subgroup Work.EKLContract.SL3) :
    ∃ R : ℝ, (∀ g ∈ Work.EKLRelCross.Ucl U 1, g⁻¹ ∈ Work.EKLRelCross.Ucl U R) ∧
      (∀ g ∈ Work.EKLRelCross.Ucl U 1, ∀ g' ∈ Work.EKLRelCross.Ucl U 1, g * g' ∈ Work.EKLRelCross.Ucl U R) ∧
      (∀ g ∈ Work.EKLRelCross.Ucl U 1, ∀ g' ∈ Work.EKLRelCross.Ucl U 1, g * g'⁻¹ ∈ Work.EKLRelCross.Ucl U R) := by
  refine ⟨37, ?_, ?_, ?_⟩
  · intro g hg
    exact Ucl_mono_le (by norm_num [LamU]) (Ucl_inv_mem (by norm_num : (0 : ℝ) ≤ 1) hg)
  · intro g hg g' hg'
    exact Ucl_mono_le (by norm_num)
      (Ucl_mul_mem (U := U) (a := 1) (b := 1) (by norm_num) (by norm_num) hg hg')
  · intro g hg g' hg'
    have h1 : g'⁻¹ ∈ Ucl U (LamU 1) := Ucl_inv_mem (by norm_num : (0 : ℝ) ≤ 1) hg'
    exact Ucl_mono_le (by norm_num [LamU])
      (Ucl_mul_mem (U := U) (a := 1) (b := LamU 1) (by norm_num) (LamU_nonneg 1) hg h1)

end Work.EKLRelCross
