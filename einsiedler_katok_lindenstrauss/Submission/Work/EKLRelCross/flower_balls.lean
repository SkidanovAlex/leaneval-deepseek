import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLRelCross.flower_balls` — a symmetric multiplicative family of balls in `U`

`bnd r = (exp r - 1)/3`,   `Bset U r = {u ∈ U | ‖u - 1‖ < bnd r ∧ ‖u⁻¹ - 1‖ < bnd r}`.

The family is symmetric, monotone, `Bset U r · Bset U s ⊆ Bset U (r+s)`, `⋂_r Bset U r = {1}`,
and every entrywise ball `V R ∩ U` sits in some `Bset U r`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- The reparametrised radius `bnd r = (exp r - 1)/3`. -/
def bnd (r : ℝ) : ℝ := (Real.exp r - 1) / 3

lemma bnd_pos {r : ℝ} (hr : 0 < r) : 0 < bnd r := by
  have h : 1 < Real.exp r := Real.one_lt_exp_iff.mpr hr
  simp only [bnd]; linarith

lemma bnd_mono : Monotone bnd := by
  intro r s hrs
  have h : Real.exp r ≤ Real.exp s := Real.exp_le_exp.mpr hrs
  simp only [bnd]; linarith

lemma one_add_three_bnd (r : ℝ) : 1 + 3 * bnd r = Real.exp r := by
  simp only [bnd]; ring

/-- For every `ε > 0` there is `r > 0` with `bnd r < ε`. -/
lemma exists_bnd_lt {ε : ℝ} (hε : 0 < ε) : ∃ r : ℝ, 0 < r ∧ bnd r < ε := by
  refine ⟨Real.log (1 + 3 * ε) / 2, by
      apply div_pos _ (by norm_num)
      apply Real.log_pos; linarith, ?_⟩
  have h1 : (0:ℝ) < 1 + 3 * ε := by linarith
  have hexp : Real.exp (Real.log (1 + 3 * ε) / 2) = Real.sqrt (1 + 3 * ε) := by
    rw [Real.exp_half, Real.exp_log h1]
  have hsqrt : Real.sqrt (1 + 3 * ε) < 1 + 3 * ε := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  simp only [bnd, hexp]
  linarith

/-- The symmetric multiplicative family of balls in `U`. -/
def Bset (U : Subgroup SL3) (r : ℝ) : Set SL3 :=
  {u | u ∈ U ∧ (∀ i j : Fin 3, |u i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < bnd r) ∧
    (∀ i j : Fin 3, |(u⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < bnd r)}

lemma mem_Bset {U : Subgroup SL3} {r : ℝ} {u : SL3} :
    u ∈ Bset U r ↔ u ∈ U ∧
      (∀ i j : Fin 3, |u i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < bnd r) ∧
      (∀ i j : Fin 3, |(u⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < bnd r) := Iff.rfl

lemma one_mem_Bset (U : Subgroup SL3) {r : ℝ} (hr : 0 < r) : (1 : SL3) ∈ Bset U r := by
  refine mem_Bset.mpr ⟨U.one_mem, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]; exact bnd_pos hr
  · rw [inv_one, Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]; exact bnd_pos hr

lemma Bset_subset_U {U : Subgroup SL3} {r : ℝ} : Bset U r ⊆ (U : Set SL3) := fun _ h => h.1

lemma Bset_symm {U : Subgroup SL3} {r : ℝ} {u : SL3} (hu : u ∈ Bset U r) :
    u⁻¹ ∈ Bset U r := by
  obtain ⟨hU, h1, h2⟩ := mem_Bset.mp hu
  refine mem_Bset.mpr ⟨U.inv_mem hU, ?_, ?_⟩
  · simpa [inv_inv] using h2
  · simpa [inv_inv] using h1

lemma Bset_mono {U : Subgroup SL3} {r s : ℝ} (hrs : r ≤ s) : Bset U r ⊆ Bset U s := by
  intro u hu
  obtain ⟨hU, h1, h2⟩ := mem_Bset.mp hu
  exact mem_Bset.mpr ⟨hU, fun i j => lt_of_lt_of_le (h1 i j) (bnd_mono hrs),
    fun i j => lt_of_lt_of_le (h2 i j) (bnd_mono hrs)⟩

lemma mul_entries_le_three {A B : Matrix (Fin 3) (Fin 3) ℝ} (i j : Fin 3) {sA sB : ℝ}
    (hA : ∀ k l, |A k l| ≤ sA) (hB : ∀ k l, |B k l| ≤ sB) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB) :
    |(A * B) i j| ≤ 3 * sA * sB := by
  rw [Matrix.mul_apply]
  calc |∑ k : Fin 3, A i k * B k j| ≤ ∑ k : Fin 3, |A i k * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin 3, |A i k| * |B k j| := by simp [abs_mul]
    _ ≤ ∑ _k : Fin 3, sA * sB :=
        Finset.sum_le_sum (fun k _ => mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hsA)
    _ = 3 * (sA * sB) := by simp [Finset.sum_const, Fintype.card_fin]
    _ = 3 * sA * sB := by ring

lemma mul_sub_one_eq (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by
  noncomm_ring

lemma entries_mul_sub_one_le {A B : Matrix (Fin 3) (Fin 3) ℝ} (i j : Fin 3) {sA sB : ℝ}
    (hA : ∀ k l, |A k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < sA)
    (hB : ∀ k l, |B k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < sB)
    (hsA : 0 ≤ sA) (hsB : 0 ≤ sB) :
    |(A * B) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < sA + sB + 3 * sA * sB := by
  have hcoe : (A * B) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = ((A - 1) * (B - 1)) i j + (A - 1) i j + (B - 1) i j := by
    have h := congrFun (congrFun (mul_sub_one_eq A B) i) j
    simpa [Matrix.sub_apply, Matrix.add_apply] using h
  have hAb : ∀ k l, |(A - 1) k l| ≤ sA := fun k l => le_of_lt (by simpa [Matrix.sub_apply] using hA k l)
  have hBb : ∀ k l, |(B - 1) k l| ≤ sB := fun k l => le_of_lt (by simpa [Matrix.sub_apply] using hB k l)
  have hsum : |((A - 1) * (B - 1)) i j| ≤ 3 * sA * sB := mul_entries_le_three i j hAb hBb hsA hsB
  have hsub : |(A - 1) i j| + |(B - 1) i j| < sA + sB := by
    exact add_lt_add (by simpa [Matrix.sub_apply] using hA i j)
      (by simpa [Matrix.sub_apply] using hB i j)
  rw [hcoe]
  have habs3 : |((A - 1) * (B - 1)) i j + (A - 1) i j + (B - 1) i j|
      ≤ |((A - 1) * (B - 1)) i j| + |(A - 1) i j| + |(B - 1) i j| := by
    calc |((A - 1) * (B - 1)) i j + (A - 1) i j + (B - 1) i j|
        = |(((A - 1) * (B - 1)) i j + (A - 1) i j) + (B - 1) i j| := by ring_nf
      _ ≤ |((A - 1) * (B - 1)) i j + (A - 1) i j| + |(B - 1) i j| := abs_add_le _ _
      _ ≤ (|((A - 1) * (B - 1)) i j| + |(A - 1) i j|) + |(B - 1) i j| := by
          linarith [abs_add_le (((A - 1) * (B - 1)) i j) ((A - 1) i j),
            abs_add_le (((A - 1) * (B - 1)) i j + (A - 1) i j) ((B - 1) i j)]
      _ = |((A - 1) * (B - 1)) i j| + |(A - 1) i j| + |(B - 1) i j| := by ring
  calc |((A - 1) * (B - 1)) i j + (A - 1) i j + (B - 1) i j|
      ≤ |((A - 1) * (B - 1)) i j| + |(A - 1) i j| + |(B - 1) i j| := habs3
    _ < |((A - 1) * (B - 1)) i j| + (sA + sB) := by linarith [hsub]
    _ ≤ 3 * sA * sB + (sA + sB) := by linarith [hsum]
    _ = sA + sB + 3 * sA * sB := by ring

/-- **The sharp multiplicative property**: `Bset U r · Bset U s ⊆ Bset U (r+s)`. -/
theorem Bset_mul {U : Subgroup SL3} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Bset U r * Bset U s ⊆ Bset U (r + s) := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  obtain ⟨hU, h1, h2⟩ := mem_Bset.mp hu
  obtain ⟨hV, h3, h4⟩ := mem_Bset.mp hv
  have hbr : 0 < bnd r := bnd_pos hr
  have hbs : 0 < bnd s := bnd_pos hs
  have hmul : bnd r + bnd s + 3 * bnd r * bnd s = bnd (r + s) := by
    have h1' : 1 + 3 * bnd (r + s) = Real.exp r * Real.exp s := by
      rw [one_add_three_bnd (r + s), Real.exp_add]
    have h2' : (1 + 3 * bnd r) * (1 + 3 * bnd s) = Real.exp r * Real.exp s := by
      rw [one_add_three_bnd r, one_add_three_bnd s]
    nlinarith [h1', h2']
  have hcoe : (((u * v : SL3)) : Matrix (Fin 3) (Fin 3) ℝ)
      = (u : Matrix (Fin 3) (Fin 3) ℝ) * (v : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.SpecialLinearGroup.coe_mul u v
  have hinvcoe : (((u * v)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((v⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * ((u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul]
  refine mem_Bset.mpr ⟨U.mul_mem hU hV, ?_, ?_⟩
  · intro i j
    rw [hcoe, ← hmul]
    exact entries_mul_sub_one_le i j h1 h3 (le_of_lt hbr) (le_of_lt hbs)
  · intro i j
    rw [hinvcoe, ← hmul]
    have h := entries_mul_sub_one_le (A := ((v⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := ((u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) (sA := bnd s) (sB := bnd r) i j h4 h2
      (le_of_lt hbs) (le_of_lt hbr)
    rwa [show bnd s + bnd r + 3 * bnd s * bnd r = bnd r + bnd s + 3 * bnd r * bnd s from by ring] at h

/-- `Bset U r ⊆ V (bnd r)`. -/
lemma Bset_subset_V {U : Subgroup SL3} {r : ℝ} : Bset U r ⊆ V (bnd r) :=
  fun _ h => (mem_Bset.mp h).2.1

/-- **Every entrywise ball sits in some `Bset` ball.** -/
theorem exists_Bset_supset_V (U : Subgroup SL3) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ V R ∩ (U : Set SL3) ⊆ Bset U r := by
  obtain ⟨C, hC⟩ := Work.EKLProd.inv_entries_bound R hR
  refine ⟨Real.log (1 + 3 * max (max R C + 2) 1), ?_, ?_⟩
  · apply Real.log_pos
    have : (1:ℝ) ≤ max (max R C + 2) 1 := le_max_right _ _
    linarith
  · have hpos : (0:ℝ) < 1 + 3 * max (max R C + 2) 1 := by
      have : (1:ℝ) ≤ max (max R C + 2) 1 := le_max_right _ _
      linarith
    have hbnd : bnd (Real.log (1 + 3 * max (max R C + 2) 1)) = max (max R C + 2) 1 := by
      simp only [bnd, Real.exp_log hpos]
      ring
    intro u hu
    obtain ⟨huV, huU⟩ := hu
    refine mem_Bset.mpr ⟨huU, fun i j => ?_, fun i j => ?_⟩
    · rw [hbnd]
      have h := huV i j
      have h1 : R < max R C + 2 := by have := le_max_left R C; linarith
      have h2 : (max R C + 2 : ℝ) ≤ max (max R C + 2) 1 := le_max_left _ _
      linarith
    · rw [hbnd]
      have h1 : |(u⁻¹) i j| ≤ C := hC u huV i j
      have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
        rw [Matrix.one_apply]; split <;> simp
      have h3 : |(u⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C + 1 := by
        have h1' := abs_le.mp h1
        have h2' := abs_le.mp h2
        rw [abs_le]
        constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
      have h4 : C + 1 < max R C + 2 := by have := le_max_right R C; linarith
      have h5 : (max R C + 2 : ℝ) ≤ max (max R C + 2) 1 := le_max_left _ _
      linarith

end Work.EKLRelCross
