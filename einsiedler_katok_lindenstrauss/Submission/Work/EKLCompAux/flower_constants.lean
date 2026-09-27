import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.inv_entries_bound

namespace Work.EKLCompAux

open Work.EKLContract

/-!
# `Work.EKLCompAux.flower_constants`

Existence of a system of "flower" constants for the flower construction: a radius `K` closed
under inversion of `V 2`, a radius `δ` realising `V 1 · V K ⊆ V δ`, and a radius `b` realising
the two "product of two `δ`-small elements is `b`-small" closure statements, with `b ≤ ρ`.

All statements are pure entrywise estimates on `3 × 3` matrices, proved from the adjugate
description of the inverse (`Matrix.SpecialLinearGroup.coe_inv`) together with the elementary
product estimate recorded below. -/

/-- Monotonicity of the displacement neighbourhoods `V`. -/
lemma V_mono {A B : ℝ} (h : A ≤ B) : V A ⊆ V B := by
  intro g hg i j
  exact lt_of_lt_of_le (hg i j) h

/-- **Product estimate.**  If `a` is `A`-close to the identity and `b` is `B`-close to the
identity entrywise, then `a * b` is `A + B + 3 A B`-close entrywise:
`(ab - 1)_{ij} = α_{ij} + β_{ij} + (αβ)_{ij}` with `α = a - 1`, `β = b - 1`. -/
lemma mul_mem_V {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) {a b : SL3}
    (ha : a ∈ V A) (hb : b ∈ V B) : a * b ∈ V (A + B + 3 * A * B) := by
  intro i j
  set alpha : Matrix (Fin 3) (Fin 3) ℝ := (a : Matrix (Fin 3) (Fin 3) ℝ) - 1 with halpha
  set beta : Matrix (Fin 3) (Fin 3) ℝ := (b : Matrix (Fin 3) (Fin 3) ℝ) - 1 with hbeta
  have haa : ∀ k l, |alpha k l| < A := by
    intro k l; rw [halpha, Matrix.sub_apply]; exact ha k l
  have hbb : ∀ k l, |beta k l| < B := by
    intro k l; rw [hbeta, Matrix.sub_apply]; exact hb k l
  have hcoe : ((a * b : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = (a : Matrix (Fin 3) (Fin 3) ℝ) * (b : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.SpecialLinearGroup.coe_mul a b
  rw [hcoe]
  have hdecomp : ((a : Matrix (Fin 3) (Fin 3) ℝ) * (b : Matrix (Fin 3) (Fin 3) ℝ)) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = alpha i j + beta i j + (alpha * beta) i j := by
    have h1a : (a : Matrix (Fin 3) (Fin 3) ℝ) = 1 + alpha := by rw [halpha]; abel
    have h1b : (b : Matrix (Fin 3) (Fin 3) ℝ) = 1 + beta := by rw [hbeta]; abel
    rw [h1a, h1b]
    have hmm : (1 + alpha) * (1 + beta) = 1 + alpha + beta + alpha * beta := by
      noncomm_ring
    rw [hmm]
    simp only [Matrix.add_apply]
    ring
  rw [hdecomp]
  have h3 : |(alpha * beta) i j| ≤ 3 * A * B := by
    rw [Matrix.mul_apply]
    calc |∑ k : Fin 3, alpha i k * beta k j| ≤ ∑ k : Fin 3, |alpha i k * beta k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |alpha i k| * |beta k j| := by simp only [abs_mul]
      _ ≤ ∑ _k : Fin 3, A * B := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul (le_of_lt (haa i k)) (le_of_lt (hbb k j)) (abs_nonneg _) hA
      _ = 3 * A * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc |alpha i j + beta i j + (alpha * beta) i j|
      ≤ |alpha i j + beta i j| + |(alpha * beta) i j| := abs_add_le _ _
    _ ≤ (|alpha i j| + |beta i j|) + |(alpha * beta) i j| :=
        add_le_add (abs_add_le (alpha i j) (beta i j)) le_rfl
    _ < A + B + 3 * A * B := by
        have hx := haa i j
        have hy := hbb i j
        linarith

/-- **Entrywise bound on inverses.**  For `u ∈ V ε` (`ε > 0`), the entries of `u⁻¹` are
bounded by `2 (1+ε)²`.  This is `Work.EKLProd.inv_entries_bound` with the witness made
explicit (so that the bound can be used definitionally). -/
lemma inv_entry_le (ε : ℝ) (hε : 0 < ε) {u : SL3} (hu : u ∈ V ε) (i j : Fin 3) :
    |(u⁻¹ : SL3) i j| ≤ 2 * (1 + ε) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  refine Work.EKLProd.abs_adjugate_entry_le (by linarith) (fun p q => ?_) i j
  have hlt : |(u : Matrix (Fin 3) (Fin 3) ℝ) p q
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < ε := hu p q
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |(u : Matrix (Fin 3) (Fin 3) ℝ) p q|
      = |((u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := by rw [sub_add_cancel]
    _ ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) p q - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := abs_add_le _ _
    _ ≤ ε + 1 := add_le_add (le_of_lt hlt) hone
    _ = 1 + ε := by ring

/-- **Inverse estimate.**  If `g` is `A`-close to the identity entrywise (`A > 0`), then
`g⁻¹` is `2 (1+A)² + 2`-close to the identity entrywise. -/
lemma inv_mem_V {A : ℝ} (hA : 0 < A) {g : SL3} (hg : g ∈ V A) :
    g⁻¹ ∈ V (2 * (1 + A) ^ 2 + 2) := by
  intro i j
  have hbound : |(g⁻¹ : SL3) i j| ≤ 2 * (1 + A) ^ 2 := inv_entry_le A hA hg i j
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |(g⁻¹ : SL3) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |(g⁻¹ : SL3) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_sub _ _
    _ ≤ 2 * (1 + A) ^ 2 + 1 := add_le_add hbound hone
    _ < 2 * (1 + A) ^ 2 + 2 := by linarith

theorem flower_constants :
    ∃ (K δ b ρ : ℝ), 0 < K ∧ 0 < δ ∧ 0 < b ∧ 2 < ρ ∧ b ≤ ρ ∧ K ≤ δ ∧
      (∀ t : Work.EKLContract.SL3, t ∈ Work.EKLContract.V 2 → t⁻¹ ∈ Work.EKLContract.V K) ∧
      (∀ a : Work.EKLContract.SL3, a ∈ Work.EKLContract.V 1 →
        ∀ c : Work.EKLContract.SL3, c ∈ Work.EKLContract.V K →
          a * c ∈ Work.EKLContract.V δ) ∧
      (∀ w : Work.EKLContract.SL3, w⁻¹ ∈ Work.EKLContract.V δ →
        ∀ u : Work.EKLContract.SL3, u ∈ Work.EKLContract.V δ →
          w * u ∈ Work.EKLContract.V b) ∧
      (∀ a : Work.EKLContract.SL3, a ∈ Work.EKLContract.V δ →
        ∀ c : Work.EKLContract.SL3, c ∈ Work.EKLContract.V δ →
          a⁻¹ * c ∈ Work.EKLContract.V b) := by
  refine ⟨20, 82, 4000000, 4000000, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact V_mono (by norm_num) (inv_mem_V (A := 2) (by norm_num) ht)
  · intro a ha c hc
    exact V_mono (by norm_num) (mul_mem_V (A := 1) (B := 20) (by norm_num) (by norm_num) ha hc)
  · intro w hw u hu
    have hw' : w ∈ V (2 * (1 + 82) ^ 2 + 2) := by
      have := inv_mem_V (A := 82) (by norm_num) hw
      simpa using this
    exact V_mono (by norm_num)
      (mul_mem_V (A := 2 * (1 + 82) ^ 2 + 2) (B := 82) (by norm_num) (by norm_num) hw' hu)
  · intro a ha c hc
    have ha' : a⁻¹ ∈ V (2 * (1 + 82) ^ 2 + 2) :=
      inv_mem_V (A := 82) (by norm_num) ha
    exact V_mono (by norm_num)
      (mul_mem_V (A := 2 * (1 + 82) ^ 2 + 2) (B := 82) (by norm_num) (by norm_num) ha' hc)

end Work.EKLCompAux
