import Mathlib
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLRelCross.flower_size_facts`

The quantitative product facts about the displacement boxes `V δ`, `Vinv δ` that the local
flower theory (`Work.EKLRelCross.atom_flower_local`, `..._flower_plaqueAlgebra_bdd`) takes as
hypotheses: there are `δ, b > 0` such that

* `V R · V 1 ⊆ V δ`,
* `(Vinv δ ∩ U) · (V δ ∩ U) ⊆ V b`,
* `(V δ ∩ U)⁻¹ (V δ ∩ U) ⊆ V b`,

for every subgroup `U ≤ SL₃(ℝ)` (the membership in `U` is not used: the statements are
entrywise estimates).

All three are entrywise estimates.  For the first, `(uv - 1)_{ij} = (u-1)_{ij} + (v-1)_{ij} +
((u-1)(v-1))_{ij}` and a `3 × 3` matrix product has three terms, whence
`entries_mul_sub_one_le`.  For the second and third, the entries of `w ∈ Vinv δ` and of `a⁻¹`
with `a ∈ V δ` are bounded by the adjugate constant `C` of
`Work.EKLProd.inv_entries_bound`; adding the two errors and the `3 ·` product error gives `b`.
-/

open MeasureTheory Topology
open scoped Pointwise

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- `|a - b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

/-- If `w⁻¹ ∈ V δ` then every entry of `w` is within `|C| + 2` of the corresponding entry of the
identity, where `C` is the adjugate bound for the entries of inverses of elements of `V δ`. -/
private lemma entries_sub_one_lt_of_inv_mem_V {δ : ℝ} (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ w : SL3, w⁻¹ ∈ V δ → ∀ i j : Fin 3,
      |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < E := by
  obtain ⟨C, hC⟩ := Work.EKLProd.inv_entries_bound δ hδ
  refine ⟨|C| + 2, by positivity, ?_⟩
  intro w hw i j
  have hw1 : |(w : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ |C| := by
    have h := hC w⁻¹ hw i j
    rw [inv_inv] at h
    exact le_trans h (le_abs_self C)
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |(w : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
        abs_sub_le_abs_add _ _
    _ ≤ |C| + 1 := add_le_add hw1 hone
    _ < |C| + 2 := by linarith

lemma flower_size_facts {U : Subgroup Work.EKLContract.SL3} {R : ℝ} (hR : 0 < R) :
    ∃ (δ b : ℝ), 0 < δ ∧ 0 < b ∧
      (∀ u ∈ Work.EKLContract.V R, ∀ u₁ ∈ Work.EKLContract.V 1, u * u₁ ∈ Work.EKLContract.V δ) ∧
      (∀ w ∈ U, w ∈ Work.EKLRelCross.Vinv δ → ∀ u ∈ U, u ∈ Work.EKLContract.V δ →
        w * u ∈ Work.EKLContract.V b) ∧
      (∀ a ∈ U, a ∈ Work.EKLContract.V δ → ∀ c ∈ U, c ∈ Work.EKLContract.V δ →
        a⁻¹ * c ∈ Work.EKLContract.V b) := by
  obtain ⟨E, hEpos, hE⟩ :=
    entries_sub_one_lt_of_inv_mem_V (δ := R + 1 + 3 * R + 1) (by linarith)
  refine ⟨R + 1 + 3 * R + 1, E + (R + 1 + 3 * R + 1) + 3 * E * (R + 1 + 3 * R + 1) + 1,
    by linarith, by nlinarith [hEpos], ?_, ?_, ?_⟩
  · intro u hu u₁ hu₁ i j
    have hu' : ∀ k l, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < R := hu
    have hu₁' : ∀ k l, |(u₁ : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < 1 := hu₁
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := entries_mul_sub_one_le (A := (u : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (u₁ : Matrix (Fin 3) (Fin 3) ℝ)) (sA := R) (sB := 1) i j hu' hu₁'
      (le_of_lt hR) (by norm_num)
    linarith
  · intro w _ hwVinv u _ huV i j
    have hw' : ∀ k l, |(w : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < E := hE w hwVinv
    have hu' : ∀ k l, |(u : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < R + 1 + 3 * R + 1 := huV
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := entries_mul_sub_one_le (A := (w : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (u : Matrix (Fin 3) (Fin 3) ℝ)) (sA := E) (sB := R + 1 + 3 * R + 1) i j
      hw' hu' (le_of_lt hEpos) (by linarith)
    linarith
  · intro a _ haV c _ hcV i j
    have ha' : ∀ k l, |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < E :=
      hE a⁻¹ (by simpa [inv_inv] using haV)
    have hc' : ∀ k l, |(c : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < R + 1 + 3 * R + 1 := hcV
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have h := entries_mul_sub_one_le (A := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := (c : Matrix (Fin 3) (Fin 3) ℝ)) (sA := E) (sB := R + 1 + 3 * R + 1) i j
      ha' hc' (le_of_lt hEpos) (by linarith)
    linarith

end Work.EKLRelCross
