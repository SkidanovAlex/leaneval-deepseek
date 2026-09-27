import Mathlib
import Submission.Work.EKLComp.FlowerDefs
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLComp.entryBox_seq_cover
import Submission.Work.EKLComp.isClosed_Ucl
import Submission.Work.EKLComp.inv_mul_mem_Uball_of_close

/-!
# `Work.EKLComp.flower_small_cover`

**`Ucl U r` is covered by countably many compact pieces of `U`-diameter `< e`.**

Fix a closed subgroup `U ≤ SL₃(ℝ)`, `r > 0` and `e > 0`.  The closed ball
`Ucl U r = {g ∈ U | ‖g - 1‖ ≤ r}` is compact (it is the entrywise box of radius `r` around `1`,
`Work.EKLProd.sl3EntryBox_compact`, intersected with the closed set `U`).  We cover it by the
countably many *entry boxes*

`K n = {g ∈ SL₃(ℝ) | ∀ i j, |g i j - Q n i j| ≤ δ} ∩ Ucl U r`,

where `δ = e / (24 (1 + r)²)` and `Q : ℕ → ℝ^{3 × 3}` is a sequence whose boxes of radius `δ`
cover all of `SL₃(ℝ)` (`Work.EKLComp.entryBox_seq_cover`).

Each `K n` is compact (`sl3EntryBox_compact` + `Work.EKLComp.isClosed_Ucl`) and lies in `Ucl U r`,
hence in `U`.  Two elements of the same box differ entrywise by at most `2δ`, and then
`Work.EKLComp.inv_mul_mem_Uball_of_close` (the estimate `v₂⁻¹v₁ - 1 = v₂⁻¹(v₁ - v₂)`, with
`‖v₂⁻¹‖ ≤ 2(1+r)²` by Cramer's rule) gives `v₂⁻¹ v₁ ∈ Uball U e`, because
`6 (1 + r)² · 2δ = e/2 < e`.
-/

namespace Work.EKLComp

open Work.EKLContract

theorem flower_small_cover (U : Subgroup Work.EKLContract.SL3) (hcl : IsClosed (U : Set Work.EKLContract.SL3))
    {r e : ℝ} (hr : 0 < r) (he : 0 < e) :
    ∃ K : ℕ → Set Work.EKLContract.SL3, (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ (U : Set Work.EKLContract.SL3)) ∧
      (∀ n, ∀ v₁ ∈ K n, ∀ v₂ ∈ K n, v₂⁻¹ * v₁ ∈ Work.EKLComp.Uball U e) ∧
      Work.EKLComp.Ucl U r ⊆ ⋃ n, K n := by
  set δ : ℝ := e / (24 * (1 + r) ^ 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos he (by nlinarith [sq_nonneg (1 + r)])
  have hη : 6 * (1 + r) ^ 2 * (2 * δ) < e := by
    have h : 6 * (1 + r) ^ 2 * (2 * δ) = e / 2 := by
      rw [hδdef]
      field_simp
      ring
    rw [h]; linarith
  obtain ⟨Q, hQ⟩ := entryBox_seq_cover δ hδpos
  have hcomp : ∀ Qn : Fin 3 → Fin 3 → ℝ,
      IsCompact {g : Work.EKLContract.SL3 |
        (∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - Qn i j| ≤ δ) ∧
          g ∈ Work.EKLComp.Ucl U r} := by
    intro Qn
    have hbox : IsCompact {g : Work.EKLContract.SL3 | ∀ i j,
        Qn i j - δ ≤ (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
          (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ Qn i j + δ} :=
      Work.EKLProd.sl3EntryBox_compact (fun i j => Qn i j - δ) (fun i j => Qn i j + δ)
    have hset : {g : Work.EKLContract.SL3 |
        (∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - Qn i j| ≤ δ) ∧
          g ∈ Work.EKLComp.Ucl U r}
        = {g : Work.EKLContract.SL3 | ∀ i j,
            Qn i j - δ ≤ (g : Matrix (Fin 3) (Fin 3) ℝ) i j ∧
              (g : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ Qn i j + δ} ∩ Work.EKLComp.Ucl U r := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h, hU⟩
        exact ⟨fun i j => by
          have h' := abs_le.mp (h i j); exact ⟨by linarith [h'.1], by linarith [h'.2]⟩, hU⟩
      · rintro ⟨h, hU⟩
        exact ⟨fun i j => by
          have h' := h i j; exact abs_le.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩, hU⟩
    rw [hset]
    exact hbox.inter_right (isClosed_Ucl U hcl r)
  refine ⟨fun n => {g : Work.EKLContract.SL3 |
      (∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - Q n i j| ≤ δ) ∧ g ∈ Work.EKLComp.Ucl U r},
    fun n => hcomp (Q n), ?_, ?_, ?_⟩
  · intro n g hg
    exact hg.2.1
  · intro n v₁ hv₁ v₂ hv₂
    exact inv_mul_mem_Uball_of_close hr (by linarith [hδpos]) hη hv₁.2.1 hv₂.2 (fun i j => by
      have h1 := hv₁.1 i j
      have h2 := hv₂.1 i j
      calc |(v₁ : Matrix (Fin 3) (Fin 3) ℝ) i j - (v₂ : Matrix (Fin 3) (Fin 3) ℝ) i j|
          = |((v₁ : Matrix (Fin 3) (Fin 3) ℝ) i j - Q n i j) -
              ((v₂ : Matrix (Fin 3) (Fin 3) ℝ) i j - Q n i j)| := by congr 1; ring
        _ ≤ |(v₁ : Matrix (Fin 3) (Fin 3) ℝ) i j - Q n i j| +
              |(v₂ : Matrix (Fin 3) (Fin 3) ℝ) i j - Q n i j| := abs_sub _ _
        _ ≤ 2 * δ := by linarith)
  · intro g hg
    rcases Set.mem_iUnion.mp (hQ (Set.mem_univ g)) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨hn, hg⟩⟩

end Work.EKLComp
