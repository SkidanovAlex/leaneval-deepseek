import Mathlib
import Submission.Commons.NumberTheory.DuffinSchaeffer.lemma_large_values
import Submission.Commons.NumberTheory.DuffinSchaeffer.addWellApproximable_mono
import Submission.Commons.NumberTheory.DuffinSchaeffer.km_positive_small

namespace Commons.NumberTheory.DuffinSchaeffer

theorem km_hard_positive (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδt : Filter.Tendsto δ Filter.atTop (nhds 0))
    (h : ¬ Summable fun n : ℕ => n.totient * δ n) :
    0 < MeasureTheory.volume (addWellApproximable UnitAddCircle δ) := by
  classical
  -- Split the radii at the threshold `n * δ n = 1/2`.
  let δbig : ℕ → ℝ := fun n => if (n : ℝ) * δ n ≤ 1 / 2 then 0 else δ n
  let δsmall : ℕ → ℝ := fun n => if (n : ℝ) * δ n ≤ 1 / 2 then δ n else 0
  have hδbig_nonneg : ∀ n, 0 ≤ δbig n := by
    intro n
    dsimp [δbig]
    split_ifs with hn
    · norm_num
    · exact hδ n
  have hδsmall_nonneg : ∀ n, 0 ≤ δsmall n := by
    intro n
    dsimp [δsmall]
    split_ifs with hn
    · exact hδ n
    · norm_num
  have hδsmall_prod : ∀ n : ℕ, (n : ℝ) * δsmall n ≤ 1 / 2 := by
    intro n
    dsimp [δsmall]
    split_ifs with hn
    · exact hn
    · simp
  have hbig_le : ∀ n, δbig n ≤ δ n := by
    intro n
    dsimp [δbig]
    split_ifs with hn
    · exact hδ n
    · exact le_rfl
  have hsmall_le : ∀ n, δsmall n ≤ δ n := by
    intro n
    dsimp [δsmall]
    split_ifs with hn
    · exact le_rfl
    · exact hδ n
  have hlarge : ∀ n, δbig n = 0 ∨ (1 : ℝ) / 2 ≤ (n : ℝ) * δbig n := by
    intro n
    dsimp [δbig]
    split_ifs with hn
    · exact Or.inl rfl
    · exact Or.inr (le_of_lt (lt_of_not_ge hn))
  have hsplit : (fun n : ℕ => (n.totient : ℝ) * δ n) =
      (fun n : ℕ => (n.totient : ℝ) * δbig n) +
        (fun n : ℕ => (n.totient : ℝ) * δsmall n) := by
    ext n
    dsimp [δbig, δsmall]
    split_ifs with hn <;> ring
  have hnotboth : ¬ (Summable (fun n : ℕ => (n.totient : ℝ) * δbig n) ∧
      Summable (fun n : ℕ => (n.totient : ℝ) * δsmall n)) := by
    intro hboth
    apply h
    rw [hsplit]
    exact hboth.1.add hboth.2
  by_cases hbigsum : Summable (fun n : ℕ => (n.totient : ℝ) * δbig n)
  · -- The small-value part has to carry the divergence; use the `ψ ≤ 1/2` core.
    have hsmallnot : ¬ Summable (fun n : ℕ => (n.totient : ℝ) * δsmall n) := by
      intro hs
      exact hnotboth ⟨hbigsum, hs⟩
    have hpos := km_positive_small δsmall hδsmall_nonneg hδsmall_prod hsmallnot
    have hsub := addWellApproximable_mono δsmall δ hsmall_le
    exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono hsub)
  · -- The large-value part diverges; Pollington--Vaughan / KM Lemma 2.2 gives full measure.
    have hfull := lemma_large_values δbig hδbig_nonneg hlarge hbigsum
    have hsub := addWellApproximable_mono δbig δ hbig_le
    have hle : (1 : ENNReal) ≤
        MeasureTheory.volume (addWellApproximable UnitAddCircle δ) := by
      calc (1 : ENNReal) =
            MeasureTheory.volume (addWellApproximable UnitAddCircle δbig) := hfull.symm
        _ ≤ MeasureTheory.volume (addWellApproximable UnitAddCircle δ) :=
            MeasureTheory.measure_mono hsub
    exact lt_of_lt_of_le zero_lt_one hle

end Commons.NumberTheory.DuffinSchaeffer
