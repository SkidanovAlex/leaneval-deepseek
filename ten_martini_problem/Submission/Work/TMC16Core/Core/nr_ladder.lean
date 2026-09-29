import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Core

open Filter

noncomputable section

/-- The `n`-th height of the ladder: `max (q n ^ (8/9)) (q (n-1) / 20)`. -/
def nrA (q : ℕ → ℕ) (n : ℕ) : ℝ :=
  max (Real.rpow (q n : ℝ) (8 / 9)) ((q (n - 1) : ℝ) / 20)

/-- `nrA q` is nondecreasing in `n`. -/
lemma nrA_mono {q : ℕ → ℕ} (hmono : StrictMono q) : Monotone (nrA q) := by
  intro m n hmn
  apply max_le_max
  · apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hmono.monotone hmn
    · norm_num
  · apply div_le_div_of_nonneg_right
    · exact_mod_cast hmono.monotone (Nat.sub_le_sub_right hmn 1)
    · norm_num

/-- `nrA q` tends to `+∞`. -/
lemma nrA_tendsto {q : ℕ → ℕ} (hmono : StrictMono q) :
    Tendsto (nrA q) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => Real.rpow (q n : ℝ) (8 / 9)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 9)).comp
      (tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop)
  refine (nrA_mono hmono).tendsto_atTop_atTop ?_
  intro b
  obtain ⟨m, hm⟩ := (hpow.eventually (eventually_ge_atTop b)).exists
  exact ⟨m, le_trans hm (le_max_left _ _)⟩

/-- Every sufficiently large integer lies in one of the intervals
`(nrA q n, nrA q (n+1)]` with `n ≥ 3`. -/
theorem nr_ladder {q : ℕ → ℕ} (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) :
    ∃ Y : ℝ, ∀ y : ℤ, Y ≤ (y : ℝ) →
      ∃ n : ℕ, 3 ≤ n ∧
        max (Real.rpow (q n : ℝ) (8 / 9)) ((q (n - 1) : ℝ) / 20) < (y : ℝ) ∧
        (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20) := by
  classical
  have hmono' : Monotone (nrA q) := nrA_mono hmono
  have htend : Tendsto (nrA q) atTop atTop := nrA_tendsto hmono
  refine ⟨nrA q 3 + 1, ?_⟩
  intro y hy
  have hy3 : nrA q 3 < (y : ℝ) := by linarith
  obtain ⟨m, hm⟩ := (htend.eventually (eventually_ge_atTop (y : ℝ))).exists
  have hex : ∃ m, (y : ℝ) ≤ nrA q m := ⟨m, hm⟩
  have hm4 : 4 ≤ Nat.find hex := by
    by_contra h
    have hle : Nat.find hex ≤ 3 := by omega
    have h13 := hmono' hle
    have hspec := Nat.find_spec hex
    linarith
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    exact not_le.mp hmin
  · have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [heq]
    exact Nat.find_spec hex

end

end Work.TMC16Core.Core
