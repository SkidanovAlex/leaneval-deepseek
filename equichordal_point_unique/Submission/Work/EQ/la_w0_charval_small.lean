import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.walk_count

/-! # A closed word containing a `false` has characteristic value `< 1`

This is the arithmetic input that makes the case-(ii) characteristic value of Rychlik's
Lemma 5.1 non-trivial: if `C` is a closed word (`fan a h C 0 = A₁`) containing a `false` letter,
then

`charVal a h C = ((wtAux a C.reverse 0 : ℝ) : ℂ)` and `wtAux a C.reverse 0 ≤ γ ^ (#false) ≤ γ < 1`

for the constant `γ < 1` of `Work.EQ.walk_count`.  In particular `charVal a h C ≠ 1`.

Together with `Work.EQ.last_letter_false_of_isChainWord` (the minimal word of a chain ends in
`false`) this excludes the trichotomy case (i) from producing `μ = 1` on the unbounded side.
-/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-- **`charVal` of a closed word containing `false` is strictly smaller than `1`** (as a real
number, with vanishing imaginary part). -/
theorem charVal_lt_one_of_false_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {C : List Bool}
    (hC : fan a h C 0 = ((-1 / 2 : ℂ), (0 : ℂ))) (hfalse : false ∈ C) :
    (charVal a h C).re < 1 ∧ (charVal a h C).im = 0 := by
  obtain ⟨γ, hγ0, hγ1, hwalk⟩ := walk_count ha0 ha1
  have hst := stAux_eq_zero_of_closed ha0 ha1 hh hC
  have hcnt : 0 < C.reverse.count false := by
    rw [List.count_reverse]
    exact List.count_pos_iff.mpr hfalse
  have hw : wtAux a C.reverse 0 ≤ γ ^ (C.reverse.count false) := hwalk C.reverse hst
  have hγ : γ ^ (C.reverse.count false) < 1 := pow_lt_one₀ hγ0.le hγ1 (by omega)
  have hcv := charVal_of_closed ha0 ha1 hh hC
  refine ⟨?_, ?_⟩
  · rw [hcv, Complex.ofReal_re]
    exact lt_of_le_of_lt hw hγ
  · rw [hcv]
    simp

/-- **A closed word containing `false` is not the identity characteristic value.** -/
theorem charVal_ne_one_of_false_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {C : List Bool}
    (hC : fan a h C 0 = ((-1 / 2 : ℂ), (0 : ℂ))) (hfalse : false ∈ C) :
    charVal a h C ≠ 1 := by
  intro h1
  obtain ⟨hre, -⟩ := charVal_lt_one_of_false_mem ha0 ha1 hh hC hfalse
  rw [h1] at hre
  norm_num at hre

end

end Work.EQ
