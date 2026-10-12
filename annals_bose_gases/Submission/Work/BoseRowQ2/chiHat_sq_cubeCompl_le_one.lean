import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowQ2

/-- The shifted full-lattice Parseval bound for `χ̂`: for every `k : ℤ³` the sum of `χ̂(vec (m−k))²`
over the lattice points *outside* the cube is at most `1`.  Indeed the shift `m ↦ m−k` is a
bijection of `ℤ³`, the summand is nonnegative, and the full lattice sum is
`Σ_n χ̂(vec n)² = 1`, which is `Work.BoseRowQ2.chiLatticeParseval 0` together with
`Work.BoseRowQ2.chiHatSq_zero` (`Σ_n χ̂(vec n)χ̂(vec n) = χ̂²(0) = 1`). -/
theorem chiHat_sq_cubeCompl_le_one (N : ℕ) (k : Fin 3 → ℤ) :
    (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
      Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - k)) ^ 2) ≤ 1 := by
  -- the full lattice sum is `χ̂²(0) = 1` (Parseval at `n = 0`)
  have hfull : (∑' m : Fin 3 → ℤ, Work.BoseRowQ2.chiHat (Work.BoseB4.vec m) ^ 2) = 1 := by
    have h := Work.BoseRowQ2.chiLatticeParseval (0 : Fin 3 → ℤ)
    simp only [add_zero] at h
    have h2 : (∑' m : Fin 3 → ℤ,
        Work.BoseRowQ2.chiHat (Work.BoseB4.vec m) * Work.BoseRowQ2.chiHat (Work.BoseB4.vec m))
        = Work.BoseRowQ2.chiHatSq (Work.BoseB4.vec (0 : Fin 3 → ℤ)) := h
    rw [show Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 from by
          ext i; simp [Work.BoseB4.vec], Work.BoseRowQ2.chiHatSq_zero] at h2
    simpa [pow_two] using h2
  have hsum : Summable (fun m : Fin 3 → ℤ =>
      Work.BoseRowQ2.chiHat (Work.BoseB4.vec m) ^ 2) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hfull
    norm_num at hfull
  -- the shift `m ↦ m − k` is injective, so the `tsum` over the outside of the cube is at most
  -- the `tsum` over the whole lattice (`ENNReal.tsum_comp_le_tsum_of_injective`)
  have hinj : Function.Injective
      (fun m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N} => m.val - k) := by
    intro a b hab
    exact Subtype.ext (sub_left_inj.mp hab)
  have hENN := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun u : Fin 3 → ℤ => ENNReal.ofReal (Work.BoseRowQ2.chiHat (Work.BoseB4.vec u) ^ 2))
  have hRHS : (∑' u : Fin 3 → ℤ,
      ENNReal.ofReal (Work.BoseRowQ2.chiHat (Work.BoseB4.vec u) ^ 2)) = ENNReal.ofReal 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun u => sq_nonneg _) hsum, hfull]
  -- transfer the `ℝ≥0∞`-bound back to `ℝ`
  have hLHS : (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
        Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - k)) ^ 2)
      = (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
        ENNReal.ofReal (Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - k)) ^ 2)).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun m => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun m => (ENNReal.toReal_ofReal (sq_nonneg _)).symm
  rw [hLHS]
  calc (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
        ENNReal.ofReal (Work.BoseRowQ2.chiHat (Work.BoseB4.vec (m.val - k)) ^ 2)).toReal
      ≤ (∑' u : Fin 3 → ℤ,
        ENNReal.ofReal (Work.BoseRowQ2.chiHat (Work.BoseB4.vec u) ^ 2)).toReal :=
        ENNReal.toReal_mono (by rw [hRHS]; exact ENNReal.ofReal_ne_top) hENN
    _ = 1 := by rw [hRHS, ENNReal.toReal_ofReal zero_le_one]

end Work.BoseRowQ2
