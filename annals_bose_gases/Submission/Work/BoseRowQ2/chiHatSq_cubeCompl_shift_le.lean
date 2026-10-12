import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTailAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowQ2

/-- For `i : ℤ³` with `‖vec i‖ ≤ L` and `R := rad N L = 2π(N+1) − L ≥ 1`, the shifted
`χ̂²`-tail over the lattice points *outside* the cube `[−N,N]³` obeys the Schwartz bound
`Σ_{m ∉ cube N} χ̂²(vec (m−i))² ≤ C/R^101`.  The shift is a bijection of `ℤ³` and
`m ∉ cube N` forces `‖vec (m−i)‖ ≥ R` (`rad_le_norm_vec_sub`, proved in
`BoseRowQ2/chatTailAux.lean`), so it reduces to `Work.BoseRowQ2.chiHatSq_tsum_le`
(proved, in `Submission/Work/BoseRowQ2/chiHatSq_tsum_le.lean`) restricted to a subset. -/
theorem chiHatSq_cubeCompl_shift_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (L : ℝ) (i : Fin 3 → ℤ), 0 ≤ L →
      1 ≤ Work.BoseRowQ2.rad N L → ‖Work.BoseB4.vec i‖ ≤ L →
      (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
        Work.BoseRowQ2.chiHatSq (Work.BoseB4.vec (m.val - i)) ^ 2)
        ≤ C / Work.BoseRowQ2.rad N L ^ 101 := by
  obtain ⟨C, hC0, hCf⟩ := chiHatSq_finset_tail_sum
  refine ⟨C, hC0, fun N L i _hL hR hi => ?_⟩
  -- the summand is nonnegative, so it suffices to bound every finite partial sum
  refine Real.tsum_le_of_sum_le (fun x => sq_nonneg _) fun s => ?_
  -- the shift `m ↦ m - i` is injective and pushes `m ∉ cube N` into `rad N L ≤ ‖vec ·‖`
  let φ : {m : Fin 3 → ℤ // m ∉ cube N} ↪ (Fin 3 → ℤ) :=
    ⟨fun m => m.val - i, fun a b h => Subtype.ext (sub_left_injective (b := i) h)⟩
  have hsum := hCf (rad N L) (s.map φ) hR (fun n hn => ?_)
  · rw [Finset.sum_map] at hsum
    exact hsum
  · rw [Finset.mem_map] at hn
    obtain ⟨x, _hx, rfl⟩ := hn
    exact rad_le_norm_vec_sub x.2 hi

end Work.BoseRowQ2
