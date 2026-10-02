import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELAssembly.Qmem_of

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- The levels `Dlev L n = L ^ (1/64^n)` of the `b₂`-nest are decreasing in `n` when `L > 1`. -/
theorem Dlev_anti' {L : ℝ} (hL : 1 < L) {m n : ℕ} (hmn : m ≤ n) :
    Work.ELNest.Dlev L n ≤ Work.ELNest.Dlev L m := by
  rw [Work.ELNest.Dlev, Work.ELNest.Dlev, Real.rpow_le_rpow_left_iff hL]
  exact one_div_le_one_div_of_le (pow_pos (by norm_num) m)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 64) hmn)

/-- The logarithm of the level is decreasing in `n` when `L > 1`. -/
theorem log_Dlev_anti {L : ℝ} (hL : 1 < L) (n : ℕ) :
    Real.log (Work.ELNest.Dlev L (n + 1)) ≤ Real.log (Work.ELNest.Dlev L n) :=
  Real.log_le_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one hL) _)
    (Dlev_anti' hL (Nat.le_succ n))

theorem Dnest_sub_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) {L : ℝ} (hL : 1 < L) (hD : ∀ n : ℕ, Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) = Work.EL.pairSideNear (N.Za n) ∩ Work.EL.pairSideNear (N.Zb n) ∩ Work.EL.pairSideNear (N.Zc n) ∩ {z : ℂ | Work.EL.pot d.hN z < Real.log (Work.ELNest.Dlev L n)}) (hsideA : ∀ n : ℕ, Work.EL.pairSideNear (N.Za (n+1)) ⊆ Work.EL.pairSideNear (N.Za n)) (hsideB : ∀ n : ℕ, Work.EL.pairSideNear (N.Zb (n+1)) ⊆ Work.EL.pairSideNear (N.Zb n)) (hsideC : ∀ n : ℕ, Work.EL.pairSideNear (N.Zc (n+1)) ⊆ Work.EL.pairSideNear (N.Zc n)) (n : ℕ) : Work.EL.polyRegion [N.Za (n+1), N.Zb (n+1), N.Zc (n+1)] (Work.ELNest.Dlev L (n+1)) ⊆ Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n) := by
  rw [hD (n + 1), hD n]
  rintro z ⟨⟨⟨hzA, hzB⟩, hzC⟩, hzpot⟩
  exact ⟨⟨⟨hsideA n hzA, hsideB n hzB⟩, hsideC n hzC⟩,
    lt_of_lt_of_le hzpot (log_Dlev_anti hL n)⟩

end Work.ELAssembly
