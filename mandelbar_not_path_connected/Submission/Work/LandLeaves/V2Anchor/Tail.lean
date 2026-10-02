import Mathlib
import Submission.Work.ELTop.All
import Submission.Work.LandLeaves.fundamental_bead_shrink
import Submission.Work.LandLeaves.V2Anchor.BranchCont
import Submission.Work.LandLeaves.exists_seed_level_window
import Submission.Work.LandLeaves.V2Anchor.TailCore

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! Clash-free copy of `exists_backward_orbit_tail` (see `V2Anchor/Helpers.lean`). -/

namespace Work.LandLeaves.V2Anchor

/-- **A backward orbit tail of a repelling landing angle.**  If `θ₀` is an angle whose dynamic
ray lands at the repelling periodic point `y` of odd period `k`, then `θ₀` has a backward orbit
`θ` under the angle `4 ^ k`-tupling map (`θ 0 = θ₀`, `(4:ℝ)^k * θ (n+1) = θ n + m` with
`m : ℤ`), all of whose rays accumulate at `y` at a *geometric* rate: for every `m ≤ n` the `m`-th
fundamental bead of the ray of angle `θ n` lies in the ball `B(y, κ ^ m * r)`. -/
theorem exists_backward_orbit_tail {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hN : Work.EL.DynB c φ)
    (hrep : Work.Landing.IsRepelling c k y)
    {θ₀ : ℝ} (hθ₀ : Work.EL.LandsN hN θ₀ y) :
    ∃ r κ r₀ : ℝ, 0 < r ∧ 0 ≤ κ ∧ κ < 1 ∧ 1 < r₀ ∧
      ∃ θ : ℕ → ℝ, θ 0 = θ₀ ∧
        (∀ n : ℕ, ∃ m : ℤ, (4 : ℝ) ^ k * θ (n + 1) = θ n + m) ∧
        (∀ m n : ℕ, m ≤ n → ∀ s : ℝ,
          s ∈ Set.Icc (Work.LandLeaves.V2Anchor.lvlSeq r₀ (4 ^ k) m)
              ((Work.LandLeaves.V2Anchor.lvlSeq r₀ (4 ^ k) m) ^ (4 ^ k)) →
          ‖Work.EL.rayPt hN (θ n) s - y‖ ≤ κ ^ m * r) := by
  classical
  have hk : 0 < k := hrep.1.1
  have hD2 : 2 ≤ 4 ^ k := by
    calc (2 : ℕ) ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- the contracting local inverse branch of `τ = (T_c)^{2k}` at `y`
  obtain ⟨r, r', κ, g, hr, hrr', hκ0, hκ1, hgy, hcont, hcontr, hright, -⟩ :=
    exists_local_repelling_branch_cont hrep
  have hr'pos : 0 < r' := lt_trans hr hrr'
  -- the size `ε` of a fundamental bead, and the contraction margin
  set ε : ℝ := (1 - κ) * r' / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; nlinarith
  have hεsmall : ε + κ * r' < r' := by rw [hεdef]; nlinarith
  have hεR : ε < r' := by rw [hεdef]; nlinarith
  -- the uniform shrinking of the fundamental beads
  obtain ⟨ρ, hρ1, hρshr⟩ := fundamental_bead_shrink hN hφ (4 ^ k) hD2 ε hεpos
  -- the seed: the bead of `θ₀` at a level close enough to `1` lies in the contraction ball
  obtain ⟨r₀, hr₀, hr₀ρ, hseed⟩ :=
    exists_seed_level_window (D := 4 ^ k) hN hθ₀ hεpos hεR hρ1 hρshr
  -- the geometric core: iterate the branch on the beads, pulling the angles back
  obtain ⟨θ, hθ0, hrel, hwin⟩ :=
    exists_backward_orbit_tail_core (r' := r') (κ := κ) (ε := ε) (ρ := ρ) (r₀ := r₀) (g := g)
      hφ hN hrep hr'pos hκ0 hκ1 hgy hcont hcontr hright hεsmall hρshr hr₀ hr₀ρ hseed
  exact ⟨r', κ, r₀, hr'pos, hκ0, hκ1, hr₀, θ, hθ0, hrel, hwin⟩

end Work.LandLeaves.V2Anchor

