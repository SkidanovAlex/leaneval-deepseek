import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

/-- **The pointwise doubly-odd extension identity.**

Writing `g := u z`, the doubly odd extension `Qext u z` of the angular slice agrees with the
three-image combination `Qcut g s - Qcut g (-s) - Qcut g (π - s)` on the window
`(-3/4, π/2 + 3/4)` that the angular mollification at scales `ε ≤ 1/2` can reach.

The three pieces are the reflections of the slice about `0` (sign `-`) and about `π/2`
(sign `-`); the endpoint values `u z 0 = 0` and `u z (π/2) = 0` are needed only at the two
exceptional angles `s = 0` and `s = π/2`, where the reflected intervals meet the base
interval `Iθ = [0, π/2]` at a single point. -/
theorem Qext_eq_Qcut_pt {u : ℝ → ℝ → ℝ} {z s : ℝ} (h0 : u z 0 = 0)
    (hp : u z (Real.pi / 2) = 0) (hs_gt : -(3 : ℝ) / 4 < s)
    (hs_lt : s < Real.pi / 2 + 3 / 4) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s
      = Qcut (fun s : ℝ => u z s) s
        - Qcut (fun s : ℝ => u z s) (-s)
        - Qcut (fun s : ℝ => u z s) (Real.pi - s) := by
  by_cases hneg : s < 0
  · -- `s < 0`: the base interval is missed, and `Qext` evaluates the `0`-reflection.
    rw [Work.FTS.EllSol.PkgK5.K5c.Qext,
      if_neg (by intro h; exact absurd h.1 (not_le.mpr hneg)), if_pos hneg]
    rw [Qcut_of_lt_zero hneg,
      Qcut_of_mem (show -s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from
        ⟨by linarith, by linarith [hs_gt, Real.pi_gt_three]⟩),
      Qcut_of_pihalf_lt (show Real.pi / 2 < Real.pi - s by linarith [Real.pi_pos])]
    ring
  · rw [not_lt] at hneg
    by_cases hle : s ≤ Real.pi / 2
    · -- `0 ≤ s ≤ π/2`: the reflected intervals meet `Iθ` only at the endpoints.
      have hQneg : Qcut (fun s : ℝ => u z s) (-s) = 0 := by
        rw [Qcut_apply]
        split_ifs with h
        · have hs0 : s = 0 := by linarith [h.1]
          rw [hs0]
          simpa using h0
        · rfl
      have hQpi : Qcut (fun s : ℝ => u z s) (Real.pi - s) = 0 := by
        rw [Qcut_apply]
        split_ifs with h
        · have hs : s = Real.pi / 2 := by linarith [h.2]
          rw [hs, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
          exact hp
        · rfl
      rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_pos ⟨hneg, hle⟩,
        Qcut_of_mem ⟨hneg, hle⟩, hQneg, hQpi]
      ring
    · -- `π/2 < s`: the base interval is missed, and `Qext` evaluates the `π/2`-reflection.
      rw [not_le] at hle
      rw [Work.FTS.EllSol.PkgK5.K5c.Qext,
        if_neg (by intro h; exact absurd h.2 (not_le.mpr hle)),
        if_neg (by intro h; linarith [Real.pi_pos])]
      rw [Qcut_of_pihalf_lt hle, Qcut_of_lt_zero (by linarith [hle, Real.pi_pos]),
        Qcut_of_mem (show Real.pi - s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from
          ⟨by linarith [hs_lt, Real.pi_gt_three], by linarith⟩)]
      ring

theorem Qext_eq_Qcut_combination {u : ℝ → ℝ → ℝ} {z ε θ' s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (h0 : u z 0 = 0) (hp : u z (Real.pi / 2) = 0)
    (hθ'1 : -(1 / 4) < θ') (hθ'2 : θ' < Real.pi / 2 + 1 / 4) :
    Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Work.FTS.EllSol.PkgK5.K5c.Qext u z s
      = Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s)
        * (Work.FTS.EllSol.EllPkgAux.Qcut (fun s : ℝ => u z s) s
            - Work.FTS.EllSol.EllPkgAux.Qcut (fun s : ℝ => u z s) (-s)
            - Work.FTS.EllSol.EllPkgAux.Qcut (fun s : ℝ => u z s) (Real.pi - s)) := by
  by_cases hker : Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) = 0
  · -- The kernel vanishes: both sides are `0`.
    rw [hker, zero_mul, zero_mul]
  · -- Otherwise the support of the bump confines `s` to `(θ' - ε, θ' + ε)`, and the
    -- pointwise identity applies because `θ' ∈ (-1/4, π/2 + 1/4)` and `ε ≤ 1/2`.
    have habs : |θ' - s| < ε :=
      not_le.mp (fun h => hker (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε h))
    have hs_gt : -(3 : ℝ) / 4 < s := by
      have h1 : θ' - s < ε := (abs_lt.mp habs).2
      linarith
    have hs_lt : s < Real.pi / 2 + 3 / 4 := by
      have h1 : -ε < θ' - s := (abs_lt.mp habs).1
      linarith
    rw [Qext_eq_Qcut_pt h0 hp hs_gt hs_lt]

end Work.FTS.EllSol.EllPkgAux
