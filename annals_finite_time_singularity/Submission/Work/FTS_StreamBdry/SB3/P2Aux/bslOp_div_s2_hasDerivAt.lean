import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_StreamBdry.SB25.bslOp_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

/-- The level-0 ODE for `u := Q/s2` (the `Lgs` identity of `bslOp`, rearranged).

`Lgs` (`Submission/Work/FTS_StreamBdry/SB25/Defs.lean`) satisfies
`bslOp α Q = s2 θ * Lgs α (fun z θ => Q z θ / s2 θ)` with
`Lgs α u = -α^2 * DzIter 2 u - 5*α * Dz u - pthIter 2 u - (4 cos 2θ/sin 2θ - tan θ) * pth u`.
Hence, from `bslOp α Q = F`,
`(Q/s2)'' + c * (Q/s2)' = -F/s2 - (α^2 * DzIter 2 (Q/s2) + 5 * α * Dz (Q/s2))`,
`c = 4 cos 2θ/sin 2θ - tan θ`; this is the statement (in `HasDerivAt` form).
`ContDiffAt ℝ 2 (uncurry Q)` supplies the second-order differentiability of the `θ`-slice. -/
theorem bslOp_div_s2_hasDerivAt {α : ℝ} {Q F : ℝ → ℝ → ℝ}
    (hCt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ))
    (hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp α Q z θ = F z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (deriv (fun θ' => Q z θ' / Work.Construction.s2 θ'))
        (-(F z θ) / Work.Construction.s2 θ
          - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
              * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
          - (α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Q z θ / Work.Construction.s2 θ) z θ
              + 5 * α * Work.Spaces.Dz (fun z θ => Q z θ / Work.Construction.s2 θ) z θ)) θ := by
  intro z θ hQd
  -- the standing hypotheses at the point `(z, θ)`
  have hQ : ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ) := hCt z θ hQd
  have hlaw' : Work.Elliptic.bslOp α Q z θ = F z θ := hlaw z θ hQd
  -- unpack `(z, θ) ∈ Qd = (0,∞) × (0,π/2)`
  have hQd' : (z, θ) ∈ Work.Construction.Qd := hQd
  simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hQd'
  obtain ⟨hz, hθ0, hθ1⟩ := hQd'
  have hsin : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  -- the ground-state identity `bslOp α Q = s2 · Lgs α (Q/s2)` (leaf E3)
  have hsplit := Work.FTS_StreamBdry.SB25.bslOp_split α Q hQd hQ
  have hLgs : Work.FTS_StreamBdry.SB25.Lgs α
      (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
      = F z θ / Work.Construction.s2 θ := by
    rw [eq_div_iff hsin, mul_comm, ← hsplit, hlaw']
  -- unfold `Lgs` and rearrange for `pthIter 2 (Q/s2)`
  have hLgs_exp :
      -(α ^ 2) * Work.Spaces.DzIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        - 5 * α * Work.Spaces.Dz (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        - Work.Spaces.pthIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
            * Work.Spaces.pth (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
        = F z θ / Work.Construction.s2 θ := by
    rw [← hLgs]
    rfl
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    at hLgs_exp
  have hval : Work.Spaces.pthIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
      = -(F z θ) / Work.Construction.s2 θ
        - (4 * Real.cos (2 * θ) / Work.Construction.s2 θ - Real.tan θ)
            * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
        - (α ^ 2 * Work.Spaces.DzIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ
            + 5 * α * Work.Spaces.Dz (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ) := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [neg_div]
    linarith [hLgs_exp]
  -- second-order differentiability of the `θ`-slice of `Q / s2`
  have hslice : ContDiffAt ℝ 2 (fun θ' => Q z θ') θ := by
    have h2 := hQ.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    convert h2 using 1
    funext x; rfl
  have hs2slice : ContDiffAt ℝ 2 (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : ContDiffAt ℝ 2 (fun θ' : ℝ => Real.sin (2 * θ')) θ := by fun_prop
    simpa only [Work.Construction.s2_eq] using h
  have hw : ContDiffAt ℝ 2 (fun θ' => Q z θ' / Work.Construction.s2 θ') θ :=
    hslice.div hs2slice hsin
  have hderiv : ContDiffAt ℝ 1 (deriv (fun θ' => Q z θ' / Work.Construction.s2 θ')) θ :=
    hw.derivWithin (m := 1) (by norm_num)
  have hmain : HasDerivAt (deriv (fun θ' => Q z θ' / Work.Construction.s2 θ'))
      (Work.Spaces.pthIter 2 (fun z' θ' => Q z' θ' / Work.Construction.s2 θ') z θ) θ := by
    have h2 := (hderiv.differentiableAt (by norm_num)).hasDerivAt
    convert h2 using 1
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [hval] at hmain
  exact hmain

end Work.FTS_StreamBdry.SB3.P2Aux
