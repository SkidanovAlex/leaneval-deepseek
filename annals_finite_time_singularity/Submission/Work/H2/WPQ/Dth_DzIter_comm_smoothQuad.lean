import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.H2.WPQ

set_option autoImplicit false

/-! ## The interior commutation identity

`Work.Spaces.quadU = (-1,∞) × (0,π/2)` is the open quadrant of the class
`Work.FTS.LocData.SmoothQuad`, and on it `D_θ` commutes with the iterates of `D_z`.  This is
the pointwise Clairaut statement `Work.Spaces.Dz_Dth_comm`, which is available at every point
of `quadU` because `SmoothQuad` is *local* smoothness (`ContDiffOn ℝ smoothOrder`) and the two
operators are local. -/

/-- On the open quadrant `quadU`, `D_θ` commutes with every iterate of `D_z`. -/
theorem Dth_DzIter_comm_quadU {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.Dth g))) Work.Spaces.quadU := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      -- `D_z^b g` is `C^∞` (hence `C²`) near `y`, so Clairaut applies there.
      have hG : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter b g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg b
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter b g)) y :=
        (hG.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hy)).of_le
          (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DzIter b g) hcd
      show Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [← hcomm]
      -- The two `z`-slices agree near `y` by the induction hypothesis, so their derivatives do.
      show y.1 * Work.Spaces.pz (Work.Spaces.Dth (Work.Spaces.DzIter b g)) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.Dth g)) y.1 y.2
      rw [Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]

/-- At `z = 0` the `θ`-slice of `D_z^{n+1} f` is constant (and zero), so its derivative
vanishes. -/
private lemma deriv_slice_DzIter_succ_zero (n : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    deriv (fun θ' => Work.Spaces.DzIter (n + 1) f 0 θ') θ = 0 := by
  have h : (fun θ' => Work.Spaces.DzIter (n + 1) f 0 θ') = fun _ : ℝ => (0 : ℝ) := by
    funext θ'
    simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
  rw [h]
  simp

/-- **`D_θ (D_z^b g)` is the mixed derivative `D_z^b D_θ g` in the interior class.**  For `g`
smooth on the open quadrant, `D_θ` commutes with the iterates of `D_z = z ∂_z`, so that the
iterated `θ`-derivative of `D_z^b g` is the mixed slot `D_z^b D_θ g` used in the `ℋ⁴`-norm.
(The case `z = 0` is degenerate: both sides vanish for `b ≥ 1`, and for `b = 0` the identity is
definitional.  For `z > 0` the identity follows from `Work.Spaces.Dz_Dth_comm` applied to
`Work.FTS.LocData.SmoothQuad.DzIter` functions — the two curvilinear derivatives commute at every
point where the function is `C²`.) -/
theorem Dth_DzIter_comm_smoothQuad {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (b : ℕ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.Spaces.DzIter b g) z θ = Work.Spaces.mixed b 1 g z θ := by
  have hzge : 0 ≤ z := hz
  rcases eq_or_lt_of_le hzge with h0 | hpos
  · -- Degenerate case `z = 0`: both sides vanish for `b ≥ 1`, and are `D_θ g` for `b = 0`.
    subst h0
    rcases b with _ | m
    · rfl
    · have hL : Work.Spaces.Dth (Work.Spaces.DzIter (m + 1) g) 0 θ = 0 := by
        show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DzIter (m + 1) g 0 θ') θ = 0
        rw [deriv_slice_DzIter_succ_zero m g θ, mul_zero]
      have hR : Work.Spaces.mixed (m + 1) 1 g 0 θ = 0 := by
        simp [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      rw [hL, hR]
  · -- Interior case `z > 0`: `(z,θ) ∈ quadU`, so the `EqOn` statement applies.
    have hy : (z, θ) ∈ Work.Spaces.quadU := ⟨Set.mem_Ioi.mpr (by linarith), hθ⟩
    have h := Dth_DzIter_comm_quadU hg b hy
    have h' : Work.Spaces.Dth (Work.Spaces.DzIter b g) z θ
        = Work.Spaces.DzIter b (Work.Spaces.Dth g) z θ := by
      simpa [Function.uncurry] using h
    exact h'

end Work.H2.WPQ
