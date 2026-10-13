/-
# `Work.FTS.LocData.SmoothQuad_hLoc` — the bump `hLoc α = φ(z)·Γ(θ)` is `C^∞` on the quadrant

The bump of the route factorises as a *radial* factor `bumpZ z = χ(4z - 5)` times an *angular*
factor `Γ(θ) = (sinθ cos²θ)^{α/3}`.  Both are `C^∞` on the relevant piece:

* `bumpZ` is a translate/dilate of the cut-off `χ`, which is `C^∞` on `ℝ`
  (`Work.Stability.chi_contDiff`), hence `contDiff_bumpZ` holds on all of `ℝ`;
* `Γ` is a real power of the positive function `θ ↦ sinθ·cos²θ` on `(0, π/2)`, hence `C^∞` there
  (`ContDiffOn.rpow`, `contDiffOn_Gam_Ioo`).

The two `SmoothQuad`-statements for functions of a *single* variable
(`smoothQuad_of_fst`, `smoothQuad_of_snd`) then combine the factors through the
multiplicativity `smoothQuad_mul` of `Work.FTS.LocData.SmoothChain`, giving
`SmoothQuad (hLoc α)`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The two factors of `hLoc` -/

/-- The radial factor `bumpZ z = χ(4z - 5)` of the bump is `C^∞` on `ℝ` (at the genuine smooth
order `Work.Stability.smoothOrder`). -/
theorem contDiff_bumpZ : ContDiff ℝ Work.Stability.smoothOrder bumpZ := by
  unfold bumpZ
  exact Work.Stability.chi_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The angular factor `Γ(θ) = (sinθ·cos²θ)^{α/3}` of the bump and of the profile `F_*` is `C^∞`
on the open interval `(0, π/2)`: there the base `sinθ·cos²θ` is positive, so the real power is a
composite of `exp` and `log` and loses no smoothness. -/
theorem contDiffOn_Gam_Ioo (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.Spaces.Gam α) (Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    ((Real.contDiff_sin (n := Work.Stability.smoothOrder)).mul
      ((Real.contDiff_cos (n := Work.Stability.smoothOrder)).pow 2)).contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => α / 3)
      (Set.Ioo 0 (π / 2)) := contDiffOn_const
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin x * Real.cos x ^ 2 ≠ 0 := by
    intro x hx
    have hs : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
    have hc : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    positivity
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (Real.sin x * Real.cos x ^ 2) ^ (α / 3)) (Set.Ioo 0 (π / 2)) :=
    ContDiffOn.rpow h1 h2 hne
  exact h3.congr (fun x _ => rfl)

/-! ## Functions of a single variable are `SmoothQuad` -/

/-- A function of `z` alone is `SmoothQuad` as soon as its slice is `C^∞` on `ℝ`. -/
theorem smoothQuad_of_fst {f : ℝ → ℝ} (hf : ContDiff ℝ Work.Stability.smoothOrder f) :
    SmoothQuad (fun z _ => f z) := by
  rw [SmoothQuad]
  exact hf.contDiffOn.comp contDiffOn_fst (fun _ _ => Set.mem_univ _)

/-- A function of `θ` alone is `SmoothQuad` as soon as its slice is `C^∞` on `(0, π/2)`. -/
theorem smoothQuad_of_snd {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f (Set.Ioo 0 (π / 2))) :
    SmoothQuad (fun _ θ => f θ) := by
  rw [SmoothQuad]
  exact hf.comp contDiffOn_snd (fun _ hp => hp.2)

/-! ## The bump -/

theorem SmoothQuad_hLoc (α : ℝ) : SmoothQuad (hLoc α) :=
  smoothQuad_mul (smoothQuad_of_fst contDiff_bumpZ)
    (smoothQuad_of_snd (contDiffOn_Gam_Ioo α))

end Work.FTS.LocData
