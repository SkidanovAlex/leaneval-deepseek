import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.law_Dform` — the elliptic law in `D`-form

C3 of the SB2/SB5 leaf interface (`Submission/Work/FTS_StreamBdry/SB25/Defs.lean`):
on the open quadrant,
`∂_θ V(P) = -(α² D_z²P + 5α D_zP + 6P) - F` whenever `bslOp α P = F` and `P` is `C²`.

The content is the algebraic rearrangement of

* `bslOp α P = -(α²z²)∂_zzP - (α(5+α)z)∂_zP + Lzero P`,
* `Lzero P = -∂_θθP + ∂_θ(tan θ·P) - 6P = -∂_θ(V(P)) - 6P` (the product rule in `θ`),
* `D_z²P = D_zP + z²∂_zzP` (the product rule in `z`).

Nothing here is specific to `bslOp`; the only analytic input is that the `θ`- and `z`-slices of
`P` and of its first partials are differentiable at an interior point, which is what
`ContDiffOn ℝ 2` on the open quadrant supplies (`Work.Spaces.uncurry_partial_c1`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB25

/-- **C3, the elliptic law in `D`-form.**  For `P` of class `C²` on the open quadrant with
`bslOp α P = F` there, one has `∂_θV(P) = -(α²D_z²P + 5αD_zP + 6P) - F` pointwise on the
quadrant. -/
theorem law_Dform (α : ℝ) (F P : ℝ → ℝ → ℝ) : Work.FTS_StreamBdry.SB25.LawDform α F P := by
  intro hP hlaw z θ hzθ
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hmem : Work.Construction.Qd ∈ 𝓝 (z, θ) := hQd.mem_nhds hzθ
  obtain ⟨_, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ1], hθ2⟩)
  -- differentiability of the slices of `P`, `∂_zP`, `∂_θP` (from `C²` on the open quadrant)
  have hAt2 : ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) := hP.contDiffAt hmem
  have hdP : DifferentiableAt ℝ (Function.uncurry P) (z, θ) :=
    hAt2.differentiableAt (by norm_num)
  have hd1θ : DifferentiableAt ℝ (fun θ' => P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right hdP
  obtain ⟨hpz1, hpth1⟩ := Work.Spaces.uncurry_partial_c1 hQd hP
  have hd2z : DifferentiableAt ℝ (fun z' => Work.Spaces.pz P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpz1.contDiffAt hmem).differentiableAt (by norm_num))
  have hd2θ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth1.contDiffAt hmem).differentiableAt (by norm_num))
  have hdtan : DifferentiableAt ℝ (fun θ' => Real.tan θ' * P z θ') θ :=
    (Real.differentiableAt_tan.mpr hcos).mul hd1θ
  -- (A) `∂_θ(V(P)) = ∂_θ²P - ∂_θ(tan θ·P)`
  have hpthVop : Work.Spaces.pth (Work.Construction.Vop P) z θ
      = Work.Spaces.pthIter 2 P z θ
        - Work.Spaces.pth (fun z θ => Real.tan θ * P z θ) z θ := by
    have hB : Work.Spaces.pth (Work.Construction.Vop P) z θ
        = deriv ((fun θ' => Work.Spaces.pth P z θ')
            - fun θ' => Real.tan θ' * P z θ') θ := rfl
    have hb : deriv (fun θ' => Work.Spaces.pth P z θ') θ = Work.Spaces.pthIter 2 P z θ := rfl
    rw [hB, deriv_sub hd2θ hdtan, hb]
    rfl
  -- (B) `D_z²P = D_zP + z²∂_zzP`
  have hkey : deriv (fun z' => z' * Work.Spaces.pz P z' θ) z
      = Work.Spaces.pz P z θ + z * Work.Spaces.pzIter 2 P z θ := by
    have hd1 : deriv (fun t => t * Work.Spaces.pz P t θ) z
        = deriv (fun t : ℝ => t) z * Work.Spaces.pz P z θ
          + z * deriv (fun t => Work.Spaces.pz P t θ) z := by
      exact deriv_mul differentiableAt_id hd2z
    have hb : deriv (fun t => Work.Spaces.pz P t θ) z = Work.Spaces.pzIter 2 P z θ := rfl
    rw [hd1, deriv_id'', hb]
    ring
  have hDz2 : Work.Spaces.DzIter 2 P z θ
      = Work.Spaces.Dz P z θ + z ^ 2 * Work.Spaces.pzIter 2 P z θ := by
    have h1 : Work.Spaces.DzIter 2 P z θ
        = z * deriv (fun z' => z' * Work.Spaces.pz P z' θ) z := rfl
    rw [h1, hkey]
    simp only [Work.Spaces.Dz]
    ring
  -- (C) `bslOp` expanded and `Lzero` with the product rule already substituted
  have hLz : Work.Elliptic.Lzero P z θ
      = - Work.Spaces.pthIter 2 P z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * P z θ) z θ - 6 * P z θ := rfl
  have hbsl : Work.Elliptic.bslOp α P z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 P z θ
        - α * (5 + α) * z * Work.Spaces.pz P z θ
        - Work.Spaces.pthIter 2 P z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * P z θ) z θ - 6 * P z θ := by
    rw [Work.Elliptic.bslOp_apply, hLz]
    ring
  -- (D) assembly
  have hh : Work.Elliptic.bslOp α P z θ = F z θ := hlaw z θ hzθ
  rw [hpthVop, ← hh, hbsl, hDz2]
  simp only [Work.Spaces.Dz]
  ring

end Work.FTS_StreamBdry.SB25
