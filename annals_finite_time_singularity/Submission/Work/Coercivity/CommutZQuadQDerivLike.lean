/-
# Derivation-like structures for `D_z`, `D_θ` on the open quadrant `(0,∞) × (0,π/2)`

Transplants of `Work.Spaces.Zb_DerivLike` / `Work.Spaces.Tb_DerivLike` from the open
set `quadU = (-1,∞) × (0,π/2)` to the smaller open quadrant `quadQ = (0,∞) × (0,π/2)`,
with the class `SmoothQ` of functions smooth there.  These are the instances needed by
`CommutZ_HkIntegrand_add_le`, whose hypotheses are smoothness on `quadQ` only.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Coercivity.CommutZQuadQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.Coercivity

/-- `D_z` is a derivation-like operator for `SmoothQ` on the open quadrant `quadQ`. -/
theorem Zb_DerivLike_quadQ :
    Work.Spaces.DerivLike quadQ SmoothQ Work.Spaces.Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A + B) (z, θ)
        = Work.Spaces.Zb A (z, θ) + Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A + B) (z', θ)) =
          (fun z' => A (z', θ)) + (fun z' => B (z', θ)) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A * B) (z, θ)
        = Work.Spaces.Zb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [show (fun z' => (A * B) (z', θ)) =
          (fun z' => A (z', θ)) * (fun z' => B (z', θ)) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi 0) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Work.Spaces.Zb A (z, θ) = Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) quadQ :=
      hA.fderiv_of_isOpen isOpen_quadQ (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) quadQ :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) quadQ :=
      (contDiff_fst.contDiffOn).mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Work.Spaces.Zb A (z, θ) = z * (fderiv ℝ A (z, θ)) (1, 0)
    simp only [Work.Spaces.Zb]
    rw [Work.Spaces.deriv_slice_fst A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    show Work.Spaces.Zb (fun p => c * A p) (z, θ) = c * Work.Spaces.Zb A (z, θ)
    simp only [Work.Spaces.Zb]
    rw [deriv_const_mul c hA']
    ring

/-- `D_θ` is a derivation-like operator for `SmoothQ` on the open quadrant `quadQ`. -/
theorem Tb_DerivLike_quadQ :
    Work.Spaces.DerivLike quadQ SmoothQ Work.Spaces.Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A + B) (z, θ)
        = Work.Spaces.Tb A (z, θ) + Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A + B) (z, θ')) =
          (fun θ' => A (z, θ')) + (fun θ' => B (z, θ')) from rfl,
        deriv_add hA' hB']
    ring
  mul := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A * B) (z, θ)
        = Work.Spaces.Tb A (z, θ) * B (z, θ) + A (z, θ) * Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [show (fun θ' => (A * B) (z, θ')) =
          (fun θ' => A (z, θ')) * (fun θ' => B (z, θ')) from rfl,
        deriv_mul hA' hB']
    ring
  congr := fun A B h => by
    rintro ⟨z, θ⟩ hp
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π/2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Work.Spaces.Tb A (z, θ) = Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ A) quadQ :=
      hA.fderiv_of_isOpen isOpen_quadQ (by simp)
    have hev : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) quadQ :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) quadQ :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ ⊤
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1)) quadQ :=
      hsin.mul hev
    refine hfun.congr (fun p hp => ?_)
    obtain ⟨z, θ⟩ := p
    dsimp only
    show Work.Spaces.Tb A (z, θ) = Real.sin (2 * θ) * (fderiv ℝ A (z, θ)) (0, 1)
    simp only [Work.Spaces.Tb]
    rw [Work.Spaces.deriv_slice_snd A z θ (hA.differentiableAt hp)]
  smul := fun c A hA => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    show Work.Spaces.Tb (fun p => c * A p) (z, θ) = c * Work.Spaces.Tb A (z, θ)
    simp only [Work.Spaces.Tb]
    rw [deriv_const_mul c hA']
    ring

end Work.Coercivity
