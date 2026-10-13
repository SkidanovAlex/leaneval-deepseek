import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two-operator Leibniz rule in the open-quadrant class `SmoothOpen`

`Work.FTS.EllipticEst.SmoothOpen` is genuine `C^∞` on the *open* quadrant
`Q0 = (0,∞) × (0,π/2)` (the order `Work.Stability.smoothOrder`, *not* the analytic order
`⊤`), so neither the derivation-like structures `Work.Spaces.Zb_DerivLike`,
`Work.Spaces.Tb_DerivLike` (analytic order on `quadU = (-1,∞) × (0,π/2)`) nor their
genuine-order siblings `Work.FTS.H2.WPQ.Zb_DerivLike_sm`, `Tb_DerivLike_sm` (genuine order,
but still on the *bigger* quadrant `quadU`, which `SmoothOpen` does not reach at `z ≤ 0`)
apply directly.  Here the two instances are rebuilt on `Q0`, exactly as in
`Submission/Work/FTS/H2/WPQ/Leibniz.lean`, and the abstract two-operator rule
`Work.Spaces.DerivLike.twoOp_iterate_mul` then produces the binomial expansion, translated
back with `Work.Spaces.Zb_iterate_uncurry`, `Work.Spaces.Tb_iterate_uncurry` and
`Work.Spaces.uncurry_mul`. -/

/-- Uncurried functions which are `C^∞` in the genuine order on the open quadrant
`Q0 = (0,∞) × (0,π/2)`.  This is definitionally the class of
`Work.FTS.EllipticEst.SmoothOpen`. -/
def SmoothOpenU (F : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder F Work.FTS.EllipticEst.Q0

lemma SmoothOpenU.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothOpenU F) {p : ℝ × ℝ}
    (hp : p ∈ Work.FTS.EllipticEst.Q0) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)).differentiableAt (by simp)

theorem SmoothOpenU_FunClass : Work.Spaces.FunClass (X := ℝ × ℝ) SmoothOpenU where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) Work.FTS.EllipticEst.Q0
    exact ContDiffOn.const_smul c hA

/-- `Zb = z ∂_z` is a derivation-like operator on the `C^∞`-functions of the open quadrant
`Q0`.  (`Work.FTS.H2.WPQ.Zb_DerivLike_sm` is the same statement on the larger quadrant
`quadU`.) -/
theorem Zb_DerivLike_open :
    Work.Spaces.DerivLike Work.FTS.EllipticEst.Q0 SmoothOpenU Work.Spaces.Zb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun z' => A (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun z' => B (z', θ)) z :=
      Work.Spaces.differentiableAt_slice_fst (hB.differentiableAt hp)
    show Work.Spaces.Zb (A + B) (z, θ) = Work.Spaces.Zb A (z, θ) + Work.Spaces.Zb B (z, θ)
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
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (0 : ℝ)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Work.Spaces.Zb A (z, θ) = Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.FTS.EllipticEst.Q0 :=
      hA.fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) Work.FTS.EllipticEst.Q0 :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) Work.FTS.EllipticEst.Q0 :=
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

/-- `Tb = sin(2θ) ∂_θ` is a derivation-like operator on the `C^∞`-functions of the open
quadrant `Q0`.  (`Work.FTS.H2.WPQ.Tb_DerivLike_sm` is the same statement on `quadU`.) -/
theorem Tb_DerivLike_open :
    Work.Spaces.DerivLike Work.FTS.EllipticEst.Q0 SmoothOpenU Work.Spaces.Tb where
  add := fun A B hA hB => by
    rintro ⟨z, θ⟩ hp
    have hA' : DifferentiableAt ℝ (fun θ' => A (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hA.differentiableAt hp)
    have hB' : DifferentiableAt ℝ (fun θ' => B (z, θ')) θ :=
      Work.Spaces.differentiableAt_slice_snd (hB.differentiableAt hp)
    show Work.Spaces.Tb (A + B) (z, θ) = Work.Spaces.Tb A (z, θ) + Work.Spaces.Tb B (z, θ)
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
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π / 2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Work.Spaces.Tb A (z, θ) = Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.FTS.EllipticEst.Q0 :=
      hA.fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) Work.FTS.EllipticEst.Q0 :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1))
        Work.FTS.EllipticEst.Q0 :=
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

theorem leibniz_open_mixed :
    ∀ (j i : ℕ) (f g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ =
        ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro j i f g hf hg z θ hz hθ0 hθ1
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have h2 := (Work.Spaces.DerivLike.twoOp_iterate_mul (X := ℝ × ℝ)
      (s := Work.FTS.EllipticEst.Q0) (P := SmoothOpenU) (Z := Work.Spaces.Zb)
      (Θb := Work.Spaces.Tb) SmoothOpenU_FunClass Zb_DerivLike_open
      Tb_DerivLike_open j i (show SmoothOpenU (Function.uncurry f) from hf)
      (show SmoothOpenU (Function.uncurry g) from hg)) hp
  have h2' : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * ((Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f))) (z, θ)
               * (Work.Spaces.Zb^[j - b] (Work.Spaces.Tb^[i - a] (Function.uncurry g)))
                   (z, θ)) := by
    simpa using h2
  have hL : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ := by
    rw [Work.Spaces.uncurry_mul f g,
      Work.Spaces.Tb_iterate_uncurry i (fun z θ => f z θ * g z θ),
      Work.Spaces.Zb_iterate_uncurry j (Work.Spaces.DthIter i (fun z θ => f z θ * g z θ))]
    rfl
  have e_f : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f)) (z, θ)
      = Work.Spaces.mixed b a f z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a f,
      Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a f)]
    rfl
  have e_g : ∀ a b, Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry g)) (z, θ)
      = Work.Spaces.mixed b a g z θ := fun a b => by
    rw [Work.Spaces.Tb_iterate_uncurry a g,
      Work.Spaces.Zb_iterate_uncurry b (Work.Spaces.DthIter a g)]
    rfl
  rw [← hL, h2']
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [e_f a b, e_g (i - a) (j - b)]

end Work.FTS.OpenPkg.ProdOpen
