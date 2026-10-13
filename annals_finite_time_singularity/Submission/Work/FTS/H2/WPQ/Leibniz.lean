/-
Copyright: work module for the Elgindi finite-time singularity project.

# The two-operator Leibniz rule in the interior class `SmoothQuad`

`Work.Spaces.mixed_mul_eq` expands `D_z^j D_θ^i (f·g)` into the binomial double sum for
functions of class `SmoothInt` (smoothness in `z` on `(-1,∞)` at every angle, hence in
particular analytic-order slice regularity at the boundary angles).  The interior
replacement `Work.FTS.LocData.SmoothQuad` only gives smoothness on the open quadrant in the
genuine `C^∞` order `Work.Stability.smoothOrder`, which is strictly weaker than the analytic
order `⊤` used by the derivation-like structures `Work.Spaces.Zb_DerivLike`,
`Work.Spaces.Tb_DerivLike` (the operators `Zb = z ∂_z` and `Tb = sin 2θ ∂_θ` on uncurried
functions).  Here the two instances are rebuilt for the class
`SmoothUsm F = ContDiffOn ℝ smoothOrder F quadU`, and
`Work.Spaces.DerivLike.twoOp_iterate_mul` then gives the same expansion, together with the
translation lemmas `Work.Spaces.Zb_iterate_uncurry`, `Work.Spaces.Tb_iterate_uncurry`,
`Work.Spaces.uncurry_mul`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeBasic
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Uncurried functions which are `C^∞` on the open strip `(-1,∞) × (0,π/2)` in the genuine
smooth order (the class of `Work.FTS.LocData.SmoothQuad`). -/
def SmoothUsm (F : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder F Work.Spaces.quadU

theorem SmoothQuad.toSmoothUsm {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    SmoothUsm (Function.uncurry f) := hf

lemma SmoothUsm.differentiableAt {F : ℝ × ℝ → ℝ} (h : SmoothUsm F) {p : ℝ × ℝ}
    (hp : p ∈ Work.Spaces.quadU) : DifferentiableAt ℝ F p :=
  (h.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hp)).differentiableAt (by simp)

theorem SmoothUsm_FunClass : Work.Spaces.FunClass (X := ℝ × ℝ) SmoothUsm where
  add := fun A B hA hB => hA.add hB
  mul := fun A B hA hB => hA.mul hB
  smul := fun c A hA => by
    show ContDiffOn ℝ Work.Stability.smoothOrder (fun p => c * A p) Work.Spaces.quadU
    exact ContDiffOn.const_smul c hA

/-- `Zb = z ∂_z` is a derivation-like operator on the `C^∞` (genuine order) functions of the
open strip.  (`Work.Spaces.Zb_DerivLike` is the analytic-order version.) -/
theorem Zb_DerivLike_sm : Work.Spaces.DerivLike Work.Spaces.quadU SmoothUsm Work.Spaces.Zb where
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
    have hs : Set.EqOn (fun z' => A (z', θ)) (fun z' => B (z', θ)) (Set.Ioi (-1)) :=
      fun z' hz' => h ⟨hz', hp.2⟩
    show Work.Spaces.Zb A (z, θ) = Work.Spaces.Zb B (z, θ)
    simp only [Work.Spaces.Zb]
    rw [hs.deriv isOpen_Ioi hp.1]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.Spaces.quadU :=
      hA.fderiv_of_isOpen Work.Spaces.isOpen_quadU
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (1, 0)) Work.Spaces.quadU :=
      hfd.clm_apply contDiffOn_const
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 * (fderiv ℝ A p) (1, 0)) Work.Spaces.quadU :=
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

/-- `Tb = sin(2θ) ∂_θ` is a derivation-like operator on the `C^∞` (genuine order) functions of
the open strip.  (`Work.Spaces.Tb_DerivLike` is the analytic-order version.) -/
theorem Tb_DerivLike_sm : Work.Spaces.DerivLike Work.Spaces.quadU SmoothUsm Work.Spaces.Tb where
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
    have hs : Set.EqOn (fun θ' => A (z, θ')) (fun θ' => B (z, θ')) (Set.Ioo 0 (π/2)) :=
      fun θ' hθ' => h ⟨hp.1, hθ'⟩
    show Work.Spaces.Tb A (z, θ) = Work.Spaces.Tb B (z, θ)
    simp only [Work.Spaces.Tb]
    rw [hs.deriv isOpen_Ioo hp.2]
  preserve := fun A hA => by
    have hfd : ContDiffOn ℝ Work.Stability.smoothOrder (fderiv ℝ A) Work.Spaces.quadU :=
      hA.fderiv_of_isOpen Work.Spaces.isOpen_quadU
        (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hev : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => (fderiv ℝ A p) (0, 1)) Work.Spaces.quadU :=
      hfd.clm_apply contDiffOn_const
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hfun : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ A p) (0, 1)) Work.Spaces.quadU :=
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

/-- **The two-operator Leibniz rule in the interior class `SmoothQuad`.**

`D_z^j D_θ^i (f·g) = ∑_{a≤i} ∑_{b≤j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} g)`
for `z ≥ 0` and `0 < θ < π/2`. -/
theorem mixed_mul_eq_smoothQuad (j i : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) g z θ) := by
  intro z hz θ hθ
  have hz1 : z ∈ Set.Ioi (-1) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have hp : (z, θ) ∈ Work.Spaces.quadU := ⟨hz1, hθ⟩
  have h2 := (Work.Spaces.DerivLike.twoOp_iterate_mul (X := ℝ × ℝ)
      (s := Work.Spaces.quadU) (P := SmoothUsm) (Z := Work.Spaces.Zb)
      (Θb := Work.Spaces.Tb) SmoothUsm_FunClass Zb_DerivLike_sm
      Tb_DerivLike_sm j i (SmoothQuad.toSmoothUsm hf) (SmoothQuad.toSmoothUsm hg)) hp
  have h2' : Work.Spaces.Zb^[j] (Work.Spaces.Tb^[i]
        (Function.uncurry f * Function.uncurry g)) (z, θ)
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * ((Work.Spaces.Zb^[b] (Work.Spaces.Tb^[a] (Function.uncurry f))) (z, θ)
               * (Work.Spaces.Zb^[j - b] (Work.Spaces.Tb^[i - a] (Function.uncurry g))) (z, θ)) := by
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

end Work.FTS.H2.WPQ
