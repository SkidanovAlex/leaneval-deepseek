/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.CruxCore` — the three staircases from the box-uniform data

Given

* the uniform `C^{2,β}` box data `BoxUniform2 a b H` of a family `H`,
* an Arzelà–Ascoli extraction `φ`, `g` with componentwise *uniform* convergence on the box of the
  six within-partials `wJet` and continuity of the limit `g`,
* the pointwise convergence of the values `H n z θ → G z θ` on the box,
* the slice data `SliceData a b (uncurry (H (φ n)))` of every member,

the three installments of `BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials` produce the
within-derivative statements of `G` (with the partials `g · 0`, `g · 1`) and of those partials
themselves (with the second partials `g · 2 … g · 5`).  Assembling the three with
`contDiffOn_two_of_fderivWithin_data` then gives `ContDiffOn ℝ 2 (uncurry G) (cbox a b)`
(`Crux.lean`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-- **The three staircases.**  From the box-uniform data of the family `H`, an Arzelà–Ascoli
extraction (`φ`, `g`) and the slice data of the members, the limit `G` has within-derivative
`ellCop (g·0) (g·1)` on the box, and its two components `g·0`, `g·1` have within-derivatives
`ellCop (g·2) (g·3)` and `ellCop (g·4) (g·5)`. -/
theorem staircase_data_of_boxUniform2_core {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hU : BoxUniform2 a b H)
    {φ : ℕ → ℕ} {g : ℝ × ℝ → (Fin 6 → ℝ)}
    (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hcv : ∀ m : Fin 6, TendstoUniformlyOn
      (fun n p => wJet (cbox a b) (Function.uncurry (H (φ n))) p m)
      (fun p => g p m) Filter.atTop (cbox a b))
    (hcontg : ContinuousOn g (cbox a b))
    (hconv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (𝓝 (G z θ)))
    (hslice : ∀ n, SliceData a b (Function.uncurry (H (φ n)))) :
    (∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry G)
        (ellCop (g p 0) (g p 1)) (cbox a b) p) ∧
    (∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 0))
        (ellCop (g p 2) (g p 3)) (cbox a b) p) ∧
    (∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 1))
        (ellCop (g p 4) (g p 5)) (cbox a b) p) := by
  obtain ⟨K, β, hβ, hsm, hb, hh⟩ := hU
  -- continuity of the members' within-partials on the box
  have hcontJ : ∀ (n : ℕ) (m : Fin 6), ContinuousOn
      (fun p : ℝ × ℝ => wJet (cbox a b) (Function.uncurry (H (φ n))) p m) (cbox a b) :=
    fun n m => continuousOn_wJet hab (hsm (φ n)) m
  have hcontP : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPz (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_zero] using hcontJ n 0
  have hcontQ : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPth (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPth (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_one] using hcontJ n 1
  have hcontPz : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPzz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPzz (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_two] using hcontJ n 2
  have hcontPt : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPtz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPtz (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_three] using hcontJ n 3
  have hcontQz : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPzt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPzt (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_four] using hcontJ n 4
  have hcontQt : ∀ n, ContinuousOn (Function.uncurry (fun z θ =>
      wPtt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))) (cbox a b) := by
    intro n
    change ContinuousOn (fun p : ℝ × ℝ =>
      wPtt (cbox a b) (Function.uncurry (H (φ n))) p) (cbox a b)
    simpa only [wJet_apply_five] using hcontJ n 5
  -- continuity of the limit's components
  have hcontg0 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 0)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 0) (cbox a b)
    exact (continuous_apply 0).comp_continuousOn hcontg
  have hcontg1 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 1)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 1) (cbox a b)
    exact (continuous_apply 1).comp_continuousOn hcontg
  have hcontg2 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 2)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 2) (cbox a b)
    exact (continuous_apply 2).comp_continuousOn hcontg
  have hcontg3 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 3)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 3) (cbox a b)
    exact (continuous_apply 3).comp_continuousOn hcontg
  have hcontg4 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 4)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 4) (cbox a b)
    exact (continuous_apply 4).comp_continuousOn hcontg
  have hcontg5 : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 5)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 5) (cbox a b)
    exact (continuous_apply 5).comp_continuousOn hcontg
  -- the first staircase: the values and their two first partials
  have hS0 : ∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry G)
      (ellCop (g p 0) (g p 1)) (cbox a b) p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := mem_cbox.mp hp
    exact Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
      (a := a) (b := b) (c := 0) (d := π / 2) (le_of_lt hab) (by positivity)
      (H := fun n => H (φ n)) (H₀ := G)
      (P := fun n z θ => wPz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (P₀ := fun z θ => g (z, θ) 0)
      (Q := fun n z θ => wPth (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (Q₀ := fun z θ => g (z, θ) 1)
      (fun n => (hsm (φ n)).continuousOn)
      (fun n z hz θ hθ => (hslice n).1 z hz θ hθ)
      (fun n z hz θ hθ => (hslice n).2.1 z hz θ hθ)
      hcontP hcontQ
      (fun z hz θ hθ => (hconv z hz θ hθ).comp hφ)
      (hcv 0) (hcv 1) hcontg0 hcontg1 z hz θ hθ
  -- the second staircase: the partial `g·0` and its two first partials
  have hS1 : ∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 0))
      (ellCop (g p 2) (g p 3)) (cbox a b) p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := mem_cbox.mp hp
    exact Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
      (a := a) (b := b) (c := 0) (d := π / 2) (le_of_lt hab) (by positivity)
      (H := fun n z θ => wPz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (H₀ := fun z θ => g (z, θ) 0)
      (P := fun n z θ => wPzz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (P₀ := fun z θ => g (z, θ) 2)
      (Q := fun n z θ => wPtz (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (Q₀ := fun z θ => g (z, θ) 3)
      hcontP
      (fun n z hz θ hθ => (hslice n).2.2.1 z hz θ hθ)
      (fun n z hz θ hθ => (hslice n).2.2.2.1 z hz θ hθ)
      hcontPz hcontPt
      (fun z hz θ hθ => (hcv 0).tendsto_at ⟨hz, hθ⟩)
      (hcv 2) (hcv 3) hcontg2 hcontg3 z hz θ hθ
  -- the third staircase: the partial `g·1` and its two first partials
  have hS2 : ∀ p ∈ cbox a b, HasFDerivWithinAt (Function.uncurry (fun z θ => g (z, θ) 1))
      (ellCop (g p 4) (g p 5)) (cbox a b) p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := mem_cbox.mp hp
    exact Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
      (a := a) (b := b) (c := 0) (d := π / 2) (le_of_lt hab) (by positivity)
      (H := fun n z θ => wPth (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (H₀ := fun z θ => g (z, θ) 1)
      (P := fun n z θ => wPzt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (P₀ := fun z θ => g (z, θ) 4)
      (Q := fun n z θ => wPtt (cbox a b) (Function.uncurry (H (φ n))) (z, θ))
      (Q₀ := fun z θ => g (z, θ) 5)
      hcontQ
      (fun n z hz θ hθ => (hslice n).2.2.2.2.1 z hz θ hθ)
      (fun n z hz θ hθ => (hslice n).2.2.2.2.2 z hz θ hθ)
      hcontQz hcontQt
      (fun z hz θ hθ => (hcv 1).tendsto_at ⟨hz, hθ⟩)
      (hcv 4) (hcv 5) hcontg4 hcontg5 z hz θ hθ
  exact ⟨hS0, hS1, hS2⟩

end Work.FTS_EllLimOK.BoxDataH
