import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false

/-- The reflection `θ ↦ π/2 - θ` of a slice. -/
def reflSlice (h : ℝ → ℝ) : ℝ → ℝ := fun θ => h (Real.pi / 2 - θ)

lemma sin_two_reflSlice (θ : ℝ) : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
  have h : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
  rw [h, Real.sin_pi_sub]

/-- `Dth1Iter` preserves `C^∞` on an open interval (slices are smooth on `(0,π/2)`). -/
lemma contDiffOn_dth1Iter {h : ℝ → ℝ} (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (j : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Elliptic.Dth1Iter j h) (Set.Ioo 0 (Real.pi / 2)) := by
  induction j with
  | zero => simpa using hsm
  | succ j ih =>
      rw [Work.Elliptic.Dth1Iter_succ]
      have hder : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (Work.Elliptic.Dth1Iter j h))
          (Set.Ioo 0 (Real.pi / 2)) :=
        ih.deriv_of_isOpen isOpen_Ioo (by simp)
      have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter j h) θ)
          (Set.Ioo 0 (Real.pi / 2)) := hsin.mul hder
      exact h1

theorem reflSlice_facts (i : ℕ) {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ')) θ
          = (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ)) ∧
      (∀ F : ℝ → ℝ,
        (∫ θ in (0 : ℝ)..(Real.pi / 2), F (Real.pi / 2 - θ))
          = ∫ θ in (0 : ℝ)..(Real.pi / 2), F θ) ∧
      (∀ θ : ℝ, Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ)) := by
  refine ⟨?_, ?_, sin_two_reflSlice⟩
  · -- anti-invariance of `D_θ` under the reflection
    have hmem : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.pi / 2 - θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    intro θ
    induction i generalizing θ with
    | zero => intro _; simp
    | succ i ih =>
        intro hθ
        have hderiv : ∀ j : ℕ, DifferentiableAt ℝ (Work.Elliptic.Dth1Iter j h)
            (Real.pi / 2 - θ) := fun j =>
          ((contDiffOn_dth1Iter hsm j).contDiffAt (isOpen_Ioo.mem_nhds (hmem θ hθ))).differentiableAt
            (by simp)
        have hev : Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ'))
            =ᶠ[𝓝 θ] fun θ' => (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ') := by
          filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
          exact ih θ' hθ'
        have hcomp : HasDerivAt (fun θ' : ℝ => Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ'))
            (deriv (Work.Elliptic.Dth1Iter i h) (Real.pi / 2 - θ) * (-1)) θ := by
          have h1 : HasDerivAt (fun θ' : ℝ => Real.pi / 2 - θ') (-1) θ := by
            have h0 := (hasDerivAt_const (x := θ) (c := Real.pi / 2)).sub (hasDerivAt_id θ)
            have hf : ((fun _ : ℝ => Real.pi / 2) - (id : ℝ → ℝ))
                = fun θ' : ℝ => Real.pi / 2 - θ' := by
              funext θ'; simp
            rw [hf] at h0
            convert h0 using 1 <;> ring
          exact (hderiv i).hasDerivAt.comp θ h1
        have hchain : deriv (fun θ' : ℝ => (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ')) θ
            = (-1 : ℝ) ^ i * (-(deriv (Work.Elliptic.Dth1Iter i h) (Real.pi / 2 - θ))) := by
          rw [(hcomp.const_mul ((-1 : ℝ) ^ i)).deriv]
          ring
        have hd : deriv (Work.Elliptic.Dth1Iter i (fun θ' => h (Real.pi / 2 - θ'))) θ
            = deriv (fun θ' : ℝ => (-1 : ℝ) ^ i * Work.Elliptic.Dth1Iter i h (Real.pi / 2 - θ')) θ :=
          hev.deriv_eq
        rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_succ]
        simp only [Work.Elliptic.Dth1]
        rw [hd, hchain, sin_two_reflSlice, pow_succ]
        ring
  · intro F
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
      (d := Real.pi / 2) (f := F)
    simpa using h

end Work.FTS.H2.DivQ
