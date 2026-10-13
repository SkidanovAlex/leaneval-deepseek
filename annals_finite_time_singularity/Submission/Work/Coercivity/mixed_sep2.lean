import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.angRad_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.Coercivity

/-- Iterated `D_θ = sin(2θ) ∂_θ` of a *sum* of two angular-times-radial terms only sees the
angular factors.  This is the two-term version of `DthIter_ang_mul_rad`; it needs
`C^∞`-regularity of the two angular factors on the open interval, since the individual
summands are differentiated there. -/
private lemma mixed_sep2_dth (g1 g2 R1 R2 : ℝ → ℝ)
    (hg1 : ContDiffOn ℝ ⊤ g1 (Set.Ioo 0 (π/2)))
    (hg2 : ContDiffOn ℝ ⊤ g2 (Set.Ioo 0 (π/2))) :
    ∀ (n : ℕ) (z θ : ℝ), θ ∈ Set.Ioo 0 (π/2) →
      Work.Spaces.DthIter n (fun z θ => g1 θ * R1 z + g2 θ * R2 z) z θ
        = CT.DthIterAng n g1 θ * R1 z + CT.DthIterAng n g2 θ * R2 z := by
  intro n
  induction n with
  | zero => intro z θ hθ; rfl
  | succ n ih =>
    intro z θ hθ
    have hc1 := DthIterAng_contDiffOn_Ioo g1 hg1 n
    have hc2 := DthIterAng_contDiffOn_Ioo g2 hg2 n
    have hd1 : DifferentiableAt ℝ (CT.DthIterAng n g1) θ :=
      (hc1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)
    have hd2 : DifferentiableAt ℝ (CT.DthIterAng n g2) θ :=
      (hc2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)
    have hev : (fun θ' => Work.Spaces.DthIter n
          (fun z θ => g1 θ * R1 z + g2 θ * R2 z) z θ')
        =ᶠ[𝓝 θ] (fun θ' => CT.DthIterAng n g1 θ' * R1 z + CT.DthIterAng n g2 θ' * R2 z) :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hθ) (fun θ' hθ' => ih z θ' hθ')
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n
        (fun z θ => g1 θ * R1 z + g2 θ * R2 z) z θ') θ
      = CT.DthIterAng (n + 1) g1 θ * R1 z + CT.DthIterAng (n + 1) g2 θ * R2 z
    have hsplit : deriv (fun θ' => CT.DthIterAng n g1 θ' * R1 z
          + CT.DthIterAng n g2 θ' * R2 z) θ
        = deriv (fun θ' => CT.DthIterAng n g1 θ' * R1 z) θ
          + deriv (fun θ' => CT.DthIterAng n g2 θ' * R2 z) θ :=
      deriv_add (hd1.mul_const (R1 z)) (hd2.mul_const (R2 z))
    have h1d : deriv (fun θ' => CT.DthIterAng n g1 θ' * R1 z) θ
        = deriv (CT.DthIterAng n g1) θ * R1 z := deriv_mul_const hd1 (R1 z)
    have h2d : deriv (fun θ' => CT.DthIterAng n g2 θ' * R2 z) θ
        = deriv (CT.DthIterAng n g2) θ * R2 z := deriv_mul_const hd2 (R2 z)
    rw [hev.deriv_eq, hsplit, h1d, h2d, CT.DthIterAng_succ n g1, CT.DthIterAng_succ n g2]
    ring

/-- Iterated `D_z = z ∂_z` of a function that agrees on `(0,∞)` (at a fixed angle `θ`) with
a sum of two separated terms `h₁(θ)·R₁(z) + h₂(θ)·R₂(z)` only differentiates the radial
factors.  This is the two-term version of `DzIter_eq_of_eqOn_Ioo`. -/
private lemma mixed_sep2_dz (G : ℝ → ℝ → ℝ) (h1 h2 R1 R2 : ℝ → ℝ) (θ : ℝ)
    (hG : ∀ z : ℝ, 0 < z → G z θ = h1 θ * R1 z + h2 θ * R2 z) :
    ∀ j : ℕ,
      (∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R1) z) →
      (∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R2) z) →
      ∀ z : ℝ, 0 < z →
        Work.Spaces.DzIter j G z θ
          = h1 θ * CT.DzRIter j R1 z + h2 θ * CT.DzRIter j R2 z := by
  intro j
  induction j with
  | zero => intro _ _ z hz; exact hG z hz
  | succ j ih =>
    intro hR1 hR2 z hz
    have hR1' : ∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R1) z :=
      fun k hk z hz => hR1 k (le_trans hk (Nat.le_succ j)) z hz
    have hR2' : ∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R2) z :=
      fun k hk z hz => hR2 k (le_trans hk (Nat.le_succ j)) z hz
    have ih' := ih hR1' hR2'
    have hd1 : DifferentiableAt ℝ (CT.DzRIter j R1) z := hR1 j (Nat.le_succ j) z hz
    have hd2 : DifferentiableAt ℝ (CT.DzRIter j R2) z := hR2 j (Nat.le_succ j) z hz
    have hev : (fun z' => Work.Spaces.DzIter j G z' θ) =ᶠ[𝓝 z]
        (fun z' => h1 θ * CT.DzRIter j R1 z' + h2 θ * CT.DzRIter j R2 z') :=
      eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ih' z' hz')
    show z * deriv (fun z' => Work.Spaces.DzIter j G z' θ) z
      = h1 θ * CT.DzRIter (j + 1) R1 z + h2 θ * CT.DzRIter (j + 1) R2 z
    have hsplit : deriv (fun z' => h1 θ * CT.DzRIter j R1 z'
          + h2 θ * CT.DzRIter j R2 z') z
        = deriv (fun z' => h1 θ * CT.DzRIter j R1 z') z
          + deriv (fun z' => h2 θ * CT.DzRIter j R2 z') z :=
      deriv_add (hd1.const_mul (h1 θ)) (hd2.const_mul (h2 θ))
    have h1d : deriv (fun z' => h1 θ * CT.DzRIter j R1 z') z
        = h1 θ * deriv (CT.DzRIter j R1) z := deriv_const_mul (h1 θ) hd1
    have h2d : deriv (fun z' => h2 θ * CT.DzRIter j R2 z') z
        = h2 θ * deriv (CT.DzRIter j R2) z := deriv_const_mul (h2 θ) hd2
    rw [hev.deriv_eq, hsplit, h1d, h2d, CT.DzRIter_succ j R1, CT.DzRIter_succ j R2]
    show z * (h1 θ * deriv (CT.DzRIter j R1) z + h2 θ * deriv (CT.DzRIter j R2) z)
      = h1 θ * (z * deriv (CT.DzRIter j R1) z) + h2 θ * (z * deriv (CT.DzRIter j R2) z)
    ring

theorem mixed_sep2 (g1 g2 R1 R2 : ℝ → ℝ) (j i : ℕ)
    (hg1 : ContDiffOn ℝ ⊤ g1 (Set.Ioo 0 (π/2)))
    (hg2 : ContDiffOn ℝ ⊤ g2 (Set.Ioo 0 (π/2)))
    (hR1 : ∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R1) z)
    (hR2 : ∀ k ≤ j, ∀ z : ℝ, 0 < z → DifferentiableAt ℝ (CT.DzRIter k R2) z) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π/2) →
      Work.Spaces.mixed j i (fun z θ => g1 θ * R1 z + g2 θ * R2 z) z θ
        = CT.DthIterAng i g1 θ * CT.DzRIter j R1 z
          + CT.DthIterAng i g2 θ * CT.DzRIter j R2 z := by
  intro z θ hz hθ
  have hG : ∀ z : ℝ, 0 < z →
      Work.Spaces.DthIter i (fun z θ => g1 θ * R1 z + g2 θ * R2 z) z θ
        = CT.DthIterAng i g1 θ * R1 z + CT.DthIterAng i g2 θ * R2 z :=
    fun z _ => mixed_sep2_dth g1 g2 R1 R2 hg1 hg2 i z θ hθ
  have key := mixed_sep2_dz (Work.Spaces.DthIter i (fun z θ => g1 θ * R1 z + g2 θ * R2 z))
    (CT.DthIterAng i g1) (CT.DthIterAng i g2) R1 R2 θ hG j hR1 hR2 z hz
  simpa only [Work.Spaces.mixed] using key

end Work.Coercivity
