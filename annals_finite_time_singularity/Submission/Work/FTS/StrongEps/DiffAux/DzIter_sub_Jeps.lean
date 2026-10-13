import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

/-- **Slotwise subtraction of the iterated `D_z`-operator.**  If the `z`-slices of the iterates
`D_z^k A`, `D_z^k B` (at the fixed angle `θ`) are differentiable on `(0,∞)` for every `k ≤ j`,
then `D_z^j` is subtractive at `(z,θ)`.

(`D_z = z∂_z` is a `deriv`-based operator, so the induction has to produce the differentiability
of the slices from the hypotheses at each level; this is where the `DifferentiableOn` hypotheses
are used.) -/
theorem DzIter_sub_of_diffOn :
    ∀ j : ℕ, ∀ {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, 0 < z →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ) (Set.Ioi 0)) →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ) (Set.Ioi 0)) →
      Work.Spaces.DzIter j (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DzIter j A z θ - Work.Spaces.DzIter j B z θ := by
  intro j
  induction j with
  | zero => intro A B z θ hz hA hB; rfl
  | succ n ih =>
    intro A B z θ hz hA hB
    have hzmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
    have hA' : ∀ k ≤ n, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ)
        (Set.Ioi 0) := fun k hk => hA k (le_trans hk (Nat.le_succ n))
    have hB' : ∀ k ≤ n, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ)
        (Set.Ioi 0) := fun k hk => hB k (le_trans hk (Nat.le_succ n))
    have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => A z θ - B z θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n A z' θ - Work.Spaces.DzIter n B z' θ) := by
      filter_upwards [hzmem] with z' hz'
      exact ih hz' hA' hB'
    have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n A z' θ) z :=
      (hA' n le_rfl).differentiableAt hzmem
    have hdB : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n B z' θ) z :=
      (hB' n le_rfl).differentiableAt hzmem
    have hd : deriv (fun z' => Work.Spaces.DzIter n A z' θ - Work.Spaces.DzIter n B z' θ) z
        = deriv (fun z' => Work.Spaces.DzIter n A z' θ) z
          - deriv (fun z' => Work.Spaces.DzIter n B z' θ) z := deriv_sub hdA hdB
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [heq.deriv_eq, hd]
    ring

/-- **The `D_z^j`-slot of the mollifier difference `J_ε f - f`** is the difference of the slots:
`D_z^j (J_ε f - f) = J_ε (D_z^j f) - D_z^j f` at every point of the open quadrant, for `f` which
is `C^n` on the quadrant for every `n`.

The two ingredients are `DzIter_sub_of_diffOn` above (subtraction of the `deriv`-based iterated
operator, from the differentiability of the slices) and the two commuting results
`DzIter_Jeps_of_smooth` (`D_z^j` commutes with `J_ε` on the quadrant for a smooth profile) and
`hasDerivAt_Jeps_slice_z` (the `z`-slices of `J_ε g` are differentiable, with an explicit
derivative, for any profile smooth on the quadrant). -/
theorem DzIter_sub_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter j f) z θ
        - Work.Spaces.DzIter j f z θ := by
  have hS : Work.FTS.StrongEps.SmQ f := Work.FTS.StrongEps.smQ_of_forall_nat hf
  -- the `z`-slices of the `D_z`-iterates of `J_ε f` are differentiable on `(0,∞)`: on the open
  -- quadrant the iterates agree with `J_ε` of the iterates of the profile, whose slices are
  -- differentiable by `hasDerivAt_Jeps_slice_z`
  have hAz : ∀ k ≤ j, DifferentiableOn ℝ
      (fun z' => Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z' θ) (Set.Ioi 0) := by
    intro k hk z' hz'
    have hk' : Work.FTS.StrongEps.SmQ (Work.Spaces.DzIter k f) := hS.DzIter k
    have hforall : ∀ n : ℕ,
        ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter k f)) Work.FTS.StrongEps.Quad :=
      fun n => contDiffOn_infty.mp hk' n
    have hev : (fun z'' => Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z'' θ)
        =ᶠ[𝓝 z'] (fun z'' =>
          Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter k f) z'' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
      exact (Work.FTS.StrongEps.DzIter_Jeps_of_smooth ρ hρ hε (g := f) hS k)
        (show (z'', θ) ∈ Work.FTS.StrongEps.Quad from ⟨hz'', hθ⟩)
    have hd : DifferentiableAt ℝ
        (fun z'' => Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter k f) z'' θ) z' :=
      (hasDerivAt_Jeps_slice_z ρ hρ hε hforall hz' hθ).differentiableAt
    exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt
  -- the `z`-slices of the `D_z`-iterates of the profile itself are differentiable, by smoothness
  have hBz : ∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k f z' θ) (Set.Ioi 0) :=
    fun k _ => ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.DzIter k f)
      (hS.DzIter k) hθ).differentiableOn (by simp [Work.Stability.smoothOrder]))
  rw [DzIter_sub_of_diffOn j hz hAz hBz]
  rw [show Work.Spaces.DzIter j (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter j f) z θ from
    (Work.FTS.StrongEps.DzIter_Jeps_of_smooth ρ hρ hε (g := f) hS j)
      (show (z, θ) ∈ Work.FTS.StrongEps.Quad from ⟨hz, hθ⟩)]

end Work.FTS.StrongEps.DiffAux
