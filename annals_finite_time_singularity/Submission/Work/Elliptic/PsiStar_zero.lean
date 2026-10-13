/-
Copyright: work module for the Elgindi finite-time singularity project.

# Step 1 of Proposition `prop:L2`: the angular moment of the solution vanishes

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates', proof of Proposition `prop:L2`,
Step 1 (tex lines 740--750).  If `Ψ` solves `(PolarBSL)` with source `F` and `F` satisfies the
solvability condition `∫_0^{π/2} F(z,θ) sin θ cos²θ dθ ≡ 0`, then the angular moment

  `F_*(Ψ)(z) = ∫_0^{π/2} Ψ(z,θ) sin θ cos²θ dθ`

vanishes identically.  Indeed `PsiStar_ode` shows that `z ↦ F_*(Ψ)(z)` solves the homogeneous
Euler equation `α²z²g'' + α(5+α)zg' = 0`, whose general solution is `c₁ + c₂z^{-5/α}`, and the two
boundary conditions (`g → 0` at `∞` and `z²g → 0` at `0⁺`) force `c₁ = c₂ = 0`
(`rigidity_ode`).

The hypothesis `hdec` is the paper's own "condition that `Ψ_⋆ → 0` as `R → ∞`" (tex line 745); it
is *not* a consequence of the pointwise-in-`θ` decay recorded in `IsBslSol`, which is why it is
part of the statement.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Elliptic.rigidity_ode
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval ContDiff
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The three successive `z`-derivatives of `z ↦ F_*(Ψ)(z) = ∫_0^{π/2} Ψ(z,θ) sinθcos²θ dθ`,
obtained by differentiating under the integral sign three times. -/
lemma Fstar_iterated_deriv (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    (∀ z ∈ Set.Ioi (-1 : ℝ), HasDerivAt (fun z' => Fstar Ψ z')
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ) z) ∧
    (∀ z ∈ Set.Ioi (-1 : ℝ),
      HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z' θ * sinCos2 θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.pz Ψ) z θ * sinCos2 θ) z) ∧
    (∀ z ∈ Set.Ioi (-1 : ℝ),
      HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.pz Ψ) z' θ * sinCos2 θ)
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pz Ψ)) z θ * sinCos2 θ) z) := by
  have hφ : ContinuousOn sinCos2 (Set.Icc 0 (π / 2)) := by unfold sinCos2; fun_prop
  have hsm1 : Work.Spaces.SmoothNbhd (Work.Spaces.pz Ψ) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm
  have hsm2 : Work.Spaces.SmoothNbhd (Work.Spaces.pz (Work.Spaces.pz Ψ)) :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm1
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · simpa only [Fstar] using hasDerivAt_integral_Iθ Ψ sinCos2 hsm hφ hz
  · exact hasDerivAt_integral_Iθ (Work.Spaces.pz Ψ) sinCos2 hsm1 hφ hz
  · exact hasDerivAt_integral_Iθ (Work.Spaces.pz (Work.Spaces.pz Ψ)) sinCos2 hsm2 hφ hz

/-- `z ↦ F_*(Ψ)(z)` is `C²` on `(0,∞)` for `Ψ` smooth on a neighbourhood of the quadrant. -/
lemma contDiffOn_two_Fstar (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ContDiffOn ℝ 2 (fun z => Fstar Ψ z) (Set.Ioi 0) := by
  obtain ⟨hA, hB, hC⟩ := Fstar_iterated_deriv Ψ hsm
  have hA' : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z' => Fstar Ψ z')
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ) z :=
    fun z hz => hA z (show (-1 : ℝ) < z by have hz' : (0 : ℝ) < z := hz; linarith)
  have hB' : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z' θ * sinCos2 θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.pz Ψ) z θ * sinCos2 θ) z :=
    fun z hz => hB z (show (-1 : ℝ) < z by have hz' : (0 : ℝ) < z := hz; linarith)
  have hC' : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.pz Ψ) z' θ * sinCos2 θ)
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pz Ψ)) z θ * sinCos2 θ) z :=
    fun z hz => hC z (show (-1 : ℝ) < z by have hz' : (0 : ℝ) < z := hz; linarith)
  have hdiff1 : DifferentiableOn ℝ (fun z => Fstar Ψ z) (Set.Ioi 0) :=
    fun z hz => (hA' z hz).differentiableAt.differentiableWithinAt
  have heq1 : Set.EqOn (deriv (fun z => Fstar Ψ z))
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * sinCos2 θ) (Set.Ioi 0) :=
    fun z hz => (hA' z hz).deriv
  have hdiff2 : DifferentiableOn ℝ (deriv (fun z => Fstar Ψ z)) (Set.Ioi 0) :=
    DifferentiableOn.congr (fun z hz => (hB' z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (heq1 hz))
  have heq2 : Set.EqOn (deriv (deriv (fun z => Fstar Ψ z)))
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.pz Ψ) z θ * sinCos2 θ)
      (Set.Ioi 0) := by
    intro z hz
    have hev : deriv (fun z' => Fstar Ψ z')
        =ᶠ[𝓝 z] (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z' θ * sinCos2 θ) :=
      heq1.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hz)
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact (hB' z hz).deriv
  have hcontB : ContinuousOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz (Work.Spaces.pz Ψ) z θ * sinCos2 θ)
      (Set.Ioi 0) :=
    DifferentiableOn.continuousOn
      (fun z hz => (hC' z hz).differentiableAt.differentiableWithinAt)
  have hcont2 : ContinuousOn (deriv (deriv (fun z => Fstar Ψ z))) (Set.Ioi 0) :=
    ContinuousOn.congr hcontB (fun z hz => heq2 hz)
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).mpr ⟨hdiff1, ?_, ?_⟩
  · exact fun hω => absurd hω (by simp)
  · refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioi).mpr ⟨hdiff2, ?_, ?_⟩
    · exact fun hω => absurd hω (by simp)
    · exact contDiffOn_zero.mpr hcont2

/-- **Step 1 of Proposition `prop:L2`** (tex 740--750): under the solvability condition on the
source, the angular moment of the solution vanishes. -/
theorem PsiStar_zero (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα2 : α < 5 / 2)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : IsBslSol α F Ψ)
    (horth : OrthCond F)
    (hdec : Tendsto (fun z => Fstar Ψ z) atTop (nhds 0)) :
    ∀ z ∈ Work.Spaces.Iz, Fstar Ψ z = 0 := by
  obtain ⟨hA, -, -⟩ := Fstar_iterated_deriv Ψ hsm
  -- `F_*(Ψ)` is continuous at `0` (it is differentiable there)
  have hcont : ContinuousAt (fun z => Fstar Ψ z) 0 :=
    (hA 0 (by norm_num)).continuousAt
  -- the ODE for the angular moment, with zero right hand side
  have hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (fun z'' => Fstar Ψ z'') z') z
        + α * (5 + α) * z * deriv (fun z' => Fstar Ψ z') z = 0 := by
    intro z hz
    have h := PsiStar_ode α F Ψ z hα hz hsm hsol
    rw [horth z] at h
    linarith [h]
  -- `z² F_*(Ψ)(z) → 0` as `z → 0⁺`
  have h0 : Tendsto (fun z => z ^ 2 * Fstar Ψ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun z : ℝ => z ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have := (continuous_pow 2).continuousAt (x := (0 : ℝ))
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z => Fstar Ψ z) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Fstar Ψ 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h3 := h1.mul h2
    simpa using h3
  have hzero : ∀ z ∈ Set.Ioi (0 : ℝ), Fstar Ψ z = 0 :=
    rigidity_ode α hα hα2 (fun z => Fstar Ψ z) (contDiffOn_two_Fstar Ψ hsm)
      (by simpa only using hode) hdec h0
  intro z hz
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with hzeq | hzpos
  · -- `z = 0`: pass to the limit from the right
    subst hzeq
    have hlim1 : Tendsto (fun w : ℝ => Fstar Ψ w) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Fstar Ψ 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun w : ℝ => Fstar Ψ w) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with w hw
      exact (hzero w hw).symm
    exact tendsto_nhds_unique hlim1 hlim2
  · exact hzero z hzpos

end Work.Elliptic
