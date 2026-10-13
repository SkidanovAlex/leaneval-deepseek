import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Stability.ModEqn
import Submission.Work.Stability.MainLHSSubN
import Submission.Work.Construction.Equation

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- **The dynamical `g`-equation (St2).**  If the rescaled profile `f = F_* + g` solves the
dynamical rescaled vorticity equation `DynEq` (St0) with stream function `φ`, then the
perturbation `g` satisfies

  `κ ∂_s g + 𝓛_Γ^T(g) = -(κ-1)F_* - (κb-1)D_zF_* + AK·L₁₂(Transport g)(0) + N₀ + N + N_*`

(`GEquation`), where `κ = κ(s)`, `b = b(s)` are the rates of the state and `N₀, N, N_*` are the
Construction area's nonlinear terms at the slice `F(·,·,s) = F_* + g(·,·,s)`.

Proof route: for `(z,θ) ∈ Qd` put `μ := κ-1`, `λ := b-1` and `F := Ftot α g s`, `Φ := slice φ s`.
`DynEq` says `κ(∂_s g + F + bD_zF) + UVR α F Φ = 0`; the static identity
`Work.Stability.MainLHSSubN` gives `κF + κbD_zF + UVR α F Φ = MainLHS α μ lam F - N α F Φ`, hence
`κ ∂_s g + MainLHS α μ lam F = N α F Φ`.  `Work.Construction.MainLHS_explicit` (tex 1345) expands
`MainLHS` using `hF` (definitional), `hDz`, `hpth`, `hL` from `GDerivData`,
`L₁₂(F_*) = 2α/(1+z)` (`Work.Construction.L12_Fstar_eq`) and the profile identity
`F_* + D_zF_* - (1/α)L₁₂(F_*)F_* = 0` (`Work.Construction.Fstar_stationary_identity`).  Then
`Work.Construction.Transport_eq` together with `L₁₂(F_*) = 2α/(1+z)` identifies the
`(3/(2α))sin(2θ)L₁₂(F_*)∂_θg` term with `Transport g`, and
`Work.Construction.LGammaT_eq` moves it to `𝓛_Γ^T(g)`, leaving exactly `gDynRHS`. -/
theorem DynGEquation {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (M : ModState) {g φ : F3}
    (hEq : DynEq α M (fun z θ s => Ftot α g s z θ) φ) (hD : GDerivData α g φ) :
    GEquation α M g φ := by
  intro z θ s hzθ
  -- the quadrant gives `z > 0`, `0 < θ < π/2`
  have hz0 : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < Real.pi / 2 := hzθ.2.2
  have hz : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have hznn : 0 ≤ z := le_of_lt hz0
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  -- the `s`-derivative of the full profile is that of the perturbation (`F_*` is `s`-free)
  have hderiv : deriv (fun u => Ftot α g u z θ) s = deriv (fun u => g z θ u) s := by
    have h1 : (fun u => Ftot α g u z θ) = fun u => Work.Construction.Fstar α z θ + g z θ u := by
      funext u; simp only [Work.Stability.Ftot]
    rw [h1, deriv_const_add]
  -- `DynEq` at `(z,θ,s)`, with the derivative of `g`
  have hdyn0 := hEq z θ s hzθ
  simp only [dynLHS, hderiv] at hdyn0
  -- (the slice of the full profile is definitionally the full profile itself)
  have hdyn : M.kappa s * (deriv (fun u => g z θ u) s + Ftot α g s z θ
        + M.b s * Work.Spaces.Dz (Ftot α g s) z θ)
      + Work.Construction.UVR α (Ftot α g s) (slice φ s) z θ = 0 := hdyn0
  -- the `Phi = PhiTil + Theta` decomposition, which is definitional
  have h1 : slice φ s z θ
      = Work.Construction.PhiTil α (Ftot α g s) (slice φ s) z θ
        + Work.Construction.Theta α (Ftot α g s) z θ := by
    simp only [Work.Construction.PhiTil]; ring
  -- the static identity (tex 1345 without the stationary equation), with `μ = κ-1`, `λ = b-1`
  have hsub := MainLHSSubN (α := α) (μ := M.kappa s - 1) (lam := M.b s - 1) hα z θ hcos h1
    (hD.h2 z θ s hzθ) (hD.h3 z θ s hzθ) (hD.h5 z θ s hzθ) (hD.h6 z θ s hzθ)
  have hcK : 1 + (M.kappa s - 1) = M.kappa s := by ring
  have hcB : 1 + (M.b s - 1) = M.b s := by ring
  simp only [hcK, hcB] at hsub
  -- hence `κ ∂_s g + MainLHS = N` (the `DynEq` holds only up to the `N`-correction)
  have hmain : M.kappa s * deriv (fun u => g z θ u) s
      + Work.Construction.MainLHS α (M.kappa s - 1) (M.b s - 1) (Ftot α g s) z θ
      = Work.Construction.N α (Ftot α g s) (slice φ s) z θ := by
    linear_combination hdyn - hsub
  -- the explicit expansion of `MainLHS` (tex 1345), using `GDerivData` and the `F_*` identities
  have hex := Work.Construction.MainLHS_explicit (α := α) (μ := M.kappa s - 1) (lam := M.b s - 1)
    hα z θ hz
    (by simp only [Work.Stability.Ftot, slice]) (hD.hDz z θ s hzθ) (hD.hpth z θ s hzθ) (hD.hL z s)
    (Work.Construction.L12_Fstar_eq hα hα1 hznn)
    (Work.Construction.Fstar_stationary_identity hα hα1 hznn)
  -- the transport term is exactly the `L₁₂(F_*)`-term of the expansion
  have hT : (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.pth (slice g s) z θ
      = Work.Coercivity.Transport (slice g s) z θ := by
    rw [Work.Construction.Transport_eq, Work.Construction.L12_Fstar_eq hα hα1 hznn]
    field_simp
  -- assembly: substitute the expansion into `hmain`, unfold `𝓛_Γ^T` and `gDynRHS`, and compare
  have key := hmain
  rw [hex, hT] at key
  simp only [Work.Stability.gDynRHS, Work.Construction.LGammaT_eq, Work.Construction.Nstar]
  ring_nf at key ⊢
  linarith [key]

end Work.Stability
