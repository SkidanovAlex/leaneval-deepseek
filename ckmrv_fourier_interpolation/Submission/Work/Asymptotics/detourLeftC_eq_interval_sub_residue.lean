import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.rectInt_eq_residue
import Submission.Work.Asymptotics.kerFormDefs
import Submission.Work.Asymptotics.kerForm_edgeH
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Asymptotics.kerFormAux

namespace Work.Asymptotics

/-- **The left detour equals the replaced interval integral minus the residue correction.**  If for
`τ` in the ball `B(1+i t₀, ε)` with `Re τ < 1` the only point of the `SL(2,ℤ)`-orbit of `τ` in the
closed rectangle `[-ξ,0] × [c-A, c+A]` is the translate `τ - 1` (`hcl`), if `τ - 1` lies in the *open*
rectangle (`hpole`) and `j'(τ - 1) ≠ 0` (`hdeg`), then the boundary integral picks up exactly the
simple pole of `z ↦ K(τ,z)e^{iπr²z}/i` at `z = τ-1`, whose residue is `e^{iπr²(τ-1)}/(2πi)`, and

  `detourLeftC ℓ d r c A ξ τ = ∫_{c-A}^{c+A} edgeV(0,·) - e^{iπr²(τ-1)}`.

The residue is computed from `Work.Residues.hasResidue_of_cleared` with
`Work.Asymptotics.Kfun_mul_slope_eq_AfunFun`, `Work.Residues.tendsto_slope_jprime` and the values
`AfunPlus_vadd_one_eq`, `AfunMinus_vadd_one_eq` at `τ = z+1` (this uses only the pointwise
non-vanishing `hdeg`), and the boundary integral is evaluated with
`Work.Asymptotics.rectInt_eq_residue`; the four boundary pieces are matched with the three terms of
`detourLeftC` and the axis integral using `ofReImT`/`ofComplex` and
`exp (πIr²(u+iv)) = phaseWeight r u * gaussWeight r v`. -/
theorem detourLeftC_eq_interval_sub_residue (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r c A ξ ε t₀ : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (hA : 0 < A)
    (hξ : 0 < ξ) (hcA : 0 < c - A)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect c A ξ z → (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ))
    (hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      -ξ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        c - A < (Work.Asymptotics.tauSubOne τ).im ∧ (Work.Asymptotics.tauSubOne τ).im < c + A)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0) :
    ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε → τ.re < 1 →
      Work.Asymptotics.detourLeftC ℓ d r c A ξ τ
        = (∫ v in Set.Ioo (c - A) (c + A), Work.Asymptotics.edgeV ℓ d r τ 0 v)
          - Work.Asymptotics.resCorr r τ := by
  intro τ hτ hτre
  · have hp := hpole τ hτ hτre
    have hclean : ∀ z : ℂ, z ∈ Work.Asymptotics.leftRectℂ c A ξ → z ≠ Work.Asymptotics.poleℂ τ →
        Work.Kernels.jInvariantFun τ
          ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z) :=
      Work.Asymptotics.dlc_clean τ c A ξ hcA (hcl τ hτ hτre)
    -- the pole lies in the open rectangle
    have hx₁ : (-ξ : ℝ) < (Work.Asymptotics.poleℂ τ).re := by
      rw [Work.Asymptotics.poleℂ, UpperHalfPlane.coe_re]
      exact hp.1
    have hx₂ : (Work.Asymptotics.poleℂ τ).re < (0 : ℝ) := by
      rw [Work.Asymptotics.poleℂ, UpperHalfPlane.coe_re]
      exact hp.2.1
    have hy₁ : c - A < (Work.Asymptotics.poleℂ τ).im := by
      rw [Work.Asymptotics.poleℂ, UpperHalfPlane.coe_im]
      exact hp.2.2.1
    have hy₂ : (Work.Asymptotics.poleℂ τ).im < c + A := by
      rw [Work.Asymptotics.poleℂ, UpperHalfPlane.coe_im]
      exact hp.2.2.2
    -- Cauchy's theorem for the rectangle
    have hrect := Work.Asymptotics.rectInt_eq_residue
      (Work.Asymptotics.kerForm ℓ d r τ) (Work.Asymptotics.poleℂ τ)
      (Work.Asymptotics.kerExp r (Work.Asymptotics.poleℂ τ)
        / (2 * (Real.pi : ℂ) * Complex.I)) (-ξ) 0 (c - A) (c + A)
      hx₁ hx₂ hy₁ hy₂
      (Work.Asymptotics.dlc_continuousOn ℓ d hd r τ c A ξ hcA hclean)
      (fun z h1 h2 h3 h4 hne =>
        Work.Asymptotics.dlc_differentiableAt ℓ d hd r τ c A ξ hcA hclean z ⟨h1, h2, h3, h4⟩ hne)
      (Work.Asymptotics.dlc_tendsto_residue ℓ d hd r τ (hdeg τ hτ hτre))
    have hRHS : 2 * (Real.pi : ℂ) * Complex.I
        * (Work.Asymptotics.kerExp r (Work.Asymptotics.poleℂ τ)
            / (2 * (Real.pi : ℂ) * Complex.I)) = Work.Asymptotics.resCorr r τ := by
      rw [Work.Asymptotics.resCorr, Work.Asymptotics.poleℂ_eq, Work.Asymptotics.kerExp]
      field_simp
    rw [hRHS] at hrect
    -- the four edges of the residue theorem versus the three sides of the detour
    simp only [Work.Asymptotics.detourLeftC]
    rw [Work.Asymptotics.dlc_integral_edgeH_neg ℓ d r τ ξ (c - A) hξ hcA,
      Work.Asymptotics.dlc_integral_edgeH_neg ℓ d r τ ξ (c + A) hξ (by linarith),
      Work.Asymptotics.dlc_integral_edgeV ℓ d r τ (-ξ) (c - A) (c + A) hcA (by linarith),
      Work.Asymptotics.dlc_integral_edgeV ℓ d r τ (0 : ℝ) (c - A) (c + A) hcA (by linarith)]
    rw [← hrect]
    ring

end Work.Asymptotics
