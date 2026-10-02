import Mathlib
import Submission.Work.MRMT.Found.forward_limit_pd
import Submission.Work.MRMT.Found.inverse_limit
import Submission.Work.MRMT.Found.records_agree_pd
import Submission.Work.MRMT.Found.M

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open Filter Topology MeasureTheory

/-- A locally uniform limit of the `C¹`-diffeomorphic solutions `Fn` of the Beltrami equation
for a family of admissible coefficients `μn`, with uniform dilatation bound `k < 1` and uniform
support radius `M`, is the principal solution `principal μ` of the a.e. limit coefficient `μ`.

The proof builds a `PrincipalData μ` from the given data (`forward_limit_pd` supplies the limit
function, its decay and the `L²`-convergence of `∂(Fn n)`; `inverse_limit` supplies the inverse
convergence and hence that the limit is a homeomorphism), and then invokes the well-definedness
of the principal solution (`records_agree_pd`). -/
theorem tendsto_principal_of_approx {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {k M : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hM0 : 0 ≤ M)
    (hμb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    {μn : ℕ → ℂ → ℂ}
    (hμnC : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμnS : ∀ n, HasCompactSupport (μn n))
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hμnT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z)))
    {Fn : ℕ → ℂ ≃ₜ ℂ}
    (hFC : ∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ))
    (hFCS : ∀ n, ContDiff ℝ 1 ((Fn n).symm : ℂ → ℂ))
    (hFB : ∀ n z, Work.MRMT.dzbar (Fn n : ℂ → ℂ) z = μn n z * Work.MRMT.dz (Fn n : ℂ → ℂ) z)
    (hFD : ∀ n, ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖Fn n z - z‖ ≤ C / ‖z‖) :
    TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ)) (Work.MRMT.Found.principal μ : ℂ → ℂ)
      Filter.atTop := by
  classical
  -- the forward limit: local uniform convergence, uniform decay, `L²`-limit of `∂`
  obtain ⟨φ, D, Cd, Rd, hφc, hφconv, hφdec, hFdec, hDtend⟩ :=
    Work.MRMT.Found.forward_limit_pd (μ := μ) (k := k) (M := M) (μn := μn) (Fn := Fn)
      hk0 hk1 hM0 hμnC hμnS hμnB hμnSp hμnT hμb hFC hFCS hFB hFD
  -- enlarge the decay constants so that they are non-negative / at least one
  have hCd' : 0 ≤ max Cd 0 := le_max_right _ _
  have hRd' : 1 ≤ max Rd 1 := le_max_right _ _
  have hFdec' : ∀ n : ℕ, ∀ z : ℂ, max Rd 1 ≤ ‖z‖ → ‖Fn n z - z‖ ≤ max Cd 0 / ‖z‖ := by
    intro n z hz
    exact (hFdec n z (le_trans (le_max_left _ _) hz)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hφdec' : ∀ z : ℂ, max Rd 1 ≤ ‖z‖ → ‖φ z - z‖ ≤ max Cd 0 / ‖z‖ := by
    intro z hz
    exact (hφdec z (le_trans (le_max_left _ _) hz)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  -- the inverse limit
  obtain ⟨ψ, hψc, hψconv, hφψ, hψφ⟩ :=
    Work.MRMT.Found.inverse_limit (μn := μn) (k := k) (M := M)
      (Cd := max Cd 0) (Rd := max Rd 1) (Fn := Fn) (φ := φ)
      hk0 hk1 hM0 hCd' hRd' hμnB hμnSp hFC hFCS hFB hFdec' hφconv
  -- assemble the homeomorphism
  let Φ : ℂ ≃ₜ ℂ :=
    { toFun := φ
      invFun := ψ
      left_inv := hψφ
      right_inv := hφψ
      continuous_toFun := hφc
      continuous_invFun := hψc }
  -- assemble the principal data record
  let d : Work.MRMT.Found.PrincipalData μ :=
    { φ := Φ
      C := max Cd 0
      R := max Rd 1
      decay := hφdec'
      k := k
      hk := hk1
      μn := μn
      contDiff_μn := fun n => (hμnC n).of_le (by simp)
      compactSupport_μn := hμnS
      norm_μn := hμnB
      tendsto_μn := hμnT
      Fn := Fn
      contDiff_Fn := hFC
      contDiff_symm_Fn := hFCS
      beltrami_Fn := hFB
      tendsto_Fn := hφconv
      tendsto_symm_Fn := hψconv
      dz_tendsto := ⟨D, hDtend⟩ }
  -- any two records agree
  have hd : (d.φ : ℂ → ℂ) = ((Work.MRMT.Found.principalData μ hμ).φ : ℂ → ℂ) :=
    Work.MRMT.Found.records_agree_pd hμ d (Work.MRMT.Found.principalData μ hμ)
  have hdφ : (d.φ : ℂ → ℂ) = φ := rfl
  have hfun : φ = (Work.MRMT.Found.principal μ : ℂ → ℂ) := by
    calc φ = (d.φ : ℂ → ℂ) := hdφ.symm
      _ = ((Work.MRMT.Found.principalData μ hμ).φ : ℂ → ℂ) := hd
      _ = (Work.MRMT.Found.principal μ : ℂ → ℂ) := by
            rw [Work.MRMT.Found.principal_eq_principalData hμ]
  rw [hfun] at hφconv
  exact hφconv

end Work.FBif
