import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.R1G.Defs
import Submission.Work.Stability.DynGEquation

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

open Work.Construction Work.Coercivity Work.Spaces

/-- **The profile residual at the effective rate is the `g`-equation residual.**

Both sides compute the *same* algebraic combination of the delivered data: expand the profile
residual `2κ(F + D_zF) + UVR p F Φ` at `F = F_* + g` by
* the static identity `Work.Stability.MainLHSSubN` (with `μ = 2κ-1`, `λ = 0`), giving
  `2κF + 2κD_zF + UVR p F Φ = MainLHS p (2κ-1) 0 F - N p F Φ`;
* the explicit expansion `Work.Construction.MainLHS_explicit` of `MainLHS` at `F = F_* + g`
  (using `L₁₂(F_*) = 2p/(1+z)` and the stationarity identity for `F_*`), whose single
  non-`g`-linear term `-(3/(2p))sin(2θ)L₁₂(F_*)∂_θg` is `-Transport g`
  (`Work.Construction.Transport_eq`);
* the definition `Work.Construction.LGammaT_eq` of the projected operator;
* the definition of `gEqResidual`/`gDynRHS` in which the `s = 0` slice of the stationary data is
  `(P.g, Φ)` and the rates are `(κ, b) = (2κ, 1)`, so that the `N₀, N, N_*` terms cancel. -/
theorem profileResid_eq_gEqResidual {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (κ : ℝ) (Φ : ℝ → ℝ → ℝ)
    (hD : Work.Stability.GDerivData (Work.ConstructionInstance.profExp α)
      (Work.R1G.gOf3 P) (Work.R1G.phiOf3 Φ))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    Work.R1G.profileResid P κ Φ z θ = Work.R1G.gEqResidual P κ Φ z θ := by
  have hz0 : 0 < z := hzθ.1
  have hznn : 0 ≤ z := le_of_lt hz0
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < Real.pi / 2 := hzθ.2.2
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθ1⟩)
  have hz : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := profExp_le_one P
  have hLstar : L12 (Fstar (Work.ConstructionInstance.profExp α)) z
      = 2 * Work.ConstructionInstance.profExp α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hp hp1 hznn
  have hstat : Fstar (Work.ConstructionInstance.profExp α) z θ
      + Dz (Fstar (Work.ConstructionInstance.profExp α)) z θ
      - (1 / Work.ConstructionInstance.profExp α)
        * L12 (Fstar (Work.ConstructionInstance.profExp α)) z
        * Fstar (Work.ConstructionInstance.profExp α) z θ = 0 :=
    Work.Construction.Fstar_stationary_identity hp hp1 hznn
  -- the `Φ = Φ̃ + Θ` decomposition is definitional
  have h1 : Φ z θ
      = PhiTil (Work.ConstructionInstance.profExp α) (profOf P) Φ z θ
        + Theta (Work.ConstructionInstance.profExp α) (profOf P) z θ := by
    simp only [PhiTil]; ring
  -- the static identity at `μ = 2κ-1`, `λ = 0`
  have hsub := Work.Stability.MainLHSSubN (α := Work.ConstructionInstance.profExp α)
    (μ := 2 * κ - 1) (lam := 0) hp (F := profOf P) (Φ := Φ) z θ hcos h1
    (hD.h2 z θ 0 hzθ) (hD.h3 z θ 0 hzθ) (hD.h5 z θ 0 hzθ) (hD.h6 z θ 0 hzθ)
  -- the explicit expansion of `MainLHS`
  have hex := Work.Construction.MainLHS_explicit (α := Work.ConstructionInstance.profExp α)
    (μ := 2 * κ - 1) (lam := 0) hp (F := profOf P) (g := P.g) z θ hz
    rfl (hD.hDz z θ 0 hzθ) (hD.hpth z θ 0 hzθ) (hD.hL z 0) hLstar hstat
  -- the transport term
  have hT : (3 / (2 * Work.ConstructionInstance.profExp α)) * s2 θ
      * L12 (Fstar (Work.ConstructionInstance.profExp α)) z * pth (P.g) z θ
      = Transport (P.g) z θ := by
    rw [Work.Construction.Transport_eq, hLstar]
    field_simp
  have hLT := Work.Construction.LGammaT_eq (Work.ConstructionInstance.profExp α) (P.g) z θ
  -- the profile residual as `MainLHS - N`
  have hres : profileResid P κ Φ z θ
      = MainLHS (Work.ConstructionInstance.profExp α) (2 * κ - 1) 0 (profOf P) z θ
        - N (Work.ConstructionInstance.profExp α) (profOf P) Φ z θ := by
    rw [profileResid_apply]
    linarith [hsub]
  have hkey : MainLHS (Work.ConstructionInstance.profExp α) (2 * κ - 1) 0 (profOf P) z θ
        - N (Work.ConstructionInstance.profExp α) (profOf P) Φ z θ
      = Work.Coercivity.LGammaT (Work.ConstructionInstance.profExp α) (P.g) z θ
        - Work.Stability.gDynRHS (Work.ConstructionInstance.profExp α)
            (modStateOf κ) (Work.R1G.gOf3 P) (Work.R1G.phiOf3 Φ) z θ 0 := by
    simp only [Work.Stability.gDynRHS, modStateOf_kappa,
      modStateOf_b, Ftot_gOf3, slice_gOf3, slice_phiOf3,
      Work.Construction.Nstar, hLT]
    rw [hex]
    linarith [hT]
  rw [hres]
  unfold Work.R1G.gEqResidual
  exact hkey

end Work.R1G
