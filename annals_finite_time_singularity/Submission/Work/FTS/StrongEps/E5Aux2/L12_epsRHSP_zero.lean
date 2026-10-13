import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-!
# `L₁₂` of the projected right-hand side `epsRHSP` vanishes at `z = 0`

The scheme's right-hand side is, by definition,
`epsRHSP α ρ ε Φs E g τ = P₀ (J_ε (epsWP α ρ ε Φs E g τ))` (`epsRHSP_eq_Pz_Jeps_epsWP`), and the
projection is `P₀ f = f − (L₁₂ f 0 / pzNorm) • b` with `b = bump` and `pzNorm = L₁₂ b 0`
(`pzNorm_pos`).  The `l12` clause of the source class is therefore automatic:

  the projection identity `X = P₀ X + (L₁₂ X 0 / pzNorm) • b`

is pure algebra, and it lets us run the standard computation `L₁₂(P₀ X)(0) = 0` in the direction
that the present hypotheses support.  Indeed `PZeroAux.L12_add_mul_ae` (linearity of `L₁₂(·)(0)`
in the a.e. slice-integrability setting) applied to `f = P₀ X` and `h = b` gives

  `L₁₂ X 0 = L₁₂ (P₀ X) 0 + (L₁₂ X 0 / pzNorm) · L₁₂ b 0`,

and `L₁₂ b 0 = pzNorm`, so the second summand is `L₁₂ X 0` and `L₁₂ (P₀ X) 0 = 0`.

The two hypotheses of the statement are exactly the two integrability certificates that
`L12_add_mul_ae` needs for `f = P₀ X`: the density of `P₀ X` on `(0,∞)` (`hdens`) and the
θ-slices of `P₀ X` a.e. (`hslice`).  The corresponding certificates for the correction profile
`b` are unconditional (`PZeroAux.integrableOn_L12dens_bump`,
`PZeroAux.integrableOn_slice_bump`). -/

theorem L12_epsRHSP_zero {α ε τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hdens : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)) (Set.Ioi 0))
    (hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ r θ / r) Work.Spaces.Iθ) :
    Work.Construction.L12 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) 0 = 0 := by
  -- the unprojected, mollified pre-mollified right-hand side
  set X : ℝ → ℝ → ℝ :=
    Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) with hX
  have hpz : Work.FTS.StrongEps.pzNorm ≠ 0 :=
    ne_of_gt Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- the θ-slices of the correction profile are integrable at every `s > 0`
  have hbs : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s hs =>
        Work.FTS.StrongEps.PZeroAux.integrableOn_slice_bump hs)
  have hB : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) (Set.Ioi 0) :=
    Work.FTS.StrongEps.PZeroAux.integrableOn_L12dens_bump
  -- the projected right-hand side is `P₀` of `X`, definitionally
  have hPzX : Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ = Work.FTS.StrongEps.Pz X := by
    rw [hX]
    exact Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP α ρ ε Φs E g τ
  -- `P₀ X` plus the correction profile reassembles `X`
  have hfun : (fun z θ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ z θ
        + (Work.Construction.L12 X 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ) = X := by
    funext z θ
    rw [hPzX, Work.FTS.StrongEps.Pz_apply]
    ring
  -- linearity of `L₁₂(·)(0)` at the two admissible pieces
  have hlin := Work.FTS.StrongEps.PZeroAux.L12_add_mul_ae
    (f := Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ)
    (h := Work.FTS.StrongEps.bump)
    (c := Work.Construction.L12 X 0 / Work.FTS.StrongEps.pzNorm) hslice hbs hdens hB
  rw [hfun] at hlin
  -- `(L₁₂ X 0 / pzNorm) · pzNorm = L₁₂ X 0`
  have hc : (Work.Construction.L12 X 0 / Work.FTS.StrongEps.pzNorm)
        * Work.Construction.L12 Work.FTS.StrongEps.bump 0 = Work.Construction.L12 X 0 := by
    rw [show Work.Construction.L12 Work.FTS.StrongEps.bump 0 = Work.FTS.StrongEps.pzNorm from rfl]
    exact div_mul_cancel₀ _ hpz
  linarith

end Work.FTS.StrongEps.E5Aux2
