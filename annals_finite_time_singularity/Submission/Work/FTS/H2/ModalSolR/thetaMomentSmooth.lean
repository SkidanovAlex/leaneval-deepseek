/-
Copyright: work module for the Elgindi finite-time singularity project.

# Smoothness and radial derivatives of the angular moments `∫_θ φ(z,θ)·e_m(θ)·cos θ`

`Work.FTS.H2.ModalSolR.thetaMomentSmooth`: for a jointly `C^∞` function `φ`, the mode-`m`
angular moment

  `M_m φ z = ∫_θ φ (z,θ) · e_m(θ) · cos θ dθ`

is `C²` in the radial variable `z`, with `M_m φ' = M_m (∂_z φ)` and
`M_m φ'' = M_m (∂_z² φ)`.

The proof differentiates under the integral sign.  The integrand
`(z,θ) ↦ ∂_z^k φ (z,θ) · e_m(θ) cos θ` is jointly continuous on `ℝ × Iθ` because `∂_z^k φ`
is jointly smooth on `ℝ²` for every `k`
(`Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le`) and `e_m cos` is continuous, so
`Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt` applies with `V = univ`; the
`C²`-conclusion is then the two-step `contDiff_succ_iff_deriv` /
`contDiff_one_iff_deriv` argument exhibiting `M_m φ'` and `M_m φ''` as the continuous
level-`1` and level-`2` moments.

Note that none of the hypotheses `hφc` (compact support) or `hφs` (support in the closed
quadrant) is needed: joint smoothness of `φ` on all of `ℝ²` is enough.  (They are part of
the statement because the consumer `Work.FTS.H2.ModalSolR.thetaMomentCompactSupport`
needs them.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta
import Submission.Work.FTS.GalBasis.exists_mixed_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

theorem thetaMomentSmooth {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (m : ℕ) :
    ContDiff ℝ 2 (fun z => ∫ θ in Work.Spaces.Iθ,
        φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ∧
      (∀ z, 0 < z → HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ,
          φ z' θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z) ∧
      (∀ z, 0 < z → HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz φ z' θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z) := by
  have hEc : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) :=
    Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)
  -- Joint continuity on `ℝ × Iθ` of the integrands, for every order `k`.
  have hcont : ∀ k : ℕ, ContinuousOn
      (Function.uncurry (fun z θ => Work.Spaces.pzIter k φ z θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ))
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    intro k
    have h1 : Continuous (Function.uncurry (Work.Spaces.pzIter k φ)) := by
      have hc : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pzIter k φ)) Set.univ :=
        Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le (V := Set.univ) isOpen_univ
          ((hφ k).contDiffOn) k 0 (by omega)
      exact continuousOn_univ.mp hc.continuousOn
    have h2 : Continuous (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) :=
      hEc.comp continuous_snd
    have h3 : Continuous (fun p : ℝ × ℝ => Real.cos p.2) :=
      Real.continuous_cos.comp continuous_snd
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.pzIter k φ) p
        * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) :=
      (h1.continuousOn.mul h2.continuousOn).mul h3.continuousOn
    exact h4.congr (fun p _ => rfl)
  -- Differentiation under the integral sign, at every `z ∈ ℝ`.
  have hderiv : ∀ k : ℕ, ∀ z : ℝ,
      HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k φ z' θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) φ z θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z := by
    intro k z
    refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt (V := Set.univ)
      isOpen_univ (Set.mem_univ z) (hcont k) (hcont (k + 1)) ?_
    intro θ hθ s hs
    have hsl : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k φ z' θ) s :=
      Work.FTS.GalBasis.differentiableAt_slice_pzIter (V := Set.univ) isOpen_univ
        ((hφ (k + 1)).contDiffOn) (i := k) (by omega) (Set.mem_univ (s, θ))
    have h1 : HasDerivAt (fun z' => Work.Spaces.pzIter k φ z' θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Work.Spaces.pzIter (k + 1) φ s θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ) s := by
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
        using hsl.hasDerivAt.mul_const (Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    simpa only using h1.mul_const (Real.cos θ)
  -- Continuity of the moments, for every order.
  have hcont' : ∀ k : ℕ, Continuous (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pzIter k φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) :=
    fun k => continuousOn_univ.mp
      (Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn (V := Set.univ)
        isOpen_univ (hcont k))
  -- The two derivatives, as identities between functions.
  have hd0 : deriv (fun z => ∫ θ in Work.Spaces.Iθ, φ z θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz φ z θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
    funext z
    exact (hderiv 0 z).deriv
  have hd1 : deriv (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 1 φ z θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 φ z θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
    funext z
    exact (hderiv 1 z).deriv
  -- The level-`1` moment is `C¹`.
  have hC1 : ContDiff ℝ 1 (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 1 φ z θ
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun z => (hderiv 1 z).differentiableAt, by rw [hd1]; exact hcont' 2⟩
  have hone : (((1 : ℕ) : WithTop ℕ∞)) ≠ (⊤ : WithTop ℕ∞) :=
    ne_of_lt (WithTop.natCast_lt_top 1)
  refine ⟨?_, ?_, ?_⟩
  · -- `ContDiff ℝ 2` of the level-`0` moment, from the two derivative identities.
    change ContDiff ℝ (((1 : ℕ) : WithTop ℕ∞) + 1) (fun z => ∫ θ in Work.Spaces.Iθ,
        φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
    rw [contDiff_succ_iff_deriv]
    exact ⟨fun z => (hderiv 0 z).differentiableAt, fun h => absurd h hone,
      by rw [hd0]; exact hC1⟩
  · intro z hz
    exact hderiv 0 z
  · intro z hz
    exact hderiv 1 z

end Work.FTS.H2.ModalSolR
