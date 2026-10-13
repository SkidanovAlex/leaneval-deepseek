import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.EllipticEst.Core.thetaAgmonCompact
import Submission.Work.FTS.EllipticEst.TT.slice_ibp_light_closed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- **The compactly supported slice integration by parts for the light weight `σ_a`.**

For `f` of class `C²` on `[0,π/2]` supported in `[a,b] ⊂ (0,π/2)`, the weighted Dirichlet
energy of `f` in the light weight `σ_a(θ) = sin(2θ)^{2-γ(α)}` is dominated by the negative
of the corresponding "second-derivative" functional: the integration by parts

  `∫ (f')²σ = -∫ f f'' σ - 2p ∫ f² σ - 2p(1-p) ∫ f² cos²(2θ) sin(2θ)^{p-2}`   (`p = 2-γ`)

has two extra terms which are `≤ 0` because `p = 1 - α/10 ∈ (0,1)`, `σ ≥ 0` and
`cos²(2θ) sin(2θ)^{p-2} ≥ 0` on `Iθ`.  (The compact support makes every boundary term of the
two integrations by parts vanish, since `f` vanishes at `0` and `π/2`.) -/
theorem slice_ibp_sigA_compact (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hsupp : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
      ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
            * Work.FTS.EllipticEst.TT.sigA α θ) := by
  -- the exponent `p = 2 - γ(α) = 1 - α/10` lies in `(0,1)`
  have hp0 : 0 < 2 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hp1 : 2 - Work.Spaces.gam α < 1 := by
    rw [Work.Spaces.gam]; linarith
  -- `f` vanishes at both endpoints (they are outside the compact support)
  have hf0 : f 0 = 0 := hsupp 0 (by rintro ⟨h1, _⟩; linarith)
  have hf1 : f (Real.pi / 2) = 0 := hsupp (Real.pi / 2) (by rintro ⟨_, h2⟩; linarith)
  -- the closed form of the double integration by parts for the light weight
  have hkey := slice_ibp_light_closed (2 - Work.Spaces.gam α) hp0 hp1 hf hf0 hf1
  have hkey' :
      (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        = - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          - 2 * (2 - Work.Spaces.gam α)
              * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          - 2 * (2 - Work.Spaces.gam α) * (1 - (2 - Work.Spaces.gam α))
              * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2)) := by
    simpa only [sigR_apply] using hkey
  -- the two correction terms are `≤ 0`
  have h4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)
  have h5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2) := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)
  have hA : 0 ≤ 2 * (2 - Work.Spaces.gam α)
      * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
    mul_nonneg (by linarith) h4
  have hB : 0 ≤ 2 * (2 - Work.Spaces.gam α) * (1 - (2 - Work.Spaces.gam α))
      * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Real.cos (2 * θ) ^ 2
          * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) h5
  have hmain :
      (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
    rw [hkey']
    linarith
  simpa only [sigA] using hmain

end Work.FTS.EllipticEst.TT
