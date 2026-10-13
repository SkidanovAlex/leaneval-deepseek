import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets.Pieces

open MeasureTheory Set Filter
open scoped Real Topology

/-
**The uniform-in-`z` sup bound on `L₁₂` at order `6`.**

`L₁₂(f)(z) = ∫_{s>z} ∫_θ K(θ) f(s,θ)/s dθ ds` is the tail integral of the density
`L₁₂dens f`.  For `z ≥ 0` the absolute value of the tail is dominated by the integral of the
absolute density over the *fixed* half-line `(0,∞)`:

  `|L₁₂ f z| ≤ ∫_{s>z} |L₁₂dens f s| ds ≤ ∫_{s>0} |L₁₂dens f s| ds`,

and the last quantity is estimated by Cauchy–Schwarz (in the angular variable against the
profile `K·sin(2θ)^{η/2}`, and radially against the weight `Wlam s = s/(1+s)²`) by
`BK·√W2·√(HkSq α 6 f)`.  This is the general-order (`k = 6`) form, uniform in `z ≥ 0`, of the
`z = 0` bound of `Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`; the constants `BK`, `W2` are `α`-
and `k`-independent.

The decomposition is
* `abs_integral_K_S_Gaz_le_gen` — the angular Cauchy–Schwarz step at order `6`;
* `integral_abs_L12dens_le_Ioi` — the radial Cauchy–Schwarz step on the tail `(z,∞)`;
* `norm_integral_le_integral_norm` — the (hypothesis-free) domination of the integral by the
  integral of the absolute value.
-/
theorem L12_sup_six : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
    Work.Spaces.HkMem α 6 f → ∀ z : ℝ, 0 ≤ z →
      |Work.Construction.L12 f z| ≤ C * Work.Spaces.HkNorm α 6 f := by
  refine ⟨Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 :=
      mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg _)
    linarith
  · intro α f hmem z hz
    -- the pointwise (in `s > z`) bound on the density
    have hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens f s|
        ≤ Work.FTS.GalBasis.cc.Wlam s
          * (Work.FTS.GalBasis.cc.BK * Real.sqrt
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f s θ)) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt hz hs
      rw [Work.FTS.GalBasis.cc.L12dens_eq_weighted f hs0, abs_mul,
        abs_of_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg hs0.le)]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le_gen α 6 f
          (hmem.1 s (Set.mem_Ici.mpr hs0.le)))
        (Work.FTS.GalBasis.cc.Wlam_nonneg hs0.le)
    have hL12 : Work.Construction.L12 f z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens f s := rfl
    calc |Work.Construction.L12 f z|
        = |∫ s in Set.Ioi z, Work.Construction.L12dens f s| := by rw [hL12]
      _ ≤ ∫ s in Set.Ioi z, |Work.Construction.L12dens f s| := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm
              (μ := volume.restrict (Set.Ioi z))
              (f := fun s => Work.Construction.L12dens f s))
      _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
            * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
          Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi α 6 f hmem hz hbd
      _ = (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2)
            * Work.Spaces.HkNorm α 6 f := by rw [Work.Spaces.HkNorm]
      _ ≤ (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1)
            * Work.Spaces.HkNorm α 6 f := by
          have hx := Work.Spaces.HkNorm_nonneg α 6 f
          have hnn : 0 ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 :=
            mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg (Real.sqrt_nonneg _)
          nlinarith [hx]

end Work.FTS_EllLimOK.PkgJets.Pieces
