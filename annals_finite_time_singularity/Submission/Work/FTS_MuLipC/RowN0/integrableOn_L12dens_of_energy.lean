import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.FTS.H2.L12densSlice
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN0

/-- (namespace `Work.FTS_MuLipC.RowN0`) **The `L₁₂`-density of a datum whose Hardy-weighted
angular energy is dominated by an integrable function is integrable.**  Writing
`Ψ(r) = ∫_θ X(r,θ)²` and `W(r) = ((1+r)/r)²`, the hypothesis is `Ψ(r)·W(r) ≤ Φ(r)` for a.e.
`r > 0` with `Φ ≥ 0` integrable on `(0,∞)`.  Then `L₁₂dens X` is integrable on `(0,∞)`: the
angular Cauchy–Schwarz bound `(L₁₂dens X r)² ≤ 3 Ψ(r)/r²`
(`Work.Coercivity.L12dens_sq_slice` with `Work.Coercivity.integral_Itheta_K`) together with
`Ψ(r)·W(r) ≤ Φ(r)` gives `√Ψ(r) ≤ √(Φ(r))·r/(1+r)`, hence `|L₁₂dens X r| ≤ √(3Φ(r))/(1+r)`;
and `r ↦ √(3Φ(r))` and `r ↦ 1/(1+r)` are both `L²` on `(0,∞)` (the first because its square is
`3Φ`), so their product is `L¹` (`MeasureTheory.MemLp.integrable_mul`), and `haesm` converts the
a.e. domination into integrability (`MeasureTheory.Integrable.mono'`). -/
theorem integrableOn_L12dens_of_energy {X : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ}
    (hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ : ℝ => (X r θ) ^ 2) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens X)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦ : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hΦ0 : ∀ r : ℝ, 0 ≤ Φ r)
    (hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (X r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens X) (Set.Ioi (0 : ℝ)) := by
  -- Gather the two a.e. hypotheses over `(0,∞)` together with the positivity of the point.
  have hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      r ∈ Set.Ioi (0 : ℝ) ∧ MeasureTheory.IntegrableOn (fun θ : ℝ => (X r θ) ^ 2) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (X r θ) ^ 2) * ((1 + r) / r) ^ 2 ≤ Φ r := by
    filter_upwards [hsl, hbd, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr1 hr2 hr3
    exact ⟨hr3, hr1, hr2⟩
  -- Slicewise: `|L₁₂dens X r| ≤ √(3Φ(r)) · (1/(1+r))`, and AM–GM turns this into the
  -- integrable domination `≤ (3Φ(r) + (1/(1+r))²)/2`.
  have hbdae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Construction.L12dens X r‖ ≤ (3 * Φ r + (1 / (1 + r)) ^ 2) / 2 := by
    filter_upwards [hae] with r ⟨hr, hslr, hbdr⟩
    have hslice : |Work.Construction.L12dens X r|
        ≤ Real.sqrt (3 * Φ r) * (1 / (1 + r)) :=
      Work.FTS.StrongPersist.H6Pair6Aux.l12sup_dens_le hr hslr hbdr
    rw [Real.norm_eq_abs]
    have hAM : 2 * (Real.sqrt (3 * Φ r) * (1 / (1 + r))) ≤ 3 * Φ r + (1 / (1 + r)) ^ 2 := by
      have hsq : Real.sqrt (3 * Φ r) ^ 2 = 3 * Φ r :=
        Real.sq_sqrt (by linarith [hΦ0 r])
      nlinarith [sq_nonneg (Real.sqrt (3 * Φ r) - 1 / (1 + r)), hsq]
    linarith
  -- The dominating function is integrable on `(0,∞)`.
  have hg : MeasureTheory.Integrable (fun r : ℝ => (3 * Φ r + (1 / (1 + r)) ^ 2) / 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : MeasureTheory.Integrable (fun r : ℝ => 3 * Φ r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hΦ.const_mul 3
    have h2 : MeasureTheory.Integrable (fun r : ℝ => (1 / (1 + r)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := (Work.FTS.H2.InvOneAddSq).1
    exact (h1.add h2).div_const 2
  exact hg.mono' haesm hbdae

end Work.FTS_MuLipC.RowN0
