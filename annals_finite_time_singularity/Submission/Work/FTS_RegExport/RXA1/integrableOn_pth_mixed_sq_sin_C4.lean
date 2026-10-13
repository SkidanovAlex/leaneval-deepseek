/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the angular Hardy integrand of a mixed slot, at the finite order `C⁴`

This is the `C⁴`-version (no analyticity, no smoothness on the boundary of the quadrant) of the
integrability step "**Get it directly**" of the road map for `RX-A1`
(`Submission/Work/FTS_RegExport/NOTES_A1_A1w_roadmap.md`, step 2):

for `f` of class `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴`
(`Work.Spaces.HkMem α 4 f`), for `a + b ≤ 2` and `z > 0`, the angular function

  `σ ↦ (∂_θ (D_z^b D_θ^a f) (z, σ))² · sin(2σ)^{2-γ}`     (`γ = gam α = 1 + α/10`)

is integrable on `Iθ = [0,π/2]`.  This is exactly the `hint` slot of the angular Hardy
inequality `Work.FTS_RegExport.C4.hardyTheta_slice_C1` for the slice `D_z^bD_θ^af z ·`.

**Proof.**  On `Iθ` the weight algebra `pth_sq_mul_sin_eq_C4` rewrites the integrand as
`(D_θ (D_z^bD_θ^af)(z,σ))² · sin(2σ)^{-γ}`, and on the open interval `D_θ` commutes with the
radial iterates (`Work.FTS_RegExport.C4.Dth_mixed_eq_C4`), so the integrand equals
`(D_z^bD_θ^{a+1}f (z,σ))² · sin(2σ)^{-γ}` — the very slot `(i,j) = (a+1,b)` of `HkIntegrand`.
Since `(w z)² ≥ 1` and `(Wt α z σ)² = (w z)²·sin(2σ)^{-γ}`, that slot is dominated pointwise by
`(D_z^bD_θ^{a+1}f (z,σ)·Wt α z σ)² ≤ HkIntegrand α 4 f z σ`
(`Work.Spaces.sq_le_HkIntegrand_mixed`), which is integrable in `σ` at the *fixed* `z` by
`hmem.1` — no Tonelli is needed, the integration is at fixed `z`.  Measurability comes from the
continuity of the slot on the open quadrant
(`Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn`) through
`Work.Spaces.aesm_slice_of_continuousOn_Qd`.  The endpoint cases `σ = 0, π/2` are harmless
because `sin(2σ)^{-γ} = 0` there.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary facts about the exponent, the weights and the `θ`-slices -/

/-- The exponent `γ = gam α = 1 + α/10` is positive for `α > 0`. -/
private lemma gam_pos_C4 {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-- For `α ≤ 1` one has `γ = gam α ≤ 11/10`, in particular `γ ≠ 2`. -/
private lemma gam_le_eleven_tenths {α : ℝ} (hα1 : α ≤ 1) :
    Work.Spaces.gam α ≤ 11 / 10 := by
  rw [Work.Spaces.gam]; linarith

/-- `sin(2θ) ≥ 0` on the angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The radial weight satisfies `1 ≤ (w z)²` for `z > 0`. -/
private lemma one_le_w_sq_C4 {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have h1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  nlinarith [h1]

/-- The weight algebra `(Wt α z θ)² = (w z)² · sin(2θ)^{-γ}` on the closed angular interval. -/
private lemma Wt_sq_Iθ {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    ring_nf
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1]

/-- The weight algebra underlying the angular Hardy inequality:
`(∂_θ u)² sin(2θ)^{2-γ} = (D_θ u)² sin(2θ)^{-γ}` on `Iθ`. -/
private lemma pth_sq_mul_sin_eq_C4 {α : ℝ} (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.Dth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hne : 2 + (-(Work.Spaces.gam α)) ≠ 0 := by
    have hg1 := gam_le_eleven_tenths hα1
    intro h
    linarith
  have hD : Work.Spaces.Dth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u z θ := rfl
  rw [hD, mul_pow, show 2 - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
    Real.rpow_add' hs hne]
  simp only [mul_assoc, mul_left_comm, mul_comm, Real.rpow_two]

/-! ## The target -/

theorem integrableOn_pth_mixed_sq_sin_C4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hγne : Work.Spaces.gam α ≠ 0 := ne_of_gt (gam_pos_C4 hα)
  have hab4 : a + 1 + b ≤ 4 := by omega
  -- The angular slice of `HkIntegrand` at the fixed radial variable `z` is integrable: this is
  -- the second component of `HkMem α 4 f`.
  have hHk : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
      Work.Spaces.Iθ := hmem.1 z (show z ∈ Work.Spaces.Iz from hz.le)
  -- Continuity of the slot `(D_z^bD_θ^{a+1}f)² sin(2θ)^{-γ}` on the open quadrant.
  have hsinposQ : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hpθ⟩ := hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hpθ.1])
      (by linarith [hpθ.2, Real.pi_pos])
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hF hab4).pow 2).mul
      (ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
        (fun p hp => Or.inl (ne_of_gt (hsinposQ p hp))))
  -- The slot `(D_z^bD_θ^{a+1}f)² sin(2θ)^{-γ}` is integrable on `Iθ`.
  have hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hHk
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => ?_
    have hs : 0 ≤ Real.sin (2 * σ) := sin_two_nonneg_Iθ hσ
    have hnn : 0 ≤ (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
    rw [Real.norm_of_nonneg hnn]
    -- the slot is dominated by the corresponding summand of `HkIntegrand α 4 f`
    have hslot := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ (a + 1) b (by omega) (by omega)
    rw [mul_pow, Wt_sq_Iθ hσ] at hslot
    have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq_C4 hz
    calc (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        ≤ (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (Real.rpow_nonneg hs _) hw) (sq_nonneg _)
      _ ≤ Work.Spaces.HkIntegrand α 4 f z σ := hslot
  -- Transfer to the `pth`-form of the integrand, pointwise on `Iθ`.
  refine hint.congr_fun (fun σ hσ => ?_) measurableSet_Icc
  show (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
  rw [pth_sq_mul_sin_eq_C4 hα1 (Work.Spaces.mixed b a f) z σ hσ]
  -- `D_θ (D_z^bD_θ^af) = D_z^bD_θ^{a+1}f` on the open interval; at the two endpoints both
  -- sides vanish because `sin(2σ)^{-γ} = 0` there.
  rcases eq_or_lt_of_le hσ.1 with h0 | h0
  · have hs0 : Real.sin (2 * σ) = 0 := by rw [← h0]; simp
    have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
      rw [hs0]
      exact Real.zero_rpow (neg_ne_zero.mpr hγne)
    rw [hz0, mul_zero, mul_zero]
  · rcases eq_or_lt_of_le hσ.2 with hπ | hπ
    · have hs0 : Real.sin (2 * σ) = 0 := by
        rw [hπ, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hs0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      rw [hz0, mul_zero, mul_zero]
    · rw [Work.FTS_RegExport.C4.Dth_mixed_eq_C4 hF b a (by omega) hz ⟨h0, hπ⟩]

end Work.FTS_RegExport.RXA1
