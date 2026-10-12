import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseFixR.LatGreen.ConvScaleInvCutoffSmooth
import Submission.Work.BoseFixR.LatGreen.G0WeightedMoment
import Submission.Work.BoseFixR.LatGreen.RadialSmoothCosDecaySchwartz
import Submission.Work.BoseFixR.Rb5Lin.W1Facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open MeasureTheory Metric
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The unit vector along the `0`-th coordinate axis; the axis of the radial profiles. -/
def axis0 : ℝ³ := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

lemma norm_axis0 : ‖(axis0 : ℝ³)‖ = 1 := by
  simp [axis0]

lemma norm_smul_axis0 (r : ℝ) : ‖r • (axis0 : ℝ³)‖ = |r| := by
  rw [norm_smul, norm_axis0, mul_one, Real.norm_eq_abs]

/-- The radial profile of `g₀`, read off on the axis: `g₀ x = ψ ‖x‖`. -/
lemma g0_eq_axisProfile {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hvrad : BoseGases.IsRadial v) (x : ℝ³) :
    Submission.BoseGases.g0 v h x = Submission.BoseGases.g0 v h (‖x‖ • axis0) :=
  isRadial_g0 hvrad h x (‖x‖ • axis0)
    (by rw [norm_smul_axis0, abs_of_nonneg (norm_nonneg x)])

/-- **The decay of `Ŵ₁` (step 3's summability input).**

`|chat (W1fun v h ℓ) q| ≤ C/(1 + ‖q‖)` for an explicit `C ≥ 0`, under the standing bundle.

The proof goes through the corpus's a.e. facts about the renormalised kernel
`W₁ = wScaled ℓ (g₀ v h) = g₀/(χ⋆χ)(·/ℓ)`:

* `W₁` is integrable (`Submission.BoseGases.wScaled_g0_integrable`), hence
  `Ŵ₁(q) = ∫ x, W₁(x)·cos⟪q,x⟫ dx` (`Work.BoseFixR.Rb5Lin.chat_eq_cos`);
* `g₀ = v(1−ω)` is radial (`Work.BoseFixR.LatGreen.isRadial_g0`), integrable and supported in `ball 0 R`
  (`Submission.BoseGases.g0_zero_of_norm_ge`), so writing `ψ r := g₀(r•e₀)` the
  integral becomes `∫ x, ψ ‖x‖·F x·cos⟪q,x⟫` where `F` is the globally `C¹`
  cut-off of `1/(χ⋆χ)(·/ℓ)` (`Work.BoseFixR.LatGreen.ConvScaleInvCutoffSmooth`), which
  agrees with `W₁/g₀` on the support of `g₀`;
* the angular estimate on the radial weight `ψ` against the smooth factor `F`
  (`Work.BoseFixR.LatGreen.RadialSmoothCosDecay`) gives the bound, with the
  weighted moment `∫₀^R r·|ψ r| dr < ∞` supplied by the Newton representation of
  the scattering solution (`Work.BoseFixR.LatGreen.G0WeightedMoment`).

Consequence for the caller: with `q_k = 2π k/ℓ` this yields
`|Ŵ₁(q_k)|²/‖q_k‖² ≤ C'‖k‖^{-4}`, i.e. `Summable` of the weighted full-lattice
row — the summability hypothesis of step 3's full-lattice Parseval identity. -/
theorem W1funDecay {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q| ≤ C / (1 + ‖q‖) := by
  -- ═══ pieces (delegated; siblings under `Submission/Work/BoseFixR/LatGreen/`) ═══
  obtain ⟨F, hFsm, hFcs, hFval, _hFbd⟩ := ConvScaleInvCutoffSmooth hℓ hR hRℓ
  obtain ⟨hmomint, _hmomle⟩ := G0WeightedMoment h hv hvrad hR hv_supp
  -- the axis profile of `g₀`
  set ψ : ℝ → ℝ := fun r => Submission.BoseGases.g0 v h (r • axis0) with hψdef
  have hψsupp : ∀ r : ℝ, R ≤ r → ψ r = 0 := by
    intro r hr
    rw [hψdef]
    refine Submission.BoseGases.g0_zero_of_norm_ge hv_supp ?_ h
    rw [norm_smul_axis0, abs_of_nonneg (le_trans hR.le hr)]
    exact hr
  have hψint : MeasureTheory.IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ)) := by
    simpa only [hψdef, axis0] using hmomint
  obtain ⟨C, hC0, hCbd⟩ := RadialSmoothCosDecaySchwartz hR hψsupp hψint hFsm hFcs
  refine ⟨C, hC0, fun q => ?_⟩
  -- ═══ `Ŵ₁(q) = ∫ x, W₁ x · cos⟪q,x⟫` ═══
  have hW1int : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  rw [Work.BoseFixR.Rb5Lin.chat_eq_cos hW1int q]
  -- ═══ replace `W₁` by `ψ ‖x‖ · F x` pointwise ═══
  have hpt : ∀ x : ℝ³, Work.BoseFixR.W1fun v h ℓ x * Real.cos (inner ℝ q x)
      = ψ ‖x‖ * F x * Real.cos (inner ℝ q x) := by
    intro x
    have hg : Submission.BoseGases.g0 v h x = ψ ‖x‖ := by
      rw [hψdef]
      exact g0_eq_axisProfile h hvrad x
    by_cases hx : ‖x‖ ≤ R
    · have hF : F x = (Submission.BoseGases.convScale ℓ x)⁻¹ := hFval x hx
      simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hg, hF, div_eq_mul_inv]
    · have hxR : R ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
      have h0 : Submission.BoseGases.g0 v h x = 0 :=
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp hxR h
      have hψ0 : ψ ‖x‖ = 0 := by
        rw [hψdef]
        refine Submission.BoseGases.g0_zero_of_norm_ge hv_supp ?_ h
        rw [norm_smul_axis0, abs_of_nonneg (norm_nonneg x)]
        exact hxR
      simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, h0, hψ0, zero_div,
        zero_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact hCbd q

end

end Work.BoseFixR.LatGreen
