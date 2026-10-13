import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardy
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePt6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.slicePtBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sigmaCritWeight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- **The `a₁ = a` family of the level-six `D_z`-transport Leibniz expansion** (all angular
derivatives on the coefficient `f`, so that the second `g`-factor is the *pure* slot
`D_z^{b-b₁+1} g`): for `1 ≤ a`, `a + b ≤ 6`, `b₁ ≤ b`, `5 ≤ a + b₁` and `b - b₁ + 1 ≤ 2`,

`|∫∫ leafGam α · (D_z^{b₁}D_θ^a f) · (D_z^{b-b₁+1} g) · (D_z^bD_θ^a g)|`
  `≤ C · |f|_{𝒲^{6,∞}} · |g|²_{ℋ⁶}`,   `C` universal (no `α`-loss).

Route (all pieces are in the workspace): `L6FBound.mixed_le_WlInf6` gives
`|D_z^{b₁}D_θ^af| ≤ 1000 |f| (α+σ)σ^{α/5}` pointwise; split `(α+σ)σ^{α/5}`, whose factors
carry the weights `σ^{-(1-α/10)}` (with the `α`) and `σ^{-α/10}`, so that the target is
`1000|f| (α∫∫ w²σ^{-(1-α/10)}|G||Y| + ∫∫ w²σ^{-α/10}|G||Y|)` with `G = D_z^{b-b₁+1}g`,
`Y = D_z^bD_θ^ag`.  The second integral is pointwise-compatible
(`σ^{-α/10} ≤ min(σ^{-η},σ^{-γ})`, `G` pure of order `≤ 2` and `Y` mixed of order `≤ 6`), so it
is `≤ HkSq α 6 g`.  For the first use Cauchy–Schwarz in the two `g`-factors:
`α∫∫w²σ^{-(1-α/10)}|G||Y| ≤ α√Q·√(∫∫w²σ^{-(1-α/10)}Y²) ≤ α√Q·√(HkSq α 6 g)` with
`Q := ∫∫w²σ^{-(1-α/10)}G²` (`σ^{-(1-α/10)} ≤ σ^{-γ}` since `1-α/10 ≤ γ`), and bound `Q` by the
weighted Hardy inequality `SixRoute.thetaHardyA` applied θ-slicewise to the (smooth on the open
interval) functions `θ ↦ D_z^{b-b₁+1}g z θ`, whose error term is the γ-weighted slot
`∫∫w²σ^{-γ}(D_θ(D_z^{b-b₁+1}g))² = ∫∫w²σ^{-γ}(D_z^{b-b₁+1}D_θg)² ≤ HkSq α 6 g` (order `≤ 3 ≤ 6`),
together with the boundary term controlled by `SixRoute.tracePi4`.  Hence
`α√Q ≤ √C·√(HkSq α 6 g)` and the claim follows. -/
theorem pureGamFamSix : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f g : ℝ → ℝ → ℝ) (a b b₁ : ℕ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    1 ≤ a → a + b ≤ 6 → b₁ ≤ b → 5 ≤ a + b₁ → b - b₁ + 1 ≤ 2 →
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2)
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) ∧
        |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
              * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
              * Work.Spaces.mixed b a g p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
          ≤ C * Work.Spaces.WlInf α 6 f * Work.Spaces.HkSq α 6 g := by
  obtain ⟨Ctr, hCtr0, htr⟩ := tracePi4
  obtain ⟨_Ctp, _hCtp0, htp⟩ := tracePt6
  obtain ⟨Cd, hCd0, hsigma⟩ := sigmaCritWeight
  refine ⟨1000 * (Real.sqrt (2 * Cd * Ctr + 2 * Cd * Cd) + 1), by positivity, ?_⟩
  intro α hα f g a b b₁ hfs hfm hgs hgm ha hab hb1b _h5 hbm
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hm2 : b - b₁ + 1 ≤ 2 := hbm
  have hm6 : b - b₁ + 1 ≤ 6 := by omega
  -- the critical weight and its bound
  have hDint : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (α / 10 - 1))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h := (hsigma α hα).1
    simpa only [show -(1 - α / 10) = α / 10 - 1 from by ring] using h
  have hDbnd : critD α ≤ Cd / α := by
    have h := (hsigma α hα).2
    rw [← int_sig_beta_eq_critD α]
    simpa only [show -(1 - α / 10) = α / 10 - 1 from by ring] using h
  -- the critical slot `G = D_z^{b-b₁+1} g`
  have hcr := critSlot_prod (α := α) (Ctr := Ctr) hα hgs hgm (b - b₁ + 1) hm2 hDint
    (htp α hα g (b - b₁ + 1) hgs hgm hm2).2 (htr α hα g (b - b₁ + 1) hgs hgm hm2)
  -- the `γ`-weighted slot `Y = D_z^bD_θ^a g`
  have hIgam := mixedSlot_sq_le_HkSq (α := α) (g := g) hgs hgm ha hab
  have hIgamA := mixedSlot_weight_le_HkSq (α := α) (c := -(1 - α / 10)) hα0 hgs hgm
    (by rw [Work.Spaces.gam]; linarith) ha hab
  have hIgam_p := mixedSlot_weight_le_HkSq (α := α) (c := α / 10) hα0 hgs hgm
    (by have := Work.Spaces.gam_pos hα0; linarith) ha hab
  have hG_p := dzSlot_weight_le_HkSq (α := α) (c := α / 10) hα0 hgs hgm
    (by rw [Work.Spaces.eta]; linarith) (b - b₁ + 1) hm6
  -- basic values
  have hCd0' : (0 : ℝ) ≤ Cd := hCd0.le
  have hCtr0' : (0 : ℝ) ≤ Ctr := hCtr0.le
  have hH0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  have hW0 : (0 : ℝ) ≤ Work.Spaces.WlInf α 6 f :=
    Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hfm
  have hD0 : 0 ≤ critD α := critD_nonneg α
  set K : ℝ := 2 * Cd * Ctr + 2 * Cd * Cd with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    nlinarith [hCd0, hCtr0, sq_nonneg Cd]
  have hsqrtK0 : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  set ρ : ℝ × ℝ → ℝ := fun p => (Work.Spaces.w p.1) ^ 2
    * (Real.sin (2 * p.2)) ^ (-(1 - α / 10)) with hρdef
  set Gn : ℝ × ℝ → ℝ := fun p => Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2 with hGdef
  set Yn : ℝ × ℝ → ℝ := fun p => Work.Spaces.mixed b a g p.1 p.2 with hYdef
  -- `ρ` is nonnegative a.e. and `ρ*G²`, `ρ*Y²` are integrable
  have hρnn : ∀ᵐ p ∂pm, 0 ≤ ρ p := by
    filter_upwards [ae_pm_snd_mem_Ioo] with p hp
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hp)) _)
  have hintG0 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p * (Gn p) ^ 2) pm := hcr.1
  have hintY0 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p * (Yn p) ^ 2) pm := hIgamA.1
  have hintG1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (α / 10) * (Gn p) ^ 2) pm := hG_p.1
  have hintY1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (α / 10) * (Yn p) ^ 2) pm := hIgam_p.1
  -- the ae equality of `ρ` with its positive part
  have hρmax : ∀ᵐ p ∂pm, max 0 (ρ p) = ρ p := by
    filter_upwards [hρnn] with p hp
    exact max_eq_right hp
  -- integrability of the two cross terms
  have hintA : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p * |Gn p| * |Yn p|) pm := by
    have hmaj : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (1 / 2) * (ρ p * (Gn p) ^ 2 + ρ p * (Yn p) ^ 2)) pm :=
      (hintG0.add hintY0).const_mul (1 / 2)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
      exact ((continuousOn_w2_sig_Qd (-(1 - α / 10))).mul
        ((hgs.DzIter (b - b₁ + 1)).continuousOn.abs)).mul
          ((hgs.mixed b a).continuousOn.abs)
    · filter_upwards [hρnn] with p hp
      have h1 := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (Gn p) (Yn p)
      rw [abs_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hp
      have h3 : ρ p * |Gn p| * |Yn p| = ρ p * (|Gn p| * |Yn p|) := by ring
      have h4 : ρ p * ((Gn p ^ 2 + Yn p ^ 2) / 2)
          = (1 / 2) * (ρ p * (Gn p) ^ 2 + ρ p * (Yn p) ^ 2) := by ring
      rw [Real.norm_eq_abs, h3,
        abs_of_nonneg (mul_nonneg hp (mul_nonneg (abs_nonneg _) (abs_nonneg _))), ← h4]
      exact h2
  have hρ1nn : ∀ᵐ p ∂pm, 0 ≤ (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) := by
    filter_upwards [ae_pm_snd_mem_Ioo] with p hp
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hp)) _)
  have hintB : MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (α / 10) * |Gn p| * |Yn p|) pm := by
    have hmaj : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (1 / 2) * ((Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (α / 10) * (Gn p) ^ 2
          + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * (Yn p) ^ 2)) pm :=
      (hintG1.add hintY1).const_mul (1 / 2)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
      exact ((continuousOn_w2_sig_Qd (α / 10)).mul
        ((hgs.DzIter (b - b₁ + 1)).continuousOn.abs)).mul
          ((hgs.mixed b a).continuousOn.abs)
    · filter_upwards [hρ1nn] with p hp
      have h1 := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (Gn p) (Yn p)
      rw [abs_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hp
      have h3 : (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * |Gn p| * |Yn p|
          = ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10)) * (|Gn p| * |Yn p|) := by
        ring
      have h4 : ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10))
            * ((Gn p ^ 2 + Yn p ^ 2) / 2)
          = (1 / 2) * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * (Gn p) ^ 2
              + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * (Yn p) ^ 2) := by
        ring
      rw [Real.norm_eq_abs, h3,
        abs_of_nonneg (mul_nonneg hp (mul_nonneg (abs_nonneg _) (abs_nonneg _))), ← h4]
      exact h2
  -- the bound on the critical slot
  have hQle : (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm)
      ≤ (2 * Cd * Ctr / α + 2 * Cd * Cd / α ^ 2) * Work.Spaces.HkSq α 6 g := by
    refine hcr.2.trans ?_
    have h1 : 2 * critD α * (Ctr * Work.Spaces.HkSq α 6 g)
        ≤ 2 * (Cd / α) * (Ctr * Work.Spaces.HkSq α 6 g) := by
      have hK0 : 0 ≤ 2 * (Ctr * Work.Spaces.HkSq α 6 g) := by positivity
      calc 2 * critD α * (Ctr * Work.Spaces.HkSq α 6 g)
          = (2 * (Ctr * Work.Spaces.HkSq α 6 g)) * critD α := by ring
        _ ≤ (2 * (Ctr * Work.Spaces.HkSq α 6 g)) * (Cd / α) :=
            mul_le_mul_of_nonneg_left hDbnd hK0
        _ = 2 * (Cd / α) * (Ctr * Work.Spaces.HkSq α 6 g) := by ring
    have h2 : 2 * critD α * critD α * Work.Spaces.HkSq α 6 g
        ≤ 2 * (Cd / α) * (Cd / α) * Work.Spaces.HkSq α 6 g := by
      have h11 : critD α * critD α ≤ (Cd / α) * (Cd / α) :=
        mul_le_mul hDbnd hDbnd hD0 (by positivity)
      nlinarith [h11, hH0]
    have h3 : 2 * (Cd / α) * (Ctr * Work.Spaces.HkSq α 6 g)
          + 2 * (Cd / α) * (Cd / α) * Work.Spaces.HkSq α 6 g
        = (2 * Cd * Ctr / α + 2 * Cd * Cd / α ^ 2) * Work.Spaces.HkSq α 6 g := by
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  have hQle' : α ^ 2 * (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm)
      ≤ K * Work.Spaces.HkSq α 6 g := by
    have h1 : α ^ 2 * (2 * Cd * Ctr / α + 2 * Cd * Cd / α ^ 2) * Work.Spaces.HkSq α 6 g
        = (2 * Cd * Ctr * α + 2 * Cd * Cd) * Work.Spaces.HkSq α 6 g := by
      field_simp
    have h2 : 2 * Cd * Ctr * α + 2 * Cd * Cd ≤ 2 * Cd * Ctr + 2 * Cd * Cd := by
      nlinarith [hCd0', hCtr0', hα1, mul_nonneg hCd0' hCtr0']
    have h3 : (2 * Cd * Ctr * α + 2 * Cd * Cd) * Work.Spaces.HkSq α 6 g
        ≤ (2 * Cd * Ctr + 2 * Cd * Cd) * Work.Spaces.HkSq α 6 g :=
      mul_le_mul_of_nonneg_right h2 hH0
    have h4 : α ^ 2 * (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm)
        ≤ α ^ 2 * ((2 * Cd * Ctr / α + 2 * Cd * Cd / α ^ 2) * Work.Spaces.HkSq α 6 g) :=
      mul_le_mul_of_nonneg_left hQle (sq_nonneg α)
    have h5 : α ^ 2 * ((2 * Cd * Ctr / α + 2 * Cd * Cd / α ^ 2) * Work.Spaces.HkSq α 6 g)
        = α ^ 2 * (2 * Cd * Ctr / α + 2 * Cd * Cd / α ^ 2) * Work.Spaces.HkSq α 6 g := by ring
    rw [h5] at h4
    have h6 : K = 2 * Cd * Ctr + 2 * Cd * Cd := hKdef
    rw [h6]
    rw [h1] at h4
    exact h4.trans h3
  -- the AM-GM bound for the critical piece
  have hstep : (∫ p : ℝ × ℝ, α * (ρ p * |Gn p| * |Yn p|) ∂pm)
      ≤ ∫ p : ℝ × ℝ, ((α ^ 2 / (2 * Real.sqrt K)) * (ρ p * (Gn p) ^ 2)
          + (Real.sqrt K / 2) * (ρ p * (Yn p) ^ 2)) ∂pm := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [hρnn] with p hp
      positivity
    · exact (hintG0.const_mul _).add (hintY0.const_mul _)
    · filter_upwards [hρnn] with p hp
      have h1 := amgm_sqrt α K (Gn p) (Yn p) hK0 hα0.le
      have h2 := mul_le_mul_of_nonneg_left h1 hp
      have h3 : α * (ρ p * |Gn p| * |Yn p|) = ρ p * (α * |Gn p| * |Yn p|) := by ring
      rw [h3]
      calc ρ p * (α * |Gn p| * |Yn p|)
          ≤ ρ p * (α ^ 2 * (Gn p) ^ 2 / (2 * Real.sqrt K)
              + Real.sqrt K * (Yn p) ^ 2 / 2) := h2
        _ = (α ^ 2 / (2 * Real.sqrt K)) * (ρ p * (Gn p) ^ 2)
              + (Real.sqrt K / 2) * (ρ p * (Yn p) ^ 2) := by ring
  have hbound1 : α * (∫ p : ℝ × ℝ, ρ p * |Gn p| * |Yn p| ∂pm)
      ≤ Real.sqrt K * Work.Spaces.HkSq α 6 g := by
    have hmain := hstep
    rw [MeasureTheory.integral_const_mul] at hmain
    rw [MeasureTheory.integral_add (hintG0.const_mul _) (hintY0.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmain
    have hRle : (∫ p : ℝ × ℝ, ρ p * (Yn p) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 g := hIgamA.2
    have h3 : (α ^ 2 / (2 * Real.sqrt K)) * (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm)
        ≤ (Real.sqrt K / 2) * Work.Spaces.HkSq α 6 g := by
      have h4 : α ^ 2 * (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm) / (2 * Real.sqrt K)
          ≤ (K * Work.Spaces.HkSq α 6 g) / (2 * Real.sqrt K) :=
        div_le_div_of_nonneg_right hQle' (by positivity)
      have h5 : (α ^ 2 / (2 * Real.sqrt K)) * (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm)
          = α ^ 2 * (∫ p : ℝ × ℝ, ρ p * (Gn p) ^ 2 ∂pm) / (2 * Real.sqrt K) := by ring
      have h6 : (K * Work.Spaces.HkSq α 6 g) / (2 * Real.sqrt K)
          = (Real.sqrt K / 2) * Work.Spaces.HkSq α 6 g := by
        have h7 : K = Real.sqrt K * Real.sqrt K := by rw [← sq, Real.sq_sqrt hK0.le]
        rw [div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.sqrt K))]
        rw [show (Real.sqrt K / 2) * Work.Spaces.HkSq α 6 g * (2 * Real.sqrt K)
            = (Real.sqrt K * Real.sqrt K) * Work.Spaces.HkSq α 6 g by ring]
        rw [← h7]
      rw [← h5, h6] at h4
      exact h4
    have h4 : (Real.sqrt K / 2) * (∫ p : ℝ × ℝ, ρ p * (Yn p) ^ 2 ∂pm)
        ≤ (Real.sqrt K / 2) * Work.Spaces.HkSq α 6 g :=
      mul_le_mul_of_nonneg_left hRle (by positivity)
    linarith [hmain, h3, h4]
  -- the second (pointwise-compatible) piece
  have hbound2 : (∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10)
      * |Gn p| * |Yn p| ∂pm) ≤ Work.Spaces.HkSq α 6 g := by
    have hstep2 : (∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10)
        * |Gn p| * |Yn p| ∂pm)
        ≤ ∫ p : ℝ × ℝ, (1 / 2) * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10)
            * (Gn p) ^ 2
          + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * (Yn p) ^ 2) ∂pm := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [hρ1nn] with p hp
        positivity
      · exact (hintG1.add hintY1).const_mul (1 / 2)
      · filter_upwards [hρ1nn] with p hp
        have h1 := Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add (Gn p) (Yn p)
        rw [abs_mul] at h1
        have h2 := mul_le_mul_of_nonneg_left h1 hp
        have h3 : (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * |Gn p| * |Yn p|
            = ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10))
              * (|Gn p| * |Yn p|) := by ring
        have h4 : ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10))
              * ((Gn p ^ 2 + Yn p ^ 2) / 2)
            = (1 / 2) * ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * (Gn p) ^ 2
                + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * (Yn p) ^ 2) := by
            ring
        rw [h3, ← h4]
        exact h2
    refine hstep2.trans ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintG1 hintY1]
    have h2 := hG_p.2
    have h3 := hIgam_p.2
    linarith [h2, h3]
  -- the pointwise bound on the integrand `F`
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b₁ a f z θ
          * Work.Spaces.DzIter (b - b₁ + 1) g z θ * Work.Spaces.mixed b a g z θ|
        ≤ 1000 * Work.Spaces.WlInf α 6 f
          * (α * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
                * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
                * |Work.Spaces.mixed b a g z θ|)
            + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10)
                * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
                * |Work.Spaces.mixed b a g z θ|) := by
    intro z θ hz hθ hθ2
    have hσ : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo ⟨hθ, hθ2⟩
    have hb := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 (a := a) (b := b₁)
      hα0 hfs hfm ha (by omega) hz (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ, hθ2⟩)
    rw [Work.FTS.TransportS.leafGam]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Work.Spaces.w z)),
      abs_of_nonneg (Real.rpow_nonneg hσ.le _)]
    have hsplit := gam_mul_split (α := α) hσ
    have hmain : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed b₁ a f z θ|
          * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ|
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (1000 * (Work.Spaces.WlInf α 6 f
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
          * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ| := by
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.DzIter (b - b₁ + 1) g z θ| * |Work.Spaces.mixed b a g z θ| := by
        positivity
      calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed b₁ a f z θ|
            * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|
          = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) * |Work.Spaces.mixed b₁ a f z θ| := by ring
        _ ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)
              * (1000 * (Work.Spaces.WlInf α 6 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
            mul_le_mul_of_nonneg_left hb hnn
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (1000 * (Work.Spaces.WlInf α 6 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ| := by ring
    refine hmain.trans ?_
    have hstep : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (1000 * (Work.Spaces.WlInf α 6 f
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
          * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ|
        = 1000 * Work.Spaces.WlInf α 6 f
          * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          * |Work.Spaces.DzIter (b - b₁ + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ| := by ring
    have hfin : 1000 * Work.Spaces.WlInf α 6 f * (Work.Spaces.w z) ^ 2
          * (α * (Real.sin (2 * θ)) ^ (-(1 - α / 10)) + (Real.sin (2 * θ)) ^ (α / 10))
          * |Work.Spaces.DzIter (b - b₁ + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
        = 1000 * Work.Spaces.WlInf α 6 f
          * (α * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 - α / 10))
                * |Work.Spaces.DzIter (b - b₁ + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
            + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (α / 10)
                * |Work.Spaces.DzIter (b - b₁ + 1) g z θ| * |Work.Spaces.mixed b a g z θ|) := by
      ring
    rw [hstep, hsplit]
    exact le_of_eq hfin
  -- integrability of the integrand
  have hmajF : MeasureTheory.Integrable (fun p : ℝ × ℝ => 1000 * Work.Spaces.WlInf α 6 f
      * (α * (ρ p * |Gn p| * |Yn p|)
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10) * |Gn p| * |Yn p|)) pm := by
    have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => α * (ρ p * |Gn p| * |Yn p|)) pm :=
      hintA.const_mul α
    exact (h1.add hintB).const_mul (1000 * Work.Spaces.WlInf α 6 f)
  have haesmF : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2) pm := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_w2_sig_Qd _)
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed b₁ a f p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _ ((hfs.mixed b₁ a).continuousOn)
    have h3 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hgs.DzIter (b - b₁ + 1)).continuousOn
    have h4 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed b a g p.1 p.2) pm :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hgs.mixed b a).continuousOn
    exact ((h1.mul h2).mul h3).mul h4
  have hbase : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
      * Work.Spaces.mixed b a g p.1 p.2) pm := by
    refine MeasureTheory.Integrable.mono' hmajF haesmF ?_
    filter_upwards [ae_pm_snd_mem_Ioo, ae_pm_fst_pos] with p hp hp1
    rw [Real.norm_eq_abs]
    exact hpt p.1 p.2 hp1 hp.1 hp.2
  refine ⟨?_, ?_⟩
  · show MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
        * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
        * Work.Spaces.mixed b a g p.1 p.2)
        (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    rw [← pm_eq_restrict]
    exact hbase
  · have habs : |∫ p : ℝ × ℝ, Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2 ∂pm|
        ≤ ∫ p : ℝ × ℝ, |Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2| ∂pm :=
      MeasureTheory.abs_integral_le_integral_abs
    have hmonoI : (∫ p : ℝ × ℝ, |Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a f p.1 p.2 * Work.Spaces.DzIter (b - b₁ + 1) g p.1 p.2
          * Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ ∫ p : ℝ × ℝ, 1000 * Work.Spaces.WlInf α 6 f
            * (α * (ρ p * |Gn p| * |Yn p|)
              + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (α / 10)
                  * |Gn p| * |Yn p|) ∂pm := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hmajF ?_
      · exact Filter.Eventually.of_forall fun p => abs_nonneg _
      · filter_upwards [ae_pm_snd_mem_Ioo, ae_pm_fst_pos] with p hp hp1
        exact hpt p.1 p.2 hp1 hp.1 hp.2
    refine habs.trans (hmonoI.trans ?_)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hintA.const_mul α) hintB,
      MeasureTheory.integral_const_mul]
    have h1 := hbound1
    have h2 := hbound2
    have hW := hW0
    nlinarith [h1, h2, hW, hH0, Real.sqrt_nonneg K]

end Work.FTS.StrongPersist.N6Trans.SixRoute
