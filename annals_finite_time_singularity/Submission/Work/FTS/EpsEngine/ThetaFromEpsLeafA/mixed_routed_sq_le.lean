import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.StepFacts.SlotAux.RouteAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.RPFresh.integral_mul_sq_le_sq_mul_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/EpsEngine/ThetaFromEpsLeafA/mixed_routed_sq_le.lean`

The **routed `L²`-slot bound** for the log-coordinate mollifier `J_ε`: every framed derivative
`D_z^b D_θ^a (J_ε g)` is bounded, pointwise in `(z,θ)`, by its *fully routed* kernel form

  `D_z^b D_θ^a (J_ε g)(z,θ) = 2^a ∫_p ∂₁^b∂₂^a(Jker ρ ε)(p) · g(z e^{-p₁}, arctan(tan θ e^{-p₂}))`

(`Work.FTS.StrongEps.mixed_Jeps_kernel_partial`), and Cauchy–Schwarz for the `p`-integral turns
this into

  `(D_z^b D_θ^a (J_ε g)(z,θ))² ≤ 4^a (∫ |∂₁^b∂₂^a Jker|) (∫ |∂₁^b∂₂^a Jker| · (g ∘ shift)²)`

— exactly the statement below.  All the `(z,θ)`-dependence that is *not* routed is carried by the
single weighted `L²`-profile `∫ |K| (g∘shift)²`, which is what the later `H^k`-gain estimates
consume.

The only analytic input is that `∂₁^b∂₂^a (Jker ρ ε)` is continuous with compact support
(`Work.FTS.StrongEps.EpsE4Thr.KdK_continuous`, `…KdK_hasCompactSupport`) and that the shifted
profile `p ↦ g (z e^{-p₁}) (arctan (tan θ e^{-p₂}))` is *continuous*: the shifts place every
argument strictly inside the open quadrant `Quad = (0,∞) × (0,π/2)`, where `g` is `C^∞`.
The Cauchy–Schwarz step is the real-integral Bunyakovsky inequality
`Work.RPFresh.integral_mul_sq_le_sq_mul_sq`, applied to the nonnegative functions
`√|K|` and `√|K|·|g∘shift|` (the sign of `K` being absorbed by `|∫ K·(g∘shift)| ≤ ∫ |K·(g∘shift)|`),
so that no hypothesis on the (possibly unbounded) profile `g` is needed beyond continuity on the
quadrant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

set_option maxHeartbeats 1000000

/-! ## The abstract Cauchy–Schwarz core -/

/-- **Cauchy–Schwarz for a compactly supported weight.**  For a continuous compactly supported
`K` and an arbitrary continuous `G`,

  `(∫ K G)² ≤ (∫ |K|) · (∫ |K| G²)`.

Proof: `|∫ K G| ≤ ∫ |K G| = ∫ √|K| · (√|K| |G|)`, and Bunyakovsky applied to
`√|K|` and `√|K| |G|` bounds the square by `(∫ |K|)(∫ |K| G²)`.  Both square-integrable
functions of the Cauchy–Schwarz are continuous (hence measurable), and both squares
(`|K|` and `|K| G²`) are continuous with compact support, hence integrable. -/
theorem cs_sq_le_of_compact {K G : ℝ × ℝ → ℝ} (hKc : Continuous K)
    (hKcpt : HasCompactSupport K) (hGc : Continuous G) :
    (∫ p : ℝ × ℝ, K p * G p) ^ 2
      ≤ (∫ p : ℝ × ℝ, |K p|) * (∫ p : ℝ × ℝ, |K p| * G p ^ 2) := by
  have hKabsi : Integrable (fun p : ℝ × ℝ => |K p|) :=
    hKc.abs.integrable_of_hasCompactSupport hKcpt.abs
  have hprodi : Integrable (fun p : ℝ × ℝ => |K p| * G p ^ 2) := by
    have h1 : HasCompactSupport (fun p : ℝ × ℝ => |K p| * G p ^ 2) := by
      refine hKcpt.mono (fun p hp => ?_)
      simp only [Function.mem_support] at hp ⊢
      intro hK0
      exact hp (by rw [hK0, abs_zero, zero_mul])
    exact (hKc.abs.mul (hGc.pow 2)).integrable_of_hasCompactSupport h1
  have hFmeas : Measurable (fun p : ℝ × ℝ => Real.sqrt |K p|) :=
    Real.continuous_sqrt.measurable.comp hKc.abs.measurable
  have hHmeas : Measurable (fun p : ℝ × ℝ => Real.sqrt |K p| * |G p|) :=
    hFmeas.mul hGc.abs.measurable
  have hF2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt |K p|) ^ 2) :=
    hKabsi.congr (Filter.Eventually.of_forall fun p => (Real.sq_sqrt (abs_nonneg (K p))).symm)
  have hH2 : Integrable (fun p : ℝ × ℝ => (Real.sqrt |K p| * |G p|) ^ 2) :=
    hprodi.congr (Filter.Eventually.of_forall fun p => by
      beta_reduce
      rw [mul_pow, Real.sq_sqrt (abs_nonneg (K p)), sq_abs])
  have hcs := Work.RPFresh.integral_mul_sq_le_sq_mul_sq (MeasureTheory.volume : Measure (ℝ × ℝ))
      (f := fun p : ℝ × ℝ => Real.sqrt |K p|) (h := fun p : ℝ × ℝ => Real.sqrt |K p| * |G p|)
      hFmeas.aestronglyMeasurable hHmeas.aestronglyMeasurable hF2 hH2
  have hkey : (∫ p : ℝ × ℝ, Real.sqrt |K p| * (Real.sqrt |K p| * |G p|))
      = ∫ p : ℝ × ℝ, |K p| * |G p| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [← mul_assoc,
      show Real.sqrt |K p| * Real.sqrt |K p| = |K p| from by
        rw [← sq, Real.sq_sqrt (abs_nonneg (K p))]]
  have hA : (∫ p : ℝ × ℝ, (Real.sqrt |K p|) ^ 2) = ∫ p : ℝ × ℝ, |K p| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [Real.sq_sqrt (abs_nonneg (K p))]
  have hB : (∫ p : ℝ × ℝ, (Real.sqrt |K p| * |G p|) ^ 2)
      = ∫ p : ℝ × ℝ, |K p| * G p ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [mul_pow, Real.sq_sqrt (abs_nonneg (K p)), sq_abs]
  rw [hkey, hA, hB] at hcs
  have habs : |∫ p : ℝ × ℝ, K p * G p| ≤ ∫ p : ℝ × ℝ, |K p| * |G p| := by
    refine (MeasureTheory.abs_integral_le_integral_abs
      (μ := (MeasureTheory.volume : Measure (ℝ × ℝ)))
      (f := fun p : ℝ × ℝ => K p * G p)).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [abs_mul]
  have hYnn : 0 ≤ ∫ p : ℝ × ℝ, |K p| * |G p| :=
    integral_nonneg fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsq : (|∫ p : ℝ × ℝ, K p * G p|) ^ 2 ≤ (∫ p : ℝ × ℝ, |K p| * |G p|) ^ 2 := by
    refine (sq_le_sq).mpr ?_
    simpa only [abs_of_nonneg hYnn, abs_abs] using habs
  calc (∫ p : ℝ × ℝ, K p * G p) ^ 2
      = (|∫ p : ℝ × ℝ, K p * G p|) ^ 2 := (sq_abs _).symm
    _ ≤ (∫ p : ℝ × ℝ, |K p| * |G p|) ^ 2 := hsq
    _ ≤ (∫ p : ℝ × ℝ, |K p|) * (∫ p : ℝ × ℝ, |K p| * G p ^ 2) := hcs

/-! ## The shifted profile is continuous -/

/-- The shifted profile `p ↦ g (z e^{-p₁}) (arctan (tan θ e^{-p₂}))` is continuous on `ℝ²`,
for `z > 0` and `θ ∈ (0,π/2)`: the shifts stay strictly inside the open quadrant
(`z e^{-p₁} > 0` and `arctan (tan θ e^{-p₂}) ∈ (0,π/2)`), and `g` is continuous there. -/
theorem continuous_shiftedProfile {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous (fun p : ℝ × ℝ =>
      g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  have hcont : ContinuousOn (Function.uncurry g) Work.FTS.StrongEps.Quad :=
    (contDiffOn_zero).mp (hg 0)
  have hΦ : Continuous
      (fun p : ℝ × ℝ =>
        (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)) := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).comp continuous_fst
    · exact Real.continuous_arctan.comp
        ((continuous_const.mul (Real.continuous_exp.comp continuous_neg)).comp continuous_snd)
  have hmem : ∀ p : ℝ × ℝ,
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
        ∈ Work.FTS.StrongEps.Quad := by
    intro p
    refine ⟨mul_pos hz (Real.exp_pos _), ?_, ?_⟩
    · exact Real.arctan_pos.mpr
        (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _))
    · exact Real.arctan_lt_pi_div_two _
  have h := hcont.comp_continuous hΦ hmem
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

/-- **Cauchy–Schwarz for the routed slot**, in exactly the shape the `H^k`-gain estimates
consume: with `K = ∂₁^b ∂₂^a (Jker ρ ε)`, the square of the routed slot integral
`∫_p K(p) · g(z e^{-p₁}, arctan(tan θ e^{-p₂}))` is bounded by
`(∫ |K|) · (∫ |K| · (g ∘ shift)²)`. -/
theorem cs_routed {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (a b : ℕ) :
    (∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|)
        * (∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
            * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
  cs_sq_le_of_compact (K := Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a)
    (G := fun p : ℝ × ℝ =>
      g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε b a)
    (Work.FTS.StrongEps.EpsE4Thr.KdK_hasCompactSupport hρ hε b a)
    (continuous_shiftedProfile hg hz hθ)

/-! ## The target -/

theorem mixed_routed_sq_le {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (a b : ℕ) :
    (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
      ≤ ((4 : ℝ) ^ a * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|)
        * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
            * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
  -- route the framed derivative `D_z^b D_θ^a (J_ε g)` completely onto the kernel
  have hrepr : Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ
      = (2 : ℝ) ^ a * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
          * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    have h := Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hg hz hθ b a 0 0
      (Nat.zero_le b) (Nat.zero_le a)
    rw [Nat.sub_zero, Nat.sub_zero] at h
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    simp only [Work.Spaces.mixed]
    rw [h]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [show Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        = iteratedDeriv b (fun s => iteratedDeriv a
            (fun t => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1
        from congrFun (Work.FTS.StrongEps.Kd_eq (Work.FTS.StrongEps.Jker ρ ε) b a) p]
  -- Cauchy–Schwarz for the `p`-integral
  have hcs := cs_routed hρ hε hg hz hθ a b
  have hpow : ((2 : ℝ) ^ a) ^ 2 = (4 : ℝ) ^ a := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm a 2]
  rw [hrepr]
  have h1 : ((2 : ℝ) ^ a * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      = (4 : ℝ) ^ a * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
    rw [mul_pow, hpow]
  rw [h1]
  refine le_trans (mul_le_mul_of_nonneg_left hcs (by positivity))
    (le_of_eq (mul_assoc _ _ _).symm)

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
