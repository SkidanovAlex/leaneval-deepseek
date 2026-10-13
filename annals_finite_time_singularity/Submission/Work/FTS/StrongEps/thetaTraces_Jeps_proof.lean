/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/thetaTraces_Jeps_proof.lean`

The `θ`-traces of the log-coordinate mollifier `J_ε f` up to order `10`, from the uniform
level-`7` `θ`-trace hypotheses of the profile: `Work.FTS.StrongEps.thetaTraces_Jeps_proof`.

## What has to be proved

`PhiStar.ThetaTraces α 10 (J_ε f)` asks that for every `s ≤ 9` and every `z > 0`,

  `sin(2θ)^(1-γ) * (D_z^s (J_ε f) z θ)^2 → 0`   as `θ → 0⁺`  and  as `θ → (π/2)⁻`,

uniformly in `z` (the `z` is fixed, but the hypothesis is uniform in `z`).

## The proof

The whole content is that the `z`-derivatives *route onto the kernel*.  In the log coordinates
`s = log z`, `ζ = log tan θ` the mollifier is a convolution (`Jeps_eq_integral`), so with
`p` the integration variable,

* the shift acts as the translation `p ↦ p` on `log z` and `log tan θ`, hence
  `∂_{p₁}(f ∘ shift) = -(D_z f) ∘ shift`;
* the routed kernel `∂₁^s (Jker ρ ε)` is smooth and supported in the closed ball of radius `ε`.

Integrating by parts `s` times in `p₁` (the boundary terms vanish because the kernel is
compactly supported) gives the identity

  `D_z^s (J_ε f) z θ = ∫ p, ∂₁^s (Jker ρ ε) p · f (z · e^{-p₁}) (arctan (tan θ · e^{-p₂}))`

(`TJ.mixed_zero_Jeps_routed`, an instance of the existing `mixed_Jeps_kernel_partial` with the
kernel-side index `j' = 0`).  Consequently `D_z^s (J_ε f)` at `(z,θ)` is a weighted average of
**values of `f` itself** (no derivative of `f` at all!) over the `(log z, log tan θ)`-ball of
radius `ε` around `(z,θ)`.

The weight `sin(2θ)^{1-γ}` can be moved from `θ` to the shifted angle `θ' = thShift θ p₂` at the
price of the factor `e^{ε|1-γ|}` (`Traces.sin_rpow_thShift_le`), and the shifted angles stay in
`(0, δ)` (resp. `(π/2 - δ, π/2)`) as soon as `θ` is close enough to the endpoint
(`Traces.eventually_thShift_{lt,gt}`).  Hence the level-`0` half of the hypotheses (`a = b = 0`,
which is `0 + 0 ≤ 7`) bounds `|f|` on the whole window, and the routed integral is bounded by the
mass of the routed kernel times that bound (`TJ.abs_routed_Jeps_le`).  This proves both one-sided
limits.  (In particular *no* derivative of `f` beyond order `0` is used; the level-`7`
hypotheses are simply what the caller has available.)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.PhiStar.ThetaTraces
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.Traces.sin_rpow_thShift_le
import Submission.Work.FTS.StrongEps.Traces.eventually_thShift_lt
import Submission.Work.FTS.StrongEps.Traces.eventually_thShift_gt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TJ

/-- A real function which is eventually nonnegative and eventually `≤ ε` for every `ε > 0` tends
to `0`. -/
theorem tendsto_zero_of_eventually_le {l : Filter ℝ} {F : ℝ → ℝ}
    (hnn : ∀ᶠ x in l, 0 ≤ F x) (h : ∀ ε' > 0, ∀ᶠ x in l, F x ≤ ε') :
    Tendsto F l (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hnn] with x hx using lt_of_lt_of_le ha hx
  · have h2 : 0 < b / 2 := by linarith
    filter_upwards [h (b / 2) h2] with x hx using lt_of_le_of_lt hx (by linarith)

/-- **The routed representation of `D_z^s (J_ε f)`**: all `s` radial derivatives are moved onto
the (smooth, compactly supported) kernel by `s` integrations by parts in the shift parameter
`p₁`, so that the integrand carries the *values* of `f` only. -/
theorem mixed_zero_Jeps_routed {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : Fn} (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (s : ℕ) :
    Work.Spaces.mixed s 0 (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p * f (zShift z p.1) (thShift θ p.2) := by
  rw [mixed_Jeps_kernel_partial ρ hρ hε hsm hz hθ s 0 0 0 (Nat.zero_le s) (le_refl 0)]
  simp only [Nat.sub_zero, pow_zero, one_mul]
  congr 1
  funext p
  simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, EpsE4Thr.KdK, Kd_eq,
    iteratedDeriv_zero]

/-- **The routed kernel vanishes off the ball of radius `ε`** (a point where it does not vanish
satisfies `|p.1| + |p.2| ≤ 2ε`, and here the sharp form holds: the kernel `Kdr ρ a b` of `ρ` is
supported in the unit ball). -/
theorem KdK_eq_zero_of_not_mem {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (a b : ℕ) {p : ℝ × ℝ} (hp : ¬ (max |p.1| |p.2| ≤ ε)) : EpsE4Thr.KdK ρ ε a b p = 0 := by
  have hstep : ∀ u : ℝ, (ε⁻¹ * u) ^ 2 ≤ 1 → |u| ≤ ε := by
    intro u hu
    have h3 : |ε⁻¹ * u| ≤ 1 := (sq_le_one_iff_abs_le_one (ε⁻¹ * u)).mp hu
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)] at h3
    have h4 : ε⁻¹ * |u| * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right h3 hε.le
    have h5 : ε⁻¹ * |u| * ε = |u| := by field_simp
    linarith
  rw [EpsE4Thr.Kd_Jker_scale hρ ε a b p]
  have hq : EpsE4Thr.Kdr ρ a b (ε⁻¹ • p) = 0 := by
    by_contra hne
    have hsupp := EpsE4Thr.Kdr_support hρ a b (ε⁻¹ • p) hne
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul] at hsupp
    exact hp (max_le (hstep p.1 (by nlinarith [sq_nonneg (ε⁻¹ * p.2)]))
      (hstep p.2 (by nlinarith [sq_nonneg (ε⁻¹ * p.1)])))
  simp only [Jker, hq, mul_zero]

/-- **The routed integral is bounded by the mass of the routed kernel times the sup of `f` on the
window**: the shifted profile is continuous on the compact ball of radius `ε` (the shift maps it
into the open quadrant), and off that ball the routed kernel vanishes. -/
theorem abs_routed_Jeps_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (a b : ℕ) {f : Fn} (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ M : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hM : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
      |f (zShift z p.1) (thShift θ p.2)| ≤ M) :
    |∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε a b p * f (zShift z p.1) (thShift θ p.2)|
      ≤ (∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε a b p|) * M := by
  have hGz : ∀ p : ℝ × ℝ, ¬ (max |p.1| |p.2| ≤ ε) → EpsE4Thr.KdK ρ ε a b p = 0 :=
    fun p hp => KdK_eq_zero_of_not_mem hρ hε a b hp
  have hGc : ContinuousOn (EpsE4Thr.KdK ρ ε a b) (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (EpsE4Thr.KdK_continuous hρ ε a b).continuousOn
  have hAc : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    ((hsm 0).continuousOn).comp (continuous_shift_pair z θ).continuousOn
      (fun _ _ => ⟨zShift_pos hz, thShift_mem hθ⟩)
  have hz0 : ∀ p : ℝ × ℝ, p ∉ Metric.closedBall (0 : ℝ × ℝ) ε →
      EpsE4Thr.KdK ρ ε a b p = 0 := fun p hp =>
    hGz p (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp; exact hp)
  have hon1 : IntegrableOn (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p| * M)
      (Metric.closedBall (0 : ℝ × ℝ) ε) volume :=
    ((hGc.abs).mul continuousOn_const).integrableOn_compact (isCompact_closedBall _ _)
  have hInt1 : Integrable (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p| * M) :=
    hon1.integrable_of_forall_notMem_eq_zero (fun p hp => by rw [hz0 p hp, abs_zero, zero_mul])
  have hon2 : IntegrableOn (fun p : ℝ × ℝ => EpsE4Thr.KdK ρ ε a b p
      * f (zShift z p.1) (thShift θ p.2)) (Metric.closedBall (0 : ℝ × ℝ) ε) volume :=
    (hGc.mul hAc).integrableOn_compact (isCompact_closedBall _ _)
  have hInt2 : Integrable (fun p : ℝ × ℝ => EpsE4Thr.KdK ρ ε a b p
      * f (zShift z p.1) (thShift θ p.2)) :=
    hon2.integrable_of_forall_notMem_eq_zero (fun p hp => by rw [hz0 p hp, zero_mul])
  calc |∫ p, EpsE4Thr.KdK ρ ε a b p * f (zShift z p.1) (thShift θ p.2)|
      ≤ ∫ p, |EpsE4Thr.KdK ρ ε a b p * f (zShift z p.1) (thShift θ p.2)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, |EpsE4Thr.KdK ρ ε a b p| * M :=
        integral_mono hInt2.abs hInt1 (fun p => by
          by_cases hpm : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
          · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hpm
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (hM p (le_trans (le_max_left _ _) hpm) (le_trans (le_max_right _ _) hpm))
              (abs_nonneg _)
          · rw [hz0 p hpm, zero_mul, abs_zero, zero_mul])
    _ = (∫ p, |EpsE4Thr.KdK ρ ε a b p|) * M := integral_mul_const M _

end TJ

theorem thetaTraces_Jeps_proof {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (ht0 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (ht1 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    Work.FTS.PhiStar.ThetaTraces α 10 (Work.FTS.StrongEps.Jeps ρ ε f) := by
  have _hα := hα
  intro s _hs z hz
  -- the routed representation, on the open quadrant
  have hcm : ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Spaces.mixed s 0 (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p * f (zShift z p.1) (thShift θ p.2) :=
    fun θ hθ => TJ.mixed_zero_Jeps_routed hρ hε hsm hz hθ s
  have hIθ : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  have hIθ' : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) :=
    Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  refine ⟨?_, ?_⟩
  · -- ### `θ → 0⁺`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine TJ.tendsto_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε'' hε''
        set K : ℝ := Real.exp (ε * |1 - Work.Spaces.gam α|) with hKdef
        have hKpos : 0 < K := Real.exp_pos _
        set C : ℝ := ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε s 0 p| with hCdef
        have hC0 : 0 ≤ C := by
          rw [hCdef]; exact integral_nonneg fun p => abs_nonneg _
        obtain ⟨δ, hδpos, hδ⟩ :=
          ht0 0 0 (by norm_num) (ε'' / (C ^ 2 + 1) / K) (by positivity)
        simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] at hδ
        have hθs : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → thShift θ p < δ :=
          Traces.eventually_thShift_lt ε δ hδpos
        filter_upwards [hIθ, hθs] with θ hθ hθs
        have hsinpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt ((ε'' / (C ^ 2 + 1))
          / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = (ε'' / (C ^ 2 + 1))
            / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg (by positivity) hsinpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |f (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hδ (thShift θ p.2) hth.1 (hθs p.2 hp2) (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α)
            hθ hε.le hp2
          have hsq : (f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsinpos]
            calc (f (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (f (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (K * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = K * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                    * (f (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ K * (ε'' / (C ^ 2 + 1) / K) := mul_le_mul_of_nonneg_left hhyp hKpos.le
              _ = ε'' / (C ^ 2 + 1) := by rw [mul_div_cancel₀ _ hKpos.ne']
          have hsq' : |f (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hJep := TJ.abs_routed_Jeps_le hρ hε s 0 hsm hz hθ hMb
        have hjsq : (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ (C * M) ^ 2 := by
          rw [← sq_abs, hCdef]
          exact pow_le_pow_left₀ (abs_nonneg _) hJep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
                  * f (zShift z p.1) (thShift θ p.2)) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (C * M) ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsinpos.le
          _ = C ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2) := by ring
          _ = C ^ 2 * (ε'' / (C ^ 2 + 1)) := by rw [hMsq, mul_div_cancel₀ _ hsinpos.ne']
          _ ≤ ε'' := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
              nlinarith [hε''.le, sq_nonneg C]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ] with θ hθ
    rw [hcm θ hθ]
  · -- ### `θ → (π/2)⁻`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := by
      refine TJ.tendsto_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ'] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε'' hε''
        set K : ℝ := Real.exp (ε * |1 - Work.Spaces.gam α|) with hKdef
        have hKpos : 0 < K := Real.exp_pos _
        set C : ℝ := ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε s 0 p| with hCdef
        have hC0 : 0 ≤ C := by
          rw [hCdef]; exact integral_nonneg fun p => abs_nonneg _
        obtain ⟨δ, hδpos, hδ⟩ :=
          ht1 0 0 (by norm_num) (ε'' / (C ^ 2 + 1) / K) (by positivity)
        simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] at hδ
        have hθs : ∀ᶠ θ in 𝓝[<] (π / 2), ∀ p : ℝ, |p| ≤ ε → π / 2 - δ < thShift θ p :=
          Traces.eventually_thShift_gt ε δ hδpos
        filter_upwards [hIθ', hθs] with θ hθ hθs
        have hsinpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt ((ε'' / (C ^ 2 + 1))
          / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = (ε'' / (C ^ 2 + 1))
            / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg (by positivity) hsinpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |f (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hδ (thShift θ p.2) hth.2 (hθs p.2 hp2) (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α)
            hθ hε.le hp2
          have hsq : (f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsinpos]
            calc (f (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (f (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (K * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = K * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                    * (f (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ K * (ε'' / (C ^ 2 + 1) / K) := mul_le_mul_of_nonneg_left hhyp hKpos.le
              _ = ε'' / (C ^ 2 + 1) := by rw [mul_div_cancel₀ _ hKpos.ne']
          have hsq' : |f (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hJep := TJ.abs_routed_Jeps_le hρ hε s 0 hsm hz hθ hMb
        have hjsq : (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ (C * M) ^ 2 := by
          rw [← sq_abs, hCdef]
          exact pow_le_pow_left₀ (abs_nonneg _) hJep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
                  * f (zShift z p.1) (thShift θ p.2)) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (C * M) ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsinpos.le
          _ = C ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2) := by ring
          _ = C ^ 2 * (ε'' / (C ^ 2 + 1)) := by rw [hMsq, mul_div_cancel₀ _ hsinpos.ne']
          _ ≤ ε'' := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
              nlinarith [hε''.le, sq_nonneg C]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ'] with θ hθ
    rw [hcm θ hθ]

end Work.FTS.StrongEps
