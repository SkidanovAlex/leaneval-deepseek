/- Assembled copy (namespace `HardyAlt`) of the `l12dens_continuousAt` proof, wired to the three finished
sub-lemmas `Hardy.pzSqSeta_box_integrable`, `Hardy.slice_sinCos2_integrable`, `Hardy.pzMoment_le_sqrt`. -/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Blocks.moment_relation
import Submission.Work.FTS.EllipticEst.sliceCSWeightedOpen
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.pzSqSeta_box_integrable
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.slice_sinCos2_integrable
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.pzMoment_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.HardyAlt

set_option maxHeartbeats 1000000

/-! ## Auxiliary facts for `l12dens_continuousAt`

Since `K θ = 3 sin θ cos²θ` and `Elliptic.sinCos2 θ = sin θ cos²θ`, we have

  `L12dens K f s = 3 · F_*(f)(s) / s`,

where `F_*(f)(s) = ∫_θ f(s,θ) sinθcos²θ dθ` is the angular moment (`Work.Elliptic.Fstar`), and
`s ↦ 1/s` is continuous at `z > 0`.  So it suffices to prove that `F_*(f)` is continuous at `z`.

`Work.FTS.EllipticEst.Blocks.moment_relation` exhibits `F_*(f)` as the primitive of the angular
moment `M(r) = ∫_θ ∂_z f(r,θ) sinθcos²θ dθ` of the radial derivative, and the pointwise bound
`|M(r)| ≤ √(π/2) · √(B(r))`, where `B(r) = ∫_θ HkIntegrand α 4 f r θ`, shows that the increment of
`F_*(f)` is dominated by the primitive of `√B`.  The latter is continuous at `z` because `B` is
integrable (`HkMem.2`) and `√B ≤ |B| + 1`. -/

/-- `√x ≤ |x| + 1`. -/
private lemma sqrt_le_abs_add_one (x : ℝ) : Real.sqrt x ≤ |x| + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [le_abs_self x, abs_nonneg x, sq_abs x, sq_nonneg x]

/-- **`L12dens` in terms of the angular moment.**  `L12dens K f s = 3 · F_*(f)(s) / s`. -/
theorem L12dens_eq_three_Fstar (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K f s = 3 * Work.Elliptic.Fstar f s / s := by
  have hpt : ∀ θ : ℝ, Work.Spaces.K θ * f s θ = 3 * (f s θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    simp only [Work.Spaces.K, Work.Elliptic.sinCos2]
    ring
  rw [Work.FM.L12dens, Work.Elliptic.Fstar, MeasureTheory.integral_div]
  congr 1
  calc ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ
      = ∫ θ in Work.Spaces.Iθ, 3 * (f s θ * Work.Elliptic.sinCos2 θ) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = 3 * ∫ θ in Work.Spaces.Iθ, f s θ * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.integral_const_mul 3 _

/-- **Continuity of the angular moment.**  With the three analytic inputs — box integrability of
`(∂_z f)² sin(2θ)^{-η}`, integrability of the angular slice `f z· · sinθcos²θ`, and the
`√`-bound on the angular moment of `∂_z f` — the angular moment `F_*(f)` is continuous at `z`. -/
theorem Fstar_continuousAt_of_aux (α : ℝ) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hSO : Work.FTS.EllipticEst.SmoothOpen f)
    (hbox : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn
        (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz f s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iz)
    (hmom : ∀ s : ℝ, 0 < s →
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
        ≤ Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) :
    ContinuousAt (Work.Elliptic.Fstar f) z := by
  have hle : z / 2 ≤ 2 * z := by linarith
  -- The angular moment of `∂_z f`.
  set M : ℝ → ℝ := fun r =>
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ with hMdef
  -- The majorant `Ψ` of `M`.
  set Ψ : ℝ → ℝ := fun r =>
    Real.sqrt (Real.pi / 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) with hΨdef
  have hΨnn : ∀ r : ℝ, 0 ≤ Ψ r := fun r => by
    rw [hΨdef]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- ## The chain identity, from `moment_relation`.
  have hchain : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b - Work.Elliptic.Fstar f a = ∫ r in Set.Icc a b, M r := by
    intro a b ha hab
    have h := Work.FTS.EllipticEst.Blocks.moment_relation f hSO hbox hsl ha hab
    simp only [hMdef]
    linarith [h]
  -- ## Integrability of the majorant near `z`.
  have hBint : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Icc (z / 2) (2 * z)) :=
    hB.mono_set (fun x hx => by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      linarith [hz, hx.1])
  have hdom : MeasureTheory.IntegrableOn
      (fun r => Real.sqrt (Real.pi / 2)
        * (|(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)| + 1))
      (Set.Icc (z / 2) (2 * z)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun r => |(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)| + 1)
        (Set.Icc (z / 2) (2 * z)) :=
      hBint.abs.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp))
    exact h1.const_mul (Real.sqrt (Real.pi / 2))
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Icc (z / 2) (2 * z)) := by
    refine hdom.mono' ?_ ?_
    · rw [hΨdef]
      exact aestronglyMeasurable_const.mul
        ((hBint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable)
    · filter_upwards with r
      rw [hΨdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (sqrt_le_abs_add_one _) (Real.sqrt_nonneg _)
  -- ## The primitive of `Ψ` is continuous at `z`.
  have hΨu : MeasureTheory.IntegrableOn Ψ (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle]
    exact hΨint
  have hprim : ContinuousOn (fun t => ∫ r in z..t, Ψ r) (Set.uIcc (z / 2) (2 * z)) :=
    intervalIntegral.continuousOn_primitive_interval' hΨu.intervalIntegrable
      (by rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩)
  have hprim_at : ContinuousAt (fun t => ∫ r in z..t, Ψ r) z :=
    hprim.continuousAt
      (by
        rw [Set.uIcc_of_le hle]
        exact Icc_mem_nhds (by linarith) (by linarith))
  have htend : Tendsto (fun t => ‖∫ r in z..t, Ψ r‖) (𝓝 z) (𝓝 0) := by
    have h := hprim_at.norm
    rw [ContinuousAt] at h
    simpa using h
  have hsymm : ∀ t : ℝ, t ≤ z → ‖∫ r in z..t, Ψ r‖ = ∫ r in t..z, Ψ r := by
    intro t ht
    rw [Real.norm_eq_abs, intervalIntegral.integral_symm t z, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg ht (fun r _ => hΨnn r))]
  -- ## The increment bound.
  have hbd_of : ∀ a b : ℝ, z / 2 ≤ a → a ≤ b → b ≤ 2 * z →
      |∫ r in a..b, M r| ≤ ∫ r in a..b, Ψ r := by
    intro a b ha hab hb
    have ha' : 0 < a := by linarith
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ ?_
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have hrpos : 0 < r := lt_trans ha' hr.1
      simp only [Real.norm_eq_abs, hMdef, hΨdef]
      exact hmom r hrpos
    · have hss : Set.uIcc a b ⊆ Set.Icc (z / 2) (2 * z) := by
        rw [Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc ha hb
      exact (hΨint.mono_set hss).intervalIntegrable
  -- ## The squeeze.
  have hev : ∀ᶠ s in 𝓝 z, ‖Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z‖
      ≤ ‖∫ r in z..s, Ψ r‖ := by
    filter_upwards [Icc_mem_nhds (by linarith : z / 2 < z) (by linarith : z < 2 * z)]
      with s hs
    have hs1 : 0 < s := by linarith [hs.1]
    have hs2 : s ≤ 2 * z := by linarith [hs.2]
    rcases lt_trichotomy z s with hzs | hzs | hsz
    · -- `z < s`
      have hch := hchain z s hz hzs
      have hIcc : (∫ r in Set.Icc z s, M r) = ∫ r in z..s, M r := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hzs.le]
      have hbd := hbd_of z s (by linarith) hzs.le hs2
      have hΨi : 0 ≤ ∫ r in z..s, Ψ r :=
        intervalIntegral.integral_nonneg hzs.le (fun r _ => hΨnn r)
      rw [hch, hIcc, Real.norm_eq_abs]
      calc |∫ r in z..s, M r| ≤ ∫ r in z..s, Ψ r := hbd
        _ = |∫ r in z..s, Ψ r| := by rw [abs_of_nonneg hΨi]
    · subst hzs
      simp
    · -- `s < z`
      have hch := hchain s z hs1 hsz
      have hIcc : (∫ r in Set.Icc s z, M r) = ∫ r in s..z, M r := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hsz.le]
      have hbd := hbd_of s z hs.1 hsz.le (by linarith [hs2])
      rw [norm_sub_rev]
      rw [hch, hIcc, Real.norm_eq_abs]
      calc |∫ r in s..z, M r| ≤ ∫ r in s..z, Ψ r := hbd
        _ = |∫ r in z..s, Ψ r| := by rw [← Real.norm_eq_abs, hsymm s hsz.le]
  have hnorm : Tendsto (fun s => ‖Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z‖)
      (𝓝 z) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) hev htend
  have hdiff : Tendsto (fun s => Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z)
      (𝓝 z) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcont : ContinuousAt (Work.Elliptic.Fstar f) z := by
    have h2 := hdiff.add_const (Work.Elliptic.Fstar f z)
    have h3 : (fun s => (Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z)
        + Work.Elliptic.Fstar f z) = Work.Elliptic.Fstar f := by
      funext s; ring
    rw [h3] at h2
    simpa [ContinuousAt] using h2
  exact hcont

/-- `L12dens K f z = ∫_θ K(θ) f z θ / z dθ` is continuous at every `z > 0` for `SmoothQuad f` with `HkMem α 4 f`.
Suggested route: `L12dens K f s = M s / s` with `M t = ∫_θ K θ * f t θ`. `s ↦ 1/s` is continuous at `z > 0`, so prove `ContinuousAt M z`:
for `θ ∈ (0,π/2)` the slice `t ↦ f t θ` is `C^∞` near `z` (`Work.FTS.LocData.SmoothQuad.curry_z` with `θ ∈ Ioo 0 (π/2)`), so
`f s θ - f z θ = ∫_{z}^{s} ∂_z f(σ,θ) dσ`; combine with Tonelli (both variables nonnegative) to get
`|M s - M z| ≤ C ∫_{z}^{s} √(B σ) dσ`, where `B σ = ∫_θ HkIntegrand α 4 f σ θ`. For that, use that for a.e. `θ`
`(f σ θ)^2 ≤ HkIntegrand α 4 f σ θ / (w σ)^2` (`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`), Cauchy–Schwarz in `θ`
against `K`, and `D_z f = σ ∂_z f`, which gives `∫_θ K θ |∂_z f(σ,θ)| dθ ≤ C √(B σ)`. Finally `√B ∈ L¹` locally near `z`:
`∫_{z-τ}^{z+τ} √B ≤ √(2τ ∫_{z-τ}^{z+τ} B)` (Cauchy–Schwarz) and `∫_{z-τ}^{z+τ} B → 0` since `B ∈ L¹(Ioi 0)` (`hmem.2`).
Also note `|∫_θ K θ f z θ| ≤ √(∫_θ K² sin^η) · √(∫_θ (f z θ)² sin^{-η}) < ∞` by `hmem.1`, so `M z` is a finite real number. -/
theorem l12dens_continuousAt (α : ℝ) {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen f := by
    have hsub : Work.FTS.EllipticEst.Q0 ⊆ Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2) := by
      intro p hp
      simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩
    exact hsm.mono hsub
  have hF : ContinuousAt (Work.Elliptic.Fstar f) z :=
    Fstar_continuousAt_of_aux α hz hSO
      (Work.FTS.CoercivityFix.Coer1T.Hardy.pzSqSeta_box_integrable α hsm hmem)
      (Work.FTS.CoercivityFix.Coer1T.Hardy.slice_sinCos2_integrable α hsm hmem)
      hmem.2
      (Work.FTS.CoercivityFix.Coer1T.Hardy.pzMoment_le_sqrt α hsm hmem)
  have hdiv : ContinuousAt (fun s : ℝ => 3 * Work.Elliptic.Fstar f s / s) z :=
    (hF.const_mul 3).div continuousAt_id (ne_of_gt hz)
  exact hdiv.congr (Filter.Eventually.of_forall fun s => (L12dens_eq_three_Fstar f s).symm)

end Work.FTS.CoercivityFix.Coer1T.HardyAlt
