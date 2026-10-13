/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L²`-integrability of the angular moment `F_*(Ψ)` for the data of `EllHyp`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021).

**Statement.**  For every `α : ℝ`, `k : ℕ` and data `(F,Ψ)` with `EllHyp α k F Ψ`,
the square of the angular moment

  `F_*(Ψ)(z) = ∫_0^{π/2} Ψ(z,θ) sinθ cos²θ dθ`

of the *solution* is integrable on `(0,∞)`.

**Proof.**  Two independent ingredients.

* *(Cauchy–Schwarz in `θ`)*  `Work.Elliptic.Fstar_sq_le` gives, for every `z` whose
  angular slice `θ ↦ Ψ(z,θ)²` is integrable,

    `F_*(Ψ)(z)² ≤ (π/2) ∫_θ Ψ(z,θ)² dθ`.

  The slice integrability is the second ingredient together with the honesty of the `ℋ^k`
  mass of `Ψ` (`EllHyp.memPsi`).

* *(domination by the `ℋ^k` integrand)*  On the open interval `θ ∈ (0,π/2)` the weight
  `sin(2θ)^{-η/2}` is `≥ 1` and the radial weight satisfies `w(z) ≥ 1` for `z > 0`, hence

    `Ψ(z,θ)² ≤ (Ψ(z,θ)·w(z))² ≤ HkIntegrand α k Ψ z θ`

  (`Work.Spaces.sq_le_HkIntegrand_z` for the `i = 0` summand of the `ℋ^k`-integrand).
  Therefore

    `∫_θ Ψ(z,θ)² dθ ≤ ∫_θ HkIntegrand α k Ψ z θ dθ`,

  and the right hand side is integrable in `z` on `[0,∞)` by `EllHyp.memPsi`.

The measurability of `z ↦ F_*(Ψ)(z)²` on `(0,∞)` comes from the smoothness of `Ψ` on a
neighbourhood of the closed quadrant: the joint integrand `(z,θ) ↦ Ψ(z,θ) sinθcos²θ` is
continuous on the open quadrant, hence a.e. strongly measurable, and integrating out `θ`
preserves a.e. strong measurability (`AEStronglyMeasurable.integral_prod_right'`).

Note that `EllHyp` is used only through `smooth` and `memPsi`; in particular the result is
uniform in `α` and `k`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.L12Aux

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The open quadrant and the neighbourhood of `SmoothNbhd` -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the smoothness of `Ψ` is used
(the analytic content of the estimates lives here; the two boundary lines
`θ = 0`, `θ = π/2` are null for `volume.restrict Iθ`). -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The open neighbourhood `(-1,∞) × (-1,π/2+1)` of the closed quadrant on which
`Work.Spaces.SmoothNbhd` is stated. -/
abbrev nbhQ : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)

/-- The open quadrant sits inside the neighbourhood of the smoothness class. -/
theorem Qd_subset_nbhQ : Qd ⊆ nbhQ :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))
    (Set.Ioo_subset_Ioo (by norm_num : (-1 : ℝ) ≤ 0)
      (by linarith [Real.pi_pos] : π / 2 ≤ π / 2 + 1))

/-- The open interval `(0,π/2)` and the closed interval `Iθ` carry the same restriction of
Lebesgue measure, since they differ by the two null points `0` and `π/2`. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-! ## Domination of the unweighted square by the `ℋ^k`-integrand -/

/-- The radial weight is at least `1` on `(0,∞)`. -/
theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- Multiplying by the radial weight does not decrease a square: `g² ≤ (g·w)²` for `z > 0`. -/
theorem sq_le_sq_mul_w {g : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    (g z θ) ^ 2 ≤ (g z θ * Work.Spaces.w z) ^ 2 := by
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by
    have := one_le_w_of_pos hz; nlinarith
  calc (g z θ) ^ 2 = (g z θ) ^ 2 * 1 := by ring
    _ ≤ (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
    _ = (g z θ * Work.Spaces.w z) ^ 2 := by ring

/-- **The pointwise domination.**  For `θ` in the *open* interval, where `sin(2θ) ∈ (0,1]`,
the square `(g·w)²` is bounded by the `ℋ^k`-integrand: the latter contains the `i = 0`
summand `(g·w·sin(2θ)^{-η/2})²` (`Work.Spaces.sq_le_HkIntegrand_z`), which is `(g·w)²`
divided by a factor `≤ 1`. -/
theorem sq_mul_w_le_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (g z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
          Real.rpow_le_rpow hs0.le hs1
            (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
      _ = 1 := Real.one_rpow _
  -- dividing by a number in `(0,1]` does not decrease a square
  have hstep : (g z θ * Work.Spaces.w z) ^ 2
      ≤ (g z θ * Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    calc (g z θ * Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        ≤ (g z θ * Work.Spaces.w z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (g z θ * Work.Spaces.w z) ^ 2 := by ring
  have hstep2 : (g z θ * Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    ring
  rw [hstep2] at hstep
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ 0 (Nat.zero_le k))

/-- The same domination, in the a.e. form on `Iθ` (the two endpoints are null). -/
theorem ae_sq_mul_w_le_HkIntegrand (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g z θ * Work.Spaces.w z) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  exact sq_mul_w_le_HkIntegrand hθ

/-- **The square of an `ℋ^k`-function is integrable on every angular slice.**  This is the
double use of `EllHyp.memPsi`: the `ℋ^k`-integrand of `Ψ` is integrable on the slice and
dominates `Ψ(z,θ)²` a.e., while the slice itself is measurable by smoothness. -/
theorem integrableOn_slice_sq {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α k g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  refine Integrable.mono' (hmem.1 z hzIz) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2) Qd :=
      (hsm.continuousOn.mono Qd_subset_nbhQ).pow 2
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2)
      hcont hz
  · rw [← restrict_Ioo_eq_restrict_Iθ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_trans (sq_le_sq_mul_w hz θ) (sq_mul_w_le_HkIntegrand hθ)

/-- The angular integral of `g²` is dominated by that of the `ℋ^k`-integrand. -/
theorem integral_slice_sq_le_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hzIz) ?_
  rw [← restrict_Ioo_eq_restrict_Iθ]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  exact le_trans (sq_le_sq_mul_w hz θ) (sq_mul_w_le_HkIntegrand hθ)


/-- The open-quadrant regularity of `SmoothInt` (the re-scoped `EllHyp.smooth` field): this is
what the two `_of_smoothNbhd` lemmas below really used. -/
theorem continuousOn_of_smoothInt_Qd {g : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothInt g) :
    ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Qd := by
  have hsub : Qd ⊆ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro q hq
    have hq' : q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := hq
    have h1 : (0 : ℝ) < q.1 := (Set.mem_prod.mp hq').1
    have h2 : q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := (Set.mem_prod.mp hq').2
    exact Set.mem_prod.mpr ⟨show (-1 : ℝ) < q.1 from by linarith, h2⟩
  exact h.1.continuousOn.mono hsub

/-- **The `SmoothInt` companion of `integrableOn_slice_sq`.** -/
theorem integrableOn_slice_sq_of_smoothInt {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt g) (hmem : Work.Spaces.HkMem α k g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  refine Integrable.mono' (hmem.1 z hzIz) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2) Qd :=
      (continuousOn_of_smoothInt_Qd hsm).pow 2
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2)
      hcont hz
  · rw [← restrict_Ioo_eq_restrict_Iθ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_trans (sq_le_sq_mul_w hz θ) (sq_mul_w_le_HkIntegrand hθ)

/-- **The `SmoothInt` companion of `aesm_Fstar_of_smoothNbhd`.** -/
theorem aesm_Fstar_of_smoothInt (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothInt Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Fstar Ψ z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) Qd :=
    ((Real.continuous_sin.comp continuous_snd).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) Qd :=
    (continuousOn_of_smoothInt_Qd hsm).mul hsin
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) hcont).integral_prod_right'
  simpa only [Work.Elliptic.Fstar] using h

/-! ## A.e. strong measurability of the angular moment -/

/-- `θ ↦ sinθ cos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- **A.e. strong measurability of `F_*(Ψ)`.**  The joint integrand
`(z,θ) ↦ Ψ(z,θ)·sinθcos²θ` is continuous on the open quadrant (smoothness of `Ψ`), hence
a.e. strongly measurable for the product measure, and
`AEStronglyMeasurable.integral_prod_right'` gives the measurability of its `θ`-integral. -/
theorem aesm_Fstar_of_smoothNbhd (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Fstar Ψ z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) Qd :=
    (hsm.continuousOn.mono Qd_subset_nbhQ).mul
      (continuous_sinCos2.comp_continuousOn
        (continuous_snd : Continuous fun p : ℝ × ℝ => p.2).continuousOn)
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) hcont).integral_prod_right'
  simpa only [Work.Elliptic.Fstar] using h

/-! ## The main statement -/

theorem Fstar_L2_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar Ψ z) ^ 2) (Set.Ioi 0) := by
  have hsm : Work.Spaces.SmoothInt Ψ := h.smooth
  have hmem : Work.Spaces.HkMem α k Ψ := h.memPsi
  -- the restrictions of Lebesgue measure to `(0,∞)` and to `Iz = [0,∞)` agree
  have hrestrict : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
  -- measurability of the integrand
  have hAESM : AEStronglyMeasurable (fun z : ℝ => (Work.Elliptic.Fstar Ψ z) ^ 2)
      (volume.restrict (Set.Ioi 0)) := by
    rw [hrestrict]
    exact (aesm_Fstar_of_smoothInt Ψ hsm).pow 2
  -- the dominating function is integrable
  have hgInt : Integrable (fun z : ℝ => (π / 2) * ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k Ψ z θ) (volume.restrict (Set.Ioi 0)) := by
    rw [hrestrict]
    exact hmem.2.const_mul (π / 2)
  refine Integrable.mono' hgInt hAESM ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  have hf1 : (Work.Elliptic.Fstar Ψ z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
    Work.Elliptic.Fstar_sq_le Ψ z (integrableOn_slice_sq_of_smoothInt hsm hmem hz)
  have hf2 : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ :=
    integral_slice_sq_le_HkIntegrand hmem hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact le_trans hf1 (mul_le_mul_of_nonneg_left hf2 (by positivity))

end Work.FTS.EllipticEst.Cert.L12Aux
