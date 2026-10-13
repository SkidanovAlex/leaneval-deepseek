/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L₁₂dens g ∈ L¹((0,∞))` from `SmoothQuad` and `ℋ⁴` alone

This module proves `Work.FTS.H2.L12densIntegrable`: the `L₁₂`-density
`L12dens g s = ∫_{Iθ} K(θ)·g(s,θ)/s dθ` of a datum which is `C^∞` on the open quadrant
(`Work.FTS.LocData.SmoothQuad`, *not* the analytic class `Work.Spaces.SmoothNbhd` — see the
remark in `Work.FTS.LocData.Defs`) and belongs to `ℋ⁴` (`Work.Spaces.HkMem α 4 g`) is
integrable on `(0,∞)`.

This is the `SmoothQuad`-analogue of `Work.Elliptic.L12densFacts` /
`Work.Coercivity.L12dens_integrableOn`, whose proofs use the analyticity of the datum
(`SmoothNbhd`) twice: for the continuity of the density and for the continuity of the
angular slices on the *closed* quadrant.  Neither is available for the localised data of
the route (a cut-off is never analytic), so the argument is redone with the two
ingredients that survive:

* the angular slice `θ ↦ g s θ` is continuous on the **open** interval `(0,π/2)`, hence
  a.e. strongly measurable for `volume.restrict Iθ` (the endpoints are null) —
  `Work.Spaces.aesm_slice_of_continuousOn_Qd`;
* the *joint* integrand `(s,θ) ↦ K(θ)·g(s,θ)/s` is continuous on the open quadrant, so
  Fubini measurability of the slice integral (`Work.Spaces.aesm_of_continuousOn_Qd` +
  `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) gives the a.e. strong
  measurability of `L12dens g` on `Iz = [0,∞)`, hence on `(0,∞)`.

The estimate itself is the one of the docstring of the theorem:

* Cauchy–Schwarz in `θ` against `Ktheta ∈ L²` (`Work.Spaces.cs_integral`) and the
  pointwise domination `(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²` on the open quadrant
  (the `D_z⁰`-term of `HkIntegrand`, `Work.Spaces.sq_le_HkIntegrand_z`, together with
  `sin(2θ)^{η/2} ≤ 1` and `w ≥ 1`), giving
  `|L12dens g s| ≤ √(∫K²)·(s/(1+s)²)·√(∫_θ HkIntegrand α 4 g s θ)` for `s > 0`;
* AM–GM `2√H ≤ 1 + H` to dominate `L12dens g` by an integrable function: the two
  integrable pieces are `(s/(1+s)²)² ∈ L¹((0,∞))` (`Work.Elliptic.psi_sq_integrable_aux`,
  transferred to `Iz` by `Work.Elliptic.restrict_Ioi_eq_restrict_Iz`) and
  `s ↦ ∫_θ HkIntegrand α 4 g s θ` (the second component of `Work.Spaces.HkMem`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
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

namespace Work.FTS.H2

set_option linter.unusedVariables false

/-- `SmoothQuad` gives continuity of the uncurried datum on the open quadrant `Qd`. -/
private lemma continuousOn_uncurry_Qd {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (Function.uncurry g) Qd := by
  have h := hsm
  rw [Work.FTS.LocData.SmoothQuad] at h
  exact h.continuousOn.mono (fun p hp => by
    simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩)

/-! ## Pointwise domination of `g²` by the `ℋ⁴`-integrand

The `D_z⁰`-term of `HkIntegrand α 4 g` carries the weight `w/sin(2θ)^{η/2}`; since
`sin(2θ)^{η/2} ≤ 1` and `w ≥ 1` on the quadrant, this term dominates `g² w²`, hence
`g²` is dominated by `HkIntegrand/(w s)²`.  The radial weight `w s = (1+s)²/s²` is exactly
what absorbs the `1/s` of the density in the Cauchy–Schwarz step. -/

/-- On the open quadrant, `(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²`. -/
private lemma g_sq_le_HkIntegrand_div_w_sq (α : ℝ) (g : ℝ → ℝ → ℝ) {s θ : ℝ} (hs : 0 < s)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
  have hSsq : S ^ 2 ≤ 1 := by
    have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul hsin.le]; norm_num
    calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
      _ ≤ 1 := Real.rpow_le_one hsin.le (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  have hkey : (g s θ * (Work.Spaces.w s / S)) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    simpa only [Work.Spaces.DzIter_zero] using
      Work.Spaces.sq_le_HkIntegrand_z α 4 g s θ 0 (by norm_num)
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hstep : (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ := by
    calc (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ (g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 / S ^ 2 := by
          rw [le_div_iff₀ (pow_pos hSpos 2)]
          nlinarith [mul_nonneg (sq_nonneg (g s θ)) (sq_nonneg (Work.Spaces.w s)), hSsq]
      _ = (g s θ * (Work.Spaces.w s / S)) ^ 2 := by
          rw [mul_pow, div_pow, mul_div_assoc]
      _ ≤ _ := hkey
  exact (le_div_iff₀ (pow_pos hwpos 2)).mpr hstep

/-! ## The pointwise bound on the density -/

/-- **The pointwise bound on the `L₁₂`-density.**  For `g` smooth on the open quadrant and
`g ∈ ℋ⁴`, and for `s > 0`,

`|L12dens g s| ≤ (√(∫_θ K(θ)² dθ) + 1)·(s/(1+s)²)·√(∫_θ HkIntegrand α 4 g s θ)`.

The angular integral is bounded by Cauchy–Schwarz in `θ` (`Work.Spaces.cs_integral`)
against `Ktheta ∈ L²` and the slice `L²`-norm `√(∫_θ (g s θ)²)`, which in turn is dominated
by `√(∫_θ HkIntegrand α 4 g s θ)/w s` through the pointwise domination above; the factor
`(1/(s·w s)) = s/(1+s)²` is the sublinear weight at the origin that makes the density
integrable there. -/
private lemma L12dens_abs_le_quad (α : ℝ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ}
    (hs : 0 < s) :
    |Work.Elliptic.L12dens g s|
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
  have hcontg : ContinuousOn (Function.uncurry g) Qd := continuousOn_uncurry_Qd hsm
  have haesm : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcontg hs
  have hwpos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hw1 : 1 ≤ Work.Spaces.w s := Work.Elliptic.one_le_w hs
  have hpk : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g s θ / (Work.Spaces.w s) ^ 2 :=
    Work.Elliptic.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => g_sq_le_HkIntegrand_div_w_sq α g hs h0 h1)
  -- the θ-slice of `g²` is integrable on `Iθ`, dominated by the `ℋ⁴`-integrand
  have hSqInt : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 s hs.le) (haesm.pow 2) ?_
    filter_upwards [hpk] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine le_trans hθ ?_
    rw [div_le_iff₀ (pow_pos hwpos 2)]
    calc Work.Spaces.HkIntegrand α 4 g s θ
        = Work.Spaces.HkIntegrand α 4 g s θ * 1 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g s θ * (Work.Spaces.w s) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hw1]) (Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hKmem : MemLp (fun θ => Work.Elliptic.Ktheta θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      Work.Elliptic.continuous_ktheta.aestronglyMeasurable).mpr
      ((Work.Elliptic.continuous_ktheta.continuousOn.pow 2).integrableOn_compact isCompact_Icc)
  have hGmem : MemLp (fun θ => g s θ) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm).mpr hSqInt
  have hcs := Work.Spaces.cs_integral hKmem hGmem
  have hA : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hH : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
    integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
  have hintle : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) / (Work.Spaces.w s) ^ 2 := by
    have h := MeasureTheory.integral_mono_ae hSqInt ((hmem.1 s hs.le).div_const _) hpk
    rwa [MeasureTheory.integral_div] at h
  -- Cauchy–Schwarz in the angle, then the slice `L²`-bound
  have hab : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s) := by
    have h1 : |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
      calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ|
          = Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) := Real.sqrt_le_sqrt hcs
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := Real.sqrt_mul hA _
    have h2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s := by
      calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
          ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / (Work.Spaces.w s) ^ 2) := Real.sqrt_le_sqrt hintle
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Real.sqrt ((Work.Spaces.w s) ^ 2) := Real.sqrt_div hH _
        _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
              / Work.Spaces.w s := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
  have key : (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    rw [Work.Spaces.w]; field_simp; try ring
  rw [Work.Elliptic.L12dens_eq_angMoment_div, Work.Elliptic.angMoment, abs_div, abs_of_pos hs]
  calc |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * g s θ| / s
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          / Work.Spaces.w s)) / s := by
        rw [div_le_div_iff_of_pos_right hs]; exact hab
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := key
    _ ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-! ## A.e. strong measurability of the density

The joint integrand `(s,θ) ↦ K(θ)·g(s,θ)/s` is continuous on the open quadrant, hence a.e.
strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`); Fubini measurability of the partial integral
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
measurability of `s ↦ ∫_θ K(θ)·g(s,θ)/s = L12dens g s` for `volume.restrict Iz`. -/

/-- `L12dens g` is a.e. strongly measurable on `Iz = [0,∞)` for `SmoothQuad` data. -/
private lemma L12dens_aesm (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (Work.Elliptic.L12dens g) (volume.restrict Work.Spaces.Iz) := by
  have hcontg : ContinuousOn (Function.uncurry g) Qd := continuousOn_uncurry_Qd hsm
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Qd :=
    Work.Elliptic.continuous_ktheta.comp_continuousOn continuous_snd.continuousOn
  have hF : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) Qd :=
    (h1.mul hcontg).div continuousOn_fst (fun p hp => ne_of_gt hp.1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * g p.1 p.2 / p.1) hF
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  convert h using 1
  funext z
  rfl

/-! ## The main theorem -/

/-- `L12dens g ∈ L¹((0,∞))` from `SmoothQuad g` and `HkMem α 4 g` alone (no analyticity, no
`SmoothNbhd`).  Route: `|L12dens g s| ≤ sqrt(∫_θ Ktheta²)·(1/w s)·sqrt(∫_θ HkIntegrand α 4 g s θ)`
for `s > 0` (Cauchy–Schwarz in `θ` against `Ktheta ∈ L²`, together with
`(g s θ)² ≤ HkIntegrand α 4 g s θ / (w s)²` for a.e. `θ`, which is
`Work.Spaces.sq_le_HkIntegrand_z` combined with `sin(2θ)^{η/2} ≤ 1` and `w ≥ 1`);
then Cauchy–Schwarz in `s` against `(1/w s)/s = s/(1+s)² ∈ L²((0,∞))`
(`Work.Elliptic.psi_sq_integrable_aux`, in `Submission/Work/Elliptic/L12densFacts.lean`) and
`∫_s ∫_θ HkIntegrand α 4 g = HkSq α 4 g` (that is the definition of `HkSq`; no integrability of
the product measure is needed: the inner `θ`-integral is finite for every `s ∈ Iz` by `hmem.1`
and the pointwise domination, and `hmem.2` gives the outer integral). -/
theorem L12densIntegrable (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
  set C : ℝ := Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have haesm := L12dens_aesm g hsm
  -- AM–GM domination of the density by an integrable function, a.e. on `Iz`
  have hbd : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz),
      ‖Work.Elliptic.L12dens g s‖ ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with s hs
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hpos
    · -- at `s = 0` both sides are `0` (the density is divided by `0`, hence vanishes)
      subst h0
      have hz : Work.Elliptic.L12dens g 0 = 0 := by
        rw [Work.Elliptic.L12dens]; simp
      rw [hz, norm_zero]
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g 0 θ :=
        integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
      refine mul_nonneg (by linarith [hCpos]) ?_
      have h0' : ((0 : ℝ) / (1 + 0) ^ 2) ^ 2 = 0 := by norm_num
      rw [h0', zero_add]
      exact hX
    · have h1 := L12dens_abs_le_quad α g hsm hmem hpos
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
        integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ)
      have hAM : C * (s / (1 + s) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
            + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
        nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
            - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)),
          Real.sq_sqrt hX]
      rw [Real.norm_eq_abs, hCdef]
      exact le_trans h1 hAM
  -- the dominating function is integrable on `Iz`
  have hH_int : IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
      Work.Spaces.Iz := hmem.2
  have hpsi : IntegrableOn (fun s => (s / (1 + s) ^ 2) ^ 2) Work.Spaces.Iz := by
    change MeasureTheory.Integrable (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz)
    rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
    exact Work.Elliptic.psi_sq_integrable_aux
  have hdom : IntegrableOn (fun s => (C / 2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)) Work.Spaces.Iz :=
    (hpsi.add hH_int).const_mul (C / 2)
  have hIntIz : IntegrableOn (Work.Elliptic.L12dens g) Work.Spaces.Iz := hdom.mono' haesm hbd
  exact hIntIz.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.H2
