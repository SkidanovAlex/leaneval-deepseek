import ChallengeDeps
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Submission.RadialTransfer
import Submission.ScatChosen
import Submission.ShellPot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Canonical scattering profile from the shell formula (Layer 3)

With the Newton-potential representation (`NewtonRep.scattering_newton_representation`:
for a radial weak scattering solution `w` of a radial `v` with
`tsupport v ⊆ ball 0 R`, `w = (8π)⁻¹∫v(1−w)(y)/‖·−y‖ dy` a.e.) and the shell
formula (`ShellPot.newton_potential_shell_split`: for radial `g`,
`∫_y g(y)/‖x−y‖ dy = 4π[(1/‖x‖)∫_{s<‖x‖} s²gprof(s)ds + ∫_{s>‖x‖} s·gprof(s)ds]`),
the radial profile `u(r) := r·radialProfile w r` has the explicit form

    u(r) = (1/2)·[ ∫_{0<s<r} s²·gprof(s) ds  +  r·∫_{s>r} s·gprof(s) ds ]
         =: canonicalProfile v w R r                       (g := v(1−w))

for almost every `r > 0`.  This module proves that explicit form and its
consequences — in particular the long-missing *origin datum* of the
maximum-principle programme:

    u(r) → 0  as  r → 0⁺                       (canonicalProfile_tendsto_zero)

(`|u(r)| ≤ (1/2)[∫_0^r s²|gprof|ds + r·∫_r^R s·|gprof|ds] → 0` by dominated
convergence and the splitting `r·∫_r^R (s²|gprof|)/s ≤ ∫_r^{√r}s²|gprof| +
√r·∫s²|gprof|`), the exterior constancy `canonicalProfile v w R r = c` for
`r ≥ R` (with `c = (8π)⁻¹∫v(1−w)`, the exterior constant of `w`), and the
right-endpoint data `HasDerivAt (canonicalProfile v w R) 0 R`
(`deriv u r = (1/2)∫_{s>r} s·gprof(s)ds` for `r < R`, which vanishes at `r=R`).

Everything is stated for an *arbitrary* radial scattering solution `w` of a
radial `v` (so it applies directly to the chosen `w₀` of the `a v ≠ 0`
branch, where additionally `∫v(1−w₀) = 8π·a v` by
`ScatChosen.chosen_scattering_integral`, making the exterior value `a v`).

## Route for `canonicalProfile_eq_profile`
1. `g := v·(1−w)` is integrable (`ScatG.scatG_integrable`), radial
   (`hvrad`,`hrad`), supported in `{‖y‖ ≥ R → g y = 0}` (`PotSupport`-style
   argument), so `gprof := radialProfile g` satisfies
   `s·|gprof s|` integrable on `(r,∞)` for `r>0` and
   `s²·|gprof s|` integrable on `(0,∞)` (radial-integral identity
   `RadialIntegral`: `∫|g| = 4π∫s²|gprof|`).
2. `NewtonRep` gives `w x = (8π)⁻¹∫g(y)/‖x−y‖ dy` for a.e. `x`; both sides
   are radial (`newtonPotential_IsRadial` for the right side), so by the
   measure-transfer lemma for radial functions the identity holds at
   `x = r·radU0` for almost every `r > 0` (the set of bad radii pulls back
   under the norm to a null set, cf. `AERadial.ae_eq_div_norm_of_radial_profile_ae`
   and `volume_preimage_norm_null` in `ScatProfileExterior`).
3. Apply `ShellPot.newton_potential_shell_split` at `x = r·radU0`
   (`‖r·radU0‖ = r` by `RadialRep.norm_smul_radU0`), multiply by `r` and by
   `1/(8π)`, and use `radialProfile w r = w (r·radU0)` (definition).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The canonical scattering profile with `g := v·(1−w)`:
`u(r) := (1/2)·[∫_{0<s<r} s²·gprof(s) ds + r·∫_{s>r} s·gprof(s) ds]` where
`gprof := radialProfile (v·(1−w))`.  For the chosen scattering solution of the
`a v ≠ 0` branch this is (a.e. in `r`) the profile `r·radialProfile w r`. -/
noncomputable def canonicalProfile (v w : ℝ³ → ℝ) (R r : ℝ) : ℝ :=
  (1 / 2) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * radialProfile (fun x => v x * (1 - w x)) s) +
    r * (∫ s in Set.Ioi r, s * radialProfile (fun x => v x * (1 - w x)) s))

/-- **Explicit profile.**  For a radial scattering solution `w` of a radial
`v` (`tsupport v ⊆ ball 0 R`), for almost every `r > 0`,
`canonicalProfile v w R r = r·radialProfile w r`. -/
theorem canonicalProfile_eq_profile {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (∀ᵐ r : ℝ, 0 < r → canonicalProfile v w R r = r * radialProfile w r) := by
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  let A : ℝ → ℝ := fun r => ∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s
  let B : ℝ → ℝ := fun r => ∫ s in Set.Ioi r, s * gprof s
  let NP : ℝ³ → ℝ := fun x => (1 / (8 * π)) * (∫ y : ℝ³, g y * (‖x - y‖ : ℝ)⁻¹)
  have hg : MeasureTheory.Integrable g := by
    simpa [g] using (scatG_integrable (v := v) (w := w) hv_supp hw)
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have hv0 : v y = 0 := v_eq_zero_of_norm_ge hv_supp hy
    dsimp [g]
    simp [hv0]
  have hcan (r : ℝ) : canonicalProfile v w R r = (1 / 2) * (A r + r * B r) := by
    dsimp [canonicalProfile, A, B, gprof, g]
  have hnew : ∀ᵐ x : ℝ³, w x = NP x := by
    have h := scattering_newton_representation (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
    simpa [NP, g] using h
  have hNP (x : ℝ³) (hx : x ≠ 0) :
      NP x = (1 / 2) * ((1 / ‖x‖) * A ‖x‖ + B ‖x‖) := by
    have hsplit := newton_potential_shell_split (g := g) (R := R) hR hgrad hgsupp hg x hx
    dsimp [NP, A, B, gprof] at hsplit ⊢
    rw [hsplit]
    field_simp
    ring
  have hmain (x : ℝ³) (hx : x ≠ 0) : canonicalProfile v w R ‖x‖ = ‖x‖ * NP x := by
    have hnrm : ‖x‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hx)
    rw [hcan ‖x‖, hNP x hx]
    field_simp
  have hzero : canonicalProfile v w R 0 = 0 * radialProfile w 0 := by
    dsimp [canonicalProfile]
    simp
  have h3d : ∀ᵐ x : ℝ³, canonicalProfile v w R ‖x‖ = ‖x‖ * radialProfile w ‖x‖ := by
    filter_upwards [hnew] with x hx
    by_cases hx0 : x = 0
    · subst x
      simpa using hzero
    · have hc := hmain x hx0
      rw [← hx] at hc
      have hwprof : w x = radialProfile w ‖x‖ := radial_eq_profile hrad x
      rw [hwprof] at hc
      exact hc
  let p : ℝ → ℝ := fun r => canonicalProfile v w R r - r * radialProfile w r
  have hbad : (volume : Measure ℝ³) {x : ℝ³ | p ‖x‖ ≠ 0} = 0 := by
    rw [MeasureTheory.ae_iff] at h3d
    let E : Set ℝ³ := {x : ℝ³ | ¬(canonicalProfile v w R ‖x‖ = ‖x‖ * radialProfile w ‖x‖)}
    have hEeq : E = {x : ℝ³ | p ‖x‖ ≠ 0} := by
      ext x
      simp [E, p, sub_eq_zero]
    have hEvol : (volume : Measure ℝ³) E = 0 := h3d
    rwa [← hEeq]
  have hpre : {x : ℝ³ | ‖x‖ ∈ {r : ℝ | p r ≠ 0}} = {x : ℝ³ | p ‖x‖ ≠ 0} := by
    ext x
    simp
  have hprevol : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ {r : ℝ | p r ≠ 0}} = 0 := by
    rwa [hpre]
  have hS : (volume : Measure ℝ) {r : ℝ | 0 < r ∧ p r ≠ 0} = 0 := by
    have htrans := null_of_norm_preimage_null (S := {r : ℝ | p r ≠ 0}) hprevol
    have hset : {r : ℝ | 0 < r ∧ p r ≠ 0} = {r : ℝ | p r ≠ 0} ∩ Set.Ioi (0 : ℝ) := by
      ext r
      simp [and_comm]
    rwa [hset]
  rw [MeasureTheory.ae_iff]
  have hTeq : {r : ℝ | ¬(0 < r → canonicalProfile v w R r = r * radialProfile w r)}
      = {r : ℝ | 0 < r ∧ p r ≠ 0} := by
    ext r
    simp [p, sub_eq_zero]
  rwa [hTeq]

/-- **Origin datum.**  The canonical profile tends to zero as `r → 0⁺`
(unconditionally — no sign of `v(1−w)` needed). -/
theorem canonicalProfile_tendsto_zero {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    Tendsto (canonicalProfile v w R) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- `g := v·(1−w)` is integrable, radial, and (its profile) vanishes for
  -- `s ≥ R`; writing `h(s) := s²·|gprof s|`, the integrability of `g` gives
  -- `h` integrable on `(0,∞)` (`shell_profile_integrable`), and both summands
  -- of the canonical profile are dominated-convergence integrals:
  --   `∫_{0<s≤r} s²·gprof s → 0` and `∫_{s>r} r·s·gprof s → 0` as `r → 0⁺`,
  -- the second because for each fixed `s > 0` the factor `r` drives it to 0
  -- (the integrand is dominated by the integrable `s²·|gprof s|` since
  -- `r·s ≤ s²` on `{s > r}`).
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hg : MeasureTheory.Integrable g := by
    simpa [g] using (scatG_integrable (v := v) (w := w) hv_supp hw)
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hprof : Integrable (fun s : ℝ => s ^ 2 * |gprof s|) μ := by
    dsimp [μ]
    exact (shell_profile_integrable (g := g) hg hgrad)
  have hgprofAE : AEStronglyMeasurable gprof μ := by
    simpa [gprof, μ] using shell_gprof_ae_strong (g := g) hg hgrad
  have hs2gprofAE : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * gprof s) μ := by
    have hsq : AEStronglyMeasurable (fun s : ℝ => s ^ 2) μ :=
      (by fun_prop : Measurable (fun s : ℝ => s ^ 2)).aestronglyMeasurable
    exact hsq.mul hgprofAE
  -- family for the first term
  let F1 : ℝ → ℝ → ℝ := fun r => (Set.Ioc (0 : ℝ) r).indicator (fun s : ℝ => s ^ 2 * gprof s)
  have hF1int (r : ℝ) : (∫ s : ℝ, F1 r s ∂μ) =
      ∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s := by
    dsimp [F1, μ]
    rw [integral_indicator (hs := measurableSet_Ioc)]
    simp only [Measure.restrict_restrict (measurableSet_Ioc)]
    congr 1
    ext s
    simp
  have tF1 : Tendsto (fun r : ℝ => ∫ s : ℝ, F1 r s ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => ∫ s : ℝ, F1 r s ∂μ) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ s : ℝ, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (ι := ℝ) (l := 𝓝[>] (0 : ℝ))
        (μ := μ) (F := F1) (f := fun _ : ℝ => (0 : ℝ)) (bound := fun s : ℝ => s ^ 2 * |gprof s|) ?_ ?_ ?_ ?_
      · filter_upwards [] with r
        exact (aestronglyMeasurable_indicator_iff (s := Set.Ioc (0:ℝ) r) (measurableSet_Ioc)).2 hs2gprofAE.restrict
      · filter_upwards [] with r
        refine ae_of_all _ ?_
        intro s
        dsimp [F1]
        by_cases hs : s ∈ Set.Ioc (0 : ℝ) r
        · simp [hs]
        · simp [hs]
          positivity
      · exact hprof
      · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
        intro s hs
        have hspos : 0 < s := by simpa using hs
        have hlim : Tendsto (fun r : ℝ => F1 r s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hev : (fun r : ℝ => F1 r s) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (0 : ℝ)) := by
            have hmem : {r : ℝ | r < s} ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hspos)
            filter_upwards [hmem] with r hr
            dsimp [F1]
            have hns : s ∉ Set.Ioc (0 : ℝ) r := by
              intro hmemIoc
              exact (not_le_of_gt hr) hmemIoc.2
            simp [hns]
          exact (tendsto_congr' hev).2 tendsto_const_nhds
        exact hlim
    simpa using ht
  have tA : Tendsto (fun r : ℝ => ∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply Tendsto.congr'
    · filter_upwards [] with r
      exact hF1int r
    · exact tF1
  -- family for the second term
  let F2 : ℝ → ℝ → ℝ := fun r => (Set.Ioi r).indicator (fun s : ℝ => r * (s * gprof s))
  have hF2int (r : ℝ) (hr : 0 < r) : (∫ s : ℝ, F2 r s ∂μ) =
      r * (∫ s in Set.Ioi r, s * gprof s) := by
    dsimp [F2, μ]
    rw [integral_indicator (hs := measurableSet_Ioi)]
    simp only [Measure.restrict_restrict (measurableSet_Ioi)]
    have hset : Set.Ioi r ∩ Set.Ioi (0 : ℝ) = Set.Ioi r := by
      ext s
      constructor
      · intro hs; exact hs.1
      · intro hs; exact ⟨hs, lt_trans hr hs⟩
    rw [hset]
    rw [← integral_const_mul r (fun s : ℝ => s * gprof s)]
  have tF2 : Tendsto (fun r : ℝ => ∫ s : ℝ, F2 r s ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun r : ℝ => ∫ s : ℝ, F2 r s ∂μ) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ s : ℝ, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (ι := ℝ) (l := 𝓝[>] (0 : ℝ))
        (μ := μ) (F := F2) (f := fun _ : ℝ => (0 : ℝ)) (bound := fun s : ℝ => s ^ 2 * |gprof s|) ?_ ?_ ?_ ?_
      · filter_upwards [] with r
        apply (aestronglyMeasurable_indicator_iff (s := Set.Ioi r) (measurableSet_Ioi)).2
        have hgAE : AEStronglyMeasurable gprof (μ.restrict (Set.Ioi r)) := hgprofAE.restrict
        have hsAE : AEStronglyMeasurable (fun s : ℝ => s) (μ.restrict (Set.Ioi r)) :=
          (measurable_id : Measurable (fun s : ℝ => s)).aestronglyMeasurable
        have hsprod : AEStronglyMeasurable (fun s : ℝ => s * gprof s) (μ.restrict (Set.Ioi r)) :=
          hsAE.mul hgAE
        exact hsprod.const_mul r
      · filter_upwards [(self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with r hr
        have hrpos : 0 < r := by simpa using hr
        refine ae_of_all _ ?_
        intro s
        dsimp [F2]
        by_cases hsI : s ∈ Set.Ioi r
        · have hrs : r < s := by simpa using hsI
          have hsgt : 0 < s := lt_trans hrpos hrs
          simp [hsI]
          rw [abs_of_pos hrpos, abs_of_pos hsgt, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg (gprof s))
        · simp [hsI]
          positivity
      · exact hprof
      · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
        intro s hs
        have hspos : 0 < s := by simpa using hs
        have hlim : Tendsto (fun r : ℝ => F2 r s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have htmp : Tendsto (fun r : ℝ => r * (s * gprof s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
            have ht0 : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
              tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
            simpa using ht0.mul tendsto_const_nhds
          have hev : (fun r : ℝ => F2 r s) =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => r * (s * gprof s)) := by
            have hmem : {r : ℝ | r < s} ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hspos)
            filter_upwards [hmem] with r hr
            dsimp [F2]
            have hsI : s ∈ Set.Ioi r := hr
            simp [hsI]
          exact (tendsto_congr' hev).2 htmp
        exact hlim
    simpa using ht
  have tRB : Tendsto (fun r : ℝ => r * (∫ s in Set.Ioi r, s * gprof s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply Tendsto.congr'
    · filter_upwards [(self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with r hr
      exact hF2int r (by simpa using hr)
    · exact tF2
  have hcan (r : ℝ) : canonicalProfile v w R r =
      (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) +
        r * (∫ s in Set.Ioi r, s * gprof s)) := by
    dsimp [canonicalProfile, gprof, g]
  have tsum : Tendsto (fun r : ℝ => (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) +
      r * (∫ s in Set.Ioi r, s * gprof s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tA.add tRB
  have hmain : Tendsto (fun r : ℝ => (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) +
      r * (∫ s in Set.Ioi r, s * gprof s))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tsum.const_mul ((1 : ℝ) / 2)
  apply Tendsto.congr'
  · filter_upwards [] with r
    exact hcan r
  · exact hmain

/-- **Exterior constancy.**  If `w x = c/‖x‖` a.e. for `‖x‖ ≥ R` (the exterior
form, e.g. `ScatExterior.scattering_solution_exterior_form`), then
`canonicalProfile v w R r = c` for all `r ≥ R`. -/
theorem canonicalProfile_const_beyond {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) {c : ℝ}
    (hform : ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w x = c / ‖x‖) :
    ∀ r : ℝ, R ≤ r → canonicalProfile v w R r = c := by
  -- For `r ≥ R` the profile is *constant*: the second integral of
  -- `canonicalProfile` (`r·∫_{s>r} s·gprof`) vanishes because `gprof s = 0`
  -- for `s ≥ R`, and the first (`∫_{0<s≤r} s²·gprof`) agrees with its value
  -- at `r = R` since `gprof` is supported in `{s < R}`.  Writing `K` for that
  -- common value, the exterior form `w x = c/‖x‖` (a.e. on `‖x‖ ≥ R`) and the
  -- a.e. profile identity `u(r) = r·(radialProfile w r)` identify `K = c`:
  -- `u‖x‖ = K` and `u‖x‖ = ‖x‖·w x = c` for almost every exterior `x`.
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  have hg : MeasureTheory.Integrable g := by
    simpa [g] using (scatG_integrable (v := v) (w := w) hv_supp hw)
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have hv0 : v y = 0 := v_eq_zero_of_norm_ge hv_supp hy
    dsimp [g]
    simp [hv0]
  have hgprof_geR : ∀ s : ℝ, R ≤ s → gprof s = 0 := by
    intro s hs
    dsimp [gprof]
    have hnorm : R ≤ ‖s • radU0‖ := by
      rw [norm_smul_radU0]
      rw [abs_of_nonneg (le_trans hR.le hs)]
      exact hs
    exact hgsupp (s • radU0) hnorm
  let K : ℝ := (1 / 2 : ℝ) * (∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s)
  have hcan (r : ℝ) : canonicalProfile v w R r =
      (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) +
        r * (∫ s in Set.Ioi r, s * gprof s)) := by
    dsimp [canonicalProfile, gprof, g]
  have hAgree (r : ℝ) (hr : R ≤ r) : (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) =
      (∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s) := by
    calc
      (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s)
          = ∫ s : ℝ, (Set.Ioc (0 : ℝ) r).indicator (fun t : ℝ => t ^ 2 * gprof t) s := by
            rw [integral_indicator (s := Set.Ioc (0 : ℝ) r) (f := fun t : ℝ => t ^ 2 * gprof t)
              (μ := (volume : Measure ℝ)) (measurableSet_Ioc)]
      _ = ∫ s : ℝ, (Set.Ioc (0 : ℝ) R).indicator (fun t : ℝ => t ^ 2 * gprof t) s := by
            refine integral_congr_ae ?_
            filter_upwards [] with s
            rw [Set.indicator_apply, Set.indicator_apply]
            simp only [Set.mem_Ioc]
            by_cases hsle : s ≤ R
            · by_cases hs0 : 0 < s
              · simp [hs0, hsle, le_trans hsle hr]
              · simp [hs0, hsle]
            · have hsR : R < s := lt_of_not_ge hsle
              by_cases hs0 : 0 < s
              · have hgs : gprof s = 0 := hgprof_geR s (le_of_lt hsR)
                by_cases hsr : s ≤ r
                · simp [hs0, hsr, hsle, hgs]
                · simp [hs0, hsr, hsle]
              · simp [hs0, hsle]
      _ = ∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s := by
            rw [integral_indicator (s := Set.Ioc (0 : ℝ) R) (f := fun t : ℝ => t ^ 2 * gprof t)
              (μ := (volume : Measure ℝ)) (measurableSet_Ioc)]
  have hTail (r : ℝ) (hr : R ≤ r) : (∫ s in Set.Ioi r, s * gprof s) = 0 := by
    calc
      (∫ s in Set.Ioi r, s * gprof s)
          = ∫ s : ℝ, (Set.Ioi r).indicator (fun t : ℝ => t * gprof t) s := by
            rw [integral_indicator (s := Set.Ioi r) (f := fun t : ℝ => t * gprof t)
              (μ := (volume : Measure ℝ)) (measurableSet_Ioi)]
      _ = (0 : ℝ) := by
            have hz : (Set.Ioi r).indicator (fun t : ℝ => t * gprof t) =ᵐ[(volume : Measure ℝ)]
                (fun _ : ℝ => (0 : ℝ)) := by
              filter_upwards [] with s
              by_cases hs : s ∈ Set.Ioi r
              · have hgs : gprof s = 0 := hgprof_geR s (le_trans hr hs.le)
                rw [Set.indicator_apply]
                simp [hs, hgs]
              · rw [Set.indicator_apply]
                simp [hs]
            rw [integral_congr_ae hz]
            simp
  have hF (r : ℝ) (hr : R ≤ r) : canonicalProfile v w R r = K := by
    rw [hcan r]
    rw [hAgree r hr, hTail r hr]
    dsimp [K]
    simp
  have h3dF : ∀ᵐ x : ℝ³, R ≤ ‖x‖ → canonicalProfile v w R ‖x‖ = ‖x‖ * w x := by
    have h_eq := canonicalProfile_eq_profile (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
    let N : Set ℝ := {r : ℝ | ¬(0 < r → canonicalProfile v w R r = r * radialProfile w r)}
    have hNvol : (volume : Measure ℝ) N = 0 := MeasureTheory.ae_iff.mp h_eq
    let S : Set ℝ := MeasureTheory.toMeasurable (volume : Measure ℝ) N
    have hSmeas : MeasurableSet S := MeasureTheory.measurableSet_toMeasurable (volume : Measure ℝ) N
    have hNS : N ⊆ S := MeasureTheory.subset_toMeasurable (volume : Measure ℝ) N
    have hSvol : (volume : Measure ℝ) S = 0 := by
      rw [MeasureTheory.measure_toMeasurable]
      exact hNvol
    have hprevol : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 :=
      volume_preimage_norm_null_r3 hSmeas hSvol
    let bad : Set ℝ³ := {x : ℝ³ | ¬(R ≤ ‖x‖ → canonicalProfile v w R ‖x‖ = ‖x‖ * w x)}
    have hbad_sub : bad ⊆ {x : ℝ³ | ‖x‖ ∈ S} := by
      intro x hx
      by_contra hxS
      have hRle : R ≤ ‖x‖ := by
        by_contra hn
        exact hx (fun h => False.elim (hn h))
      have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hR hRle
      have hnotN : ‖x‖ ∉ N := by
        intro hNmem
        exact hxS (hNS hNmem)
      have hgoodR : canonicalProfile v w R ‖x‖ = ‖x‖ * radialProfile w ‖x‖ := by
        by_contra h
        exact hnotN (fun hP => h (hP hxpos))
      have hgood : canonicalProfile v w R ‖x‖ = ‖x‖ * w x := by
        rw [radial_eq_profile hrad x]
        exact hgoodR
      exact hx (fun _ => hgood)
    have hbadvol : (volume : Measure ℝ³) bad = 0 :=
      measure_mono_null hbad_sub hprevol
    rw [MeasureTheory.ae_iff]
    change (volume : Measure ℝ³) bad = 0
    exact hbadvol
  have h_aec : ∀ᵐ x : ℝ³, R ≤ ‖x‖ → K = c := by
    filter_upwards [h3dF, hform] with x hx1 hx2
    intro hRle
    have hFKx := hF ‖x‖ hRle
    have h1x := hx1 hRle
    have h2x := hx2 hRle
    rw [← hFKx]
    rw [h1x, h2x]
    have hnx : ‖x‖ ≠ 0 := by
      have : 0 < ‖x‖ := lt_of_lt_of_le hR hRle
      exact ne_of_gt this
    field_simp
  have hKc : K = c := by
    by_contra hne
    have hnull : (volume : Measure ℝ³) {x : ℝ³ | ¬(R ≤ ‖x‖ → K = c)} = 0 :=
      MeasureTheory.ae_iff.mp h_aec
    have hsub : {x : ℝ³ | R ≤ ‖x‖} ⊆ {x : ℝ³ | ¬(R ≤ ‖x‖ → K = c)} := by
      intro x hxR
      intro himp
      exact hne (himp hxR)
    have hvol0 : (volume : Measure ℝ³) {x : ℝ³ | R ≤ ‖x‖} = 0 :=
      measure_mono_null hsub hnull
    have hpos : (volume : Measure ℝ³) {x : ℝ³ | R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R} ≠ 0 := by
      rw [volume_annulus_r3 R (2 * R) hR.le (by linarith)]
      have hR3 : 0 < R ^ 3 := pow_pos hR 3
      have h7 : (2 * R) ^ 3 - R ^ 3 = 7 * R ^ 3 := by ring
      rw [h7]
      have hposarg : 0 < (4 / 3) * π * (7 * R ^ 3) := by positivity
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hposarg)
    have hann0 : (volume : Measure ℝ³) {x : ℝ³ | R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R} = 0 := by
      exact measure_mono_null (by intro x hx; exact hx.1) hvol0
    exact hpos hann0
  intro r hr
  rw [hF r hr]
  exact hKc

/-- **Right-endpoint derivative.**  `deriv (canonicalProfile v w R) r =
(1/2)·∫_{s>r} s·gprof(s) ds` for `r ∈ (0,R)` in the a.e.-sense appropriate to
the absolutely continuous profile; in particular `HasDerivAt
(canonicalProfile v w R) 0 R`.  (Statement: the right-hand derivative at `R`
vanishes.) -/
theorem canonicalProfile_hasDerivAt_R {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    HasDerivAt (canonicalProfile v w R) 0 R := by
  -- The derivative at `R` vanishes.  For `r ≥ R` the profile is constant
  -- (its `∫_{s>r}` tail vanishes and the head agrees with its value at `R`).
  -- For `r < R` the difference is exactly
  --   `u r − u R = −(1/2)·∫_{(r,R]} s·(s−r)·gprof(s) ds`
  -- (the head-tail cancellation is exact), so the difference quotient is
  -- bounded by `(1/2)·R·∫_{(r,R]} |gprof|` (as `s·(s−r) ≤ R·(R−r)`), which
  -- tends to 0 by dominated convergence.  Both one-sided slopes therefore
  -- tend to 0, giving `HasDerivAt` via `hasDerivAt_iff_tendsto_slope`.
  let g : ℝ³ → ℝ := fun y => v y * (1 - w y)
  let gprof : ℝ → ℝ := radialProfile g
  let u : ℝ → ℝ := canonicalProfile v w R
  let μ0 : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hg : MeasureTheory.Integrable g := by
    simpa [g] using (scatG_integrable (v := v) (w := w) hv_supp hw)
  have hgrad : IsRadial g := by
    intro x y hxy
    dsimp [g]
    rw [hvrad x y hxy, hrad x y hxy]
  have hgsupp : ∀ y : ℝ³, R ≤ ‖y‖ → g y = 0 := by
    intro y hy
    have hv0 : v y = 0 := v_eq_zero_of_norm_ge hv_supp hy
    dsimp [g]
    simp [hv0]
  have hgprof_geR : ∀ s : ℝ, R ≤ s → gprof s = 0 := by
    intro s hs
    dsimp [gprof]
    have hnorm : R ≤ ‖s • radU0‖ := by
      rw [norm_smul_radU0]
      rw [abs_of_nonneg (le_trans hR.le hs)]
      exact hs
    exact hgsupp (s • radU0) hnorm
  have hcan (r : ℝ) : u r =
      (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) +
        r * (∫ s in Set.Ioi r, s * gprof s)) := by
    dsimp [u, canonicalProfile, gprof, g]
  have hprof0 : Integrable (fun s : ℝ => s ^ 2 * |gprof s|) μ0 := by
    dsimp [μ0]
    exact (shell_profile_integrable (g := g) hg hgrad)
  have hgprofAE0 : AEStronglyMeasurable gprof μ0 := by
    simpa [gprof, μ0] using shell_gprof_ae_strong (g := g) hg hgrad
  have hf2AE0 : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * gprof s) μ0 := by
    have hsq : AEStronglyMeasurable (fun s : ℝ => s ^ 2) μ0 :=
      (by fun_prop : Measurable (fun s : ℝ => s ^ 2)).aestronglyMeasurable
    exact hsq.mul hgprofAE0
  let f2 : ℝ → ℝ := fun s => s ^ 2 * gprof s
  let f1 : ℝ → ℝ := fun s => s * gprof s
  have hf2_int_R : IntegrableOn f2 (Set.Ioc (0 : ℝ) R) volume := by
    change Integrable (fun s : ℝ => s ^ 2 * gprof s) (volume.restrict (Set.Ioc (0 : ℝ) R))
    constructor
    · exact (hf2AE0.mono_set (s := Set.Ioc (0 : ℝ) R) (t := Set.Ioi (0 : ℝ)) Set.Ioc_subset_Ioi_self)
    · have hb : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|)
          (volume.restrict (Set.Ioc (0 : ℝ) R)) := by
        exact hprof0.2.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)
      refine hb.mono ?_
      filter_upwards [] with s
      simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
  have hBformula (t : ℝ) (htR : t ≤ R) :
      (∫ s in Set.Ioi t, s * gprof s) = (∫ s in Set.Ioc t R, s * gprof s) := by
    have hsplit : Set.Ioi t = Set.Ioc t R ∪ Set.Ioi R := by
      ext s
      constructor
      · intro hts
        by_cases hsR : s ≤ R
        · left
          exact ⟨hts, hsR⟩
        · right
          exact lt_of_not_ge hsR
      · intro hs
        rcases hs with h1 | h2
        · exact h1.1
        · exact lt_of_le_of_lt htR h2
    calc
      (∫ s in Set.Ioi t, s * gprof s)
          = ∫ s in Set.Ioc t R ∪ Set.Ioi R, s * gprof s := by rw [hsplit]
      _ = ∫ s in Set.Ioc t R, s * gprof s := by
          refine integral_union_eq_left_of_forall (s := Set.Ioc t R) (t := Set.Ioi R)
            (f := fun s : ℝ => s * gprof s) (μ := (volume : Measure ℝ))
            (measurableSet_Ioi) ?_
          intro x hx
          have hg0 : gprof x = 0 := hgprof_geR x (le_of_lt hx)
          simp [hg0]
  have hBR0 : (∫ s in Set.Ioi R, s * gprof s) = 0 := by
    have := hBformula R le_rfl
    rw [this]
    simp
  have huR0 : u R = (1 / 2 : ℝ) * (∫ s in Set.Ioc (0 : ℝ) R, f2 s) := by
    rw [hcan R, hBR0]
    dsimp [f2]
    ring
  have hAdiff (y : ℝ) (hy0 : 0 ≤ y) (hyR : y ≤ R) :
      (∫ s in Set.Ioc (0 : ℝ) R, f2 s) - (∫ s in Set.Ioc (0 : ℝ) y, f2 s) =
        (∫ s in Set.Ioc y R, f2 s) := by
    have hsub : Set.Ioc (0 : ℝ) y ⊆ Set.Ioc (0 : ℝ) R := by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hyR⟩
    have hsdiff : Set.Ioc (0 : ℝ) R \ Set.Ioc (0 : ℝ) y = Set.Ioc y R := by
      ext s
      constructor
      · intro hs
        rcases hs with ⟨⟨hs0, hsR⟩, hsy⟩
        refine ⟨?_, hsR⟩
        by_contra hnot
        have hsle : s ≤ y := le_of_not_gt hnot
        exact hsy ⟨hs0, hsle⟩
      · intro hs
        have hs0' : 0 < s := lt_of_le_of_lt hy0 hs.1
        constructor
        · exact ⟨hs0', hs.2⟩
        · intro hmem
          exact (not_lt_of_ge hmem.2) hs.1
    calc
      (∫ s in Set.Ioc (0 : ℝ) R, f2 s) - (∫ s in Set.Ioc (0 : ℝ) y, f2 s)
          = ∫ s in Set.Ioc (0 : ℝ) R \ Set.Ioc (0 : ℝ) y, f2 s := by
            exact (setIntegral_sdiff (t := Set.Ioc (0 : ℝ) y) (f := f2)
              (μ := (volume : Measure ℝ)) (measurableSet_Ioc) hf2_int_R hsub).symm
      _ = ∫ s in Set.Ioc y R, f2 s := by rw [hsdiff]
  -- constancy beyond R
  have hFbeyond (r : ℝ) (hr : R ≤ r) : u r = u R := by
    have hAgree : (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s) =
        (∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s) := by
      calc
        (∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * gprof s)
            = ∫ s : ℝ, (Set.Ioc (0 : ℝ) r).indicator (fun t : ℝ => t ^ 2 * gprof t) s := by
              rw [integral_indicator (s := Set.Ioc (0 : ℝ) r) (f := fun t : ℝ => t ^ 2 * gprof t)
                (μ := (volume : Measure ℝ)) (measurableSet_Ioc)]
        _ = ∫ s : ℝ, (Set.Ioc (0 : ℝ) R).indicator (fun t : ℝ => t ^ 2 * gprof t) s := by
              refine integral_congr_ae ?_
              filter_upwards [] with s
              rw [Set.indicator_apply, Set.indicator_apply]
              simp only [Set.mem_Ioc]
              by_cases hsle : s ≤ R
              · by_cases hs0 : 0 < s
                · simp [hs0, hsle, le_trans hsle hr]
                · simp [hs0, hsle]
              · have hsR : R < s := lt_of_not_ge hsle
                by_cases hs0 : 0 < s
                · have hgs : gprof s = 0 := hgprof_geR s (le_of_lt hsR)
                  by_cases hsr : s ≤ r
                  · simp [hs0, hsr, hsle, hgs]
                  · simp [hs0, hsr, hsle]
                · simp [hs0, hsle]
        _ = ∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s := by
              rw [integral_indicator (s := Set.Ioc (0 : ℝ) R) (f := fun t : ℝ => t ^ 2 * gprof t)
                (μ := (volume : Measure ℝ)) (measurableSet_Ioc)]
    have hTail : (∫ s in Set.Ioi r, s * gprof s) = 0 := by
      calc
        (∫ s in Set.Ioi r, s * gprof s)
            = ∫ s : ℝ, (Set.Ioi r).indicator (fun t : ℝ => t * gprof t) s := by
              rw [integral_indicator (s := Set.Ioi r) (f := fun t : ℝ => t * gprof t)
                (μ := (volume : Measure ℝ)) (measurableSet_Ioi)]
        _ = (0 : ℝ) := by
              have hz : (Set.Ioi r).indicator (fun t : ℝ => t * gprof t) =ᵐ[(volume : Measure ℝ)]
                  (fun _ : ℝ => (0 : ℝ)) := by
                filter_upwards [] with s
                by_cases hs : s ∈ Set.Ioi r
                · have hgs : gprof s = 0 := hgprof_geR s (le_trans hr hs.le)
                  rw [Set.indicator_apply]
                  simp [hs, hgs]
                · rw [Set.indicator_apply]
                  simp [hs]
              rw [integral_congr_ae hz]
              simp
    calc
      u r = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s) + r * 0) := by
        rw [hcan r, hAgree, hTail]
      _ = (1 / 2 : ℝ) * (∫ s in Set.Ioc (0 : ℝ) R, s ^ 2 * gprof s) := by simp
      _ = u R := by
        rw [huR0]
  -- f1 integrable on (y,R]
  have hf1_int_D (y : ℝ) (hy0 : 0 < y) : IntegrableOn f1 (Set.Ioc y R) volume := by
    have hy0le : 0 ≤ y := hy0.le
    have hyIoi : Set.Ioc y R ⊆ Set.Ioi (0 : ℝ) := by
      intro s hs
      exact lt_of_le_of_lt hy0le hs.1
    have hyRm : Set.Ioc y R ⊆ Set.Ioc (0 : ℝ) R := by
      intro s hs
      exact ⟨hyIoi hs, hs.2⟩
    change Integrable (fun s : ℝ => s * gprof s) (volume.restrict (Set.Ioc y R))
    constructor
    · have hgAEy : AEStronglyMeasurable gprof (volume.restrict (Set.Ioc y R)) := by
        exact hgprofAE0.mono_set (s := Set.Ioc y R) (t := Set.Ioi (0 : ℝ)) hyIoi
      have hsAEy : AEStronglyMeasurable (fun s : ℝ => s) (volume.restrict (Set.Ioc y R)) :=
        (measurable_id : Measurable (fun s : ℝ => s)).aestronglyMeasurable
      exact hsAEy.mul hgAEy
    · have hb2' : HasFiniteIntegral (fun s : ℝ => (1 / y) * (s ^ 2 * |gprof s|))
          (volume.restrict (Set.Ioc y R)) := by
        have hb0 : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|)
            (volume.restrict (Set.Ioc y R)) := by
          exact hprof0.2.mono_measure (Measure.restrict_mono hyIoi le_rfl)
        exact hb0.const_mul (1 / y)
      refine hb2'.mono ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsy : y < s := hs.1
      have hspos : 0 < s := lt_trans hy0 hsy
      have hgpos : 0 ≤ |gprof s| := abs_nonneg (gprof s)
      have hsydiv : 1 ≤ s / y := by
        rw [one_le_div hy0]
        exact hsy.le
      have hle : s ≤ (1 / y) * s ^ 2 := by
        calc
          s = s * 1 := by ring
          _ ≤ s * (s / y) := by
            exact mul_le_mul_of_nonneg_left hsydiv (le_of_lt hspos)
          _ = (1 / y) * s ^ 2 := by ring
      calc
        |s * gprof s| = s * |gprof s| := by rw [abs_mul, abs_of_nonneg (le_of_lt hspos)]
        _ ≤ (1 / y) * s ^ 2 * |gprof s| := by
          exact mul_le_mul_of_nonneg_right hle hgpos
        _ = |(1 / y) * (s ^ 2 * |gprof s|)| := by
          rw [abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hy0.le)
            (mul_nonneg (sq_nonneg s) (abs_nonneg (gprof s))))]
          ring
  -- difference identity
  have hdiff (y : ℝ) (hy0 : 0 < y) (hyR : y < R) :
      u y - u R = - (1 / 2 : ℝ) * (∫ s in Set.Ioc y R, s * (s - y) * gprof s) := by
    have hyR' : y ≤ R := hyR.le
    have hBfy : (∫ s in Set.Ioi y, s * gprof s) = ∫ s in Set.Ioc y R, s * gprof s := hBformula y hyR'
    have hAy' : (∫ s in Set.Ioc (0 : ℝ) y, f2 s) - (∫ s in Set.Ioc (0 : ℝ) R, f2 s) =
        - (∫ s in Set.Ioc y R, f2 s) := by
      rw [← hAdiff y hy0.le hyR']
      ring
    have hf2y : IntegrableOn f2 (Set.Ioc y R) volume := by
      exact hf2_int_R.mono_set (s := Set.Ioc y R) (by
        intro s hs; exact ⟨lt_of_le_of_lt hy0.le hs.1, hs.2⟩)
    have hf1y : IntegrableOn f1 (Set.Ioc y R) volume := hf1_int_D y hy0
    have hysub : (∫ s in Set.Ioc y R, y * f1 s) =
        y * (∫ s in Set.Ioc y R, f1 s) := by
      rw [← integral_const_mul y f1]
    have hsum : (∫ s in Set.Ioc y R, y * f1 s) - ∫ s in Set.Ioc y R, f2 s =
        ∫ s in Set.Ioc y R, (y * f1 s - f2 s) := by
      have hyi : IntegrableOn (fun s : ℝ => y * f1 s) (Set.Ioc y R) volume := by
        exact hf1y.const_mul y
      exact (integral_sub hyi hf2y).symm
    calc
      u y - u R
          = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) y, f2 s) +
              y * (∫ s in Set.Ioi y, s * gprof s)) -
              (1 / 2 : ℝ) * (∫ s in Set.Ioc (0 : ℝ) R, f2 s) := by
            rw [hcan y, huR0]
      _ = (1 / 2 : ℝ) * ((∫ s in Set.Ioc (0 : ℝ) y, f2 s) -
              (∫ s in Set.Ioc (0 : ℝ) R, f2 s) + y * (∫ s in Set.Ioc y R, f1 s)) := by
            rw [hBfy]
            ring
      _ = (1 / 2 : ℝ) * (- (∫ s in Set.Ioc y R, f2 s) + y * (∫ s in Set.Ioc y R, f1 s)) := by
            rw [hAy']
      _ = (1 / 2 : ℝ) * (∫ s in Set.Ioc y R, y * f1 s - f2 s) := by
            have hcomb : - (∫ s in Set.Ioc y R, f2 s) + y * (∫ s in Set.Ioc y R, f1 s) =
                ∫ s in Set.Ioc y R, (y * f1 s - f2 s) := by
              calc
                - (∫ s in Set.Ioc y R, f2 s) + y * (∫ s in Set.Ioc y R, f1 s)
                    = (∫ s in Set.Ioc y R, y * f1 s) - ∫ s in Set.Ioc y R, f2 s := by
                      rw [← hysub]
                      ring
                _ = ∫ s in Set.Ioc y R, (y * f1 s - f2 s) := hsum
            rw [hcomb]
      _ = - (1 / 2 : ℝ) * (∫ s in Set.Ioc y R, s * (s - y) * gprof s) := by
            have hA : (∫ s in Set.Ioc y R, y * f1 s - f2 s) =
                - ∫ s in Set.Ioc y R, s * (s - y) * gprof s := by
              have hpt : (fun s : ℝ => y * f1 s - f2 s) =ᵐ[(volume.restrict (Set.Ioc y R))]
                  (fun s : ℝ => -(s * (s - y) * gprof s)) := by
                filter_upwards [] with s
                dsimp [f1, f2]
                ring
              rw [integral_congr_ae hpt]
              rw [integral_neg]
            rw [hA]
            ring
  -- J(y) := ∫_{(y,R]} |gprof| → 0 as y → R⁻ (dominated convergence)
  have hJ : Tendsto (fun y : ℝ => ∫ s in Set.Ioc y R, |gprof s|) (𝓝[<] R) (𝓝 0) := by
    let FJ : ℝ → ℝ → ℝ := fun y => (Set.Ioc y R).indicator (fun s : ℝ => |gprof s|)
    have hFJint (y : ℝ) (hy : 0 ≤ y) : (∫ s : ℝ, FJ y s ∂μ0) =
        ∫ s in Set.Ioc y R, |gprof s| := by
      dsimp [FJ, μ0]
      rw [integral_indicator (hs := measurableSet_Ioc)]
      simp only [Measure.restrict_restrict (measurableSet_Ioc)]
      congr 1
      ext s
      simp [hy]
    have hgAE0 : AEStronglyMeasurable (fun s : ℝ => |gprof s|) μ0 := hgprofAE0.norm
    have hbig : Integrable (fun s : ℝ => (4 / R ^ 2) * (s ^ 2 * |gprof s|)) μ0 := by
      have hsm : AEStronglyMeasurable (fun s : ℝ => s ^ 2 * |gprof s|) μ0 := by
        exact (by fun_prop : Measurable (fun s : ℝ => s ^ 2)).aestronglyMeasurable.mul hgAE0
      rw [Integrable]
      constructor
      · exact hsm.const_mul (4 / R ^ 2)
      · exact hprof0.2.const_mul (4 / R ^ 2)
    have ht : Tendsto (fun y : ℝ => ∫ s : ℝ, FJ y s ∂μ0) (𝓝[<] R)
        (𝓝 (∫ s : ℝ, (0 : ℝ) ∂μ0)) := by
      refine tendsto_integral_filter_of_dominated_convergence (ι := ℝ) (l := 𝓝[<] R)
        (μ := μ0) (F := FJ) (f := fun _ : ℝ => (0 : ℝ))
        (bound := fun s : ℝ => (4 / R ^ 2) * (s ^ 2 * |gprof s|)) ?_ ?_ ?_ ?_
      · filter_upwards [] with y
        exact (aestronglyMeasurable_indicator_iff (s := Set.Ioc y R) (measurableSet_Ioc)).2 hgAE0.restrict
      · filter_upwards [(mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith [hR] : R / 2 < R)))] with y hy
        have hyq : R / 2 < y := by simpa using hy
        refine ae_of_all _ ?_
        intro s
        dsimp [FJ]
        by_cases hsI : s ∈ Set.Ioc y R
        · simp [hsI]
          have hsgt0 : 0 < s := lt_trans (half_pos hR) (lt_trans hyq hsI.1)
          have h2s : R ≤ 2 * s := by
            have hRs : R / 2 < s := lt_trans hyq hsI.1
            have h1 : (R / 2) * 2 < s * 2 := mul_lt_mul_of_pos_right hRs (by norm_num)
            ring_nf at h1
            exact le_of_lt (by simpa [mul_comm] using h1)
          have hle : 1 ≤ 2 * s / R := by
            rw [one_le_div hR]
            exact h2s
          have hsq : (2 * s / R) ^ 2 = (4 / R ^ 2) * s ^ 2 := by
            field_simp [hR.ne']
            ring
          have hsq1 : (1 : ℝ) ≤ (4 / R ^ 2) * s ^ 2 := by
            rw [← hsq]
            have hx : 0 ≤ 2 * s / R := le_of_lt (div_pos (by positivity) hR)
            have hm := mul_le_mul hle hle (by norm_num) hx
            simpa [pow_two] using hm
          have hfac : |gprof s| ≤ (4 / R ^ 2) * (s ^ 2 * |gprof s|) := by
            have hgpos : 0 ≤ |gprof s| := abs_nonneg (gprof s)
            calc
              |gprof s| = (1 : ℝ) * |gprof s| := by ring
              _ ≤ ((4 / R ^ 2) * s ^ 2) * |gprof s| := by
                exact mul_le_mul_of_nonneg_right hsq1 hgpos
              _ = (4 / R ^ 2) * (s ^ 2 * |gprof s|) := by ring
          exact hfac
        · simp [hsI]
          positivity
      · simpa [μ0] using hbig
      · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
        intro s hs
        have hlim : Tendsto (fun y : ℝ => FJ y s) (𝓝[<] R) (𝓝 0) := by
          have hev : (fun y : ℝ => FJ y s) =ᶠ[𝓝[<] R] (fun _ : ℝ => (0 : ℝ)) := by
            by_cases hsR : s < R
            · have hmem : {y : ℝ | s < y} ∈ 𝓝[<] R := by
                apply mem_nhdsWithin_of_mem_nhds
                exact Ioi_mem_nhds hsR
              filter_upwards [hmem, (self_mem_nhdsWithin : Set.Iio R ∈ 𝓝[<] R)] with y hy1 hy2
              dsimp [FJ]
              have hns : s ∉ Set.Ioc y R := by
                intro hmem2
                exact (not_lt_of_ge hy1.le) hmem2.1
              simp [hns]
            · by_cases hseq : s = R
              · subst s
                filter_upwards [] with y
                dsimp [FJ]
                simp [hgprof_geR R le_rfl]
              · have hRlt : R < s := lt_of_le_of_ne (le_of_not_gt hsR) (Ne.symm hseq)
                filter_upwards [] with y
                dsimp [FJ]
                have hns : s ∉ Set.Ioc y R := by
                  intro hmem2
                  exact (not_le_of_gt hRlt) hmem2.2
                simp [hns]
          exact (tendsto_congr' hev).2 tendsto_const_nhds
        exact hlim
    have ht0 : Tendsto (fun y : ℝ => ∫ s : ℝ, FJ y s ∂μ0) (𝓝[<] R) (𝓝 0) := by
      simpa using ht
    refine ht0.congr' ?_
    filter_upwards [(mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hR))] with y hy
    exact hFJint y (le_of_lt (by simpa using hy))
  -- |gprof|, g1, g2 integrable on (y,R]
  have habs_int_D (y : ℝ) (hy0 : 0 < y) :
      IntegrableOn (fun s : ℝ => |gprof s|) (Set.Ioc y R) volume := by
    let D : Set ℝ := Set.Ioc y R
    have hDsub : D ⊆ Set.Ioi (0 : ℝ) := by
      intro s hs
      exact lt_of_le_of_lt hy0.le hs.1
    change Integrable (fun s : ℝ => |gprof s|) (volume.restrict D)
    constructor
    · exact (hgprofAE0.norm).mono_measure (Measure.restrict_mono hDsub le_rfl)
    · have hb0 : HasFiniteIntegral (fun s : ℝ => (1 / y ^ 2) * (s ^ 2 * |gprof s|))
          (volume.restrict D) := by
        have hb : HasFiniteIntegral (fun s : ℝ => s ^ 2 * |gprof s|) (volume.restrict D) := by
          exact hprof0.2.mono_measure (Measure.restrict_mono hDsub le_rfl)
        exact hb.const_mul (1 / y ^ 2)
      refine hb0.mono' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsy : y ≤ s := hs.1.le
      rw [Real.norm_eq_abs, abs_abs]
      have hle1 : 1 ≤ s ^ 2 / y ^ 2 := by
        rw [one_le_div (sq_pos_of_pos hy0)]
        exact (sq_le_sq.mpr (by
          have hyabs : |y| = y := abs_of_nonneg hy0.le
          have hsabs : |s| = s := abs_of_nonneg (le_of_lt (lt_trans hy0 hs.1))
          rw [hyabs, hsabs]
          exact hsy))
      calc
        |gprof s| = (1 : ℝ) * |gprof s| := by ring
        _ ≤ (s ^ 2 / y ^ 2) * |gprof s| := by
          exact mul_le_mul_of_nonneg_right hle1 (abs_nonneg (gprof s))
        _ = (1 / y ^ 2) * (s ^ 2 * |gprof s|) := by ring
  have hg2_int_D (y : ℝ) (hy0 : 0 < y) :
      IntegrableOn (fun s : ℝ => R * (R - y) * |gprof s|) (Set.Ioc y R) volume := by
    let D : Set ℝ := Set.Ioc y R
    change Integrable (fun s : ℝ => R * (R - y) * |gprof s|) (volume.restrict D)
    constructor
    · have hgAEy : AEStronglyMeasurable (fun s : ℝ => |gprof s|) (volume.restrict D) := by
        exact (hgprofAE0.norm).mono_measure (Measure.restrict_mono
          (by intro s hs; exact lt_of_le_of_lt hy0.le hs.1) le_rfl)
      exact hgAEy.const_mul (R * (R - y))
    · have hb : HasFiniteIntegral (fun s : ℝ => |gprof s|) (volume.restrict D) := by
        exact (habs_int_D y hy0).2
      exact hb.const_mul (R * (R - y))
  have hg1_int_D (y : ℝ) (hy0 : 0 < y) :
      IntegrableOn (fun s : ℝ => s * (s - y) * |gprof s|) (Set.Ioc y R) volume := by
    let D : Set ℝ := Set.Ioc y R
    change Integrable (fun s : ℝ => s * (s - y) * |gprof s|) (volume.restrict D)
    constructor
    · have hgAEy : AEStronglyMeasurable (fun s : ℝ => |gprof s|) (volume.restrict D) := by
        exact (hgprofAE0.norm).mono_measure (Measure.restrict_mono
          (by intro s hs; exact lt_of_le_of_lt hy0.le hs.1) le_rfl)
      have hcoe : AEStronglyMeasurable (fun s : ℝ => s * (s - y)) (volume.restrict D) :=
        (by fun_prop : Measurable (fun s : ℝ => s * (s - y))).aestronglyMeasurable
      exact hcoe.mul hgAEy
    · have hb2 : HasFiniteIntegral (fun s : ℝ => R * (R - y) * |gprof s|)
          (volume.restrict D) := by
        exact (hg2_int_D y hy0).2
      refine hb2.mono ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hxy : y < s := hs.1
      have hxR : s ≤ R := hs.2
      have hxsub : s - y ≤ R - y := by linarith
      have hmain : s * (s - y) ≤ R * (R - y) := by
        calc
          s * (s - y) = (s - y) * s := by ring
          _ ≤ (s - y) * R := by
            exact mul_le_mul_of_nonneg_left hxR (sub_nonneg.mpr hxy.le)
          _ ≤ (R - y) * R := by
            exact mul_le_mul_of_nonneg_right hxsub hR.le
          _ = R * (R - y) := by ring
      have hnonneg : 0 ≤ s * (s - y) * |gprof s| :=
        mul_nonneg (mul_nonneg (le_of_lt (lt_trans hy0 hxy)) (sub_nonneg.mpr hxy.le))
          (abs_nonneg (gprof s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        s * (s - y) * |gprof s| ≤ R * (R - y) * |gprof s| := by
          exact mul_le_mul_of_nonneg_right hmain (abs_nonneg (gprof s))
        _ = ‖R * (R - y) * |gprof s|‖ := by
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg hR.le (sub_nonneg.mpr (by linarith [hy0, hxR, hxy]))) (abs_nonneg (gprof s)))]
  -- difference-quotient bound
  have hdiffnorm (y : ℝ) (hy0 : 0 < y) (hyR : y < R) :
      |u y - u R| ≤ (1 / 2) * R * (R - y) * (∫ s in Set.Ioc y R, |gprof s|) := by
    let D : Set ℝ := Set.Ioc y R
    let h : ℝ → ℝ := fun s => s * (s - y) * gprof s
    let g1 : ℝ → ℝ := fun s => s * (s - y) * |gprof s|
    let g2 : ℝ → ℝ := fun s => R * (R - y) * |gprof s|
    have hdif := hdiff y hy0 hyR
    have hpt : (fun s : ℝ => |h s|) =ᵐ[(volume.restrict D)]
        (fun s : ℝ => g1 s) := by
      dsimp [D, h, g1]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hsy : y < s := hs.1
      have hsp : 0 < s := lt_trans hy0 hsy
      have hss : 0 ≤ s * (s - y) := mul_nonneg (le_of_lt hsp) (le_of_lt (sub_pos.mpr hsy))
      calc
        |s * (s - y) * gprof s| = |s * (s - y)| * |gprof s| := by rw [abs_mul]
        _ = (s * (s - y)) * |gprof s| := by rw [abs_of_nonneg hss]
        _ = s * (s - y) * |gprof s| := by ring
    have hmono : ∀ x ∈ D, g1 x ≤ g2 x := by
      intro x hx
      have hxy : y < x := hx.1
      have hxR : x ≤ R := hx.2
      have hxsub : x - y ≤ R - y := by linarith
      have hmain : x * (x - y) ≤ R * (R - y) := by
        calc
          x * (x - y) = (x - y) * x := by ring
          _ ≤ (x - y) * R := by
            exact mul_le_mul_of_nonneg_left hxR (sub_nonneg.mpr hxy.le)
          _ ≤ (R - y) * R := by
            exact mul_le_mul_of_nonneg_right hxsub hR.le
          _ = R * (R - y) := by ring
      calc
        g1 x = x * (x - y) * |gprof x| := by rfl
        _ ≤ R * (R - y) * |gprof x| := by
          exact mul_le_mul_of_nonneg_right hmain (abs_nonneg (gprof x))
        _ = g2 x := by rfl
    have hstepb : |u y - u R| ≤ (1 / 2) * (∫ s in D, |h s|) := by
      rw [hdif]
      have hni : |∫ s in D, h s| ≤ ∫ s in D, |h s| := by
        dsimp [h]
        exact abs_integral_le_integral_abs
      calc
        |-(1 / 2 : ℝ) * (∫ s in D, h s)| = |-(1 / 2 : ℝ)| * |∫ s in D, h s| := by
          rw [abs_mul]
        _ ≤ (1 / 2) * (∫ s in D, |h s|) := by
          rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left hni (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hG2 : (∫ s in D, g2 s) = R * (R - y) * (∫ s in D, |gprof s|) := by
      dsimp [g2]
      rw [← integral_const_mul (R * (R - y)) (fun s : ℝ => |gprof s|)]
    calc
      |u y - u R| ≤ (1 / 2) * (∫ s in D, |h s|) := hstepb
      _ = (1 / 2) * (∫ s in D, g1 s) := by
        rw [integral_congr_ae hpt]
      _ ≤ (1 / 2) * (∫ s in D, g2 s) := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_mono_on (s := D) (μ := (volume : Measure ℝ))
            (hg1_int_D y hy0) (hg2_int_D y hy0) measurableSet_Ioc hmono)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = (1 / 2) * (R * (R - y) * (∫ s in D, |gprof s|)) := by
        rw [hG2]
      _ = (1 / 2) * R * (R - y) * (∫ s in Set.Ioc y R, |gprof s|) := by
        ring
  -- slope equals the difference quotient
  have hslope_eq (y : ℝ) : slope u R y = (u y - u R) / (y - R) := by
    simp [slope, div_eq_mul_inv, mul_comm]
  have hslope_abs (y : ℝ) (hyR : y < R) : |slope u R y| = |u y - u R| / (R - y) := by
    rw [hslope_eq, abs_div]
    have hneg : |y - R| = R - y := by
      rw [abs_of_neg (sub_neg.mpr hyR)]
      ring
    rw [hneg]
  have hslope_bound (y : ℝ) (hy0 : 0 < y) (hyR : y < R) :
      |slope u R y| ≤ (1 / 2) * R * (∫ s in Set.Ioc y R, |gprof s|) := by
    have h1 := hdiffnorm y hy0 hyR
    have hRmy : 0 < R - y := sub_pos.mpr hyR
    rw [hslope_abs y hyR]
    rw [div_le_iff₀ hRmy]
    have htmp : (1 / 2) * R * (R - y) * (∫ s in Set.Ioc y R, |gprof s|) =
        ((1 / 2) * R * (∫ s in Set.Ioc y R, |gprof s|)) * (R - y) := by ring
    rwa [← htmp]
  have hslope_left : Tendsto (fun y : ℝ => slope u R y) (𝓝[<] R) (𝓝 0) := by
    have hJm : Tendsto (fun y : ℝ => (1 / 2) * R * (∫ s in Set.Ioc y R, |gprof s|))
        (𝓝[<] R) (𝓝 0) := by
      simpa using hJ.const_mul ((1 / 2) * R)
    have hnonneg : ∀ᶠ y in 𝓝[<] R, 0 ≤ |slope u R y| :=
      Eventually.of_forall (fun y => abs_nonneg (slope u R y))
    have hle : ∀ᶠ y in 𝓝[<] R,
        |slope u R y| ≤ (1 / 2) * R * (∫ s in Set.Ioc y R, |gprof s|) := by
      filter_upwards [(mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hR)),
          (self_mem_nhdsWithin : Set.Iio R ∈ 𝓝[<] R)] with y hy0p hyRp
      exact hslope_bound y (by simpa using hy0p) hyRp
    have hnorm0 : Tendsto (fun y : ℝ => ‖slope u R y‖) (𝓝[<] R) (𝓝 0) := by
      have hsq := squeeze_zero' hnonneg hle hJm
      simpa [Real.norm_eq_abs] using hsq
    exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm0
  have hslope_right : Tendsto (fun y : ℝ => slope u R y) (𝓝[>] R) (𝓝 0) := by
    have hev : (fun y : ℝ => slope u R y) =ᶠ[𝓝[>] R] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [(self_mem_nhdsWithin : Set.Ioi R ∈ 𝓝[>] R)] with y hy
      have huy : u y = u R := hFbeyond y (le_of_lt hy)
      simp [slope, huy]
    exact (tendsto_congr' hev).2 tendsto_const_nhds
  rw [hasDerivAt_iff_tendsto_slope]
  have hF : nhdsWithin R ({R}ᶜ) = nhdsWithin R (Set.Iio R) ⊔ nhdsWithin R (Set.Ioi R) := by
    rw [← nhdsWithin_union]
    congr 1
    exact Set.Iio_union_Ioi.symm
  rw [hF]
  rw [tendsto_sup]
  constructor
  · exact hslope_left
  · exact hslope_right

end Submission.BoseGases
