import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixR.LatGreen.MomentOfTail
import Submission.Work.BoseFixR.LatGreen.TailOfCanonical
import Submission.Work.UBB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary facts about the profile of `g₀ = v(1−ω)`

These reduce the target to the abstract one-dimensional estimates
`Work.BoseFixR.LatGreen.TailOfCanonical` and `Work.BoseFixR.LatGreen.MomentOfTail`
for the radial profile `s ↦ radialProfile (g₀ v h) s`:

* `isRadial_g0` — `g₀` is radial (so its profile is available);
* `radialProfile_g0_nonneg` — the profile is nonnegative a.e. (from `0 ≤ v` and
  the a.e. bound `ω ≤ 1` on the profile of the scattering solution);
* `integrableOn_sq_abs_g0profile` — `s²|profile|` is integrable on `(0,∞)`
  (polar-coordinate form of `g₀ ∈ L¹`), and
  `aestronglyMeasurable_g0profile` — the profile is a.e. strongly measurable;
* `canonicalProfile_le_r_g0` — the corpus maximum-principle bound
  `canonicalProfile v w₀ R r ≤ r` for `0 < r < R`, in exactly the shape
  `(1/2)(∫_{0<s≤r} s² G + r∫_{s>r} s G) ≤ r` consumed by `TailOfCanonical`;
* `g0_smul_single_eq_profile` — `g₀(r • e₀)` is the profile at `r` for `r > 0`,
  which transfers the profile estimate to the vector form of the target.
-/

/-- `g₀ = v(1−ω)` is radial when `v` is. -/
lemma isRadial_g0 {v : ℝ³ → ℝ} (hvrad : BoseGases.IsRadial v) (h : Work.UBB.ScatSol v) :
    BoseGases.IsRadial (Submission.BoseGases.g0 v h) := by
  intro x y hxy
  have hw : BoseGases.IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  show v x * (1 - Classical.choose h x) = v y * (1 - Classical.choose h y)
  rw [hvrad x y hxy, hw x y hxy]

/-- The profile of `g₀ = v(1−ω)` factors through the profiles of `v` and `ω`. -/
lemma radialProfile_g0_eq {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (s : ℝ) :
    Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s =
      Submission.BoseGases.radialProfile v s *
        (1 - Submission.BoseGases.radialProfile (Classical.choose h) s) := by
  simp only [Submission.BoseGases.radialProfile, Submission.BoseGases.g0]

/-- The profile of `g₀ = v(1−ω)` is nonnegative a.e. on `(0,∞)`. -/
lemma radialProfile_g0_nonneg {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s := by
  have hw : BoseGases.IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  have hws : BoseGases.IsScatteringSolution (Classical.choose h) v :=
    (Classical.choose_spec h).2
  have hb := Submission.BoseGases.radialProfile_bounds_ae (v := v) (w := Classical.choose h) (R := R)
    hR hv hvrad hv_supp hw hws
  have hb' : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ Submission.BoseGases.radialProfile (Classical.choose h) s ∧
        Submission.BoseGases.radialProfile (Classical.choose h) s ≤ 1 := by
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioi] with s hs hmem
    exact hs hmem
  filter_upwards [hb'] with s hs
  rw [radialProfile_g0_eq]
  have hvprof : 0 ≤ Submission.BoseGases.radialProfile v s := by
    simp only [Submission.BoseGases.radialProfile]
    exact hv _
  exact mul_nonneg hvprof (by linarith [hs.2])

/-- Polar-coordinate form of `g₀ ∈ L¹`: `s²|profile|` is integrable on `(0,∞)`. -/
lemma integrableOn_sq_abs_g0profile {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) :
    IntegrableOn (fun s : ℝ =>
      s ^ 2 * |Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s|)
      (Set.Ioi (0 : ℝ)) :=
  Submission.BoseGases.shell_profile_integrable (g := Submission.BoseGases.g0 v h)
    (Submission.BoseGases.g0_integrable hR hv_supp h) (isRadial_g0 hvrad h)

/-- The profile of `g₀` is a.e. strongly measurable on `(0,∞)`. -/
lemma aestronglyMeasurable_g0profile {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) :
    AEStronglyMeasurable
      (fun s : ℝ => Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
  Submission.BoseGases.shell_gprof_ae_strong (g := Submission.BoseGases.g0 v h)
    (Submission.BoseGases.g0_integrable hR hv_supp h) (isRadial_g0 hvrad h)

/-- The maximum-principle bound on the canonical profile of `g₀ = v(1−ω)`, in the
shape consumed by `TailOfCanonical`. -/
lemma canonicalProfile_le_r_g0 {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) :
    ∀ r : ℝ, 0 < r → r < R →
      (1 / 2) * ((∫ s in Set.Ioc (0 : ℝ) r,
            s ^ 2 * Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s) +
          r * (∫ s in Set.Ioi r,
            s * Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s)) ≤ r := by
  have hw : BoseGases.IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  have hws : BoseGases.IsScatteringSolution (Classical.choose h) v :=
    (Classical.choose_spec h).2
  have hcan := Submission.BoseGases.canonicalProfile_le_r (v := v) (w := Classical.choose h) (R := R)
    hR hv hvrad hv_supp hw hws
  intro r hr0 hrR
  have heq : Submission.BoseGases.canonicalProfile v (Classical.choose h) R r =
      (1 / 2) * ((∫ s in Set.Ioc (0 : ℝ) r,
            s ^ 2 * Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s) +
          r * (∫ s in Set.Ioi r,
            s * Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s)) := by
    simp only [Submission.BoseGases.canonicalProfile, Submission.BoseGases.g0,
      Submission.BoseGases.radialProfile]
  rw [← heq]
  exact hcan r hr0 hrR

/-- For `r > 0`, the value of `g₀` at `r • e₀` is the radial profile of `g₀` at `r`
(`e₀` any unit vector). -/
lemma g0_smul_single_eq_profile {v : ℝ³ → ℝ} (hvrad : BoseGases.IsRadial v)
    (h : Work.UBB.ScatSol v) {r : ℝ} (_hr : 0 < r) :
    Submission.BoseGases.g0 v h (r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) =
      Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) r := by
  have hrad := isRadial_g0 hvrad h
  have hnorm : ‖r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = |r| := by
    rw [norm_smul]
    simp [Real.norm_eq_abs]
  rw [Submission.BoseGases.radial_eq_profile hrad, hnorm,
    Submission.BoseGases.radialProfile_abs hrad r]

/-- **The weighted mass of `g₀ = v(1−ω)` near the origin.**

For a nonnegative radial potential `v` of range `R` with a radial scattering
solution (`Work.UBB.ScatSol v`), the radial profile of the source
`g₀ = v(1−ω)` (`Submission.BoseGases.g0`) has finite weighted mass

`∫₀^∞ r·|g₀(r•e₀)| dr ≤ 2`,   equivalently  `∫_{ℝ³} g₀(x)/‖x‖ dx ≤ 8π`.

This is the summability input of `Work.BoseFixR.LatGreen.W1funDecay`'s angular
estimate (the weight `r` in front of the radial profile): it is *not* a
consequence of `∫g₀ = 8πa` alone, but it does follow from the physics, through
the Newton representation of the scattering solution: with `u := 1 - ω` one has
`u ≥ 0`, `u ≤ 1` a.e. and `ω = N_{g₀/8π}`, so
`⨍_{‖x‖=ρ} ω dσ = (1/8π) ∫ g₀(y)/max(ρ,‖y‖) dy ≤ 1`, and `ρ → 0` gives
`∫ g₀(y)/‖y‖ dy ≤ 8π`.

Route (all available in the corpus):

* `Submission.BoseGases.scattering_bounds_ae` gives `0 ≤ ω` and `ω ≤ 1` a.e.;
* `Submission.BoseGases.scattering_newton_representation` (`Submission/NewtonRep.lean`)
  gives `ω x = (1/8π)∫_y (v y(1−ω y))‖x−y‖⁻¹ dy` for a.e. `x`;
* `Submission.BoseGases.shell_mean_e0` (`Submission/ShellMean.lean`) gives the
  spherical mean of the Newton kernel: `∫_{S²} ‖r•e₀ − s•u‖⁻¹ dσ(u) = 4π/max r s`
  for `r,s > 0` (and the formula extends to `s = 0`, where it is the constant
  `4π/r`); with `g₀` radial this turns the spherical average of the Newton
  potential at radius `ρ` into `(1/8π)∫ g₀(y)/max(ρ,‖y‖) dy`;
* combine with the a.e. bound `ω ≤ 1` on the sphere of radius `ρ` (Fubini in
  `(ρ, x)`; the sphere measure is finite, `σ(S²) = 4π`), obtaining the bound for
  a.e. `ρ > 0`; monotone convergence (`ρ → 0`, the integrand
  `g₀(y)/max(ρ,‖y‖)` increases to `g₀(y)/‖y‖` for `g₀ ≥ 0` a.e.) gives the
  `ℝ≥0∞`-inequality `∫⁻ g₀(y)/‖y‖ ≤ 8π`, hence integrability of
  `y ↦ g₀ y/‖y‖` and the value bound;
* the radial formula `Submission.RadialIntegral.integral_fun_norm_r3`
  (`∫_x G(‖x‖) = 4π∫₀^∞ r²G r`) with `G r = ψ r / r` converts the 3D integral
  into the profile integral (`4π∫₀^∞ r|ψ r|`), giving `∫₀^∞ r|g₀(r•e₀)|dr ≤ 2`. -/
theorem G0WeightedMoment {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    MeasureTheory.IntegrableOn
        (fun r : ℝ =>
          r * |Submission.BoseGases.g0 v h (r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))|)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ),
          r * |Submission.BoseGases.g0 v h (r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))|) ≤ 2 := by
  -- Formalisation note.  Rather than averaging the Newton representation over
  -- spheres (the route in the docstring), the corpus's maximum-principle bound
  -- on the *canonical profile* of the scattering solution is used:
  -- `canonicalProfile v ω R r = (1/2)(∫_{0<s≤r} s²·gprof + r∫_{s>r} s·gprof)`
  -- satisfies `0 ≤ canonicalProfile v ω R r ≤ r` for every `0 < r < R`
  -- (`Submission.BoseGases.canonicalProfile_le_r`, proved by the
  -- concave/maximum-principle argument of `Submission/T3Bounds.lean`).  Since the
  -- radial profile `gprof` of `g₀ = v(1−ω)` is nonnegative a.e. (from `0 ≤ v` and
  -- the a.e. bound `ω ≤ 1`), the first integral is nonnegative and the bound gives
  -- `∫_{s>r} s·gprof ≤ 2` for every `0 < r < R`; monotone convergence as `r ↓ 0`
  -- yields `∫_{s>0} s·|gprof| ≤ 2`.  The two abstract one-dimensional steps are
  -- `Work.BoseFixR.LatGreen.TailOfCanonical` and
  -- `Work.BoseFixR.LatGreen.MomentOfTail`.
  set G : ℝ → ℝ := fun s => Submission.BoseGases.radialProfile (Submission.BoseGases.g0 v h) s
    with hG
  have hmeas : AEStronglyMeasurable G (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [hG] using aestronglyMeasurable_g0profile h hvrad hR hv_supp
  have hInt2 : IntegrableOn (fun s : ℝ => s ^ 2 * |G s|) (Set.Ioi (0 : ℝ)) := by
    simpa only [hG] using integrableOn_sq_abs_g0profile h hvrad hR hv_supp
  have hnn : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ G s := by
    simpa only [hG] using radialProfile_g0_nonneg h hv hvrad hR hv_supp
  have hU : ∀ r : ℝ, 0 < r → r < R →
      (1 / 2) * ((∫ s in Set.Ioc (0 : ℝ) r, s ^ 2 * G s) +
        r * (∫ s in Set.Ioi r, s * G s)) ≤ r := by
    simpa only [hG] using canonicalProfile_le_r_g0 h hv hvrad hR hv_supp
  have hTail : ∀ r : ℝ, 0 < r → r < R → (∫ s in Set.Ioi r, s * G s) ≤ 2 :=
    TailOfCanonical (G := G) hR hInt2 hnn hU
  obtain ⟨hintG, hbdG⟩ := MomentOfTail (G := G) hR hmeas hInt2 hnn hTail
  have hpt : Set.EqOn (fun r : ℝ => r * |G r|)
      (fun r : ℝ =>
        r * |Submission.BoseGases.g0 v h (r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))|)
      (Set.Ioi (0 : ℝ)) := by
    intro r hr
    show r * |G r| = r * |Submission.BoseGases.g0 v h (r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))|
    rw [g0_smul_single_eq_profile hvrad h hr]
  constructor
  · exact hintG.congr_fun hpt measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hpt]
    exact hbdG

end Work.BoseFixR.LatGreen
