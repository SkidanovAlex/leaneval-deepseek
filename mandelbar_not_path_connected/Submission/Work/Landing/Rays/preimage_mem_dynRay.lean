import Mathlib
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.image_dynRay_subset
import Submission.Work.ParamRays.isDynBottcher_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Preimages of a point of a dynamic ray, on the ray of the half angle

For the antiholomorphic quadratic family `T_c(z) = z̄² + c` with a Böttcher coordinate `φ`
(`Work.ParamRays.IsDynBottcher c φ`), the map `T_c` sends the dynamic ray `R_c(θ)` into the
dynamic ray `R_c(angDouble θ)` (`image_dynRay_subset`).  This file proves the converse: every
point `w` of `R_c(angDouble θ)` different from the critical value `c` has a preimage on
`R_c(θ)`.

The critical value is genuinely exceptional: `c` itself may lie on a ray, while its only
preimage `0` is the critical point, which never escapes.

## The argument

Fix `w ∈ R_c(angDouble θ) ∖ {c}`, write `φ w = r · e^{2πi·angDouble θ}` with `r > 1`, and let
`s` be a square root of `w - c`, so that `z₁ = conj s` and `-z₁` are exactly the two preimages
of `w` under `T_c`.  Because `φ (T_c u) = conj (φ u)²`, we have
`φ (z₁)² = conj (φ w) = r · (e^{2πiθ})²`, so `φ z₁ = ± √r · e^{2πiθ}`; the two preimages have
opposite `φ`-values, `φ (-z₁) = - φ z₁`, since **a Böttcher coordinate is odd** on the escaping
set (`isDynBottcher_odd`, proved here from the preconnectedness of the escaping set).  Hence one
of `z₁`, `-z₁` has `φ`-value `√r · e^{2πiθ}`, i.e. lies on `R_c(θ)`, and that is our preimage.
-/

namespace Work.Landing.Rays

open scoped ComplexConjugate
open Classical Function Filter
open LeanEval.ComplexAnalysis (Tantibar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet orbit orbit_succ orbit_one_add
  orbit_zero escaping_of_lt_norm)
open Work.Landing (rayDirection radialRay dynRay angDouble Tantibar_apply)

noncomputable section

/-! ## Elementary dynamics of the preimage `-z` -/

/-- The conjugate of the ray direction at the doubled angle is the square of the ray direction:
`conj (e^{2πi·angDouble θ}) = (e^{2πiθ})²`. -/
theorem star_rayDirection_angDouble (θ : ℝ) :
    star (rayDirection (angDouble θ)) = rayDirection θ ^ 2 := by
  have h2 := congrArg star (ImageDynRay.rayDirection_angDouble θ)
  simpa using h2

/-- `T_c (-z) = T_c z`: the antiholomorphic quadratic is an even function. -/
theorem Tantibar_neg (c z : ℂ) : Tantibar c (-z) = Tantibar c z := by
  simp only [Tantibar, map_neg, neg_sq]

/-- The orbits of `z` and `-z` agree from the first iterate on. -/
theorem orbit_neg (c z : ℂ) (n : ℕ) : orbit c (-z) (n + 1) = orbit c z (n + 1) := by
  rw [orbit_one_add c (-z) n, orbit_one_add c z n, Tantibar_neg]

/-- If `z` escapes to infinity then so does `-z` (their orbits coincide from the first step). -/
theorem escaping_neg {c z : ℂ} (h : Escaping c z) : Escaping c (-z) := by
  simp only [Escaping] at h ⊢
  have h2 : (fun m : ℕ => ‖orbit c (-z) (m + 1)‖) = fun m : ℕ => ‖orbit c z (m + 1)‖ := by
    funext m; rw [orbit_neg]
  refine (Filter.tendsto_add_atTop_iff_nat (f := fun m => ‖orbit c (-z) m‖) 1).mp ?_
  rw [h2]
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun m => ‖orbit c z m‖) 1).mpr h

/-- A preimage of an escaping point is escaping. -/
theorem escaping_of_preimage {c z w : ℂ} (h : Tantibar c z = w) (hw : Escaping c w) :
    Escaping c z := by
  have horbit : ∀ n : ℕ, orbit c z (n + 1) = orbit c w n := by
    intro n
    induction n with
    | zero => rw [orbit_succ, orbit_zero, h, orbit_zero]
    | succ n ih => rw [orbit_succ c z (n + 1), orbit_succ c w n, ih]
  simp only [Escaping] at hw ⊢
  have h2 : (fun m : ℕ => ‖orbit c z (m + 1)‖) = fun m : ℕ => ‖orbit c w m‖ := by
    funext m; rw [horbit]
  refine (Filter.tendsto_add_atTop_iff_nat (f := fun m => ‖orbit c z m‖) 1).mp ?_
  rw [h2]; exact hw

/-! ## The Böttcher coordinate is odd on the escaping set -/

/-- The square of a Böttcher coordinate at `u` is the conjugate of its value at `T_c u`:
`φ u ² = conj (φ (T_c u))`. -/
theorem isDynBottcher_phi_sq {c : ℂ} {φ : ℂ → ℂ} (h : IsDynBottcher c φ) {u : ℂ}
    (hu : Escaping c u) : φ u ^ 2 = star (φ (Tantibar c u)) := by
  have h1 := congrArg star (h.2.1 u hu)
  simpa using h1.symm

/-- **A Böttcher coordinate is odd on the escaping set**: `φ (-z) = - φ z`.

The ratio `ρ z = φ (-z) / φ z` is continuous on the preconnected escaping set
(`Work.ParamRays.isPreconnected_escapingSet`), takes values in `{+1, -1}` (because
`φ (-z)² = conj (φ (T_c (-z))) = conj (φ (T_c z)) = φ z²`), and equals `-1` far away from the
origin by the asymptotic clause `φ w ~ w`. -/
theorem isDynBottcher_odd {c : ℂ} {φ : ℂ → ℂ} (h : IsDynBottcher c φ) {z : ℂ}
    (hz : Escaping c z) : φ (-z) = -φ z := by
  have hneg_maps : Set.MapsTo (fun z : ℂ => -z) (escapingSet c) (escapingSet c) :=
    fun z hz' => escaping_neg hz'
  have hcomp : ContinuousOn (fun z : ℂ => φ (-z)) (escapingSet c) :=
    h.1.comp continuous_neg.continuousOn hneg_maps
  have hFcont : ContinuousOn (fun z : ℂ => φ (-z) / φ z) (escapingSet c) :=
    hcomp.div h.1 (fun z hz' => h.ne_zero hz')
  have hpre : IsPreconnected ((fun z : ℂ => φ (-z) / φ z) '' escapingSet c) :=
    (Work.ParamRays.isPreconnected_escapingSet c).image _ hFcont
  have hsub : (fun z : ℂ => φ (-z) / φ z) '' escapingSet c ⊆
      {ζ : ℂ | ∃ n : ℕ, ζ ^ (2 ^ n) = 1} := by
    rintro ζ ⟨z, hz', rfl⟩
    refine ⟨1, ?_⟩
    have h2 : φ (-z) ^ 2 = φ z ^ 2 := by
      rw [isDynBottcher_phi_sq h (escaping_neg hz'), isDynBottcher_phi_sq h hz', Tantibar_neg]
    have hgoal : (φ (-z) / φ z) ^ 2 = 1 := by
      rw [div_pow, h2, div_self (pow_ne_zero 2 (h.ne_zero hz'))]
    simpa using hgoal
  have hsingle : ((fun z : ℂ => φ (-z) / φ z) '' escapingSet c).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre hsub
  -- a point of the escaping set far enough out that the asymptotic bound holds at `z₀` and `-z₀`
  obtain ⟨K, hKc, hKs⟩ := Filter.mem_cocompact.mp (h.2.2 (1 / 4) (by norm_num))
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
  set z₀ : ℂ := ((max R 0 + max 2 ‖c‖ + 1 : ℝ) : ℂ) with hz₀def
  have hz₀norm : ‖z₀‖ = max R 0 + max 2 ‖c‖ + 1 := by
    rw [hz₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    have := le_max_right R 0; have := le_max_left (2 : ℝ) ‖c‖; linarith
  have hz₀big : max 2 ‖c‖ < ‖z₀‖ := by
    rw [hz₀norm]; have := le_max_right R 0; linarith
  have hz₀esc : Escaping c z₀ := escaping_of_lt_norm c z₀ hz₀big
  have hz₀K : z₀ ∉ K := by
    intro hmem
    have h1 : ‖z₀‖ ≤ R := by
      have := Metric.mem_closedBall.mp (hR hmem); rwa [dist_zero_right] at this
    rw [hz₀norm] at h1
    have h3 := le_max_left R 0
    have h4 := le_max_left (2 : ℝ) ‖c‖
    linarith
  have hz₀Kneg : -z₀ ∉ K := by
    intro hmem
    have h1 : ‖-z₀‖ ≤ R := by
      have := Metric.mem_closedBall.mp (hR hmem); rwa [dist_zero_right] at this
    rw [norm_neg, hz₀norm] at h1
    have h3 := le_max_left R 0
    have h4 := le_max_left (2 : ℝ) ‖c‖
    linarith
  have hb1 : ‖φ z₀ - z₀‖ ≤ (1 / 4) * ‖z₀‖ := hKs hz₀K
  have hb2 : ‖φ (-z₀) - (-z₀)‖ ≤ (1 / 4) * ‖z₀‖ := by
    have h : ‖φ (-z₀) - (-z₀)‖ ≤ (1 / 4) * ‖(-z₀)‖ := hKs hz₀Kneg
    rwa [norm_neg] at h
  -- the value of the ratio at `z₀` is `-1`
  have hFz0 : φ (-z₀) / φ z₀ = -1 := by
    have hsq : (φ (-z₀) / φ z₀) ^ 2 = 1 := by
      have h2 : φ (-z₀) ^ 2 = φ z₀ ^ 2 := by
        rw [isDynBottcher_phi_sq h (escaping_neg hz₀esc), isDynBottcher_phi_sq h hz₀esc,
          Tantibar_neg]
      rw [div_pow, h2, div_self (pow_ne_zero 2 (h.ne_zero hz₀esc))]
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · exfalso
      have heq : φ (-z₀) = φ z₀ := (div_eq_one_iff_eq (h.ne_zero hz₀esc)).mp h1
      have hh : z₀ - (-z₀) = (z₀ - φ z₀) + (φ (-z₀) - (-z₀)) := by rw [heq]; ring
      have htri : ‖z₀ - (-z₀)‖ ≤ (1 / 4) * ‖z₀‖ + (1 / 4) * ‖z₀‖ := by
        calc ‖z₀ - (-z₀)‖ = ‖(z₀ - φ z₀) + (φ (-z₀) - (-z₀))‖ := by rw [hh]
          _ ≤ ‖z₀ - φ z₀‖ + ‖φ (-z₀) - (-z₀)‖ := norm_add_le _ _
          _ = ‖φ z₀ - z₀‖ + ‖φ (-z₀) - (-z₀)‖ := by rw [norm_sub_rev]
          _ ≤ (1 / 4) * ‖z₀‖ + (1 / 4) * ‖z₀‖ := by linarith
      have hlhs : ‖z₀ - (-z₀)‖ = 2 * ‖z₀‖ := by
        rw [show z₀ - (-z₀) = 2 * z₀ from by ring, norm_mul]
        simp
      have hpos : 0 < ‖z₀‖ := by
        rw [hz₀norm]; have := le_max_right R 0; have := le_max_left (2 : ℝ) ‖c‖; linarith
      linarith
    · exact h1
  have hval : φ (-z) / φ z = -1 := by
    have hthis : φ (-z) / φ z = φ (-z₀) / φ z₀ :=
      hsingle ⟨z, hz, rfl⟩ ⟨z₀, hz₀esc, rfl⟩
    rw [hthis, hFz0]
  have hfin : φ (-z) = -1 * φ z := (div_eq_iff (h.ne_zero hz)).mp hval
  simpa using hfin

/-! ## The preimage on the ray of the half angle -/

/-- The conjugate of a ray value at angle `angDouble θ` is the square of the direction at `θ`:
if `ρ² = r` then `conj (r · e^{2πi·angDouble θ}) = (ρ · e^{2πiθ})²`. -/
theorem star_mul_rayDirection_angDouble (r θ ρ : ℝ) (hρ : ρ ^ 2 = r) :
    star ((r : ℂ) * rayDirection (angDouble θ)) = (((ρ : ℂ) * rayDirection θ)) ^ 2 := by
  rw [star_mul, star_rayDirection_angDouble, ← starRingEnd_apply, Complex.conj_ofReal]
  rw [show (r : ℂ) = ((ρ : ℂ)) ^ 2 by rw [← Complex.ofReal_pow, hρ]]
  ring

/-- A point of the ray `R_c(angDouble θ)`, other than the critical value `c`, has a preimage under
`T_c` on the ray `R_c(θ)`.  The two preimages `z₁ z₂` of `w ≠ c` satisfy `φ z₁ = - φ z₂` (a
Böttcher coordinate is odd on the escaping set, `isDynBottcher_odd`), so exactly one of them lies
on the ray of angle `θ`. -/
theorem preimage_mem_dynRay {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ) {θ : ℝ}
    {w : ℂ} (hw : w ∈ Work.Landing.dynRay c φ ((Work.Landing.angDouble) θ)) (hwc : w ≠ c) :
    ∃ z : ℂ, z ∈ Work.Landing.dynRay c φ θ ∧ LeanEval.ComplexAnalysis.Tantibar c z = w := by
  obtain ⟨hwesc, r, hr1, hwr⟩ := hw
  -- the two preimages of `w`
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := by
    obtain ⟨s, hs⟩ := (isSquare_iff_exists_sq (w - c)).mp (Complex.isSquare (w - c))
    exact ⟨s, hs.symm⟩
  set z₁ : ℂ := star s with hz₁def
  have hTz₁ : Tantibar c z₁ = w := by
    rw [hz₁def, Tantibar_apply, star_star, hs]; ring
  have hz₁esc : Escaping c z₁ := escaping_of_preimage hTz₁ hwesc
  -- the level `ρ = √r`
  set ρ : ℝ := Real.sqrt r with hρdef
  have hρsq : ρ ^ 2 = r := by
    rw [hρdef]; exact Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one hr1))
  have hρ1 : 1 < ρ := by
    rw [hρdef]; exact (Real.lt_sqrt zero_le_one).mpr (by simpa using hr1)
  -- the conjugate of `φ w` is the square of `ρ · e^{2πiθ}`
  have hφsq : φ z₁ ^ 2 = (((ρ : ℂ) * rayDirection θ)) ^ 2 := by
    rw [isDynBottcher_phi_sq h hz₁esc, hTz₁, hwr]
    exact star_mul_rayDirection_angDouble r θ ρ hρsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hφsq with hcase | hcase
  · -- `z₁` itself lies on the ray
    exact ⟨z₁, ⟨hz₁esc, ⟨ρ, hρ1, hcase⟩⟩, hTz₁⟩
  · -- otherwise `-z₁` does
    refine ⟨-z₁, ⟨escaping_neg hz₁esc, ⟨ρ, hρ1, ?_⟩⟩, ?_⟩
    · rw [isDynBottcher_odd h hz₁esc, hcase, neg_neg]
    · rw [Tantibar_neg, hTz₁]

end

end Work.Landing.Rays
