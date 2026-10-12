import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.RadialIntegral
import Submission.RadialLaplacian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial test functions and the 1D reduction of the weak equation

Layer-3 (scattering) infrastructure.  A radial profile `ψ : ℝ → ℝ` with
compact support inside `(R,∞)` (where `R > 0`) produces a *radial* test
function `φ(x) := ψ ‖x‖` on `ℝ³ = EuclideanSpace ℝ (Fin 3)` which is smooth
and compactly supported with `tsupport φ ⊆ {x | R ≤ ‖x‖}` (smoothness at `0`
is automatic because `φ` vanishes on the whole open ball of radius `R`).

For such a test function the Laplacian is the classical radial Laplacian

    Δφ(x) = ψ''(‖x‖) + 2·ψ'(‖x‖)/‖x‖          (x ≠ 0),

so if a *radial* locally-integrable `w` (with radial profile `f := radialProfile w`)
satisfies the exterior weak-harmonic identity `∫ w·Δφ = 0` for every such
radial test function, then the polar/radial integral identity
(`Submission.RadialIntegral`) reduces it to the 1D statement

    ∫₀^∞ [ r²·f(r)·ψ''(r) + 2r·f(r)·ψ'(r) ] dr = 0 .

This is the bridge from the three-dimensional weak equation
(`ChallengeDeps.IsScatteringSolution` / `ScatHarmonic.scattering_harmonic_exterior`)
to the 1D calculus used in the classification `ω(x) = a/‖x‖` outside the
support of the potential and in the identification of the scattering length.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real RealInnerProductSpace

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- For a smooth profile `ψ` whose support lies in `(R,∞)` with `R > 0`, the
radial function `φ(x) := ψ ‖x‖` is smooth on all of `ℝ³`.  (Away from `0` it
is a smooth composition with the norm; on the ball `{‖x‖ < R}` it vanishes
identically because `ψ r = 0` whenever `r ≤ R`.) -/
lemma radialTest_contDiff {R : ℝ} {ψ : ℝ → ℝ} (hR : 0 < R)
    (hψ : ContDiff ℝ ∞ ψ) (hψsup : ∀ r : ℝ, ψ r ≠ 0 → R < r) :
    ContDiff ℝ ∞ (fun x : ℝ³ => ψ ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    -- x = 0: on the open ball of radius R (a neighbourhood of 0 since R > 0)
    -- the function vanishes identically, so it is smooth there.
    have hzero : (fun y : ℝ³ => ψ ‖y‖) =ᶠ[𝓝 (0 : ℝ³)] (fun _ : ℝ³ => (0 : ℝ)) := by
      rw [Filter.EventuallyEq]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ³) hR] with y hy
      have hyR : ‖y‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hy
      by_contra h
      have hlt : R < ‖y‖ := hψsup ‖y‖ h
      linarith
    exact ContDiffAt.congr_of_eventuallyEq
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ³ => (0 : ℝ))).contDiffAt) hzero
  · -- x ≠ 0: smooth composition of the smooth profile with the norm
    exact (hψ.contDiffAt (x := ‖x‖)).comp x (contDiffAt_norm ℝ (n := ∞) hx)

/-- For a compactly-supported profile `ψ`, the radial function
`φ(x) := ψ ‖x‖` has compact support: the support of `φ` is contained in the
preimage under the norm of the (bounded) support of `ψ`, hence inside a large
closed ball. -/
lemma radialTest_hasCompactSupport {R : ℝ} {ψ : ℝ → ℝ} (_hR : 0 < R)
    (hψcs : HasCompactSupport ψ) (_hψsup : ∀ r : ℝ, ψ r ≠ 0 → R < r) :
    HasCompactSupport (fun x : ℝ³ => ψ ‖x‖) := by
  rw [HasCompactSupport]
  have hK : IsCompact (tsupport ψ) := hψcs
  rcases hK.bddAbove with ⟨M, hM⟩
  have hsup_sub : Function.support (fun x : ℝ³ => ψ ‖x‖) ⊆
      (fun x : ℝ³ => ‖x‖) ⁻¹' (tsupport ψ) := by
    intro x hx
    have hφx : ψ ‖x‖ ≠ 0 := by simpa using (Function.mem_support.mp hx)
    have hnx0 : ‖x‖ ∈ Function.support ψ := Function.mem_support.mpr hφx
    exact Set.mem_preimage.mpr (by simpa [tsupport] using (subset_closure hnx0))
  have hcl_pre : IsClosed ((fun x : ℝ³ => ‖x‖) ⁻¹' (tsupport ψ)) :=
    (isClosed_tsupport ψ).preimage continuous_norm
  have htsub : tsupport (fun x : ℝ³ => ψ ‖x‖) ⊆
      (fun x : ℝ³ => ‖x‖) ⁻¹' (tsupport ψ) := by
    rw [tsupport]
    exact closure_minimal hsup_sub hcl_pre
  refine IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (0 : ℝ³) M)
    (isClosed_tsupport (fun x : ℝ³ => ψ ‖x‖)) ?_
  intro x hx
  have hnx : ‖x‖ ∈ tsupport ψ := by
    simpa using Set.mem_preimage.mp (htsub hx)
  have hle : ‖x‖ ≤ M := hM hnx
  simpa [Metric.mem_closedBall, dist_zero_right] using hle

/-- For a profile supported inside `(R,∞)`, the (topological) support of
`φ(x) := ψ ‖x‖` is contained in the exterior closed region `{x | R ≤ ‖x‖}`. -/
lemma radialTest_support_ge {R : ℝ} {ψ : ℝ → ℝ}
    (hψsup : ∀ r : ℝ, ψ r ≠ 0 → R < r) :
    tsupport (fun x : ℝ³ => ψ ‖x‖) ⊆ {x : ℝ³ | R ≤ ‖x‖} := by
  rw [tsupport]
  apply closure_minimal
  · intro x hx
    have hψx : ψ ‖x‖ ≠ 0 := by simpa using (Function.mem_support.mp hx)
    have hlt : R < ‖x‖ := hψsup ‖x‖ hψx
    exact le_of_lt hlt
  · exact isClosed_le (continuous_const : Continuous fun _ : ℝ³ => R) continuous_norm

/-- The Laplacian of the radial test function (classical radial Laplacian),
for `x ≠ 0`. -/
lemma radialTest_delta {ψ : ℝ → ℝ} {x : ℝ³} (hx : x ≠ 0) (hψ : ContDiffAt ℝ 2 ψ ‖x‖) :
    (Δ fun y : ℝ³ => ψ ‖y‖) x = deriv (deriv ψ) ‖x‖ + 2 * deriv ψ ‖x‖ / ‖x‖ := by
  exact laplacian_radial_norm (f := ψ) hx hψ

/-- **1D reduction of exterior weak harmonicity.**  Let `w` be radial (profile
`f := radialProfile w`) and locally integrable.  If `w` is weakly harmonic in
the exterior region `{x | R ≤ ‖x‖}` — meaning `∫ w·Δφ = 0` for every smooth
compactly-supported `φ` with `tsupport φ ⊆ {x | R ≤ ‖x‖}` — then for every
smooth compactly-supported radial profile `ψ` supported in `(R,∞)`:

    ∫₀^∞ [ r²·f(r)·ψ''(r) + 2r·f(r)·ψ'(r) ] dr = 0 .
-/
theorem radial_weakHarmonic_1D {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) (_hwli : LocallyIntegrable w)
    (hwh : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {x : ℝ³ | R ≤ ‖x‖} → (∫ x : ℝ³, w x * (Δ φ) x) = 0)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψcs : HasCompactSupport ψ)
    (hψsup : ∀ r : ℝ, ψ r ≠ 0 → R < r) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r) = 0 := by
  let φ : ℝ³ → ℝ := fun x => ψ ‖x‖
  let g : ℝ → ℝ := fun r => radialProfile w r * (deriv (deriv ψ) r + 2 * deriv ψ r / r)
  have hφ : ContDiff ℝ ∞ φ := by
    dsimp [φ]
    exact radialTest_contDiff hR hψ hψsup
  have hφcs : HasCompactSupport φ := by
    dsimp [φ]
    exact radialTest_hasCompactSupport hR hψcs hψsup
  have hφsupp : tsupport φ ⊆ {x : ℝ³ | R ≤ ‖x‖} := by
    dsimp [φ]
    exact radialTest_support_ge hψsup
  have h0 : (∫ x : ℝ³, w x * (Δ φ) x) = 0 := hwh φ hφ hφcs hφsupp
  -- pointwise identity on x ≠ 0:  w x = f‖x‖ and  Δφ x = ψ''‖x‖ + 2ψ'‖x‖/‖x‖
  have hpoint (x : ℝ³) (hx : x ≠ 0) : w x * (Δ φ) x = g ‖x‖ := by
    have hw : w x = radialProfile w ‖x‖ := radial_eq_profile hrad x
    have hψ2 : ContDiffAt ℝ 2 ψ ‖x‖ := (contDiff_infty.mp hψ 2).contDiffAt
    have hφx : (Δ φ) x = deriv (deriv ψ) ‖x‖ + 2 * deriv ψ ‖x‖ / ‖x‖ := by
      dsimp [φ]
      exact radialTest_delta (x := x) hx hψ2
    dsimp [g]
    rw [hw, hφx]
  -- the two integrands agree a.e. (everywhere except possibly at x = 0)
  have h_ae : (fun x : ℝ³ => w x * (Δ φ) x) =ᵐ[volume] (fun x : ℝ³ => g ‖x‖) := by
    change ∀ᵐ (x : ℝ³) ∂(volume : Measure ℝ³),
      w x * (Δ φ) x = g ‖x‖
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null
    · intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hx0
      exact hx (hpoint x hx0)
    · exact MeasureTheory.NullSingletonClass.measure_singleton (x := (0 : ℝ³))
  have hcong : (∫ x : ℝ³, w x * (Δ φ) x) = (∫ x : ℝ³, g ‖x‖) :=
    MeasureTheory.integral_congr_ae h_ae
  -- the radial (polar) integral identity on ℝ³
  have hmain : (∫ x : ℝ³, w x * (Δ φ) x) = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := by
    rw [hcong]
    exact integral_fun_norm_r3 (g := g)
  -- on Ioi 0 the two 1D integrands coincide pointwise for every r
  have hfun : (fun r : ℝ => r ^ 2 * g r) = (fun r : ℝ =>
      r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r) := by
    funext r
    by_cases hr : r = 0
    · subst r
      simp [g]
    · dsimp [g]
      field_simp [hr]
  have hI : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) =
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r) := by
    exact congrArg (fun h : ℝ → ℝ => ∫ r : ℝ in Set.Ioi (0 : ℝ), h r) hfun
  have hfact : (4 * π : ℝ) ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero
  have hprod : (4 * π : ℝ) * (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r) = 0 := by
    calc
      (4 * π : ℝ) * (∫ r in Set.Ioi (0 : ℝ),
          r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r)
          = (4 * π : ℝ) * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) := by rw [hI]
      _ = ∫ x : ℝ³, w x * (Δ φ) x := by rw [hmain]
      _ = 0 := h0
  exact (mul_eq_zero.mp hprod).resolve_left hfact

end Submission.BoseGases
