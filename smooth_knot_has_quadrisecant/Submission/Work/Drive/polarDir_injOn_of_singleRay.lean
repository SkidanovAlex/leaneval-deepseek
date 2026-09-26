import Mathlib
import Submission.Work.Drive.polarDataOfStarShaped
import Submission.Work.Drive.angleLift_singleRay

/-!
# Injectivity of the direction map from positivity plus ONE ray

`Work.Drive.polarData_of_starShaped` (`polarDataOfStarShaped.lean`) derives the polar data of a
planar curve from the *injectivity* of its direction map plus the positivity of its angular
velocity.  The injectivity hypothesis, however, is used in the angle-lift proof
(`Work.Drive.exists_cInf_angle_lift`) at exactly one place: to rule out a second hit of the *single*
direction `(1,0)` inside one period.

This file records the honest consequence: **if the angular velocity about the centre is positive
everywhere and the single ray in the base direction `u` is met only at the base parameter, then the
direction map is injective on one period.**

The proof: `Work.Drive.angleLift_singleRay` gives a `C^∞` `ψ` with `ψ 0 = 0`,
`ψ (t + period) = ψ t + period` and `polarDir = (cos ∘ ψ, sin ∘ ψ)`; the positivity of the angular
velocity makes `ψ` strictly increasing (chain rule, as in `polarData_of_starShaped`).  Two parameters
with the same direction have `ψ`-values differing by a multiple of `2π` (`Real.cos_eq_cos_iff`,
`Real.sin_eq_sin_iff`/`Real.sin_eq_zero_iff` in the anti-parallel case), while the strict
monotonicity and the shift bound the difference to `[0, 2π)`: hence the difference is `0`, and `ψ`
is injective.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The direction map is injective on one period as soon as one ray is met once** (and the
angular velocity about the centre is positive everywhere). -/
theorem polarDir_injOn_of_singleRay {N : ℝ → Space} {c u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hN : ContDiff ℝ cInfT N) (hNper : Function.Periodic N period)
    (hplane : ∀ t : ℝ,
      N t - c = inner ℝ (N t - c) u • u + inner ℝ (N t - c) v • v)
    (hne : ∀ t : ℝ, N t ≠ c)
    (h0 : polarDir N c u v 0 = (1, 0))
    (hsingle : ∀ t : ℝ, 0 < t → t < period → polarDir N c u v t ≠ (1, 0))
    (hpos : ∀ t : ℝ,
      0 < polarCoord N c u t * deriv (polarCoord N c v) t
        - polarCoord N c v t * deriv (polarCoord N c u) t) :
    Set.InjOn (polarDir N c u v) (Set.Ico (0 : ℝ) period) := by
  have ha_sm : ContDiff ℝ cInfT (polarCoord N c u) := polarCoord_smooth c u hN hne
  have hb_sm : ContDiff ℝ cInfT (polarCoord N c v) := polarCoord_smooth c v hN hne
  have hnpos : ∀ t : ℝ, polarRad N c t ≠ 0 := fun t => ne_of_gt (polarRad_pos c hne t)
  have hnorm : ∀ t : ℝ, polarCoord N c u t ^ 2 + polarCoord N c v t ^ 2 = 1 := by
    intro t
    have hp := norm_sq_eq_coords hu hv huv (hplane t)
    have hlt : polarRad N c t ≠ 0 := hnpos t
    have hlam2 : polarRad N c t ^ 2
        = (inner ℝ (N t - c) u) ^ 2 + (inner ℝ (N t - c) v) ^ 2 := by
      rw [polarRad]; exact hp
    have ha' : polarCoord N c u t = inner ℝ (N t - c) u / polarRad N c t := by
      rw [polarCoord, polarRad]
    have hb' : polarCoord N c v t = inner ℝ (N t - c) v / polarRad N c t := by
      rw [polarCoord, polarRad]
    rw [ha', hb', div_pow, div_pow, ← add_div,
      div_eq_one_iff_eq (by positivity), hlam2]
  have h0' : polarCoord N c u 0 = 1 ∧ polarCoord N c v 0 = 0 := by
    have h := h0
    rw [polarDir] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hper' : ∀ t : ℝ, polarCoord N c u (t + period) = polarCoord N c u t ∧
      polarCoord N c v (t + period) = polarCoord N c v t := by
    intro t
    constructor <;>
      · rw [polarCoord, polarCoord, hNper t]
  have hsingle' : ∀ t : ℝ, 0 < t → t < period →
      ¬ (polarCoord N c u t = 1 ∧ polarCoord N c v t = 0) := by
    intro t ht ht'
    have h := hsingle t ht ht'
    intro hcon
    exact h (by rw [polarDir]; exact Prod.ext hcon.1 hcon.2)
  obtain ⟨psi, hpsi_sm, hpsi0, hpsishift, hpsisincos⟩ :=
    angleLift_singleRay ha_sm hb_sm hnorm h0' hper' hsingle' hpos
  have hcos : ∀ t : ℝ, polarCoord N c u t = Real.cos (psi t) := fun t => (hpsisincos t).1
  have hsin : ∀ t : ℝ, polarCoord N c v t = Real.sin (psi t) := fun t => (hpsisincos t).2
  -- the angle is strictly increasing (chain rule, as in `polarData_of_starShaped`)
  have hpsi_diff : ∀ t : ℝ, DifferentiableAt ℝ psi t :=
    fun t => (hpsi_sm.differentiable cInfT_ne_zero).differentiableAt
  have hderiv_cos : ∀ t : ℝ, deriv (fun s : ℝ => Real.cos (psi s)) t
      = -Real.sin (psi t) * deriv psi t := by
    intro t
    exact (((Real.hasDerivAt_cos (psi t)).comp t (hpsi_diff t).hasDerivAt)).deriv
  have hderiv_sin : ∀ t : ℝ, deriv (fun s : ℝ => Real.sin (psi s)) t
      = Real.cos (psi t) * deriv psi t := by
    intro t
    exact (((Real.hasDerivAt_sin (psi t)).comp t (hpsi_diff t).hasDerivAt)).deriv
  have hpsideriv : ∀ t : ℝ, deriv psi t
      = polarCoord N c u t * deriv (polarCoord N c v) t
        - polarCoord N c v t * deriv (polarCoord N c u) t := by
    intro t
    have hda : deriv (polarCoord N c u) t = deriv (fun s : ℝ => Real.cos (psi s)) t := by
      rw [show polarCoord N c u = fun s : ℝ => Real.cos (psi s) from
        funext fun s => hcos s]
    have hdb : deriv (polarCoord N c v) t = deriv (fun s : ℝ => Real.sin (psi s)) t := by
      rw [show polarCoord N c v = fun s : ℝ => Real.sin (psi s) from
        funext fun s => hsin s]
    rw [hda, hdb, hderiv_cos t, hderiv_sin t, hcos t, hsin t]
    have hs : Real.sin (psi t) ^ 2 + Real.cos (psi t) ^ 2 = 1 := Real.sin_sq_add_cos_sq (psi t)
    have hexp : Real.cos (psi t) * (Real.cos (psi t) * deriv psi t)
        - Real.sin (psi t) * (-Real.sin (psi t) * deriv psi t)
        = (Real.sin (psi t) ^ 2 + Real.cos (psi t) ^ 2) * deriv psi t := by ring
    rw [hexp, hs, one_mul]
  have hpsi_mono : StrictMono psi :=
    strictMono_of_deriv_pos (fun t => by rw [hpsideriv t]; exact hpos t)
  -- the final argument
  intro t₁ ht₁ t₂ ht₂ heq
  have hc : Real.cos (psi t₁) = Real.cos (psi t₂) := by
    rw [← hcos t₁, ← hcos t₂]
    exact congrArg Prod.fst heq
  have hs : Real.sin (psi t₁) = Real.sin (psi t₂) := by
    rw [← hsin t₁, ← hsin t₂]
    exact congrArg Prod.snd heq
  have hmod : ∃ n : ℤ, psi t₂ - psi t₁ = (n : ℝ) * (2 * Real.pi) := by
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hc
    · refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      ring
    · -- the anti-parallel case: `sin (psi t₁) = 0`, so both angles are multiples of `π`
      have hs0 : Real.sin (psi t₁) = 0 := by
        have hanti : Real.sin (psi t₂) = -Real.sin (psi t₁) := by
          rw [hk, show (2:ℝ) * (k:ℝ) * Real.pi - psi t₁ = (k:ℝ) * (2 * Real.pi) - psi t₁
            by ring]
          exact Real.sin_int_mul_two_pi_sub (psi t₁) k
        linarith
      obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp hs0
      refine ⟨k - j, ?_⟩
      rw [hk, ← hj]
      push_cast
      ring
  -- the difference lies in `[0, 2π)`
  have hbnd : ∀ {a : ℝ}, a ∈ Set.Ico (0 : ℝ) period →
      psi a - psi 0 < 2 * Real.pi := by
    intro a ha
    have hper : period = 2 * Real.pi := rfl
    have h2 : psi a < psi (0 + period) := hpsi_mono (by linarith [ha.2])
    rw [hpsishift 0, hper] at h2
    linarith
  have hkey : psi t₂ - psi t₁ = 0 := by
    rcases le_total t₁ t₂ with hle | hle
    · obtain ⟨n, hn⟩ := hmod
      have h0b : 0 ≤ psi t₂ - psi t₁ := by
        have := hpsi_mono.monotone hle; linarith
      have h1b : psi t₂ - psi t₁ < 2 * Real.pi := by
        have h5 := hbnd (a := t₂) ht₂
        have h4 : 0 ≤ psi t₁ - psi 0 := by
          have := hpsi_mono.monotone ht₁.1; linarith
        linarith
      have hn0 : n = 0 := by
        have hA : (0 : ℝ) ≤ (n : ℝ) := by nlinarith [h0b, hn, Real.pi_pos]
        have hB : (n : ℝ) < 1 := by nlinarith [h1b, hn, Real.pi_pos]
        have hn0' : (0 : ℤ) ≤ n := by exact_mod_cast hA
        have hn1 : n < 1 := by exact_mod_cast hB
        omega
      rw [hn, hn0]; ring
    · obtain ⟨n, hn⟩ := hmod
      have h0b : 0 ≤ -(psi t₂ - psi t₁) := by
        have := hpsi_mono.monotone hle; linarith
      have h1b : -(psi t₂ - psi t₁) < 2 * Real.pi := by
        have h6 := hbnd (a := t₁) ht₁
        have h4 : 0 ≤ psi t₂ - psi 0 := by
          have := hpsi_mono.monotone ht₂.1; linarith
        linarith
      have hn0 : n = 0 := by
        have hA : (0 : ℝ) ≤ -(n : ℝ) := by nlinarith [h0b, hn, Real.pi_pos]
        have hB : (-(n : ℝ)) < 1 := by nlinarith [h1b, hn, Real.pi_pos]
        have hn0' : (0 : ℤ) ≤ -n := by exact_mod_cast hA
        have hn1 : -n < 1 := by exact_mod_cast hB
        omega
      rw [hn, hn0]; ring
  exact hpsi_mono.injective (by linarith)

end Work.Drive
