import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.dchord_symplectic
import Submission.Work.RPB.B2.argLift_deriv
import Submission.Work.RPB.B2.hasDerivAt_chordPS

/-!
# The chord annulus is Lagrangian (`Work.RPB.B2.chordSurf_lagrangian`)

For a curve isotopy `CI` and a chord phase `a` of it, the chord annulus
`Π τ t r = chordSurf CI.c a τ t r` (the chord `(c τ (t+r), c τ (t-r))` seen in `PS` through
`chordPS`, with `a τ t r` a lift of `arg (c τ (t+r) - c τ (t-r))`) satisfies

`symp (∂_t Π) (∂_r Π) = 0`.

## Proof

By the chain rule, the two partial derivatives are the image under the linearisation `dchord` of
`chordPS` of the pairs of endpoint velocities:
`∂_t Π = dchord (c'(t+r)) (c'(t-r))` and `∂_r Π = dchord (c'(t+r)) (-(c'(t-r)))` at `(τ,t,r)`;
this uses that the derivative of the phase is forced by the chord relation
`c τ (t+r) - c τ (t-r) = ‖…‖ · exp (a · I)` (`argLift_deriv`).  Then
`Work.RPV.dchord_symplectic` identifies `symp` of two `dchord` values with `ωC ⊕ ωC`, and
`ωC x x = ωC y (-y) = 0`.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-- The section `u ↦ c τ u` of a curve family is smooth. -/
theorem contDiff_curve_section (CI : Work.RPV.CurveIsotopy) (τ : ℝ) :
    ContDiff ℝ ∞ (fun u : ℝ => CI.c τ u) :=
  CI.smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun u : ℝ => (τ, u)))

/-- The section `u ↦ c τ u` of a curve family has derivative `deriv (c τ) u` at `u`. -/
theorem hasDerivAt_curve_section (CI : Work.RPV.CurveIsotopy) (τ u : ℝ) :
    HasDerivAt (fun u : ℝ => CI.c τ u) (deriv (CI.c τ) u) u :=
  (show DifferentiableAt ℝ (fun u : ℝ => CI.c τ u) u from
    ((contDiff_curve_section CI τ).differentiable (by simp)).differentiableAt).hasDerivAt

/-- A `C^∞` function on the closed strip `[0,1] × ℝ × [0,π]` is `C^∞` at every point of the
strip along the `t`-sections (the `t`-coordinate is free, so the interior requirement in `τ` is
irrelevant). -/
theorem contDiffAt_phase_section_fst {a : ℝ → ℝ → ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi))
    {τ t r : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ∞ (fun s : ℝ => a τ s r) t := by
  have hmem : ((τ, (t, r)) : ℝ × (ℝ × ℝ)) ∈
      Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hτ, trivial, hr.1, hr.2⟩
  have hγ : ContDiff ℝ ∞ (fun u : ℝ => ((τ, (u, r)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have hmap : Set.MapsTo (fun u : ℝ => ((τ, (u, r)) : ℝ × (ℝ × ℝ))) Set.univ
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
    fun u _ => ⟨hτ, trivial, hr.1, hr.2⟩
  exact ((ha.contDiffWithinAt hmem).comp t hγ.contDiffWithinAt hmap).contDiffAt Filter.univ_mem

/-- A `C^∞` function on the closed strip `[0,1] × ℝ × [0,π]` is `C^∞` at interior points along
the `r`-sections. -/
theorem contDiffAt_phase_section_snd {a : ℝ → ℝ → ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi))
    {τ t r : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ∞ (fun s : ℝ => a τ t s) r := by
  have hmem : ((τ, (t, r)) : ℝ × (ℝ × ℝ)) ∈
      Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hτ, trivial, hr.1.le, hr.2.le⟩
  have hγ : ContDiffWithinAt ℝ ∞ (fun u : ℝ => ((τ, (t, u)) : ℝ × (ℝ × ℝ)))
      (Set.Ioo (0 : ℝ) Real.pi) r := (by fun_prop : ContDiff ℝ ∞ _).contDiffWithinAt
  have hmap : Set.MapsTo (fun u : ℝ => ((τ, (t, u)) : ℝ × (ℝ × ℝ))) (Set.Ioo (0 : ℝ) Real.pi)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
    fun u hu => ⟨hτ, trivial, hu.1.le, hu.2.le⟩
  exact ((ha.contDiffWithinAt hmem).comp r hγ hmap).contDiffAt (Ioo_mem_nhds hr.1 hr.2)

/-- The two endpoints of a chord of the curve family at parameter `r ∈ (0,π)` are distinct. -/
theorem chord_endpoints_ne (CI : Work.RPV.CurveIsotopy) {τ t r : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    CI.c τ (t + r) ≠ CI.c τ (t - r) := by
  intro h
  obtain ⟨m, hm⟩ := CI.inj τ hτ (t + r) (t - r) h
  have h2 : r = Real.pi * (-(m : ℤ) : ℝ) := by
    have : r = -Real.pi * (m : ℝ) := by linarith [hm]
    rw [this]; ring
  have hpos : (0 : ℝ) < (-(m : ℤ) : ℝ) := by nlinarith [Real.pi_pos, hr.1, h2]
  have hlt : (-(m : ℤ) : ℝ) < 1 := by nlinarith [Real.pi_pos, hr.2, h2]
  have hone : (1 : ℤ) ≤ -m := by
    have : (0 : ℤ) < -m := by exact_mod_cast hpos
    omega
  have hcast : (1 : ℝ) ≤ -(m : ℝ) := by
    have : ((1 : ℤ) : ℝ) ≤ ((-m : ℤ) : ℝ) := by exact_mod_cast hone
    simpa using this
  linarith

theorem chordSurf_lagrangian (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      Work.RPV.symp (deriv (fun s => Work.RPB.chordSurf CI.c a τ s r) t)
        (deriv (fun s => Work.RPB.chordSurf CI.c a τ t s) r) = 0 := by
  intro τ hτ t r hr
  obtain ⟨hr0, hrπ⟩ := hr
  -- the chord is nondegenerate
  have hne : CI.c τ (t + r) ≠ CI.c τ (t - r) := chord_endpoints_ne CI hτ ⟨hr0, hrπ⟩
  -- ## the `t`-direction
  have hphase_t : ContDiffAt ℝ ∞ (fun s : ℝ => a τ s r) t :=
    contDiffAt_phase_section_fst ha.1 hτ ⟨hr0.le, hrπ.le⟩
  have hzt : HasDerivAt (fun s : ℝ => CI.c τ (s + r)) (deriv (CI.c τ) (t + r)) t :=
    (hasDerivAt_curve_section CI τ (t + r)).comp_add_const t r
  have hwt : HasDerivAt (fun s : ℝ => CI.c τ (s - r)) (deriv (CI.c τ) (t - r)) t :=
    (hasDerivAt_curve_section CI τ (t - r)).comp_sub_const t r
  have hAt : HasDerivAt (fun s : ℝ => a τ s r) (deriv (fun s : ℝ => a τ s r) t) t :=
    (hphase_t.differentiableAt (by simp)).hasDerivAt
  have hargt : ∀ᶠ s in nhds t, CI.c τ (s + r) - CI.c τ (s - r) =
      (‖CI.c τ (s + r) - CI.c τ (s - r)‖ : ℂ) * Complex.exp (a τ s r * Complex.I) :=
    Filter.Eventually.of_forall (fun s => ha.2.1 τ hτ s r ⟨hr0, hrπ⟩)
  have hA't : deriv (fun s : ℝ => a τ s r) t =
      ((deriv (CI.c τ) (t + r) - deriv (CI.c τ) (t - r)) /
        (CI.c τ (t + r) - CI.c τ (t - r))).im :=
    argLift_deriv (z := fun s : ℝ => CI.c τ (s + r)) (w := fun s : ℝ => CI.c τ (s - r))
      (A := fun s : ℝ => a τ s r) (ζ := deriv (CI.c τ) (t + r)) (η := deriv (CI.c τ) (t - r))
      (A' := deriv (fun s : ℝ => a τ s r) t) hzt hwt hAt hne hargt
  have hdt : HasDerivAt (fun s : ℝ => Work.RPB.chordSurf CI.c a τ s r)
      (Work.RPV.dchord (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r)
        (deriv (CI.c τ) (t + r)) (deriv (CI.c τ) (t - r))) t := by
    have := hasDerivAt_chordPS (z := fun s : ℝ => CI.c τ (s + r)) (w := fun s : ℝ => CI.c τ (s - r))
      (A := fun s : ℝ => a τ s r) (ζ := deriv (CI.c τ) (t + r)) (η := deriv (CI.c τ) (t - r))
      (A' := deriv (fun s : ℝ => a τ s r) t) hzt hwt hAt hA't
    simpa [Work.RPB.chordSurf] using this
  -- ## the `r`-direction
  have hphase_r : ContDiffAt ℝ ∞ (fun s : ℝ => a τ t s) r :=
    contDiffAt_phase_section_snd ha.1 hτ ⟨hr0, hrπ⟩
  have hzr : HasDerivAt (fun s : ℝ => CI.c τ (t + s)) (deriv (CI.c τ) (t + r)) r :=
    (hasDerivAt_curve_section CI τ (t + r)).comp_const_add t r
  have hwr : HasDerivAt (fun s : ℝ => CI.c τ (t - s)) (-(deriv (CI.c τ) (t - r))) r :=
    (hasDerivAt_curve_section CI τ (t - r)).comp_const_sub t r
  have hAr : HasDerivAt (fun s : ℝ => a τ t s) (deriv (fun s : ℝ => a τ t s) r) r :=
    (hphase_r.differentiableAt (by simp)).hasDerivAt
  have hargr : ∀ᶠ s in nhds r, CI.c τ (t + s) - CI.c τ (t - s) =
      (‖CI.c τ (t + s) - CI.c τ (t - s)‖ : ℂ) * Complex.exp (a τ t s * Complex.I) := by
    filter_upwards [Ioo_mem_nhds hr0 hrπ] with s hs
    exact ha.2.1 τ hτ t s hs
  have hA'r : deriv (fun s : ℝ => a τ t s) r =
      ((deriv (CI.c τ) (t + r) - -deriv (CI.c τ) (t - r)) /
        (CI.c τ (t + r) - CI.c τ (t - r))).im :=
    argLift_deriv (z := fun s : ℝ => CI.c τ (t + s)) (w := fun s : ℝ => CI.c τ (t - s))
      (A := fun s : ℝ => a τ t s) (ζ := deriv (CI.c τ) (t + r)) (η := -(deriv (CI.c τ) (t - r)))
      (A' := deriv (fun s : ℝ => a τ t s) r) hzr hwr hAr hne hargr
  have hdr : HasDerivAt (fun s : ℝ => Work.RPB.chordSurf CI.c a τ t s)
      (Work.RPV.dchord (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r)
        (deriv (CI.c τ) (t + r)) (-(deriv (CI.c τ) (t - r)))) r := by
    have := hasDerivAt_chordPS (z := fun s : ℝ => CI.c τ (t + s)) (w := fun s : ℝ => CI.c τ (t - s))
      (A := fun s : ℝ => a τ t s) (ζ := deriv (CI.c τ) (t + r)) (η := -(deriv (CI.c τ) (t - r)))
      (A' := deriv (fun s : ℝ => a τ t s) r) hzr hwr hAr hA'r
    simpa [Work.RPB.chordSurf] using this
  -- ## the symplectic pairing
  rw [hdt.deriv, hdr.deriv,
    Work.RPV.dchord_symplectic (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r) hne
      (ha.2.1 τ hτ t r ⟨hr0, hrπ⟩)]
  simp [Work.RPV.ωC]
  ring

end Work.RPB.B2
