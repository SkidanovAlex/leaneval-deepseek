import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordPhase_exists
import Submission.Work.RPB.B1.windInt_lift

/-!
# B5: the signed area of the chord loop of a constant chord length family

For a curve isotopy `CI` and a chord-length parameter `σ < 0` (so the chords have length
`2√(-σ)`), any `2π`-periodic family of chord parameters `r τ · σ` with

`‖CI.c τ (t + r τ t σ) - CI.c τ (t - r τ t σ)‖ ^ 2 = -4 σ` (constant length,

`r τ · σ ∈ (0,π)`) traces a closed *chord loop* `γ τ σ t = c τ (t + r) - c τ (t - r)` whose signed
area is exactly the area of the disc of radius `√(-σ)`:

`Work.RPB.B5.chordLoop_area`:  `signedArea (γ τ σ) = -4 π σ = π (2√(-σ))²`.

The proof is topological and uses the two halves of the route's chord-phase/winding machinery:

* the chord phase `a` of `Work.RPB.B2.chordPhase_exists` gives the *explicit continuous argument
  lift* `θ t = a τ t (r τ t σ)` of `γ`, with the monodromy `θ (t + 2π) = θ t + 2π`;
* `Work.RPB.B1.windInt_lift` then evaluates the logarithmic integral
  `∮ Im (γ'/γ) = θ (2π) - θ 0 = 2π`, i.e. the chord loop winds once about `0`;
* since `‖γ t‖² = -4 σ` is constant, `conj (γ t) * γ' t = ‖γ t‖² · (γ' t / γ t)`, so
  `signedArea γ = (1/2) · (-4 σ) · 2π = -4 π σ`.

No circularity is involved: the monodromy `+2π` of the chord phase is exactly the statement that
the chord loop of a curve starting at the unit circle has winding number one, which is why the
identity holds for every `τ ∈ [0,1]` and not merely for circles.
-/

namespace Work.RPB.B5

theorem chordLoop_area (CI : Work.RPV.CurveIsotopy) (r : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hrpos : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      0 < r τ t σ ∧ r τ t σ < Real.pi)
    (hrsm : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0,
      ContDiff ℝ 2 (fun t : ℝ => r τ t σ))
    (hrper : ∀ τ t σ, r τ (t + 2*Real.pi) σ = r τ t σ)
    (hlev : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ‖CI.c τ (t + r τ t σ) - CI.c τ (t - r τ t σ)‖ ^ 2 = -4 * σ) :
    ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0,
      Work.RPB.signedArea (fun t => CI.c τ (t + r τ t σ) - CI.c τ (t - r τ t σ))
        = -4 * Real.pi * σ := by
  intro τ hτ σ hσ
  obtain ⟨a, ha⟩ := Work.RPB.B2.chordPhase_exists CI
  let ρ : ℝ → ℝ := fun t => r τ t σ
  let γ : ℝ → ℂ := fun t => CI.c τ (t + ρ t) - CI.c τ (t - ρ t)
  change Work.RPB.signedArea γ = -4 * Real.pi * σ
  have hρpos : ∀ t, 0 < ρ t := fun t => (hrpos τ hτ t σ hσ).1
  have hρlt : ∀ t, ρ t < Real.pi := fun t => (hrpos τ hτ t σ hσ).2
  have hρ1 : ContDiff ℝ 1 ρ := (hrsm τ hτ σ hσ).of_le (by norm_num)
  have hρc : Continuous ρ := hρ1.continuous
  have hρper : ∀ t, ρ (t + 2 * Real.pi) = ρ t := fun t => hrper τ t σ
  have hγ1 : ContDiff ℝ 1 γ := by
    have hs : ContDiff ℝ 1 (fun z : ℝ × ℝ => CI.c z.1 z.2) := CI.smooth.of_le (by simp)
    exact (hs.comp (ContDiff.prodMk contDiff_const (contDiff_id.add hρ1))).sub
      (hs.comp (ContDiff.prodMk contDiff_const (contDiff_id.sub hρ1)))
  -- `γ` is `2π`-periodic (periodicity of `ρ` and of `CI.c τ`)
  have hγper : ∀ t, γ (t + 2 * Real.pi) = γ t := by
    intro t
    have hu : t + 2 * Real.pi + ρ (t + 2 * Real.pi) = (t + ρ t) + 2 * Real.pi := by
      rw [hρper t]; ring
    have hv : t + 2 * Real.pi - ρ (t + 2 * Real.pi) = (t - ρ t) + 2 * Real.pi := by
      rw [hρper t]; ring
    have h1 := CI.per τ (t + ρ t)
    have h2 := CI.per τ (t - ρ t)
    simp only [γ, hu, hv, h1, h2]
  -- the constant modulus of `γ`: `‖γ t‖² = -4σ > 0`
  have hlevγ : ∀ t, ‖γ t‖ ^ 2 = -4 * σ := fun t => hlev τ hτ t σ hσ
  have hγne : ∀ t, γ t ≠ 0 := by
    intro t h0
    have h := hlevγ t
    rw [h0, norm_zero] at h
    norm_num at h
    linarith [hσ.2]
  -- the explicit argument lift of `γ`, from the chord phase `a`
  let θ : ℝ → ℝ := fun t => a τ t (ρ t)
  have hθcont : Continuous θ := by
    have hA : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) := ha.1.continuousOn
    have hg : Continuous (fun t : ℝ => (τ, t, ρ t)) :=
      continuous_const.prodMk (continuous_id.prodMk hρc)
    refine hA.comp_continuous hg (fun t => ?_)
    exact ⟨hτ, Set.mem_univ _, ⟨(hρpos t).le, (hρlt t).le⟩⟩
  have hrepr : ∀ t, γ t = (‖γ t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := by
    intro t
    have h := ha.2.1 τ hτ t (ρ t) ⟨hρpos t, hρlt t⟩
    simpa [Work.RPB.chordVec, γ, θ] using h
  -- the chord loop winds once around the origin
  have hint : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv γ t / γ t).im = 2 * Real.pi := by
    obtain ⟨-, hlift⟩ := Work.RPB.B1.windInt_lift γ hγ1 hγper hγne
    have h := hlift θ hθcont hrepr
    have hθdiff : θ (2 * Real.pi) - θ 0 = 2 * Real.pi := by
      have hm := ha.2.2.1 τ hτ 0 (ρ 0) ⟨hρpos 0, hρlt 0⟩
      have h2 : θ (2 * Real.pi) = a τ 0 (ρ 0) + 2 * Real.pi := by
        have hρ0 : ρ (2 * Real.pi) = ρ 0 := by simpa using hρper 0
        have hm' : a τ (2 * Real.pi) (ρ 0) = a τ 0 (ρ 0) + 2 * Real.pi := by
          simpa using hm
        show a τ (2 * Real.pi) (ρ (2 * Real.pi)) = a τ 0 (ρ 0) + 2 * Real.pi
        rw [hρ0, hm']
      have h3 : θ 0 = a τ 0 (ρ 0) := rfl
      rw [h2, h3]
      ring
    rw [h, hθdiff]
  -- `conj γ · γ' = ‖γ‖² · (γ'/γ)` with the modulus `‖γ t‖² = -4σ`
  have hpoint : ∀ t, ((starRingEnd ℂ) (γ t) * deriv γ t).im
      = (-4 * σ) * (deriv γ t / γ t).im := by
    intro t
    have hnm : Complex.normSq (γ t) = -4 * σ := by
      rw [Complex.normSq_eq_norm_sq]; exact hlevγ t
    have hz : γ t ≠ 0 := hγne t
    have h1 : (starRingEnd ℂ) (γ t) * deriv γ t
        = ((-4 * σ : ℝ) : ℂ) * (deriv γ t / γ t) := by
      have h2 : (starRingEnd ℂ) (γ t) * γ t = ((-4 * σ : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, hnm]
      calc (starRingEnd ℂ) (γ t) * deriv γ t
          = (starRingEnd ℂ) (γ t) * (γ t * (deriv γ t / γ t)) := by
            rw [mul_div_cancel₀ (deriv γ t) hz]
        _ = ((starRingEnd ℂ) (γ t) * γ t) * (deriv γ t / γ t) := by ring
        _ = ((-4 * σ : ℝ) : ℂ) * (deriv γ t / γ t) := by rw [h2]
    have h3 := congrArg Complex.im h1
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h3
    exact h3
  have hpointω : ∀ t, Work.RPV.ωC (γ t) (deriv γ t)
      = (-4 * σ) * (deriv γ t / γ t).im := by
    intro t
    simpa only [Work.RPV.ωC] using hpoint t
  have hInt : ∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (γ t) (deriv γ t)
      = (-4 * σ) * (2 * Real.pi) := by
    rw [show (∫ t in (0 : ℝ)..(2 * Real.pi), Work.RPV.ωC (γ t) (deriv γ t))
        = ∫ t in (0 : ℝ)..(2 * Real.pi), (-4 * σ) * (deriv γ t / γ t).im
        from intervalIntegral.integral_congr (fun t _ => hpointω t)]
    rw [intervalIntegral.integral_const_mul, hint]
  rw [Work.RPB.signedArea, hInt]
  ring

end Work.RPB.B5
