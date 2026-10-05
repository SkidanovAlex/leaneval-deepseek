import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B3.halfChordPhaseEq
import Submission.Work.RPB.B2.hasDerivAt_div_norm

/-!
# B5: the phase of the chord direction is the imaginary part of the logarithmic derivative

`phaseDeriv_eq` differentiates the phase relation of the chord annulus

`hc τ t r = ‖hc τ t r‖ * exp (a τ t r * I)`  (`0 < r < π`),

which is `Work.RPB.B3.halfChordPhaseEq`.  Dividing by the (positive) modulus gives
`hc τ t r / ‖hc τ t r‖ = exp (a τ t r * I)`, and differentiating the unit vector on the left via
`Work.RPB.B2.hasDerivAt_div_norm` while differentiating the exponential on the right identifies the
angular velocity `∂_r a` with the imaginary part of the logarithmic derivative `∂_r hc / hc`.

The two ingredients are the pure algebra

* `im_div_eq_omegaC` : `Im (v / u) = ωC u v / ‖u‖²` for `u ≠ 0`, and

* `div_norm_eq_exp` : `g / ‖g‖ = exp (θ I)` whenever `g = ‖g‖ * exp (θ I)` and `g ≠ 0`,

together with the fact that the `r`-slice of a function that is `C^∞` on the closed strip
`Icc 0 1 ×ˢ univ ×ˢ Icc 0 π` is differentiable at every *interior* point `0 < r < π`.
-/

open scoped Topology

namespace Work.RPB.B5

open Complex Filter

/-- The imaginary part of `v / u` is the symplectic pairing `ωC u v` divided by `‖u‖²`.  This is
the algebraic form of "the imaginary part of the logarithmic derivative is the angular velocity":
for `u ≠ 0` both sides equal `Im (conj u * v) / ‖u‖²`. -/
lemma im_div_eq_omegaC (u v : ℂ) (hu : u ≠ 0) :
    Complex.im (v / u) = Work.RPV.ωC u v / ‖u‖ ^ 2 := by
  have hnormSq : u * (starRingEnd ℂ) u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hcu : (starRingEnd ℂ) u ≠ 0 := by
    intro h
    apply hu
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have h1 : v / u = (v * (starRingEnd ℂ) u) / ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hnormSq]
    exact (mul_div_mul_right v u hcu).symm
  rw [h1, Complex.div_ofReal_im, Work.RPV.ωC, mul_comm v (starRingEnd ℂ u)]

/-- Dividing the phase relation `g = ‖g‖ * exp (θ I)` by the modulus `‖g‖`: this recovers the unit
vector `exp (θ I)`. -/
lemma div_norm_eq_exp (g : ℂ) (θ : ℝ) (h : g = (‖g‖ : ℂ) * Complex.exp (θ * Complex.I))
    (hg : g ≠ 0) : g / (‖g‖ : ℂ) = Complex.exp (θ * Complex.I) := by
  have hnorm : (‖g‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
  nth_rewrite 1 [h]
  exact mul_div_cancel_left₀ _ hnorm

theorem phaseDeriv_eq (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (ha : Work.RPB.IsChordPhase c a)
    (hc : ℝ → ℝ → ℝ → ℂ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hc_half : ∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord c τ t r)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {t r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hne : hc τ t r ≠ 0) :
    deriv (fun s : ℝ => a τ t s) r
      = Complex.im (deriv (fun s : ℝ => hc τ t s) r / hc τ t r) := by
  -- the phase relation for `hc` on the open strip `0 < s < π`
  have hphase : ∀ s ∈ Set.Ioo (0 : ℝ) Real.pi,
      hc τ t s = (‖hc τ t s‖ : ℂ) * Complex.exp (a τ t s * Complex.I) :=
    fun s hs => Work.RPB.B3.halfChordPhaseEq c a ha hc hc_half τ hτ t s hs
  -- the `r`-slice of `hc` is smooth, hence differentiable at `r`
  have hslice_hc : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun s : ℝ => hc τ t s) := by
    have hφ : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun s : ℝ => (τ, (t, s)) : ℝ → ℝ × (ℝ × ℝ)) :=
      contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    exact hc_sm.comp hφ
  have hdiff_hc : DifferentiableAt ℝ (fun s : ℝ => hc τ t s) r :=
    hslice_hc.contDiffAt.differentiableAt (by simp)
  have hg : HasDerivAt (fun s : ℝ => hc τ t s) (deriv (fun s : ℝ => hc τ t s) r) r :=
    hdiff_hc.hasDerivAt
  have hev_ne : ∀ᶠ s in 𝓝 r, hc τ t s ≠ 0 := hg.continuousAt.eventually_ne hne
  -- the `r`-slice of `a` is smooth at `r`: `IsChordPhase` gives `C^∞` regularity of `a` on the
  -- closed strip, and `0 < r < π` is an interior point of the last factor
  have hslice_a : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun s : ℝ => a τ t s) r := by
    have hmem : (τ, (t, r)) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hτ, trivial, ⟨le_of_lt hr.1, le_of_lt hr.2⟩⟩
    have hA : ContDiffWithinAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) (τ, (t, r)) :=
      ha.1.contDiffWithinAt hmem
    have hφ : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun s : ℝ => (τ, (t, s)) : ℝ → ℝ × (ℝ × ℝ)) :=
      contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    have hf : ContDiffWithinAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun s : ℝ => (τ, (t, s)))
        (Set.Icc (0 : ℝ) Real.pi) r := hφ.contDiffWithinAt
    have hmaps : Set.MapsTo (fun s : ℝ => (τ, (t, s))) (Set.Icc (0 : ℝ) Real.pi)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
      fun s hs => ⟨hτ, trivial, ⟨hs.1, hs.2⟩⟩
    have := ContDiffWithinAt.comp r hA hf hmaps
    exact this.contDiffAt (Icc_mem_nhds hr.1 hr.2)
  have hdiff_a : DifferentiableAt ℝ (fun s : ℝ => a τ t s) r :=
    hslice_a.differentiableAt (by simp)
  have hθ : HasDerivAt (fun s : ℝ => a τ t s) (deriv (fun s : ℝ => a τ t s) r) r :=
    hdiff_a.hasDerivAt
  -- the two slivers `hc • / ‖hc •‖` and `exp (a • I)` agree near `r`
  have hEq : (fun s : ℝ => hc τ t s / ‖hc τ t s‖) =ᶠ[𝓝 r]
      (fun s : ℝ => Complex.exp (a τ t s * Complex.I)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr, hev_ne] with s hs hsg
    exact div_norm_eq_exp (hc τ t s) (a τ t s) (hphase s hs) hsg
  -- their derivatives at `r`, computed by the quotient rule `hasDerivAt_div_norm` and by `exp`
  have hd1 : deriv (fun s : ℝ => hc τ t s / ‖hc τ t s‖) r
      = Complex.I * (hc τ t r / ‖hc τ t r‖) *
        ((Work.RPV.ωC (hc τ t r) (deriv (fun s : ℝ => hc τ t s) r) / ‖hc τ t r‖ ^ 2 : ℝ) : ℂ) :=
    (Work.RPB.B2.hasDerivAt_div_norm (fun s : ℝ => hc τ t s)
      (deriv (fun s : ℝ => hc τ t s) r) r hg hne).deriv
  have hd2 : deriv (fun s : ℝ => Complex.exp (a τ t s * Complex.I)) r
      = deriv (fun s : ℝ => a τ t s) r * Complex.I * Complex.exp (a τ t r * Complex.I) := by
    have hθC : HasDerivAt (fun s : ℝ => ((a τ t s : ℝ) : ℂ))
        (((deriv (fun s : ℝ => a τ t s) r : ℝ)) : ℂ) r := hθ.ofReal_comp
    have hinner : HasDerivAt (fun s : ℝ => ((a τ t s : ℝ) : ℂ) * Complex.I)
        ((((deriv (fun s : ℝ => a τ t s) r : ℝ)) : ℂ) * Complex.I) r :=
      hθC.mul_const Complex.I
    rw [hinner.cexp.deriv]
    ring
  -- cancel the common factor `I * exp (a τ t r * I) = g r / ‖g r‖` to read off `∂_r a = ωC / ‖·‖²`
  have hkey : (Work.RPV.ωC (hc τ t r) (deriv (fun s : ℝ => hc τ t s) r) / ‖hc τ t r‖ ^ 2 : ℝ)
      = deriv (fun s : ℝ => a τ t s) r := by
    have hgr : hc τ t r / ‖hc τ t r‖ = Complex.exp (a τ t r * Complex.I) :=
      div_norm_eq_exp (hc τ t r) (a τ t r) (hphase r hr) hne
    have h := hEq.deriv_eq
    rw [hd1] at h
    rw [hd2] at h
    rw [hgr] at h
    have hA : Complex.I * Complex.exp (a τ t r * Complex.I) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
    have h'' : (Complex.I * Complex.exp (a τ t r * Complex.I)) *
          (((Work.RPV.ωC (hc τ t r) (deriv (fun s : ℝ => hc τ t s) r) / ‖hc τ t r‖ ^ 2 : ℝ)) : ℂ)
        = (Complex.I * Complex.exp (a τ t r * Complex.I)) *
          (((deriv (fun s : ℝ => a τ t s) r : ℝ)) : ℂ) := by
      rw [h]
      ring
    exact Complex.ofReal_injective (mul_left_cancel₀ hA h'')
  rw [im_div_eq_omegaC (hc τ t r) (deriv (fun s : ℝ => hc τ t s) r) hne]
  exact hkey.symm

end Work.RPB.B5
