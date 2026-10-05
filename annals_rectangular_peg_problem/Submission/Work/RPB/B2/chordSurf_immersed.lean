import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.dchord_symplectic
import Submission.Work.RPB.B2.hasDerivAt_chordPS_path
import Submission.Work.RPB.B2.phase_deriv_eq
import Submission.Work.RPB.B2.phase_deriv_eq_nhds
import Submission.Work.RPB.B2.dchord_injective
import Submission.Work.RPB.B2.dchord_combo

/-!
# The chord annulus is an immersion (`Work.RPB.B2.chordSurf_immersed`)

For a `CurveIsotopy` `CI` and a chord phase `a` (`IsChordPhase`), the chord annulus
`Π τ t r = chordSurf CI.c a τ t r` is an immersion in `(t, r)`: the two tangent vectors
`∂_t Π` and `∂_r Π` are linearly independent on `0 < r < π`.

The two derivatives are linearisations of the chord map `chordPS`:
* `∂_t Π = dchord (c'(t+r)) (c'(t-r))`,
* `∂_r Π = dchord (c'(t+r)) (-(c'(t-r)))`,
where the phase derivative is fixed by the `arg`-condition of `IsChordPhase`
(`phase_deriv_eq`, `phase_deriv_eq_nhds`) and the chord map is differentiated along the path
(`hasDerivAt_chordPS_path`).  Because `dchord` is ℝ-linear (`dchord_combo`), a vanishing
combination `α • ∂_t Π + β • ∂_r Π` is `dchord (((α+β) c'(t+r)) ((α-β) (-(c'(t-r))))`;
injectivity of `dchord` (`dchord_injective`, from `dchord_symplectic` and nondegeneracy of `ωC`)
together with `c' ≠ 0` and `c(t+r) ≠ c(t-r)` forces `α = β = 0`.
-/

set_option autoImplicit false

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff

noncomputable section

namespace Work.RPB.B2

/-! ## Differentiability of the sections of a smooth curve family -/

/-- `s ↦ c τ s` is differentiable, from `ContDiff` of the two-variable family. -/
private theorem hasDerivAt_curve (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (τ u : ℝ) : HasDerivAt (fun s : ℝ => c τ s) (deriv (c τ) u) u := by
  have hsec : ContDiffAt ℝ ∞ (fun s : ℝ => c τ s) u := by
    have hG : ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2) Set.univ (τ, u) :=
      (contDiffWithinAt_univ).2 (hc.contDiffAt)
    have hφ : ContDiffWithinAt ℝ ∞ (fun s : ℝ => (τ, s)) Set.univ u := by fun_prop
    have h := hG.comp u hφ (by intro s _; trivial)
    rwa [contDiffWithinAt_univ] at h
  exact (hsec.differentiableAt (by simp)).hasDerivAt

/-- `s ↦ c τ (s + r)`. -/
private theorem hasDerivAt_curve_add (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (τ u r : ℝ) : HasDerivAt (fun s : ℝ => c τ (s + r)) (deriv (c τ) (u + r)) u := by
  have hF := hasDerivAt_curve c hc τ (u + r)
  have hcomp := hF.scomp u ((hasDerivAt_id u).add_const r)
  convert hcomp using 1
  · ext s; simp
  · simp

/-- `s ↦ c τ (u - s)`. -/
private theorem hasDerivAt_curve_sub (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (τ u r : ℝ) : HasDerivAt (fun s : ℝ => c τ (u - s)) (-(deriv (c τ) (u - r))) r := by
  have hF := hasDerivAt_curve c hc τ (u - r)
  have hinner : HasDerivAt (fun s : ℝ => u - s) (-1) r := by
    simpa using (hasDerivAt_id r).const_sub u
  have hcomp := hF.scomp r hinner
  convert hcomp using 1
  · ext s; simp
  · simp

/-- `ContDiffAt` of `s ↦ a τ s r` from the `ContDiffOn` hypothesis of `IsChordPhase`. -/
private theorem contDiffAt_phase (a : ℝ → ℝ → ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi))
    (τ t r : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ∞ (fun s : ℝ => a τ s r) t := by
  have hx : (τ, t, r) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hτ, trivial, hr⟩
  have hG := ha.contDiffWithinAt hx
  have hφ : ContDiffWithinAt ℝ ∞ (fun s : ℝ => (τ, s, r)) Set.univ t := by fun_prop
  have h := hG.comp t hφ (by intro s _; exact ⟨hτ, trivial, hr⟩)
  rwa [contDiffWithinAt_univ] at h

/-- `ContDiffAt` of `s ↦ a τ t s` (third argument), at an interior point. -/
private theorem contDiffAt_phase_r (a : ℝ → ℝ → ℝ → ℝ)
    (ha : ContDiffOn ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi))
    (τ t r : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ContDiffAt ℝ ∞ (fun s : ℝ => a τ t s) r := by
  have hrIcc : r ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hx : (τ, t, r) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi :=
    ⟨hτ, trivial, hrIcc⟩
  have hG := ha.contDiffWithinAt hx
  have hφ : ContDiffWithinAt ℝ ∞ (fun s : ℝ => (τ, t, s)) (Set.Ioo (0 : ℝ) Real.pi) r := by
    fun_prop
  have hmt : Set.MapsTo (fun s : ℝ => (τ, t, s)) (Set.Ioo (0 : ℝ) Real.pi)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) := by
    intro s hs
    exact ⟨hτ, trivial, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
  exact (hG.comp r hφ hmt).contDiffAt (isOpen_Ioo.mem_nhds hr)

/-! ## The reality constraint from the phase lift -/

/-- Core algebra: the `arg`-constraint is a reality statement for
`exp(-ia)·(c(t+r) - c(t-r))`. -/
private theorem chordVec_im_zero (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (τ t r : ℝ)
    (hav : Work.RPB.chordVec c τ t r
      = (‖Work.RPB.chordVec c τ t r‖ : ℂ) * Complex.exp (a τ t r * I)) :
    (Complex.exp (-(a τ t r : ℂ) * Complex.I) * (c τ (t + r) - c τ (t - r))).im = 0 := by
  have hch : c τ (t + r) - c τ (t - r) = Work.RPB.chordVec c τ t r := rfl
  rw [hch, hav]
  have h1 : Complex.exp (-(a τ t r : ℂ) * Complex.I) * Complex.exp ((a τ t r : ℂ) * I) = 1 := by
    rw [← Complex.exp_add,
      show -(a τ t r : ℂ) * Complex.I + (a τ t r : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]
  have heq : Complex.exp (-(a τ t r : ℂ) * Complex.I) *
        (((‖Work.RPB.chordVec c τ t r‖ : ℝ) : ℂ) * Complex.exp (a τ t r * I))
      = ((‖Work.RPB.chordVec c τ t r‖ : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_comm (Complex.exp (-(a τ t r : ℂ) * Complex.I)) _, mul_assoc, h1,
      mul_one]
  rw [heq]
  simp

/-- The imaginary-part constraint from `IsChordPhase.arg`, middle argument varying. -/
private theorem arg_im_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ∀ s, (Complex.exp (-(a τ s r : ℂ) * Complex.I) * (CI.c τ (s + r) - CI.c τ (s - r))).im = 0 := by
  intro s
  exact chordVec_im_zero CI.c a τ s r (ha.2.1 τ hτ s r hr)

/-- The imaginary-part constraint, third argument varying, on a neighbourhood. -/
private theorem arg_im_zero_r (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ∀ᶠ s in nhds r,
      (Complex.exp (-(a τ t s : ℂ) * Complex.I) * (CI.c τ (t + s) - CI.c τ (t - s))).im = 0 := by
  have hopen : ∀ᶠ s in nhds r, s ∈ Set.Ioo (0 : ℝ) Real.pi := isOpen_Ioo.mem_nhds hr
  filter_upwards [hopen] with s hs
  exact chordVec_im_zero CI.c a τ t s (ha.2.1 τ hτ t s hs)

/-- `c τ (t+r) ≠ c τ (t-r)` for `0 < r < π` (from `CurveIsotopy.inj`). -/
private theorem curve_pair_ne (CI : Work.RPV.CurveIsotopy) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) (t : ℝ) :
    CI.c τ (t + r) ≠ CI.c τ (t - r) := by
  intro heq
  have heq' : CI.c τ (t - r) = CI.c τ (t + r) := heq.symm
  obtain ⟨m, hm⟩ := CI.inj τ hτ (t - r) (t + r) heq'
  have hr_eq : r = Real.pi * (m : ℝ) := by linarith [hm]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have := hr.1; rw [hr_eq] at this; nlinarith [Real.pi_pos, this]
  have hmlt : (m : ℝ) < 1 := by
    have := hr.2; rw [hr_eq] at this; nlinarith [Real.pi_pos, this]
  have h1 : (0 : ℤ) < m := by exact_mod_cast hmpos
  have h2 : m < 1 := by exact_mod_cast hmlt
  omega

/-! ## The two derivatives of the chord annulus -/

/-- Derivative of `s ↦ chordSurf c a τ s r` at `t` is `dchord (c'(t+r)) (c'(t-r))`. -/
private theorem deriv_chordSurf_t (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) (t : ℝ) :
    deriv (fun s => Work.RPB.chordSurf CI.c a τ s r) t
      = Work.RPV.dchord (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r)
          (deriv (CI.c τ) (t + r)) (deriv (CI.c τ) (t - r)) := by
  have hz : HasDerivAt (fun s : ℝ => CI.c τ (s + r)) (deriv (CI.c τ) (t + r)) t :=
    hasDerivAt_curve_add CI.c CI.smooth τ t r
  have hw : HasDerivAt (fun s : ℝ => CI.c τ (s - r)) (deriv (CI.c τ) (t - r)) t := by
    simpa [sub_eq_add_neg] using hasDerivAt_curve_add CI.c CI.smooth τ t (-r)
  have hφ : HasDerivAt (fun s : ℝ => a τ s r) (deriv (fun s : ℝ => a τ s r) t) t :=
    ((contDiffAt_phase a ha.1 τ t r hτ ⟨le_of_lt hr.1, le_of_lt hr.2⟩).differentiableAt
      (by simp)).hasDerivAt
  have harg := arg_im_zero CI a ha τ hτ r hr
  have hzd : (fun s : ℝ => CI.c τ (s + r)) t - (fun s : ℝ => CI.c τ (s - r)) t ≠ 0 := by
    show CI.c τ (t + r) - CI.c τ (t - r) ≠ 0
    exact sub_ne_zero.mpr (curve_pair_ne CI τ hτ r hr t)
  have hB := phase_deriv_eq (fun s : ℝ => CI.c τ (s + r)) (fun s : ℝ => CI.c τ (s - r))
    (fun s : ℝ => a τ s r) t (deriv (CI.c τ) (t + r)) (deriv (CI.c τ) (t - r))
    (deriv (fun s : ℝ => a τ s r) t) hz hw hφ hzd (by
      intro s
      simpa only [Work.RPB.chordVec] using harg s)
  have hB' : deriv (fun s : ℝ => a τ s r) t
      = ((deriv (CI.c τ) (t + r) - deriv (CI.c τ) (t - r))
          / (CI.c τ (t + r) - CI.c τ (t - r))).im := by
    simpa only [] using hB
  have hA := hasDerivAt_chordPS_path (fun s : ℝ => CI.c τ (s + r)) (fun s : ℝ => CI.c τ (s - r))
    (fun s : ℝ => a τ s r) t (deriv (CI.c τ) (t + r)) (deriv (CI.c τ) (t - r))
    (deriv (fun s : ℝ => a τ s r) t) hz hw hφ
  have hfun : (fun s : ℝ => Work.RPB.chordSurf CI.c a τ s r)
      = (fun s : ℝ => Work.RPV.chordPS ((fun s : ℝ => CI.c τ (s + r)) s)
          ((fun s : ℝ => CI.c τ (s - r)) s) ((fun s : ℝ => a τ s r) s)) := rfl
  rw [hfun, hA.deriv]
  simp only [Work.RPV.dchord]
  rw [hB']

/-- Derivative of `s ↦ chordSurf c a τ t s` at `r` is `dchord (c'(t+r)) (-(c'(t-r)))`. -/
private theorem deriv_chordSurf_r (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) (t : ℝ) :
    deriv (fun s => Work.RPB.chordSurf CI.c a τ t s) r
      = Work.RPV.dchord (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r)
          (deriv (CI.c τ) (t + r)) (-(deriv (CI.c τ) (t - r))) := by
  have hz : HasDerivAt (fun s : ℝ => CI.c τ (t + s)) (deriv (CI.c τ) (t + r)) r := by
    simpa [add_comm] using hasDerivAt_curve_add CI.c CI.smooth τ r t
  have hw : HasDerivAt (fun s : ℝ => CI.c τ (t - s)) (-(deriv (CI.c τ) (t - r))) r :=
    hasDerivAt_curve_sub CI.c CI.smooth τ t r
  have hφ : HasDerivAt (fun s : ℝ => a τ t s) (deriv (fun s : ℝ => a τ t s) r) r :=
    ((contDiffAt_phase_r a ha.1 τ t r hτ hr).differentiableAt (by simp)).hasDerivAt
  have harg := arg_im_zero_r CI a ha τ hτ t r hr
  have hzd : (fun s : ℝ => CI.c τ (t + s)) r - (fun s : ℝ => CI.c τ (t - s)) r ≠ 0 := by
    show CI.c τ (t + r) - CI.c τ (t - r) ≠ 0
    exact sub_ne_zero.mpr (curve_pair_ne CI τ hτ r hr t)
  have hB := phase_deriv_eq_nhds (fun s : ℝ => CI.c τ (t + s)) (fun s : ℝ => CI.c τ (t - s))
    (fun s : ℝ => a τ t s) r (deriv (CI.c τ) (t + r)) (-(deriv (CI.c τ) (t - r)))
    (deriv (fun s : ℝ => a τ t s) r) hz hw hφ hzd (by
      filter_upwards [harg] with s hs
      simpa only [Work.RPB.chordVec] using hs)
  have hB' : deriv (fun s : ℝ => a τ t s) r
      = ((deriv (CI.c τ) (t + r) - (-(deriv (CI.c τ) (t - r))))
          / (CI.c τ (t + r) - CI.c τ (t - r))).im := by
    simpa only [] using hB
  have hA := hasDerivAt_chordPS_path (fun s : ℝ => CI.c τ (t + s)) (fun s : ℝ => CI.c τ (t - s))
    (fun s : ℝ => a τ t s) r (deriv (CI.c τ) (t + r)) (-(deriv (CI.c τ) (t - r)))
    (deriv (fun s : ℝ => a τ t s) r) hz hw hφ
  have hfun : (fun s : ℝ => Work.RPB.chordSurf CI.c a τ t s)
      = (fun s : ℝ => Work.RPV.chordPS ((fun s : ℝ => CI.c τ (t + s)) s)
          ((fun s : ℝ => CI.c τ (t - s)) s) ((fun s : ℝ => a τ t s) s)) := rfl
  rw [hfun, hA.deriv]
  simp only [Work.RPV.dchord]
  rw [hB']

/-! ## The immersion -/

theorem chordSurf_immersed (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ α β : ℝ,
      α • deriv (fun s => Work.RPB.chordSurf CI.c a τ s r) t
        + β • deriv (fun s => Work.RPB.chordSurf CI.c a τ t s) r = 0 → α = 0 ∧ β = 0 := by
  intro τ hτ t r hr α β h
  have hzw : CI.c τ (t + r) ≠ CI.c τ (t - r) := curve_pair_ne CI τ hτ r hr t
  have harg : CI.c τ (t + r) - CI.c τ (t - r)
      = (‖CI.c τ (t + r) - CI.c τ (t - r)‖ : ℂ) * Complex.exp (a τ t r * I) :=
    ha.2.1 τ hτ t r hr
  have hζ : deriv (CI.c τ) (t + r) ≠ 0 := CI.imm τ hτ (t + r)
  have hη : deriv (CI.c τ) (t - r) ≠ 0 := CI.imm τ hτ (t - r)
  rw [deriv_chordSurf_t CI a ha τ hτ r hr t, deriv_chordSurf_r CI a ha τ hτ r hr t] at h
  have h2 := dchord_combo (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r) α β
    (deriv (CI.c τ) (t + r)) (deriv (CI.c τ) (t - r))
  rw [h2] at h
  obtain ⟨h3a, h3b⟩ := dchord_injective (CI.c τ (t + r)) (CI.c τ (t - r)) (a τ t r) hzw harg
    (((α + β : ℝ) : ℂ) * deriv (CI.c τ) (t + r))
    (((α - β : ℝ) : ℂ) * deriv (CI.c τ) (t - r)) h
  have hab : α + β = 0 := by
    have hc : ((α + β : ℝ) : ℂ) = 0 := (mul_eq_zero.mp h3a).resolve_right hζ
    exact_mod_cast hc
  have hsub : α - β = 0 := by
    have hc : ((α - β : ℝ) : ℂ) = 0 := (mul_eq_zero.mp h3b).resolve_right hη
    exact_mod_cast hc
  exact ⟨by linarith, by linarith⟩

end Work.RPB.B2
