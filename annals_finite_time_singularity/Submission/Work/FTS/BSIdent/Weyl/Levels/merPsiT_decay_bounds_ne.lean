import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Extension
import Submission.Work.FTS.BSIdent.Weyl.Levels.DecayTwoDefs
import Submission.Work.FTS.BSIdent.Weyl.Levels.abs_div_psiCore_le_one
import Submission.Work.FTS.BSIdent.Weyl.Levels.abs_pdZ_pdR_psiCore_le_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The decay of the meridian stream function in the sharp (`q = 1`) regime

The `Cyl.DecayAux` chain bounds `∂_z ψ`, `∂_r ψ` and `ψ/r` by `K/(1+ρ)` for a profile rate
`(π/2-θ)^q` with `q > 2`, under `3 ≤ p·λ`.  Here the sharper statement needed by the
reconstruction is proved instead: the rate carries the weight `π/2 - θ` only in first power (and
loses it completely for `∂_θ`), and the exponent hypothesis is only `2 ≤ p·λ`.

The two pointwise corollaries (one for `ψ/r`, one for the pair `∂_z ψ`, `∂_r ψ`) are proved in
`Levels.abs_div_psiCore_le_one` and `Levels.abs_pdZ_pdR_psiCore_le_one`; this file supplies the
two rate/differentiability transfers from the hypotheses of the statement to the ones those
lemmas ask for, and assembles the result — including the extension from `z > 0` to `z < 0` by
the oddness of `ψ` in `z`.
-/

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

set_option maxHeartbeats 1000000

/-- The rate hypothesis of `merPsiT_decay_bounds_ne`, as a named predicate (the sharp `q = 1`
form: the weight `π/2 - θ` occurs in the value bound and in the `∂_w`-bound, and disappears from
the `∂_θ`-bounds). -/
def PhiRateOne (Φ : Work.FTS.BSIdent.Fam) (τ C₀ lam : ℝ) : Prop :=
  ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
    |Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
    |deriv (fun w' : ℝ => Φ w' θ τ) w| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
    |deriv (fun θ' : ℝ => Φ w θ' τ) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
    |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' τ) θ') θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
    |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' τ) w) θ| ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
    |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ τ) w') w|
      ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)

/-- On the open quadrant the odd extension `Φ̂(·,·,τ)` inherits the first three clauses of
`PhiRateOne`. -/
theorem phiOdd_rate_one {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam : ℝ}
    (h0 : ∀ w, 0 < w → Φ w 0 τ = 0) (hrate : PhiRateOne Φ τ C₀ lam)
    {w θ : ℝ} (hw : 0 < w) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.FTS.BSIdent.PhiOdd Φ w θ τ| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
    |Work.Cyl.pdR (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ|
      ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
    |Work.Cyl.pdZ (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ|
      ≤ C₀ * (1 + w) ^ (-lam) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Work.FTS.BSIdent.PhiOdd_of_nonneg hθ0.le]
    exact (hrate w θ hw.le hθ0.le hθ1).1
  · have hev : (fun w' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w' θ τ) =ᶠ[𝓝 w]
        fun w' => Φ w' θ τ :=
      Eventually.of_forall (fun w' => Work.FTS.BSIdent.PhiOdd_of_nonneg hθ0.le)
    rw [Work.Cyl.pdR, EventuallyEq.deriv_eq hev]
    exact (hrate w θ hw.le hθ0.le hθ1).2.1
  · have hev : (fun θ' : ℝ => Work.FTS.BSIdent.PhiOdd Φ w θ' τ) =ᶠ[𝓝 θ]
        fun θ' => Φ w θ' τ := by
      filter_upwards [isOpen_Ioi.mem_nhds hθ0] with θ' hθ'
      exact Work.FTS.BSIdent.PhiOdd_of_nonneg hθ'.le
    rw [Work.Cyl.pdZ, EventuallyEq.deriv_eq hev]
    exact (hrate w θ hw.le hθ0.le hθ1).2.2.1

/-- Differentiability of the odd extension on the open quadrant, from `C²` smoothness of `Φ` on a
neighbourhood of the closed quadrant. -/
theorem diffAt2_PhiOdd_strip {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Cyl.DiffAt2 (fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ) w θ := by
  have hmem : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w, θ) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hθ0
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w, θ)]
      fun p : ℝ × ℝ => Work.FTS.BSIdent.PhiOdd Φ p.1 p.2 τ := by
    filter_upwards [hmem] with p hp
    exact (Work.FTS.BSIdent.PhiOdd_of_nonneg hp.le).symm
  exact (((hsm w θ (by linarith) (by linarith) (by linarith)).of_le
    (by decide)).differentiableAt_one).congr_of_eventuallyEq hev.symm

theorem merPsiT_decay_bounds_ne {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r z : ℝ, 0 < r → z ≠ 0 →
      |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z| / r ≤ K / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ K / (1 + Work.Cyl.rhoP r z) ∧
      |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z|
        ≤ K / (1 + Work.Cyl.rhoP r z) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hrate1 : PhiRateOne Φ (Physical.clockInv C t) C₀ lam := hrate
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = max (decayKzrOne (Work.FTS.Regularity.pExp α) ((A (Physical.clockInv C t))⁻¹) C₀ lam
          (B (Physical.clockInv C t)))
        (decayKqOne ((A (Physical.clockInv C t))⁻¹) C₀ lam (B (Physical.clockInv C t))) :=
    ⟨_, rfl⟩
  refine ⟨K, ?_, ?_⟩
  · rw [hKdef]
    exact le_trans (decayKzrOne_nonneg hC₀.le hp.le) (le_max_left _ _)
  · intro r z hr hz
    have hquad : ∀ u : ℝ, 0 < u →
        |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r u| / r ≤ K / (1 + Work.Cyl.rhoP r u) ∧
        |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r u|
          ≤ K / (1 + Work.Cyl.rhoP r u) ∧
        |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r u|
          ≤ K / (1 + Work.Cyl.rhoP r u) := by
      intro u hu
      have hρ : 0 < Work.Cyl.rhoP r u := Work.Cyl.rhoP_pos hr u
      have hden : (0 : ℝ) ≤ 1 + Work.Cyl.rhoP r u := by
        linarith [Work.Cyl.rhoP_nonneg r u]
      have hθ0 : 0 < Work.Cyl.thetaP r u :=
        Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hu
      have hθ1 : Work.Cyl.thetaP r u < Real.pi / 2 :=
        Work.FTS.BSIdent.Cyl.thetaP_lt_pi_div_two r u
      have hw : 0 < Work.Cyl.rhoP r u ^ Work.FTS.Regularity.pExp α
          / B (Physical.clockInv C t) :=
        div_pos (Real.rpow_pos_of_pos hρ _) hB
      obtain ⟨hval, hwd, hth⟩ :=
        phiOdd_rate_one (τ := Physical.clockInv C t) hzeroPlane hrate1 hw hθ0 hθ1
      have hG := diffAt2_PhiOdd_strip (τ := Physical.clockInv C t) hsm hw hθ0 hθ1
      have hD := abs_div_psiCore_le_one
        (G := fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t))
        (c := (A (Physical.clockInv C t))⁻¹) hC₀.le hlam hp hB hr hu hexp hval
      have hZ := abs_pdZ_pdR_psiCore_le_one
        (G := fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ (Physical.clockInv C t))
        (c := (A (Physical.clockInv C t))⁻¹) hC₀.le hlam hp hB hr hu hexp hG hval hwd hth
      obtain ⟨hZ1, hZ2⟩ := hZ
      rw [Work.FTS.BSIdent.Cyl.merPsiT_eq_psiCore]
      refine ⟨?_, ?_, ?_⟩
      · have habsdiv : ∀ x : ℝ, |x| / r = |x / r| := fun x => by
          rw [abs_div, abs_of_pos hr]
        rw [habsdiv, hKdef]
        exact hD.trans (div_le_div_of_nonneg_right (le_max_right _ _) hden)
      · rw [hKdef]
        exact hZ1.trans (div_le_div_of_nonneg_right (le_max_left _ _) hden)
      · rw [hKdef]
        exact hZ2.trans (div_le_div_of_nonneg_right (le_max_left _ _) hden)
    rcases lt_trichotomy z 0 with hzneg | hz0 | hzpos
    · obtain ⟨h1, h2, h3⟩ := hquad (-z) (by linarith)
      have hodd : ∀ y : ℝ, Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r (-y)
          = - Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r y :=
        fun y => Work.FTS.BSIdent.Cyl.merPsiT_odd_z hB hzeroPlane (r := r) (z := y) hr
      have hoddz : Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z
          = - Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r (-z) := by
        simpa using hodd (-z)
      have h1' : |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r (-z)| / r
          ≤ K / (1 + Work.Cyl.rhoP r z) := by
        rw [Work.Cyl.rhoP_neg] at h1
        exact h1
      refine ⟨?_, ?_, ?_⟩
      · rw [hoddz, abs_neg]
        exact h1'
      · rw [show Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z
              = deriv (fun z' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z') z from rfl,
            Work.FTS.BSIdent.Cyl.deriv_odd_eq hodd z]
        rw [Work.Cyl.rhoP_neg] at h2
        exact h2
      · rw [show Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r z
              = deriv (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' z) r from rfl]
        have hev : (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' z)
            =ᶠ[𝓝 r] fun r' => - Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z) := by
          filter_upwards [isOpen_Ioi.mem_nhds hr] with r' hr'
          simpa using Work.FTS.BSIdent.Cyl.merPsiT_odd_z hB hzeroPlane (r := r') (z := -z) hr'
        rw [Filter.EventuallyEq.deriv_eq hev,
          show deriv (fun r' : ℝ => - Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z)) r
              = - deriv (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z)) r from
            Work.FTS.BSIdent.Cyl.deriv_neg_fun
              (g := fun r' => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' (-z)) r,
          abs_neg]
        rw [Work.Cyl.rhoP_neg] at h3
        exact h3
    · exact absurd hz0 hz
    · exact hquad z hzpos

end Work.FTS.BSIdent.Weyl.Levels
