import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.zIBP_compact
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-integrated radial integration by parts of the truncated energy identity

This module proves `Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta`: for a datum `u` which is
`C^∞` on the open quadrant `(0,∞) × (0,π/2)` and honestly in `ℋ⁰` (i.e. `HkMem α 0` of `u`,
`z ∂_z u` and `z²∂_z²u`), and a compactly supported `C²` radial weight `ω` (supported in `[a,b]`,
`0 < a < b`) which is bounded by the square of the radial weight `w`,

`∫_0^∞ ω(z) ∫_θ σ(θ)(α²z²∂_z²u + α(5+α)z∂_zu)·u
  = -α²∫_0^∞ ω(z)∫_θ σ(θ)(z∂_zu)²
    + (α²/2)∫_0^∞ (z²ω)''(z)∫_θ σ(θ)u²
    - (α(5+α)/2)∫_0^∞ (zω)'(z)∫_θ σ(θ)u²`,  `σ = sin(2θ)^{-η}`.

Route: the per-`θ` radial identity `Honest.zIBP_compact`, applied to the `z`-slices
`z ↦ u z θ` for a.e. `θ ∈ Iθ`, followed by an exchange of the two integrals (Fubini, whose
integrability hypothesis comes from the three `ℋ⁰`-memberships and `|ω| ≤ w²`).
-/

noncomputable section

namespace Work.FTS.EllipticEst.Dispatch

open MeasureTheory Set Filter
open scoped Topology Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The Fubini/Tonelli swap of the `z`- and `θ`-integrations -/

/-- **Fubini for the iterated integrals over `(0,∞) × Iθ`.**  If `(z,θ) ↦ K z · G z θ` is
integrable against the product measure `nuFts = dz|_{(0,∞)} × dθ|_{Iθ}`, then the `z`-outer
iterated integral is the `θ`-outer iterated integral.  This is `integral_integral_swap`
together with the pointwise `K z * ∫ = ∫ K z *` (`integral_const_mul`). -/
theorem tRibp_swapRadial {K : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => K p.1 * G p.1 p.2) nuFts) :
    (∫ z in Set.Ioi (0 : ℝ), K z * (∫ θ in Work.Spaces.Iθ, G z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ), K z * G z θ := by
  have h1 : (∫ z in Set.Ioi (0 : ℝ), K z * (∫ θ in Work.Spaces.Iθ, G z θ))
      = ∫ z, ∫ θ, K z * G z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (K z) (fun θ => G z θ)).symm
  rw [h1]
  exact MeasureTheory.integral_integral_swap hint

/-! ## The pointwise-in-`θ` radial identity -/

/-- **The radial integration by parts on a single angular slice.**  For a.e. `θ ∈ Iθ` the
`θ`-weight `σ(θ) = sEta θ` is a constant for the `z`-integral, so `Honest.zIBP_compact` applied
to the slice `z ↦ u z θ` gives the identity with the weight. -/
theorem tRibp_sliceIbpSeta {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hωsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ *
        ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z *
            (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  have hsl : ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) := by
    have h2 := hsm 2
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun z hz => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  have hkey := Work.FTS.EllipticEst.Honest.zIBP_compact α ω (fun z : ℝ => u z θ)
    ha hab hωsupp hωd hsl
  have key : ∀ (F : ℝ → ℝ), (∫ z in Set.Ioi (0 : ℝ), ω z *
        (Work.FTS.EllipticEst.sEta θ * F z))
      = Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), ω z * F z) := by
    intro F
    rw [show (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ * F z))
        = ∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.sEta θ * (ω z * F z) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have key2 : ∀ (G : ℝ → ℝ), (∫ z in Set.Ioi (0 : ℝ),
        G z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      = Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), G z * (u z θ) ^ 2) := by
    intro G
    rw [show (∫ z in Set.Ioi (0 : ℝ), G z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        = ∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.sEta θ * (G z * (u z θ) ^ 2) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hL : (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ *
        ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
      = Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), ω z *
          (α ^ 2 * z ^ 2 * deriv (deriv (fun z : ℝ => u z θ)) z
            + (α * (5 + α) * z) * deriv (fun z : ℝ => u z θ) z) * u z θ) := by
    rw [key (fun z => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    simp only [Work.Spaces.pz, Work.Spaces.pzIter, Work.Spaces.pzIter_succ,
      Work.Spaces.pzIter_zero]
    ring
  rw [hL, hkey, key (fun z => (z * Work.Spaces.pz u z θ) ^ 2),
    key2 (fun z => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z),
    key2 (fun z => deriv (fun y : ℝ => y * ω y) z)]
  simp only [Work.Spaces.pz]
  ring

/-! ## Vanishing off the support `[a,b]` and bounds for the weight coefficients -/

/-- `ω = 0` in a neighbourhood of every point outside `[a,b]`. -/
private lemma tRibp_omega_eventually_zero {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → ω =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  rcases hz' with hlt | hgt
  · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
    exact hω0 w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
  · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
    exact hω0 w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)

private lemma tRibp_deriv_one_off {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → deriv (fun y : ℝ => y * ω y) z = 0 := by
  intro z hz
  have hev : (fun y : ℝ => y * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [tRibp_omega_eventually_zero hω0 z hz] with y hy
    rw [hy]; ring
  rw [hev.deriv_eq]; simp

private lemma tRibp_deriv_two_off {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → deriv (fun y : ℝ => y ^ 2 * ω y) z = 0 := by
  intro z hz
  have hev : (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [tRibp_omega_eventually_zero hω0 z hz] with y hy
    rw [hy]; ring
  rw [hev.deriv_eq]; simp

private lemma tRibp_deriv_two_two_off {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z = 0 := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  have hev : deriv (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
      exact tRibp_deriv_two_off hω0 w
        (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
      exact tRibp_deriv_two_off hω0 w
        (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
  rw [hev.deriv_eq]; simp

/-- The two weight coefficients `(z²ω)''` and `(zω)'` are globally bounded.  Both vanish off
`[a,b]` (since `ω` does, near every point outside it) and are continuous on the compact `[a,b]`
(as `ω` is `C²` on `(0,∞) ⊇ [a,b]`). -/
theorem tRibp_exists_bound_derivs {ω : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z : ℝ, |deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z| ≤ M)
      ∧ (∀ z : ℝ, |deriv (fun y : ℝ => y * ω y) z| ≤ M) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hW2 : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hW2' : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
    hW2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hZ2 : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hc2 : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Icc a b) :=
    (hW2'.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hc1 : ContinuousOn (deriv (fun y : ℝ => y * ω y)) (Set.Icc a b) :=
    (hZ2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  refine ⟨max (max M2 M1) 0, le_max_right _ _, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ Set.Icc a b
    · have h := hM2 z hz
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [tRibp_deriv_two_two_off hω0 z hz, abs_zero]
      exact le_max_right _ _
  · intro z
    by_cases hz : z ∈ Set.Icc a b
    · have h := hM1 z hz
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [tRibp_deriv_one_off hω0 z hz, abs_zero]
      exact le_max_right _ _


/-- `σ(θ) = sEta θ = sin(2θ)^{-η}` is continuous on the open quadrant. -/
theorem tRibp_continuousOn_sEta :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hpow : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun p hp =>
      Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos]))))
  exact hpow

/-- The elementary AM–GM bound `|A|·|B| ≤ (A² + B²)/2`. -/
private lemma tRibp_abs_mul_le_half (A B : ℝ) : |A| * |B| ≤ (A ^ 2 + B ^ 2) / 2 := by
  nlinarith [sq_nonneg (|A| - |B|), abs_mul_abs_self A, abs_mul_abs_self B]

/-! ## Joint integrability of the four integrands -/

/-- **Joint integrability of the pairing integrands.**  The `ℋ⁰`-integrand of a function `g` is
`w(z)² g² σ(θ)`, and `σ ≥ 0`, `w ≥ 0`; with `|ω z| ≤ w(z)²` and `2|A||B| ≤ A² + B²` this
dominates the two `ω`-weighted pairings by sums of `ℋ⁰`-integrands of `z²∂_z²u`, `z∂_zu` and
`u`, all of which are integrable on `nuFts` by `HkMem α 0` (`integrable_HkIntegrand_of_smoothOpen`
plus the a.e. form `HkIntegrand_zero_D`). -/
theorem tRibp_integrablePair {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hrad2 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    (hu : Work.Spaces.HkMem α 0 u)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hωsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0)
    (hωbdd : ∀ z : ℝ, |ω z| ≤ (Work.Spaces.w z) ^ 2) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
        ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts
    ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 *
        (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) nuFts := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hIu := integrable_HkIntegrand_of_smoothOpen huS hu
  have hIg := integrable_HkIntegrand_of_smoothOpen huS.Dz hgrad
  have hIr := integrable_HkIntegrand_of_smoothOpen
    (Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq huS) hrad2
  have hωcont : ContinuousOn (fun p : ℝ × ℝ => ω p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hPz2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (huS.pzIter 2).continuousOn
  have hPz1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := huS.pz.continuousOn
  have hPsi : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := huS.continuousOn
  -- the second conjunct
  have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 *
      (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) nuFts := by
    have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ω p.1 *
        (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) nuFts :=
      aesm_prod_of_continuousOn_Q0 (hωcont.mul (tRibp_continuousOn_sEta.mul
        (((continuous_fst.continuousOn).mul hPz1).pow 2)))
    refine hIg.mono' haesm ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    have hnn : 0 ≤ Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 :=
      mul_nonneg hsEta (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc |ω p.1| * (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
        ≤ (Work.Spaces.w p.1) ^ 2 *
            (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) :=
          mul_le_mul_of_nonneg_right (hωbdd p.1) hnn
      _ = Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) p.1 p.2 := by
          rw [HkIntegrand_zero_D α _ hθ]; ring
  -- the first conjunct
  have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
        ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts := by
    have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ω p.1 *
        (Work.FTS.EllipticEst.sEta p.2 *
          ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts :=
      aesm_prod_of_continuousOn_Q0 (hωcont.mul (tRibp_continuousOn_sEta.mul
        ((((continuousOn_const.mul ((continuous_fst.continuousOn).pow 2)).mul hPz2).add
          ((continuousOn_const.mul continuous_fst.continuousOn).mul hPz1)).mul hPsi)))
    set K : ℝ := max 1 (max (α ^ 4 / 2) ((α * (5 + α)) ^ 2 / 2)) with hKdef
    have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one (le_max_left _ _)
    have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
    have hK2 : α ^ 4 / 2 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK3 : (α * (5 + α)) ^ 2 / 2 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
    have hsum : MeasureTheory.Integrable (fun p : ℝ × ℝ => K *
        (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
          + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) p.1 p.2
          + Work.Spaces.HkIntegrand α 0 u p.1 p.2)) nuFts :=
      ((hIr.add hIg).add hIu).const_mul K
    refine hsum.mono' haesm ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    obtain ⟨z, θ⟩ := p
    have hcore : |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|
        ≤ (α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
          + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
          + (u z θ) ^ 2 := by
      have h1' := tRibp_abs_mul_le_half (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ) (u z θ)
      have h2' := tRibp_abs_mul_le_half ((α * (5 + α) * z) * Work.Spaces.pz u z θ) (u z θ)
      rw [abs_mul]
      calc |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ| * |u z θ|
          ≤ (|α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ|
              + |(α * (5 + α) * z) * Work.Spaces.pz u z θ|) * |u z θ| :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
        _ = |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|
              + |(α * (5 + α) * z) * Work.Spaces.pz u z θ| * |u z θ| := by ring
        _ ≤ ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2
              + (((α * (5 + α) * z) * Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2 :=
            add_le_add h1' h2'
        _ = (α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
              + (u z θ) ^ 2 := by ring
    have hstep : |ω z| * (Work.FTS.EllipticEst.sEta θ *
          |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
          ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
            + (u z θ) ^ 2)) := by
      have h0 : 0 ≤ Work.FTS.EllipticEst.sEta θ *
          |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ| :=
        mul_nonneg hsEta (abs_nonneg _)
      calc |ω z| * (Work.FTS.EllipticEst.sEta θ *
            |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|)
          ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
              |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
                + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|) :=
            mul_le_mul_of_nonneg_right (hωbdd z) h0
        _ ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
              ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
                + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
                + (u z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore hsEta) hw2
    have hkey : (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
          ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
            + (u z θ) ^ 2))
        = (α ^ 4 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
          + ((α * (5 + α)) ^ 2 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 u z θ := by
      rw [HkIntegrand_zero_D α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) hθ,
        HkIntegrand_zero_D α (fun z θ => z * Work.Spaces.pz u z θ) hθ,
        HkIntegrand_zero_D α u hθ]
      ring
    have hnn3 : 0 ≤ Work.Spaces.HkIntegrand α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ z θ
    have hnn2 : 0 ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ z θ
    have hnn1 : 0 ≤ Work.Spaces.HkIntegrand α 0 u z θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ z θ
    have hnnEta : 0 ≤ Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2 :=
      mul_nonneg hsEta (sq_nonneg _)
    have hnnAbs : 0 ≤ Work.FTS.EllipticEst.sEta θ *
        |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ| :=
      mul_nonneg hsEta (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hsEta]
    calc |ω z| * (Work.FTS.EllipticEst.sEta θ *
          |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
            ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
              + (u z θ) ^ 2)) := hstep
      _ = (α ^ 4 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
          + ((α * (5 + α)) ^ 2 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 u z θ := hkey
      _ ≤ K * (Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 u z θ) := by
          calc (α ^ 4 / 2) * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + ((α * (5 + α)) ^ 2 / 2) * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z * Work.Spaces.pz u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ
              ≤ K * Work.Spaces.HkIntegrand α 0
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + K * Work.Spaces.HkIntegrand α 0
                    (fun z θ => z * Work.Spaces.pz u z θ) z θ
                + K * Work.Spaces.HkIntegrand α 0 u z θ := by
                refine add_le_add (add_le_add ?_ ?_) ?_
                · exact mul_le_mul_of_nonneg_right hK2 hnn3
                · exact mul_le_mul_of_nonneg_right hK3 hnn2
                · simpa using mul_le_mul_of_nonneg_right hK1 hnn1
            _ = K * (Work.Spaces.HkIntegrand α 0
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by ring
  exact ⟨h1, h2⟩

/-- **Joint integrability of the weight-coefficient integrands.**  With `M` a global bound for
`(z²ω)''` and `(zω)'` (they vanish off the compact `[a,b]` and are continuous there), the two
integrands `(z²ω)''(z)·σ(θ)u²` and `(zω)'(z)·σ(θ)u²` are dominated by `M` times
`HkIntegrand α 0 u` (using `w ≥ 1` on `(0,∞)` and `σ ≥ 0`). -/
theorem tRibp_integrableCoeff {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hu : Work.Spaces.HkMem α 0 u)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hωsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) p.1 *
          (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)) nuFts
    ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (fun y : ℝ => y * ω y) p.1 *
          (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)) nuFts := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hIu := integrable_HkIntegrand_of_smoothOpen huS hu
  obtain ⟨M, hM0, hM2, hM1⟩ := tRibp_exists_bound_derivs (ω := ω) ha hωd hωsupp
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hW2 : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hW2' : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
    hW2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hZ2 : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hc2 : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Ioi 0) :=
    hW2'.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hc1 : ContinuousOn (deriv (fun y : ℝ => y * ω y)) (Set.Ioi 0) :=
    hZ2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hPsi : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := huS.continuousOn
  have hdom : ∀ᵐ p ∂nuFts, ∀ (c : ℝ → ℝ), (∀ z, |c z| ≤ M) →
      ‖c p.1 * (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)‖
        ≤ M * Work.Spaces.HkIntegrand α 0 u p.1 p.2 := by
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    intro c hc
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    have hnn : 0 ≤ Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2 :=
      mul_nonneg hsEta (sq_nonneg _)
    have hw1 : (1 : ℝ) ≤ Work.Spaces.w p.1 := one_le_w_D hp1
    have hw2 : (1 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := one_le_pow₀ hw1
    have hsq : Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 0 u p.1 p.2 := by
      calc Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2
          = 1 * (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2) := (one_mul _).symm
        _ ≤ (Work.Spaces.w p.1) ^ 2 *
              (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2) :=
            mul_le_mul_of_nonneg_right hw2 hnn
        _ = Work.Spaces.HkIntegrand α 0 u p.1 p.2 := by
            rw [HkIntegrand_zero_D α u hθ]; ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact le_trans (mul_le_mul_of_nonneg_right (hc p.1) hnn)
      (mul_le_mul_of_nonneg_left hsq hM0)
  refine ⟨?_, ?_⟩
  · refine integrable_of_le_const_mul_HkIntegrand hM0
      (aesm_prod_of_continuousOn_Q0 ((hc2.comp continuous_fst.continuousOn
        (fun p hp => hp.1)).mul (tRibp_continuousOn_sEta.mul (hPsi.pow 2)))) hIu ?_
    filter_upwards [hdom] with p hp
    exact hp _ hM2
  · refine integrable_of_le_const_mul_HkIntegrand hM0
      (aesm_prod_of_continuousOn_Q0 ((hc1.comp continuous_fst.continuousOn
        (fun p hp => hp.1)).mul (tRibp_continuousOn_sEta.mul (hPsi.pow 2)))) hIu ?_
    filter_upwards [hdom] with p hp
    exact hp _ hM1

/-! ## The target theorem -/

theorem truncRadialIbpTheta {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hrad2 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    (hu : Work.Spaces.HkMem α 0 u)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0)) (hωsupp : ∀ z, z ∉ Set.Icc a b → ω z = 0)
    (hωbdd : ∀ z, |ω z| ≤ (Work.Spaces.w z) ^ 2) :
    (∫ z in Set.Ioi (0 : ℝ), ω z * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
        ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ + (α * (5 + α) * z) * Work.Spaces.pz u z θ)
          * u z θ)))
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ), deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  -- ## the four joint-integrability facts
  obtain ⟨hIntL, hIntY⟩ := tRibp_integrablePair (α := α) (u := u) ω ha hab hsm hgrad hrad2 hu
    hωd hωsupp hωbdd
  obtain ⟨hIntA, hIntB⟩ := tRibp_integrableCoeff (α := α) (u := u) ω ha hab hsm hu hωd hωsupp
  -- ## the slicewise identity holds for a.e. `θ`
  have hθae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    have hset : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ *
          ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
        = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z *
              (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
          + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
                (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
              deriv (fun y : ℝ => y * ω y) z *
                (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
    hθae.mono (fun θ hθ => tRibp_sliceIbpSeta (α := α) (u := u) ω ha hab hsm hωd hωsupp hθ)
  -- ## exchange the two integrations
  rw [tRibp_swapRadial hIntL, tRibp_swapRadial hIntY, tRibp_swapRadial hIntA,
    tRibp_swapRadial hIntB]
  -- ## apply the slicewise identity under the `θ`-integral
  rw [MeasureTheory.integral_congr_ae hae]
  -- ## split the linear combination
  have hF1 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z in Set.Ioi (0 : ℝ),
      ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntY.integral_prod_right
  have hF2 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z in Set.Ioi (0 : ℝ),
      deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
        (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntA.integral_prod_right
  have hF3 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z in Set.Ioi (0 : ℝ),
      deriv (fun y : ℝ => y * ω y) z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntB.integral_prod_right
  have hA1c : MeasureTheory.Integrable (fun θ : ℝ => -α ^ 2 *
      (∫ z in Set.Ioi (0 : ℝ),
        ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hF1.const_mul (-α ^ 2)
  have hA2c : MeasureTheory.Integrable (fun θ : ℝ => α ^ 2 / 2 *
      (∫ z in Set.Ioi (0 : ℝ), deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
        (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hF2.const_mul (α ^ 2 / 2)
  have hA3c : MeasureTheory.Integrable (fun θ : ℝ => α * (5 + α) / 2 *
      (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z *
        (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hF3.const_mul (α * (5 + α) / 2)
  have e1 : (∫ θ in Work.Spaces.Iθ, -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
        ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)))
      = -α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
        ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)) :=
    MeasureTheory.integral_const_mul (-α ^ 2) _
  have e2 : (∫ θ in Work.Spaces.Iθ, α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
          (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      = α ^ 2 / 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
          (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
    MeasureTheory.integral_const_mul (α ^ 2 / 2) _
  have e3 : (∫ θ in Work.Spaces.Iθ, α * (5 + α) / 2 * (∫ z in Set.Ioi (0 : ℝ),
        deriv (fun y : ℝ => y * ω y) z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      = α * (5 + α) / 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
        deriv (fun y : ℝ => y * ω y) z *
          (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
    MeasureTheory.integral_const_mul (α * (5 + α) / 2) _
  have e4 : (∫ θ in Work.Spaces.Iθ, (-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
          ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
          deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))))
      = (∫ θ in Work.Spaces.Iθ, -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
          ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)))
        + (∫ θ in Work.Spaces.Iθ, α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
          deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))) :=
    MeasureTheory.integral_add hA1c hA2c
  have e5 : (∫ θ in Work.Spaces.Iθ, ((-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
            ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
          + α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
        - α * (5 + α) / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))))
      = (∫ θ in Work.Spaces.Iθ, (-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
            ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
          + α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))))
        - (∫ θ in Work.Spaces.Iθ, α * (5 + α) / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))) :=
    MeasureTheory.integral_sub (hA1c.add hA2c) hA3c
  rw [e5, e4, e1, e2, e3]

end Work.FTS.EllipticEst.Dispatch
