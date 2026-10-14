import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.ModalSolR.thetaMomentSmooth
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.H2.T1Q.IbpCutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

set_option maxHeartbeats 3200000

/-- The angular moment `Θ(z) = ∫_θ φ(z,θ) · e_m(θ) · cos θ dθ` of the test function. -/
def Theta (m : ℕ) (φ : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ

/-! ## Elementary vanishing facts -/

/-- If a `θ`-slice of `φ` vanishes identically, then all its iterated `z`-derivatives vanish. -/
theorem pzIter_eq_zero_of_slice_zero {φ : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, φ z θ = 0) :
    ∀ k z, Work.Spaces.pzIter k φ z θ = 0 := by
  intro k
  induction k with
  | zero => intro z; exact h z
  | succ k ih =>
      intro z
      rw [Work.Spaces.pzIter_succ]
      show deriv (fun z' => Work.Spaces.pzIter k φ z' θ) z = 0
      have hone : (fun z' => Work.Spaces.pzIter k φ z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [hone, deriv_const]

/-- `Lzero φ z θ = 0` when the angle lies outside the *closed* support box of `φ`. -/
theorem Lzero_eq_zero_of_theta_not_mem {φ : ℝ → ℝ → ℝ} {a b c d z θ : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    (hθ : θ ∉ Set.Icc c d) : Work.Elliptic.Lzero φ z θ = 0 := by
  have hev : ∀ᶠ θ' in 𝓝 θ, φ z θ' = 0 := by
    rcases lt_or_ge θ c with h | h
    · filter_upwards [isOpen_Iio.mem_nhds h] with θ' hθ'
      exact test_vanishes_off_theta hbox (fun hm => absurd hm.1 (not_lt.mpr hθ'.le))
    · rcases lt_or_ge d θ with h2 | h2
      · filter_upwards [isOpen_Ioi.mem_nhds h2] with θ' hθ'
        exact test_vanishes_off_theta hbox (fun hm => absurd hm.2 (not_lt.mpr hθ'.le))
      · exact absurd ⟨h, h2⟩ hθ
  have hpt : ∀ k, Work.Spaces.pthIter k φ z θ = 0 := fun k =>
    Work.FTS.H2.ModalSol.ModeIdent.pthIter_eq_zero_of_eventually (F := φ) (z := z) (θ := θ) hev k
  have htan : Work.Spaces.pth (fun z' θ' => Real.tan θ' * φ z' θ') z θ = 0 := by
    show deriv (fun θ' => Real.tan θ' * φ z θ') θ = 0
    have hev' : (fun θ' => Real.tan θ' * φ z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with θ' hθ'
      rw [hθ']; ring
    rw [hev'.deriv_eq, deriv_const]
  have hL : Work.Elliptic.Lzero φ z θ
      = -(Work.Spaces.pthIter 2 φ z θ)
        + Work.Spaces.pth (fun z' θ' => Real.tan θ' * φ z' θ') z θ - 6 * φ z θ := rfl
  rw [hL, hpt 2, htan, hev.self_of_nhds]
  ring


/-! ## Set-integral conversions -/

/-- The `θ`-integral over `[c,d]` equals the one over `Iθ` for an integrand vanishing off the
closed interval `[c,d]` (the difference is a set of measure zero). -/
theorem setIntegral_Icc_cd_eq_Iθ {c d : ℝ} (hc0 : 0 ≤ c) (hd : d ≤ π / 2) {f : ℝ → ℝ}
    (hf : ∀ θ ∉ Set.Icc c d, f θ = 0) :
    (∫ θ in Set.Icc c d, f θ) = ∫ θ in Work.Spaces.Iθ, f θ := by
  have hsub : Set.Icc c d ⊆ Work.Spaces.Iθ := fun θ hθ => ⟨hc0.trans hθ.1, hθ.2.trans hd⟩
  rw [← MeasureTheory.integral_indicator measurableSet_Icc,
    ← MeasureTheory.integral_indicator (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
  congr 1
  funext θ
  by_cases hθ : θ ∈ Set.Icc c d
  · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem (hsub hθ)]
  · by_cases hI : θ ∈ Work.Spaces.Iθ
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_mem hI, hf θ hθ]
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hI]

/-- The `z`-integral over `[a,b]` equals the one over `(0,∞)` for an integrand vanishing off
`[a,b]`. -/
theorem setIntegral_Icc_ab_eq_Ioi {a b : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ∀ z ∉ Set.Icc a b, f z = 0) :
    (∫ z in Set.Icc a b, f z) = ∫ z in Set.Ioi 0, f z :=
  (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (t := Set.Ioi (0 : ℝ)) (s := Set.Icc a b) measurableSet_Ioi
    (fun z hz => lt_of_lt_of_le ha hz.1) (fun z hz => hf z hz.2)).symm

/-! ## Vanishing of the angular moment off the box -/

/-- `Θ` vanishes outside the closed `z`-box. -/
theorem Theta_eq_zero_of_not_mem {m : ℕ} {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) : Theta m φ z = 0 := by
  have hz' : z ∉ Set.Ioo a b := fun h => hz ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hfun : (fun θ => φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = fun _ => (0 : ℝ) :=
    funext (fun θ => by rw [test_vanishes_off_z hbox hz']; ring)
  rw [Theta, hfun]
  simp

/-- `Θ` is eventually zero outside the closed `z`-box. -/
theorem Theta_eventuallyEq_zero {m : ℕ} {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) : Theta m φ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  filter_upwards [isClosed_Icc.compl_mem_nhds hz] with z' hz'
  exact Theta_eq_zero_of_not_mem hbox hz'

/-- The derivative of `Θ` vanishes outside the closed `z`-box. -/
theorem deriv_Theta_eq_zero_of_not_mem {m : ℕ} {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) : deriv (Theta m φ) z = 0 := by
  rw [(Theta_eventuallyEq_zero hbox hz).deriv_eq, deriv_const]

/-- The derivative of `Θ` is eventually zero outside the closed `z`-box. -/
theorem deriv_Theta_eventuallyEq_zero {m : ℕ} {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) : deriv (Theta m φ) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  filter_upwards [isClosed_Icc.compl_mem_nhds hz] with z' hz'
  exact deriv_Theta_eq_zero_of_not_mem hbox hz'

/-- The second derivative of `Θ` vanishes outside the closed `z`-box. -/
theorem deriv2_Theta_eq_zero_of_not_mem {m : ℕ} {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) : deriv (deriv (Theta m φ)) z = 0 := by
  rw [(deriv_Theta_eventuallyEq_zero hbox hz).deriv_eq, deriv_const]


end Work.FTS.H2.ModalSolR
