import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Existence.theta_integrable
import Submission.Work.OddVolterra.Existence.volterra_rows_of_moment_eqs
import Submission.Work.OddEnvelope.Sanity
import Submission.Work.OddEnvelope.Close.isEnvelopeCurve_semicircle

/-!
# The base Volterra equation of the odd transition-slope argument

For `h = 0` and `x = y = profileX` (the ball), the paper's system `(hah44)`

`G(s, Z(s)) = ∫_s^1 Θ(s,σ,Z(σ)) dσ + 𝚵(s)`

holds on the whole slope interval `(0,1)`.

The two ingredients are the general ones proved elsewhere in the chapter, instantiated at the
unperturbed data:

* `volterra_rows_of_moment_eqs` — rows `2,3` of the system from the two moment equations;
* `theta_integrable` — the interval-integrability of the `𝚯`-integrand, which lets the two
  `FTC` rows `0,1` be read off componentwise;
* the moment equations for the ball are `ball_momentF`/`ball_momentH`, and the envelope profile of
  the unperturbed data is the semicircle (`envelopeProfile_semicircle_eq`).
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle profileX_pos profileX_mem_Icc
  oddSemicircleMomentConstant)

noncomputable section

lemma profileX_eq_inv (s : ℝ) : profileX s = (Real.sqrt (1 + s ^ 2))⁻¹ := by
  unfold Commons.Geometry.Ulam.profileX
  rw [one_div]

lemma contDiff_profileX : ContDiff ℝ (⊤ : ℕ∞) profileX := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + s ^ 2) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
    h1.sqrt (fun x => by positivity)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) :=
    h2.inv (fun x => by positivity)
  rw [show profileX = fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹ from funext profileX_eq_inv]
  exact h3

lemma profileX_lt_one {s : ℝ} (hs : 0 < s) : profileX s < 1 :=
  Work.OddEnvelope.profileX_lt_one hs

/-- The unperturbed chord data is an envelope curve. -/
theorem isEnvelopeCurve_base :
    Work.OddEnvelope.IsEnvelopeCurve (fun _ : ℝ => 0) profileX profileX :=
  Work.OddEnvelope.Close.isEnvelopeCurve_semicircle

/-- The envelope profile of the unperturbed data is the semicircle. -/
theorem envelopeProfile_base {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX t = semicircle t :=
  Work.OddEnvelope.envelopeProfile_semicircle_eq ht

private lemma psi_profile_eq {s : ℝ} {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    psi (fun _ : ℝ => 0) (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s t
      = psi (fun _ : ℝ => 0) semicircle s t := by
  unfold psi line
  rw [envelopeProfile_base ht]

/-- The first moment equation for the unperturbed data. -/
theorem base_momentF (n : ℕ) {s : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) :
    momentF n (fun _ : ℝ => 0) profileX profileX (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s
      = oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2) := by
  have hle : -profileX s ≤ profileX s := by
    have := profileX_pos s hs
    linarith
  have hmem := profileX_mem_Icc s
  have hint : (∫ t in (-profileX s)..(profileX s),
        momentIntegrand n (fun _ : ℝ => 0) (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s t)
      = ∫ t in (-profileX s)..(profileX s), momentIntegrand n (fun _ : ℝ => 0) semicircle s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      have hlt : profileX s < 1 := profileX_lt_one hs
      exact ⟨by linarith [ht.1, hlt], by linarith [ht.2, hmem.2]⟩
    unfold momentIntegrand
    rw [psi_profile_eq htI]
  unfold momentF at *
  rw [hint]
  exact ball_momentF n hs

/-- The second (centroid) moment equation for the unperturbed data. -/
theorem base_momentH (n : ℕ) {s : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) :
    momentH n (fun _ : ℝ => 0) profileX profileX (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s = 0 := by
  have hle : -profileX s ≤ profileX s := by
    have := profileX_pos s hs
    linarith
  have hmem := profileX_mem_Icc s
  have hint : (∫ t in (-profileX s)..(profileX s),
        centroidIntegrand n (fun _ : ℝ => 0) (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s t)
      = ∫ t in (-profileX s)..(profileX s), centroidIntegrand n (fun _ : ℝ => 0) semicircle s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      have hlt : profileX s < 1 := profileX_lt_one hs
      exact ⟨by linarith [ht.1, hlt], by linarith [ht.2, hmem.2]⟩
    unfold centroidIntegrand
    rw [psi_profile_eq htI]
  unfold momentH at *
  rw [hint]
  exact ball_momentH n hs

/-- The closeness package of the unperturbed data is trivial. -/
theorem base_close :
    ∀ s : ℝ, 0 < s →
      |profileX s - profileX s| ≤ 1 / 100 ∧
      |deriv profileX s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv profileX) s - deriv (deriv profileX) s| ≤ 1 / 100 ∧
      |profileX s - profileX s| ≤ 1 / 100 ∧
      |deriv profileX s - deriv profileX s| ≤ 1 / 100 ∧
      |deriv (deriv profileX) s - deriv (deriv profileX) s| ≤ 1 / 100 := by
  intro s _
  norm_num

/-! ## Component extraction and the two `FTC` rows -/

/-- Component extraction for `St`-valued interval integrals. -/
lemma intervalIntegral_apply_fin4 {f : ℝ → Work.OddVolterra.St} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (i : Fin 4) :
    (∫ x in a..b, f x) i = ∫ x in a..b, f x i := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i :
    Work.OddVolterra.St →L[ℝ] ℝ).intervalIntegral_comp_comm (μ := volume) (a := a) (b := b) hf
  simpa [ContinuousLinearMap.proj_apply] using h.symm

/-- The two `FTC` rows of the system for the unperturbed data. -/
theorem base_rows01 (n : ℕ) (hn : 1 ≤ n) :
    ∀ s ∈ Set.Ioo (0:ℝ) 1,
      (Godd n (fun _ : ℝ => 0) s (stateOf profileX profileX s)) 0 =
          ((∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) + Xi n (fun _ : ℝ => 0) s) 0 ∧
        (Godd n (fun _ : ℝ => 0) s (stateOf profileX profileX s)) 1 =
          ((∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) + Xi n (fun _ : ℝ => 0) s) 1 := by
  have hH := isEnvelopeCurve_base
  have hmeF : ∀ s : ℝ, 0 < s → s ≤ 1 →
      momentF n (fun _ : ℝ => 0) profileX profileX (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s
        = oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2) :=
    fun s hs hs1 => base_momentF n hs hs1
  have hmeH : ∀ s : ℝ, 0 < s → s ≤ 1 →
      momentH n (fun _ : ℝ => 0) profileX profileX (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s = 0 :=
    fun s hs hs1 => base_momentH n hs hs1
  have hclose := base_close
  have hint := theta_integrable n hn contDiff_const hH hmeF hmeH hclose
  intro s hs
  have hi := hint s hs
  have hcont : Continuous (deriv profileX) :=
    contDiff_profileX.continuous_deriv (WithTop.coe_le_coe.mpr le_top)
  have hFTC : (∫ σ in s..(1:ℝ), deriv profileX σ) = profileX 1 - profileX s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => ((contDiff_profileX.differentiable (by simp)).differentiableAt
        (x := u)).hasDerivAt)
      (hcont.intervalIntegrable _ _)
  beta_reduce at hi
  constructor
  · have he := intervalIntegral_apply_fin4 hi (0 : Fin 4)
    have h0 : (Godd n (fun _ : ℝ => 0) s (stateOf profileX profileX s)) 0 = profileX s := by
      simp [Godd, stateOf]
    have hX : (Xi n (fun _ : ℝ => 0) s) 0 = profileX 1 := by simp [Xi]
    have hsum : ((∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) + Xi n (fun _ : ℝ => 0) s) 0
        = (∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) 0 + (Xi n (fun _ : ℝ => 0) s) 0 := rfl
    have hT : (∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) 0
        = -(∫ σ in s..(1:ℝ), deriv profileX σ) := by
      rw [he]
      rw [show (∫ σ in s..(1:ℝ), (Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) 0)
            = ∫ σ in s..(1:ℝ), -(deriv profileX σ) from
          intervalIntegral.integral_congr (fun σ _ => by simp [Theta, stateOf])]
      rw [intervalIntegral.integral_neg]
    rw [h0, hsum, hX, hT]
    linarith
  · have he := intervalIntegral_apply_fin4 hi (1 : Fin 4)
    have h0 : (Godd n (fun _ : ℝ => 0) s (stateOf profileX profileX s)) 1 = profileX s := by
      simp [Godd, stateOf]
    have hX : (Xi n (fun _ : ℝ => 0) s) 1 = profileX 1 := by simp [Xi]
    have hsum : ((∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) + Xi n (fun _ : ℝ => 0) s) 1
        = (∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) 1 + (Xi n (fun _ : ℝ => 0) s) 1 := rfl
    have hT : (∫ σ in s..(1:ℝ), Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) 1
        = -(∫ σ in s..(1:ℝ), deriv profileX σ) := by
      rw [he]
      rw [show (∫ σ in s..(1:ℝ), (Theta n (fun _ : ℝ => 0) s σ (stateOf profileX profileX σ)) 1)
            = ∫ σ in s..(1:ℝ), -(deriv profileX σ) from
          intervalIntegral.integral_congr (fun σ _ => by simp [Theta, stateOf])]
      rw [intervalIntegral.integral_neg]
    rw [h0, hsum, hX, hT]
    linarith

/-- **The base Volterra equation**: the unperturbed ball satisfies the paper's system `(hah44)` on
the whole slope interval `(0,1)`. -/
theorem base_volterra (n : ℕ) (hn : 1 ≤ n) :
    Work.OddVolterra.VolterraEqOn n (fun _ : ℝ => 0) Commons.Geometry.Ulam.profileX Commons.Geometry.Ulam.profileX (Set.Ioo (0:ℝ) 1) := by
  have hmeF : ∀ s : ℝ, 0 < s → s ≤ 1 →
      momentF n (fun _ : ℝ => 0) profileX profileX (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s
        = oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2) :=
    fun s hs hs1 => base_momentF n hs hs1
  have hmeH : ∀ s : ℝ, 0 < s → s ≤ 1 →
      momentH n (fun _ : ℝ => 0) profileX profileX (Work.OddEnvelope.envelopeProfile (fun _ : ℝ => 0) profileX profileX) s = 0 :=
    fun s hs hs1 => base_momentH n hs hs1
  have h01 := base_rows01 n hn
  have h23 := volterra_rows_of_moment_eqs n hn contDiff_const isEnvelopeCurve_base hmeF hmeH base_close
  intro s hs
  funext i
  fin_cases i
  · exact (h01 s hs).1
  · exact (h01 s hs).2
  · exact (h23 s hs).1
  · exact (h23 s hs).2

end

end Work.OddVolterra.Existence
