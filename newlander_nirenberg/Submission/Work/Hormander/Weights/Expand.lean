/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Continuity, compact support and integrability for the `(0,1)`/`(1,0)`-derivatives

Plumbing for the Kohn–Morrey identity: `∂̄_j` and `∂_j` preserve `C⁰` and compact support,
and the integrands of the real pairing `rpair0` are integrable as soon as the first factor is
continuous with compact support.
-/
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

lemma continuous_dbarCoord {u : Cn n → ℂ} (hu : ContDiff ℝ 1 u) (j : Fin n) :
    Continuous (fun z => dbarCoord n j u z) := by
  have h1 : Continuous (fun z => fderiv ℝ u z (evec n j)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ u z (ivec n j)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  simp only [dbarCoord]
  exact continuous_const.mul (h1.add (continuous_const.mul h2))

lemma continuous_dCoord {u : Cn n → ℂ} (hu : ContDiff ℝ 1 u) (j : Fin n) :
    Continuous (fun z => dCoord n j u z) := by
  have h1 : Continuous (fun z => fderiv ℝ u z (evec n j)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ u z (ivec n j)) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  simp only [dCoord]
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

lemma hasCompactSupport_dbarCoord {u : Cn n → ℂ} (hsu : HasCompactSupport u) (j : Fin n) :
    HasCompactSupport (fun z => dbarCoord n j u z) := by
  exact (hsu.fderiv ℝ).comp_left (g := fun L : Cn n →L[ℝ] ℂ =>
    (1 / 2 : ℂ) * (L (evec n j) + Complex.I * L (ivec n j))) (by simp)

lemma hasCompactSupport_dCoord {u : Cn n → ℂ} (hsu : HasCompactSupport u) (j : Fin n) :
    HasCompactSupport (fun z => dCoord n j u z) := by
  exact (hsu.fderiv ℝ).comp_left (g := fun L : Cn n →L[ℝ] ℂ =>
    (1 / 2 : ℂ) * (L (evec n j) - Complex.I * L (ivec n j))) (by simp)

/-- The integrand of the real pairing `rpair0` is integrable when the first factor is
continuous with compact support. -/
lemma integrable_rpair0_integrand {φ : Cn n → ℝ} {u v : Cn n → ℂ} (hφ : Continuous φ)
    (hu : Continuous u) (hsu : HasCompactSupport u) (hv : Continuous v) :
    Integrable (fun z => (u z * star (v z)).re * wn n φ z) := by
  have hcont : Continuous (fun z => (u z * star (v z)).re * wn n φ z) :=
    (Complex.continuous_re.comp (hu.mul (continuous_star.comp hv))).mul (continuous_wn hφ)
  have hcs : HasCompactSupport (fun z => (u z * star (v z)).re * wn n φ z) := by
    refine hsu.mono (fun z hz => ?_)
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by simp [h])
  exact hcont.integrable_of_hasCompactSupport hcs

end Work.Hormander.Weights
