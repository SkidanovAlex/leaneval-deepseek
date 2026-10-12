import ChallengeDeps
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Commons.Analysis.Fourier.integrable_fourier_mul_fourier_neg
import Submission.Work.SmallBoxPairAssembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-278 — the A₂-link: `q4PairWord` in anti-diagonal τ-pairing form

`SmallBoxPairMomentum.q4PairWord_eq_fourier_integral` puts the corpus's pair word in momentum form
(`Σ_{q∈pairSet} ∫_u 𝓕W₁(u)𝓕(pairFibreDens_q)(−u)du`) and `SmallBoxPairAssembly.c2_sum` identifies
the pointwise (in `u`) mode sum with the anti-diagonal τ-pairing quadratic form
`∫_{abox} Φ·(bDag (qMode ℓ (−2πu)))(bDag (qMode ℓ (2πu)) Φ)`.  Combining them (finite sum/integral
swap) gives FS `lm:appbogolubov`'s `A₂` in the form the Bogoliubov layer consumes.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution FourierTransform

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The A₂-link.**  The corpus's pair word `q4PairWord` equals the `u`-integral of the
anti-diagonal τ-pairing quadratic form against the (χ-renormalised) scattering kernel `ŴS₁`. -/
theorem q4PairWord_eq_tau_pairing {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ((q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) : ℝ) : ℂ)
      = ∫ u, FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
          (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-((2 * π : ℝ) • u)))
            (bDag ℓ (qMode ℓ ((2 * π : ℝ) • u)) (fun y => (Φ y : ℂ))) x) := by
  rw [q4PairWord_eq_fourier_integral hℓ hR hRℓ hv_supp h hΦ]
  have hcong : (∫ u, FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
        (∫ x in abox (p + 2) ℓ, (Φ x : ℂ) * bDag ℓ (qMode ℓ (-((2 * π : ℝ) • u)))
          (bDag ℓ (qMode ℓ ((2 * π : ℝ) • u)) (fun y => (Φ y : ℂ))) x))
      = ∫ u, FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
          (∑ q ∈ pairSet (p + 2),
            FourierTransform.fourier (fun x => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) (-u)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only []
    rw [c2_sum hℓ hΦ u]
  have hcong2 : (∫ u, FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
        (∑ q ∈ pairSet (p + 2),
          FourierTransform.fourier (fun x => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) (-u)))
      = ∫ u, ∑ q ∈ pairSet (p + 2),
          FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
            FourierTransform.fourier (fun x => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) (-u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only []
    rw [Finset.mul_sum]
  rw [hcong, hcong2]
  refine (MeasureTheory.integral_finsetSum (s := pairSet (p + 2)) ?_).symm
  intro q hq
  have hqne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
  have hEW : MeasureTheory.Integrable (fun x : ℝ³ => (wScaled ℓ (g0 v h) x : ℂ)) :=
    (wScaled_integrable_ae hℓ hR.le hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h)).ofReal
  have hsupp : HasCompactSupport (fun x : ℝ³ => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) :=
    (hasCompactSupport_pairFibreDens hℓ Φ q.1 q.2).comp_left
      (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hcd : ContDiff ℝ ∞ (fun x : ℝ³ => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_pairFibreDens hℓ q.1 q.2 hqne hΦ)
  exact Commons.Analysis.Fourier.integrable_fourier_mul_fourier_neg
    (f := fun x : ℝ³ => (wScaled ℓ (g0 v h) x : ℂ)) hEW (hsupp.toSchwartzMap hcd)

end BoseGases
end Submission
