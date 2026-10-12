import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/W1hat_abs_le.lean`

**FS `eq:WSestimate` for the corpus's `Ŵ₁ = chat (W1fun v h ℓ)`:**

    |Ŵ₁(k)| ≤ 16π·a v        for every `k`,

where `W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g0 v h)` (FS §4's
`W₁ = g/(χ⋆χ(·/ℓ))`, the χ-renormalised scattering kernel of the chosen branch
`s = Classical.choose h` of `g = v(1−s)`).

## Route

1. `chat W k = pairW W k`: the two Fourier conventions of the corpus (the
   `p`-convention `kinFT` used by `chat`, and Mathlib's `FourierTransform.fourier`
   with the frequency `(2π)⁻¹•k` used by `pairW`) agree *for every* `k`, not just
   at `k = 0` (the corpus had only `Work.BoseFixR.chat_zero_eq_pairW`).

2. `abs_chat_le_integral_abs`: the Fourier transform is dominated by the `L¹`
   mass, `|Ŵ(k)| ≤ ∫|W|` (`VectorFourier.norm_fourierIntegral_le_integral_norm`),
   i.e. the `chat`-side analogue of `Submission.BoseGases.abs_pairW_le_integral_abs`.

3. `∫|wScaled ℓ (g0 v h)| ≤ 16π·(a v)`: the real-space mass bound
   `Submission.BoseGases.wScaled_g0_abs_integral_le` (in the dilute regime
   `R ≤ ℓ·chiR0` the normalisation satisfies `(χ⋆χ)(·/ℓ) ≥ 1/2` on the support
   `ball 0 R` of `g₀`, so `|W₁| ≤ 2|g₀|` a.e., and `∫|g₀| = 8π·(a v)`).

Consequently `|Ŵ₁(k)| ≤ ∫|W₁| ≤ 2∫|g₀| = 16π·(a v)` for every momentum `k`, with
no low-momentum restriction — which is exactly the uniformity the per-mode
`|ℬ(k)| ≤ 16π·(a v)` hypothesis of the Bogoliubov block needs (the sharpened
`8π(1+δ)(a v)` version available a.e. is `Work.MGroupInput.SimpleA2Aux.
abs_pairW_wScaled_g0_le_sharp`).

The statement is unchanged; only helper lemmas are added above it.
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

/-- **The two Fourier conventions of the corpus agree at *every* momentum:**
`chat W k = pairW W k`.  (`chat` is the real part of the `p`-convention
`kinFT W k = ∫ e^{−i⟪k,y⟫}W(y)dy`, `pairW` the real part of Mathlib's
`FourierTransform.fourier W` at the frequency `(2π)⁻¹•k`.)  This generalises
`Work.BoseFixR.chat_zero_eq_pairW` from `k = 0` to all `k`. -/
lemma chat_eq_pairW (W : EuclideanSpace ℝ (Fin 3) → ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat W k = Submission.BoseGases.pairW W k := by
  have h1 : Work.BoseFixR.chat W k
      = (FourierTransform.fourier (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))
          ((2 * Real.pi)⁻¹ • k)).re := by
    rw [Work.BoseFixR.chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  rw [h1, Submission.BoseGases.pairW_eq_cfourier_re]
  simp [Submission.BoseGases.cfourier]

/-- **The Fourier transform is dominated by the `L¹` mass:** `|Ŵ(k)| ≤ ∫|W|`
for the `chat`-convention.  The `chat`-side analogue of
`Submission.BoseGases.abs_pairW_le_integral_abs` (via `chat_eq_pairW`, or
directly from `VectorFourier.norm_fourierIntegral_le_integral_norm` together with
`kinFT_eq_fourier`, which is the route taken here so that no integrability
hypothesis is needed). -/
lemma abs_chat_le_integral_abs {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (k : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat W k| ≤ ∫ x : EuclideanSpace ℝ (Fin 3), |W x| := by
  have h := VectorFourier.norm_fourierIntegral_le_integral_norm (e := Real.fourierChar)
    (μ := volume) (L := innerₗ (EuclideanSpace ℝ (Fin 3)))
    (f := fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ)) ((2 * π : ℝ)⁻¹ • k)
  rw [Work.BoseFixR.chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  have hcf : FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ))
      = VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ (EuclideanSpace ℝ (Fin 3))) (fun x => (W x : ℂ)) := rfl
  rw [hcf]
  refine le_trans h ?_
  simp [Complex.norm_real, Real.norm_eq_abs]

/-- **FS `eq:WSestimate`, uniformly in the momentum** (the row requested in
`FINDING_W1low.md`): `|Ŵ₁(k)| ≤ 16π·(a v)` for every `k`, where
`W₁ = W1fun v h ℓ = wScaled ℓ (g0 v h)`.

`L¹`-domination of the Fourier transform plus the real-space mass bound
`∫|wScaled ℓ (g0 v h)| ≤ 16π·(a v)` (`wScaled_g0_abs_integral_le`). -/
theorem W1hat_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (k : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k| ≤ 16 * Real.pi * _root_.BoseGases.a v := by
  refine le_trans (abs_chat_le_integral_abs (W := Work.BoseFixR.W1fun v h ℓ) k) ?_
  exact Submission.BoseGases.wScaled_g0_abs_integral_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ

end

end Work.BoseB7AK.W1rows
