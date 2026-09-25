import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.IonescuWainger.opArc_arcShift

/-!
# The Fourier transform of the modulated input `mstModSeq`

`ftLp` is the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary of `FourierL2Defs.lean`, realized through Mathlib's Hilbert
basis `fourierBasis`.  Writing out the modulated input
`mstModSeq G E f u k = (Σ_{β∈E} G β · e^{2πi(k−u)β}) · f k` as a finite linear combination of
plain modulations `k ↦ e^{2πi k β} · f k`, whose transforms are the translates
`shiftLp β (ftLp f hf)` (`ftLp_modSeq`), gives the multiplier identity

`𝓕 (mstModSeq G E f u) = Σ_{β∈E} (G β · e^{−2πi u β}) • shiftLp β (𝓕 f)`,

i.e. on the circle `𝓕 (mstModSeq G E f u) (ξ) = Σ_{β∈E} G β · e^{−2πi u β} · 𝓕f (ξ + β)`.

The proof is a coefficient comparison along `fourierBasis`: the `n`-th coefficient of the left side
is `Σ_{β∈E} G β · e^{2πi(n−u)β} · f n` and of the right side
`Σ_{β∈E} G β · e^{−2πi u β} · (e^{2πi n β} · f n)` (`repr_shiftLp`), and the two agree because
`e^{2πi(n−u)β} = e^{2πi n β} · e^{−2πi u β}` (`fourier_add`).
-/

open MeasureTheory Finset
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.Maximal.mstOrtho

open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal (mstModSeq memℒp_mstModSeq)

/-- **The Fourier transform of the modulated input `mstModSeq G E f u`.**  With
`mstModSeq G E f u k = (Σ_{β∈E} G β · fourier (k-u) β) · f k`, its transform is the finite sum of
translated transforms
`Σ_{β∈E} (G β · fourier (-u) β) • shiftLp β (ftLp f hf)`,
i.e. evaluated on the circle, `𝓕 (mstModSeq G E f u) (ξ) = Σ_{β∈E} G β · fourier (-u) β · 𝓕f (ξ+β)`.
Route: compare Hilbert-basis (`fourierBasis`) coefficients on both sides; the `n`-th coefficient of
the left side is `Σ_β G β fourier (n-u) β · f n`, and of the right side
`Σ_β G β fourier (-u) β · (fourier n β · f n)` (`repr_shiftLp`), which agree since
`fourier (n-u) β = fourier n β · fourier (-u) β`. -/
theorem ftLp_mstModSeq (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) (u : ℤ) :
    Work.BourgainPlan.IonescuWainger.ftLp
        (Work.BourgainPlan.Maximal.mstModSeq G E f u)
        (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf u)
      = ∑ β ∈ E,
          (G β * fourier (-u) β) •
            Work.BourgainPlan.IonescuWainger.shiftLp β
              (Work.BourgainPlan.IonescuWainger.ftLp f hf) := by
  -- The Hilbert-basis coefficients of `ftLp (mstModSeq G E f u)`: `n ↦ (Σ_β G β e^{2πi(n-u)β}) f n`.
  have hrepr : (fourierBasis (T := 1)).repr
        (ftLp (mstModSeq G E f u) (memℒp_mstModSeq hf u))
      = ⟨mstModSeq G E f u, memℒp_mstModSeq hf u⟩ := by
    rw [ftLp]; exact LinearIsometryEquiv.apply_symm_apply _ _
  have hL : ((fourierBasis (T := 1)).repr
        (ftLp (mstModSeq G E f u) (memℒp_mstModSeq hf u)) : ℤ → ℂ)
      = fun i => (∑ β ∈ E, G β * fourier (i - u) β) * f i := by
    rw [hrepr]
    funext i
    simp [Work.BourgainPlan.Maximal.mstModSeq_apply, Work.BourgainPlan.Maximal.mstArc_apply,
      Finset.sum_mul]
  -- The Hilbert-basis coefficients of the right-hand side: `n ↦ Σ_β G β e^{-2πiuβ} e^{2πinβ} f n`.
  have hR : ((fourierBasis (T := 1)).repr
        (∑ β ∈ E, (G β * fourier (-u) β) • shiftLp β (ftLp f hf)) : ℤ → ℂ)
      = fun i => ∑ β ∈ E, (G β * fourier (-u) β) * (fourier i β * f i) := by
    have hlp : (fourierBasis (T := 1)).repr
          (∑ β ∈ E, (G β * fourier (-u) β) • shiftLp β (ftLp f hf))
        = ∑ β ∈ E, (G β * fourier (-u) β) •
            (fourierBasis (T := 1)).repr (shiftLp β (ftLp f hf)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun β _ => by rw [map_smul])
    rw [show ((fourierBasis (T := 1)).repr
          (∑ β ∈ E, (G β * fourier (-u) β) • shiftLp β (ftLp f hf)) : ℤ → ℂ)
        = (((∑ β ∈ E, (G β * fourier (-u) β) •
            (fourierBasis (T := 1)).repr (shiftLp β (ftLp f hf))) : lp (fun _ : ℤ => ℂ) 2) :
              ℤ → ℂ) from by rw [hlp]]
    rw [lp.coeFn_sum]
    funext i
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, repr_shiftLp hf β i]
  -- The two families of coefficients agree termwise, by `fourier_add`.
  refine (fourierBasis (T := 1)).repr.injective (Subtype.ext ?_)
  rw [hL, hR]
  funext i
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [sub_eq_add_neg, fourier_add]
  ring

end Work.Maximal.mstOrtho
