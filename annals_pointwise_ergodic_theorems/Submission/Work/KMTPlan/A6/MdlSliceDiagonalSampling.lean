/-
# The decimated (`x ↦ x mod Q`) sampling comparison for the `r`-variational norm

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), §8, display (5.4) ("Theorem `Sampling`").  In the large-scale
`(2,2,1)` analysis the discrete model tuple is the *sample* of the adelic tuple
`F : ℝ × Ẑ → ℂ`, i.e. it is the restriction to the diagonal `(x, x mod Q)`:

  `c n x = F n (x) (x mod Q)`      (`x ∈ ℤ`).

This module proves the resulting norm comparison *from the real-variable sampling comparison*

  `∑_{N∈ℤ} Vʳ_n(G n (ρ + Q N)) ≤ C Q⁻¹ ∫_ℝ Vʳ_n(G n x) dx`
  (for `G = F · ρ` band-limited in the real variable, `β Q ≤ 1/4`),

which is the `p = 1` case of `Work.KMTAreas.A7Hi.vrSamplingDensity`
(`Work.KMTAreas.A7Hi.vrSamplingDensity_one`); the residue decomposition of `ℤ` is
`Work.BourgainPlan.IonescuWainger.lintegral_count_residue`.

The conclusion is

  `∑_{x∈ℤ} Vʳ_n(c n x) ≤ C ∫_ℝ (1/Q) ∑_{ρ<Q} Vʳ_n(F n x ρ) dx`,

i.e. the discrete `ℓ¹(ℤ;Vʳ)`-norm of the sampled tuple is controlled by the *adelic*
`L¹(ℝ × ℤ/Q;Vʳ)`-norm of the tuple it samples.  This is the transfer that the A6/A7 large-scale
assembly needs (see `NOTES_A6_MdlSliceCoreGain_ROUTE_REFINEMENT.md` §0bis).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.BourgainPlan.IonescuWainger.lintegral_count_residue
import Submission.Work.KMTAreas.A7Hi.vrSamplingDensity_one

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## The residue decomposition of the `ℓ¹`-norm of the variational norm -/

/-- **The residue decomposition of `∑_x Vʳ(c x)`.**  Every `x : ℤ` is written uniquely as
`Q * N + ρ` with `0 ≤ ρ < Q`, and the `ℓ¹`-norm splits accordingly. -/
theorem tsum_variationalNorm_residue (r : NNReal) (Q : ℕ) (hQ : 1 ≤ Q) (c : ℕ → ℤ → ℂ) :
    (∑' x : ℤ, variationalNorm r (fun n : ℕ => c n x))
      = ∑ ρ ∈ Finset.range Q,
          ∑' N : ℤ, variationalNorm r (fun n : ℕ => c n ((Q : ℤ) * N + (ρ : ℤ))) := by
  have h := Work.BourgainPlan.IonescuWainger.lintegral_count_residue (Q := Q) hQ
    (fun x : ℤ => variationalNorm r (fun n : ℕ => c n x))
  simp only [MeasureTheory.lintegral_count] at h
  rw [h]

/-- **Measurability of the `r`-variational norm of a continuous family.** -/
theorem measurable_variationalNorm_of_continuous {r : NNReal} (hr : 0 < r) (u : ℕ → ℝ → ℂ)
    (hu : ∀ n : ℕ, Continuous (u n)) :
    Measurable (fun X : ℝ => variationalNorm r (fun n : ℕ => u n X)) :=
  Submission.PointwiseErgodicTheorems.measurable_variationalNorm hr (fun n => (hu n).measurable)

/-- **A function with real-frequency support (an `L¹` amplitude) is continuous** — it is the
inverse Fourier transform of an integrable function. -/
theorem continuous_of_hasRealFreqSupport {ψ : ℝ → ℂ} {S : Set ℝ}
    (h : Work.KMTAreas.A7Rep.HasRealFreqSupport ψ S) : Continuous ψ := by
  obtain ⟨g, hgint, -, hg⟩ := h
  have h1 : (⇑(Real.Lp.fourierTransformInv
        (MemLp.toLp g (memLp_one_iff_integrable.mpr hgint))) : ℝ → ℂ)
      = FourierTransformInv.fourierInv g := Real.Lp.fourierTransformInv_toLp _
  rw [show ψ = FourierTransformInv.fourierInv g from funext hg, ← h1]
  exact (Real.Lp.fourierTransformInv _).continuous

/-- **Measurability of the `r`-variational norm of a band-limited family**, obtained from
continuity of each member.  This discharges the measurability hypothesis of the transfer. -/
theorem measurable_variationalNorm_of_hasRealFreqSupport {r : NNReal} (hr : 0 < r) {S : Set ℝ}
    (u : ℕ → ℝ → ℂ) (hu : ∀ n : ℕ, Work.KMTAreas.A7Rep.HasRealFreqSupport (u n) S) :
    Measurable (fun X : ℝ => variationalNorm r (fun n : ℕ => u n X)) :=
  measurable_variationalNorm_of_continuous hr u
    (fun n => continuous_of_hasRealFreqSupport (hu n))


/-! ## The decimated sampling comparison -/

/-- **The decimated (diagonal) sampling comparison for the `r`-variational norm.**

Hypothesis `hslice`: the real-variable sampling comparison for each vertical slice `F · ρ` at the
lattice `ρ + Qℤ` (the `p = 1` case of Theorem `Sampling`, e.g. the conclusion of
`Work.KMTAreas.A7Hi.vrSamplingDensity_one` at `q = Q`, `a = ρ`).  Conclusion: the discrete
`ℓ¹(ℤ; Vʳ)`-norm of the diagonal sample `c n x = F n x (x mod Q)` is bounded by the adelic
`L¹(ℝ × ℤ/Q; Vʳ)`-norm of `F`. -/
theorem diagonalVrSampling_le {r : NNReal} {Q : ℕ} (hQ : 1 ≤ Q) {C : ℝ}
    (hC : 0 < C) {F : ℕ → ℝ → ℤ → ℂ}
    (hmeas : ∀ ρ : ℤ, Measurable
      (fun x : ℝ => variationalNorm r (fun n : ℕ => F n x ρ)))
    (hslice : ∀ (ρ : ℤ),
      (∑' N : ℤ, variationalNorm r
          (fun n : ℕ => F n ((ρ : ℝ) + (Q : ℝ) * (N : ℝ)) ρ))
        ≤ ENNReal.ofReal C * (Q : ENNReal)⁻¹
            * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x ρ))
    {c : ℕ → ℤ → ℂ} (hc : ∀ n x, c n x = F n (x : ℝ) (x % Q)) :
    (∑' x : ℤ, variationalNorm r (fun n : ℕ => c n x))
      ≤ ENNReal.ofReal C
          * ∫⁻ x : ℝ, (Q : ENNReal)⁻¹
              * ∑ ρ ∈ Finset.range Q, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)) := by
  have hQpos : (0 : ℤ) < (Q : ℤ) := by
    have : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ
    exact_mod_cast this
  -- the per-residue bound
  have hper : ∀ ρ ∈ Finset.range Q,
      (∑' N : ℤ, variationalNorm r (fun n : ℕ => c n ((Q : ℤ) * N + (ρ : ℤ))))
        ≤ ENNReal.ofReal C * (Q : ENNReal)⁻¹
            * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)) := by
    intro ρ hρ
    have hlt : (ρ : ℤ) < (Q : ℤ) := by
      have := Finset.mem_range.mp hρ
      exact_mod_cast this
    have hnn : (0 : ℤ) ≤ (ρ : ℤ) := Int.natCast_nonneg ρ
    have hfam : (fun N : ℤ => variationalNorm r (fun n : ℕ => c n ((Q : ℤ) * N + (ρ : ℤ))))
        = (fun N : ℤ => variationalNorm r
            (fun n : ℕ => F n ((ρ : ℝ) + (Q : ℝ) * (N : ℝ)) (ρ : ℤ))) := by
      funext N
      congr 1
      funext n
      rw [hc n ((Q : ℤ) * N + (ρ : ℤ))]
      congr 1
      · push_cast; ring
      · rw [show (Q : ℤ) * N + (ρ : ℤ) = (ρ : ℤ) + (Q : ℤ) * N by ring,
          Int.add_mul_emod_self_left, Int.emod_eq_of_lt hnn hlt]
    rw [hfam]
    exact hslice (ρ : ℤ)
  -- assemble
  rw [tsum_variationalNorm_residue r Q hQ c]
  have hInt : (∫⁻ x : ℝ, ∑ ρ ∈ Finset.range Q,
        variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)))
      = ∑ ρ ∈ Finset.range Q,
          ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)) :=
    MeasureTheory.lintegral_finsetSum' (Finset.range Q) (fun ρ _ => (hmeas (ρ : ℤ)).aemeasurable)
  have hQne : (Q : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hQinv : (Q : ENNReal)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hQne
  have hSumEq : (∑ ρ ∈ Finset.range Q, ENNReal.ofReal C * (Q : ENNReal)⁻¹
        * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)))
      = ENNReal.ofReal C * ∫⁻ x : ℝ, (Q : ENNReal)⁻¹
          * ∑ ρ ∈ Finset.range Q, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)) := by
    have hL : (∑ ρ ∈ Finset.range Q, ENNReal.ofReal C * (Q : ENNReal)⁻¹
          * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)))
        = ∑ ρ ∈ Finset.range Q, ENNReal.ofReal C * ((Q : ENNReal)⁻¹
            * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ))) :=
      Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [hL, ← Finset.mul_sum, ← Finset.mul_sum, ← hInt,
      ← MeasureTheory.lintegral_const_mul' (Q : ENNReal)⁻¹ _ hQinv]
  exact (Finset.sum_le_sum hper).trans (le_of_eq hSumEq)

/-! ## The transfer with the band-limitation hypothesis discharged -/

/-- **The decimated sampling comparison, with the real-variable sampling comparison discharged.**
For band-limited slices (`HasRealFreqSupport (F · ρ) (Icc (-β) β)`, `β Q ≤ 1/4`) the diagonal
sample `c n x = F n x (x mod Q)` obeys the adelic bound.  This is the form the A6/A7 large-scale
assembly consumes. -/
theorem diagonalVrSampling_le_of_band (r : NNReal) (hr : 1 ≤ r) (Q : ℕ) (hQ : 1 ≤ Q)
    (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 2) (hβQ : β * (Q : ℝ) ≤ 1 / 4)
    (F : ℕ → ℝ → ℤ → ℂ)
    (hband : ∀ (n : ℕ) (ρ : ℤ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (fun x : ℝ => F n x ρ) (Set.Icc (-β) β))
    (c : ℕ → ℤ → ℂ) (hc : ∀ n x, c n x = F n (x : ℝ) (x % Q)) :
    ∃ C : ℝ, 0 < C ∧
      (∑' x : ℤ, variationalNorm r (fun n : ℕ => c n x))
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, (Q : ENNReal)⁻¹
            * ∑ ρ ∈ Finset.range Q, variationalNorm r (fun n : ℕ => F n x (ρ : ℤ)) := by
  have hmeas : ∀ ρ : ℤ, Measurable
      (fun x : ℝ => variationalNorm r (fun n : ℕ => F n x ρ)) :=
    fun ρ => measurable_variationalNorm_of_hasRealFreqSupport (lt_of_lt_of_le zero_lt_one hr) _
      (fun n => hband n ρ)
  obtain ⟨C, hC, hSamp⟩ := Work.KMTAreas.A7Hi.vrSamplingDensity_one r hr β hβ hβ'
  refine ⟨C, hC, diagonalVrSampling_le (r := r) (Q := Q) hQ hC (F := F) (c := c)
    hmeas (fun ρ => ?_) hc⟩
  simpa only using hSamp (fun n x => F n x ρ) (fun n => hband n ρ) Q
    (by omega : 0 < Q) hβQ ρ

end Work.KMTPlan.A6
