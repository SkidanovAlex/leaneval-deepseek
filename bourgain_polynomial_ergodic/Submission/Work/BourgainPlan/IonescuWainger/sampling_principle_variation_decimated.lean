import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.sampling_principle_variation
import Submission.Work.BourgainPlan.IonescuWainger.msw_torsion_kernel
import Submission.Work.BourgainPlan.IonescuWainger.torsion_kernel_classsum
import Submission.Work.BourgainPlan.IonescuWainger.torsion_kernel_changevar
import Submission.Work.BourgainPlan.IonescuWainger.lintegral_count_residue

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal BigOperators Interval FourierTransform

set_option maxHeartbeats 1000000
-- the hypotheses `hOp` and `ha` of the (fixed) statement occur only as hypotheses
set_option linter.unusedVariables false

/-- **The `ℤ`-periodisation of the sampling principle for the `2`-variation**, i.e. KMSZ
Definition 5.1(3) in the decimated form in which it is used.

If the *rescaled* symbol `ξ ↦ m n (ξ / Q)` has continuous `L^p(ℝ)`-variation bound `A` (the
hypothesis `hOp`, tested on band-limited functions), then the discrete operator with the decimated
kernel `j ↦ Q · [Q ∣ j] · ∫_{-1/2}^{1/2} m n (ξ) e^{2πi j ξ} dξ` obeys the same `ℓ^p(ℤ)`
variation bound with a constant `C = C(p)` independent of `Q`, `κ` and `m`.

Proof: `(T a)(Q N + r) = Σ_{M} W(N - M) a (Q M + r)` on the residue class `r mod Q`
(`torsion_kernel_classsum` plus the change of variable `torsion_kernel_changevar`, pointwise in
`n`), so on each class the operator is the *undecimated* multiplier of the rescaled symbol and
`Work.BourgainPlan.IonescuWainger.sampling_principle_variation` applies; `lintegral_count_residue`
splits the `ℓ^p(ℤ)`-variation over the residue classes, and the `∑_{r}` of the resulting finite
sums is compared with the `∑_{j ∈ s}` by adjoining the (compact) remainder of the `ℓ^p` mass of
`a`, which vanishes off `s` by `ha`. -/
theorem sampling_principle_variation_decimated {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ Q : ℕ) (hQ : 1 ≤ Q) (m : ℕ → ℝ → ℂ)
      (hm : ∀ n, MeasureTheory.Integrable (m n))
      (hsupp : ∀ (n : ℕ) (ξ : ℝ),
        ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m n ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv
              (fun ξ : ℝ => m n (ξ / (Q : ℝ)) * FourierTransform.fourier g ξ) x)) ^ p
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume)
      (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ k, k ∉ s → a k = 0),
      ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n =>
          ∑ j ∈ s, ((Q : ℂ) * (if ((Q : ℤ) ∣ (k - j)) then
            (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
              Complex.exp (2 * Real.pi * Complex.I * (((k - j : ℤ) : ℂ) * (ξ : ℂ))))
            else 0)) * a j)) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * A) ^ p) * ∑ j ∈ s, ENNReal.ofReal ‖a j‖ ^ p := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sampling_principle_variation (p := p) hp
  refine ⟨C₁, hC₁pos, ?_⟩
  intro κ Q hQ m hm hsupp A hA hOp s a ha
  classical
  have hQne : (Q : ℤ) ≠ 0 := by
    have h1 : (1 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ
    omega
  have hQneR : (Q : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  -- the decimated kernel `K n j = Q [Q ∣ j] ∫ m n ξ e^{2πi j ξ}`
  set K : ℕ → ℤ → ℂ := fun n j => (Q : ℂ) * (if (Q : ℤ) ∣ j then
    (∫ ξ in (-(1/2):ℝ)..(1/2),
      m n ξ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ)))) else 0) with hK
  -- the (undecimated) kernel `W n j = ∫ m n (ξ/Q) e^{2πi j ξ}` of the rescaled symbol
  set W : ℕ → ℤ → ℂ := fun n j =>
    ∫ ξ in (-(1/2):ℝ)..(1/2),
      m n (ξ / (Q : ℝ)) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ))) with hW
  have hK0 : ∀ (n : ℕ) (j : ℤ), ¬ (Q : ℤ) ∣ j → K n j = 0 := by
    intro n j hj
    rw [hK]
    simp [hj]
  have hKW : ∀ (n : ℕ) (j : ℤ), K n ((Q : ℤ) * j) = W n j := by
    intro n j
    rw [hK, hW]
    beta_reduce
    rw [if_pos (show (Q : ℤ) ∣ (Q : ℤ) * j from ⟨j, rfl⟩)]
    simpa only [mul_assoc] using (torsion_kernel_changevar hQ (m n) (hm n) (hsupp n) j).symm
  -- the rescaled index sets
  set u : ℕ → Finset ℤ := fun r =>
    (s.filter (fun k => (Q : ℤ) ∣ (k - (r : ℤ)))).image (fun k => (k - (r : ℤ)) / (Q : ℤ))
    with hu
  -- the rescaled symbol is integrable and band-limited
  have hmti : ∀ n : ℕ, MeasureTheory.Integrable (fun ξ : ℝ => m n (ξ / (Q : ℝ))) := by
    intro n
    have h := (hm n).comp_mul_right' (R := (Q : ℝ)⁻¹) (inv_ne_zero hQneR)
    refine h.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    simp [div_eq_mul_inv]
  have hmtsupp : ∀ (n : ℕ) (ξ : ℝ),
      ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m n (ξ / (Q : ℝ)) = 0 := by
    intro n ξ hξ
    apply hsupp n
    intro hcon
    apply hξ
    have hpos : (0 : ℝ) < (Q : ℝ) := by positivity
    rcases hcon with ⟨h1, h2⟩
    constructor
    · have h : -(1 / (2 * (Q : ℝ))) * (Q : ℝ) ≤ ξ := (le_div_iff₀ hpos).mp h1
      calc -(1 / 2 : ℝ) = -(1 / (2 * (Q : ℝ))) * (Q : ℝ) := by field_simp
        _ ≤ ξ := h
    · have h : ξ ≤ (1 / (2 * (Q : ℝ))) * (Q : ℝ) := (div_le_iff₀ hpos).mp h2
      calc ξ ≤ (1 / (2 * (Q : ℝ))) * (Q : ℝ) := h
        _ = 1 / 2 := by field_simp
  have hOp' : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
      ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => FourierTransformInv.fourierInv
            (fun ξ : ℝ => (fun n ξ => m n (ξ / (Q : ℝ))) n ξ *
              FourierTransform.fourier g ξ) x)) ^ p
        ∂MeasureTheory.volume
      ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume :=
    fun g hg hgb => hOp g hg hgb
  -- the per-residue-class bound
  have hper : ∀ r ∈ Finset.range Q,
      ∫⁻ N : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => ∑ j ∈ s, a j * K n ((Q : ℤ) * N + (r : ℤ) - j))) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C₁ * A) ^ p) *
          ∫⁻ N : ℤ, ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    intro r hr
    set ar : ℤ → ℂ := fun M => a ((Q : ℤ) * M + (r : ℤ)) with har
    have har0 : ∀ M : ℤ, M ∉ u r → ar M = 0 := by
      intro M hM
      by_contra hne
      have hmem : (Q : ℤ) * M + (r : ℤ) ∈ s := by
        by_contra hns
        exact hne (ha _ hns)
      have hdvd : (Q : ℤ) ∣ ((Q : ℤ) * M + (r : ℤ) - (r : ℤ)) := ⟨M, by ring⟩
      have hquot : ((Q : ℤ) * M + (r : ℤ) - (r : ℤ)) / (Q : ℤ) = M := by
        rw [show (Q : ℤ) * M + (r : ℤ) - (r : ℤ) = (Q : ℤ) * M by ring]
        exact Int.mul_ediv_cancel_left M hQne
      have hmemu : M ∈ u r := by
        rw [hu]
        exact Finset.mem_image.mpr ⟨(Q : ℤ) * M + (r : ℤ),
          Finset.mem_filter.mpr ⟨hmem, hdvd⟩, hquot⟩
      exact hM hmemu
    have hmsw := hC₁ κ (fun n ξ => m n (ξ / (Q : ℝ))) hmti hmtsupp A hA hOp' (u r) ar har0
    have hsum : ∀ N : ℤ, (fun n : ℕ => ∑ j ∈ s, a j * K n ((Q : ℤ) * N + (r : ℤ) - j))
        = (fun n : ℕ => ∑ j ∈ u r,
            (∫ ξ in (-(1/2):ℝ)..(1/2),
              m n (ξ / (Q : ℝ)) *
                Complex.exp (2 * Real.pi * Complex.I * (((N - j : ℤ)) : ℂ) * (ξ : ℂ))) * ar j) := by
      intro N
      funext n
      rw [torsion_kernel_classsum hQ (K n) (hK0 n) a s (r : ℤ) N]
      refine Finset.sum_congr rfl (fun M hM => ?_)
      rw [hKW n (N - M), har, hW]
      simp only [mul_assoc]
      ring
    have hfin : ∑ j ∈ u r, ENNReal.ofReal ‖ar j‖ ^ p
        = ∫⁻ N : ℤ, ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p ∂MeasureTheory.Measure.count := by
      rw [MeasureTheory.lintegral_count]
      rw [tsum_eq_sum (s := u r)
        (f := fun M : ℤ => ‖a ((Q : ℤ) * M + (r : ℤ))‖ₑ ^ p) ?_]
      · apply Finset.sum_congr rfl
        intro M hM
        rw [har, ofReal_norm]
      · intro M hM
        have h0 : a ((Q : ℤ) * M + (r : ℤ)) = 0 := by
          have := har0 M hM
          simpa only [har] using this
        rw [h0]
        simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < p)]
    calc
      ∫⁻ N : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => ∑ j ∈ s, a j * K n ((Q : ℤ) * N + (r : ℤ) - j))) ^ p
          ∂MeasureTheory.Measure.count
        = ∫⁻ N : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => ∑ j ∈ u r,
              (∫ ξ in (-(1/2):ℝ)..(1/2),
                m n (ξ / (Q : ℝ)) *
                  Complex.exp (2 * Real.pi * Complex.I * (((N - j : ℤ)) : ℂ) * (ξ : ℂ))) * ar j)) ^ p
            ∂MeasureTheory.Measure.count := by
          apply lintegral_congr; intro N; rw [hsum N]
      _ ≤ ENNReal.ofReal ((C₁ * A) ^ p) * ∑ j ∈ u r, ENNReal.ofReal ‖ar j‖ ^ p := hmsw
      _ = ENNReal.ofReal ((C₁ * A) ^ p) *
            ∫⁻ N : ℤ, ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p ∂MeasureTheory.Measure.count := by
          rw [hfin]
  -- the identification of the decimated sum with the `K`-convolution
  have hsumk : ∀ k : ℤ, (fun n : ℕ => ∑ j ∈ s, ((Q : ℂ) * (if ((Q : ℤ) ∣ (k - j)) then
        (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
          Complex.exp (2 * Real.pi * Complex.I * (((k - j : ℤ) : ℂ) * (ξ : ℂ))))
        else 0)) * a j)
      = (fun n : ℕ => ∑ j ∈ s, a j * K n (k - j)) := by
    intro k
    funext n
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hK]
    ring
  -- the `ℓ^p` mass of `a` is the sum over its support
  have hvan : ∫⁻ k : ℤ, ‖a k‖ₑ ^ p ∂MeasureTheory.Measure.count
      = ∑ j ∈ s, ENNReal.ofReal ‖a j‖ ^ p := by
    rw [MeasureTheory.lintegral_count]
    rw [tsum_eq_sum (s := s) (f := fun k : ℤ => ‖a k‖ₑ ^ p) ?_]
    · apply Finset.sum_congr rfl; intro j hj; rw [ofReal_norm]
    · intro k hk
      rw [ha k hk]
      simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < p)]
  calc
    ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n =>
        ∑ j ∈ s, ((Q : ℂ) * (if ((Q : ℤ) ∣ (k - j)) then
          (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
            Complex.exp (2 * Real.pi * Complex.I * (((k - j : ℤ) : ℂ) * (ξ : ℂ))))
          else 0)) * a j)) ^ p
        ∂MeasureTheory.Measure.count
      = ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => ∑ j ∈ s, a j * K n (k - j))) ^ p ∂MeasureTheory.Measure.count := by
        apply lintegral_congr; intro k; rw [hsumk k]
    _ = ∑ r ∈ Finset.range Q, ∫⁻ N : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => ∑ j ∈ s, a j * K n ((Q : ℤ) * N + (r : ℤ) - j))) ^ p
          ∂MeasureTheory.Measure.count :=
        lintegral_count_residue (Q := Q) hQ (fun k : ℤ =>
          (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => ∑ j ∈ s, a j * K n (k - j))) ^ p)
    _ ≤ ∑ r ∈ Finset.range Q, ENNReal.ofReal ((C₁ * A) ^ p) *
          ∫⁻ N : ℤ, ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p ∂MeasureTheory.Measure.count :=
        Finset.sum_le_sum hper
    _ = ENNReal.ofReal ((C₁ * A) ^ p) *
          ∑ r ∈ Finset.range Q,
            ∫⁻ N : ℤ, ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p ∂MeasureTheory.Measure.count := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal ((C₁ * A) ^ p) * ∫⁻ k : ℤ, ‖a k‖ₑ ^ p ∂MeasureTheory.Measure.count := by
        rw [lintegral_count_residue (Q := Q) hQ (fun k : ℤ => ‖a k‖ₑ ^ p)]
    _ = ENNReal.ofReal ((C₁ * A) ^ p) * ∑ j ∈ s, ENNReal.ofReal ‖a j‖ ^ p := by rw [hvan]

end Work.BourgainPlan.IonescuWainger
