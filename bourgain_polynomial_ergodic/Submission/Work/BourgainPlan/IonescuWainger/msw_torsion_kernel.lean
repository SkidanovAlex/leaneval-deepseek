import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.msw_sampling_lp
import Submission.Work.BourgainPlan.IonescuWainger.torsion_kernel_changevar
import Submission.Work.BourgainPlan.IonescuWainger.msw_torsion_dilate
import Submission.Work.BourgainPlan.IonescuWainger.torsion_kernel_classsum
import Submission.Work.BourgainPlan.IonescuWainger.lintegral_count_residue

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped ENNReal BigOperators Interval FourierTransform

/-- **The torsion case of the Magyar–Stein–Wainger sampling principle** (Tao, arXiv:2008.05066, Proposition `msw`(ii)): for a symbol `m` supported in `[-(1/2Q), 1/2Q]`, the discrete multiplier operator whose symbol is the `1/Q`-periodisation `Σ_{b ∈ ℤ} m(ξ - b/Q)` — equivalently, by the computation of its kernel, the operator with the *decimated* kernel `j ↦ Q · [Q ∣ j] · ∫_{-1/2}^{1/2} m(ξ) e^{2πi j ξ} dξ` — is bounded on `ℓ^p(ℤ)` by `O(1)` times the `L^p(ℝ)` operator norm of `Op_m`, uniformly in `Q` and in `m`.

Proof route (short): let `m̃(ξ) := m(ξ/Q)`, so `m̃` is supported in `[-1/2, 1/2]` and `‖Op_{m̃}‖_{L^p(ℝ)} = ‖Op_m‖_{L^p(ℝ)}` (dilation invariance, a change of variables in the Fourier transform, worth isolating as a helper; note that the hypothesis below is stated on band-limited test functions only, so one may need the elementary passage `‖Op_m‖_{L^p} ≤ B_p · A` with `B_p` the `L^p` norm of the band projection `1_{[-1/2,1/2]}`, and `B_p` is then absorbed into the existential constant `C`). The kernel of `Op_{m̃}` is `∫_{-1/2}^{1/2} m̃(ξ) e^{2πi j ξ}dξ = Q · ∫_{-(1/2Q)}^{1/(2Q)} m(u) e^{2πi Q j u} du = Q · m̂(Q j)`, so `Op_{m̃}` is exactly the operator `V` with kernel `j ↦ Q m̂(Q j)` (no decimation), and `msw_sampling_lp` bounds it. The decimated operator `T` (kernel `Q m̂(Q j)` on `Qℤ`, zero off it) is the direct sum of copies of `V` over the `Q` residue classes modulo `Q`: on the class `r`, with `f_r(QN+r) =: a_r(N)`, one has `(T f_r)(QN+r) = (V a_r)(N)` and `T f_r` vanishes off the class, so `‖T‖_{ℓ^p} = ‖V‖_{ℓ^p}`. -/
theorem msw_torsion_kernel {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (hQ : 1 ≤ Q) (m : ℝ → ℂ) (hmi : MeasureTheory.Integrable m)
      (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
          FourierTransform.fourier g ξ = 0) →
        MeasureTheory.lintegral MeasureTheory.volume (fun x : ℝ => ENNReal.ofReal
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => m ξ * FourierTransform.fourier g ξ) x‖ ^ p)
          ≤ ENNReal.ofReal (A ^ p) *
            MeasureTheory.lintegral MeasureTheory.volume
              (fun x : ℝ => ENNReal.ofReal ‖g x‖ ^ p))
      (s : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ n, n ∉ s → a n = 0),
      MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun n : ℤ => ENNReal.ofReal ‖∑ k ∈ s, a k * ((Q : ℂ) *
        (if ((Q : ℤ) ∣ (n - k)) then
          (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
            m ξ * Complex.exp (2 * Real.pi * Complex.I * (((n - k : ℤ) : ℂ) * (ξ : ℂ))))
          else 0))‖ ^ p)
        ≤ ENNReal.ofReal ((C * A) ^ p) *
          MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun n : ℤ => ENNReal.ofReal ‖a n‖ ^ p) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := msw_sampling_lp p hp
  refine ⟨C₁, hC₁pos, ?_⟩
  intro Q hQ m hmi hmsupp A hA hOp s a ha
  simp only [ofReal_norm]
  set W : ℤ → ℂ := fun j => ∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
    m (ξ / (Q : ℝ)) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ))) with hW
  set K : ℤ → ℂ := fun j => (Q : ℂ) * (if (Q : ℤ) ∣ j then
    (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
      m ξ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ)))) else 0) with hK
  have hQne : (Q : ℤ) ≠ 0 := by
    have h1 : (1 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ
    omega
  have hQneR : (Q : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hK0 : ∀ j : ℤ, ¬ (Q : ℤ) ∣ j → K j = 0 := by
    intro j hj
    rw [hK]
    simp [hj]
  have hmti : MeasureTheory.Integrable (fun ξ : ℝ => m (ξ / (Q : ℝ))) := by
    have h := hmi.comp_mul_right' (R := (Q : ℝ)⁻¹) (inv_ne_zero hQneR)
    refine h.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    simp [div_eq_mul_inv]
  have hmtsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → m (ξ / (Q : ℝ)) = 0 := by
    intro ξ hξ
    apply hmsupp
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
  have hOpmt : ∀ g : ℝ → ℂ, MeasureTheory.Integrable g →
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier g ξ = 0) →
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => m (ξ / (Q : ℝ)) * FourierTransform.fourier g ξ) x‖ₑ ^ p
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p := by
    intro g hg hgb
    simpa only [← ofReal_norm] using
      msw_torsion_dilate (lt_trans zero_lt_one hp) hQ m hmi hmsupp A hA hOp g hg hgb
  have hper : ∀ r ∈ Finset.range Q,
      MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun N : ℤ => ‖∑ k ∈ s, a k * K ((Q : ℤ) * N + (r : ℤ) - k)‖ₑ ^ p)
        ≤ ENNReal.ofReal ((C₁ * A) ^ p) *
          MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun N : ℤ => ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p) := by
    intro r hr
    set u : Finset ℤ := (s.filter (fun k => (Q : ℤ) ∣ (k - (r : ℤ)))).image
      (fun k => (k - (r : ℤ)) / (Q : ℤ)) with hu
    set ar : ℤ → ℂ := fun M => a ((Q : ℤ) * M + (r : ℤ)) with har
    have har0 : ∀ M : ℤ, M ∉ u → ar M = 0 := by
      intro M hM
      by_contra hne
      have hmem : (Q : ℤ) * M + (r : ℤ) ∈ s := by
        by_contra hns
        exact hne (ha _ hns)
      have hdvd : (Q : ℤ) ∣ ((Q : ℤ) * M + (r : ℤ) - (r : ℤ)) := ⟨M, by ring⟩
      have hquot : ((Q : ℤ) * M + (r : ℤ) - (r : ℤ)) / (Q : ℤ) = M := by
        rw [show (Q : ℤ) * M + (r : ℤ) - (r : ℤ) = (Q : ℤ) * M by ring]
        exact Int.mul_ediv_cancel_left M hQne
      have hmemu : M ∈ u := by
        rw [hu]
        exact Finset.mem_image.mpr ⟨(Q : ℤ) * M + (r : ℤ),
          Finset.mem_filter.mpr ⟨hmem, hdvd⟩, hquot⟩
      exact hM hmemu
    have hmsw := hC₁ (fun ξ : ℝ => m (ξ / (Q : ℝ))) hmti hmtsupp A hA hOpmt u ar har0
    have hsum : ∀ N : ℤ, (∑ k ∈ s, a k * K ((Q : ℤ) * N + (r : ℤ) - k))
        = ∑ k ∈ u, W (N - k) * ar k := by
      intro N
      rw [torsion_kernel_classsum hQ K hK0 a s (r : ℤ) N]
      rw [hu]
      refine Finset.sum_congr rfl (fun M hM => ?_)
      have hKW : K ((Q : ℤ) * (N - M)) = W (N - M) := by
        rw [hK, hW]
        beta_reduce
        rw [if_pos (show (Q : ℤ) ∣ (Q : ℤ) * (N - M) from ⟨N - M, rfl⟩)]
        simpa only [mul_assoc] using (torsion_kernel_changevar hQ m hmi hmsupp (N - M)).symm
      rw [hKW, har]
      ring
    calc
      MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun N : ℤ => ‖∑ k ∈ s, a k * K ((Q : ℤ) * N + (r : ℤ) - k)‖ₑ ^ p)
        = MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun N : ℤ => ‖∑ k ∈ u, W (N - k) * ar k‖ₑ ^ p) := by
          apply lintegral_congr; intro N; rw [hsum N]
      _ ≤ ENNReal.ofReal ((C₁ * A) ^ p) *
          MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun N : ℤ => ‖ar N‖ₑ ^ p) := by
          simpa only [hW, mul_assoc] using hmsw
      _ = ENNReal.ofReal ((C₁ * A) ^ p) *
          MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun N : ℤ => ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p) := by rw [har]
  have hLHS : MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun n : ℤ => ‖∑ k ∈ s, a k * ((Q : ℂ) *
        (if ((Q : ℤ) ∣ (n - k)) then
          (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
            m ξ * Complex.exp (2 * Real.pi * Complex.I * (((n - k : ℤ) : ℂ) * (ξ : ℂ))))
          else 0))‖ₑ ^ p)
      = MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun n : ℤ => ‖∑ k ∈ s, a k * K (n - k)‖ₑ ^ p) := by
    simp only [hK]
  calc
    MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun n : ℤ => ‖∑ k ∈ s, a k * ((Q : ℂ) *
        (if ((Q : ℤ) ∣ (n - k)) then
          (∫ ξ in (-(1 / 2) : ℝ)..(1 / 2),
            m ξ * Complex.exp (2 * Real.pi * Complex.I * (((n - k : ℤ) : ℂ) * (ξ : ℂ))))
          else 0))‖ₑ ^ p)
      = MeasureTheory.lintegral MeasureTheory.Measure.count
        (fun n : ℤ => ‖∑ k ∈ s, a k * K (n - k)‖ₑ ^ p) := hLHS
    _ = ∑ r ∈ Finset.range Q, MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun N : ℤ => ‖∑ k ∈ s, a k * K ((Q : ℤ) * N + (r : ℤ) - k)‖ₑ ^ p) := by
        rw [lintegral_count_residue (Q := Q) hQ
          (fun n : ℤ => ‖∑ k ∈ s, a k * K (n - k)‖ₑ ^ p)]
    _ ≤ ∑ r ∈ Finset.range Q, ENNReal.ofReal ((C₁ * A) ^ p) *
          MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun N : ℤ => ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p) :=
        Finset.sum_le_sum hper
    _ = ENNReal.ofReal ((C₁ * A) ^ p) * ∑ r ∈ Finset.range Q,
          MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun N : ℤ => ‖a ((Q : ℤ) * N + (r : ℤ))‖ₑ ^ p) := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal ((C₁ * A) ^ p) *
        MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun n : ℤ => ‖a n‖ₑ ^ p) := by
        rw [lintegral_count_residue (Q := Q) hQ (fun n : ℤ => ‖a n‖ₑ ^ p)]


end Work.BourgainPlan.IonescuWainger
