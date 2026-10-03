import Mathlib
import Submission.Work.KMTAreas.A7.eLpNorm_varNorm_fiberOp_le_of_mass
import Submission.Work.KMTAreas.A7.eLpNorm_residueLp_le
import Submission.Work.KMTAreas.A7Hi.FiberSliceAlgebra
import Submission.Port.Aesm

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## The crude `ℓ^p(V^r)` bound for the fibre of the `g`-side twisted projection

The fibre operator `fiberOpP ρ P l m n₀` is the convolution of its input with the kernel
`j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(α (P n₀ - j))) · cw m j`, so the variational norm of a family
`n ↦ fiberOpP ρ P l m n₀ (w n)` is dominated pointwise by the `ℓ¹`-weighted sum of the variational
norms of the shifted inputs (`fiberOpVarYoungExact`).  The weights are the *modulus* of the kernel
coefficients, and the modulus of the arithmetic character is at most the cardinality of the
frequency set, so the total mass of the weight family is at most `#(ℚ/ℤ)_{≤l} · ∑_j ‖cw m j‖`.
Minkowski/Young for the lattice convolution then gives the `ℓ^p` bound with that constant, and the
average over the residues `n₀ < q` is handled by `eLpNorm_residueLp_le`.

This is deliberately crude: no cancellation in `∑_α e(α (P n₀ - j))` is used, no hypothesis is
placed on the family `w`, and the only input on the bump `m` is the summability and the size of the
`ℓ¹`-mass of its Fourier coefficients `cw m`. -/

/-- **Minkowski/Young on the lattice `ℤ` with the counting measure.**  If `F` is dominated
pointwise by the weighted convolution `∑'_j k j · W (x - j)`, then the `ℓ^s`-norm of `F` is at most
the total mass `∑'_j k j` times the `ℓ^s`-norm of `W`, for `s ≥ 1`. -/
private theorem eLpNorm_tsum_mul_sub_le (s : ℝ) (hs : 1 ≤ s) (k W F : ℤ → ENNReal)
    (hF : ∀ x : ℤ, F x ≤ ∑' j : ℤ, k j * W (x - j)) :
    MeasureTheory.eLpNorm F (ENNReal.ofReal s) MeasureTheory.Measure.count
      ≤ (∑' j : ℤ, k j)
        * MeasureTheory.eLpNorm W (ENNReal.ofReal s) MeasureTheory.Measure.count := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1 : MeasureTheory.eLpNorm F (ENNReal.ofReal s) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑' j : ℤ, k j * W (x - j))
          (ENNReal.ofReal s) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hF x)
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => ∑' j : ℤ, k j * W (x - j))
        (ENNReal.ofReal s) MeasureTheory.Measure.count
      ≤ ∑' j : ℤ, MeasureTheory.eLpNorm (fun x : ℤ => k j * W (x - j))
          (ENNReal.ofReal s) MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm (μ := MeasureTheory.Measure.count)
      (p := ENNReal.ofReal s) (ENNReal.one_le_ofReal.mpr hs)
      (f := fun j : ℤ => fun x : ℤ => k j * W (x - j))
      (fun j => (measurable_of_countable _).aemeasurable)
  have h3 : ∀ j : ℤ, MeasureTheory.eLpNorm (fun x : ℤ => k j * W (x - j))
        (ENNReal.ofReal s) MeasureTheory.Measure.count
      = k j * MeasureTheory.eLpNorm W (ENNReal.ofReal s) MeasureTheory.Measure.count := by
    intro j
    rw [Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
        (f := fun x : ℤ => W (x - j)) (measurable_of_countable _).aemeasurable (k j) hs0,
      Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal W j hs0]
  refine h1.trans (h2.trans ?_)
  rw [tsum_congr h3, ENNReal.tsum_mul_right]

/-- **The modulus of a fibre kernel coefficient.**  The arithmetic character
`∑_{α ∈ A} e(α (y - j))` has modulus at most `#B` for any `B ⊇ A`, by the triangle inequality and
`‖e(·)‖ = 1`. -/
private theorem fiberKernel_enorm_le (A B : Finset Work.Analysis.IonescuWainger.Circle)
    (hAB : A ⊆ B) (m : ℝ → ℂ) (y j : ℤ) :
    ‖(∑ α ∈ A, fourier (T := 1) (y - j) α) * Work.KMTAreas.A7.cw m j‖ₑ
      ≤ ENNReal.ofReal (B.card : ℝ) * ‖Work.KMTAreas.A7.cw m j‖ₑ := by
  have hcard : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card hAB
  have hnorm : ‖∑ α ∈ A, fourier (T := 1) (y - j) α‖ ≤ (B.card : ℝ) := by
    calc ‖∑ α ∈ A, fourier (T := 1) (y - j) α‖
        ≤ ∑ α ∈ A, ‖fourier (T := 1) (y - j) α‖ := norm_sum_le _ _
      _ = ∑ _α ∈ A, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [fourier_apply]
          exact Circle.norm_coe _
      _ = (A.card : ℝ) := by simp
      _ ≤ (B.card : ℝ) := hcard
  rw [enorm_mul, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (B.card : ℝ) by positivity)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- **The crude `ℓ^s(V^r)` bound for the fibre, with the mass of the bump as the only input.**
For an arbitrary family `w` (no boundedness), an arbitrary shift map `P.eval`, and a bump `m` whose
Fourier coefficients `cw m` form a summable family of `ℓ¹`-mass `≤ Cstar`,

`‖ (q⁻¹ ∑_{n₀<q} V^r(n ↦ fiberOp ρ l m (P n₀) (w n))^s)^{1/s} ‖_{ℓ^s(ℤ)}
   ≤ (#(ℚ/ℤ)_{≤l} · Cstar + 1) · ‖ V^r(w) ‖_{ℓ^s(ℤ)}`.

The proof uses no cancellation in the arithmetic character: the mass of the kernel is bounded by
`#(ℚ/ℤ)_{≤l} · ∑_j ‖cw m j‖`. -/
private theorem crude_core (P : Polynomial ℤ) (r : NNReal) (hr : 1 ≤ r) (Cstar : ℝ)
    (hC : 0 < Cstar) (m : ℝ → ℂ)
    (hmassum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    (hmassbd : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) ≤ Cstar)
    (ρ : ℝ) (s : ℝ) (hs : 1 ≤ s) (l₂ q : ℕ) (hq : 0 < q) (w : ℕ → ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp s q (fun y n₀ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₀) (w n) y)) x)
        (ENNReal.ofReal s) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * Cstar + 1)
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => w n x)) (ENNReal.ofReal s) MeasureTheory.Measure.count := by
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hcardnat : (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card
      ≤ (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card := by
    rw [Work.Analysis.IonescuWainger.iwArithFreqsNew]
    exact Finset.card_le_card Finset.sdiff_subset
  have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ)
      ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) := by
    exact_mod_cast hcardnat
  -- Step 1: the pointwise Young inequality, with the crude modulus bound on the weights.
  have hpt : ∀ (n₀ : ℤ) (x : ℤ), PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₀) (w n) x)
      ≤ ∑' j : ℤ, (ENNReal.ofReal ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
            * ‖Work.KMTAreas.A7.cw m j‖ₑ)
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)) := by
    intro n₀ x
    refine (Work.KMTAreas.A7.fiberOpVarYoungExact ρ l₂ m (P.eval n₀) w r hr x).trans ?_
    refine ENNReal.tsum_le_tsum (fun j => mul_le_mul' ?_ le_rfl)
    exact fiberKernel_enorm_le (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) (by
        rw [Work.Analysis.IonescuWainger.iwArithFreqsNew]
        exact Finset.sdiff_subset) m (P.eval n₀) j
  -- Step 2: Minkowski/Young on the lattice.
  have hYoung : ∀ n₀ : ℤ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₀) (w n) x))
        (ENNReal.ofReal s) MeasureTheory.Measure.count
      ≤ (∑' j : ℤ, (ENNReal.ofReal ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
            * ‖Work.KMTAreas.A7.cw m j‖ₑ))
          * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => w n x)) (ENNReal.ofReal s) MeasureTheory.Measure.count :=
    fun n₀ => eLpNorm_tsum_mul_sub_le s hs
      (fun j : ℤ => ENNReal.ofReal ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
          * ‖Work.KMTAreas.A7.cw m j‖ₑ)
      (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
      (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₀) (w n) x))
      (fun x => hpt n₀ x)
  -- Step 3: the total mass of the weights.
  have hmass : (∑' j : ℤ, (ENNReal.ofReal ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
        * ‖Work.KMTAreas.A7.cw m j‖ₑ))
      ≤ ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * Cstar) := by
    rw [ENNReal.tsum_mul_left]
    have h1 : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ)
        = ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) := by
      rw [show (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ)
          = ∑' j : ℤ, ENNReal.ofReal ‖Work.KMTAreas.A7.cw m j‖ from
          tsum_congr (fun j => (ofReal_norm (Work.KMTAreas.A7.cw m j)).symm)]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg (Work.KMTAreas.A7.cw m j))
        hmassum).symm
    rw [h1]
    exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hmassbd)).trans_eq
      (ENNReal.ofReal_mul (by positivity)).symm
  -- Step 4: aggregate over the residues.
  have hres : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp s q (fun y n₀ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₀) (w n) y)) x)
        (ENNReal.ofReal s) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * Cstar)
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => w n x)) (ENNReal.ofReal s) MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_residueLp_le (p := s) hspos
      (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₀) (w n) y))
      (ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * Cstar)
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => w n x)) (ENNReal.ofReal s) MeasureTheory.Measure.count)
      (fun n₀ _ => le_trans (hYoung (n₀ : ℤ)) (mul_le_mul' hmass le_rfl))
  refine hres.trans (mul_le_mul' ?_ le_rfl)
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)

theorem fiberOpP_crude (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r) (Cstar : ℝ) (hC : 0 < Cstar)
    (hCU : ∀ U : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖)
      ∧ (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖) ≤ Cstar) :
    ∀ (ρ : ℝ) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (l₂ U q : ℕ) (hq : 0 < q)
      (w : ℕ → ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U) n₀ (w n) y)) x)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal
          (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * Cstar + 1) *
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => w n x)) p MeasureTheory.Measure.count := by
  intro ρ p hp hptop l₂ U q hq w
  obtain ⟨hmassum, hmassbd⟩ := hCU U
  have hptop' : p ≠ ⊤ := ne_of_lt hptop
  have hr1 : (1 : NNReal) ≤ r :=
    le_of_lt (lt_of_lt_of_le (by norm_num : (1 : NNReal) < 2) hr.le)
  have hs1 : 1 ≤ p.toReal := by
    have h : (1 : ENNReal).toReal ≤ p.toReal := ENNReal.toReal_mono hptop' hp.le
    simpa using h
  have key := crude_core P r hr1 Cstar hC (Work.KMTAreas.A7.mStargF P.natDegree U)
    hmassum hmassbd ρ p.toReal hs1 l₂ q hq w
  rw [ENNReal.ofReal_toReal hptop'] at key
  exact key

end Work.KMTPlan.A6Clean
