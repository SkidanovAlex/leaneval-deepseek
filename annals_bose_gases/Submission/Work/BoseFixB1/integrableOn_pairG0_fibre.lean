import ChallengeDeps
import Submission.Work.BoseFixB1.Q1FibBound
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false

/-! ## The general `P P` pair integrand -/

/-- **Pair integrability with the doubly projected second factor.**  For `A` measurable with
`A ⊆ acube ℓ`, `V = |A|`, and a fibre `fib` that is a.e. strongly measurable and uniformly
bounded on the analysis cube, the integrand
`P_j(Q_i Φ) · P_j(P_i Φ) · fib(x i)` is integrable over the box `abox N ℓ`.

This is `Work.BoseFixB1.integrableOn_boxQ1_pair_fib` with the second factor `P_i Φ` replaced
by `P_j(P_i Φ)` (the form produced by the one-slot peel); both factors are bounded on the box
by the bounds of `Q_i Φ` resp. `Φ`, so the same `IntegrableOn.of_bound` argument applies. -/
theorem integrableOn_boxQ1_pair_PP_fib {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hVeq : V = (volume : Measure E3).real A)
    {fib : E3 → ℝ}
    (hFm : AEStronglyMeasurable fib (volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i j : Fin N) :
    IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x
        * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
        * fib (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
  classical
  -- `Φ` is continuous, hence bounded on the compact analysis box, and measurable.
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := Work.BoseFixB1S.exists_abox_bound (N := N) hℓ hΦc
  have hΦm : Measurable Φ := hΦc.measurable
  have hfinA : (volume : Measure E3) A < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  -- The mean-free projection `Q_iΦ` is bounded on the box by `CΦ + |V|⁻¹(CΦ·V)`.
  have hQb : ∀ x : Submission.BoseGases.X N,
      (∀ k : Fin N, x k ∈ Submission.BoseGases.acube ℓ) →
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ CΦ + |V|⁻¹ * (CΦ * V) := by
    intro x hx
    have h := Work.SlotWord.abs_boxQInd_le_of_bound (N := N) (L := ℓ) (volA := V) (C := CΦ)
      hAc hCΦ0 hfinA (Ψ := Φ) (fun y hy => hCΦ y hy) i x hx
    simpa only [← hVeq] using h
  have hV0 : 0 ≤ V := hV.le
  have hCq0 : 0 ≤ CΦ + |V|⁻¹ * (CΦ * V) :=
    add_nonneg hCΦ0 (mul_nonneg (inv_nonneg.mpr (abs_nonneg V)) (mul_nonneg hCΦ0 hV0))
  have hQab : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ CΦ + |V|⁻¹ * (CΦ * V) :=
    fun x hx => hQb x hx
  have hvolA : V = ((volume : Measure E3) A).toReal := by
    rw [Measure.real_def] at hVeq; exact hVeq
  -- The two box projections are bounded on the box by the bounds of their arguments.
  have hPjQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x|
        ≤ CΦ + |V|⁻¹ * (CΦ * V) :=
    Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hvolA hAc j hQab
  have hPib : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i Φ x| ≤ CΦ :=
    Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hvolA hAc i hCΦ
  have hPPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x| ≤ CΦ :=
    Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hvolA hAc j hPib
  -- Measurability: the two projections are measurable, and the fibre is pulled back to a
  -- function of the `i`-th coordinate.
  have hsm : AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x
        * Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x * fib (x i))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) := by
    have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) :=
      Work.SlotWord.measurable_boxQInd V A hA i hΦm
    have h1 : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd V A hA j hQm
    have h2 : Measurable (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x) :=
      Work.BoseFixB1S.measurable_boxPInd V A hA j
        (Work.BoseFixB1S.measurable_boxPInd V A hA i hΦm)
    exact ((h1.mul h2).aestronglyMeasurable).mul (Submission.BoseGases.aem_comp_coord' i hFm)
  -- The integrand is a.e. bounded on the finite-measure box.
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hsm
    ((CΦ + |V|⁻¹ * (CΦ * V)) * CΦ * C) ?_
  filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)] with x hx
  have h1 := hPjQb x hx
  have h2 := hPPb x hx
  have hprod : |Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x
        * Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x|
      ≤ (CΦ + |V|⁻¹ * (CΦ * V)) * CΦ := by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCq0
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hprod (hC (x i) (hx i)) (abs_nonneg _) (le_trans (abs_nonneg _) hprod)

/-! ## The requested lemma -/

theorem integrableOn_pairG0_fibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x t)))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  -- The `g₀`-fibre `fib₁ = w1Fibre ℓ (wSmall1Pair h M ℓ d u)` is a.e. strongly measurable
  -- and uniformly bounded on the analysis cube (`Q1FibBound`, fibre-`g₀` component).
  obtain ⟨hFm, C, hC0, hC⟩ :=
    (q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u).2
  -- Instantiate the general pair integrability at `A = dlBox ℓ d u`, `V = |dlBox ℓ d u|`,
  -- `fib = fib₁`, `i = t` (the fibre slot) and `j = s` (the peeled slot).
  refine integrableOn_boxQ1_pair_PP_fib (N := N) (ℓ := ℓ)
    (V := Work.SmallBoxSliding.boxMass ℓ d u)
    (A := Submission.BoseGases.dlBox ℓ d u)
    (fib := q1Fib1 h M ℓ d u)
    hℓ hvol (q1Box_measurableSet ℓ d u) (q1Box_subset_acube ℓ d u)
    (q1Vol_eq_real ℓ d u) hFm (fun z _ => hC z) hΦc t s

end Work.BoseFixB1
