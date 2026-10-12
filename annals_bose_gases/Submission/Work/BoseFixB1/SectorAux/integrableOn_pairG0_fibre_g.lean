import ChallengeDeps
import Submission.Work.BoseFixB1.integrableOn_pairG0_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1.SectorAux

set_option autoImplicit false

/-! ## The general `P P` pair integrand, measurable/box-bounded form -/

/-- **Pair integrability with the doubly projected second factor, from a measurable, box-bounded
`Φ`.**  For `A` measurable with `A ⊆ acube ℓ`, `V = |A|`, `fib` a.e. strongly measurable and
uniformly bounded on the analysis cube, and `Φ` measurable with `|Φ| ≤ Cb` on `abox N ℓ`, the
integrand `P_j(Q_i Φ) · P_j(P_i Φ) · fib(x i)` is integrable over the box `abox N ℓ`.

This is `Work.BoseFixB1.integrableOn_boxQ1_pair_PP_fib` with the hypothesis `Continuous Φ` replaced
by `Measurable Φ` plus the bound `hΦb`. -/
theorem integrableOn_boxQ1_pair_PP_fib_g {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set Work.BoseFixB1.E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hVeq : V = (volume : Measure Work.BoseFixB1.E3).real A)
    {fib : Work.BoseFixB1.E3 → ℝ}
    (hFm : AEStronglyMeasurable fib (volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) (i j : Fin N) :
    IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x
        * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
        * fib (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
  classical
  have hfinA : (volume : Measure Work.BoseFixB1.E3) A < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  -- the bound on `Φ` holds at the nonnegative constant `|Cb|`
  have hCb0 : 0 ≤ |Cb| := abs_nonneg Cb
  have hΦb' : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ |Cb| :=
    fun x hx => le_trans (hΦb x hx) (le_abs_self Cb)
  -- the mean-free projection `Q_i Φ` is bounded on the box
  have hQb : ∀ x : Submission.BoseGases.X N,
      (∀ k : Fin N, x k ∈ Submission.BoseGases.acube ℓ) →
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ |Cb| + |V|⁻¹ * (|Cb| * V) := by
    intro x hx
    have h := Work.SlotWord.abs_boxQInd_le_of_bound (N := N) (L := ℓ) (volA := V) (C := |Cb|)
      hAc hCb0 hfinA (Ψ := Φ) hΦb' i x hx
    simpa only [← hVeq] using h
  have hV0 : 0 ≤ V := hV.le
  have hCq0 : 0 ≤ |Cb| + |V|⁻¹ * (|Cb| * V) :=
    add_nonneg hCb0 (mul_nonneg (inv_nonneg.mpr (abs_nonneg V)) (mul_nonneg hCb0 hV0))
  have hQab : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ |Cb| + |V|⁻¹ * (|Cb| * V) :=
    fun x hx => hQb x hx
  have hvolA : V = ((volume : Measure Work.BoseFixB1.E3) A).toReal := by
    rw [Measure.real_def] at hVeq; exact hVeq
  -- the two box projections are bounded on the box by the bounds of their arguments
  have hPjQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x|
        ≤ |Cb| + |V|⁻¹ * (|Cb| * V) :=
    Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hvolA hAc j hQab
  have hPib : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i Φ x| ≤ |Cb| :=
    Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hvolA hAc i hΦb'
  have hPPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x| ≤ |Cb| :=
    Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hvolA hAc j hPib
  -- measurability: the two projections are measurable, and the fibre is pulled back to a
  -- function of the `i`-th coordinate
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
  -- the integrand is a.e. bounded on the finite-measure box
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hsm
    ((|Cb| + |V|⁻¹ * (|Cb| * V)) * |Cb| * C) ?_
  filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)] with x hx
  have h1 := hPjQb x hx
  have h2 := hPPb x hx
  have hprod : |Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxQInd V A i Φ) x
        * Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x|
      ≤ (|Cb| + |V|⁻¹ * (|Cb| * V)) * |Cb| := by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCq0
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hprod (hC (x i) (hx i)) (abs_nonneg _) (le_trans (abs_nonneg _) hprod)

/-! ## The requested lemma -/

theorem integrableOn_pairG0_fibre_g {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
    {s t : Fin N} (hst : s ≠ t) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
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
  obtain ⟨hFm, C, _hC0, hC⟩ :=
    (Work.BoseFixB1.q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
      hM hℓ hd hR hRχ u).2
  -- Instantiate the general pair integrability at `A = dlBox ℓ d u`, `V = |dlBox ℓ d u|`,
  -- `fib = fib₁`, `i = t` (the fibre slot) and `j = s` (the peeled slot).
  refine integrableOn_boxQ1_pair_PP_fib_g (N := N) (ℓ := ℓ)
    (V := Work.SmallBoxSliding.boxMass ℓ d u)
    (A := Submission.BoseGases.dlBox ℓ d u)
    (fib := Work.BoseFixB1.q1Fib1 h M ℓ d u)
    hℓ hvol (Work.BoseFixB1.q1Box_measurableSet ℓ d u)
    (Work.BoseFixB1.q1Box_subset_acube ℓ d u)
    (Work.BoseFixB1.q1Vol_eq_real ℓ d u) hFm (fun z _ => hC z) hΦm hΦb t s

end Work.BoseFixB1.SectorAux
