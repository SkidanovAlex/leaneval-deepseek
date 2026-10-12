import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.boxQ1CrossSqrtB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

/-!
# `Work.BoseFixB1S.boxPQBoundsFix`

The two per-slot bounds of the box `PQ`-cross line, at the localised one-body fibre
`fib(z) = ∫_{acube ℓ} w_{1,B(u)}(z,y) dy`:

* **the cross term** — Cauchy–Schwarz in the `i`-slot and in `x`:
  `|Σᵢ ∫ QᵢΦ·PᵢΦ·fib(xᵢ)| ≤ √(Σᵢ∫(QᵢΦ)²fib(xᵢ)) · √(Σᵢ∫(PᵢΦ)²fib(xᵢ))`
  (`pqCrossCS` below);
* the two inputs of the right-hand side at the sliding box, both already machine-checked:
  `Σᵢ∫(QᵢΦ)²fib(xᵢ) ≤ KfibConst M·(a v)·n₊` (`Work.BoseFixB1.boxQIndFibreCountB1`) and
  `Σᵢ∫(PᵢΦ)²fib(xᵢ) = (M₁/|B|)·S` (`Work.BoseFixB1.boxPIndFibreMassB1`), with
  `n₊ = boxQCount`, `S = boxFlatCount`, `M₁ = boxM1`.

The assembly is the arithmetic lemma `sqrt_mul_arith`: with `κ = KfibConst M ≥ 0`,
`α = a v ≥ 0` the constant `C := max κ (√(κ/α))` pays both conjuncts.
-/

/-- **Cauchy–Schwarz for the box `PQ` cross term.**  For a pointwise nonnegative weight `ψ`
which is bounded on the cube and a.e. strongly measurable there,

    |Σᵢ ∫_{abox N ℓ} (QᵢΦ)(PᵢΦ)ψ(xᵢ)| ≤ √(Σᵢ∫(QᵢΦ)²ψ(xᵢ)) · √(Σᵢ∫(PᵢΦ)²ψ(xᵢ)) .

This is the triangle inequality, Cauchy–Schwarz on `abox N ℓ` for each `i`
(`Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt`, at the two `MemLp 2` functions
`QᵢΦ·√(ψ(xᵢ))` and `PᵢΦ·√(ψ(xᵢ))`, bounded on the compact box), and Cauchy–Schwarz over the
finite index set (`Real.sum_sqrt_mul_sqrt_le`). -/
theorem pqCrossCS {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ0 : ∀ z, 0 ≤ ψ z) {K : ℝ}
    (hψK : ∀ z, ψ z ≤ K)
    (hψm : MeasureTheory.AEStronglyMeasurable ψ
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))) :
    |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ψ (x i)|
      ≤ Real.sqrt (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * ψ (x i))
        * Real.sqrt (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * ψ (x i)) := by
  classical
  obtain ⟨C, hC0, hΦb, hPb, hQb⟩ := boxBounds hℓ hvol hA hvolA hAc hΦc
  have hK0 : 0 ≤ K := le_trans (hψ0 0) (hψK 0)
  haveI hfin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (ne_of_lt (Submission.BoseGases.abox_lt_top N ℓ hℓ.le))
  have hper : ∀ i : Fin N,
      |∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
            * ψ (x i)|
        ≤ Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * ψ (x i))
          * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * ψ (x i)) := by
    intro i
    have hψc : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N => Real.sqrt (ψ (x i)))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (Submission.BoseGases.aem_comp_coord' (N := N) (ℓ := ℓ) i hψm)
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
      measurable_boxQInd volA hA i hΦc.measurable
    have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
      measurable_boxPInd volA A hA i hΦc.measurable
    have hfF : MeasureTheory.MemLp
        (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxQInd volA A i Φ x * Real.sqrt (ψ (x i))) 2
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) := by
      refine MeasureTheory.MemLp.of_bound (hQm.aestronglyMeasurable.mul hψc)
        ((2 * C) * Real.sqrt K) ?_
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := hQb i x hx
      have h2 : |Real.sqrt (ψ (x i))| ≤ Real.sqrt K := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hψK (x i))
      exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
    have hgF : MeasureTheory.MemLp
        (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxPInd volA A i Φ x * Real.sqrt (ψ (x i))) 2
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) := by
      refine MeasureTheory.MemLp.of_bound (hPm.aestronglyMeasurable.mul hψc)
        (C * Real.sqrt K) ?_
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C := hPb i x hx
      have h2 : |Real.sqrt (ψ (x i))| ≤ Real.sqrt K := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hψK (x i))
      exact mul_le_mul h1 h2 (abs_nonneg _) hC0
    have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hfF hgF
    calc |∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
              * ψ (x i)|
        = |∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x * Real.sqrt (ψ (x i)))
              * (Work.UBBInputs8.boxPInd volA A i Φ x * Real.sqrt (ψ (x i)))| := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          refine Filter.Eventually.of_forall (fun x => ?_)
          have hs : Real.sqrt (ψ (x i)) * Real.sqrt (ψ (x i)) = ψ (x i) := by
            rw [← pow_two]; exact Real.sq_sqrt (hψ0 (x i))
          calc Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
                * ψ (x i)
              = (Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
                  * (Real.sqrt (ψ (x i)) * Real.sqrt (ψ (x i))) := by rw [hs]
            _ = (Work.UBBInputs8.boxQInd volA A i Φ x * Real.sqrt (ψ (x i)))
                  * (Work.UBBInputs8.boxPInd volA A i Φ x * Real.sqrt (ψ (x i))) := by ring
      _ ≤ Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x * Real.sqrt (ψ (x i))) ^ 2)
            * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x * Real.sqrt (ψ (x i))) ^ 2) := hcs
      _ = Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * ψ (x i))
            * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * ψ (x i)) := by
          congr 1
          · congr 1
            apply MeasureTheory.integral_congr_ae
            refine Filter.Eventually.of_forall (fun x => ?_)
            dsimp only
            rw [mul_pow, Real.sq_sqrt (hψ0 (x i))]
          · congr 1
            apply MeasureTheory.integral_congr_ae
            refine Filter.Eventually.of_forall (fun x => ?_)
            dsimp only
            rw [mul_pow, Real.sq_sqrt (hψ0 (x i))]
  have hAnn : ∀ i : Fin N, 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * ψ (x i) :=
    fun i => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hψ0 (x i))))
  have hBnn : ∀ i : Fin N, 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * ψ (x i) :=
    fun i => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hψ0 (x i))))
  calc |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
            * ψ (x i)|
      ≤ ∑ i : Fin N, |∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
            * ψ (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N,
          Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * ψ (x i))
            * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * ψ (x i)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ ≤ Real.sqrt (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * ψ (x i))
          * Real.sqrt (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * ψ (x i)) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ hAnn hBnn

/-- **The arithmetic core of the two-conjunct constant.**  For `κ, α, X, W ≥ 0`,

    `√(κ·α·X)·√W ≤ max κ (√(κ/α))·α·√(X·W)` .

The two extremes: `√(κ·α) = √(κ/α)·α` (both sides are `0` at `α = 0`), and
`√(κ/α) ≤ max κ (√(κ/α))`. -/
lemma sqrt_mul_arith (κ α X W : ℝ) (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hX : 0 ≤ X) (hW : 0 ≤ W) :
    Real.sqrt (κ * α * X) * Real.sqrt W
      ≤ max κ (Real.sqrt (κ / α)) * α * Real.sqrt (X * W) := by
  have hsq : (κ / α) * (α * α) = κ * α := by
    rcases eq_or_lt_of_le hα with h0 | h0
    · subst h0; simp
    · have h1 : (κ / α) * (α * α) = κ * (α⁻¹ * α) * α := by ring
      rw [h1, inv_mul_cancel₀ (ne_of_gt h0), mul_one]
  have hroot : Real.sqrt (κ * α) = Real.sqrt (κ / α) * α := by
    rw [← hsq, Real.sqrt_mul (div_nonneg hκ hα) (α * α), Real.sqrt_mul_self hα]
  have hstep : Real.sqrt (κ * α * X) * Real.sqrt W
      = Real.sqrt (κ * α) * Real.sqrt (X * W) := by
    rw [← Real.sqrt_mul (mul_nonneg (mul_nonneg hκ hα) hX) W,
      show κ * α * X * W = κ * α * (X * W) by ring,
      Real.sqrt_mul (mul_nonneg hκ hα) (X * W)]
  rw [hstep, hroot]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hα) (Real.sqrt_nonneg _)

theorem boxPQBoundsFix {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
        (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ),
        |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)|
          ≤ C * (_root_.BoseGases.a v)
              * Real.sqrt (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ
                  * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                      (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                    / Work.SmallBoxSliding.boxMass ℓ d u)
                  * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                      (Submission.BoseGases.dlBox ℓ d u) Φ)
          ∧ (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
                * Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            ≤ C * (_root_.BoseGases.a v)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  have hα0 : 0 ≤ _root_.BoseGases.a v := Work.BoseFixB1.a_nonneg hR0 hv hvrad hv_supp h
  refine ⟨max (Work.BoseFixB1.KfibConst M)
      (Real.sqrt (Work.BoseFixB1.KfibConst M / _root_.BoseGases.a v)),
    le_trans (Work.BoseFixB1.KfibConst_nonneg M) (le_max_left _ _), ?_⟩
  intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦc
  -- ## the localised fibre: sign, size and a.e. strong measurability
  have hfib0 : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
    fun z => boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
  have hfibK : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
        ≤ Work.BoseFixB1.Kfib (v := v) M :=
    fun z => le_trans (le_abs_self _)
      (Work.BoseFixB1.q1cw1_w1Fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h hM
        hℓ hd hR hRχ u z)
  have hfibm : MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)) := by
    have hg0 : AEMeasurable (Submission.BoseGases.g0 v h)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      (Submission.BoseGases.g0_integrable (R := R0) hR0 hv_supp h).aemeasurable
    have hh := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
    simpa only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.w1Fibre] using hh
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- ## Cauchy–Schwarz, and the two inputs of its right-hand side
  have hCS := pqCrossCS hℓ hvol hAmeas hvolA hAc hΦc
    (ψ := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
    hfib0 (K := Work.BoseFixB1.Kfib (v := v) M) hfibK hfibm
  have hF1 := Work.BoseFixB1.boxQIndFibreCountB1 (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
    hM hℓ hd hR hRχ u hvol hΦc
  have hF2 := Work.BoseFixB1.boxPIndFibreMassB1 (v := v) (R0 := R0) hv_supp hR0 hv hvrad hv1 h
    hM hℓ hd hR hRχ u hvol hΦc
  have hKfib : Work.BoseFixB1.Kfib (v := v) M
      = Work.BoseFixB1.KfibConst M * _root_.BoseGases.a v :=
    Work.BoseFixB1.Kfib_eq_KfibConst_mul_a v M
  have hF1' : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      ≤ Work.BoseFixB1.KfibConst M * _root_.BoseGases.a v
        * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
    rw [hKfib] at hF1
    exact hF1
  -- ## nonnegativity of the counts and of the fibre mass
  have hQ0 : 0 ≤ Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ :=
    Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ :=
    Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  have hM10 : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Submission.BoseGases.wSmall1Pair h M ℓ d u) :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => hfib0 z))
  have hW0 : 0 ≤ (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        / Work.SmallBoxSliding.boxMass ℓ d u)
      * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) Φ :=
    mul_nonneg (div_nonneg hM10 (le_of_lt hvol)) hS0
  -- ## the arithmetic
  have harith := sqrt_mul_arith (Work.BoseFixB1.KfibConst M) (_root_.BoseGases.a v)
    (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
      (Submission.BoseGases.dlBox ℓ d u) Φ)
    ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      / Work.SmallBoxSliding.boxMass ℓ d u)
      * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
          (Submission.BoseGases.dlBox ℓ d u) Φ)
    (Work.BoseFixB1.KfibConst_nonneg M) hα0 hQ0 hW0
  have hconj1 : |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)|
          ≤ max (Work.BoseFixB1.KfibConst M)
              (Real.sqrt (Work.BoseFixB1.KfibConst M / _root_.BoseGases.a v))
            * (_root_.BoseGases.a v)
            * Real.sqrt (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                  / Work.SmallBoxSliding.boxMass ℓ d u)
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ) := by
    refine hCS.trans ?_
    calc Real.sqrt (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          * Real.sqrt (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
              * Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        ≤ Real.sqrt (Work.BoseFixB1.KfibConst M * _root_.BoseGases.a v
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ)
            * Real.sqrt ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                / Work.SmallBoxSliding.boxMass ℓ d u)
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ) :=
          mul_le_mul (Real.sqrt_le_sqrt hF1') (le_of_eq (congrArg Real.sqrt hF2))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ max (Work.BoseFixB1.KfibConst M)
              (Real.sqrt (Work.BoseFixB1.KfibConst M / _root_.BoseGases.a v))
            * (_root_.BoseGases.a v)
            * Real.sqrt (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                  / Work.SmallBoxSliding.boxMass ℓ d u)
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ) := by
          rw [show (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ)
                * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                  / Work.SmallBoxSliding.boxMass ℓ d u)
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ
              = (Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ)
                * ((Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u)
                  / Work.SmallBoxSliding.boxMass ℓ d u)
                  * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                      (Submission.BoseGases.dlBox ℓ d u) Φ) from by ring]
          exact harith
  have hconj2 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      ≤ max (Work.BoseFixB1.KfibConst M)
          (Real.sqrt (Work.BoseFixB1.KfibConst M / _root_.BoseGases.a v))
        * (_root_.BoseGases.a v)
        * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ := by
    refine hF1'.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hα0) hQ0
  exact ⟨hconj1, hconj2⟩

end Work.BoseFixB1S
