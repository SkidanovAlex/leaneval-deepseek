import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxFibLine_fibre_sq_le
import Submission.Work.BoseFixB1S.boxFibLine_uniform
import Submission.Work.BoseFixB1S.boxPQw_mass_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxPQ_abs_bounds`

The two `Q`–`P` cross estimates at the FS-faithful box projections `P = boxPInd`,
`Q = boxQInd` of the sliding box `B(u) = dlBox ℓ d u`, against the localised one-body fibre
`fib(z) = w1Fibre ℓ (wSmall1Pair h M ℓ d u) z`:

1. `|Σᵢ∫_{abox N ℓ} (QᵢΦ)(PᵢΦ)·fib(xᵢ)| ≤ C·a(v)·√(n₊ · (M₁/volA) · S)`,
2. `Σᵢ∫_{abox N ℓ} (QᵢΦ)²·fib(xᵢ) ≤ C·a(v)·n₊`,

where `n₊ = boxQCount`, `S = boxFlatCount`, `M₁ = boxM1 = ∫_A fib`, `volA = boxMass ℓ d u`.

Both are consequences of the *pointwise sign and size* of the fibre
(`boxFibLine_fibre_nonneg`, `boxFibLine_fibre_le`: `0 ≤ fib z ≤ Kf` with
`Kf = K₀·a(v)`, `K₀ = boxFibConst M = (χ·D_M)·(2(χ·D_M)/smallConvLower M)·8π`):

* (2) is the monotonicity of the integral, `boxFibLine_uniform`;
* (1) is the `L²` Cauchy–Schwarz `pqCosCore_aux` for the box cross term, together with
  `boxFibLine_fibre_sq_le` (`∫_A fib² ≤ Kf·∫_A fib`), which turns the `L²` mass of the fibre
  into its `L¹` mass: for each slot `i`, with `G_i = PᵢΦ·fib(xᵢ)`,
  `∫G_i² = (∫_A fib²)·(∫PᵢΦ²)/volA` by the peel identities `Q0C.one_kernel`/`Q0C.one_flat`,
  so `|∫QᵢΦ·G_i| ≤ √(∫(QᵢΦ)²)·√(Kf·(M₁/volA)·∫(PᵢΦ)²)` and Cauchy–Schwarz over `i` gives (1).

The single constant is `C = K₀ + √(K₀/a(v)) + 1`: `K₀ ≤ C` pays for (2), and
`√(Kf) = √(K₀ a(v)) = √(K₀/a(v))·a(v) ≤ C·a(v)` pays for (1).
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real BigOperators

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

-- ===== TEMPORARY: the statements of the three delegated lemmas (to be replaced by imports) =====

private theorem pqCosCore_aux {N : ℕ} {ℓ volA Kf : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {f : E3 → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hf0 : ∀ z, 0 ≤ f z) (hfK : ∀ z, f z ≤ Kf) (hKf0 : 0 ≤ Kf)
    (hfsq : MeasureTheory.IntegrableOn (fun z => f z ^ 2) A)
    (hfsqle : (∫ z in A, f z ^ 2) ≤ Kf * (∫ z in A, f z)) :
    |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * f (x i)|
      ≤ Real.sqrt (Kf * ((∫ z in A, f z) / volA)
          * Work.BoseFixB1S.boxQCount volA ℓ A Φ
          * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) := by
  classical
  have hvolAreal : volA = MeasureTheory.volume.real A := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  have hM1nn : 0 ≤ ∫ z in A, f z :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => hf0 z))
  have hAfin : (MeasureTheory.volume : MeasureTheory.Measure E3) A < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono hAc)
      (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top)
  have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
    rw [Work.BoseFixB1S.boxQCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hSnn : 0 ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
    rw [Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [Work.BoseFixB1S.boxQCount, Work.BoseFixB1S.boxFlatCount]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  -- the compact-box bound on `Φ`
  obtain ⟨BΦ, hBΦ⟩ := (Submission.BoseGases.abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (f := Φ) hΦc.continuousOn
  have hBΦ0 : 0 ≤ BΦ :=
    le_trans (norm_nonneg _) (hBΦ _ (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hbΦ : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Φ x| ≤ BΦ := fun x hx => by
    simpa [Real.norm_eq_abs] using hBΦ x hx
  haveI : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top (n + 1) ℓ hℓ.le⟩
  -- per-slot bound
  have hper : ∀ i : Fin (n + 1),
      |∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
            * f (x i)|
        ≤ Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          * Real.sqrt (Kf * ((∫ z in A, f z) / volA)
              * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) := by
    intro i
    have hQm : Measurable (Work.UBBInputs8.boxQInd volA A i Φ) :=
      Work.BoseFixB1S.measurable_boxQInd volA hA i hΦc.measurable
    have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
      Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦc.measurable
    have hQb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
        |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * BΦ :=
      Work.BoseFixB1S.abs_boxQInd_le hℓ hvol hA hvolAreal hAc i hbΦ
    have hPb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
        |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ BΦ :=
      boxPInd_abs_le_noPos hℓ hvol.le hA hvolA hAc i hBΦ0 hbΦ
    have hFm : AEStronglyMeasurable (Work.UBBInputs8.boxQInd volA A i Φ)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ)) := hQm.aestronglyMeasurable
    have hGm : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X (n + 1) =>
          Work.UBBInputs8.boxPInd volA A i Φ x * f (x i))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
          (Submission.BoseGases.abox (n + 1) ℓ)) :=
      hPm.aestronglyMeasurable.mul (Submission.BoseGases.aem_comp_coord' i hfm)
    have hbF : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X (n + 1))).restrict (Submission.BoseGases.abox (n + 1) ℓ)),
        |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * BΦ := by
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) ℓ)]
      exact ae_of_all _ (fun x hx => hQb x hx)
    have hbG : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X (n + 1))).restrict (Submission.BoseGases.abox (n + 1) ℓ)),
        |Work.UBBInputs8.boxPInd volA A i Φ x * f (x i)| ≤ BΦ * Kf := by
      rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) ℓ)]
      refine ae_of_all _ (fun x hx => ?_)
      have hfK' : |f (x i)| ≤ Kf := by
        rw [abs_of_nonneg (hf0 (x i))]
        exact hfK (x i)
      rw [abs_mul]
      exact mul_le_mul (hPb x hx) hfK' (abs_nonneg _) hBΦ0
    have hCS := Work.BoseFixB1S.Q0C.integral_mul_sq_le (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)) hFm hGm hbF hbG
    have hstep : |∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
            * f (x i)|
        ≤ Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x * f (x i)) ^ 2) := by
      have h1 : |∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * f (x i)|
          = Real.sqrt ((∫ x, (Work.UBBInputs8.boxQInd volA A i Φ x)
                * (Work.UBBInputs8.boxPInd volA A i Φ x * f (x i))
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
                (Submission.BoseGases.abox (n + 1) ℓ))) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        ring
      rw [h1]
      refine le_trans (Real.sqrt_le_sqrt hCS) ?_
      rw [Real.sqrt_mul (integral_nonneg (fun x => sq_nonneg _))]
    -- the `L²` mass of the fibre against the `P`-slot
    have hone := Work.BoseFixB1S.Q0C.one_kernel (volA := volA) hℓ hvol hA hAc hvolAreal i hΦc
      (g := fun z => f z ^ 2) hfsq
    have hG2 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x * f (x i)) ^ 2)
        = (∫ z in A, f z ^ 2)
          * (∫ r in Submission.BoseGases.abox n ℓ,
              (Work.BoseFixB1S.Q0C.oneRest volA A i Φ r) ^ 2) := by
      rw [← hone]
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hflat := Work.BoseFixB1S.Q0C.one_flat (volA := volA) hℓ hvol hA hAc hvolAreal i hΦc
    have hone' : (∫ r in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB1S.Q0C.oneRest volA A i Φ r) ^ 2)
        = (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) / volA := by
      rw [hflat]
      field_simp
    have hG2le : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x * f (x i)) ^ 2)
        ≤ Kf * ((∫ z in A, f z) / volA)
          * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
      rw [hG2, hone']
      have hP2nn : 0 ≤ ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
      calc (∫ z in A, f z ^ 2)
            * ((∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) / volA)
          ≤ (Kf * (∫ z in A, f z))
              * ((∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) / volA) :=
            mul_le_mul_of_nonneg_right hfsqle (div_nonneg hP2nn hvol.le)
        _ = Kf * ((∫ z in A, f z) / volA)
              * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by ring
    exact le_trans hstep
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG2le) (Real.sqrt_nonneg _))
  -- sum over the slots
  have hterm : ∀ i : Fin (n + 1),
      Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        * Real.sqrt (Kf * ((∫ z in A, f z) / volA)
            * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2))
      = Real.sqrt (Kf * ((∫ z in A, f z) / volA))
        * (Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) := by
    intro i
    rw [Real.sqrt_mul (mul_nonneg hKf0 (div_nonneg hM1nn hvol.le))]
    ring
  have hKfM1nn : 0 ≤ Kf * ((∫ z in A, f z) / volA) :=
    mul_nonneg hKf0 (div_nonneg hM1nn hvol.le)
  calc |∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * f (x i)|
      ≤ ∑ i : Fin (n + 1), |∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
            * f (x i)| := by
        simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (f := fun i : Fin (n + 1) => ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
              * f (x i)))
    _ ≤ ∑ i : Fin (n + 1),
          Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            * Real.sqrt (Kf * ((∫ z in A, f z) / volA)
                * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                    (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = Real.sqrt (Kf * ((∫ z in A, f z) / volA))
          * ∑ i : Fin (n + 1),
              Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
                * Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                    (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ Real.sqrt (Kf * ((∫ z in A, f z) / volA))
          * (Real.sqrt (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            * Real.sqrt (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (Real.sum_sqrt_mul_sqrt_le
            (f := fun i : Fin (n + 1) => ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            (g := fun i : Fin (n + 1) => ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
            Finset.univ
            (fun i => integral_nonneg (fun x => sq_nonneg _))
            (fun i => integral_nonneg (fun x => sq_nonneg _)))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt (Kf * ((∫ z in A, f z) / volA)
          * Work.BoseFixB1S.boxQCount volA ℓ A Φ
          * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) := by
        rw [Work.BoseFixB1S.boxQCount, Work.BoseFixB1S.boxFlatCount]
        set SQ : ℝ := ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 with hSQ
        set SS : ℝ := ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 with hSS
        have h1 : 0 ≤ SQ := by
          rw [hSQ]; exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
        have h2 : 0 ≤ SS := by
          rw [hSS]; exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
        rw [← Real.sqrt_mul h1 SS, ← Real.sqrt_mul hKfM1nn (SQ * SS)]
        congr 1
        exact (mul_assoc (Kf * ((∫ z in A, f z) / volA)) SQ SS).symm

-- ===== the fibre constant =====

private def boxFibConst (M : ℕ) : ℝ :=
  (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
    * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        / Work.SmallBoxSliding.smallConvLower M)
      * 8 * Real.pi)

private lemma boxFibConst_nonneg (M : ℕ) : 0 ≤ boxFibConst M := by
  rw [boxFibConst]
  have h1 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  have h2 : 0 ≤ 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (mul_nonneg (by norm_num) h1)
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M))
  have h3 : (0 : ℝ) ≤ 8 := by norm_num
  have h4 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  exact mul_nonneg h1 (mul_nonneg (mul_nonneg h2 h3) h4)

private lemma boxFib_literal_eq (M : ℕ) (a : ℝ) :
    boxFibConst M * a
      = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M)
            * (8 * Real.pi * a)) := by
  rw [boxFibConst]; ring

-- ===== the target =====

theorem boxPQ_abs_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
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
  set a0 : ℝ := _root_.BoseGases.a v with ha0def
  have ha0 : 0 ≤ a0 :=
    (Submission.BoseGases.av_bounds_weak hR0 hv hvrad hv_supp h).1
  have hK0 : 0 ≤ boxFibConst M := boxFibConst_nonneg M
  refine ⟨boxFibConst M + Real.sqrt (boxFibConst M / a0) + 1, ?_, ?_⟩
  · have h2 : 0 ≤ Real.sqrt (boxFibConst M / a0) := Real.sqrt_nonneg _
    linarith
  · intro ℓ d μ hℓ hd hR hRχ u hvol N Φ hΦc
    set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
    set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
    set f : E3 → ℝ := Submission.BoseGases.w1Fibre ℓ
      (Submission.BoseGases.wSmall1Pair h M ℓ d u) with hfdef
    have hAmeas : MeasurableSet A := by
      rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
    have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
      rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
    have hvolA : V = (MeasureTheory.volume A).toReal := by
      rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def]
    have hVpos : 0 < V := hvol
    have hf0 : ∀ z, 0 ≤ f z := by
      intro z
      rw [hfdef]
      exact boxFibLine_fibre_nonneg hR0 hv hvrad hv_supp h u z
    have hfib_le : ∀ z, f z ≤
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M)
            * (8 * Real.pi * _root_.BoseGases.a v)) := by
      intro z
      rw [hfdef]
      exact boxFibLine_fibre_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
    have hKf_eq : boxFibConst M * a0
        = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M)
            * (8 * Real.pi * _root_.BoseGases.a v)) := by
      rw [ha0def]
      exact boxFib_literal_eq M (_root_.BoseGases.a v)
    have hfK : ∀ z, f z ≤ boxFibConst M * a0 := by
      intro z
      rw [hKf_eq]
      exact hfib_le z
    have hKf0 : 0 ≤ boxFibConst M * a0 := mul_nonneg hK0 ha0
    -- the fibre inputs
    have hfm : AEStronglyMeasurable f
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
      have hg0 : AEMeasurable (Submission.BoseGases.g0 v h)
          (MeasureTheory.volume : MeasureTheory.Measure E3) :=
        (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
      have h := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
      rw [hfdef]
      exact h
    obtain ⟨hfsq_int, hfsq_le, _hmass0⟩ :=
      boxFibLine_fibre_sq_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u
    have hfsq : IntegrableOn (fun z => f z ^ 2) A := hfsq_int
    have hfsqle : (∫ z in A, f z ^ 2) ≤ (boxFibConst M * a0) * (∫ z in A, f z) := by
      rw [hKf_eq]
      exact hfsq_le
    -- the Cauchy–Schwarz core
    have hcore := pqCosCore_aux (N := N) (ℓ := ℓ) (volA := V)
      (Kf := boxFibConst M * a0) hℓ hVpos hAmeas hvolA hAc hΦc hfm hf0 hfK hKf0 hfsq hfsqle
    -- nonnegativities and the peel identity for the fibre mass
    have hM1eq : boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u) = ∫ z in A, f z := by
      rw [hfdef]
      rfl
    have hQnn : 0 ≤ boxQCount V ℓ A Φ := boxQCount_nonneg V ℓ A Φ
    have hSnn : 0 ≤ boxFlatCount V ℓ A Φ := by
      rw [boxFlatCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hM1nn : 0 ≤ ∫ z in A, f z :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => hf0 z))
    -- the arithmetic
    have hsqrt : Real.sqrt (boxFibConst M * a0)
        ≤ (boxFibConst M + Real.sqrt (boxFibConst M / a0) + 1) * a0 := by
      have hroot : Real.sqrt (boxFibConst M * a0)
          = Real.sqrt (boxFibConst M / a0) * a0 := by
        have hsq : (boxFibConst M / a0) * (a0 * a0) = boxFibConst M * a0 := by
          rcases eq_or_lt_of_le ha0 with h0 | h0
          · rw [← h0]; ring
          · field_simp
        calc Real.sqrt (boxFibConst M * a0)
            = Real.sqrt ((boxFibConst M / a0) * (a0 * a0)) := by rw [hsq]
          _ = Real.sqrt (boxFibConst M / a0) * Real.sqrt (a0 * a0) :=
              Real.sqrt_mul (div_nonneg hK0 ha0) (a0 * a0)
          _ = Real.sqrt (boxFibConst M / a0) * a0 := by rw [Real.sqrt_mul_self ha0]
      rw [hroot]
      exact mul_le_mul_of_nonneg_right
        (by linarith [Real.sqrt_nonneg (boxFibConst M / a0), hK0]) ha0
    have hArith : Real.sqrt (boxFibConst M * a0 * ((∫ z in A, f z) / V)
          * boxQCount V ℓ A Φ * boxFlatCount V ℓ A Φ)
        ≤ (boxFibConst M + Real.sqrt (boxFibConst M / a0) + 1) * a0
          * Real.sqrt (boxQCount V ℓ A Φ
              * (boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u) / V)
              * boxFlatCount V ℓ A Φ) := by
      have hsplit : Real.sqrt (boxFibConst M * a0 * ((∫ z in A, f z) / V)
            * boxQCount V ℓ A Φ * boxFlatCount V ℓ A Φ)
          = Real.sqrt (boxFibConst M * a0) * Real.sqrt (boxQCount V ℓ A Φ
              * (boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u) / V)
              * boxFlatCount V ℓ A Φ) := by
        rw [show boxFibConst M * a0 * ((∫ z in A, f z) / V)
              * boxQCount V ℓ A Φ * boxFlatCount V ℓ A Φ
            = (boxFibConst M * a0) * (boxQCount V ℓ A Φ
              * (boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u) / V)
              * boxFlatCount V ℓ A Φ) by rw [hM1eq]; ring,
          Real.sqrt_mul hKf0]
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    refine ⟨?_, ?_⟩
    · calc |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x)
              * f (x i)|
          ≤ Real.sqrt ((boxFibConst M * a0) * ((∫ z in A, f z) / V)
              * boxQCount V ℓ A Φ * boxFlatCount V ℓ A Φ) := hcore
        _ ≤ (boxFibConst M + Real.sqrt (boxFibConst M / a0) + 1) * a0
              * Real.sqrt (boxQCount V ℓ A Φ
                  * (boxM1 ℓ A (Submission.BoseGases.wSmall1Pair h M ℓ d u) / V)
                  * boxFlatCount V ℓ A Φ) := hArith
    · have hunif := boxFibLine_uniform (v := v) (R0 := R0) hv_supp hR0 hv hvrad h hM
        hℓ hd hR hRχ u hΦc
      have hstep : boxFibConst M * a0 * boxQCount V ℓ A Φ
          ≤ (boxFibConst M + Real.sqrt (boxFibConst M / a0) + 1) * a0 * boxQCount V ℓ A Φ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (by linarith [Real.sqrt_nonneg (boxFibConst M / a0), hK0]) ha0) hQnn
      refine hunif.trans ?_
      rw [← hKf_eq]
      exact hstep

end

end Work.BoseFixB1S
