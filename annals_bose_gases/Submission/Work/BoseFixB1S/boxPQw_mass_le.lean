import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.BoxPotDefs
import Submission.Work.BoseFixB1S.boxM1Info
import Submission.Work.BoseFixB1S.wSmallPairG0FibreLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxPQw_mass_le`

The `|w_{B(u)}|`-weighted `(P Q)`-pair mass at the FS-faithful box projections is
`n₊`-linear:

    Σ_{p ∈ pairSet N} ∫_{abox N ℓ} (P_{p.1}(Q_{p.2}Φ))² · |wSmallPair M ℓ d u (g₀) (x p.1) (x p.2)|
      ≤ C(M) · (a v) · |B(u)|⁻¹ · N · n₊(B(u)) .

The mathematical content is the pair of estimates

* `boxPIndPairMassLe` (the peel): for a nonnegative kernel `k` whose `A`-fibre integral is `≤ C`
  (`A = dlBox ℓ d u`), peeling the `P`-slot gives
  `∫(P_iΨ)²k(x i)(x j) ≤ C·∫_r (oneRest r)²`;
* `oneRest_sq_integral_le`: `∫_r (oneRest r)² ≤ volA⁻¹·∫(1_A(x i)Ψ)²`  (Cauchy–Schwarz on the
  `A`-fibre),

together with the sharp fibre bound `wSmallPairG0FibreLe` for the kernel `|w_{B(u)}|` at the
numerator `g₀` and the combinatorial identity `sum_pairSet_second_eq`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 0. The degenerate bump at `M = 0` -/

lemma chiSmallNormSq_zero : Submission.BoseGases.chiSmallNormSq 0 = 0 := by
  dsimp [Submission.BoseGases.chiSmallNormSq, Submission.BoseGases.chiSmallBase]
  simp only [pow_zero, one_pow]
  rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def,
    MeasureTheory.measure_univ_of_isAddLeftInvariant]
  simp

lemma chiSmall_zero_M0 (z : EuclideanSpace ℝ (Fin 3)) : Submission.BoseGases.chiSmall 0 z = 0 := by
  rw [Submission.BoseGases.chiSmall, chiSmallNormSq_zero, Real.sqrt_zero, div_zero]

lemma chiSmallB_zero_M0 {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB 0 ℓ d u x = 0 := by
  rw [Submission.BoseGases.chiSmallB, chiSmall_zero_M0, mul_zero]

lemma wSmallPair_zero_M0 {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wSmallPair 0 ℓ d u f x y = 0 := by
  simp only [Submission.BoseGases.wSmallPair, chiSmallB_zero_M0, zero_mul]

/-! ## 1. Elementary nonnegativity and emptiness facts -/

lemma boxQCount_nonneg {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (Φ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  rw [Work.BoseFixB1S.boxQCount]
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))

/-- The pair set is empty in the degenerate cases `N ≤ 1`.

Hygiene fix (this session): this was the **last non-private** copy of the name; the tree also has
`private` copies at `boxPairValue.lean:53`, `boxWeightedPairMass.lean:59`,
`boxPQw_mass_leB1.lean:56`, `BoseFixB3/Tests.lean:34` and
`Work/BoseFixB1/rungXB_le_pairMass.lean:51` (renamed `...'`).  Any cone containing two
non-private copies failed with "*a non-private declaration has already been declared*", which made
`Submission/Work/BoseFixB1S/boxWeightedPairMass.lean` **unbuildable** and blocked the assembly of
`FINDING_mfSection10FewB1_session3.md` §10.  This copy is used only in this file (line 481). -/
private lemma pairSet_eq_empty_of_le_one {N : ℕ} (hN : N ≤ 1) :
    Submission.BoseGases.pairSet N = ∅ := by
  ext p
  simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false]
  intro hne
  refine hne (Fin.ext ?_)
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  omega

/-! ## 2. Measurability and boundedness of the box projections -/

lemma measurable_boxQInd {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (Work.UBBInputs8.boxQInd volA A i Φ) := by
  have h1 : Measurable (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦ
  have h2 : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦ
  exact h1.sub h2

lemma abs_boxQInd_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) (hvolA : volA = MeasureTheory.volume.real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := by
  have hvolA' : volA = (MeasureTheory.volume A).toReal := by
    rw [hvolA, MeasureTheory.Measure.real_def]
  intro x hx
  have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    rw [abs_mul]
    have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hmem : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul hσ (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have h2 : |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA' hAc i hC x hx
  have h3 : Work.UBBInputs8.boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
        - Work.UBBInputs8.boxPInd volA A i Φ x := rfl
  rw [h3]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd volA A i Φ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
          + |Work.UBBInputs8.boxPInd volA A i Φ x| := abs_sub _ _
    _ ≤ C + C := add_le_add h1 h2
    _ = 2 * C := by ring

/-! ## 3. The two measure-theoretic estimates (delegated) -/

/-- **Peel at the `P`-slot against a general kernel.** -/
lemma boxPIndPairMassLe_aux {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin (n + 1)} (hij : i ≠ j)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hkC : ∀ a : EuclideanSpace ℝ (Fin 3), ∫ y in A, k y a ≤ C)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨm : Measurable Ψ) {B : ℝ} (hB0 : 0 ≤ B)
    (hBb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Ψ x| ≤ B)
    (hint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * k (x i) (x j))
      (Submission.BoseGases.abox (n + 1) ℓ) MeasureTheory.volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * k (x i) (x j))
      ≤ C * ∫ r in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 := by
  have hAfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ∞ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hboxfin : (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n ℓ) < ∞ :=
    Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  haveI hfinab : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hboxfin⟩
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  -- ## the peel
  rw [Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
    (fun x => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * k (x i) (x j)) hint]
  -- ## the pointwise value at an inserted configuration
  have hpt : ∀ (t : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n),
      (Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
        * k ((Submission.BoseGases.kcInsN n i (t, r)) i)
            ((Submission.BoseGases.kcInsN n i (t, r)) j)
      = Work.BoseFixB1S.Aind A t
        * ((Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * k t (r j')) := by
    intro t r
    rw [Work.BoseFixB1S.Q0C.boxPInd_sq_kcInsN, ← hj', Submission.BoseGases.kc_insN_apply_succ]
    simp only [Work.BoseFixB1S.Aind, Submission.BoseGases.kc_insN_apply_same]
    ring
  -- ## the bound on the inner integral
  have hbound : ∀ r : Submission.BoseGases.X n,
      (∫ t in Submission.BoseGases.acube ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
          * k ((Submission.BoseGases.kcInsN n i (t, r)) i)
              ((Submission.BoseGases.kcInsN n i (t, r)) j))
      ≤ (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * C := by
    intro r
    have h1 : (∫ t in Submission.BoseGases.acube ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
          * k ((Submission.BoseGases.kcInsN n i (t, r)) i)
              ((Submission.BoseGases.kcInsN n i (t, r)) j))
        = (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * (∫ t in A, k t (r j')) := by
      simp only [hpt]
      rw [show (fun t : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1S.Aind A t
            * ((Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * k t (r j')))
          = fun t : EuclideanSpace ℝ (Fin 3) =>
            (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * (Work.BoseFixB1S.Aind A t * k t (r j'))
          from funext (fun t => by ring)]
      rw [MeasureTheory.integral_const_mul]
      congr 1
      simpa only [Work.BoseFixB1S.Aind] using
        Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc (fun t => k t (r j'))
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hkC (r j')) (sq_nonneg _)
  -- ## integrability of the two sides of the outer integration
  have hinner_int : Integrable (fun r : Submission.BoseGases.X n =>
      ∫ t in Submission.BoseGases.acube ℓ,
        (Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
          * k ((Submission.BoseGases.kcInsN n i (t, r)) i)
              ((Submission.BoseGases.kcInsN n i (t, r)) j))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine (Submission.BoseGases.abox_peel_inner_integrable (n := n) (ℓ := ℓ) i _ hint).congr ?_
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with t
    rw [Submission.BoseGases.kc_insN_apply_same]
  have hrest_bd : ∀ r ∈ Submission.BoseGases.abox n ℓ,
      |Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r|
        ≤ |(1 / volA)| * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A) := by
    intro r hr
    have h : |∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))|
        ≤ B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := by
      have hh := norm_setIntegral_le_of_norm_le_const hAfin (s := A)
        (f := fun t : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        (C := B) (fun t ht => by
          rw [Real.norm_eq_abs]
          exact hBb _ (Work.BoseFixB1S.kcInsN_mem_abox hAc i ht hr))
      simpa [Real.norm_eq_abs] using hh
    rw [Work.BoseFixB1S.Q0C.oneRest_def, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hrest_int : Integrable (fun r : Submission.BoseGases.X n =>
      (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * C)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine Integrable.mono'
      (integrableOn_const (C := (|(1 / volA)| * (B * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)) ^ 2 * C)
        hboxfin.ne) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
          Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r)
          ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
        simpa only [Work.BoseFixB1S.Q0C.oneRest_def] using
          (Work.BoseFixB1S.Q0C.aem_oneRest (ℓ := ℓ) volA A i hΨm).const_mul (1 / volA)
      exact (h1.pow 2).mul_const C
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right
        (by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hrest_bd r hr) 2) hC0
  -- ## conclude
  calc (∫ r in Submission.BoseGases.abox n ℓ,
        ∫ t in Submission.BoseGases.acube ℓ,
          (Work.UBBInputs8.boxPInd volA A i Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
            * k ((Submission.BoseGases.kcInsN n i (t, r)) i)
                ((Submission.BoseGases.kcInsN n i (t, r)) j))
      ≤ ∫ r in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 * C :=
        integral_mono_ae hinner_int hrest_int (Filter.Eventually.of_forall hbound)
    _ = C * ∫ r in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2 := by
        rw [MeasureTheory.integral_mul_const]
        ring

/-- **The `oneRest`-mass bound** (Cauchy–Schwarz on the `A`-fibre). -/
lemma oneRest_sq_integral_le_aux {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = MeasureTheory.volume.real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin (n + 1)) {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨm : Measurable Ψ)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hBb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Ψ x| ≤ B) :
    (∫ r in Submission.BoseGases.abox n ℓ, (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2)
      ≤ volA⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.BoseFixB1S.Aind A (x i) * Ψ x) ^ 2) := by
  have hAfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ∞ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  haveI hfinA : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  have hboxfin : (volume : Measure (Submission.BoseGases.X n)) (Submission.BoseGases.abox n ℓ) < ∞ :=
    Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  haveI hfinab : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hboxfin⟩
  -- ## the pointwise Cauchy–Schwarz bound, a.e. in `r`
  have hCS : ∀ᵐ r ∂((volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)),
      (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2
        ≤ volA⁻¹ * ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2 := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    refine ae_of_all _ (fun r hr => ?_)
    have hb1 : ∀ᵐ t ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A),
        |(fun t : EuclideanSpace ℝ (Fin 3) =>
            Ψ (Submission.BoseGases.kcInsN n i (t, r)))| t ≤ B := by
      rw [ae_restrict_iff' hA]
      refine ae_of_all _ (fun t ht => ?_)
      exact hBb _ (Work.BoseFixB1S.kcInsN_mem_abox hAc i ht hr)
    have hb2 : ∀ᵐ t ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A),
        |(fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))| t ≤ 1 :=
      ae_of_all _ (fun t => by simp)
    have hm1 : AEStronglyMeasurable
        (fun t : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
      ((hΨm.comp ((Submission.BoseGases.kcInsN n i).measurable.comp
        (by fun_prop : Measurable fun t : EuclideanSpace ℝ (Fin 3) =>
          (t, r))))).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable
        (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
      aestronglyMeasurable_const
    have hcs := Work.BoseFixB1S.Q0C.integral_mul_sq_le
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) hm1 hm2 hb1 hb2
    simp only [mul_one, one_pow] at hcs
    have hvolAset : (∫ t in A, (1 : ℝ)) = volA := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      exact hvolA.symm
    rw [hvolAset] at hcs
    rw [Work.BoseFixB1S.Q0C.oneRest_def]
    have hX2 : ((1 / volA) * ∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
        = (∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2 / volA ^ 2 := by
      field_simp
    have hY2 : volA⁻¹ * ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
        = (∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2) * volA / volA ^ 2 := by
      field_simp
    rw [hX2, hY2]
    exact div_le_div_of_nonneg_right hcs (by positivity)
  -- ## boundedness of `oneRest` on the box
  have hone_bd : ∀ r ∈ Submission.BoseGases.abox n ℓ,
      |Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r| ≤ B := by
    intro r hr
    have h1 : |∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))| ≤ B * volA := by
      have h := norm_setIntegral_le_of_norm_le_const hAfin (s := A)
        (f := fun t : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (t, r)))
        (C := B) (fun t ht => by
          rw [Real.norm_eq_abs]
          exact hBb _ (Work.BoseFixB1S.kcInsN_mem_abox hAc i ht hr))
      rwa [← hvolA] at h
    rw [Work.BoseFixB1S.Q0C.oneRest_def, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
    calc (1 / volA) * |∫ t in A, Ψ (Submission.BoseGases.kcInsN n i (t, r))|
        ≤ (1 / volA) * (B * volA) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by field_simp
  -- ## integrability of the two sides
  have hLint : Integrable (fun r : Submission.BoseGases.X n =>
      (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine Integrable.mono' (integrableOn_const (C := B ^ 2) hboxfin.ne) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
          Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r)
          ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
        simpa only [Work.BoseFixB1S.Q0C.oneRest_def] using
          (Work.BoseFixB1S.Q0C.aem_oneRest (ℓ := ℓ) volA A i hΨm).const_mul (1 / volA)
      exact h1.pow 2
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r)) (hone_bd r hr) 2
  have hRsm : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
      ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2) := by
    have h2 : StronglyMeasurable (Function.uncurry (fun (r : Submission.BoseGases.X n)
        (t : EuclideanSpace ℝ (Fin 3)) => (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2)) := by
      have hmap : Measurable (fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.kcInsN n i (p.2, p.1)) :=
        (Submission.BoseGases.kcInsN n i).measurable.comp (by fun_prop)
      exact ((hΨm.comp hmap).pow_const 2).stronglyMeasurable
    exact StronglyMeasurable.integral_prod_right
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) h2
  have hRint : Integrable (fun r : Submission.BoseGases.X n =>
      volA⁻¹ * ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    refine Integrable.mono' (integrableOn_const (C := B ^ 2) hboxfin.ne) (hRsm.aestronglyMeasurable.const_mul _) ?_
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with r hr
    have h1 : |∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2| ≤ B ^ 2 * volA := by
      have h := norm_setIntegral_le_of_norm_le_const hAfin (s := A)
        (f := fun t : EuclideanSpace ℝ (Fin 3) => (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2)
        (C := B ^ 2) (fun t ht => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
            (hBb _ (Work.BoseFixB1S.kcInsN_mem_abox hAc i ht hr)) 2)
      rwa [← hvolA] at h
    have hintnn : 0 ≤ ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2 :=
      integral_nonneg (fun t => sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvol.le), abs_of_nonneg hintnn]
    calc volA⁻¹ * ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
        ≤ volA⁻¹ * (B ^ 2 * volA) :=
          mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h1) (by positivity)
      _ = B ^ 2 := by field_simp
  -- ## the peel identity for the `A`-weighted square
  have hRHS : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.BoseFixB1S.Aind A (x i) * Ψ x) ^ 2)
      = ∫ r in Submission.BoseGases.abox n ℓ,
          ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2 := by
    have hFmeas : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.BoseFixB1S.Aind A (x i) * Ψ x) ^ 2) := by
      have h : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
          Work.BoseFixB1S.Aind A (x i) * Ψ x) :=
        (((measurable_const.indicator hA).comp (measurable_pi_apply i))).mul hΨm
      exact h.pow_const 2
    have hFb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
        |(Work.BoseFixB1S.Aind A (x i) * Ψ x) ^ 2| ≤ B ^ 2 := by
      intro x hx
      rw [Work.BoseFixB1S.Aind, abs_of_nonneg (sq_nonneg _)]
      have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases hmem : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
      calc (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x) ^ 2
          = (A.indicator (fun _ => (1 : ℝ)) (x i)) ^ 2 * (Ψ x) ^ 2 := by ring
        _ ≤ 1 ^ 2 * B ^ 2 := by
              refine mul_le_mul ?_ ?_ (sq_nonneg _) (by positivity)
              · simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hσ 2
              · simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hBb x hx) 2
        _ = B ^ 2 := by ring
    have hFint : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.BoseFixB1S.Aind A (x i) * Ψ x) ^ 2) (Submission.BoseGases.abox (n + 1) ℓ) volume :=
      integrableOn_sq_of_bound hℓ (by
        have h : Measurable (fun x : Submission.BoseGases.X (n + 1) =>
            Work.BoseFixB1S.Aind A (x i) * Ψ x) :=
          (((measurable_const.indicator hA).comp (measurable_pi_apply i))).mul hΨm
        exact h) (fun x hx => by
        rw [Work.BoseFixB1S.Aind]
        have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
          by_cases hmem : x i ∈ A <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
        calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x|
            = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| := abs_mul _ _
          _ ≤ 1 * B := mul_le_mul hσ (hBb x hx) (abs_nonneg _) zero_le_one
          _ = B := one_mul B)
    rw [Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i _ hFint]
    apply integral_congr_ae
    filter_upwards with r
    have hpt : ∀ t : EuclideanSpace ℝ (Fin 3),
        (Work.BoseFixB1S.Aind A (Submission.BoseGases.kcInsN n i (t, r) i)
            * Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2
          = Work.BoseFixB1S.Aind A t * ((Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2) := by
      intro t
      rw [Submission.BoseGases.kc_insN_apply_same]
      by_cases ht : t ∈ A <;>
        simp [Work.BoseFixB1S.Aind, Set.indicator_of_mem, Set.indicator_of_notMem, ht]
    simp only [hpt]
    simpa only [Work.BoseFixB1S.Aind] using Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc
      (fun t => (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2)
  calc (∫ r in Submission.BoseGases.abox n ℓ, (Work.BoseFixB1S.Q0C.oneRest volA A i Ψ r) ^ 2)
      ≤ ∫ r in Submission.BoseGases.abox n ℓ,
          volA⁻¹ * ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2 :=
        integral_mono_ae hLint hRint hCS
    _ = volA⁻¹ * ∫ r in Submission.BoseGases.abox n ℓ,
          ∫ t in A, (Ψ (Submission.BoseGases.kcInsN n i (t, r))) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
    _ = volA⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.BoseFixB1S.Aind A (x i) * Ψ x) ^ 2) := by rw [hRHS]

/-! ## 4. The target -/

theorem boxPQw_mass_le (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {N : ℕ} {ℓ d : ℝ}, 0 < ℓ → 0 < d →
      ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} (u : EuclideanSpace ℝ (Fin 3)),
        0 ≤ v → _root_.BoseGases.IsRadial v → MeasureTheory.MemLp v 1 →
      ∀ {R : ℝ}, 0 < R →
        tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      ∀ (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
            _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v),
        R ≤ ℓ * d / 16 → R ≤ ℓ * Submission.BoseGases.chiR0 →
        0 < Work.SmallBoxSliding.boxMass ℓ d u →
      ∀ {Φ : Submission.BoseGases.X N → ℝ}, Continuous Φ →
        (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.1
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
                * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2)|)
          ≤ C * (_root_.BoseGases.a v) * (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ * (N : ℝ)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ := by
  by_cases hM1 : 1 ≤ M
  · -- the genuine case `M ≥ 1`
    obtain ⟨C0, hC0nn, hfib⟩ := wSmallPairG0FibreLe M
    refine ⟨C0, hC0nn, ?_⟩
    intro N ℓ d hℓ hd v u hv hvrad hv1 R hR hvsupp h hR16 hRchi hvolmass Φ hΦc
    set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
    set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
    have hAmeas : MeasurableSet A := by
      rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
    have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
      rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
    have hvolreal : volA = MeasureTheory.volume.real A := by
      rw [hvolAdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
    have hvolApos : 0 < volA := hvolmass
    have hav0 : 0 ≤ _root_.BoseGases.a v :=
      (Submission.BoseGases.av_bounds_weak hR hv hvrad hvsupp h).1
    have hCfib0 : 0 ≤ C0 * _root_.BoseGases.a v := mul_nonneg hC0nn hav0
    rcases Nat.lt_or_ge N 2 with hN | hN
    · -- `N ≤ 1`
      have hL : (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1
                  (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2
                * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2)|) = 0 := by
        rw [pairSet_eq_empty_of_le_one (by omega : N ≤ 1)]
        simp
      rw [hL]
      have h1 : 0 ≤ volA⁻¹ := inv_nonneg.mpr hvolApos.le
      have h2 : 0 ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg N
      have h3 : 0 ≤ boxQCount volA ℓ A Φ := boxQCount_nonneg volA ℓ A Φ
      have hR0 : 0 ≤ C0 * _root_.BoseGases.a v := hCfib0
      calc (0 : ℝ) ≤ (C0 * _root_.BoseGases.a v) * volA⁻¹ * ((N : ℕ) : ℝ)
              * boxQCount volA ℓ A Φ :=
            mul_nonneg (mul_nonneg (mul_nonneg hR0 h1) h2) h3
        _ = C0 * _root_.BoseGases.a v * volA⁻¹ * ((N : ℕ) : ℝ)
              * boxQCount volA ℓ A Φ := by ring
    · -- the main case `N ≥ 2`
      obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
      -- a bound for `Φ` on the box
      obtain ⟨BΦ, hBΦ⟩ := (Submission.BoseGases.abox_compact (m + 2) hℓ).exists_bound_of_continuousOn
        (s := Submission.BoseGases.abox (m + 2) ℓ) (f := Φ) hΦc.continuousOn
      have hBΦ0 : 0 ≤ BΦ :=
        le_trans (norm_nonneg (Φ 0)) (hBΦ 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
      have hbΦ : ∀ x ∈ Submission.BoseGases.abox (m + 2) ℓ, |Φ x| ≤ BΦ :=
        fun x hx => by simpa [Real.norm_eq_abs] using hBΦ x hx
      -- the per-pair bound
      have hstep : ∀ p ∈ Submission.BoseGases.pairSet (m + 2),
          (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1
                  (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2
                * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2)|)
            ≤ (C0 * _root_.BoseGases.a v) * volA⁻¹
                * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                    (Work.UBBInputs8.boxQInd volA A p.2 Φ x) ^ 2) := by
        intro p hp
        have hne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
        set Ψ : Submission.BoseGases.X (m + 2) → ℝ := Work.UBBInputs8.boxQInd volA A p.2 Φ
          with hΨdef
        have hΨm : Measurable Ψ := measurable_boxQInd volA hAmeas p.2 hΦc.measurable
        have hΨb : ∀ x ∈ Submission.BoseGases.abox (m + 2) ℓ, |Ψ x| ≤ 2 * BΦ :=
          abs_boxQInd_le hℓ hvolApos hAmeas hvolreal hAc p.2 hbΦ
        have hΨsq : IntegrableOn (fun x : Submission.BoseGases.X (m + 2) => (Ψ x) ^ 2)
            (Submission.BoseGases.abox (m + 2) ℓ) volume :=
          integrableOn_sq_of_bound hℓ hΨm hΨb
        -- integrability of the `(P)²·|w|`-integrand
        have hSmeas : AEStronglyMeasurable
            (fun x : Submission.BoseGases.X (m + 2) =>
              (Work.UBBInputs8.boxPInd volA A p.1 Ψ x) ^ 2)
            (volume.restrict (Submission.BoseGases.abox (m + 2) ℓ)) :=
          ((measurable_boxPInd volA A hAmeas p.1 hΨm).pow_const 2).aestronglyMeasurable
        have hvolreal' : volA = (MeasureTheory.volume A).toReal := by
          rw [hvolreal, MeasureTheory.Measure.real_def]
        have hSb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (m + 2) ℓ)),
            |(Work.UBBInputs8.boxPInd volA A p.1 Ψ x) ^ 2| ≤ (2 * BΦ) ^ 2 := by
          rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable (m + 2) ℓ)]
          refine ae_of_all _ (fun x hx => ?_)
          have hb := abs_boxPInd_le hℓ hvolApos hAmeas hvolreal' hAc p.1 hΨb x hx
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (Work.UBBInputs8.boxPInd volA A p.1 Ψ x)]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have hInt1 : IntegrableOn
            (fun x : Submission.BoseGases.X (m + 2) =>
              (Work.UBBInputs8.boxPInd volA A p.1 Ψ x) ^ 2
                * Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2))
            (Submission.BoseGases.abox (m + 2) ℓ) volume :=
          Work.BoseFixB1.integrableOn_slot_wSmallPair (f := Submission.BoseGases.g0 v h)
            hℓ hd (Submission.BoseGases.g0_integrable hR hvsupp h)
            (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hvsupp hz h)
            hM1 hR16 hRchi u hne hSmeas (B := (2 * BΦ) ^ 2) (by positivity) hSb
        have hInt2 : IntegrableOn
            (fun x : Submission.BoseGases.X (m + 2) =>
              (Work.UBBInputs8.boxPInd volA A p.1 Ψ x) ^ 2
                * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2)|)
            (Submission.BoseGases.abox (m + 2) ℓ) volume := by
          have h := hInt1.abs
          refine h.congr ?_
          filter_upwards with x
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        -- the peel
        have hpeel := boxPIndPairMassLe_aux (volA := volA) hℓ hAmeas hAc hne
          (k := fun y a => |Submission.BoseGases.wSmallPair M ℓ d u
            (Submission.BoseGases.g0 v h) y a|)
          (C := C0 * _root_.BoseGases.a v) hCfib0
          (fun a => hfib hR hℓ hd hv hvrad hvsupp h hR16 hRchi A hAmeas hAc u a)
          hΨm (B := 2 * BΦ) (by positivity) hΨb hInt2
        -- the Cauchy–Schwarz mass bound for `oneRest`
        have hcs := oneRest_sq_integral_le_aux (volA := volA) hℓ hvolApos hAmeas hvolreal hAc
          p.1 hΨm (B := 2 * BΦ) (by positivity) hΨb
        -- monotonicity in the `A`-indicator
        have hmono : (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Work.BoseFixB1S.Aind A (x p.1) * Ψ x) ^ 2)
            ≤ ∫ x in Submission.BoseGases.abox (m + 2) ℓ, (Ψ x) ^ 2 := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) hΨsq ?_
          filter_upwards with x
          have hσ : Work.BoseFixB1S.Aind A (x p.1) ^ 2 ≤ 1 := by
            rw [Work.BoseFixB1S.Aind]
            by_cases hmem : x p.1 ∈ A <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hmem]
          calc (Work.BoseFixB1S.Aind A (x p.1) * Ψ x) ^ 2
              = Work.BoseFixB1S.Aind A (x p.1) ^ 2 * (Ψ x) ^ 2 := by ring
            _ ≤ 1 * (Ψ x) ^ 2 := mul_le_mul_of_nonneg_right hσ (sq_nonneg _)
            _ = (Ψ x) ^ 2 := one_mul _
        calc (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 Ψ x) ^ 2
                * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2)|)
            ≤ (C0 * _root_.BoseGases.a v)
                * (∫ r in Submission.BoseGases.abox (m + 1) ℓ,
                    (Work.BoseFixB1S.Q0C.oneRest volA A p.1 Ψ r) ^ 2) := hpeel
          _ ≤ (C0 * _root_.BoseGases.a v) * (volA⁻¹
                * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                    (Work.BoseFixB1S.Aind A (x p.1) * Ψ x) ^ 2)) :=
              mul_le_mul_of_nonneg_left hcs hCfib0
          _ = (C0 * _root_.BoseGases.a v) * volA⁻¹
                * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                    (Work.BoseFixB1S.Aind A (x p.1) * Ψ x) ^ 2) := by ring
          _ ≤ (C0 * _root_.BoseGases.a v) * volA⁻¹
                * (∫ x in Submission.BoseGases.abox (m + 2) ℓ, (Ψ x) ^ 2) :=
              mul_le_mul_of_nonneg_left hmono (mul_nonneg hCfib0 (inv_nonneg.mpr hvolApos.le))
      -- sum over the pairs
      have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount volA ℓ A Φ := boxQCount_nonneg volA ℓ A Φ
      have hsum : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
            ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1
                  (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2
                * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                    (x p.1) (x p.2)|)
          ≤ (C0 * _root_.BoseGases.a v) * volA⁻¹ * ((m + 2 : ℕ) : ℝ)
              * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
        calc (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
              ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                (Work.UBBInputs8.boxPInd volA A p.1
                    (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2
                  * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                      (x p.1) (x p.2)|)
            ≤ ∑ p ∈ Submission.BoseGases.pairSet (m + 2),
                (C0 * _root_.BoseGases.a v) * volA⁻¹
                  * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                      (Work.UBBInputs8.boxQInd volA A p.2 Φ x) ^ 2) :=
              Finset.sum_le_sum hstep
          _ = (C0 * _root_.BoseGases.a v) * volA⁻¹
                * (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
                    ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                      (Work.UBBInputs8.boxQInd volA A p.2 Φ x) ^ 2) := by
              rw [Finset.mul_sum]
          _ = (C0 * _root_.BoseGases.a v) * volA⁻¹ * (((m + 2 : ℕ) : ℝ) - 1)
                * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
              have hsum2 : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
                    ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                      (Work.UBBInputs8.boxQInd volA A p.2 Φ x) ^ 2)
                  = (((m + 2 : ℕ) : ℝ) - 1) * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
                have h := Submission.BoseGases.sum_pairSet_second_eq (m + 2)
                  (fun i : Fin (m + 2) => ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                      (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
                rw [Work.BoseFixB1S.boxQCount]
                simpa using h
              rw [hsum2]
              ring
          _ ≤ (C0 * _root_.BoseGases.a v) * volA⁻¹ * ((m + 2 : ℕ) : ℝ)
                * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
              have hc : 0 ≤ (C0 * _root_.BoseGases.a v) * volA⁻¹ :=
                mul_nonneg hCfib0 (inv_nonneg.mpr hvolApos.le)
              have h1 : (((m + 2 : ℕ) : ℝ) - 1) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
              calc (C0 * _root_.BoseGases.a v) * volA⁻¹ * (((m + 2 : ℕ) : ℝ) - 1)
                    * Work.BoseFixB1S.boxQCount volA ℓ A Φ
                  = ((C0 * _root_.BoseGases.a v) * volA⁻¹)
                      * ((((m + 2 : ℕ) : ℝ) - 1) * Work.BoseFixB1S.boxQCount volA ℓ A Φ) := by
                    ring
                _ ≤ ((C0 * _root_.BoseGases.a v) * volA⁻¹)
                      * (((m + 2 : ℕ) : ℝ) * Work.BoseFixB1S.boxQCount volA ℓ A Φ) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hQnn) hc
                _ = (C0 * _root_.BoseGases.a v) * volA⁻¹ * ((m + 2 : ℕ) : ℝ)
                      * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by ring
      simpa using hsum
  · -- the degenerate case `M = 0`
    have hM0 : M = 0 := by omega
    refine ⟨1, zero_le_one, ?_⟩
    intro N ℓ d hℓ hd v u hv hvrad hv1 R hR hvsupp h hR16 hRchi hvolmass Φ hΦc
    have hL : (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
              * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                  (x p.1) (x p.2)|) = 0 := by
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have hzero : (fun x : Submission.BoseGases.X N =>
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) p.1
                (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) p.2 Φ) x) ^ 2
              * |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
                  (x p.1) (x p.2)|) = fun _ => 0 := by
        funext x
        rw [hM0, Work.BoseFixB1S.wSmallPair_zero_M0, abs_zero, mul_zero]
      rw [hzero, integral_zero]
    rw [hL]
    have hav0 : 0 ≤ _root_.BoseGases.a v :=
      (Submission.BoseGases.av_bounds_weak hR hv hvrad hvsupp h).1
    have hvA0 : 0 ≤ (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ :=
      inv_nonneg.mpr hvolmass.le
    have hN0 : 0 ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg N
    have hQnn : 0 ≤ Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) Φ :=
      boxQCount_nonneg _ _ _ _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_one hav0) hvA0) hN0) hQnn

end Work.BoseFixB1S
