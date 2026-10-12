import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.chiP_sum_peel
import Submission.Work.BoseB1Cube.flatScountB_eq_qcp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.flatScountB_le_Qdecomp`

**The Cauchy–Schwarz (square-completion) decomposition of the cutoff count.**

With `χ = chiSmallB M ℓ d u`, `B(u) = dlBox ℓ d u`, `V = boxMass ℓ d u`,
`Pᵢ = boxPInd V B(u) i`, `Qᵢ = boxQInd V B(u) i` (so `Pᵢ + Qᵢ = 1_{B(u)}(xᵢ)` on the
configuration box), the exact slot decomposition
`Work.BoseB1Cube.flatScountB_eq_qcp` reads

    flatScountB = Σᵢ∫(χ·QᵢΦ)² + 2Σᵢ∫χ²(QᵢΦ)(PᵢΦ) + Σᵢ∫(χ·PᵢΦ)² .

The point of this file is to `complete the square` of the cross term.  Writing

    a := Σᵢ∫(χQᵢ)² ,   b := Σᵢ∫(χPᵢ)² ,   c := Σᵢ∫χ²QᵢPᵢ ,

Cauchy–Schwarz slot by slot gives `cᵢ² ≤ qᵢpᵢ` (`qᵢ = ∫(χQᵢ)²`, `pᵢ = ∫(χPᵢ)²`), hence
`Σᵢ|cᵢ| ≤ Σᵢ√(qᵢpᵢ) ≤ √a·√b` (Cauchy–Schwarz over the slot index,
`Real.sum_sqrt_mul_sqrt_le`), and therefore `a + 2c + b ≤ (√a + √b)²`.  With the two input
bounds

* (i) `a ≤ Ξ·boxQCount` whenever `χ² ≤ Ξ` pointwise (the hypothesis of the statement; the
  per-slot pointwise domination `(χ·Qᵢ)² = χ²·Qᵢ² ≤ Ξ·Qᵢ²` plus monotonicity of the
  integral), and
* (ii) `b = (chiMass/boxMass)·boxFlatCount` (the exact peel `Work.BoseB1Cube.chiP_sum_peel`),

the square completion gives exactly

    flatScountB ≤ (χ/|B|)·boxFlatCount
        + 2·√(Ξ·χ/|B|)·√(boxFlatCount·boxQCount) + Ξ·boxQCount .

The last step is the rewriting `√(ΞQ·AS) = √(ΞA)·√(SQ)` (`Real.sqrt_mul`, the two products
being nonnegative) together with the definitional unfolding of `boxFlatCount`/`boxQCount`.

The slot Cauchy–Schwarz of this file is also available as the standalone library lemma
`Work.BoseB1Cube.crossSum_le_sqrt` (`Submission/Work/BoseB1Cube/crossSum_le_sqrt.lean`), and the
specialisation of (i) to a slot-independent function as `Work.BoseB1Cube.sum_chiSqMul_le`; the
proof below is self-contained so that this file has no dependency on those.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseB1Cube

open Submission.BoseGases
open Work.UBBInputs8 (boxPInd boxQInd)
open Work.SmallBoxSliding (boxMass chiMass)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- Measurability of the box excitation `Q_{B,i}Φ = 1_{B(u)}(xᵢ)Φ − P_{B,i}Φ` (definitional
unfolding plus the measurability of the indicator, of `Φ` and of the box projection). -/
private lemma measurable_boxQInd' {V : ℝ} {A : Set E3} (hA : MeasurableSet A) {N : ℕ}
    (i : Fin N) {Φ : X N → ℝ} (hΦ : Measurable Φ) :
    Measurable (boxQInd V A i Φ) := by
  have h : boxQInd V A i Φ = fun x : X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - boxPInd V A i Φ x := rfl
  rw [h]
  exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦ).sub
    (Work.BoseFixB1S.measurable_boxPInd V A hA i hΦ)

/-- Pointwise bound of the box excitation: `|Q_{B,i}Φ| ≤ 2C` on the configuration box whenever
`|Φ| ≤ C` there (and `|P_{B,i}Φ| ≤ C`, which is `abs_boxPInd_le`). -/
private lemma abs_boxQInd_le' {ℓ V C : ℝ} {A : Set E3} {N : ℕ} (i : Fin N)
    {Φ : X N → ℝ}
    (hC : ∀ x ∈ abox N ℓ, |Φ x| ≤ C)
    (hP : ∀ x ∈ abox N ℓ, |boxPInd V A i Φ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |boxQInd V A i Φ x| ≤ 2 * C := by
  intro x hx
  have h : boxQInd V A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - boxPInd V A i Φ x := rfl
  rw [h]
  have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    have h2 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hmem : x i ∈ A
      · rw [Set.indicator_of_mem hmem]; norm_num
      · rw [Set.indicator_of_notMem hmem]; norm_num
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul h2 (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x + -boxPInd V A i Φ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |-boxPInd V A i Φ x| := abs_add_le _ _
    _ = |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |boxPInd V A i Φ x| := by rw [abs_neg]
    _ ≤ C + C := add_le_add h1 (hP x hx)
    _ = 2 * C := by ring

/-- **Slot Cauchy–Schwarz, summed over the slots.**  For the sliding cutoff `χ = chiSmallB M ℓ d u`
and the two box projections `Pᵢ`, `Qᵢ = boxQInd`, the `χ²`-weighted cross slot sum is dominated by
the geometric mean of the two `χ`-weighted counts:

    Σᵢ∫χ²(QᵢΦ)(PᵢΦ) ≤ √(Σᵢ∫(χQᵢΦ)²) · √(Σᵢ∫(χPᵢΦ)²) . -/
private lemma crossSum_le_sqrt_core {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (hV : 0 < boxMass ℓ d u)
    {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin n, ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
        * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
        * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
      ≤ Real.sqrt (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        * Real.sqrt (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
  classical
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : boxMass ℓ d u = (volume : Measure E3).real (dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  obtain ⟨B, hB⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn
    (s := abox n ℓ) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
  have hΦb : ∀ x ∈ abox n ℓ, |Φ x| ≤ B := fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx
  have hCχ : ∀ z : E3, |chiSmallB M ℓ d u z| ≤ chiSupAbs * chiSmallDecay M :=
    fun z => Work.BoseFixB1S.abs_chiSmallB_le_supB hM u z
  have hCχ0 : 0 ≤ chiSupAbs * chiSmallDecay M := le_trans (abs_nonneg _) (hCχ 0)
  have hPm : ∀ i : Fin n, Measurable (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ) :=
    fun i => Work.BoseFixB1S.measurable_boxPInd _ _ hA i hΦc.measurable
  have hPb : ∀ i : Fin n, ∀ x ∈ abox n ℓ, |boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x| ≤ B :=
    fun i x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hΦb x hx
  have hQm : ∀ i : Fin n, Measurable (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ) :=
    fun i => measurable_boxQInd' hA i hΦc.measurable
  have hQb : ∀ i : Fin n, ∀ x ∈ abox n ℓ,
      |boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x| ≤ 2 * B :=
    fun i x hx => abs_boxQInd_le' i hΦb (hPb i) x hx
  -- ## the slot Cauchy–Schwarz, in squared form
  have key : ∀ i : Fin n,
      (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
          * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
          * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2
      ≤ (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
            * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        * (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
            * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
    intro i
    haveI : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ.le⟩
    have hfae : AEStronglyMeasurable (fun x : X n => chiSmallB M ℓ d u (x i)
        * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      (((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).comp
        (continuous_apply i)).measurable.mul (hQm i)).aestronglyMeasurable
    have hgae : AEStronglyMeasurable (fun x : X n => chiSmallB M ℓ d u (x i)
        * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      (((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).comp
        (continuous_apply i)).measurable.mul (hPm i)).aestronglyMeasurable
    have h := Work.BoseFixB1S.Q0C.integral_mul_sq_le
      (μ := (volume : Measure (X n)).restrict (abox n ℓ)) (f := fun x : X n =>
        chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
      (g := fun x : X n =>
        chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
      hfae hgae
      (by
        rw [ae_restrict_iff' (abox_measurable n ℓ)]
        exact Filter.Eventually.of_forall (fun x hx => by
          rw [abs_mul]
          exact mul_le_mul (hCχ (x i)) (hQb i x hx) (abs_nonneg _) hCχ0))
      (by
        rw [ae_restrict_iff' (abox_measurable n ℓ)]
        exact Filter.Eventually.of_forall (fun x hx => by
          rw [abs_mul]
          exact mul_le_mul (hCχ (x i)) (hPb i x hx) (abs_nonneg _) hCχ0))
    have e1 : (∫ x, (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
          * (chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
          ∂((volume : Measure (X n)).restrict (abox n ℓ)))
        = ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
            * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
            * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [e1] at h
    exact h
  -- ## nonnegativity of the two slot sums
  have hnnq : ∀ i : Fin n, 0 ≤ ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
      * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 :=
    fun i => integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have hnnp : ∀ i : Fin n, 0 ≤ ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
      * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 :=
    fun i => integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  -- ## per-slot conclusion in the square-root form
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
          * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
          * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
        ≤ Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
    intro i _
    have h2 := key i
    have hs : Real.sqrt ((∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        * (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2))
        = Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) :=
      Real.sqrt_mul (hnnq i) _
    have h3 : |∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
          * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
          * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x|
        ≤ Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
      rw [← hs]
      calc |∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
            * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
            * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x|
          = Real.sqrt ((∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
                * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
              * (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
                * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)) := Real.sqrt_le_sqrt h2
    exact le_trans (le_abs_self _) h3
  -- ## Cauchy–Schwarz over the slot index
  calc (∑ i : Fin n, ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
          * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
          * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)),
          Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * Real.sqrt (∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) :=
        Finset.sum_le_sum hterm
    _ ≤ Real.sqrt (∑ i : Fin n, ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * Real.sqrt (∑ i : Fin n, ∫ x in abox n ℓ, (chiSmallB M ℓ d u (x i)
              * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) :=
        Real.sum_sqrt_mul_sqrt_le _ hnnq hnnp

/-- **The Cauchy–Schwarz square completion of the cutoff count.**  Under `χ² ≤ Ξ` pointwise,

    flatScountB ≤ (chiMass/boxMass)·boxFlatCount
        + 2√(Ξ·chiMass/boxMass)·√(boxFlatCount·boxQCount) + Ξ·boxQCount . -/
theorem flatScountB_le_Qdecomp {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {Ξ : ℝ} (hΞ0 : 0 ≤ Ξ)
    (hΞ : ∀ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 ≤ Ξ) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ
      ≤ (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
          * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
        + 2 * Real.sqrt (Ξ * Work.SmallBoxSliding.chiMass M ℓ d u
              / Work.SmallBoxSliding.boxMass ℓ d u)
            * Real.sqrt (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ)
        + Ξ * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ := by
  classical
  -- ## the box geometry
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : boxMass ℓ d u = (volume : Measure E3).real (dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  -- ## the state is bounded on the configuration box
  obtain ⟨B, hB⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn
    (s := abox n ℓ) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
  have hΦb : ∀ x ∈ abox n ℓ, |Φ x| ≤ B := fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx
  -- ## per-slot measurability and bounds for the two projections
  have hPm : ∀ i : Fin n, Measurable (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ) :=
    fun i => Work.BoseFixB1S.measurable_boxPInd _ _ hA i hΦc.measurable
  have hPb : ∀ i : Fin n, ∀ x ∈ abox n ℓ, |boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x| ≤ B :=
    fun i x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hΦb x hx
  have hQm : ∀ i : Fin n, Measurable (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ) :=
    fun i => measurable_boxQInd' hA i hΦc.measurable
  have hQb : ∀ i : Fin n, ∀ x ∈ abox n ℓ,
      |boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x| ≤ 2 * B :=
    fun i x hx => abs_boxQInd_le' i hΦb (hPb i) x hx
  -- ## (1) the `Ξ`-majorant of the excited slot sum
  have hQle : (∑ i : Fin n, ∫ x in abox n ℓ,
        (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
      ≤ Ξ * ∑ i : Fin n, ∫ x in abox n ℓ,
          (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hpt : ∀ x : X n,
        (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2
          ≤ Ξ * (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 := by
      intro x
      have h1 : (chiSmallB M ℓ d u (x i)) ^ 2 ≤ Ξ := hΞ (x i)
      nlinarith [sq_nonneg (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)]
    have hQi : Integrable (fun x : X n =>
        (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        (volume.restrict (abox n ℓ)) :=
      Work.BoseFixB1S.integrableOn_sq_of_bound hℓ (hQm i) (hQb i)
    have hmχ : AEStronglyMeasurable
        (fun x : X n => (chiSmallB M ℓ d u (x i)) ^ 2) (volume.restrict (abox n ℓ)) :=
      (((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).comp
        (continuous_apply i)).pow 2).aestronglyMeasurable
    have hfi : Integrable (fun x : X n =>
        (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        (volume.restrict (abox n ℓ)) := by
      refine Integrable.mono' (hQi.const_mul Ξ) ?_ ?_
      · have heq : (fun x : X n =>
            (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
            = fun x => (chiSmallB M ℓ d u (x i)) ^ 2
                * (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 := by
          funext x; ring
        rw [heq]
        exact hmχ.mul hQi.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpt x
    calc ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2
        ≤ ∫ x in abox n ℓ, Ξ * (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 :=
          integral_mono_ae hfi (hQi.const_mul Ξ) (Filter.Eventually.of_forall hpt)
      _ = Ξ * ∫ x in abox n ℓ, (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 :=
          integral_const_mul Ξ _
  -- ## (2) the exact peel of the condensate slot sum
  have hPsum : (∑ i : Fin n, ∫ x in abox n ℓ,
        (chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
      = (chiMass M ℓ d u / boxMass ℓ d u)
        * ∑ i : Fin n, ∫ x in abox n ℓ,
            (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 :=
    chiP_sum_peel hM hℓ hd u hV hΦc
  -- ## (3) Cauchy–Schwarz for the cross slot sum
  have hcross : (∑ i : Fin n, ∫ x in abox n ℓ,
        (chiSmallB M ℓ d u (x i)) ^ 2 * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
          * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
      ≤ Real.sqrt (Ξ * ∑ i : Fin n, ∫ x in abox n ℓ,
            (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        * Real.sqrt ((chiMass M ℓ d u / boxMass ℓ d u)
            * ∑ i : Fin n, ∫ x in abox n ℓ,
                (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
    have h0 := crossSum_le_sqrt_core (M := M) hM hℓ hd u hV hΦc
    have hs2 : Real.sqrt (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        = Real.sqrt ((chiMass M ℓ d u / boxMass ℓ d u)
            * ∑ i : Fin n, ∫ x in abox n ℓ,
                (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by rw [hPsum]
    refine le_trans h0 ?_
    rw [hs2]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hQle) (Real.sqrt_nonneg _)
  -- ## (4) the two counts unfold definitionally
  have hSdef : Work.BoseFixB1S.boxFlatCount (boxMass ℓ d u) ℓ (dlBox ℓ d u) Φ
      = ∑ i : Fin n, ∫ x in abox n ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 := rfl
  have hQdef : Work.BoseFixB1S.boxQCount (boxMass ℓ d u) ℓ (dlBox ℓ d u) Φ
      = ∑ i : Fin n, ∫ x in abox n ℓ, (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 := rfl
  -- ## (5) nonnegativity of the two counts and of the cutoff mass
  have hQnn : 0 ≤ ∑ i : Fin n, ∫ x in abox n ℓ,
      (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _)))
  have hχnn : 0 ≤ chiMass M ℓ d u := by
    rw [← setIntegral_chiSmallB_sq hM hℓ hd u]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _))
  have hΞAnn : 0 ≤ Ξ * (chiMass M ℓ d u / boxMass ℓ d u) :=
    mul_nonneg hΞ0 (div_nonneg hχnn hV.le)
  -- ## (6) `√(ΞQ)·√(AS) = √(ΞA)·√(SQ)`
  have hcrosssqrt : Real.sqrt (Ξ * ∑ i : Fin n, ∫ x in abox n ℓ,
          (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        * Real.sqrt ((chiMass M ℓ d u / boxMass ℓ d u)
          * ∑ i : Fin n, ∫ x in abox n ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
      = Real.sqrt (Ξ * (chiMass M ℓ d u / boxMass ℓ d u))
        * Real.sqrt ((∑ i : Fin n, ∫ x in abox n ℓ,
              (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * (∑ i : Fin n, ∫ x in abox n ℓ,
              (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)) := by
    rw [← Real.sqrt_mul (mul_nonneg hΞ0 hQnn) ((chiMass M ℓ d u / boxMass ℓ d u)
          * ∑ i : Fin n, ∫ x in abox n ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2),
        ← Real.sqrt_mul hΞAnn ((∑ i : Fin n, ∫ x in abox n ℓ,
              (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
          * (∑ i : Fin n, ∫ x in abox n ℓ,
              (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2))]
    congr 1
    ring
  have hsqrtArg : Ξ * (chiMass M ℓ d u / boxMass ℓ d u)
      = Ξ * chiMass M ℓ d u / boxMass ℓ d u := by ring
  -- ## (7) the square completion `a + 2c + b ≤ ΞQ + 2√(ΞQ·AS) + AS`
  have hstep : (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        + 2 * (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i)) ^ 2 * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
            * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
        + (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
      ≤ Ξ * (∑ i : Fin n, ∫ x in abox n ℓ,
            (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        + 2 * (Real.sqrt (Ξ * ∑ i : Fin n, ∫ x in abox n ℓ,
              (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
            * Real.sqrt ((chiMass M ℓ d u / boxMass ℓ d u)
              * ∑ i : Fin n, ∫ x in abox n ℓ,
                  (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2))
        + (chiMass M ℓ d u / boxMass ℓ d u)
          * (∑ i : Fin n, ∫ x in abox n ℓ,
              (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
    have h2 : 2 * (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i)) ^ 2 * boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x
            * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x)
        ≤ 2 * (Real.sqrt (Ξ * ∑ i : Fin n, ∫ x in abox n ℓ,
              (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
            * Real.sqrt ((chiMass M ℓ d u / boxMass ℓ d u)
              * ∑ i : Fin n, ∫ x in abox n ℓ,
                  (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)) := by
      linarith [hcross]
    have h3 : (∑ i : Fin n, ∫ x in abox n ℓ,
          (chiSmallB M ℓ d u (x i) * boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        ≤ (chiMass M ℓ d u / boxMass ℓ d u)
          * (∑ i : Fin n, ∫ x in abox n ℓ,
              (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := le_of_eq hPsum
    exact add_le_add (add_le_add hQle h2) h3
  -- ## (8) rewrite the whole right-hand side and finish
  have hmain : Ξ * (∑ i : Fin n, ∫ x in abox n ℓ,
          (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        + 2 * (Real.sqrt (Ξ * ∑ i : Fin n, ∫ x in abox n ℓ,
              (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
            * Real.sqrt ((chiMass M ℓ d u / boxMass ℓ d u)
              * ∑ i : Fin n, ∫ x in abox n ℓ,
                  (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2))
        + (chiMass M ℓ d u / boxMass ℓ d u)
          * (∑ i : Fin n, ∫ x in abox n ℓ,
              (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
      = (chiMass M ℓ d u / boxMass ℓ d u)
          * (∑ i : Fin n, ∫ x in abox n ℓ,
              (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
        + 2 * Real.sqrt (Ξ * chiMass M ℓ d u / boxMass ℓ d u)
            * Real.sqrt ((∑ i : Fin n, ∫ x in abox n ℓ,
                (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2)
              * (∑ i : Fin n, ∫ x in abox n ℓ,
                  (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2))
        + Ξ * (∑ i : Fin n, ∫ x in abox n ℓ,
            (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x) ^ 2) := by
    rw [hcrosssqrt, ← hsqrtArg]
    ring
  rw [flatScountB_eq_qcp hM hℓ hd u hV hΦc, hSdef, hQdef]
  exact le_trans hstep (le_of_eq hmain)

end Work.BoseB1Cube
