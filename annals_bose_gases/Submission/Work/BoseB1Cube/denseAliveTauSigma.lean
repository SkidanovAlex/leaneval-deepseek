import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.abs_boxQCross_le
import Submission.Work.BoseB1Cube.abs_sigRho_le
import Submission.Work.BoseB1Cube.chiP_sum_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.denseAliveTauSigma`

**The sharp `τ`-decomposition at the single cube cutoff.**

Session 3 of the node `Work.BoseB1Cube.cubeBandArmDenseAliveRow` paid the `τ`-column of the
ledger `(R)` through the lossy bound `τ = flatScountB/(chiMass·N) ≤ Ξ·𝔐/(κ·N)`.  That bound is
*not* payable in the regime where the state is flat inside the box: there the true value is
`τ ≈ 𝔐/(V·N)`, smaller by the fixed factor `λ = ΞV/κ`, and the ledger's payers
(`½μ²W₁N` plus the Jensen part `W₁(S²/N − S)/(2V²)` of the pair row) are **tight** at the
marginal density, so no fixed constant absorbs the loss whenever `λ > 1`.

The repair is the **exact split**

    χ(x)² = χ̄·1_A(x) + ρ(x),     χ̄ := chiMass/boxMass,   ρ := χ² − χ̄·1_A,   ∫_A ρ = 0,

which gives the identity (this file)

    flatScountB M ℓ d u Φ = χ̄·𝔐 + σρ ,
      𝔐  := ∫Φ²·Σᵢ1_A(xᵢ)     (`Work.BoseB1Cube.NAmass`),
      σρ := ∫Φ²·Σᵢρ(xᵢ)       (`Work.BoseB1Cube.sigRho`).

The deviation `σρ` is `Q`-controlled, with the **same** shape as the proved
`Work.BoseB1Cube.abs_boxQCross_le` for the `QQ`/`QP` box cross line:

    |σρ| ≤ Ξ·(2√(S·Q) + Q),       S := boxFlatCount,  Q := boxQCount,

for any pointwise bound `Ξ` of `|ρ|`.  (Filed as the delegation
`Work.BoseB1Cube.abs_sigRho_le`; the mechanism is that the condensate part
`(PᵢΦ)²ρ(xᵢ)` dies by the one-slot kernel identity `Work.BoseFixB1S.Q0C.one_kernel` with
`g = ρ`, because its slice integral is `∫_Aρ = 0`.)

**Consequence for the ledger.**  With the split, the `τ`-charge of `(R)` is

    μ·W₁·τ·N ≤ μ·W₁·𝔐/V + μ·W₁·Ξ·(2√(SQ) + Q)/chiMass ,

whose first term is the mean-field density `𝔐/V` — paid by the perfect square
`W₁(S²/N − S)/(2V²) + ½μ²W₁N`, whose deficit is `O(μ²/(V·N))`-sized and absorbed by the credit
`C(μ²aΓκ + μa)N` — and whose second term is `O(Q + √(SQ))`-sized and paid by the gap
`tbGapCoeff·Q`, because `tbGapCoeff/(μa) → ∞` while `(W₁/κ)·Ξ = 8πa·Ξ` is `μa`-proportional.
Without the split the whole `Ξ·𝔐/chiMass` column would have to be paid by the gap, which is
impossible whenever `S ≫ Q` (the box-flat states), since `Q ≤ 𝔐` is an upper bound in the wrong
direction.
-/

/-!
## 2bis. Recipe for the instantiation `Work.BoseB1Cube.abs_sigRho_le_chiRho`

(The statement itself is delegated; this note records the Lean route and the two Mathlib
gotchas found while attempting it.)

* apply `Work.BoseB1Cube.abs_sigRho_le` with `A := Submission.BoseGases.dlBox ℓ d u`,
  `V := Work.SmallBoxSliding.boxMass ℓ d u`, `ρ := chiRho M ℓ d u`;
* `hA := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u`;
* `hAc := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u`;
* `hVeq := by rw [Work.SmallBoxSliding.boxMass_eq_measureReal,
  MeasureTheory.Measure.real_def]`;
* `hρm` (measurability): `Measurable.sub` of
  `((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).measurable` and
  `measurable_const.mul (measurable_const.indicator hA)`;
  **gotcha 1**: `rw [chiRho]` *fails* under an integral/`∀` binder — use
  `funext z; rw [chiRho]`, or `simp only [chiRho]`;
* `hsupp : ∀ z, z ∉ A → chiRho M ℓ d u z = 0`: from
  `Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd : chiSmallB … z ≠ 0 → z ∈ dlBox ℓ d u`
  (contrapositive), then `Set.indicator_of_notMem`;
* `hρA : ∫ z in A, chiRho M ℓ d u z = 0`: rewrite the integrand first (this avoids all
  integrability trouble with the indicator) —
  `MeasureTheory.setIntegral_congr_fun hA (fun z hz => by simp only [chiRho,
  Set.indicator_of_mem hz]; ring)` turns the goal into `∫ z in A, ((chiSmallB … z)^2 − χ̄) = 0`;
  then `MeasureTheory.integral_sub` with the witnesses
  `((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).continuousOn.integrableOn_compact
     (Submission.BoseGases.acube_compact hℓ) |>.mono_set (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)`
  and `MeasureTheory.integrableOn_const hfin` (its first autoParam is `μ s ≠ ⊤`),
  then `Work.BoseB1Cube.setIntegral_chiSmallB_sq hM hℓ hd u`,
  `MeasureTheory.integral_const`, `MeasureTheory.Measure.restrict_apply_univ`,
  `Work.SmallBoxSliding.boxMass_eq_measureReal`, `smul_eq_mul`, `mul_one`, `field_simp`;
* `hfin : (volume : Measure E3) A ≠ ⊤` is
  `ne_of_lt (lt_of_le_of_lt (measure_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u))
     (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top))`;
* **gotcha 2**: `MeasureTheory.setIntegral_indicator` + `MeasureTheory.integral_indicator_one`
  are the right pair for `∫ z in A, A.indicator 1 z = boxMass` (do *not* use
  `MeasureTheory.integral_const`, which produces `μ.real univ • c` and needs
  `MeasureTheory.Measure.restrict_apply_univ`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. The two objects of the split -/

/-- The box-count mass `𝔐 = ∫Φ²·Σᵢ1_A(xᵢ)`. -/
noncomputable def NAmass {n : ℕ} (ℓ d : ℝ) (u : E3) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
    (∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))

/-- The one-variable deviation `ρ = χ² − χ̄·1_A` of the smooth count from the box density. -/
noncomputable def chiRho (M : ℕ) (ℓ d : ℝ) (u z : E3) : ℝ :=
  (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
    - (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
      * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z

/-- The `ρ`-deviation of the smooth count: `σρ = ∫Φ²·Σᵢρ(xᵢ)`. -/
noncomputable def sigRho (M : ℕ) (ℓ d : ℝ) (u : E3) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, chiRho M ℓ d u (x i))

/-! ## 0b. An elementary absolute-value bound -/

/-- `|a − b·ind| ≤ c + b` for `0 ≤ a ≤ c`, `b ≥ 0`, `ind ∈ [0,1]`. -/
private lemma abs_sub_mul_ind_le {a b ind c : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ c) (hb : 0 ≤ b)
    (h0 : 0 ≤ ind) (h1 : ind ≤ 1) : |a - b * ind| ≤ c + b := by
  have hb3 : 0 ≤ b * ind := mul_nonneg hb h0
  have hbi : b * ind ≤ b := by nlinarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-! ## 1. The exact split -/

/-- **The exact `τ`-split at the single cube cutoff.**  With `χ = chiSmallB M ℓ d u`,
`A = dlBox ℓ d u`, `V = boxMass ℓ d u`, `κ = chiMass M ℓ d u` and
`N_A(x) = Σᵢ1_A(xᵢ)`,

    flatScountB M ℓ d u Φ = (κ/V)·𝔐 + σρ .

The identity is the pointwise decomposition `χ² = χ̄·1_A + ρ` integrated against `Φ²`. -/
theorem flatScountB_eq_split {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ
      = (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
          * NAmass ℓ d u Φ
        + sigRho M ℓ d u Φ := by
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  obtain ⟨C, hC0, hΦb, _hPb, _hQb⟩ := Work.BoseFixB1S.boxBounds (ℓ := ℓ) (volA := V)
    hℓ (by rw [hVdef]; exact hV) (A := A)
    (by rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
    (by rw [hVdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal,
        MeasureTheory.Measure.real_def])
    (by rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hΦc
  have hAm : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  -- the count function and its bound
  have hind_meas : Measurable (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    Finset.measurable_sum _ (fun i _ =>
      (measurable_const.indicator hAm).comp (measurable_pi_apply i))
  have hind_bd : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (n : ℝ) := by
    intro x hx
    calc |∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)|
        ≤ ∑ i : Fin n, |A.indicator (fun _ => (1 : ℝ)) (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          by_cases hxi : x i ∈ A
          · rw [Set.indicator_of_mem hxi]; simp
          · rw [Set.indicator_of_notMem hxi]; simp
      _ = (n : ℝ) := by simp
  have hrho_meas : Measurable (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, chiRho M ℓ d u (x i)) := by
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.sub ?_ ?_
    · exact (((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).measurable).comp
        (measurable_pi_apply i)
    · exact (measurable_const.mul (measurable_const.indicator hAm)).comp
        (measurable_pi_apply i)
  -- the pointwise bound for `ρ`
  have hchi2le : ∀ z : E3, (χ z) ^ 2
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
    intro z
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (by rw [hχdef]; exact Work.BoseFixB1S.abs_chiSmallB_le_supB hM u z) 2
  have hind1 : ∀ z : E3, A.indicator (fun _ => (1 : ℝ)) z ≤ 1 := by
    intro z
    by_cases hz : z ∈ A
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  have hind0 : ∀ z : E3, 0 ≤ A.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ A
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  have hrho_bd : ∀ z : E3, |chiRho M ℓ d u z|
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 + |κ / V| := by
    intro z
    have hkey := abs_sub_mul_ind_le (a := (χ z) ^ 2) (b := κ / V)
      (ind := A.indicator (fun _ => (1 : ℝ)) z)
      (c := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2)
      (sq_nonneg _) (hchi2le z) (div_nonneg (Work.SmallBoxSliding.chiMass_nonneg M ℓ d u) hV.le)
      (hind0 z) (hind1 z)
    rw [chiRho]
    exact le_trans hkey (by linarith [le_abs_self (κ / V)])
  -- integrability of the two pieces
  have hNb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |(Φ x) ^ 2| ≤ C ^ 2 := by
    intro x hx
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (Φ x)]
    exact pow_le_pow_left₀ (abs_nonneg (Φ x)) (hΦb x hx) 2
  have hNA_int : IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)))
      (Submission.BoseGases.abox n ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ ((hΦc.pow 2).measurable) hind_meas
      hNb hind_bd
  have hSρbd : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |∑ i : Fin n, chiRho M ℓ d u (x i)|
        ≤ (n : ℝ) * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            + |κ / V|) := by
    intro x hx
    calc |∑ i : Fin n, chiRho M ℓ d u (x i)|
        ≤ ∑ i : Fin n, |chiRho M ℓ d u (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            + |κ / V|) := Finset.sum_le_sum (fun i _ => hrho_bd (x i))
      _ = (n : ℝ) * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            + |κ / V|) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hρ_int : IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ i : Fin n, chiRho M ℓ d u (x i)))
      (Submission.BoseGases.abox n ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ ((hΦc.pow 2).measurable) hrho_meas
      hNb hSρbd
  -- the pointwise identity
  have hsum : ∀ x : Submission.BoseGases.X n,
      (κ / V) * (∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i))
        + (∑ i : Fin n, chiRho M ℓ d u (x i))
      = ∑ i : Fin n, (χ (x i)) ^ 2 := by
    intro x
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [chiRho, hχdef]; ring
  have hpt : (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * (∑ i : Fin n, (χ (x i)) ^ 2))
      = fun x : Submission.BoseGases.X n =>
          (κ / V) * ((Φ x) ^ 2 * (∑ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)))
          + (Φ x) ^ 2 * (∑ i : Fin n, chiRho M ℓ d u (x i)) := by
    funext x
    rw [← hsum x]; ring
  have hflat : Work.BoseFixB1.flatScountB M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, (χ (x i)) ^ 2) := by
    simp only [Work.BoseFixB1.flatScountB, Work.BoseFixB1.nCountB, hχdef]
  rw [hflat, hpt, MeasureTheory.integral_add (hNA_int.const_mul (κ / V)) hρ_int,
    MeasureTheory.integral_const_mul, NAmass, sigRho, hAdef]

end Work.BoseB1Cube
