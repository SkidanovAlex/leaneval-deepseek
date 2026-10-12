import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.denseAliveTauSigma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.rhoRho_pair_null` — the `χχ`-pair annihilates the box projections

The density-deviation `chiRho M ℓ d u = χ_{B(u)}² − (chiMass/boxMass)·1_{B(u)}` of the
per-box chapter is **mean zero on the sliding box** `B(u) = dlBox ℓ d u`
(`∫_{B(u)} chiRho = 0`, from `∫_{B(u)} χ² = chiMass`), and `chiRho` is supported in `B(u)`
(`chiSmallB_support_subset_dlBox`).  Hence for two distinct slots `i ≠ j` the product
`chiRho(xᵢ)·chiRho(xⱼ)` is **orthogonal to the range of the one-slot and two-slot box
projections** `Pᵢ = boxPInd V B(u) i`:

    ∫_{abox n ℓ} χ(xᵢ)χ(xⱼ)·(PᵢF) = 0 ,  ∫ χ(xᵢ)χ(xⱼ)·(PⱼF) = 0 ,  ∫ χ(xᵢ)χ(xⱼ)·(PᵢPⱼF) = 0 .

The mechanism is the *slot peel* `Work.BoseB1Cube.slotWeightedPeel`:  for a function `H` whose
value on `kcInsN m i (y, r)` does not depend on the slot value `y`,

    ∫_{abox (m+1) ℓ} w(xᵢ)·H = (∫_{acube ℓ} w)·(∫_{abox m ℓ} H(kcInsN m i (0, r))) ,

and `∫_{B(u)} chiRho·1_{B(u)} = ∫_{B(u)} chiRho = 0` kills it.  The projections have exactly
that structure:  `PᵢF x = 1_B(xᵢ)·(1/|B|)∫_{z∈B} F(x|i↦z)dz` with the *slot mean* independent of
the slot-`i` value, so after multiplying by `chiRho(xᵢ)` (which is supported in `B`) the whole
integrand factors as `w(xᵢ)·H` with `w = chiRho·1_B` and `H` peel-invariant.

Consequently the ±`P` "fluctuation" `F − PᵢF − PⱼF + PᵢPⱼF` may be replaced by `F` inside
`∫ χ(xᵢ)χ(xⱼ)·(·)`, which is the requested statement `rhoRho_pair_null`.

## Layout

* `rhoRho_pM_one` — the box particle-number parameter is `≥ 1`;
* `acube_subset_singleton_of_nonpos`, `pD_pos_of_boxMass_pos` — `0 < boxMass` forces `0 < d`
  (for `d ≤ 0` the sliding box degenerates to at most a point);
* `rhoRho_measurable_chiRho`, `rhoRho_abs_chiRho_le` — measurability and the sup-bound `Ξ` of the deviation
  (needed for the integrability of the four pieces of the final linearity step);
* `int_chiRho_mul_indicator_acube_zero` — `∫_{B(u)} chiRho = 0`;
* `int_chiRho_ind_mul_invariant_zero` — the peel + mean-zero annihilation;
* `int_chiRho_chiRho_boxPInd_zero` — the annihilation of a single projection
  `∫ χ(xᵢ)χ(xⱼ)·PᵢF = 0` (instantiated three times, with the slots swapped for `Pⱼ`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseB1Cube

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The box parameter `M` and the positivity of the ratio `d` -/

/-- The small-box particle-number parameter is `mValue = 48 ≥ 1`. -/
theorem rhoRho_pM_one {v : E3 → ℝ} {μ : ℝ} : 1 ≤ Work.BoseFixB1.pM v μ := by
  simp only [Work.BoseFixB1.pM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  norm_num

/-- For `c ≤ 0` the centred cube `acube c` is at most the origin:  every coordinate of a point of
`acube c` lies in `Icc (-c/2) (c/2)` with `-c/2 ≥ 0 ≥ c/2`. -/
theorem acube_subset_singleton_of_nonpos {c : ℝ} (hc : c ≤ 0) :
    Submission.BoseGases.acube c ⊆ ({0} : Set E3) := by
  intro y hy
  rw [Set.mem_singleton_iff]
  ext m
  have hm := (Submission.BoseGases.mem_acube_iff c y).mp hy m
  rw [Set.mem_Icc] at hm
  show y m = (0 : E3) m
  rw [PiLp.zero_apply]
  exact le_antisymm (by linarith [hm.2, hc]) (by linarith [hm.1, hc])

/-- **`0 < boxMass` forces `0 < d`**:  for `d ≤ 0` the sliding box `dlBox ℓ d u` is contained in
the single point `(ℓd)•u` (the small cube `acube (ℓd)` is empty for `ℓd < 0` and `{0}` for
`ℓd = 0`), hence has measure zero. -/
theorem pD_pos_of_boxMass_pos {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : E3}
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) : 0 < d := by
  by_contra h
  have hle : d ≤ 0 := le_of_not_gt h
  have hc : ℓ * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hℓ.le hle
  have hsub : Submission.BoseGases.dlBox ℓ d u ⊆ ({((ℓ * d) • u : E3)} : Set E3) := by
    intro x hx
    rw [Set.mem_singleton_iff]
    have hx' := (Submission.BoseGases.mem_dlBox_iff ℓ d u x).mp hx
    have h1 : x - (ℓ * d) • u ∈ ({0} : Set E3) := acube_subset_singleton_of_nonpos hc hx'.2
    rw [Set.mem_singleton_iff] at h1
    exact sub_eq_zero.mp h1
  have hnull : (volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u) = 0 :=
    measure_mono_null hsub (MeasureTheory.NullSingletonClass.measure_singleton _)
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def, hnull] at hV
  simp only [ENNReal.toReal_zero] at hV
  exact lt_irrefl 0 hV

/-! ## 2. Measurability and the sup-bound of the deviation `chiRho` -/

/-- `chiRho M ℓ d u` is measurable (`chiSmallB²` is continuous and the box indicator measurable). -/
theorem rhoRho_measurable_chiRho {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : E3) :
    Measurable (chiRho M ℓ d u) := by
  have hEq : chiRho M ℓ d u = fun z : E3 =>
      (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
        - (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
          * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
    funext z
    rw [chiRho]
  rw [hEq]
  exact Measurable.sub (((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).measurable)
    (measurable_const.mul
      (measurable_const.indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)))

/-- **Sup-bound of the deviation**:  with `Ξ := (chiSupAbs·chiSmallDecay M)²` bounding `χ_{B(u)}²`
and `chiMass/boxMass ≥ 0`,

    |chiRho M ℓ d u z| ≤ Ξ + chiMass M ℓ d u / boxMass ℓ d u .

(This is `chiRho = χ² − (κ/V)·1_B` with `χ² ∈ [0, Ξ]` and `1_B ∈ [0,1]`.) -/
theorem rhoRho_abs_chiRho_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) (z : E3) :
    |chiRho M ℓ d u z| ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
      + Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u := by
  have hΞ : (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Work.BoseFixB1S.abs_chiSmallB_le_supB hM u z) 2
  have hc0 : 0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u :=
    div_nonneg (Work.SmallBoxSliding.chiMass_nonneg M ℓ d u) hV.le
  have hind0 : 0 ≤ (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
    by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]
  have hind1 : (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z ≤ 1 := by
    by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hle : (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
      * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z
      ≤ Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u := by
    calc _ ≤ (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u) * 1 :=
          mul_le_mul_of_nonneg_left hind1 hc0
      _ = _ := mul_one _
  have hge : 0 ≤ (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
      * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z :=
    mul_nonneg hc0 hind0
  have hΞ0 : (0 : ℝ) ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 :=
    sq_nonneg _
  have hχ2 : (0 : ℝ) ≤ (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 := sq_nonneg _
  rw [chiRho, abs_le]
  constructor
  · linarith [hΞ, hΞ0, hge, hle, hχ2]
  · linarith [hΞ, hΞ0, hge, hχ2]

/-! ## 3. The deviation is mean zero on the sliding box -/

/-- **`∫_{B(u)} chiRho = 0`**:  `chiRho = χ² − (κ/V)1_B` with `χ` supported in `B`,
`∫_B χ² = κ = chiMass` and `|B| = V = boxMass`, so the two terms cancel. -/
theorem int_chiRho_mul_indicator_acube_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) :
    (∫ y in Submission.BoseGases.acube ℓ,
        chiRho M ℓ d u y * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y)
      = 0 := by
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  have hA : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : V = (volume : Measure E3).real A := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hVne : V ≠ 0 := ne_of_gt (by rw [hVdef]; exact hV)
  have hpt : ∀ y : E3, chiRho M ℓ d u y * A.indicator (fun _ => (1 : ℝ)) y
      = A.indicator (fun y => chiRho M ℓ d u y) y := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_indicator
    (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hA]
  rw [MeasureTheory.Measure.restrict_restrict_of_subset (μ := (volume : Measure E3)) hAc]
  have hstep : (∫ y in A, chiRho M ℓ d u y)
      = ∫ y in A, ((Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2 - (κ / V)) := by
    refine MeasureTheory.setIntegral_congr_fun hA (fun y hy => ?_)
    rw [hAdef] at hy
    simp only [chiRho, Set.indicator_of_mem hy, mul_one, hκdef, hVdef]
  rw [hstep]
  have hint1 : Integrable (fun y : E3 => (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2)
      ((volume : Measure E3).restrict A) :=
    (((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).continuousOn.integrableOn_compact
      (Submission.BoseGases.acube_compact hℓ)).mono_set hAc
  have hfin : (volume : Measure E3) A ≠ ⊤ := (Work.BoseFixB1S.volume_A_lt_top hℓ hAc).ne
  have hint2 : Integrable (fun _ : E3 => κ / V) ((volume : Measure E3).restrict A) :=
    MeasureTheory.integrableOn_const (μ := (volume : Measure E3)) (s := A) (C := κ / V) hfin
  rw [MeasureTheory.integral_sub hint1 hint2]
  have h1 : (∫ y in A, (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2) = κ := by
    rw [hκdef, hAdef]; exact setIntegral_chiSmallB_sq hM hℓ hd u
  have h2 : (∫ y in A, (κ / V)) = κ := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, ← hVeq]
    field_simp
  rw [h1, h2, sub_self]

/-! ## 4. The peel + mean-zero annihilation -/

/-- **The slot peel combined with the mean-zero identity.**  For a function `H` whose value on
`kcInsN m i (y, r)` is independent of the slot value `y`,

    ∫_{abox (m+1) ℓ} (chiRho(xᵢ)·1_{B(u)}(xᵢ))·H = (∫_{B(u)} chiRho)·(…) = 0 . -/
theorem int_chiRho_ind_mul_invariant_zero {m : ℕ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (i : Fin (m + 1)) {H : Submission.BoseGases.X (m + 1) → ℝ}
    (hH : ∀ (r : Submission.BoseGases.X m) (y y' : E3),
      H (Submission.BoseGases.kcInsN m i (y, r)) = H (Submission.BoseGases.kcInsN m i (y', r))) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (chiRho M ℓ d u (x i)
            * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) * H x) = 0 := by
  rw [slotWeightedPeel (ℓ := ℓ) i (w := fun y : E3 => chiRho M ℓ d u y
      * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y) hH,
    int_chiRho_mul_indicator_acube_zero hM hℓ hd u hV, zero_mul]

/-! ## 5. The pair `chiRho(xᵢ)chiRho(xⱼ)` annihilates one box projection -/

/-- **`∫ χ(xᵢ)χ(xⱼ)·PᵢF = 0`** for `i ≠ j`.  Pointwise
`χ(xᵢ)χ(xⱼ)PᵢF x = (χ(xᵢ)1_B(xᵢ))·H x` with `H x = χ(xⱼ)·(1/|B|)∫_{z∈B} F(x|i↦z)dz`, and `H` is
peel-invariant in the slot `i` because the slot mean is (and `χ(xⱼ)` with `j ≠ i` is too). -/
theorem int_chiRho_chiRho_boxPInd_zero {m : ℕ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {i j : Fin (m + 1)} (hij : i ≠ j) {F : Submission.BoseGases.X (m + 1) → ℝ} :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        chiRho M ℓ d u (x i) * chiRho M ℓ d u (x j)
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i F x) = 0 := by
  have hpt : ∀ x : Submission.BoseGases.X (m + 1),
      chiRho M ℓ d u (x i) * chiRho M ℓ d u (x j)
        * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i F x
      = (chiRho M ℓ d u (x i)
            * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
        * (chiRho M ℓ d u (x j) * ((1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ z in Submission.BoseGases.dlBox ℓ d u, F (Function.update x i z))) := by
    intro x
    simp only [Work.UBBInputs8.boxPInd]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  refine int_chiRho_ind_mul_invariant_zero hM hℓ hd u hV i ?_
  intro r y y'
  simp only [Submission.BoseGases.update_kcInsN]
  rw [Submission.BoseGases.kc_insN_other_indep m i y y' r j hij.symm]

/-! ## 6. The requested statement -/

theorem rhoRho_pair_null {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) (i j : Fin n) (hij : i ≠ j)
    (hℓ : 0 < Work.BoseFixB1.pL v μ)
    (hV : 0 < Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (F : Submission.BoseGases.X n → ℝ) (hF : Continuous F) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ),
        Work.BoseB1Cube.chiRho (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u (x i)
          * Work.BoseB1Cube.chiRho (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u (x j)
          * F x)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.pL v μ),
          Work.BoseB1Cube.chiRho (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u (x i)
            * Work.BoseB1Cube.chiRho (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u (x j)
            * (F x
                - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u) i F x
                - Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u) j F x
                + Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u) i
                    (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                      (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u) j F) x) := by
  have hd : 0 < Work.BoseFixB1.pD v μ := pD_pos_of_boxMass_pos hℓ hV
  have hM : 1 ≤ Work.BoseFixB1.pM v μ := rhoRho_pM_one
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set χ : E3 → ℝ :=
      chiRho (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u with hχdef
    set A : Set E3 :=
      Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u with hAdef
    set V : ℝ :=
      Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u with hVdef
    set Ξ : ℝ := (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay (Work.BoseFixB1.pM v μ)) ^ 2
      + Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u / V with hΞdef
    have hVpos : 0 < V := by rw [hVdef]; exact hV
    have hAmeas : MeasurableSet A := by
      rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox _ _ _
    have hAc : A ⊆ Submission.BoseGases.acube (Work.BoseFixB1.pL v μ) := by
      rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube _ _ _
    have hVeq : V = (volume : Measure E3).real A := by
      rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _
    have hχm : Measurable χ := rhoRho_measurable_chiRho hM u
    have hχb : ∀ z : E3, |χ z| ≤ Ξ := fun z => rhoRho_abs_chiRho_le hM hℓ hd u hV z
    -- bounds of the state and of its two projections
    obtain ⟨C, hC0, hFb, hPb, _hQb⟩ :=
      Work.BoseFixB1S.boxBounds (ℓ := Work.BoseFixB1.pL v μ) (volA := V) (A := A)
        hℓ hVpos hAmeas hVeq hAc (Φ := F) hF
    have hPj_b : ∀ x ∈ Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
        |Work.UBBInputs8.boxPInd V A j F x| ≤ C := hPb j
    have hPij_b : ∀ x ∈ Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
        |Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j F) x| ≤ C :=
      Work.BoseFixB1S.abs_boxPInd_le hℓ hVpos hAmeas hVeq hAc i hPj_b
    -- the three annihilations
    have h1 : (∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
        χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A i F x) = 0 :=
      int_chiRho_chiRho_boxPInd_zero hM hℓ hd u hV hij
    have h2 : (∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
        χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A j F x) = 0 := by
      have hswap := int_chiRho_chiRho_boxPInd_zero (m := m) hM hℓ hd u hV
        (i := j) (j := i) hij.symm (F := F)
      rwa [show (fun x : Submission.BoseGases.X (m + 1) =>
            χ (x j) * χ (x i) * Work.UBBInputs8.boxPInd V A j F x)
          = (fun x : Submission.BoseGases.X (m + 1) =>
            χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A j F x) from by
        funext x; ring] at hswap
    have h3 : (∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
        χ (x i) * χ (x j)
          * Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j F) x) = 0 :=
      int_chiRho_chiRho_boxPInd_zero hM hℓ hd u hV hij
    -- integrability of the four pieces
    have hχi : Measurable (fun x : Submission.BoseGases.X (m + 1) => χ (x i)) :=
      hχm.comp (measurable_pi_apply i)
    have hχj : Measurable (fun x : Submission.BoseGases.X (m + 1) => χ (x j)) :=
      hχm.comp (measurable_pi_apply j)
    have hχij : Measurable (fun x : Submission.BoseGases.X (m + 1) => χ (x i) * χ (x j)) :=
      hχi.mul hχj
    have hχij_b : ∀ x ∈ Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
        |χ (x i) * χ (x j)| ≤ Ξ * Ξ :=
      fun x _ => abs_mul_le_of_abs_le (hχb (x i)) (hχb (x j))
    have hI0 : Integrable (fun x : Submission.BoseGases.X (m + 1) => χ (x i) * χ (x j) * F x)
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ))) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hχij hF.measurable hχij_b hFb
    have hI1 : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A i F x)
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ))) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hχij
        (Work.BoseFixB1S.measurable_boxPInd V A hAmeas i hF.measurable) hχij_b (hPb i)
    have hI2 : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A j F x)
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ))) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hχij
        (Work.BoseFixB1S.measurable_boxPInd V A hAmeas j hF.measurable) hχij_b hPj_b
    have hI3 : Integrable (fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j)
            * Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j F) x)
        ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
          (Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ))) :=
      Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hχij
        (Work.BoseFixB1S.measurable_boxPInd V A hAmeas i
          (Work.BoseFixB1S.measurable_boxPInd V A hAmeas j hF.measurable)) hχij_b hPij_b
    -- the linearity step
    rw [show (∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
          χ (x i) * χ (x j)
            * (F x - Work.UBBInputs8.boxPInd V A i F x - Work.UBBInputs8.boxPInd V A j F x
                + Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j F) x))
        = ∫ x in Submission.BoseGases.abox (m + 1) (Work.BoseFixB1.pL v μ),
            (χ (x i) * χ (x j) * F x
              - χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A i F x
              - χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A j F x
              + χ (x i) * χ (x j)
                  * Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j F) x) from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    rw [integral_add
        (f := fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j) * F x
            - χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A i F x
            - χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A j F x)
        (g := fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j)
            * Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j F) x)
        ((hI0.sub hI1).sub hI2) hI3,
      integral_sub
        (f := fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j) * F x
            - χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A i F x)
        (g := fun x : Submission.BoseGases.X (m + 1) =>
          χ (x i) * χ (x j) * Work.UBBInputs8.boxPInd V A j F x)
        (hI0.sub hI1) hI2,
      integral_sub hI0 hI1, h1, h2, h3]
    ring

end Work.BoseB1Cube
