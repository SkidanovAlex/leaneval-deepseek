import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.boxConstCalibB1
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.flatPairEraseB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseB1Cube

namespace FlatPairJensen

open Submission.BoseGases Work.SmallBoxSliding Work.UBBInputs8

/-- The particle space of the chapter. -/
abbrev PE3 : Type := EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1. Auxiliary lemmas -/

/-- `pairSet n` is the set of *ordered* pairs of distinct indices, so summing over it is
iterating over `i` and the complement of `{i}`. -/
theorem pairSet_sum_eq_erase (n : ℕ) (g : Fin n → Fin n → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet n, g p.1 p.2)
      = ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i), g i j := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter, Finset.filter_ne]

/-- The sliding box volume is nonnegative. -/
theorem boxMass_nonneg (ℓ d : ℝ) (u : PE3) : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.measureReal_def]
  exact ENNReal.toReal_nonneg

/-- A null sliding box kills the cutoff mass. -/
theorem chiMass_eq_zero_of_boxMass_eq_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : PE3) (h : Work.SmallBoxSliding.boxMass ℓ d u = 0) :
    Work.SmallBoxSliding.chiMass M ℓ d u = 0 := by
  have hfin : (volume : Measure PE3) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
  have hreal : (volume : Measure PE3) (Submission.BoseGases.dlBox ℓ d u) = 0 := by
    have h1 : (volume : Measure PE3).real (Submission.BoseGases.dlBox ℓ d u) = 0 := by
      rw [← Work.SmallBoxSliding.boxMass_eq_measureReal]
      exact h
    rw [MeasureTheory.measureReal_def] at h1
    rcases (ENNReal.toReal_eq_zero_iff _).mp h1 with h0 | htop
    · exact h0
    · exact absurd htop hfin.ne
  have hzero : Submission.BoseGases.chiSmallB M ℓ d u = 0 :=
    Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero hM hℓ hd u hreal
  rw [Work.SmallBoxSliding.chiMass_def, hzero]
  simp

/-- The pure-real arithmetic of the chapter: with `S = (κ/b)Q`, `X = T/b²` and
`Q² − QN ≤ TN` one has `(S/(κN))² − S/(κN)/b ≤ X/N`. -/
theorem flatPairArith {b N Q To κ S X : ℝ} (hκ : κ ≠ 0) (hb : 0 < b) (hN : 0 < N)
    (hS : S = (κ / b) * Q) (hX : X = To / b ^ 2) (hkey : Q ^ 2 - Q * N ≤ To * N) :
    (S / (κ * N)) ^ 2 - S / (κ * N) / b ≤ X / N := by
  have hb2 : (0 : ℝ) < b ^ 2 * N ^ 2 := by positivity
  have hb3 : (0 : ℝ) < b ^ 2 * N := by positivity
  have h1 : S / (κ * N) = Q / (b * N) := by
    rw [hS]
    field_simp
  have e1 : (Q / (b * N)) ^ 2 - Q / (b * N) / b = (Q ^ 2 - Q * N) / (b ^ 2 * N ^ 2) := by
    field_simp
  have e2 : (To / b ^ 2) / N = To / (b ^ 2 * N) := by
    field_simp
  rw [h1, hX, e1, e2, div_le_div_iff₀ hb2 hb3]
  have h : (Q ^ 2 - Q * N) * (b ^ 2 * N) ≤ (To * N) * (b ^ 2 * N) :=
    mul_le_mul_of_nonneg_right hkey hb3.le
  nlinarith [h]

/-! ## 2. The one-slot corpus peels at an arbitrary particle number -/

/-- The one-slot box peel `Work.BoseFixB1S.Q0C.one_kernel` combined with `one_flat` at an
arbitrary particle number (the intermediate `oneRest` is eliminated, so the statement is
closed in `N`): for a function `g` supported on the box,

  `(∫_{abox N ℓ} (PᵢΨ)² g(xᵢ)) · volA = (∫_{B} g) · ∫_{abox N ℓ} (PᵢΨ)²`. -/
theorem one_kernel_gen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set PE3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure PE3).real A) (i : Fin N)
    {Ψ : X N → ℝ} (hΨc : Continuous Ψ) {g : PE3 → ℝ}
    (hg : Integrable g ((volume : Measure PE3).restrict A)) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * g (x i)) * volA
      = (∫ z in A, g z)
        * (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2) := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
      have h1 := Work.BoseFixB1S.Q0C.one_kernel (n := n) hℓ hvol hA hAc hvolA i hΨc hg
      have h2 := Work.BoseFixB1S.Q0C.one_flat (n := n) hℓ hvol hA hAc hvolA i hΨc
      rw [h1, h2]
      ring

/-! ## 3. The cutoff `χ_{B(u)}` -/

/-- The uniform bound `|χ_{B(u)}| ≤ chiSupAbs · chiSmallDecay M`. -/
theorem chiSmallB_abs_le_const {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u z : PE3) :
    |chiSmallB M ℓ d u z| ≤ chiSupAbs * chiSmallDecay M := by
  have h1 : |chiScale ℓ z| ≤ chiSupAbs := chiScale_abs_le_sup ℓ z
  have h2 : |chiSmall M ((ℓ * d)⁻¹ • z - u)| ≤ chiSmallDecay M :=
    chiSmall_decay_coord_le_decay hM _
  calc |chiSmallB M ℓ d u z|
      = |chiScale ℓ z| * |chiSmall M ((ℓ * d)⁻¹ • z - u)| := by
        rw [chiSmallB, abs_mul]
    _ ≤ chiSupAbs * chiSmallDecay M :=
        mul_le_mul h1 h2 (abs_nonneg _) chiSupAbs_nonneg

/-- `chiMass` is the box integral of `χ²`: `χ` vanishes off the box. -/
theorem chiMass_eq_setIntegral {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : PE3) :
    chiMass M ℓ d u = ∫ z in dlBox ℓ d u, (chiSmallB M ℓ d u z) ^ 2 := by
  rw [chiMass_def]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun z : PE3 => (chiSmallB M ℓ d u z) ^ 2) (s := dlBox ℓ d u)
    (μ := (volume : Measure PE3)) ?_).symm
  intro z hz
  have h0 : chiSmallB M ℓ d u z = 0 :=
    Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hz
  rw [h0]
  ring

/-- `χ²` is integrable on the sliding box. -/
theorem integrable_chiSq_on {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : PE3) :
    Integrable (fun z : PE3 => (chiSmallB M ℓ d u z) ^ 2)
      ((volume : Measure PE3).restrict (dlBox ℓ d u)) := by
  have hfin : (volume : Measure PE3) (dlBox ℓ d u) < ⊤ :=
    Work.BoseFixB1S.volume_A_lt_top hℓ (dlBox_subset_acube ℓ d u)
  refine MeasureTheory.IntegrableOn.of_bound hfin ?_ ((chiSupAbs * chiSmallDecay M) ^ 2) ?_
  · exact ((Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).pow 2).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M))]
    exact chiSmallB_abs_le_const hM ℓ d u z

/-- `χ(y)²χ(z)²` is integrable on the product of the box with itself. -/
theorem integrable_chiSq_prod_on {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : PE3) :
    Integrable (fun p : PE3 × PE3 => (chiSmallB M ℓ d u p.1) ^ 2 * (chiSmallB M ℓ d u p.2) ^ 2)
      ((volume : Measure (PE3 × PE3)).restrict (dlBox ℓ d u ×ˢ dlBox ℓ d u)) := by
  rw [Measure.volume_eq_prod PE3 PE3, ← Measure.prod_restrict]
  exact Integrable.mul_prod (integrable_chiSq_on hM hℓ hd u) (integrable_chiSq_on hM hℓ hd u)

/-- The double box mass of the product cutoff `χ(y)²χ(z)²` is the square of `chiMass`. -/
theorem boxM2_chiSq_eq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : PE3) :
    Work.BoseFixB1S.boxM2 (boxMass ℓ d u) (dlBox ℓ d u)
        (fun y z => (chiSmallB M ℓ d u y) ^ 2 * (chiSmallB M ℓ d u z) ^ 2)
      = (chiMass M ℓ d u) ^ 2 := by
  have hkey : (∫ p in dlBox ℓ d u ×ˢ dlBox ℓ d u,
        (chiSmallB M ℓ d u p.1) ^ 2 * (chiSmallB M ℓ d u p.2) ^ 2)
      = (∫ z in dlBox ℓ d u, (chiSmallB M ℓ d u z) ^ 2)
        * (∫ z in dlBox ℓ d u, (chiSmallB M ℓ d u z) ^ 2) := by
    show (∫ p : PE3 × PE3, (chiSmallB M ℓ d u p.1) ^ 2 * (chiSmallB M ℓ d u p.2) ^ 2
        ∂((volume : Measure (PE3 × PE3)).restrict (dlBox ℓ d u ×ˢ dlBox ℓ d u))) = _
    rw [Measure.volume_eq_prod PE3 PE3, ← Measure.prod_restrict]
    exact integral_prod_mul (f := fun z : PE3 => (chiSmallB M ℓ d u z) ^ 2)
      (g := fun z : PE3 => (chiSmallB M ℓ d u z) ^ 2)
  rw [Work.BoseFixB1S.boxM2, hkey, ← chiMass_eq_setIntegral hM hℓ hd u]
  ring

/-! ## 4. The a.e. forms of the flat hypothesis -/

/-- `boxQInd = 0` read as `1_B(xᵢ)·Φ = P_{B,i}Φ` a.e. -/
theorem ae_Aind_mul_eq_boxPInd {N : ℕ} {ℓ volA : ℝ} {A : Set PE3} {Φ : X N → ℝ}
    {i : Fin N}
    (h : Work.UBBInputs8.boxQInd volA A i Φ
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)] 0) :
    (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
        (Work.UBBInputs8.boxPInd volA A i Φ) := by
  filter_upwards [h] with x hx
  simp only [Work.UBBInputs8.boxQInd, Pi.zero_apply] at hx
  linarith

/-- The a.e. per-slot vanishing of `Q_{B,i}Φ` forces `n₊(B) = cnPlusBoxInd = 0`. -/
theorem cnPlusBoxInd_eq_zero_of_flat {N : ℕ} {ℓ volA : ℝ} {A : Set PE3} {Φ : X N → ℝ}
    (hflat : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Φ
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)] 0) :
    Work.UBBInputs8.cnPlusBoxInd ℓ A volA Φ = 0 := by
  rw [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : (fun x : X N => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)] (fun _ : X N => 0) := by
    filter_upwards [hflat i] with x hx
    have hx' : Work.UBBInputs8.boxQInd volA A i Φ x = 0 := by simpa using hx
    rw [hx']
    ring
  rw [MeasureTheory.integral_congr_ae h0]
  simp

/-! ## 5. The two peels -/

/-- **The flat slot peel.**  If the mean-free component of `Φ` in the slot `i` vanishes
a.e. on the ambient box — i.e. `Φ` is, in slot `i`, constant across the sliding small box
`B(u) = dlBox ℓ d u` — then the `χ_{B(u)}(xᵢ)²`-weighted second moment of `Φ` collapses
onto the (box-indicator-weighted) condensate projection `P_{B,i}`:

  `∫_abox Φ² χ(xᵢ)² = (chiMass / boxMass) · ∫_abox (P_{B,i}Φ)²`. -/
theorem flatSlotPeel {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (hflat : ∀ i : Fin n, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0)
    (i : Fin n) :
    ∫ x in Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      = (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u)
        * ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 := by
  classical
  -- `Q_{B,i}Φ = 0` a.e. is `1_{B(u)}(xᵢ)·Φ = P_{B,i}Φ` a.e.
  have hP := ae_Aind_mul_eq_boxPInd (N := n) (ℓ := ℓ)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u)
      (A := Submission.BoseGases.dlBox ℓ d u) (Φ := Φ) (i := i) (hflat i)
  -- hence the two integrands agree a.e. (the cutoff is supported in the box, so the
  -- box indicator may be inserted for free).
  have hae : (fun x : Submission.BoseGases.X n =>
        Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2) := by
    filter_upwards [hP] with x hx
    have hEq : Φ x * Submission.BoseGases.chiSmallB M ℓ d u (x i)
        = Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x
          * Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
      by_cases hc : Submission.BoseGases.chiSmallB M ℓ d u (x i) = 0
      · rw [hc, mul_zero, mul_zero]
      · have hmem : x i ∈ Submission.BoseGases.dlBox ℓ d u := by
          by_contra hnot
          exact hc (Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox (M := M) hM hℓ hd u hnot)
        have h1 : (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
            = 1 := by
          rw [Set.indicator_of_mem hmem]
        rw [h1, one_mul] at hx
        rw [hx]
    calc Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        = (Φ x * Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by ring
      _ = (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x
            * Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by rw [hEq]
      _ = (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
            * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by ring
  rw [MeasureTheory.integral_congr_ae hae]
  -- the one-slot peel at `g = χ²`
  have h1 := one_kernel_gen (N := n) (ℓ := ℓ)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) hℓ hvol
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u) i hΦc
      (integrable_chiSq_on hM hℓ hd u)
  rw [← chiMass_eq_setIntegral hM hℓ hd u] at h1
  rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hvol)]
  exact h1

/-- **The flat pair peel.**  Same hypotheses as `flatSlotPeel`, for a pair of distinct slots:
the product cutoff `χ(xᵢ)²χ(xⱼ)²` collapses onto the double projection `PᵢPⱼΦ`, with the
factor `(chiMass/boxMass)²`. -/
theorem flatPairPeel {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (hflat : ∀ i : Fin n, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0)
    {i j : Fin n} (hij : i ≠ j) :
    ∫ x in Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2
      = (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
        * ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ) x) ^ 2 := by
  classical
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = MeasureTheory.volume.real (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  -- the numerical form of the flat hypothesis
  have hflatCn : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0 :=
    cnPlusBoxInd_eq_zero_of_flat (A := Submission.BoseGases.dlBox ℓ d u) (Φ := Φ) hflat
  -- the two-slot erasure: `1_B(xᵢ)·1_B(xⱼ)·Φ = PᵢPⱼΦ` a.e.
  have herase := Work.BoseFixB1S.flatPairEraseB1 (ℓ := ℓ) (d := d) hℓ hd u hM hΦc hflatCn hij
  -- the two integrands agree a.e. (the cutoffs are supported in the box)
  have hae : (fun x : Submission.BoseGases.X n =>
        Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
          * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x : Submission.BoseGases.X n =>
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) j Φ) x) ^ 2
          * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
          * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2) := by
    filter_upwards [herase] with x hx
    simp only [Pi.zero_apply] at hx
    by_cases hci : Submission.BoseGases.chiSmallB M ℓ d u (x i) = 0
    · rw [hci]; ring
    by_cases hcj : Submission.BoseGases.chiSmallB M ℓ d u (x j) = 0
    · rw [hcj]; ring
    have hi : x i ∈ Submission.BoseGases.dlBox ℓ d u := by
      by_contra hnot
      exact hci (Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hnot)
    have hj : x j ∈ Submission.BoseGases.dlBox ℓ d u := by
      by_contra hnot
      exact hcj (Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hnot)
    have h1i : (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) = 1 := by
      rw [Set.indicator_of_mem hi]
    have h1j : (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 1 := by
      rw [Set.indicator_of_mem hj]
    have hΦ : Φ x = Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) j Φ) x := by
      rw [h1i, h1j, one_mul, one_mul] at hx
      linarith
    rw [hΦ]
  -- the two-slot peel at the product cutoff
  have hpv := Work.BoseFixB1S.Q0C.pair_value (N := n) (ℓ := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (A := Submission.BoseGases.dlBox ℓ d u)
    hℓ hvol hA hvolA hAc hij
    (w2 := fun y z => (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
      * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
    (integrable_chiSq_prod_on hM hℓ hd u) hΦc
  calc
    ∫ x in Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ) x) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2 :=
          MeasureTheory.integral_congr_ae hae
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ) x) ^ 2
              * ((fun y z => (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
                  * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) (x i) (x j)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
    _ = (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (fun y z => (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
          / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
        * ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ) x) ^ 2 := hpv
    _ = (Work.SmallBoxSliding.chiMass M ℓ d u / Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
        * ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) j Φ) x) ^ 2 := by
          rw [boxM2_chiSq_eq hM hℓ hd u, ← div_pow]

end FlatPairJensen

open FlatPairJensen

/-! ## 6. The target -/

theorem flatPairJensenCube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hflat : ∀ i : Fin n, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0) :
    let κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u
    let N : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2
    let S : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
    let X : ℝ := κ⁻¹ ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2
    (S / (κ * N)) ^ 2 - S / (κ * N) / (Work.SmallBoxSliding.boxMass ℓ d u) ≤ X / N := by
  classical
  dsimp only
  set κ : ℝ := Work.SmallBoxSliding.chiMass M ℓ d u with hκdef
  set b : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hbdef
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  set N : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2 with hNdef
  set S : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 with hSdef
  set X : ℝ := κ⁻¹ ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2 with hXdef
  -- ## degenerate cases
  by_cases hN0 : N = 0
  · simp [hN0]
  by_cases hκ0 : κ = 0
  · simp [hκ0, hXdef]
  by_cases hb0 : b = 0
  · exact absurd (chiMass_eq_zero_of_boxMass_eq_zero hM hℓ hd u (by rw [← hbdef]; exact hb0))
      hκ0
  -- ## the non-degenerate case
  have hbpos : 0 < b := lt_of_le_of_ne (by rw [hbdef]; exact boxMass_nonneg ℓ d u) (Ne.symm hb0)
  have hNpos : 0 < N :=
    lt_of_le_of_ne (by rw [hNdef]; exact integral_nonneg (fun x => sq_nonneg (Φ x))) (Ne.symm hN0)
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : b = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    rw [hbdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal]
  have hflat' : ∀ i : Fin n, Work.UBBInputs8.boxQInd b A i Φ
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0 := by
    intro i
    rw [hbdef, hAdef]
    exact hflat i
  -- ## the peel counts
  set Q : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxPInd b A i Φ x) ^ 2 with hQdef
  set To : ℝ := ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n ℓ,
        (Work.UBBInputs8.boxPInd b A i (Work.UBBInputs8.boxPInd b A j Φ) x) ^ 2 with hTodef
  -- ## the slot peel: `S = (κ/b)·Q`
  have hS_eq : S = (κ / b) * Q := by
    rw [hSdef, hQdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [flatSlotPeel hM hℓ hd hΦc hbpos hflat' i]
  -- ## the pair peel: `X = To/b²`
  have hXsum : (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2) = (κ / b) ^ 2 * To := by
    rw [hTodef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    rw [flatPairPeel hM hℓ hd hΦc hbpos hflat' hij]
  have hXval : X = To / b ^ 2 := by
    rw [hXdef, hXsum]
    field_simp
  -- ## the Cauchy–Schwarz (Jensen) inequality
  have hQbc : Q = Work.BoseFixB1S.boxFlatCount b ℓ A Φ := by
    rw [hQdef, Work.BoseFixB1S.boxFlatCount]
  have hTobc : Work.BoseFixB1S.boxPairCount b ℓ A Φ = To := by
    rw [Work.BoseFixB1S.boxPairCount, hTodef]
    exact pairSet_sum_eq_erase n
      (fun i j => ∫ x in Submission.BoseGases.abox n ℓ,
        (Work.UBBInputs8.boxPInd b A i (Work.UBBInputs8.boxPInd b A j Φ) x) ^ 2)
  have hjensen := Work.BoseFixB1S.boxFlatSqJensen (N := n) (ℓ := ℓ) (volA := b)
    hℓ hbpos hAmeas hvolA hAc hΦc
  have hkey : Q ^ 2 - Q * N ≤ To * N := by
    rw [← hQbc, ← hNdef, hTobc] at hjensen
    simpa [mul_comm] using hjensen
  exact flatPairArith hκ0 hbpos hNpos hS_eq hXval hkey

end Work.BoseB1Cube
