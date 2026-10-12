import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.SectorAux.one_le_mu_boxMassGood
import Submission.Work.BoseFixB1.Up.FibreRowOper
import Submission.Work.BoseFixB1.Up.FrowSharp
import Submission.Work.BoseFixB1.Up.fibSumAboxIntegrable
import Submission.Work.BoseFixB1.Up.flatZeroOmega
import Submission.Work.BoseFixB1B.flatPairMass_le_const_mul_chiMass_regime
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1S.chiMass_le_const_mul_boxMass
import Submission.Work.BoseFixB1S.w1MassB_le_flatPairMassB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.CubeFlat

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. Elementary local helpers -/

/-- A continuous function is integrable on the box `abox n ℓ`. -/
theorem integrableOn_abox_local {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X n → ℝ} (hF : Continuous F) :
    IntegrableOn F (Submission.BoseGases.abox n ℓ) :=
  ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ) hF.continuousOn

/-- `χ` is continuous (local copy; the corpus version needs `1 ≤ M`). -/
theorem chiSmall_continuous_local (M : ℕ) :
    Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) := by
  unfold Submission.BoseGases.chiSmall
  exact (Submission.BoseGases.chiSmallBase_continuous M).div_const _

/-- The cube cutoff is continuous (local copy; the corpus version needs `1 ≤ M`). -/
theorem chiSmallB_continuous_local (M : ℕ) (ℓ d : ℝ) (u : E3) :
    Continuous (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) := by
  unfold Submission.BoseGases.chiSmallB
  exact (Submission.BoseGases.chiScale_continuous ℓ).mul
    ((chiSmall_continuous_local M).comp (by fun_prop))

/-- The uniform bound `|χ_{B(u)}| ≤ chiSupAbs · chiSmallDecay M` (copy of
`Work.BoseFixB1Up.chiSmallB_abs_le_const`). -/
theorem chiSmallB_abs_le_const {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u z : E3) :
    |Submission.BoseGases.chiSmallB M ℓ d u z|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  have h1 : |Submission.BoseGases.chiScale ℓ z| ≤ Submission.BoseGases.chiSupAbs :=
    Submission.BoseGases.chiScale_abs_le_sup ℓ z
  have h2 : |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)|
      ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmall_decay_coord_le_decay hM _
  calc |Submission.BoseGases.chiSmallB M ℓ d u z|
      = |Submission.BoseGases.chiScale ℓ z|
        * |Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)| := by
        rw [Submission.BoseGases.chiSmallB, abs_mul]
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        mul_le_mul h1 h2 (abs_nonneg _) Submission.BoseGases.chiSupAbs_nonneg

/-- `x ≤ z·y` with `x,y,z ≥ 0` gives `x/y ≤ z` (also at `y = 0`). -/
theorem div_le_of_le_mul_of_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x ≤ z * y) : x / y ≤ z := by
  rcases eq_or_lt_of_le hy with h0 | hpos
  · rw [← h0, div_zero]; exact hz
  · exact (div_le_iff₀ hpos).mpr h

/-- `(Σᵢ fᵢ)² = Σᵢ fᵢ² + Σᵢ Σ_{j≠i} fᵢfⱼ`. -/
theorem sq_sum_eq_sum_sq_add_erase {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 = (∑ i, f i ^ 2) + ∑ i, ∑ j ∈ (Finset.univ.erase i), f i * f j := by
  have h2 : ∀ i : ι, (∑ j, f i * f j) = f i * f i + ∑ j ∈ (Finset.univ.erase i), f i * f j := by
    intro i
    rw [← Finset.sum_erase_add _ (fun j => f i * f j) (Finset.mem_univ i)]
    ring
  calc (∑ i, f i) ^ 2 = (∑ i, f i) * (∑ j, f j) := by rw [sq]
    _ = ∑ i, ∑ j, f i * f j := Finset.sum_mul_sum _ _ _ _
    _ = ∑ i, (f i * f i + ∑ j ∈ (Finset.univ.erase i), f i * f j) :=
        Finset.sum_congr rfl (fun i _ => h2 i)
    _ = (∑ i, f i * f i) + ∑ i, ∑ j ∈ (Finset.univ.erase i), f i * f j :=
        Finset.sum_add_distrib
    _ = (∑ i, f i ^ 2) + ∑ i, ∑ j ∈ (Finset.univ.erase i), f i * f j := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ## 2. The two flat state functionals -/

/-- The **diagonal correction** `κ⁻¹²∫Φ²Σᵢχ(xᵢ)⁴` (copy of `Work.BoseFixB1.Up.flatD`). -/
noncomputable def flatD (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  (chiMass (pM v μ) (pL v μ) (pD v μ) u)⁻¹ ^ 2 *
    ∫ x in Submission.BoseGases.abox n (pL v μ), (Φ x) ^ 2 *
      ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i)) ^ 4

/-- The **pair-condensate count** `κ⁻¹²ΣᵢΣ_{j≠i}∫Φ²χ(xᵢ)²χ(xⱼ)²` (copy of
`Work.BoseFixB1.Up.flatXp`). -/
noncomputable def flatXp (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  (chiMass (pM v μ) (pL v μ) (pD v μ) u)⁻¹ ^ 2 *
    ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
      ∫ x in Submission.BoseGases.abox n (pL v μ), (Φ x) ^ 2 *
        (Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i)) ^ 2 *
        (Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x j)) ^ 2

/-- `flatMass (pL v μ) Φ = ∫_{abox}Φ²` **is** the corpus `normB`. -/
theorem flatMass_pL_eq_normB {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    flatMass (pL v μ) Φ = normB v μ n Φ := rfl

/-- The slot-sum form of the flat count. -/
theorem flatScountB_eq_sum {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
  simp only [Work.BoseFixB1.flatScountB, Work.BoseFixB1.nCountB, Finset.mul_sum]
  refine MeasureTheory.integral_finsetSum _ (fun i _ => ?_)
  exact integrableOn_abox_local hℓ
    ((hΦc.pow 2).mul (((chiSmallB_continuous_local M ℓ d u).comp
      (continuous_apply i)).pow 2))

/-! ## 3. The diagonal row -/

/-- **The diagonal row**: `flatD/‖Φ‖² ≤ Cχ²τ/κ` for any pointwise bound `Cχ` of the cutoff.
The pointwise `χ⁴ ≤ Cχ²χ²` gives `S4 ≤ Cχ²·S`; the rest is the field identity
`κ⁻¹²(Cχ²S)/N = Cχ²(S/(κN))/κ`.  (Copy of `Work.BoseFixB1.Up.flatD_div_le`.) -/
theorem flatD_div_le {v : E3 → ℝ} {μ Cχ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) (hℓ : 0 < pL v μ) (u : E3)
    (hCχ : ∀ z : E3, |Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u z| ≤ Cχ) :
    flatD v μ Φ u / normB v μ n Φ
      ≤ Cχ ^ 2 * flatTau (pM v μ) (pL v μ) (pD v μ) u Φ
          / chiMass (pM v μ) (pL v μ) (pD v μ) u := by
  have hCχ0 : 0 ≤ Cχ := le_trans (abs_nonneg _) (hCχ 0)
  rw [flatD, flatTau, flatMass_pL_eq_normB]
  set S4 : ℝ := ∫ x in Submission.BoseGases.abox n (pL v μ),
      (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ)
        (pL v μ) (pD v μ) u (x i)) ^ 4 with hS4def
  set S : ℝ := flatScountB (pM v μ) (pL v μ) (pD v μ) u Φ with hSdef
  set κ : ℝ := chiMass (pM v μ) (pL v μ) (pD v μ) u with hκdef
  set N : ℝ := normB v μ n Φ with hNdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; exact chiMass_nonneg _ _ _ _
  have hNnn : 0 ≤ N := by
    rw [hNdef, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hS4le : S4 ≤ Cχ ^ 2 * S := by
    simp only [hS4def, hSdef, flatScountB, nCountB]
    have hpt : ∀ x : Submission.BoseGases.X n,
        (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ)
            (pL v μ) (pD v μ) u (x i)) ^ 4
          ≤ Cχ ^ 2 * ((Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB
              (pM v μ) (pL v μ) (pD v μ) u (x i)) ^ 2) := by
      intro x
      have hsum : (∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ)
            (pL v μ) (pD v μ) u (x i)) ^ 4)
          ≤ Cχ ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ)
              (pL v μ) (pD v μ) u (x i)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h1 : (Submission.BoseGases.chiSmallB (pM v μ)
            (pL v μ) (pD v μ) u (x i)) ^ 2 ≤ Cχ ^ 2 := by
          have h := hCχ (x i)
          rw [abs_le] at h
          nlinarith [h.1, h.2]
        have h3 : (Submission.BoseGases.chiSmallB (pM v μ)
            (pL v μ) (pD v μ) u (x i)) ^ 4
          ≤ Cχ ^ 2 * (Submission.BoseGases.chiSmallB (pM v μ)
            (pL v μ) (pD v μ) u (x i)) ^ 2 := by
          have hh := mul_le_mul_of_nonneg_right h1
            (sq_nonneg (Submission.BoseGases.chiSmallB (pM v μ)
              (pL v μ) (pD v μ) u (x i)))
          nlinarith [hh]
        exact h3
      have h2 : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
      have h4 := mul_le_mul_of_nonneg_left hsum h2
      nlinarith [h4]
    have hI1 : Integrable (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ)
          (pL v μ) (pD v μ) u (x i)) ^ 4)
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (pL v μ))) :=
      integrableOn_abox_local hℓ ((hΦc.pow 2).mul (continuous_finsetSum _ fun i _ =>
        ((chiSmallB_continuous_local _ _ _ _).comp (continuous_apply i)).pow 4))
    have hI2 : Integrable (fun x : Submission.BoseGases.X n => Cχ ^ 2 *
        ((Φ x) ^ 2 * ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ)
          (pL v μ) (pD v μ) u (x i)) ^ 2))
        ((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n (pL v μ))) :=
      integrableOn_abox_local hℓ (continuous_const.mul ((hΦc.pow 2).mul
        (continuous_finsetSum _ fun i _ =>
          ((chiSmallB_continuous_local _ _ _ _).comp (continuous_apply i)).pow 2)))
    have hmono := integral_mono hI1 hI2 hpt
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul]
  by_cases hκ0 : κ = 0
  · simp [hκ0]
  by_cases hN0 : N = 0
  · simp [hN0]
  have hκpos : 0 < κ := lt_of_le_of_ne hκnn (Ne.symm hκ0)
  have hNpos : 0 < N := lt_of_le_of_ne hNnn (Ne.symm hN0)
  have hrhs : Cχ ^ 2 * (S / (κ * N)) / κ = κ⁻¹ ^ 2 * (Cχ ^ 2 * S) / N := by
    field_simp
  rw [hrhs]
  have hcoef : 0 ≤ κ⁻¹ ^ 2 / N := div_nonneg (sq_nonneg _) hNpos.le
  have h := mul_le_mul_of_nonneg_right hS4le hcoef
  rwa [show S4 * (κ⁻¹ ^ 2 / N) = κ⁻¹ ^ 2 * S4 / N from by ring,
    show Cχ ^ 2 * S * (κ⁻¹ ^ 2 / N) = κ⁻¹ ^ 2 * (Cχ ^ 2 * S) / N from by ring] at h

/-! ## 4. The `τ`-identity and the zero-mass state -/

/-- A state of zero mass on the box has zero flat count (the integrand carries `Φ²`). -/
theorem flatScountB_eq_zero_of_flatMass_eq_zero {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦc : Continuous Φ)
    (hm : flatMass ℓ Φ = 0) :
    flatScountB M ℓ d u Φ = 0 := by
  have hfint : Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    integrableOn_abox_local hℓ (hΦc.pow 2)
  have hz : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) = 0 := by
    rw [Work.BoseFixB1.flatMass] at hm; exact hm
  have hae : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      =ᵐ[(volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (Φ x)) hfint).mp hz
  have hae2 : (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * nCountB M ℓ d u x)
      =ᵐ[(volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)] 0 := by
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, zero_mul]
  rw [flatScountB, MeasureTheory.integral_congr_ae hae2]
  simp

/-- **The `τ`-identity**: `flatScountB/κ = flatTau·flatMass`. -/
theorem flatScountB_div_eq_flatTau_mul {M : ℕ} {ℓ d : ℝ} {u : E3} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦc : Continuous Φ) :
    flatScountB M ℓ d u Φ / chiMass M ℓ d u
      = flatTau M ℓ d u Φ * flatMass ℓ Φ := by
  by_cases hκ : chiMass M ℓ d u = 0
  · have hτ0 : flatTau M ℓ d u Φ = 0 := by
      rw [flatTau, hκ, zero_mul, div_zero]
    rw [hτ0, zero_mul, hκ, div_zero]
  · by_cases hm : flatMass ℓ Φ = 0
    · have hS0 := flatScountB_eq_zero_of_flatMass_eq_zero (M := M) (d := d) (u := u) hℓ hΦc hm
      have hτ0 : flatTau M ℓ d u Φ = 0 := by
        rw [flatTau, hm, mul_zero, div_zero]
      rw [hτ0, zero_mul, hS0, zero_div]
    · rw [flatTau]
      field_simp

/-- The same identity in the `normB` vocabulary. -/
theorem flatScountB_div_eq_flatTau_mul_normB {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < pL v μ)
    (hΦc : Continuous Φ) (u : E3) :
    flatScountB (pM v μ) (pL v μ) (pD v μ) u Φ
        / chiMass (pM v μ) (pL v μ) (pD v μ) u
      = flatTau (pM v μ) (pL v μ) (pD v μ) u Φ * normB v μ n Φ :=
  flatScountB_div_eq_flatTau_mul (M := pM v μ) (ℓ := pL v μ)
    (d := pD v μ) (u := u) hℓ hΦc

/-! ## 5. The variance split -/

/-- **The `(Σχ²)²` split of `∫Φ²t²`**: `flatT2 = flatD + flatXp`. -/
theorem flatT2_eq_flatD_add_flatXp {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hℓ : 0 < pL v μ) (u : E3) :
    Work.BoseFixB1.Up.flatT2 v μ Φ u = flatD v μ Φ u + flatXp v μ Φ u := by
  show (∫ x in Submission.BoseGases.abox n (pL v μ), (Φ x) ^ 2 *
        (nCountB (pM v μ) (pL v μ) (pD v μ) u x
          / chiMass (pM v μ) (pL v μ) (pD v μ) u) ^ 2)
      = (chiMass (pM v μ) (pL v μ) (pD v μ) u)⁻¹ ^ 2 *
          (∫ x in Submission.BoseGases.abox n (pL v μ), (Φ x) ^ 2 *
            ∑ i : Fin n, (Submission.BoseGases.chiSmallB (pM v μ) (pL v μ)
              (pD v μ) u (x i)) ^ 4)
        + (chiMass (pM v μ) (pL v μ) (pD v μ) u)⁻¹ ^ 2 *
          (∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
            ∫ x in Submission.BoseGases.abox n (pL v μ), (Φ x) ^ 2 *
              (Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i)) ^ 2 *
              (Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x j)) ^ 2)
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB (pM v μ) (pL v μ) (pD v μ) u with hχdef
  set κ : ℝ := chiMass (pM v μ) (pL v μ) (pD v μ) u with hκdef
  have hχc : Continuous χ := by rw [hχdef]; exact chiSmallB_continuous_local _ _ _ _
  -- the pointwise identity
  have hpt : ∀ x : Submission.BoseGases.X n, (nCountB (pM v μ) (pL v μ) (pD v μ) u x / κ) ^ 2
      = κ⁻¹ ^ 2 * ((∑ i : Fin n, (χ (x i)) ^ 4)
          + ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
              (χ (x i)) ^ 2 * (χ (x j)) ^ 2) := by
    intro x
    have hsq := sq_sum_eq_sum_sq_add_erase (fun i : Fin n => (χ (x i)) ^ 2)
    have h4 : (∑ i : Fin n, ((χ (x i)) ^ 2) ^ 2) = ∑ i : Fin n, (χ (x i)) ^ 4 :=
      Finset.sum_congr rfl (fun i _ => by ring)
    have hdiv : ((∑ i : Fin n, (χ (x i)) ^ 2) / κ) ^ 2
        = ((∑ i : Fin n, (χ (x i)) ^ 2) ^ 2) * κ⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, mul_pow]
    rw [Work.BoseFixB1.nCountB, hdiv, hsq, h4]
    ring
  -- integrability of the pieces
  have hintD : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, (χ (x i)) ^ 4)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (pL v μ))) :=
    integrableOn_abox_local hℓ ((hΦc.pow 2).mul
      (continuous_finsetSum _ fun i _ => (hχc.comp (continuous_apply i)).pow 4))
  have hintcont : Continuous (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        (χ (x i)) ^ 2 * (χ (x j)) ^ 2) :=
    (hΦc.pow 2).mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ =>
        ((hχc.comp (continuous_apply i)).pow 2).mul
          ((hχc.comp (continuous_apply j)).pow 2))
  have hintX : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
        (χ (x i)) ^ 2 * (χ (x j)) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (pL v μ))) :=
    integrableOn_abox_local hℓ hintcont
  have hintXi : ∀ i : Fin n, Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ j ∈ (Finset.univ.erase i), (χ (x i)) ^ 2 * (χ (x j)) ^ 2)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (pL v μ))) := fun i =>
    integrableOn_abox_local hℓ ((hΦc.pow 2).mul (continuous_finsetSum _ fun j _ =>
      ((hχc.comp (continuous_apply i)).pow 2).mul
        ((hχc.comp (continuous_apply j)).pow 2)))
  have hintXij : ∀ (i : Fin n) (j : Fin n), Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ((χ (x i)) ^ 2 * (χ (x j)) ^ 2))
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (pL v μ))) := fun i j =>
    integrableOn_abox_local hℓ ((hΦc.pow 2).mul
      (((hχc.comp (continuous_apply i)).pow 2).mul
        ((hχc.comp (continuous_apply j)).pow 2)))
  -- the three conversions
  have hstep1 : (∫ x in Submission.BoseGases.abox n (pL v μ),
        (Φ x) ^ 2 * (nCountB (pM v μ) (pL v μ) (pD v μ) u x / κ) ^ 2)
      = κ⁻¹ ^ 2 * (∫ x in Submission.BoseGases.abox n (pL v μ),
          (Φ x) ^ 2 * ((∑ i : Fin n, (χ (x i)) ^ 4)
            + ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
                (χ (x i)) ^ 2 * (χ (x j)) ^ 2)) := by
    rw [show (fun x : Submission.BoseGases.X n =>
            (Φ x) ^ 2 * (nCountB (pM v μ) (pL v μ) (pD v μ) u x / κ) ^ 2)
          = (fun x : Submission.BoseGases.X n => κ⁻¹ ^ 2 *
              ((Φ x) ^ 2 * ((∑ i : Fin n, (χ (x i)) ^ 4)
                + ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
                    (χ (x i)) ^ 2 * (χ (x j)) ^ 2))) from by
        funext x
        rw [hpt x]
        ring]
    rw [MeasureTheory.integral_const_mul]
  have hstep2 : (∫ x in Submission.BoseGases.abox n (pL v μ),
          (Φ x) ^ 2 * ((∑ i : Fin n, (χ (x i)) ^ 4)
            + ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
                (χ (x i)) ^ 2 * (χ (x j)) ^ 2))
      = (∫ x in Submission.BoseGases.abox n (pL v μ),
            (Φ x) ^ 2 * ∑ i : Fin n, (χ (x i)) ^ 4)
        + ∫ x in Submission.BoseGases.abox n (pL v μ),
            (Φ x) ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
              (χ (x i)) ^ 2 * (χ (x j)) ^ 2 := by
    rw [← MeasureTheory.integral_add hintD hintX]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have hstep3 : (∫ x in Submission.BoseGases.abox n (pL v μ),
          (Φ x) ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
            (χ (x i)) ^ 2 * (χ (x j)) ^ 2)
      = ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
          ∫ x in Submission.BoseGases.abox n (pL v μ),
            (Φ x) ^ 2 * (χ (x i)) ^ 2 * (χ (x j)) ^ 2 := by
    rw [show (fun x : Submission.BoseGases.X n =>
            (Φ x) ^ 2 * ∑ i : Fin n, ∑ j ∈ (Finset.univ.erase i),
              (χ (x i)) ^ 2 * (χ (x j)) ^ 2)
          = (fun x : Submission.BoseGases.X n =>
              ∑ i : Fin n, (Φ x) ^ 2 * ∑ j ∈ (Finset.univ.erase i),
                (χ (x i)) ^ 2 * (χ (x j)) ^ 2) from by
        funext x
        rw [Finset.mul_sum]]
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => hintXi i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (fun x : Submission.BoseGases.X n =>
            (Φ x) ^ 2 * ∑ j ∈ (Finset.univ.erase i), (χ (x i)) ^ 2 * (χ (x j)) ^ 2)
          = (fun x : Submission.BoseGases.X n =>
              ∑ j ∈ (Finset.univ.erase i),
                (Φ x) ^ 2 * ((χ (x i)) ^ 2 * (χ (x j)) ^ 2)) from by
        funext x
        rw [Finset.mul_sum]]
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => hintXij i j)]
    exact Finset.sum_congr rfl (fun j _ =>
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring)))
  rw [hstep1, hstep2, hstep3]
  ring

/-- `flatVar v μ Φ u = flatD v μ Φ u + flatXp v μ Φ u − τ²‖Φ‖²`. -/
theorem flatVar_eq_flatD_add_flatXp_sub {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hℓ : 0 < pL v μ) (u : E3) :
    Work.BoseFixB1.Up.flatVar v μ Φ u = flatD v μ Φ u + flatXp v μ Φ u
      - flatTau (pM v μ) (pL v μ) (pD v μ) u Φ ^ 2 * normB v μ n Φ := by
  rw [Work.BoseFixB1.Up.flatVar, flatT2_eq_flatD_add_flatXp h hΦc hℓ u]

end Work.BoseB1Cube.CubeFlat

/-!
# `Submission.Work.BoseB1Cube.flatZeroAux` — the cone-restricted exactly-flat per-box rows

This module carries, **in a fresh namespace** (`Work.BoseB1Cube.CubeFlat`), the pieces of the
exactly-flat branch of FS `thm:smallbox` that the cone of
`Submission.Work.BoseB1Cube.cubePerBox_flatZeroArm` can hold.  The original development lives in
`Submission/Work/BoseFixB1/Up/` and `Submission/Work/BoseFixB1Up/`, but those modules cannot be
imported here: they (or their cones) re-declare `Work.BoseFixB1S.chiSmallB_continuous`,
`chiSmallB_eq_zero_of_notMem_dlBox`, `wSmallPair_eq_zero_of_notMem_dlBox` or
`Work.BoseFixB1S.boxQInd_eq`, all of which are already present in this area's cone (via
`Submission.Work.BoseFixB1S.boxM1Info`, `...chiSmallB_eq_zero_of_volume_dlBox_eq_zero` and
`...BoxPotOper`).  Hence the proofs are re-stated here from scratch, under fresh names, in the
restricted cone.

Contents:

* `flatD` — the diagonal correction `κ⁻¹²∫Φ²Σᵢχ(xᵢ)⁴`;
* `flatXp` — the pair-condensate count `κ⁻¹²ΣᵢΣ_{j≠i}∫Φ²χ(xᵢ)²χ(xⱼ)²`;
* `flatD_div_le` — `flatD/‖Φ‖² ≤ Cχ²τ/κ`;
* `flatT2_eq_flatD_add_flatXp` — the elementary `(Σχ²)²` split of `∫Φ²t²`;
* `flatVar_eq_flatD_add_flatXp_sub` — the variance split `flatVar = flatD + flatXp − τ²‖Φ‖²`;
* `flatScountB_div_eq_flatTau_mul` — `flatScountB/κ = τ‖Φ‖²`;
* the elementary helper `chiSmallB_abs_le_const`.
-/
