import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.WB.Lead` — the lead's own pieces of the window proof

Elementary facts about the vocabulary of `WB.Defs` that the chain needs:
positivity of the localised mass and of the density, the vanishing of `χ_{B(u)}`
where the cutoff mass vanishes, the `u`-slice bound for `χ_{B(u)}(z)²`, FS's
`U ≥ 0`, the `ε`-dictionary `nWindow = ε·μℓ³`, and the sector sums
`Σᵢ‖PᵢΦ‖² = n‖Φ‖² − n₊`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Positivity -/

lemma nCountB_nonneg (M : ℕ) (ℓ d : ℝ) (u : ℝ³) {n : ℕ} (x : X n) :
    0 ≤ nCountB M ℓ d u x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma wbMass_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {R0 : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    (hR0 : 0 < R0) {μ : ℝ} (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v))
    (hd : 0 < (paramsAt μ (a v)).d) (u : ℝ³) : 0 ≤ wbMass v h μ u :=
  wSmall1Pair_mass_nonneg hv hvrad hv_supp hR0 h hM hℓ hd u

/-! ## 2. The density: division splitting and positivity -/

lemma integral_nCountB_div (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (c : ℝ) {n : ℕ} (Φ : X n → ℝ) :
    (∫ x in abox n ℓ, (Φ x) ^ 2 * (nCountB M ℓ d u x / c))
      = (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x) / c := by
  rw [← MeasureTheory.integral_div]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
    ring)

lemma wbDens_eq {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (Φ : X n → ℝ) (u : ℝ³) :
    wbDens v h μ n Φ u
      = (∫ x in abox n (sideAt μ (a v)),
            (Φ x) ^ 2 * (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u x
              / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
          / normB v μ n Φ := by
  have h := integral_nCountB_div (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
    (chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ
  rw [wbDens, h]
  ring

lemma wbDens_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (Φ : X n → ℝ) (u : ℝ³) :
    0 ≤ wbDens v h μ n Φ u := by
  rw [wbDens_eq]
  refine div_nonneg ?_ (normB_nonneg Φ)
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
    (div_nonneg (nCountB_nonneg _ _ _ _ x) (chiMass_nonneg _ _ _ _))

/-! ## 3. Where the cutoff mass vanishes, the cutoff and the mass vanish -/

lemma chiSmallB_ae_eq_zero_of_chiMass_eq_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³} (h : chiMass M ℓ d u = 0) :
    (fun z : ℝ³ => chiSmallB M ℓ d u z) =ᵐ[volume] 0 := by
  have hint : Integrable (fun z : ℝ³ => (chiSmallB M ℓ d u z) ^ 2) :=
    integrable_chiSmallB_sq_slice hM hℓ u
  have h0 : ∫ z : ℝ³, (chiSmallB M ℓ d u z) ^ 2 = 0 := by
    rw [← chiMass_def]; exact h
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hint).1 h0
  filter_upwards [hae] with z hz
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz

lemma wbMass_eq_zero_of_chiMass_eq_zero {v : ℝ³ → ℝ} {h : ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : ℝ³}
    (hχ : chiMass M ℓ d u = 0) : w1MassB h M ℓ d u = 0 := by
  have hae := chiSmallB_ae_eq_zero_of_chiMass_eq_zero hM hℓ hd hχ
  rw [w1MassB]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with x hx
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with y hy
  simp only [Pi.zero_apply] at hx hy
  unfold wSmall1Pair wSmallPair
  rw [hx, hy]
  simp

/-! ## 4. The `u`-slice bound `∫_{I₋} χ_{B(u)}(z)² du ≤ chiSupAbs²` -/

/-- `u ↦ χ_{B(u)}(z)²` is integrable (continuous with compact support in `u`). -/
lemma integrable_chiSmallB_sq_slice_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (z : ℝ³) :
    Integrable (fun u : ℝ³ => (chiSmallB M ℓ d u z) ^ 2) := by
  have hcont : Continuous (fun u : ℝ³ => (chiSmallB M ℓ d u z) ^ 2) := by
    have h1 : Continuous (fun u : ℝ³ => chiScale ℓ z) := continuous_const
    have h2 : Continuous (fun u : ℝ³ => chiSmall M ((ℓ * d)⁻¹ • z - u)) :=
      (chiSmall_continuous hM).comp (continuous_const.sub continuous_id)
    have h3 : Continuous (fun u : ℝ³ => chiSmallB M ℓ d u z) := by
      have hgoal : (fun u : ℝ³ => chiSmallB M ℓ d u z)
          = fun u : ℝ³ => chiScale ℓ z * chiSmall M ((ℓ * d)⁻¹ • z - u) := rfl
      rw [hgoal]
      exact h1.mul h2
    exact h3.pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := closedBall (((ℓ * d)⁻¹ • z) : ℝ³) 1) (isCompact_closedBall _ _) ?_
  intro u hu
  have hu' : chiSmall M ((ℓ * d)⁻¹ • z - u) ≠ 0 := by
    intro h0
    have hb : chiSmallB M ℓ d u z = 0 := by
      rw [chiSmallB, h0, mul_zero]
    exact (Function.mem_support.mp hu) (by rw [hb]; ring)
  have hcoord : ∀ j : Fin 3, |(((ℓ * d)⁻¹ • z - u).ofLp j)| ≤ 1 / 2 :=
    fun j => chiSmall_support_mem_abs_le hM hu' j
  have hnorm : ‖((ℓ * d)⁻¹ • z - u)‖ ≤ Real.sqrt 3 * (1 / 2) :=
    coord_box_subset_eucl_ball (by norm_num) hcoord
  have hle : Real.sqrt 3 * (1 / 2) ≤ 1 := by
    have h3 : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_iff] <;> norm_num
    linarith
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact le_trans hnorm hle

lemma integral_interiorSet_chiSmallB_sq_le {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (z : ℝ³) :
    (∫ u in interiorSet ℓ d μ, (chiSmallB M ℓ d u z) ^ 2) ≤ chiSupAbs ^ 2 := by
  have hpoint : ∀ u : ℝ³, 0 ≤ (chiSmallB M ℓ d u z) ^ 2 := fun u => sq_nonneg _
  have h1 : (∫ u in interiorSet ℓ d μ, (chiSmallB M ℓ d u z) ^ 2)
      ≤ ∫ u : ℝ³, (chiSmallB M ℓ d u z) ^ 2 :=
    setIntegral_le_integral (integrable_chiSmallB_sq_slice_u hM z)
      (Filter.Eventually.of_forall hpoint)
  have h2 : (∫ u : ℝ³, (chiSmallB M ℓ d u z) ^ 2) = (chiScale ℓ z) ^ 2 :=
    integral_chiSmallB_sq_u hM z
  have h3 : (chiScale ℓ z) ^ 2 ≤ chiSupAbs ^ 2 := by
    have h := chiScale_abs_le_sup ℓ z
    calc (chiScale ℓ z) ^ 2 = |chiScale ℓ z| ^ 2 := by rw [sq_abs]
      _ ≤ chiSupAbs ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

/-! ## 5. FS's `U` is nonnegative -/

lemma wbU_nonneg {v : ℝ³ → ℝ} {h : ScatSol v} {R0 : ℝ} (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    (hR0 : 0 < R0) {μ : ℝ} (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v))
    (hd : 0 < (paramsAt μ (a v)).d) (z : ℝ³) : 0 ≤ wbU v h μ z := by
  refine integral_nonneg fun u => ?_
  exact mul_nonneg
    (div_nonneg (wbMass_nonneg hv hvrad hv_supp hR0 hM hℓ hd u) (chiMass_nonneg _ _ _ _))
    (sq_nonneg _)

/-! ## 6. The `ε`-dictionary `nWindow = ε·μℓ³` -/

lemma nWindow_eq_wbEps {v : ℝ³ → ℝ} {μ : ℝ} :
    nWindow (paramsAt μ (a v)) μ (a v) = wbEps v μ * (μ * sideAt μ (a v) ^ 3) := by
  rw [nWindow_eq, wbEps]
  ring

/-! ## 7. The sector sums -/

lemma qSum_eq {n : ℕ} {ℓ : ℝ} (Φ : X n → ℝ) :
    (∑ i : Fin n, ∫ x in abox n ℓ, (aQ ℓ i Φ x) ^ 2) = cnPlus ℓ Φ := rfl

/-- `Σᵢ‖PᵢΦ‖² = n‖Φ‖² − n₊` (per-slot Parseval, summed). -/
lemma pSum_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    (∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
      = (n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2) - cnPlus ℓ Φ := by
  have h : ∀ i : Fin n, (∫ x in abox n ℓ, (aP ℓ i Φ x) ^ 2)
      = (∫ x in abox n ℓ, (Φ x) ^ 2) - (∫ x in abox n ℓ, (aQ ℓ i Φ x) ^ 2) := by
    intro i
    have hdec := sq_norm_decomp (N := n) (ℓ := ℓ) hℓ i hΦ
    linarith
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp only [cnPlus, nsmul_eq_mul]

end Work.BoseFixB1
