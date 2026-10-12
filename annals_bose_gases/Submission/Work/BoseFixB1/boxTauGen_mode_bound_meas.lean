import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.bogoliubov_one_mode
import Submission.Work.BoseFixB1.boxOpG_adjoint_one_meas
import Submission.Work.BoseFixB1.boxOpG_one_one_flatCount
import Submission.Work.BoseFixB1.boxOpZ_gg_nonneg_meas
import Submission.Work.BoseFixB1.integral_boxOpG_f_congr_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxTauGen_mode_bound_meas` — the sharp per-mode Bogoliubov bound at a
general box for an **a.e. measurable** mode function

This is the measurable-weight version of the (continuous-weight) bound
`Work.BoseFixB1.boxTauGen_mode_bound`: for a measurable `g` with `tsupport g ⊆ Ac ⊆ acube a`
and `|g| ≤ Cg`, and a continuous state `Ψ` on `X (N+1)`,

  `- ((A - √(A² − B²))/2)·(∫_Ac g²)·S ≤ A·P_g + B·R_g`  for `A > 0`, `|B| ≤ A`,

where `P_g = boxModePGen`, `R_g = boxModeRGen` are the number and pairing contents of the
genuine (indicator-carrying) box `τ`-operator at the mode `g`, and
`S = boxFlatCount volA a Ac Ψ` is the localised flat count.

## Proof

The analytic core is `boxTauGen_comm_diff_le_meas`:

  `boxModeTGen − boxModePGen ≤ (∫_Ac g²)·S`,

i.e. the sharp two-mode commutator bound, obtained from the exact operator identity
`X(YΨ) − Y(XΨ) = (∫_Ac g²)·boxOpG A 1 1 Ψ − volA·boxOpZ A g g Ψ` (`boxOpG_commutator_meas`)
together with the two adjointness identities (`boxOpG_adjoint_meas`, `boxOpG_adjoint_one_meas`),
the flat-count identity `∫ Ψ·boxOpG A 1 1 Ψ = volA·S` (`boxOpG_one_one_flatCount`) and the
positivity `0 ≤ ∫ Ψ·boxOpZ A g g Ψ` (`boxOpZ_gg_nonneg_meas`).  The c-number (LHY) step is the
purely algebraic `bogoliubov_one_mode`.

The passage from an `AEMeasurable` `g` to the measurable case is by replacing `g` with a
measurable, bounded representative that vanishes off `Ac` (`AEMeasurable.mk`), which agrees with
`g` a.e. on `Ac`; every function of `g` that occurs is an integral over `Ac`, hence unchanged.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary helpers -/

/-- A continuous state is bounded on the box (nonnegative bound). -/
lemma exists_bound_abox_pos {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : X N → ℝ} (hΨ : Continuous Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |Ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΨ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- A function whose topological support lies in `A` vanishes off `A`. -/
lemma eq_zero_of_tsupport_subset {A : Set E3} {g : E3 → ℝ} (hgs : tsupport g ⊆ A) :
    ∀ z, z ∉ A → g z = 0 := by
  intro z hz
  by_contra hne
  exact hz (hgs (subset_tsupport g (Function.mem_support.mpr hne)))

/-- For `g` vanishing off `A`, the two `(g,1)`-slot operators agree pointwise. -/
lemma boxOpZ_g_one_eq_boxOpG_pointwise {M : ℕ} {A : Set E3} {g : E3 → ℝ}
    (hg0 : ∀ z, z ∉ A → g z = 0) (Φ : X M → ℝ) (x : X M) :
    boxOpZ A g (fun _ => (1 : ℝ)) Φ x = boxOpG A g (fun _ => (1 : ℝ)) Φ x := by
  simp only [boxOpZ, boxOpG, one_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : x i ∈ A
  · rw [Set.indicator_of_mem hi, one_mul]
  · rw [Set.indicator_of_notMem hi, zero_mul, hg0 (x i) hi, zero_mul]

/-- The `(f + α g)²`-expansion of the box integral for bounded measurable `f`, `g`. -/
lemma integral_sq_add_expand_meas {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : X N → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) (hgb : ∀ x ∈ abox N ℓ, |g x| ≤ Cg) (α : ℝ) :
    (∫ x in abox N ℓ, (f x + α * g x) ^ 2)
      = (∫ x in abox N ℓ, (f x) ^ 2) + 2 * α * (∫ x in abox N ℓ, f x * g x)
        + α ^ 2 * (∫ x in abox N ℓ, (g x) ^ 2) := by
  have hI1 : IntegrableOn (fun x : X N => (f x) ^ 2) (abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hfm hfb
  have hI3 : IntegrableOn (fun x : X N => (g x) ^ 2) (abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hgm hgb
  have hI2 : IntegrableOn (fun x : X N => 2 * α * (f x * g x)) (abox N ℓ) volume :=
    (Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hfm hgm hfb hgb).const_mul (2 * α)
  have hI4 : IntegrableOn (fun x : X N => α ^ 2 * (g x) ^ 2) (abox N ℓ) volume :=
    hI3.const_mul (α ^ 2)
  have hI12 : IntegrableOn (fun x : X N => (f x) ^ 2 + 2 * α * (f x * g x)) (abox N ℓ) volume :=
    hI1.add hI2
  rw [show (fun x : X N => (f x + α * g x) ^ 2)
      = fun x => ((f x) ^ 2 + 2 * α * (f x * g x)) + α ^ 2 * (g x) ^ 2 by
    funext x; ring]
  rw [MeasureTheory.integral_add hI12 hI4, MeasureTheory.integral_add hI1 hI2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## 2. Auxiliary: Fubini on `A × A`, the cross-slot commutation and the one-slot algebra -/

/-- Fubini on `A × A` for a bounded measurable kernel. -/
lemma integral_integral_swap_restrict {A : Set E3} (hAm : MeasurableSet A)
    (hAfin : (volume : Measure E3) A < ⊤) {K : E3 → E3 → ℝ}
    (hKm : Measurable (Function.uncurry K)) {C : ℝ}
    (hKb : ∀ z ∈ A, ∀ w ∈ A, ‖K z w‖ ≤ C) :
    (∫ z in A, ∫ w in A, K z w) = ∫ w in A, ∫ z in A, K z w := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  refine MeasureTheory.integral_integral_swap (μ := (volume : Measure E3).restrict A)
    (ν := (volume : Measure E3).restrict A) ?_
  refine MeasureTheory.Integrable.of_bound hKm.aestronglyMeasurable C ?_
  rw [Measure.prod_restrict]
  rw [MeasureTheory.ae_restrict_iff' (hAm.prod hAm)]
  exact Filter.Eventually.of_forall (fun p hp => hKb p.1 hp.1 p.2 hp.2)

/-- Two successive updates of a box configuration stay in the box. -/
lemma update_update_mem_abox {M : ℕ} {a : ℝ} {A : Set E3} (hAc : A ⊆ acube a)
    {x : X M} (hx : x ∈ abox M a) {i j : Fin M} {z w : E3} (hz : z ∈ A) (hw : w ∈ A) :
    Function.update (Function.update x i z) j w ∈ abox M a := by
  intro k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk1 : k = j
  · rw [if_pos hk1]; exact hAc hw
  · rw [if_neg hk1]
    by_cases hk2 : k = i
    · rw [if_pos hk2]; exact hAc hz
    · rw [if_neg hk2]; exact hx k

/-- The cross-slot commutation `Aop_i Bop_j = Bop_j Aop_i` (`i ≠ j`) at a measurable weight. -/
lemma Aop_Bop_comm_restrict {M : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a)
    {g : E3 → ℝ} (hgm : Measurable g) {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X M → ℝ} (hΨ : Continuous Ψ) {i j : Fin M} (hij : i ≠ j)
    {x : X M} (hx : x ∈ abox M a) :
    Aop A g i (Bop A g j Ψ) x = Bop A g j (Aop A g i Ψ) x := by
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := exists_bound_abox_pos (N := M) ha hΨ
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  -- the kernel of the Fubini step
  have hKm : Measurable (Function.uncurry (fun z w : E3 =>
      g w * Ψ (Function.update (Function.update x i w) j z))) := by
    have hcd : Continuous fun p : E3 × E3 =>
        Function.update (Function.update x i p.2) j p.1 :=
      (((continuous_const : Continuous fun _ : E3 × E3 => x).update i continuous_snd).update j
        continuous_fst)
    exact Measurable.mul (hgm.comp measurable_snd) (hΨ.measurable.comp hcd.measurable)
  have hKb : ∀ z ∈ A, ∀ w ∈ A,
      ‖g w * Ψ (Function.update (Function.update x i w) j z)‖ ≤ max Cg 0 * max CΨ 0 := by
    intro z hz w hw
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (le_trans (hgC w) (le_max_left _ _))
      (le_trans (hCΨ _ (update_update_mem_abox hAc hx hw hz)) (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  have hF := integral_integral_swap_restrict (A := A) hAm hAfin hKm hKb
  -- unfold the two one-slot operators
  simp only [Aop_apply, Bop_apply, one_mul]
  -- LHS = 1_A(x i) * g (x j) * ∫_z (g z * ∫_w Ψ(x[i:=z][j:=w]))
  have hL : A.indicator (fun _ => (1 : ℝ)) (x i)
        * ∫ z in A, g z * (g ((Function.update x i z) j)
            * ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
      = A.indicator (fun _ => (1 : ℝ)) (x i) * g (x j)
        * ∫ z in A, (g z * ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) := by
    have h1 : ∀ z : E3, g ((Function.update x i z) j) = g (x j) := by
      intro z
      rw [Function.update_apply, if_neg (Ne.symm hij)]
    rw [show (fun z : E3 => g z * (g ((Function.update x i z) j)
          * ∫ w in A, Ψ (Function.update (Function.update x i z) j w)))
        = fun z : E3 => g (x j) * (g z
          * ∫ w in A, Ψ (Function.update (Function.update x i z) j w)) from by
      funext z; rw [h1 z]; ring]
    rw [MeasureTheory.integral_const_mul]
    ring
  -- RHS = g (x j) * 1_A(x i) * ∫_z ∫_w g w Ψ(x[i:=w][j:=z])
  have hR : g (x j) * ∫ z in A, A.indicator (fun _ => (1 : ℝ))
          ((Function.update x j z) i)
        * ∫ w in A, g w * Ψ (Function.update (Function.update x j z) i w)
      = A.indicator (fun _ => (1 : ℝ)) (x i) * g (x j)
        * ∫ z in A, ∫ w in A, g w * Ψ (Function.update (Function.update x i w) j z) := by
    have h1 : ∀ z : E3, (Function.update x j z) i = x i := by
      intro z
      rw [Function.update_apply, if_neg hij]
    have h2 : ∀ z w : E3, Function.update (Function.update x j z) i w
        = Function.update (Function.update x i w) j z := by
      intro z w
      rw [Function.update_comm hij w z x]
    rw [show (fun z : E3 => A.indicator (fun _ => (1 : ℝ)) ((Function.update x j z) i)
          * ∫ w in A, g w * Ψ (Function.update (Function.update x j z) i w))
        = fun z : E3 => A.indicator (fun _ => (1 : ℝ)) (x i)
          * ∫ w in A, g w * Ψ (Function.update (Function.update x i w) j z) from by
      funext z
      rw [h1 z]
      congr 1
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun w => by simp only [h2 z w]))]
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [hL, hR]
  have hIR : (∫ z in A, ∫ w in A, g w * Ψ (Function.update (Function.update x i w) j z))
      = ∫ z in A, ∫ w in A, g z * Ψ (Function.update (Function.update x i z) j w) := by
    rw [hF]
  rw [hIR]
  rw [show (∫ z in A, (g z * ∫ w in A, Ψ (Function.update (Function.update x i z) j w)))
      = ∫ z in A, ∫ w in A, g z * Ψ (Function.update (Function.update x i z) j w) from by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show g z * (∫ w in A, Ψ (Function.update (Function.update x i z) j w))
        = ∫ w in A, g z * Ψ (Function.update (Function.update x i z) j w)
    rw [MeasureTheory.integral_const_mul]]

/-- Same-slot composition `Aop_i ∘ Bop_i = (∫_A g²)·Dop_i` (purely algebraic). -/
lemma Aop_Bop_self_restrict {M : ℕ} {A : Set E3} (g : E3 → ℝ) (Ψ : X M → ℝ) (i : Fin M) :
    Aop A g i (Bop A g i Ψ) = fun y => (∫ z in A, (g z) ^ 2) * Dop A i Ψ y := by
  funext y
  simp only [Aop_apply, Bop_apply, Dop_apply, one_mul, Function.update_self, Function.update_idem]
  set C : ℝ := ∫ w in A, Ψ (Function.update y i w)
  have hcongr : (∫ z in A, g z * (g z * C)) = (∫ z in A, (g z) ^ 2) * C := by
    rw [show (fun z => g z * (g z * C)) = fun z => (g z) ^ 2 * C by
      funext z; ring]
    rw [MeasureTheory.integral_mul_const]
  rw [hcongr]
  ring

/-- Same-slot composition `Bop_i ∘ Aop_i = (∫_A 1)·Cop_i` (purely algebraic). -/
lemma Bop_Aop_self_restrict {M : ℕ} {A : Set E3} (hAm : MeasurableSet A) (g : E3 → ℝ)
    (Ψ : X M → ℝ) (i : Fin M) :
    Bop A g i (Aop A g i Ψ) = fun y => (∫ z in A, (1 : ℝ)) * Cop A g i Ψ y := by
  funext y
  simp only [Bop_apply, Aop_apply, Cop_apply, Function.update_self, Function.update_idem]
  have hInt : (∫ z in A, (1 : ℝ) * (A.indicator (fun _ => (1 : ℝ)) z
        * (∫ w in A, g w * Ψ (Function.update y i w))))
      = (∫ z in A, (1 : ℝ)) * (∫ w in A, g w * Ψ (Function.update y i w)) := by
    simp only [one_mul]
    rw [MeasureTheory.integral_mul_const, MeasureTheory.setIntegral_indicator hAm, Set.inter_self]
  rw [hInt]
  ring

/-- Measurability of a one-slot `Aop`. -/
lemma measurable_Aop_restrict {M : ℕ} {A : Set E3} (hAm : MeasurableSet A) {g : E3 → ℝ}
    (hgm : Measurable g) {Ψ : X M → ℝ} (hΨm : Measurable Ψ) (j : Fin M) :
    Measurable (Aop A g j Ψ) := by
  have h : Aop A g j Ψ = fun u => A.indicator (fun _ => (1 : ℝ)) (u j)
      * ∫ z in A, g z * Ψ (Function.update u j z) := by
    funext u; simp only [Aop_apply]
  rw [h]
  exact ((measurable_const.indicator hAm).comp (measurable_pi_apply j)).mul
    (measurable_fibreMean_mul hAm j hgm hΨm)

/-- Measurability of a one-slot `Bop`. -/
lemma measurable_Bop_restrict {M : ℕ} {A : Set E3} (hAm : MeasurableSet A) {g : E3 → ℝ}
    (hgm : Measurable g) {Ψ : X M → ℝ} (hΨm : Measurable Ψ) (j : Fin M) :
    Measurable (Bop A g j Ψ) := by
  have h : Bop A g j Ψ = fun u => g (u j)
      * ∫ z in A, (1 : ℝ) * Ψ (Function.update u j z) := by
    funext u; simp only [Bop_apply]
  rw [h]
  exact (hgm.comp (measurable_pi_apply j)).mul
    (measurable_fibreMean_mul hAm j measurable_const hΨm)

/-- Bound of a one-slot `Aop` at a point of the box. -/
lemma abs_Aop_le_restrict {M : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3} (hAc : A ⊆ acube a)
    {g : E3 → ℝ} {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X M → ℝ} {CΨ : ℝ} (hΨb : ∀ u ∈ abox M a, |Ψ u| ≤ CΨ) (j : Fin M) :
    ∀ u ∈ abox M a, |Aop A g j Ψ u| ≤ max Cg 0 * (max CΨ 0 * (volume A).toReal) := by
  intro u hu
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  have hInt : |∫ w in A, g w * Ψ (Function.update u j w)|
      ≤ max Cg 0 * (max CΨ 0 * (volume A).toReal) := by
    have hb : ∀ w ∈ A, ‖g w * Ψ (Function.update u j w)‖ ≤ max Cg 0 * max CΨ 0 := by
      intro w hw
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (le_trans (hgC w) (le_max_left _ _))
        (le_trans (hΨb _ (update_mem_abox_toolbox hAc hu j hw)) (le_max_left _ _))
        (abs_nonneg _) (le_max_right _ _)
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3)) (s := A)
      (f := fun w : E3 => g w * Ψ (Function.update u j w)) (C := max Cg 0 * max CΨ 0) hAfin hb
    rw [Real.norm_eq_abs, MeasureTheory.Measure.real] at h
    refine le_trans h ?_
    rw [mul_assoc]
  have hind : |A.indicator (fun _ => (1 : ℝ)) (u j)| ≤ 1 := by
    by_cases hui : u j ∈ A
    · rw [Set.indicator_of_mem hui, abs_one]
    · rw [Set.indicator_of_notMem hui, abs_zero]; exact zero_le_one
  show |A.indicator (fun _ => (1 : ℝ)) (u j) * (∫ w in A, g w * Ψ (Function.update u j w))|
      ≤ max Cg 0 * (max CΨ 0 * (volume A).toReal)
  rw [abs_mul]
  calc |A.indicator (fun _ => (1 : ℝ)) (u j)| * |∫ w in A, g w * Ψ (Function.update u j w)|
      ≤ 1 * (max Cg 0 * (max CΨ 0 * (volume A).toReal)) :=
        mul_le_mul hind hInt (abs_nonneg _) zero_le_one
    _ = max Cg 0 * (max CΨ 0 * (volume A).toReal) := one_mul _

/-- Bound of a one-slot `Bop` at a point of the box. -/
lemma abs_Bop_le_restrict {M : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3} (hAc : A ⊆ acube a)
    {g : E3 → ℝ} {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X M → ℝ} {CΨ : ℝ} (hΨb : ∀ u ∈ abox M a, |Ψ u| ≤ CΨ) (j : Fin M) :
    ∀ u ∈ abox M a, |Bop A g j Ψ u| ≤ max Cg 0 * (max CΨ 0 * (volume A).toReal) := by
  intro u hu
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  have hInt : |∫ w in A, (1 : ℝ) * Ψ (Function.update u j w)|
      ≤ max CΨ 0 * (volume A).toReal := by
    have hb : ∀ w ∈ A, ‖(1 : ℝ) * Ψ (Function.update u j w)‖ ≤ max CΨ 0 := by
      intro w hw
      rw [Real.norm_eq_abs, abs_mul, abs_one, one_mul]
      exact le_trans (hΨb _ (update_mem_abox_toolbox hAc hu j hw)) (le_max_left _ _)
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3)) (s := A)
      (f := fun w : E3 => (1 : ℝ) * Ψ (Function.update u j w)) (C := max CΨ 0) hAfin hb
    rwa [Real.norm_eq_abs, MeasureTheory.Measure.real] at h
  simp only [Bop_apply]
  rw [abs_mul]
  exact mul_le_mul (le_trans (hgC _) (le_max_left _ _)) hInt (abs_nonneg _) (le_max_right _ _)

/-- Slotwise linearity of `Aop_i` over a finite sum of `Bop_j`, at a point of the box. -/
lemma Aop_finset_sum_at {M : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ acube a) {g : E3 → ℝ} (hgm : Measurable g) {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X M → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ u ∈ abox M a, |Ψ u| ≤ CΨ)
    (i : Fin M) {x : X M} (hx : x ∈ abox M a) :
    Aop A g i (∑ j : Fin M, Bop A g j Ψ) x
      = ∑ j : Fin M, Aop A g i (Bop A g j Ψ) x := by
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  have keymix : (fun z : E3 => g z * (∑ j : Fin M, Bop A g j Ψ) (Function.update x i z))
      = fun z : E3 => ∑ j : Fin M, g z * Bop A g j Ψ (Function.update x i z) := by
    funext z
    rw [Finset.sum_apply (M := fun _ : X M => ℝ) (Function.update x i z) Finset.univ
      (fun j : Fin M => Bop A g j Ψ), Finset.mul_sum]
  have key : (∫ z in A, g z * (∑ j : Fin M, Bop A g j Ψ) (Function.update x i z))
      = ∑ j : Fin M, ∫ z in A, g z * Bop A g j Ψ (Function.update x i z) := by
    rw [keymix, MeasureTheory.integral_finsetSum]
    intro j _
    refine MeasureTheory.IntegrableOn.of_bound hAfin ?_
      (max Cg 0 * (max Cg 0 * (max CΨ 0 * (volume A).toReal))) ?_
    · exact (hgm.mul ((measurable_Bop_restrict hAm hgm hΨm j).comp
        ((continuous_const : Continuous fun _ : E3 => x).update i continuous_id).measurable)).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' hAm]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : |Bop A g j Ψ (Function.update x i z)|
          ≤ max Cg 0 * (max CΨ 0 * (volume A).toReal) :=
        abs_Bop_le_restrict ha hAc hgC hΨb j _ (update_mem_abox_toolbox hAc hx i hz)
      exact mul_le_mul (le_trans (hgC z) (le_max_left _ _)) h2 (abs_nonneg _) (by positivity)
  simp only [Aop_apply]
  rw [key, Finset.mul_sum]

/-- Slotwise linearity of `Bop_i` over a finite sum of `Aop_j`, at a point of the box. -/
lemma Bop_finset_sum_at {M : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3} (hAm : MeasurableSet A)
    (hAc : A ⊆ acube a) {g : E3 → ℝ} (hgm : Measurable g) {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X M → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ u ∈ abox M a, |Ψ u| ≤ CΨ)
    (i : Fin M) {x : X M} (hx : x ∈ abox M a) :
    Bop A g i (∑ j : Fin M, Aop A g j Ψ) x
      = ∑ j : Fin M, Bop A g i (Aop A g j Ψ) x := by
  have hAfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top ha hAc
  have keymix : (fun z : E3 => (1 : ℝ) * (∑ j : Fin M, Aop A g j Ψ) (Function.update x i z))
      = fun z : E3 => ∑ j : Fin M, (1 : ℝ) * Aop A g j Ψ (Function.update x i z) := by
    funext z
    rw [Finset.sum_apply (M := fun _ : X M => ℝ) (Function.update x i z) Finset.univ
      (fun j : Fin M => Aop A g j Ψ), Finset.mul_sum]
  have key : (∫ z in A, (1 : ℝ) * (∑ j : Fin M, Aop A g j Ψ) (Function.update x i z))
      = ∑ j : Fin M, ∫ z in A, (1 : ℝ) * Aop A g j Ψ (Function.update x i z) := by
    rw [keymix, MeasureTheory.integral_finsetSum]
    intro j _
    refine MeasureTheory.IntegrableOn.of_bound hAfin ?_
      (max Cg 0 * (max CΨ 0 * (volume A).toReal)) ?_
    · exact (measurable_const.mul ((measurable_Aop_restrict hAm hgm hΨm j).comp
        ((continuous_const : Continuous fun _ : E3 => x).update i continuous_id).measurable)).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' hAm]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_one, one_mul]
      exact abs_Aop_le_restrict ha hAc hgC hΨb j _ (update_mem_abox_toolbox hAc hx i hz)
  simp only [Bop_apply]
  rw [key, Finset.mul_sum]

/-- The exact commutator identity `X(YΨ) − Y(XΨ) = (∫_A g²)·WΨ − volA·UΨ` at the box. -/
lemma boxOpG_commutator_restrict {N : ℕ} {a volA : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a)
    (hvol : volA = (volume A).toReal)
    {g : E3 → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ A → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X (N + 1) → ℝ} (hΨ : Continuous Ψ)
    {x : X (N + 1)} (hx : x ∈ abox (N + 1) a) :
    boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x
      - boxOpZ A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x
      = (∫ z in A, (g z) ^ 2) * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
        - volA * boxOpZ A g g Ψ x := by
  classical
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := exists_bound_abox_pos (N := N + 1) ha hΨ
  have hΨm : Measurable Ψ := hΨ.measurable
  have hInd : ∀ z, A.indicator (fun _ => (1 : ℝ)) z * g z = g z := fun z => by
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, one_mul]
    · rw [Set.indicator_of_notMem hz, zero_mul, hg0 z hz]
  -- ### the four sum expansions
  have e1 : boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x
      = ∑ i : Fin (N + 1), Aop A g i (∑ j : Fin (N + 1), Bop A g j Ψ) x := by
    have h : boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ)
        = ∑ i : Fin (N + 1), Aop A g i (∑ j : Fin (N + 1), Bop A g j Ψ) := by
      rw [boxOpG_g_one A g hInd Ψ, boxOpG_one_g A g (∑ j : Fin (N + 1), Bop A g j Ψ)]
    rw [h, Finset.sum_apply (M := fun _ : X (N + 1) => ℝ) x Finset.univ
      (fun i : Fin (N + 1) => Aop A g i (∑ j : Fin (N + 1), Bop A g j Ψ))]
  have e2 : boxOpZ A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x
      = ∑ i : Fin (N + 1), Bop A g i (∑ j : Fin (N + 1), Aop A g j Ψ) x := by
    have h : boxOpZ A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ)
        = ∑ i : Fin (N + 1), Bop A g i (∑ j : Fin (N + 1), Aop A g j Ψ) := by
      rw [boxOpG_one_g A g Ψ, boxOpZ_g_one A g (∑ j : Fin (N + 1), Aop A g j Ψ)]
    rw [h, Finset.sum_apply (M := fun _ : X (N + 1) => ℝ) x Finset.univ
      (fun i : Fin (N + 1) => Bop A g i (∑ j : Fin (N + 1), Aop A g j Ψ))]
  have hA : (∑ i : Fin (N + 1), Aop A g i (∑ j : Fin (N + 1), Bop A g j Ψ) x)
      = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Aop A g i (Bop A g j Ψ) x :=
    Finset.sum_congr rfl (fun i _ =>
      Aop_finset_sum_at ha hAm hAc hgm hgC hΨm hCΨ i hx)
  have hB : (∑ i : Fin (N + 1), Bop A g i (∑ j : Fin (N + 1), Aop A g j Ψ) x)
      = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Bop A g i (Aop A g j Ψ) x :=
    Finset.sum_congr rfl (fun i _ =>
      Bop_finset_sum_at ha hAm hAc hgm hgC hΨm hCΨ i hx)
  have hR : boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
      = ∑ i : Fin (N + 1), Dop A i Ψ x := by
    rw [congrFun (boxOpG_one_one A Ψ) x,
      Finset.sum_apply (M := fun _ : X (N + 1) => ℝ) x Finset.univ
        (fun i : Fin (N + 1) => Dop A i Ψ)]
  have hS : boxOpZ A g g Ψ x = ∑ i : Fin (N + 1), Cop A g i Ψ x := by
    rw [congrFun (boxOpZ_g_g A g Ψ) x,
      Finset.sum_apply (M := fun _ : X (N + 1) => ℝ) x Finset.univ
        (fun i : Fin (N + 1) => Cop A g i Ψ)]
  -- ### the off-diagonal cancellation
  have hsum : (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Aop A g i (Bop A g j Ψ) x)
      - (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Bop A g i (Aop A g j Ψ) x)
      = ∑ i : Fin (N + 1), (Aop A g i (Bop A g i Ψ) x - Bop A g i (Aop A g i Ψ) x) := by
    have hb' : (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Bop A g j (Aop A g i Ψ) x)
        = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Bop A g i (Aop A g j Ψ) x := by
      rw [Finset.sum_comm]
    rw [← hb', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hj
      rw [Aop_Bop_comm_restrict ha hAm hAc hgm hgC hΨ hj.symm hx]
      ring
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  -- ### the diagonal
  have hdiag : (∑ i : Fin (N + 1),
        (Aop A g i (Bop A g i Ψ) x - Bop A g i (Aop A g i Ψ) x))
      = (∫ z in A, (g z) ^ 2) * (∑ i : Fin (N + 1), Dop A i Ψ x)
        - (∫ z in A, (1 : ℝ)) * (∑ i : Fin (N + 1), Cop A g i Ψ x) := by
    have h1 : ∀ i : Fin (N + 1), Aop A g i (Bop A g i Ψ) x
        = (∫ z in A, (g z) ^ 2) * Dop A i Ψ x :=
      fun i => congrFun (Aop_Bop_self_restrict g Ψ i) x
    have h2 : ∀ i : Fin (N + 1), Bop A g i (Aop A g i Ψ) x
        = (∫ z in A, (1 : ℝ)) * Cop A g i Ψ x :=
      fun i => congrFun (Bop_Aop_self_restrict hAm g Ψ i) x
    rw [Finset.sum_congr rfl (fun i _ => by rw [h1 i, h2 i]), Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [e1, e2, hA, hB, hR, hS, hsum, hdiag]
  rw [show (∫ z in A, (1 : ℝ)) = volA from by
    rw [MeasureTheory.integral_const]
    show ((volume.restrict A) Set.univ).toReal * 1 = volA
    rw [MeasureTheory.Measure.restrict_apply_univ, ← hvol, mul_one]]

/-! ## 3. The sharp commutator bound `boxModeTGen − boxModePGen ≤ (∫_A g²)·S` -/

lemma boxTauGen_comm_diff_le_meas {N : ℕ} {a volA : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a)
    (hvol : volA = (volume A).toReal) (hvolpos : 0 < volA)
    {g : E3 → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ A → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    boxModeTGen a volA A g Ψ - boxModePGen a volA A g Ψ
      ≤ (∫ z in A, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a A Ψ := by
  have hΨm : Measurable Ψ := hΨ.measurable
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := exists_bound_abox_pos (N := N + 1) ha hΨ
  have hmX : Measurable (boxOpG A (fun _ => (1 : ℝ)) g Ψ) :=
    measurable_boxOpG_toolbox hAm measurable_const hgm hΨm
  have hmY : Measurable (boxOpG A g (fun _ => (1 : ℝ)) Ψ) :=
    measurable_boxOpG_toolbox hAm hgm measurable_const hΨm
  obtain ⟨CX, hCX0, hCX⟩ := abs_boxOpG_le_toolbox (f := fun _ => (1 : ℝ)) (h := g)
    ha hAm hAc measurable_const hgm (Cf := 1) (fun z => by norm_num) (Ch := Cg) hgC hΨm hCΨ
  obtain ⟨CY, hCY0, hCY⟩ := abs_boxOpG_le_toolbox (f := g) (h := fun _ => (1 : ℝ))
    ha hAm hAc hgm measurable_const (Cf := Cg) hgC (Ch := 1) (fun z => by norm_num) hΨm hCΨ
  have hmXY : Measurable (boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ)) :=
    measurable_boxOpG_toolbox hAm measurable_const hgm hmY
  have hmYX : Measurable (boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ)) :=
    measurable_boxOpG_toolbox hAm hgm measurable_const hmX
  obtain ⟨CXY, hCXY0, hCXY⟩ := abs_boxOpG_le_toolbox (f := fun _ => (1 : ℝ)) (h := g)
    ha hAm hAc measurable_const hgm (Cf := 1) (fun z => by norm_num) (Ch := Cg) hgC hmY hCY
  obtain ⟨CYX, hCYX0, hCYX⟩ := abs_boxOpG_le_toolbox (f := g) (h := fun _ => (1 : ℝ))
    ha hAm hAc hgm measurable_const (Cf := Cg) hgC (Ch := 1) (fun z => by norm_num) hmX hCX
  have hmW : Measurable (boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ) :=
    measurable_boxOpG_toolbox hAm measurable_const measurable_const hΨm
  have hmU : Measurable (boxOpZ A g g Ψ) := measurable_boxOpZ_toolbox hAm hgm hgm hΨm
  obtain ⟨CW, hCW0, hCW⟩ := abs_boxOpG_le_toolbox (f := fun _ => (1 : ℝ)) (h := fun _ => (1 : ℝ))
    ha hAm hAc measurable_const measurable_const (Cf := 1) (fun z => by norm_num)
    (Ch := 1) (fun z => by norm_num) hΨm hCΨ
  obtain ⟨CU, hCU0, hCU⟩ := abs_boxOpZ_le_toolbox ha hAm hAc hgm hgm hgC hgC hΨm hCΨ
  -- integrability of the four integrands on the box
  have hI1 : IntegrableOn (fun x : X (N + 1) =>
      Ψ x * boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x)
      (abox (N + 1) a) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound ha hΨm hmXY hCΨ hCXY
  have hI2 : IntegrableOn (fun x : X (N + 1) =>
      Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x)
      (abox (N + 1) a) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound ha hΨm hmYX hCΨ hCYX
  have hI3 : IntegrableOn (fun x : X (N + 1) =>
      Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x) (abox (N + 1) a) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound ha hΨm hmW hCΨ hCW
  have hI4 : IntegrableOn (fun x : X (N + 1) =>
      Ψ x * boxOpZ A g g Ψ x) (abox (N + 1) a) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound ha hΨm hmU hCΨ hCU
  -- ### the two adjointness identities (one-slot peel)
  have hQY : (∫ x in abox (N + 1) a, (boxOpG A g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
      = ∫ x in abox (N + 1) a,
          Ψ x * boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x := by
    have hadj : (∫ x in abox (N + 1) a,
          boxOpG A g (fun _ => (1 : ℝ)) Ψ x * boxOpG A g (fun _ => (1 : ℝ)) Ψ x)
        = ∫ x in abox (N + 1) a,
            boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x * Ψ x :=
      boxOpG_adjoint_one_meas (N := N) ha hAm hAc (f := g) hgm (Cf := Cg) hgC
        (Φ := boxOpG A g (fun _ => (1 : ℝ)) Ψ) (Ψ := Ψ) hmY hΨm hCY hCΨ
    rw [show (∫ x in abox (N + 1) a, (boxOpG A g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
        = ∫ x in abox (N + 1) a,
            boxOpG A g (fun _ => (1 : ℝ)) Ψ x * boxOpG A g (fun _ => (1 : ℝ)) Ψ x from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))]
    rw [hadj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have hQX : (∫ x in abox (N + 1) a, (boxOpG A (fun _ => (1 : ℝ)) g Ψ x) ^ 2)
      = ∫ x in abox (N + 1) a,
          Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x := by
    have hadj : (∫ x in abox (N + 1) a,
          Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x)
        = ∫ x in abox (N + 1) a,
            boxOpG A (fun _ => (1 : ℝ)) g Ψ x * boxOpG A (fun _ => (1 : ℝ)) g Ψ x :=
      boxOpG_adjoint_one_meas (N := N) ha hAm hAc (f := g) hgm (Cf := Cg) hgC
        (Φ := Ψ) (Ψ := boxOpG A (fun _ => (1 : ℝ)) g Ψ) hΨm hmX hCΨ hCX
    rw [hadj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- ### the exact commutator identity, integrated
  have hkey : (∫ x in abox (N + 1) a,
        Ψ x * boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x)
      - (∫ x in abox (N + 1) a,
        Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x)
      = (∫ z in A, (g z) ^ 2)
          * (∫ x in abox (N + 1) a,
              Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - volA * (∫ x in abox (N + 1) a, Ψ x * boxOpZ A g g Ψ x) := by
    have hcomm' : ∀ x ∈ abox (N + 1) a,
        boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x
          - boxOpZ A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x
        = (∫ z in A, (g z) ^ 2) * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
          - volA * boxOpZ A g g Ψ x := by
      intro x hx
      exact boxOpG_commutator_restrict ha hAm hAc hvol hgm hg0 hgC hΨ hx
    have hR : ((∫ z in A, (g z) ^ 2)
          * (∫ x in abox (N + 1) a,
              Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - volA * (∫ x in abox (N + 1) a, Ψ x * boxOpZ A g g Ψ x))
        = ∫ x in abox (N + 1) a, ((∫ z in A, (g z) ^ 2)
              * (Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
            - volA * (Ψ x * boxOpZ A g g Ψ x)) := by
      rw [MeasureTheory.integral_sub (hI3.const_mul _) (hI4.const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_sub hI1 hI2, hR]
    refine MeasureTheory.setIntegral_congr_fun (abox_measurable (N + 1) a) (fun x hx => ?_)
    show Ψ x * boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x
        - Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x
      = (∫ z in A, (g z) ^ 2) * (Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
        - volA * (Ψ x * boxOpZ A g g Ψ x)
    calc Ψ x * boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x
          - Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x
        = Ψ x * (boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x
            - boxOpZ A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x) := by
          rw [show boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x
              = boxOpZ A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x from
            (boxOpZ_g_one_eq_boxOpG_pointwise hg0 _ x).symm]
          ring
      _ = Ψ x * ((∫ z in A, (g z) ^ 2)
              * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x
            - volA * boxOpZ A g g Ψ x) := by rw [hcomm' x hx]
      _ = (∫ z in A, (g z) ^ 2)
              * (Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
            - volA * (Ψ x * boxOpZ A g g Ψ x) := by ring
  -- ### the flat count and the positivity
  have hflat := boxOpG_one_one_flatCount (N := N) ha hAm hAc hvol hvolpos hΨ
  have hU0 : 0 ≤ ∫ x in abox (N + 1) a, Ψ x * boxOpZ A g g Ψ x :=
    boxOpZ_gg_nonneg_meas (N := N) ha hAm hAc hgm hg0 hgC hΨ
  have hgnn : 0 ≤ ∫ z in A, (g z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hBsq : (Real.sqrt volA) ^ 2 = volA := Real.sq_sqrt hvolpos.le
  have h1vol : ((Real.sqrt volA) ^ 2)⁻¹ * volA = 1 := by
    rw [hBsq, inv_mul_cancel₀ (ne_of_gt hvolpos)]
  have hP : boxModePGen a volA A g Ψ
      = ((Real.sqrt volA) ^ 2)⁻¹
          * ∫ x in abox (N + 1) a, (boxOpG A (fun _ => (1 : ℝ)) g Ψ x) ^ 2 := by
    unfold boxModePGen
    rw [show (∫ x in abox (N + 1) a, (boxTauAnnGen volA A g Ψ x) ^ 2)
        = ∫ x in abox (N + 1) a,
            ((Real.sqrt volA) ^ 2)⁻¹ * (boxOpG A (fun _ => (1 : ℝ)) g Ψ x) ^ 2 from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        show boxTauAnnGen volA A g Ψ x ^ 2
          = ((Real.sqrt volA) ^ 2)⁻¹ * boxOpG A (fun _ => (1 : ℝ)) g Ψ x ^ 2
        rw [show boxTauAnnGen volA A g Ψ x
            = (Real.sqrt volA)⁻¹ * boxOpG A (fun _ => (1 : ℝ)) g Ψ x from
          congrFun (boxTauAnnGen_eq_boxOpG volA A g Ψ) x]
        rw [mul_pow, inv_pow]))]
    rw [MeasureTheory.integral_const_mul]
  have hT : boxModeTGen a volA A g Ψ
      = ((Real.sqrt volA) ^ 2)⁻¹
          * ∫ x in abox (N + 1) a, (boxOpG A g (fun _ => (1 : ℝ)) Ψ x) ^ 2 := by
    unfold boxModeTGen
    rw [show (∫ x in abox (N + 1) a, (boxTauDagGen volA A g Ψ x) ^ 2)
        = ∫ x in abox (N + 1) a,
            ((Real.sqrt volA) ^ 2)⁻¹ * (boxOpG A g (fun _ => (1 : ℝ)) Ψ x) ^ 2 from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        show boxTauDagGen volA A g Ψ x ^ 2
          = ((Real.sqrt volA) ^ 2)⁻¹ * boxOpG A g (fun _ => (1 : ℝ)) Ψ x ^ 2
        rw [show boxTauDagGen volA A g Ψ x
            = (Real.sqrt volA)⁻¹ * boxOpG A g (fun _ => (1 : ℝ)) Ψ x from
          congrFun (boxTauDagGen_eq_boxOpG volA A g Ψ) x]
        rw [mul_pow, inv_pow]))]
    rw [MeasureTheory.integral_const_mul]
  calc boxModeTGen a volA A g Ψ - boxModePGen a volA A g Ψ
      = ((Real.sqrt volA) ^ 2)⁻¹ *
          ((∫ x in abox (N + 1) a, (boxOpG A g (fun _ => (1 : ℝ)) Ψ x) ^ 2)
            - (∫ x in abox (N + 1) a, (boxOpG A (fun _ => (1 : ℝ)) g Ψ x) ^ 2)) := by
        rw [hT, hP]; ring
    _ = ((Real.sqrt volA) ^ 2)⁻¹ *
          ((∫ x in abox (N + 1) a,
              Ψ x * boxOpG A (fun _ => (1 : ℝ)) g (boxOpG A g (fun _ => (1 : ℝ)) Ψ) x)
            - (∫ x in abox (N + 1) a,
              Ψ x * boxOpG A g (fun _ => (1 : ℝ)) (boxOpG A (fun _ => (1 : ℝ)) g Ψ) x)) := by
        rw [hQY, hQX]
    _ = ((Real.sqrt volA) ^ 2)⁻¹ *
          ((∫ z in A, (g z) ^ 2)
              * (∫ x in abox (N + 1) a,
                  Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)
            - volA * (∫ x in abox (N + 1) a, Ψ x * boxOpZ A g g Ψ x)) := by
        rw [hkey]
    _ ≤ ((Real.sqrt volA) ^ 2)⁻¹ *
          ((∫ z in A, (g z) ^ 2)
            * (∫ x in abox (N + 1) a,
                Ψ x * boxOpG A (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) Ψ x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [hU0, hvolpos]
    _ = ((Real.sqrt volA) ^ 2)⁻¹ *
          ((∫ z in A, (g z) ^ 2) * (volA * Work.BoseFixB1S.boxFlatCount volA a A Ψ)) := by
        rw [hflat]
    _ = (∫ z in A, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a A Ψ := by
        rw [show ((Real.sqrt volA) ^ 2)⁻¹
              * ((∫ z in A, (g z) ^ 2) * (volA * Work.BoseFixB1S.boxFlatCount volA a A Ψ))
            = (((Real.sqrt volA) ^ 2)⁻¹ * volA)
              * ((∫ z in A, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a A Ψ) from by ring]
        rw [h1vol, one_mul]

/-! ## 4. Positivity of the Bogoliubov-transformed quadratic form -/

lemma boxTauGen_bog_pos_meas {N : ℕ} {a volA : ℝ} (ha : 0 < a)
    {A : Set E3} (hAm : MeasurableSet A) (hAc : A ⊆ acube a) (hvolpos : 0 < volA)
    {g : E3 → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ A → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X (N + 1) → ℝ} (hΨ : Continuous Ψ) (α : ℝ) :
    0 ≤ boxModePGen a volA A g Ψ + 2 * α * boxModeRGen a volA A g Ψ
        + α ^ 2 * boxModeTGen a volA A g Ψ := by
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := exists_bound_abox_pos (N := N + 1) ha hΨ
  have hΨm : Measurable Ψ := hΨ.measurable
  have hmX : Measurable (boxOpG A (fun _ => (1 : ℝ)) g Ψ) :=
    measurable_boxOpG_toolbox hAm measurable_const hgm hΨm
  have hmY : Measurable (boxOpG A g (fun _ => (1 : ℝ)) Ψ) :=
    measurable_boxOpG_toolbox hAm hgm measurable_const hΨm
  obtain ⟨CX, hCX0, hCX⟩ := abs_boxOpG_le_toolbox (f := fun _ => (1 : ℝ)) (h := g)
    ha hAm hAc measurable_const hgm (Cf := 1) (fun z => by norm_num) (Ch := Cg) hgC hΨm hCΨ
  obtain ⟨CY, hCY0, hCY⟩ := abs_boxOpG_le_toolbox (f := g) (h := fun _ => (1 : ℝ))
    ha hAm hAc hgm measurable_const (Cf := Cg) hgC (Ch := 1) (fun z => by norm_num) hΨm hCΨ
  have hmA : Measurable (boxTauAnnGen volA A g Ψ) := by
    rw [boxTauAnnGen_eq_boxOpG]
    exact hmX.const_mul _
  have hmD : Measurable (boxTauDagGen volA A g Ψ) := by
    rw [boxTauDagGen_eq_boxOpG]
    exact hmY.const_mul _
  have hbA : ∀ x ∈ abox (N + 1) a,
      |boxTauAnnGen volA A g Ψ x| ≤ |(Real.sqrt volA)⁻¹| * max CX 0 := by
    intro x hx
    rw [show boxTauAnnGen volA A g Ψ x
        = (Real.sqrt volA)⁻¹ * boxOpG A (fun _ => (1 : ℝ)) g Ψ x from
      congrFun (boxTauAnnGen_eq_boxOpG volA A g Ψ) x, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans (hCX x hx) (le_max_left _ _)) (abs_nonneg _)
  have hbD : ∀ x ∈ abox (N + 1) a,
      |boxTauDagGen volA A g Ψ x| ≤ |(Real.sqrt volA)⁻¹| * max CY 0 := by
    intro x hx
    rw [show boxTauDagGen volA A g Ψ x
        = (Real.sqrt volA)⁻¹ * boxOpG A g (fun _ => (1 : ℝ)) Ψ x from
      congrFun (boxTauDagGen_eq_boxOpG volA A g Ψ) x, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans (hCY x hx) (le_max_left _ _)) (abs_nonneg _)
  have h1 : boxModePGen a volA A g Ψ + 2 * α * boxModeRGen a volA A g Ψ
        + α ^ 2 * boxModeTGen a volA A g Ψ
      = ∫ x in abox (N + 1) a,
          (boxTauAnnGen volA A g Ψ x + α * boxTauDagGen volA A g Ψ x) ^ 2 := by
    rw [integral_sq_add_expand_meas ha hmA hmD hbA hbD α]
    unfold boxModePGen boxModeRGen boxModeTGen
    ring
  rw [h1]
  exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)

/-! ## 5. The `R`-content in terms of `boxOpG`, and a.e.-congruence of the `g`-slot -/

/-- The pairing content in terms of the box one-slot operators (definitional, no hypotheses). -/
lemma boxModeRGen_eq_boxOpG {N : ℕ} (a volA : ℝ) (A : Set E3) (g : E3 → ℝ)
    (Ψ : X (N + 1) → ℝ) :
    boxModeRGen a volA A g Ψ = ((Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹)
      * ∫ x in abox (N + 1) a,
          boxOpG A (fun _ => (1 : ℝ)) g Ψ x * boxOpG A g (fun _ => (1 : ℝ)) Ψ x := by
  unfold boxModeRGen
  rw [show (fun x => boxTauAnnGen volA A g Ψ x * boxTauDagGen volA A g Ψ x)
      = fun x => (Real.sqrt volA)⁻¹ * (Real.sqrt volA)⁻¹
          * (boxOpG A (fun _ => (1 : ℝ)) g Ψ x * boxOpG A g (fun _ => (1 : ℝ)) Ψ x) from by
    funext x
    rw [congrFun (boxTauAnnGen_eq_boxOpG volA A g Ψ) x,
      congrFun (boxTauDagGen_eq_boxOpG volA A g Ψ) x]
    ring]
  rw [MeasureTheory.integral_const_mul]

/-- The genuine box annihilation operator depends on `g` only through its a.e.-class on `A`. -/
lemma boxTauAnnGen_congr_ae {M : ℕ} {volA : ℝ} {A : Set E3} {g g' : E3 → ℝ}
    (hgg' : g =ᵐ[volume.restrict A] g') (Ψ : X M → ℝ) :
    boxTauAnnGen volA A g Ψ = boxTauAnnGen volA A g' Ψ := by
  funext x
  simp only [boxTauAnnGen]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact MeasureTheory.integral_congr_ae (hgg'.mono (fun z hz => by simp only [hz]))

/-- `boxOpG A 1 ·` depends on its `h`-slot function only through the a.e.-class on `A`. -/
lemma boxOpG_one_congr_ae {M : ℕ} {A : Set E3} {g g' : E3 → ℝ}
    (hgg' : g =ᵐ[volume.restrict A] g') (Φ : X M → ℝ) :
    boxOpG A (fun _ => (1 : ℝ)) g Φ = boxOpG A (fun _ => (1 : ℝ)) g' Φ := by
  funext x
  simp only [boxOpG, one_mul, mul_one]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact MeasureTheory.integral_congr_ae (hgg'.mono (fun z hz => by simp only [hz]))

/-! ## 6. The sharp per-mode Bogoliubov bound for measurable `g` -/

theorem boxTauGen_mode_bound_measurable {N : ℕ} {a Acoef B volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ acube a)
    (hvol : volA = (volume Ac).toReal) (hvolpos : 0 < volA)
    {g : E3 → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ Ac → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : X (N + 1) → ℝ} (hΨ : Continuous Ψ)
    (hA : 0 < Acoef) (hB : |B| ≤ Acoef) :
    - ((Acoef - Real.sqrt (Acoef ^ 2 - B ^ 2)) / 2) *
        ((∫ z in Ac, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a Ac Ψ)
      ≤ Acoef * boxModePGen a volA Ac g Ψ + B * boxModeRGen a volA Ac g Ψ := by
  have hTP := boxTauGen_comm_diff_le_meas (N := N) ha hAcm hAcsub hvol hvolpos hgm hg0 hgC hΨ
  have hU := boxTauGen_bog_pos_meas (N := N) ha hAcm hAcsub hvolpos hgm hg0 hgC hΨ
    (B / (Acoef + Real.sqrt (Acoef ^ 2 - B ^ 2)))
  have hc0 : 0 ≤ (∫ z in Ac, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a Ac Ψ := by
    have h1 : 0 ≤ ∫ z in Ac, (g z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
    have h2 : 0 ≤ Work.BoseFixB1S.boxFlatCount volA a Ac Ψ := by
      rw [Work.BoseFixB1S.boxFlatCount]
      exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    exact mul_nonneg h1 h2
  exact bogoliubov_one_mode (α := Acoef) (β := B) (P := boxModePGen a volA Ac g Ψ)
    (R := boxModeRGen a volA Ac g Ψ) (T := boxModeTGen a volA Ac g Ψ)
    (c := (∫ z in Ac, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a Ac Ψ)
    hA hB hc0 hTP hU

/-! ## 7. The target: an a.e. measurable mode function

Given an `AEMeasurable` `g` with `tsupport g ⊆ Ac`, replace it by the measurable
`g' = 1_{Ac}·clamp(g₀)` (with `g₀ = hgm.mk g`), which agrees with `g` a.e. on `Ac`, is bounded by
`max Cg 0` and vanishes off `Ac`.  Every quantity in the conclusion is an integral over `Ac` of
`g`:

* `∫_Ac g²` and `boxModePGen` (whose `g`-dependence is only through the fibre integral
  `∫_Ac g z·Ψ(x|i↦z) dz`) are unchanged *pointwise*;
* `boxModeRGen` is unchanged by the peel lemma `integral_boxOpG_f_congr_ae` (its `g`-dependence
  sits in the `f`-slot of `boxOpG A g 1`, i.e. in the pointwise factor `g(x_i)`, which after the
  one-slot peel only sees `g` through `∫_Ac`).
-/

theorem boxTauGen_mode_bound_meas {N : ℕ} {a Acoef B volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : AEMeasurable g)
    (hgsupp : tsupport g ⊆ Ac) {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ)
    (hA : 0 < Acoef) (hB : |B| ≤ Acoef) :
    - ((Acoef - Real.sqrt (Acoef ^ 2 - B ^ 2)) / 2) *
        ((∫ z in Ac, (g z) ^ 2) * Work.BoseFixB1S.boxFlatCount volA a Ac Ψ)
      ≤ Acoef * Work.BoseFixB1.boxModePGen a volA Ac g Ψ
        + B * Work.BoseFixB1.boxModeRGen a volA Ac g Ψ := by
  have hg0 : ∀ z, z ∉ Ac → g z = 0 := eq_zero_of_tsupport_subset hgsupp
  by_cases hCg : 0 ≤ Cg
  · set g₀ : E3 → ℝ := hgm.mk g with hg₀def
    have hg₀m : Measurable g₀ := by rw [hg₀def]; exact hgm.measurable_mk
    have hg₀ae : g₀ =ᵐ[(volume : Measure E3)] g := by
      rw [hg₀def]; exact hgm.ae_eq_mk.symm
    set g' : E3 → ℝ := fun z => Ac.indicator (fun z => max (-Cg) (min (g₀ z) Cg)) z with hg'def
    have hg'm : Measurable g' := by
      rw [hg'def]
      exact (measurable_const.max (hg₀m.min measurable_const)).indicator hAcm
    have hg'0 : ∀ z, z ∉ Ac → g' z = 0 := fun z hz => by
      simp only [hg'def, Set.indicator_of_notMem hz]
    have hg'C : ∀ z, |g' z| ≤ max Cg 0 := by
      intro z
      simp only [hg'def]
      by_cases hz : z ∈ Ac
      · rw [Set.indicator_of_mem hz, abs_le]
        constructor
        · have h3 : -max Cg 0 ≤ -Cg := by
            have : Cg ≤ max Cg 0 := le_max_left _ _
            linarith
          linarith [le_max_left (-Cg) (min (g₀ z) Cg)]
        · have h2 : max (-Cg) (min (g₀ z) Cg) ≤ Cg :=
            max_le (by linarith) (min_le_right _ _)
          exact le_trans h2 (le_max_left Cg 0)
      · rw [Set.indicator_of_notMem hz, abs_zero]
        exact le_max_right _ _
    have hgg' : g' =ᵐ[volume.restrict Ac] g := by
      have h1 : ∀ᵐ z ∂(volume.restrict Ac), g₀ z = g z := ae_restrict_of_ae hg₀ae
      filter_upwards [h1] with z hz0
      by_cases hz : z ∈ Ac
      · simp only [hg'def, Set.indicator_of_mem hz, hz0]
        have hzC : |g z| ≤ Cg := hgC z
        rw [abs_le] at hzC
        rw [min_eq_left hzC.2, max_eq_right hzC.1]
      · simp only [hg'def, Set.indicator_of_notMem hz, hg0 z hz]
    have hcore := boxTauGen_mode_bound_measurable (N := N) ha hAcm hAcsub hvol hvolpos hg'm
      hg'0 (Cg := max Cg 0) hg'C hΨ hA hB
    have hc_eq : (∫ z in Ac, (g z) ^ 2) = ∫ z in Ac, (g' z) ^ 2 := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hgg'] with z hz
      show (g z) ^ 2 = (g' z) ^ 2
      rw [hz]
    have hP_eq : boxModePGen a volA Ac g Ψ = boxModePGen a volA Ac g' Ψ := by
      unfold boxModePGen
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      show (boxTauAnnGen volA Ac g Ψ x) ^ 2 = (boxTauAnnGen volA Ac g' Ψ x) ^ 2
      rw [show boxTauAnnGen volA Ac g Ψ x = boxTauAnnGen volA Ac g' Ψ x from
        congrFun (boxTauAnnGen_congr_ae hgg'.symm Ψ) x]
    have hR_eq : boxModeRGen a volA Ac g Ψ = boxModeRGen a volA Ac g' Ψ := by
      rw [boxModeRGen_eq_boxOpG, boxModeRGen_eq_boxOpG]
      congr 1
      obtain ⟨CΨ, hCΨ0, hCΨ⟩ := exists_bound_abox_pos (N := N + 1) ha hΨ
      have hΦm : Measurable (boxOpG Ac (fun _ => (1 : ℝ)) g' Ψ) :=
        measurable_boxOpG_toolbox hAcm measurable_const hg'm hΨ.measurable
      obtain ⟨CΦ, hCΦ0, hCΦ⟩ := abs_boxOpG_le_toolbox (f := fun _ => (1 : ℝ)) (h := g')
        ha hAcm hAcsub measurable_const hg'm (Cf := 1) (fun z => by norm_num)
        (Ch := max Cg 0) hg'C hΨ.measurable hCΨ
      rw [show (∫ x in abox (N + 1) a,
            boxOpG Ac (fun _ => (1 : ℝ)) g Ψ x * boxOpG Ac g (fun _ => (1 : ℝ)) Ψ x)
          = ∫ x in abox (N + 1) a,
            boxOpG Ac (fun _ => (1 : ℝ)) g' Ψ x * boxOpG Ac g (fun _ => (1 : ℝ)) Ψ x from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
          show boxOpG Ac (fun _ => (1 : ℝ)) g Ψ x * boxOpG Ac g (fun _ => (1 : ℝ)) Ψ x
              = boxOpG Ac (fun _ => (1 : ℝ)) g' Ψ x * boxOpG Ac g (fun _ => (1 : ℝ)) Ψ x
          rw [show boxOpG Ac (fun _ => (1 : ℝ)) g Ψ x
              = boxOpG Ac (fun _ => (1 : ℝ)) g' Ψ x from
            congrFun (boxOpG_one_congr_ae hgg'.symm Ψ) x]))]
      exact integral_boxOpG_f_congr_ae (Cg := max Cg 0) ha hAcm hAcsub hgm hg'm hgg'.symm
        (fun z => le_trans (hgC z) (le_max_left Cg 0)) hg'C hΦm hΨ.measurable hCΦ hCΨ
    rw [hc_eq, hP_eq, hR_eq]
    exact hcore
  · have h1 : |g 0| ≤ Cg := hgC 0
    have h2 : 0 ≤ |g 0| := abs_nonneg _
    linarith

end Work.BoseFixB1
