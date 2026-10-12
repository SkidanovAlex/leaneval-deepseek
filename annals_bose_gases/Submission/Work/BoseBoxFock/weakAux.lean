import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.sectorXSpow_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Weak` — the slot-mean algebra for measurable, bounded states

The corpus's slot-mean API (`Submission.BoseGases.aP`, `aQ` and their algebra: `aP_idem`,
`aP_comm`, `aP_sym_box`, `aP_add`, …) is stated for **continuous** states, because continuity
supplies the integrability of every fibre integral occurring in the definitions.  The state class
of the box ↔ model bridge (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`,
`FINDING_stateClass_RESOLVED_s17.md` §1.2) only provides **measurable, everywhere bounded**
states (the box restriction `Φ·1_abox` of a smooth state is discontinuous), so a twin of that
algebra in the measurable/bounded class is needed.

The hypotheses are

* `hΦm : Measurable Φ`, and
* `hΦb : ∀ x, |Φ x| ≤ C` (**global**, i.e. on all of `Ω^N`, not only on the box: the fibre
  integrals `y ↦ Φ (update x i y)` with `x` outside the box need it),

and `0 ≤ C` whenever a bound is *concluded*.

Two facts are hypothesis-free because they are pointwise rewrites of the defining integrals
(`Function.update_idem` and `integral_const_acube`):

* `aP_idem`     — `Pᵢ(PᵢΦ) = PᵢΦ`;
* `aP_const_in_coord` — `PᵢΦ` does not depend on the `i`-th coordinate;

and `aP_abs_le` is `sectorXSpow_decomp_aP_abs_le` of the sibling module (a global sup-norm
contraction, used for the boundedness of the iterated slot operators).  Everything else is Fubini
for bounded measurable functions on the finite measure space `acube ℓ` (resp. `abox N ℓ`).

The naming convention mirrors the corpus: the statements in this namespace are the weak twins of
`Submission.BoseGases.aP_idem`, `…aP_comm`, `…aP_sym_box`, `…`, referred to as `Weak.aP_idem` etc.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock
namespace Weak

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-! ## 0. The truncated measures are finite -/

theorem acube_isFiniteMeasure {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IsFiniteMeasure ((volume : Measure Sp).restrict (acube ℓ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ⟩

theorem abox_isFiniteMeasure (n : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ⟩

/-! ## 1. Measurability and boundedness -/

/-- The slot mean of a measurable state is measurable (a Bochner integral, in the averaged slot,
of a jointly strongly measurable function). -/
theorem aP_measurable {n : ℕ} {ℓ : ℝ} (i : Fin n) {Φ : X n → ℝ} (hΦm : Measurable Φ) :
    Measurable (aP ℓ i Φ) := by
  unfold aP
  refine Measurable.const_mul ?_ _
  have huncurry : StronglyMeasurable
      (fun p : X n × Sp => Φ (Function.update p.1 i p.2)) :=
    (hΦm.comp (by fun_prop : Measurable fun p : X n × Sp =>
      Function.update p.1 i p.2)).stronglyMeasurable
  haveI : SFinite ((volume : Measure Sp).restrict (acube ℓ)) := inferInstance
  have h := huncurry.integral_prod_right' (ν := (volume : Measure Sp).restrict (acube ℓ))
  simpa using h.measurable

/-- The complementary slot of a measurable state is measurable. -/
theorem aQ_measurable {n : ℕ} {ℓ : ℝ} (i : Fin n) {Φ : X n → ℝ} (hΦm : Measurable Φ) :
    Measurable (aQ ℓ i Φ) := by
  unfold aQ
  exact hΦm.sub (aP_measurable i hΦm)

/-- **The slot mean is a sup-norm contraction on all of `Ω^N`** (a global bound propagates, not
only a bound on the box: the fibre of a point outside the box is averaged over the cube). -/
theorem aP_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦb : ∀ x, |Φ x| ≤ C) : ∀ x, |aP ℓ i Φ x| ≤ C :=
  sectorXSpow_decomp_aP_abs_le (ℓ := ℓ) hℓ i hC hΦb

/-- The complementary slot is bounded by twice the bound of the state. -/
theorem aQ_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦb : ∀ x, |Φ x| ≤ C) : ∀ x, |aQ ℓ i Φ x| ≤ 2 * C := by
  intro x
  have hP : |aP ℓ i Φ x| ≤ C := aP_abs_le hℓ i hC hΦb x
  exact le_trans (abs_sub _ _) (by linarith [hΦb x, hP, hC])

/-- The fibre `y ↦ Φ (x[i ↦ y])` of a measurable bounded state is integrable on the cube. -/
theorem integrable_comp_update {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (x : X n) :
    Integrable (fun y : Sp => Φ (Function.update x i y))
      ((volume : Measure Sp).restrict (acube ℓ)) := by
  haveI := acube_isFiniteMeasure hℓ.le
  refine Integrable.of_bound ?_ C ?_
  · exact (hΦm.comp (by fun_prop : Measurable fun y : Sp =>
      Function.update x i y)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΦb _

/-! ## 2. Idempotence and slot-independence (hypothesis-free) -/

/-- **Idempotence of the slot mean**, for an *arbitrary* state (the two defining integrals have
literally the same integrand by `Function.update_idem`). -/
theorem aP_idem_fun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) (Φ : X n → ℝ) :
    aP ℓ i (aP ℓ i Φ) = aP ℓ i Φ := by
  funext x
  have hconst : (fun y : Sp => aP ℓ i Φ (Function.update x i y)) = fun _ => aP ℓ i Φ x := by
    funext y
    unfold aP
    congr 2
    funext z
    rw [Function.update_idem]
  rw [aP, hconst, integral_const_acube ℓ hℓ]
  field_simp [ne_of_gt hℓ]

/-- Idempotence of the slot mean, pointwise. -/
theorem aP_idem {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) (Φ : X n → ℝ) (x : X n) :
    aP ℓ i (aP ℓ i Φ) x = aP ℓ i Φ x :=
  congrFun (aP_idem_fun hℓ i Φ) x

/-- The slot mean `aP ℓ i Φ` does not depend on the `i`-th coordinate (for an *arbitrary* state:
the two defining integrals have the same integrand). -/
theorem aP_const_in_coord {n : ℕ} {ℓ : ℝ} (i : Fin n) (Φ : X n → ℝ) (x : X n) (z : Sp) :
    aP ℓ i Φ (Function.update x i z) = aP ℓ i Φ x := by
  unfold aP
  congr 2
  funext y
  rw [Function.update_idem]

/-! ## 3. Fubini algebra -/

/-- **The slot means of distinct slots commute** (Fubini for a bounded measurable state). -/
theorem aP_comm {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (x : X n) :
    aP ℓ i (aP ℓ j Φ) x = aP ℓ j (aP ℓ i Φ) x := by
  let μ' : Measure Sp := (volume : Measure Sp).restrict (acube ℓ)
  let G : Sp → Sp → ℝ := fun y z => Φ (Function.update (Function.update x i y) j z)
  have hGsymm : ∀ y z : Sp, G y z = Φ (Function.update (Function.update x j z) i y) := by
    intro y z
    dsimp only [G]
    congr 1
    rw [Function.update_comm hij]
  haveI : IsFiniteMeasure μ' := acube_isFiniteMeasure hℓ.le
  haveI : IsFiniteMeasure (μ'.prod μ') := inferInstance
  have hGm : AEStronglyMeasurable (Function.uncurry G) (μ'.prod μ') := by
    have hcont : Continuous
        (fun p : Sp × Sp => Function.update (Function.update x i p.1) j p.2) := by fun_prop
    exact (hΦm.comp hcont.measurable).aestronglyMeasurable
  have hGbdd : ∀ᵐ p ∂(μ'.prod μ'), ‖Function.uncurry G p‖ ≤ C := by
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hΦb _
  have hGint : Integrable (Function.uncurry G) (μ'.prod μ') := Integrable.of_bound hGm C hGbdd
  have hswap : (∫ y : Sp, ∫ z : Sp, G y z ∂μ' ∂μ') = ∫ z : Sp, ∫ y : Sp, G y z ∂μ' ∂μ' :=
    integral_integral_swap hGint
  have hL : aP ℓ i (aP ℓ j Φ) x
      = (1 / ℓ ^ 3) * ((1 / ℓ ^ 3) * ∫ y in acube ℓ, ∫ z in acube ℓ, G y z) := by
    simp only [aP]
    rw [MeasureTheory.integral_const_mul]
  have hfun_eq : (fun z : Sp => ∫ y in acube ℓ,
        Φ (Function.update (Function.update x j z) i y))
      = fun z : Sp => ∫ y in acube ℓ, G y z := by
    funext z
    refine integral_congr_ae ?_
    filter_upwards with y
    exact (hGsymm y z).symm
  have hR : aP ℓ j (aP ℓ i Φ) x
      = (1 / ℓ ^ 3) * ((1 / ℓ ^ 3) * ∫ z in acube ℓ, ∫ y in acube ℓ, G y z) := by
    simp only [aP]
    rw [MeasureTheory.integral_const_mul, hfun_eq]
  rw [hL, hR, hswap]

/-- The slot means of distinct slots commute, as an identity of functions. -/
theorem aP_comm_fun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) :
    aP ℓ i (aP ℓ j Φ) = aP ℓ j (aP ℓ i Φ) :=
  funext fun x => aP_comm hℓ hij hC hΦm hΦb x

/-- The slot mean is additive over a pair of measurable bounded states. -/
theorem aP_add {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ Ψ : X n → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) (x : X n) :
    aP ℓ i (Φ + Ψ) x = aP ℓ i Φ x + aP ℓ i Ψ x := by
  have h1 := integrable_comp_update hℓ i hC hΦm hΦb x
  have h2 := integrable_comp_update hℓ i hD hΨm hΨb x
  simp only [aP]
  rw [show (fun y : Sp => (Φ + Ψ) (Function.update x i y))
      = fun y : Sp => Φ (Function.update x i y) + Ψ (Function.update x i y) from rfl,
    MeasureTheory.integral_add h1 h2]
  ring

/-- The slot mean is additive over a difference of measurable bounded states. -/
theorem aP_sub {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ Ψ : X n → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) (x : X n) :
    aP ℓ i (Φ - Ψ) x = aP ℓ i Φ x - aP ℓ i Ψ x := by
  have h1 := integrable_comp_update hℓ i hC hΦm hΦb x
  have h2 := integrable_comp_update hℓ i hD hΨm hΨb x
  simp only [aP]
  rw [show (fun y : Sp => (Φ - Ψ) (Function.update x i y))
      = fun y : Sp => Φ (Function.update x i y) - Ψ (Function.update x i y) from rfl,
    MeasureTheory.integral_sub h1 h2]
  ring

/-- `Pᵢ (Qᵢ Φ) = 0` for a measurable bounded state. -/
theorem aP_aQ_self_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) :
    aP ℓ i (aQ ℓ i Φ) = 0 := by
  have hPm : Measurable (aP ℓ i Φ) := aP_measurable i hΦm
  have hPb : ∀ x, |aP ℓ i Φ x| ≤ C := aP_abs_le hℓ i hC hΦb
  funext x
  rw [show aQ ℓ i Φ = Φ - aP ℓ i Φ from rfl, aP_sub hℓ i hC hC hΦm hΦb hPm hPb x,
    aP_idem hℓ i Φ x, Pi.zero_apply]
  ring

/-- `Pᵢ` commutes with `Qⱼ` on distinct slots, for a measurable bounded state. -/
theorem aP_aQ_comm {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (x : X n) :
    aP ℓ i (aQ ℓ j Φ) x = aQ ℓ j (aP ℓ i Φ) x := by
  have hPm : Measurable (aP ℓ j Φ) := aP_measurable j hΦm
  have hPb : ∀ x, |aP ℓ j Φ x| ≤ C := aP_abs_le hℓ j hC hΦb
  rw [show aQ ℓ j Φ = Φ - aP ℓ j Φ from rfl, aP_sub hℓ i hC hC hΦm hΦb hPm hPb x,
    aP_comm hℓ hij hC hΦm hΦb x]
  rfl

/-- `Pᵢ` commutes with `Qⱼ` on distinct slots, as an identity of functions. -/
theorem aP_aQ_comm_fun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) :
    aP ℓ i (aQ ℓ j Φ) = aQ ℓ j (aP ℓ i Φ) :=
  funext fun x => aP_aQ_comm hℓ hij hC hΦm hΦb x

/-- `Qᵢ` and `Qⱼ` commute on distinct slots, for a measurable bounded state. -/
theorem aQ_comm_fun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) :
    aQ ℓ i (aQ ℓ j Φ) = aQ ℓ j (aQ ℓ i Φ) := by
  have hPim : Measurable (aP ℓ i Φ) := aP_measurable i hΦm
  have hPib : ∀ x, |aP ℓ i Φ x| ≤ C := aP_abs_le hℓ i hC hΦb
  have hPjm : Measurable (aP ℓ j Φ) := aP_measurable j hΦm
  have hPjb : ∀ x, |aP ℓ j Φ x| ≤ C := aP_abs_le hℓ j hC hΦb
  have h1 : aQ ℓ i (aQ ℓ j Φ) = (Φ - aP ℓ j Φ) - (aP ℓ i Φ - aP ℓ j (aP ℓ i Φ)) := by
    rw [show aQ ℓ i (aQ ℓ j Φ) = aQ ℓ j Φ - aP ℓ i (aQ ℓ j Φ) from rfl,
      aP_aQ_comm_fun hℓ hij hC hΦm hΦb,
      show aQ ℓ j Φ = Φ - aP ℓ j Φ from rfl,
      show aQ ℓ j (aP ℓ i Φ) = aP ℓ i Φ - aP ℓ j (aP ℓ i Φ) from rfl]
  have h2 : aQ ℓ j (aQ ℓ i Φ) = (Φ - aP ℓ i Φ) - (aP ℓ j Φ - aP ℓ i (aP ℓ j Φ)) := by
    rw [show aQ ℓ j (aQ ℓ i Φ) = aQ ℓ i Φ - aP ℓ j (aQ ℓ i Φ) from rfl,
      aP_aQ_comm_fun hℓ hij.symm hC hΦm hΦb,
      show aQ ℓ i Φ = Φ - aP ℓ i Φ from rfl,
      show aQ ℓ i (aP ℓ j Φ) = aP ℓ j Φ - aP ℓ i (aP ℓ j Φ) from rfl]
  rw [h1, h2, show aP ℓ j (aP ℓ i Φ) = aP ℓ i (aP ℓ j Φ) from
    (aP_comm_fun hℓ hij hC hΦm hΦb).symm]
  ring

/-- `Qᵢ` and `Qⱼ` commute on distinct slots, pointwise. -/
theorem aQ_comm {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (x : X n) :
    aQ ℓ i (aQ ℓ j Φ) x = aQ ℓ j (aQ ℓ i Φ) x :=
  congrFun (aQ_comm_fun hℓ hij hC hΦm hΦb) x

/-! ## 4. Self-adjointness over the box -/

/-- **`Pᵢ` is self-adjoint over the box** for measurable bounded states: both sides are the same
iterated integral over `abox × acube`, in the two orders. -/
theorem aP_sym_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ Ψ : X n → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) :
    (∫ x in abox n ℓ, (aP ℓ i Φ x) * Ψ x) = ∫ x in abox n ℓ, Φ x * (aP ℓ i Ψ x) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    haveI : IsFiniteMeasure ((volume : Measure Sp).restrict (acube ℓ)) :=
      acube_isFiniteMeasure hℓ.le
    have hPΦm : Measurable (aP ℓ i Φ) := aP_measurable i hΦm
    have hPΦb : ∀ x, |aP ℓ i Φ x| ≤ C := aP_abs_le hℓ i hC hΦb
    have hPΨm : Measurable (aP ℓ i Ψ) := aP_measurable i hΨm
    have hPΨb : ∀ x, |aP ℓ i Ψ x| ≤ D := aP_abs_le hℓ i hD hΨb
    have hInt1 : IntegrableOn (fun x : X (n + 1) => Ψ x * aP ℓ i Φ x) (abox (n + 1) ℓ) volume :=
      IntegrableOn.of_bound (s := abox (n + 1) ℓ) (abox_lt_top (n + 1) ℓ hℓ.le)
        ((hΨm.aestronglyMeasurable.restrict).mul
          hPΦm.aestronglyMeasurable.restrict) (D * C) (by
          filter_upwards with x
          simp only [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hΨb x) (hPΦb x) (abs_nonneg _) (le_trans (abs_nonneg _) (hΨb x)))
    have hInt2 : IntegrableOn (fun x : X (n + 1) => Φ x * aP ℓ i Ψ x) (abox (n + 1) ℓ) volume :=
      IntegrableOn.of_bound (s := abox (n + 1) ℓ) (abox_lt_top (n + 1) ℓ hℓ.le)
        ((hΦm.aestronglyMeasurable.restrict).mul
          hPΨm.aestronglyMeasurable.restrict) (C * D) (by
          filter_upwards with x
          simp only [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hΦb x) (hPΨb x) (abs_nonneg _) (le_trans (abs_nonneg _) (hΦb x)))
    have hP1 := abox_integral_peel (i := i) (F := fun x : X (n + 1) => Ψ x * aP ℓ i Φ x) hInt1
    have hP2 := abox_integral_peel (i := i) (F := fun x : X (n + 1) => Φ x * aP ℓ i Ψ x) hInt2
    have hpoint : ∀ r : X n,
        (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
          = ∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r)) := by
      intro r
      have hL : (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
          = (1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))
              * (∫ y in acube ℓ, Ψ (kcInsN n i (y, r))) := by
        simp only [aP_kcInsN]
        rw [MeasureTheory.integral_mul_const]
        ring
      have hR : (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r)))
          = (1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))
              * (∫ y in acube ℓ, Ψ (kcInsN n i (y, r))) := by
        simp only [aP_kcInsN]
        rw [MeasureTheory.integral_mul_const]
        ring
      rw [hL, hR]
    calc (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) * Ψ x)
        = ∫ x in abox (n + 1) ℓ, Ψ x * aP ℓ i Φ x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = ∫ r : X n, (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := hP1
      _ = ∫ r : X n, (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r)))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
          refine integral_congr_ae ?_
          filter_upwards with r
          exact hpoint r
      _ = ∫ x in abox (n + 1) ℓ, Φ x * (aP ℓ i Ψ x) := hP2.symm

/-- **`Qᵢ` is self-adjoint over the box** (it is `1 - Pᵢ`). -/
theorem aQ_sym_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ Ψ : X n → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) :
    (∫ x in abox n ℓ, (aQ ℓ i Φ x) * Ψ x) = ∫ x in abox n ℓ, Φ x * (aQ ℓ i Ψ x) := by
  have hPΦm : Measurable (aP ℓ i Φ) := aP_measurable i hΦm
  have hPΦb : ∀ x, |aP ℓ i Φ x| ≤ C := aP_abs_le hℓ i hC hΦb
  have hPΨm : Measurable (aP ℓ i Ψ) := aP_measurable i hΨm
  have hPΨb : ∀ x, |aP ℓ i Ψ x| ≤ D := aP_abs_le hℓ i hD hΨb
  have hI1 : IntegrableOn (fun x : X n => Φ x * Ψ x) (abox n ℓ) volume :=
    IntegrableOn.of_bound (s := abox n ℓ) (abox_lt_top n ℓ hℓ.le) ((hΦm.aestronglyMeasurable.restrict).mul
      hΨm.aestronglyMeasurable.restrict) (C * D) (by
        filter_upwards with x
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hΦb x) (hΨb x) (abs_nonneg _) (le_trans (abs_nonneg _) (hΦb x)))
  have hI2 : IntegrableOn (fun x : X n => aP ℓ i Φ x * Ψ x) (abox n ℓ) volume :=
    IntegrableOn.of_bound (s := abox n ℓ) (abox_lt_top n ℓ hℓ.le) ((hPΦm.aestronglyMeasurable.restrict).mul
      hΨm.aestronglyMeasurable.restrict) (C * D) (by
        filter_upwards with x
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hPΦb x) (hΨb x) (abs_nonneg _) (le_trans (abs_nonneg _) (hPΦb x)))
  have hI3 : IntegrableOn (fun x : X n => Φ x * aP ℓ i Ψ x) (abox n ℓ) volume :=
    IntegrableOn.of_bound (s := abox n ℓ) (abox_lt_top n ℓ hℓ.le) ((hΦm.aestronglyMeasurable.restrict).mul
      hPΨm.aestronglyMeasurable.restrict) (C * D) (by
        filter_upwards with x
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hΦb x) (hPΨb x) (abs_nonneg _) (le_trans (abs_nonneg _) (hΦb x)))
  have hfun : (fun x : X n => aQ ℓ i Φ x * Ψ x)
      = fun x : X n => Φ x * Ψ x - aP ℓ i Φ x * Ψ x := by
    funext x
    rw [show aQ ℓ i Φ x = Φ x - aP ℓ i Φ x from rfl]
    ring
  have hfun2 : (fun x : X n => Φ x * aQ ℓ i Ψ x)
      = fun x : X n => Φ x * Ψ x - Φ x * aP ℓ i Ψ x := by
    funext x
    rw [show aQ ℓ i Ψ x = Ψ x - aP ℓ i Ψ x from rfl]
    ring
  rw [hfun, hfun2, MeasureTheory.integral_sub hI1 hI2, MeasureTheory.integral_sub hI1 hI3,
    aP_sym_box hℓ i hC hD hΦm hΦb hΨm hΨb]

/-! ## 5. Linearity over a finite sum -/

/-- The slot mean is linear over a finite sum of measurable bounded states with nonnegative
coefficients. -/
theorem aP_finset_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (f : ι → X n → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ W ∈ s, 0 ≤ c W) (hfm : ∀ W ∈ s, Measurable (f W))
    (hfb : ∀ W ∈ s, ∀ x, |f W x| ≤ C) (x : X n) :
    aP ℓ i (fun y => ∑ W ∈ s, c W * f W y) x = ∑ W ∈ s, c W * aP ℓ i (f W) x := by
  haveI := acube_isFiniteMeasure hℓ.le
  have hbdd : ∀ W ∈ s, ∀ᵐ y ∂((volume : Measure Sp).restrict (acube ℓ)),
      ‖c W * f W (Function.update x i y)‖ ≤ c W * C := by
    intro W hW
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc W hW)]
    exact mul_le_mul_of_nonneg_left (hfb W hW _) (hc W hW)
  have hInt : ∀ W ∈ s, Integrable (fun y : Sp => c W * f W (Function.update x i y))
      ((volume : Measure Sp).restrict (acube ℓ)) := fun W hW =>
    Integrable.of_bound (measurable_const.mul ((hfm W hW).comp (by fun_prop))).aestronglyMeasurable
      (c W * C) (hbdd W hW)
  simp only [aP]
  rw [MeasureTheory.integral_finsetSum _ hInt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [MeasureTheory.integral_const_mul]
  ring

end Weak
end Work.BoseBoxFock
