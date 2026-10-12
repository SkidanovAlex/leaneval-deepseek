import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiLinearAux
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_pairSlot_split`

The `Q₁` χ-row pair slot form `pairSlot` (`Submission/Work/BoseBoxFock/chiRowDefs.lean`) is the
`n₀`-sandwich `⟨Φ, (n₀ X_w + X_w† n₀) Φ⟩` of the pair field, written as the sum of its two
orientations

    `pairHalfOne ℓ w Φ = ⟨Φ, n₀ X_w Φ⟩`,   `pairHalfTwo ℓ w Φ = ⟨Φ, X_w† n₀ Φ⟩` .

This module proves the two structural facts the χ-row assembly uses:

* `pairSlot = pairHalfOne + pairHalfTwo` — the pointwise linearity of the integrand together with
  the integrability of each orientation on the box;
* **`pairHalfOne = pairHalfTwo`** — the pair field is *symmetric*: the two orientations differ
  only by the exchange of the two slots of the pair, and the double slot sum is invariant under
  that exchange.

The mathematical heart is the self-adjointness of a single slot mean `Pᵢ = aP ℓ i` over the box,
`∫_{abox}(PᵢΦ)·Ψ = ∫_{abox}Φ·(PᵢΨ)`.  Here the state `Φ` is continuous but the weight `w` is only
*measurable, bounded*, so the pair weight `Ψ` is merely measurable with a bound on the box;
`Work.BoseBoxFock.Weak.aP_sym_box` — the slot self-adjointness for measurable bounded states —
needs *global* bounds (the slot mean is taken at every point of `Ωᴺ`), so it is applied to the
box restrictions `Φ·1_{abox}`, `Ψ·1_{abox}` and transferred back with `aP_restrictBox`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## The two pair weights and the two orientations of the pair slot form -/

/-- The first pair weight of the χ-row: `Σ_j w(y_j)·P_jΦ`. -/
noncomputable def pairWtOne (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : X n → ℝ :=
  fun y => ∑ j : Fin n, w (y j) * aP ℓ j Φ y

/-- The second pair weight of the χ-row, at slot `i`: `w(y_i)·Σ_j P_jΦ`. -/
noncomputable def pairWtTwo (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) (i : Fin n) :
    X n → ℝ :=
  fun y => w (y i) * (∑ j : Fin n, aP ℓ j Φ y)

lemma pairHalfOne_eq (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) :
    pairHalfOne n ℓ w Φ
      = ∫ x in abox n ℓ, Φ x * (∑ i, aP ℓ i (pairWtOne n ℓ w Φ) x) := rfl

lemma pairHalfTwo_eq (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) :
    pairHalfTwo n ℓ w Φ
      = ∫ x in abox n ℓ, Φ x * (∑ i, aP ℓ i (pairWtTwo n ℓ w Φ i) x) := rfl

lemma pairSlot_eq (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) :
    pairSlot n ℓ w Φ
      = ∫ x in abox n ℓ, Φ x *
          ((∑ i, aP ℓ i (pairWtOne n ℓ w Φ) x) + (∑ i, aP ℓ i (pairWtTwo n ℓ w Φ i) x)) := rfl

/-! ## The box restriction `Φ·1_{abox}` -/

/-- The box restriction of a state: `Φ · 1_{abox n ℓ}`.  It agrees with `Φ` on the box and is
globally bounded as soon as `Φ` is bounded on the box. -/
noncomputable def restrictBox {n : ℕ} (ℓ : ℝ) (Φ : X n → ℝ) : X n → ℝ :=
  fun x => Φ x * (abox n ℓ).indicator (fun _ => (1 : ℝ)) x

lemma restrictBox_of_mem {n : ℕ} {ℓ : ℝ} {Φ : X n → ℝ} {x : X n} (hx : x ∈ abox n ℓ) :
    restrictBox ℓ Φ x = Φ x := by
  rw [restrictBox, Set.indicator_of_mem hx, mul_one]

lemma restrictBox_of_notMem {n : ℕ} {ℓ : ℝ} {Φ : X n → ℝ} {x : X n} (hx : x ∉ abox n ℓ) :
    restrictBox ℓ Φ x = 0 := by
  rw [restrictBox, Set.indicator_of_notMem hx, mul_zero]

lemma measurable_restrictBox {n : ℕ} (ℓ : ℝ) {Φ : X n → ℝ} (hΦ : Measurable Φ) :
    Measurable (restrictBox ℓ Φ) :=
  hΦ.mul (measurable_const.indicator (abox_measurable n ℓ))

lemma abs_restrictBox_le {n : ℕ} {ℓ : ℝ} {Φ : X n → ℝ} {B : ℝ}
    (hΦb : ∀ x ∈ abox n ℓ, |Φ x| ≤ B) :
    ∀ x, |restrictBox ℓ Φ x| ≤ max B 0 := by
  intro x
  by_cases hx : x ∈ abox n ℓ
  · rw [restrictBox_of_mem hx]
    exact le_trans (hΦb x hx) (le_max_left _ _)
  · rw [restrictBox_of_notMem hx, abs_zero]
    exact le_max_right _ _

/-- **The slot mean of the box restriction agrees with that of the state on the box.** -/
lemma aP_restrictBox {n : ℕ} {ℓ : ℝ} (i : Fin n) (Φ : X n → ℝ) {x : X n}
    (hx : x ∈ abox n ℓ) :
    aP ℓ i (restrictBox ℓ Φ) x = aP ℓ i Φ x := by
  unfold aP restrictBox
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (acube_measurable ℓ) (fun y hy => ?_)
  have hupd : Function.update x i y ∈ abox n ℓ := update_mem_abox i hx hy
  rw [Set.indicator_of_mem hupd, mul_one]

/-! ## Integrability of `Φ` times a slot mean -/

/-- The product of a continuous state with a slot mean of a measurable function bounded on the
box is integrable over the box. -/
lemma integrableOn_Phi_mul_aP {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ F : X n → ℝ}
    (hΦc : Continuous Φ) (hFm : Measurable F) {D : ℝ}
    (hFb : ∀ x ∈ abox n ℓ, |F x| ≤ D) :
    IntegrableOn (fun x : X n => Φ x * aP ℓ i F x) (abox n ℓ) volume := by
  obtain ⟨B, hB⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn (s := abox n ℓ)
    (f := Φ) hΦc.continuousOn
  have hB' : ∀ x ∈ abox n ℓ, |Φ x| ≤ B := fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx
  refine IntegrableOn.of_bound (abox_lt_top n ℓ hℓ.le)
    ((hΦc.aestronglyMeasurable.restrict).mul (aP_aestronglyMeasurable_of_measurable i hFm))
    (max B 0 * max D 0) ?_
  rw [ae_restrict_iff' (abox_measurable n ℓ)]
  refine ae_of_all volume (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul (le_trans (hB' x hx) (le_max_left B 0))
    (le_trans (aP_abs_le_of_boundOn hℓ i hFm hFb x hx) (le_max_left D 0))
    (abs_nonneg _) ?_
  exact le_trans (abs_nonneg _) (le_trans (hB' x hx) (le_max_left B 0))

/-- The product of a continuous state with a finite sum of slot means of measurable functions
bounded on the box is integrable over the box. -/
lemma integrableOn_Phi_mul_sum_aP {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) {F : Fin n → X n → ℝ} (hFm : ∀ i, Measurable (F i)) {D : ℝ}
    (hFb : ∀ i, ∀ x ∈ abox n ℓ, |F i x| ≤ D) :
    IntegrableOn (fun x : X n => Φ x * (∑ i, (aP ℓ i (F i)) x)) (abox n ℓ) volume := by
  have hpt : (fun x : X n => Φ x * (∑ i, (aP ℓ i (F i)) x))
      = fun x : X n => ∑ i, Φ x * (aP ℓ i (F i)) x := by
    funext x
    rw [Finset.mul_sum]
  rw [hpt]
  exact integrable_finsetSum Finset.univ
    (fun i _ => integrableOn_Phi_mul_aP hℓ i hΦc (hFm i) (hFb i))

/-! ## Self-adjointness of a slot mean with mixed hypotheses -/

/-- **Self-adjointness of the slot mean over the box, mixed hypotheses.**  The state `Φ` is
continuous, the test function `Ψ` is only measurable with a bound *on the box*. -/
theorem aP_sym_box_of_boundOn {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ Ψ : X n → ℝ}
    (hΦc : Continuous Φ) (hΨm : Measurable Ψ) {D : ℝ} (hD : 0 ≤ D)
    (hΨb : ∀ x ∈ abox n ℓ, |Ψ x| ≤ D) :
    (∫ x in abox n ℓ, (aP ℓ i Φ x) * Ψ x)
      = ∫ x in abox n ℓ, Φ x * (aP ℓ i Ψ x) := by
  obtain ⟨B, hB⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn (s := abox n ℓ)
    (f := Φ) hΦc.continuousOn
  have hB' : ∀ x ∈ abox n ℓ, |Φ x| ≤ B := fun x hx => by
    simpa [Real.norm_eq_abs] using hB x hx
  have hkey := Weak.aP_sym_box (n := n) (ℓ := ℓ) hℓ i (C := max B 0) (D := max D 0)
    (le_max_right _ _) (le_max_right _ _)
    (measurable_restrictBox ℓ hΦc.measurable) (abs_restrictBox_le hB')
    (measurable_restrictBox ℓ hΨm) (abs_restrictBox_le hΨb)
  have h1 : (∫ x in abox n ℓ, (aP ℓ i (restrictBox ℓ Φ) x) * restrictBox ℓ Ψ x)
      = ∫ x in abox n ℓ, (aP ℓ i Φ x) * Ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict (abox_measurable n ℓ)] with x hx
    rw [aP_restrictBox i Φ hx, restrictBox_of_mem hx]
  have h2 : (∫ x in abox n ℓ, restrictBox ℓ Φ x * (aP ℓ i (restrictBox ℓ Ψ) x))
      = ∫ x in abox n ℓ, Φ x * (aP ℓ i Ψ x) := by
    refine integral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict (abox_measurable n ℓ)] with x hx
    rw [aP_restrictBox i Ψ hx, restrictBox_of_mem hx]
  rw [← h1, hkey, h2]

/-- **The slot self-adjointness distributed over the slots**, for weights that are only
measurable with a bound on the box. -/
theorem aP_sym_sum_pt_of_boundOn {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) {F : Fin n → X n → ℝ} (hFm : ∀ i, Measurable (F i)) {D : ℝ}
    (hD : 0 ≤ D) (hFb : ∀ i, ∀ x ∈ abox n ℓ, |F i x| ≤ D) :
    (∫ x in abox n ℓ, Φ x * (∑ i, (aP ℓ i (F i)) x))
      = ∑ i, ∫ x in abox n ℓ, (aP ℓ i Φ) x * F i x := by
  have hpt : (fun x : X n => Φ x * (∑ i, (aP ℓ i (F i)) x))
      = fun x : X n => ∑ i, Φ x * (aP ℓ i (F i)) x := by
    funext x
    rw [Finset.mul_sum]
  have h1 : (∫ x in abox n ℓ, Φ x * (∑ i, (aP ℓ i (F i)) x))
      = ∑ i, ∫ x in abox n ℓ, Φ x * (aP ℓ i (F i)) x := by
    rw [hpt, integral_finsetSum]
    intro i _
    exact integrableOn_Phi_mul_aP hℓ i hΦc (hFm i) (hFb i)
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (aP_sym_box_of_boundOn hℓ i hΦc (hFm i) hD (hFb i)).symm

/-! ## The split of the pair slot form -/

theorem chiRow_pairSlot_split {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hwm : Measurable w)
    {K : ℝ} (hw : ∀ x, |w x| ≤ K) :
    Work.BoseBoxFock.pairSlot n ℓ w Φ
        = Work.BoseBoxFock.pairHalfOne n ℓ w Φ + Work.BoseBoxFock.pairHalfTwo n ℓ w Φ
      ∧ Work.BoseBoxFock.pairHalfOne n ℓ w Φ = Work.BoseBoxFock.pairHalfTwo n ℓ w Φ := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (w 0)) (hw 0)
  choose C hC0 hCb using fun j : Fin n => exists_bound_aP (ℓ := ℓ) hℓ j hΦc
  -- measurability of the two pair weights
  have hW1m : Measurable (pairWtOne n ℓ w Φ) :=
    Finset.measurable_sum _ (fun j _ =>
      (hwm.comp (measurable_pi_apply j)).mul (aP_continuous hℓ j hΦc).measurable)
  have hW2m : ∀ i : Fin n, Measurable (pairWtTwo n ℓ w Φ i) := fun i =>
    (hwm.comp (measurable_pi_apply i)).mul
      (Finset.measurable_sum _ (fun j _ => (aP_continuous hℓ j hΦc).measurable))
  -- bounds on the box
  have hW1b : ∀ x ∈ abox n ℓ, |pairWtOne n ℓ w Φ x| ≤ ∑ j : Fin n, K * C j := by
    intro x hx
    calc |pairWtOne n ℓ w Φ x| = |∑ j : Fin n, w (x j) * aP ℓ j Φ x| := rfl
      _ ≤ ∑ j : Fin n, |w (x j) * aP ℓ j Φ x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |w (x j)| * |aP ℓ j Φ x| :=
          Finset.sum_congr rfl (fun j _ => abs_mul _ _)
      _ ≤ ∑ j : Fin n, K * C j :=
          Finset.sum_le_sum (fun j _ => mul_le_mul (hw (x j)) (hCb j x hx) (abs_nonneg _) hK)
  have hW2b : ∀ i : Fin n, ∀ x ∈ abox n ℓ, |pairWtTwo n ℓ w Φ i x| ≤ K * ∑ j : Fin n, C j := by
    intro i x hx
    have hS : |∑ j : Fin n, aP ℓ j Φ x| ≤ ∑ j : Fin n, C j := by
      calc |∑ j : Fin n, aP ℓ j Φ x| ≤ ∑ j : Fin n, |aP ℓ j Φ x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin n, C j := Finset.sum_le_sum (fun j _ => hCb j x hx)
    calc |pairWtTwo n ℓ w Φ i x| = |w (x i)| * |∑ j : Fin n, aP ℓ j Φ x| := abs_mul _ _
      _ ≤ K * ∑ j : Fin n, C j := mul_le_mul (hw (x i)) hS (abs_nonneg _) hK
  have hD1 : 0 ≤ ∑ j : Fin n, K * C j := Finset.sum_nonneg (fun j _ => mul_nonneg hK (hC0 j))
  have hD2 : 0 ≤ K * ∑ j : Fin n, C j :=
    mul_nonneg hK (Finset.sum_nonneg (fun j _ => hC0 j))
  -- the two halves, evaluated slot by slot
  have hOneL : pairHalfOne n ℓ w Φ
      = ∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtOne n ℓ w Φ x := by
    rw [pairHalfOne_eq]
    exact aP_sym_sum_pt_of_boundOn hℓ hΦc (fun _ => hW1m) hD1 (fun _ => hW1b)
  have hTwoL : pairHalfTwo n ℓ w Φ
      = ∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtTwo n ℓ w Φ i x := by
    rw [pairHalfTwo_eq]
    exact aP_sym_sum_pt_of_boundOn hℓ hΦc hW2m hD2 hW2b
  -- expansion of the two pair weights inside the slot integral
  have hOneL2 : (∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtOne n ℓ w Φ x)
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x j) * (aP ℓ j Φ x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtOne n ℓ w Φ x)
        = ∫ x in abox n ℓ, ∑ j : Fin n, (aP ℓ i Φ x) * w (x j) * (aP ℓ j Φ x) from by
      apply integral_congr_ae
      filter_upwards with x
      rw [show pairWtOne n ℓ w Φ x = ∑ j : Fin n, w (x j) * aP ℓ j Φ x from rfl,
        Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [integral_finsetSum]
    intro j _
    exact integrableOn_cont_slot_bounded hℓ j (aP_continuous hℓ i hΦc)
      (aP_continuous hℓ j hΦc) hwm hw
  have hTwoL2 : (∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtTwo n ℓ w Φ i x)
      = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x in abox n ℓ, (aP ℓ i Φ x) * pairWtTwo n ℓ w Φ i x)
        = ∫ x in abox n ℓ, ∑ j : Fin n, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) from by
      apply integral_congr_ae
      filter_upwards with x
      rw [show pairWtTwo n ℓ w Φ i x = w (x i) * (∑ j : Fin n, aP ℓ j Φ x) from rfl,
        ← mul_assoc, Finset.mul_sum]]
    rw [integral_finsetSum]
    intro j _
    exact integrableOn_cont_slot_bounded hℓ i (aP_continuous hℓ i hΦc)
      (aP_continuous hℓ j hΦc) hwm hw
  -- the exchange of the two slots of the pair
  have hswap : (∑ i : Fin n, ∑ j : Fin n,
        ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x j) * (aP ℓ j Φ x))
      = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) := by
    have hAB : ∀ i j : Fin n,
        (∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x j) * (aP ℓ j Φ x))
          = (∫ x in abox n ℓ, (aP ℓ j Φ x) * w (x j) * (aP ℓ i Φ x)) := fun i j => by
      apply integral_congr_ae
      filter_upwards with x
      ring
    calc (∑ i : Fin n, ∑ j : Fin n,
          ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x j) * (aP ℓ j Φ x))
        = ∑ i : Fin n, ∑ j : Fin n,
            ∫ x in abox n ℓ, (aP ℓ j Φ x) * w (x j) * (aP ℓ i Φ x) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hAB i j))
      _ = ∑ j : Fin n, ∑ i : Fin n,
            ∫ x in abox n ℓ, (aP ℓ j Φ x) * w (x j) * (aP ℓ i Φ x) :=
          Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n,
            ∫ x in abox n ℓ, (aP ℓ i Φ x) * w (x i) * (aP ℓ j Φ x) := rfl
  -- the first conjunct
  have hAint : IntegrableOn (fun x : X n => Φ x * (∑ i, (aP ℓ i (pairWtOne n ℓ w Φ)) x))
      (abox n ℓ) volume :=
    integrableOn_Phi_mul_sum_aP hℓ hΦc (fun _ => hW1m) (fun _ => hW1b)
  have hBint : IntegrableOn (fun x : X n => Φ x * (∑ i, (aP ℓ i (pairWtTwo n ℓ w Φ i)) x))
      (abox n ℓ) volume :=
    integrableOn_Phi_mul_sum_aP hℓ hΦc hW2m hW2b
  have hsplit : pairSlot n ℓ w Φ = pairHalfOne n ℓ w Φ + pairHalfTwo n ℓ w Φ := by
    rw [pairSlot_eq, pairHalfOne_eq, pairHalfTwo_eq]
    rw [show (∫ x in abox n ℓ, Φ x *
          ((∑ i, aP ℓ i (pairWtOne n ℓ w Φ) x) + (∑ i, aP ℓ i (pairWtTwo n ℓ w Φ i) x)))
        = ∫ x in abox n ℓ, (Φ x * (∑ i, aP ℓ i (pairWtOne n ℓ w Φ) x)
            + Φ x * (∑ i, aP ℓ i (pairWtTwo n ℓ w Φ i) x)) from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    exact integral_add hAint hBint
  refine ⟨hsplit, ?_⟩
  rw [hOneL, hTwoL, hOneL2, hTwoL2, hswap]

end Work.BoseBoxFock
