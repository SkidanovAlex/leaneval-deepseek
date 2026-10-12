import Mathlib
import Submission.Work.BoseBoxFock.pairGBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pairGc23Aux` — the box measure theory of the clean `pairGc23` fibre

The clean fibre `pairGc23 ℓ p hp Θ₀ A B w₀ w₁` (`pairGCore`) is the *set* integral

    ∫ z in (boxPiSet P12 ℓ) ×ˢ ((boxL ℓ) ×ˢ (boxL ℓ)),
        star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
          * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)

over the "product box" `pairS23 ℓ p`.  This module collects the elementary measure theory of that
box that the `L²` (Cauchy–Schwarz) bound of the fibre rests on:

* compactness / finiteness of `pairS23 ℓ p` (`isCompact_pairS23`, `pairS23_measure_ne_top`);
* the identification of its restriction measure with the product of the restricted one-particle
  measures (`pairS23_restrict_eq_prod`) and the value `ℓ⁶` of the volume of the two kernel boxes
  (`pairS23_second_volume`);
* the *splitting* identity `insertCoord2 p a b x' = splitEquiv hp (x', (a, b))` and the fact that
  the measure preserving equivalence `splitEquiv hp` of `blockTwo3_aux` carries `pairS23 ℓ p` onto
  the `n`-particle box `abox n ℓ` (`splitEquiv_image_pairS23`);
* consequently the **change of variables** for the *free* state factor
  `pairS23_integral_sq_eq_pinL2`: `∫_{pairS23} ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖² = pinL2 ℓ Θ₀`.
  This is the `g`-factor of the Cauchy–Schwarz estimate for `pairGc23`.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The complementary fibre index type of the two removed slots `p.1`, `p.2`. -/
abbrev pairFib23 (n : ℕ) (p : Fin n × Fin n) : Type := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}

/-- **The product box of the clean `pairGc23` fibre**: the free fibre box times the two kernel
boxes (in the order `(w₀, w₁)`, matching the definition of `pairGc23`). -/
def pairS23 {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) :
    Set ((pairFib23 n p → E3) × (E3 × E3)) :=
  boxPiSet (pairFib23 n p) ℓ ×ˢ (boxL ℓ ×ˢ boxL ℓ)

theorem mem_pairS23 {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n}
    {z : (pairFib23 n p → E3) × (E3 × E3)} :
    z ∈ pairS23 ℓ p ↔ z.1 ∈ boxPiSet (pairFib23 n p) ℓ ∧ z.2.1 ∈ boxL ℓ ∧ z.2.2 ∈ boxL ℓ := by
  rw [pairS23, Set.mem_prod, Set.mem_prod]

theorem isCompact_pairS23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    IsCompact (pairS23 ℓ p) := by
  rw [pairS23]
  exact (isCompact_boxPiSet (ι := pairFib23 n p) hℓ).prod
    ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ))

theorem pairS23_measurableSet {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    MeasurableSet (pairS23 ℓ p) :=
  (isCompact_pairS23 hℓ p).measurableSet

theorem pairS23_measure_ne_top {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) :
    (volume : Measure ((pairFib23 n p → E3) × (E3 × E3))) (pairS23 ℓ p) ≠ ⊤ :=
  (isCompact_pairS23 hℓ p).measure_ne_top

/-- **The restriction of the product volume to the box is the product of the restricted
one-particle measures.** -/
theorem pairS23_restrict_eq_prod {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n) :
    (volume : Measure ((pairFib23 n p → E3) × (E3 × E3))).restrict (pairS23 ℓ p)
      = ((volume : Measure (pairFib23 n p → E3)).restrict (boxPiSet (pairFib23 n p) ℓ)).prod
          (((volume : Measure E3).restrict (boxL ℓ)).prod
            ((volume : Measure E3).restrict (boxL ℓ))) := by
  rw [pairS23, Measure.volume_eq_prod (pairFib23 n p → E3) (E3 × E3)]
  rw [← Measure.prod_restrict (boxPiSet (pairFib23 n p) ℓ) (boxL ℓ ×ˢ boxL ℓ)]
  rw [Measure.volume_eq_prod E3 E3]
  rw [← Measure.prod_restrict (boxL ℓ) (boxL ℓ)]

/-- **The volume of the two kernel boxes is `ℓ⁶`.** -/
theorem pairS23_second_volume (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) Set.univ
      = ENNReal.ofReal (ℓ ^ 6) := by
  have h1 : (((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))) Set.univ
      = ((volume : Measure E3).restrict (boxL ℓ)) Set.univ
        * ((volume : Measure E3).restrict (boxL ℓ)) Set.univ := by
    simpa using Measure.prod_prod (μ := (volume : Measure E3).restrict (boxL ℓ))
      (ν := (volume : Measure E3).restrict (boxL ℓ)) Set.univ Set.univ
  rw [h1, Measure.restrict_apply_univ,
    Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ℓ ^ 3 by positivity)]
  congr 1
  ring

/-- The real-valued form of `pairS23_second_volume`. -/
theorem pairS23_second_volume_real (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ((((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ)))).real Set.univ = ℓ ^ 6 := by
  rw [Measure.real, pairS23_second_volume ℓ hℓ, ENNReal.toReal_ofReal (by positivity)]

/-- The insertion of the two kernel coordinates is continuous (in the `pairGc23` order). -/
lemma continuous_insertCoord2_joint_pg23 {n : ℕ} (p : Fin n × Fin n) :
    Continuous (fun z : (pairFib23 n p → E3) × (E3 × E3) =>
      insertCoord2 p z.2.1 z.2.2 z.1) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have : (fun z : (pairFib23 n p → E3) × (E3 × E3) =>
        insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.2.1 := by
      funext z
      simp only [insertCoord2_eq, dif_pos h1]
    rw [this]; exact continuous_snd.fst
  · by_cases h2 : k = p.2
    · have : (fun z : (pairFib23 n p → E3) × (E3 × E3) =>
          insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.2.2 := by
        funext z
        simp only [insertCoord2_eq, dif_neg h1, dif_pos h2]
      rw [this]; exact continuous_snd.snd
    · have : (fun z : (pairFib23 n p → E3) × (E3 × E3) =>
          insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.1 ⟨k, h1, h2⟩ := by
        funext z
        simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]
      rw [this]
      exact (continuous_apply _).comp continuous_fst

/-- The insertion with the two kernel coordinates fixed is continuous. -/
lemma continuous_insertCoord2_fixed_pg23 {n : ℕ} (p : Fin n × Fin n) (a b : E3) :
    Continuous (fun x' : pairFib23 n p → E3 => insertCoord2 p a b x') := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have : (fun x' : pairFib23 n p → E3 => insertCoord2 p a b x' k) = fun _ => a := by
      funext x'
      simp only [insertCoord2_eq, dif_pos h1]
    rw [this]; exact continuous_const
  · by_cases h2 : k = p.2
    · have : (fun x' : pairFib23 n p → E3 => insertCoord2 p a b x' k) = fun _ => b := by
        funext x'
        simp only [insertCoord2_eq, dif_neg h1, dif_pos h2]
      rw [this]; exact continuous_const
    · have : (fun x' : pairFib23 n p → E3 => insertCoord2 p a b x' k)
          = fun x' => x' ⟨k, h1, h2⟩ := by
        funext x'
        simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]
      rw [this]
      exact (continuous_apply _)

/-- The square of the inserted state is integrable over the fibre box. -/
theorem integrableOn_normSq_insertCoord2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} (hΘ₀ : Continuous Θ₀) (w₀ w₁ : E3) :
    IntegrableOn (fun x' : pairFib23 n p → E3 => ‖Θ₀ (insertCoord2 p w₀ w₁ x')‖ ^ 2)
      (boxPiSet (pairFib23 n p) ℓ) :=
  (((hΘ₀.comp (continuous_insertCoord2_fixed_pg23 p w₀ w₁)).norm.pow 2)).continuousOn
    |>.integrableOn_compact (isCompact_boxPiSet (ι := pairFib23 n p) hℓ)

/-- The inserted configuration is the measure preserving insertion `splitEquiv`. -/
theorem insertCoord2_eq_splitEquiv_pg23 {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (z : (pairFib23 n p → E3) × (E3 × E3)) :
    insertCoord2 p z.2.1 z.2.2 z.1 = splitEquiv hp z := by
  obtain ⟨x', a, b⟩ := z
  simp only [insertCoord2_eq, splitEquiv_apply]

/-- **The insertion carries the product box onto the `n`-particle box.** -/
theorem splitEquiv_image_pairS23 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) :
    splitEquiv hp '' pairS23 ℓ p = Submission.BoseGases.abox n ℓ := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← insertCoord2_eq_splitEquiv_pg23 hp z]
    rw [Submission.BoseGases.mem_abox_iff, ← corpusBox_boxL_eq_acube hℓ]
    obtain ⟨hz1, hz2a, hz2b⟩ := mem_pairS23.mp hz
    have hz1' := mem_boxPiSet.mp hz1
    intro k
    simp only [insertCoord2_eq]
    by_cases h1 : k = p.1
    · rw [dif_pos h1]; exact hz2a
    · by_cases h2 : k = p.2
      · rw [dif_neg h1, dif_pos h2]; exact hz2b
      · rw [dif_neg h1, dif_neg h2]; exact hz1' ⟨k, h1, h2⟩
  · intro hx
    have hxab : ∀ i : Fin n, x i ∈ boxL ℓ := fun i => by
      rw [corpusBox_boxL_eq_acube hℓ]
      exact (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx i
    refine ⟨(fun k => x k.1, (x p.1, x p.2)), ?_, ?_⟩
    · rw [mem_pairS23]
      exact ⟨mem_boxPiSet.mpr (fun k => hxab k.1), hxab p.1, hxab p.2⟩
    · rw [splitEquiv_apply]
      funext k
      by_cases h1 : k = p.1
      · rw [dif_pos h1, h1]
      · by_cases h2 : k = p.2
        · rw [dif_neg h1, dif_pos h2, h2]
        · rw [dif_neg h1, dif_neg h2]

/-- **Change of variables for the free state factor.**  The box integral of
`‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖²` is `pinL2 ℓ Θ₀`. -/
theorem pairS23_integral_sq_eq_pinL2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {Θ₀ : Xn n → ℂ} (hΘ₀ : Continuous Θ₀) :
    (∫ z in pairS23 ℓ p, ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2) = pinL2 ℓ Θ₀ := by
  have himg := splitEquiv_image_pairS23 hℓ hp
  have h := (measurePreserving_splitEquiv hp).setIntegral_image_emb
    (splitEquiv hp).measurableEmbedding (fun x : Xn n => ‖Θ₀ x‖ ^ 2) (pairS23 ℓ p)
  rw [himg] at h
  have h2 : (∫ z in pairS23 ℓ p, ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ^ 2)
      = ∫ z in pairS23 ℓ p, ‖Θ₀ (splitEquiv hp z)‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [insertCoord2_eq_splitEquiv_pg23 hp z]
  have key : (∫ z in pairS23 ℓ p, ‖Θ₀ (splitEquiv hp z)‖ ^ 2)
      = ∫ y in Submission.BoseGases.abox n ℓ, ‖Θ₀ y‖ ^ 2 := by
    rw [Measure.volume_eq_prod (pairFib23 n p → E3) (E3 × E3)]
    exact h.symm
  rw [h2, key, pinL2]

end Work.BoseBoxFock
