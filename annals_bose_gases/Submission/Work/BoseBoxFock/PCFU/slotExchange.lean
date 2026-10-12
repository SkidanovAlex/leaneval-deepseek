import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.slotExchange` — the slot/momentum exchange

For `i ≠ j` the map

  `T (x, (a, b)) = (x[i ↦ a][j ↦ b], (x i, x j))`

on `X n × (E³ × E³)` replaces the two particle slots `i, j` of `x` by the two momentum-slot
variables `a, b`, returning the old slot values `x i, x j` as the new momentum pair.  It is an
involution, and it is measure preserving for the Lebesgue product measure: with the
identification `X n × (E³ × E³) ≃ᵐ (Fin n ⊕ Fin 2) → E³` (`Fin n` = particle slots, `Fin 2` = the
two momentum slots) it becomes the coordinate permutation

  `swap (Sum.inl i) (Sum.inr 0) * swap (Sum.inl j) (Sum.inr 1)`,

and coordinate permutations of a finite Pi of Lebesgue measures preserve the measure.  Hence

`∫ F (x i) (x j) a b · Θ(x[i↦a][j↦b]) = ∫ F a b (x i) (x j) · Θ x`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The identification `X n × (E³ × E³) ≃ᵐ (Fin n ⊕ Fin 2) → E³` -/

/-- `X n × (E³ × E³)` is the space of functions on `Fin n ⊕ Fin 2`: the `n` particle slots
(`Sum.inl`) together with the two momentum slots (`Sum.inr 0`, `Sum.inr 1`). -/
def pairSlotIso (n : ℕ) : (Fin n ⊕ Fin 2 → E3) ≃ᵐ (Submission.BoseGases.X n × (E3 × E3)) where
  toEquiv :=
    { toFun := fun f => (fun k => f (Sum.inl k), (f (Sum.inr 0), f (Sum.inr 1)))
      invFun := fun q s => Sum.elim q.1 (fun m : Fin 2 => if m = 0 then q.2.1 else q.2.2) s
      left_inv := by
        intro f; funext s; cases s with
        | inl k => rfl
        | inr m => fin_cases m <;> simp
      right_inv := by
        rintro ⟨x, a, b⟩; simp }
  measurable_invFun := by
    rw [measurable_pi_iff]
    rintro (k | m)
    · exact (measurable_pi_apply k).comp measurable_fst
    · fin_cases m <;> simp <;>
        first
          | exact measurable_fst.comp measurable_snd
          | exact measurable_snd.comp measurable_snd

lemma pairSlotIso_apply {n : ℕ} (f : Fin n ⊕ Fin 2 → E3) :
    pairSlotIso n f = (fun k => f (Sum.inl k), (f (Sum.inr 0), f (Sum.inr 1))) := rfl

/-- `pairSlotIso` preserves the (Lebesgue) volume, being the composite of
`sumPiEquivProdPi` and `piFinTwo`. -/
lemma pairSlotIso_measurePreserving (n : ℕ) :
    MeasurePreserving (pairSlotIso n) (volume : Measure (Fin n ⊕ Fin 2 → E3))
      (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin 2 => (volume : Measure E3))
  have h2 := measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure E3))
  have h3 : MeasurePreserving (fun p : (Fin n → E3) × (Fin 2 → E3) =>
        (p.1, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => E3)) p.2))
      ((Measure.pi fun _ : Fin n => (volume : Measure E3)).prod
        (Measure.pi fun _ : Fin 2 => (volume : Measure E3)))
      ((Measure.pi fun _ : Fin n => (volume : Measure E3)).prod
        ((volume : Measure E3).prod (volume : Measure E3))) :=
    MeasurePreserving.prod (MeasurePreserving.id _) h2
  exact h3.comp h1

/-! ## The index permutation `swap (inl i) (inr 0) * swap (inl j) (inr 1)` -/

def pairSlotPerm {n : ℕ} (i j : Fin n) : Fin n ⊕ Fin 2 ≃ Fin n ⊕ Fin 2 :=
  (Equiv.swap (Sum.inl i) (Sum.inr 0)).trans (Equiv.swap (Sum.inl j) (Sum.inr 1))

lemma pairSlotPerm_inl_i {n : ℕ} {i j : Fin n} : pairSlotPerm i j (Sum.inl i) = Sum.inr 0 := by
  rw [pairSlotPerm, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (by simp)

lemma pairSlotPerm_inl_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    pairSlotPerm i j (Sum.inl j) = Sum.inr 1 := by
  rw [pairSlotPerm, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (by simpa using hij.symm) Sum.inl_ne_inr,
    Equiv.swap_apply_left]

lemma pairSlotPerm_inr_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    pairSlotPerm i j (Sum.inr 0) = Sum.inl i := by
  rw [pairSlotPerm, Equiv.trans_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by simpa using hij) Sum.inl_ne_inr]

lemma pairSlotPerm_inr_one {n : ℕ} {i j : Fin n} : pairSlotPerm i j (Sum.inr 1) = Sum.inl j := by
  rw [pairSlotPerm, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (by simp),
    Equiv.swap_apply_right]

lemma pairSlotPerm_inl_other {n : ℕ} {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    pairSlotPerm i j (Sum.inl k) = Sum.inl k := by
  rw [pairSlotPerm, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (by simpa using hki) Sum.inl_ne_inr,
    Equiv.swap_apply_of_ne_of_ne (by simpa using hkj) Sum.inl_ne_inr]

/-! ## The slot/momentum exchange -/

/-- The slot/momentum exchange on `X n × (E³ × E³)`. -/
def pairSlotRoll {n : ℕ} (i j : Fin n) (q : Submission.BoseGases.X n × (E3 × E3)) :
    Submission.BoseGases.X n × (E3 × E3) :=
  (Function.update (Function.update q.1 i q.2.1) j q.2.2, (q.1 i, q.1 j))

/-- **`pairSlotRoll` is the coordinate permutation `pairSlotPerm`** under `pairSlotIso`. -/
lemma pairSlotIso_pairSlotPerm {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : Fin n ⊕ Fin 2 → E3) :
    pairSlotIso n (fun s => f (pairSlotPerm i j s)) = pairSlotRoll i j (pairSlotIso n f) := by
  rw [pairSlotIso_apply, pairSlotIso_apply, pairSlotRoll]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext k
    by_cases hki : k = i
    · rw [hki, pairSlotPerm_inl_i]
      simp [hij]
    · by_cases hkj : k = j
      · rw [hkj, pairSlotPerm_inl_j hij]
        simp
      · rw [pairSlotPerm_inl_other hki hkj]
        simp [hki, hkj]
  · simp only [pairSlotPerm_inr_zero hij]
  · simp only [pairSlotPerm_inr_one]

/-- The coordinate permutation on functions induced by `pairSlotPerm`. -/
def pairSlotAct {n : ℕ} (i j : Fin n) :
    (Fin n ⊕ Fin 2 → E3) ≃ᵐ (Fin n ⊕ Fin 2 → E3) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin 2 => E3) (pairSlotPerm i j).symm

lemma pairSlotAct_apply {n : ℕ} (i j : Fin n) (f : Fin n ⊕ Fin 2 → E3) :
    pairSlotAct i j f = fun s => f (pairSlotPerm i j s) := by
  funext s
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n ⊕ Fin 2 => E3)
    (pairSlotPerm i j).symm f (pairSlotPerm i j s)
  simpa [pairSlotAct] using h

/-- `pairSlotRoll`, bundled as a measurable equivalence. -/
def pairSlotRollEquiv {n : ℕ} (i j : Fin n) :
    Submission.BoseGases.X n × (E3 × E3) ≃ᵐ Submission.BoseGases.X n × (E3 × E3) :=
  (pairSlotIso n).symm.trans ((pairSlotAct i j).trans (pairSlotIso n))

lemma pairSlotRollEquiv_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (q : Submission.BoseGases.X n × (E3 × E3)) :
    pairSlotRollEquiv i j q = pairSlotRoll i j q := by
  have h1 : pairSlotRollEquiv i j q
      = pairSlotIso n (pairSlotAct i j ((pairSlotIso n).symm q)) := rfl
  rw [h1, pairSlotAct_apply, pairSlotIso_pairSlotPerm hij, MeasurableEquiv.apply_symm_apply]

lemma pairSlotRollEquiv_measurePreserving {n : ℕ} (i j : Fin n) :
    MeasurePreserving (pairSlotRollEquiv i j)
      (volume : Measure (Submission.BoseGases.X n × (E3 × E3)))
      (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) := by
  have he := pairSlotIso_measurePreserving n
  have ha : MeasurePreserving (pairSlotAct i j) (volume : Measure (Fin n ⊕ Fin 2 → E3))
      (volume : Measure (Fin n ⊕ Fin 2 → E3)) :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin 2 => E3) (pairSlotPerm i j).symm
  exact he.symm.trans (ha.trans he)

/-- **The slot/momentum exchange is measure preserving.** -/
lemma pairSlotRoll_measurePreserving {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (pairSlotRoll i j)
      (volume : Measure (Submission.BoseGases.X n × (E3 × E3)))
      (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) := by
  have h := pairSlotRollEquiv_measurePreserving i j
  rwa [show ⇑(pairSlotRollEquiv i j) = pairSlotRoll i j from
    funext (fun q => pairSlotRollEquiv_apply hij q)] at h

theorem slotExchange {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (Θ : Submission.BoseGases.X n → ℝ) (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hF : MeasureTheory.Integrable (fun q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      F (q.1 i) (q.1 j) q.2.1 q.2.2
        * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))) :
    (∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        F (q.1 i) (q.1 j) q.2.1 q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        F q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) := by
  have _hF := hF
  have hmp := pairSlotRollEquiv_measurePreserving i j
  have key := hmp.integral_comp' (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      F q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ))
  rw [← key]
  apply integral_congr_ae
  filter_upwards with q
  rw [pairSlotRollEquiv_apply hij q]
  simp [pairSlotRoll, hij]

end Work.BoseBoxFock.PCFU
