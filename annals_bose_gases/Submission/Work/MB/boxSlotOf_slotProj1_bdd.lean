import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.boxSlotOf_slotProj1_self
import Submission.Work.MB.boxSlotSum_measurable_bounded_ae
import Submission.Work.MB.slotProj1_idem_weak
import Submission.Work.MB.slotProj1_linear_bdd
import Submission.Work.MB.slotProj_mb_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
## The measurable/bounded slot calculus of `boxSlotOf e (evec l) (evec l') j`

The helpers below are the weak (measurable, everywhere bounded, box supported) twins of
`Work.BoseBoxFock.etaOf_evec_self`, of the one-variable kernel computation
`Work.BoseBoxFock.integral_PV_mul_PV`, and of the Fubini integrability inputs of
`Work.BoseBoxFock.boxSlotOf_slotProj1_self` / `slotProj1_boxSlotOf_self` /
`boxSlotOf_slotProj1_comm`.

The only point in which the weak setting differs from the strong one is the integrability of the
two-variable Fubini integrands: instead of continuity plus compact support we use that the
integrand is measurable, everywhere bounded, and pointwise supported in
`boxL ℓ ×ˢ boxL ℓ` (of finite measure) — `Work.MB.integrable_of_bdd_of_support` together with
`Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL`.
-/

/-- `etaOf e (evec m l) = e l`, in applied form. -/
theorem etaOf_evec_apply_bdd {m : ℕ} {e : Fin m → E3 → ℂ} (l : Fin m) (z : E3) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m l) z = e l z :=
  congrFun (Work.BoseBoxFock.etaOf_evec_self e l) z

/-- The dictionary slot at the coordinate vectors, in the form in which the slot computations
are carried out:
`(boxSlotOf e (evec l) (evec l') j Θ)(x) = e l (x j) · ∫ z, star (e l' z) · Θ (x[j ↦ z])`. -/
theorem boxSlotOf_evec_apply_bdd {m d : ℕ} {e : Fin m → E3 → ℂ} (l l' : Fin m) (j : Fin d)
    (Θ : (Fin d → E3) → ℂ) (x : Fin d → E3) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x
      = e l (x j) * ∫ z : E3, star (e l' z) * Θ (Function.update x j z) := by
  simp only [Work.BoseDict.boxSlotOf, etaOf_evec_apply_bdd, starRingEnd_apply]

/-- **The resolution form of the projection kernel** for weak modes:
`∫ z, star (e l' z) · PV e z w = star (e l' w)`.  This is the one-variable kernel computation
behind the absorption of the `j`-slot operator by the `j`-slot projection. -/
theorem integral_star_mode_mul_PV_bdd {m : ℕ} {e : Fin m → E3 → ℂ}
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', Integrable (fun z : E3 => star (e l z) * e l' z) volume)
    (l' : Fin m) (w : E3) :
    ∫ z : E3, star (e l' z) * Work.BoseBoxFock.PV e z w = star (e l' w) := by
  have hpt : (fun z : E3 => star (e l' z) * Work.BoseBoxFock.PV e z w)
      = (fun z : E3 => ∑ k : Fin m, star (e k w) * (star (e l' z) * e k z)) := by
    funext z
    simp only [Work.BoseBoxFock.PV, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hpt, MeasureTheory.integral_finsetSum]
  swap
  · intro k _
    exact (hint l' k).const_mul _
  have hsum : (∑ k : Fin m, ∫ z : E3, star (e k w) * (star (e l' z) * e k z))
      = ∑ k : Fin m, star (e k w) * (if l' = k then (1 : ℂ) else 0) :=
    Finset.sum_congr rfl (fun k _ => by rw [MeasureTheory.integral_const_mul, horth l' k])
  rw [hsum]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- **Joint integrability of the uncurried integrand of the `j`-self absorption.**  For weak
modes and a weak state the integrand `(z, w) ↦ star (e l' z) · (PV e z w · Θ (x[j ↦ w]))` is
integrable on `volume × volume`: it is measurable, everywhere bounded, and pointwise supported
in `boxL ℓ ×ˢ boxL ℓ` (the first factor dies with `star (e l' z)` for `z` outside the box, the
second with `PV e z w` for `w` outside). -/
theorem integrable_uncurry_self_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (l' : Fin m) (j : Fin d) (Θ : (Fin d → E3) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (x : Fin d → E3) :
    Integrable (Function.uncurry (fun z w : E3 =>
      star (e l' z) * (Work.BoseBoxFock.PV e z w * Θ (Function.update x j w))))
      (volume.prod volume) := by
  obtain ⟨K, hK0, hK⟩ := PV_weak_bound hbdd
  obtain ⟨Ce, hCe⟩ := hbdd l'
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  set B : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hB
  have hBmeas : MeasurableSet B := by
    rw [hB]; exact Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hBfin : (volume : Measure E3) B ≠ ⊤ := by
    rw [hB]; exact (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  have hpair : Integrable (fun p : E3 × E3 =>
      star (e l' p.1) * (Work.BoseBoxFock.PV e p.1 p.2 * Θ (Function.update x j p.2)))
      (volume.prod volume) := by
    refine integrable_of_bdd_of_support (μ := volume.prod volume) (S := B ×ˢ B)
      (hBmeas.prod hBmeas) ?_ ?_ (C := max Ce 0 * (K * max CΘ 0)) ?_ ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hBfin hBfin
    · exact (((continuous_star.measurable.comp (hmeas l')).comp measurable_fst).mul
        ((PV_weak_measurable hmeas).mul
          (hΘm.comp (Work.BoseBoxFock.measurable_update_snd x j)))).aestronglyMeasurable
    · intro p
      change ‖star (e l' p.1) * (Work.BoseBoxFock.PV e p.1 p.2 *
        Θ (Function.update x j p.2))‖ ≤ max Ce 0 * (K * max CΘ 0)
      rw [norm_mul, norm_star, norm_mul]
      exact mul_le_mul ((hCe p.1).trans (le_max_left _ _))
        (mul_le_mul (hK p.1 p.2) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hK0)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (le_max_right _ _)
    · intro p hp
      change star (e l' p.1) * (Work.BoseBoxFock.PV e p.1 p.2 *
        Θ (Function.update x j p.2)) = 0
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hz : e l' p.1 = 0 := by
          by_contra hne
          exact hp (hsupp l' (Function.mem_support.mpr hne))
        rw [hz, star_zero, zero_mul]
      · rw [Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp hp, zero_mul, mul_zero]
  have huncurry : Function.uncurry (fun z w : E3 =>
      star (e l' z) * (Work.BoseBoxFock.PV e z w * Θ (Function.update x j w)))
      = (fun p : E3 × E3 => star (e l' p.1) *
          (Work.BoseBoxFock.PV e p.1 p.2 * Θ (Function.update x j p.2))) := by
    funext p
    obtain ⟨a, b⟩ := p
    rfl
  rw [huncurry]
  exact hpair

/-- **Absorption at the same slot.**  The rank-one slot `|e l⟩⟨e l'|` acting in the slot `j` is
unchanged by the `j`-th slot projection onto `span{e k}`. -/
theorem boxSlotOf_slotProj1_self_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', Integrable (fun z : E3 => star (e l z) * e l' z) volume)
    {Θ : (Fin d → E3) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    ∀ (l l' : Fin m) (j : Fin d),
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (Work.BoseBoxFock.slotProj1 e j Θ)
        = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  intro l l' j
  funext x
  have hval : ∀ w : E3,
      (∫ z : E3, star (e l' z) * Work.BoseBoxFock.PV e z w) = star (e l' w) :=
    fun w => integral_star_mode_mul_PV_bdd horth hint l' w
  have hstep : ∀ z : E3, (Work.BoseBoxFock.slotProj1 e j Θ) (Function.update x j z)
      = ∫ w : E3, Work.BoseBoxFock.PV e z w * Θ (Function.update x j w) := by
    intro z
    rw [Work.BoseBoxFock.slotProj1]
    apply integral_congr_ae
    filter_upwards with w
    rw [Function.update_self, Function.update_idem]
  have hintg : Integrable (Function.uncurry (fun z w : E3 =>
      star (e l' z) * (Work.BoseBoxFock.PV e z w * Θ (Function.update x j w))))
      (volume.prod volume) :=
    integrable_uncurry_self_bdd hmeas hbdd hsupp l' j Θ hΘm hΘb x
  rw [boxSlotOf_evec_apply_bdd l l' j (Work.BoseBoxFock.slotProj1 e j Θ) x,
    boxSlotOf_evec_apply_bdd l l' j Θ x]
  congr 1
  calc ∫ z : E3, star (e l' z) * (Work.BoseBoxFock.slotProj1 e j Θ) (Function.update x j z)
      = ∫ z : E3, star (e l' z) *
          (∫ w : E3, Work.BoseBoxFock.PV e z w * Θ (Function.update x j w)) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hstep z]
    _ = ∫ z : E3, ∫ w : E3, star (e l' z) *
          (Work.BoseBoxFock.PV e z w * Θ (Function.update x j w)) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ w : E3, ∫ z : E3, star (e l' z) *
          (Work.BoseBoxFock.PV e z w * Θ (Function.update x j w)) :=
        MeasureTheory.integral_integral_swap hintg
    _ = ∫ w : E3, (∫ z : E3, star (e l' z) * Work.BoseBoxFock.PV e z w) *
          Θ (Function.update x j w) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [show (fun z : E3 => star (e l' z) *
              (Work.BoseBoxFock.PV e z w * Θ (Function.update x j w)))
            = (fun z : E3 => (star (e l' z) * Work.BoseBoxFock.PV e z w) *
              Θ (Function.update x j w)) from funext fun z => by ring]
        rw [MeasureTheory.integral_mul_const]
    _ = ∫ w : E3, star (e l' w) * Θ (Function.update x j w) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [hval w]

/-- **Absorption of the slot by its own slot projection.**  The slot operator
`boxSlotOf e (evec l) (evec l') j` has its `j`-th slot already in `span{e k}`, so `slotProj1 e j`
leaves it unchanged.  The whole content is the one-variable kernel computation
`∫ w, PV e (x j) w · e l w = e l (x j)`. -/
theorem slotProj1_boxSlotOf_self_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', Integrable (fun z : E3 => star (e l z) * e l' z) volume)
    {Θ : (Fin d → E3) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    ∀ (l l' : Fin m) (j : Fin d),
      Work.BoseBoxFock.slotProj1 e j
          (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
        = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  intro l l' j
  funext x
  have hPV : ∫ w : E3, Work.BoseBoxFock.PV e (x j) w * e l w = e l (x j) := by
    rw [Work.BoseBoxFock.integral_PV_mul_eq_sum e (fun y : E3 => e l y)
      (fun k => hint k l) (x j)]
    rw [Finset.sum_eq_single l]
    · rw [horth l l, if_pos rfl, mul_one]
    · intro k _ hk
      rw [horth k l, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  have hpt : (fun w : E3 => Work.BoseBoxFock.PV e (x j) w *
        (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
          (Function.update x j w))
      = (fun w : E3 => (Work.BoseBoxFock.PV e (x j) w * e l w) *
          (∫ z : E3, star (e l' z) * Θ (Function.update x j z))) := by
    funext w
    simp only [boxSlotOf_evec_apply_bdd, Function.update_self, Function.update_idem]
    ring
  rw [Work.BoseBoxFock.slotProj1, hpt, MeasureTheory.integral_mul_const, hPV]
  rw [boxSlotOf_evec_apply_bdd]

/-- **Commutation at different slots.**  For `i ≠ j` the slot-`j` rank-one operator and the
slot-`i` projection act on different variables and commute (a Fubini exchange). -/
theorem boxSlotOf_slotProj1_comm_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', Integrable (fun z : E3 => star (e l z) * e l' z) volume)
    {Θ : (Fin d → E3) → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    ∀ (l l' : Fin m) (i j : Fin d), i ≠ j →
      Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (Work.BoseBoxFock.slotProj1 e i Θ)
        = Work.BoseBoxFock.slotProj1 e i
            (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) := by
  classical
  intro l l' i j hij
  funext x
  obtain ⟨K, hK0, hK⟩ := PV_weak_bound hbdd
  obtain ⟨Ce, hCe⟩ := hbdd l'
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  set B : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hB
  have hBmeas : MeasurableSet B := by
    rw [hB]; exact Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hBfin : (volume : Measure E3) B ≠ ⊤ := by
    rw [hB]; exact (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  -- the joint integrand of the two slot integrals
  have hpair : Integrable (fun p : E3 × E3 => star (e l' p.1) *
      (Work.BoseBoxFock.PV e (x i) p.2 *
        Θ (Function.update (Function.update x i p.2) j p.1)))
      (volume.prod volume) := by
    refine integrable_of_bdd_of_support (μ := volume.prod volume) (S := B ×ˢ B)
      (hBmeas.prod hBmeas) ?_ ?_ (C := max Ce 0 * (K * max CΘ 0)) ?_ ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hBfin hBfin
    · have h1 : Measurable (fun p : E3 × E3 => star (e l' p.1)) :=
        (continuous_star.measurable.comp (hmeas l')).comp measurable_fst
      have h2 : Measurable (fun p : E3 × E3 => Work.BoseBoxFock.PV e (x i) p.2) :=
        (PV_weak_measurable_snd hmeas (x i)).comp measurable_snd
      have h3 : Measurable (fun p : E3 × E3 =>
          Θ (Function.update (Function.update x i p.2) j p.1)) :=
        hΘm.comp (Work.BoseBoxFock.measurable_update_update x j i)
      exact (h1.mul (h2.mul h3)).aestronglyMeasurable
    · intro p
      change ‖star (e l' p.1) * (Work.BoseBoxFock.PV e (x i) p.2 *
        Θ (Function.update (Function.update x i p.2) j p.1))‖ ≤ max Ce 0 * (K * max CΘ 0)
      rw [norm_mul, norm_star, norm_mul]
      exact mul_le_mul ((hCe p.1).trans (le_max_left _ _))
        (mul_le_mul (hK (x i) p.2) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hK0)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (le_max_right _ _)
    · intro p hp
      change star (e l' p.1) * (Work.BoseBoxFock.PV e (x i) p.2 *
        Θ (Function.update (Function.update x i p.2) j p.1)) = 0
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hz : e l' p.1 = 0 := by
          by_contra hne
          exact hp (hsupp l' (Function.mem_support.mpr hne))
        rw [hz, star_zero, zero_mul]
      · rw [Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp hp, zero_mul, mul_zero]
  have hInt : Integrable (Function.uncurry (fun z w : E3 => star (e l' z) *
      (Work.BoseBoxFock.PV e (x i) w *
        Θ (Function.update (Function.update x i w) j z)))) (volume.prod volume) := by
    have huncurry : Function.uncurry (fun z w : E3 => star (e l' z) *
        (Work.BoseBoxFock.PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)))
        = (fun p : E3 × E3 => star (e l' p.1) *
            (Work.BoseBoxFock.PV e (x i) p.2 *
              Θ (Function.update (Function.update x i p.2) j p.1))) := by
      funext p
      obtain ⟨a, b⟩ := p
      rfl
    rw [huncurry]
    exact hpair
  have hswap := MeasureTheory.integral_integral_swap hInt
  -- left-hand side, reduced to the `z`-outer double integral
  have hL : (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
        (Work.BoseBoxFock.slotProj1 e i Θ)) x
      = e l (x j) * ∫ z : E3, ∫ w : E3, star (e l' z) * (Work.BoseBoxFock.PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)) := by
    rw [boxSlotOf_evec_apply_bdd]
    have h2 : (fun z : E3 => star (e l' z) *
          Work.BoseBoxFock.slotProj1 e i Θ (Function.update x j z))
        = fun z : E3 => ∫ w : E3, star (e l' z) * (Work.BoseBoxFock.PV e (x i) w *
            Θ (Function.update (Function.update x i w) j z)) := by
      funext z
      rw [Work.BoseBoxFock.slotProj1]
      simp only [Function.update_of_ne hij, Function.update_comm (Ne.symm hij)]
      rw [← MeasureTheory.integral_const_mul]
    rw [h2]
  -- right-hand side, reduced to the `w`-outer double integral
  have hR : (Work.BoseBoxFock.slotProj1 e i
        (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)) x
      = e l (x j) * ∫ w : E3, ∫ z : E3, star (e l' z) * (Work.BoseBoxFock.PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)) := by
    rw [Work.BoseBoxFock.slotProj1]
    have h2 : (fun w : E3 => Work.BoseBoxFock.PV e (x i) w *
          (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
            (Function.update x i w))
        = fun w : E3 => e l (x j) * (Work.BoseBoxFock.PV e (x i) w *
            ∫ z : E3, star (e l' z) *
              Θ (Function.update (Function.update x i w) j z)) := by
      funext w
      simp only [boxSlotOf_evec_apply_bdd, Function.update_of_ne (Ne.symm hij)]
      ring
    rw [h2, MeasureTheory.integral_const_mul]
    have h3 : (∫ w : E3, Work.BoseBoxFock.PV e (x i) w * ∫ z : E3, star (e l' z) *
          Θ (Function.update (Function.update x i w) j z))
        = ∫ w : E3, ∫ z : E3, star (e l' z) * (Work.BoseBoxFock.PV e (x i) w *
            Θ (Function.update (Function.update x i w) j z)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      ring
    rw [h3]
  have hmid : e l (x j) * (∫ z : E3, ∫ w : E3, star (e l' z) *
        (Work.BoseBoxFock.PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)))
      = e l (x j) * (∫ w : E3, ∫ z : E3, star (e l' z) *
        (Work.BoseBoxFock.PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z))) := by
    rw [hswap]
  exact hL.trans (hmid.trans hR.symm)

/-- The slot operators `boxSlotOf e (evec l) (evec l') j` commute with, and are absorbed by, the
one-slot projections `slotProj1 e i`, for weak (measurable, everywhere bounded, box supported)
modes.  Mirror of `Work.BoseBoxFock.boxSlotOf_slotProj1_self`,
`Work.BoseBoxFock.slotProj1_boxSlotOf_self` and `Work.BoseBoxFock.boxSlotOf_slotProj1_comm`, which
need `Continuous`/`HasCompactSupport` modes; here the Fubini integrands are bounded and pointwise
supported in `boxL ℓ × boxL ℓ` of finite measure, so the weak version replaces the continuity
integrability arguments by `Work.MB.integrable_of_bdd_of_support` (in
`Submission.Work.MB.SlotWeakBase`) together with `Work.MB.PV_weak_bound`, `Work.MB.etaOf_weak_*`,
`Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL` (and its first-variable twin
`Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL_fst`).  The one-variable kernel computations are
`Work.BoseBoxFock.integral_PV_mul_PV` (needs `horth` and `hint`) and
`Work.BoseBoxFock.integral_PV_mul_eq_sum`; `etaOf e (evec m l) = e l` is
`Work.BoseBoxFock.etaOf_evec_self`. -/
theorem boxSlotOf_slotProj1_bdd {m d : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    {Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    (∀ (l l' : Fin m) (j : Fin d),
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
            (Work.BoseBoxFock.slotProj1 e j Θ)
          = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
    (∀ (l l' : Fin m) (j : Fin d),
        Work.BoseBoxFock.slotProj1 e j
            (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
          = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
    (∀ (l l' : Fin m) (i j : Fin d), i ≠ j →
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
            (Work.BoseBoxFock.slotProj1 e i Θ)
          = Work.BoseBoxFock.slotProj1 e i
              (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)) ∧
    (∀ (l l' : Fin m) (j : Fin d),
        Measurable (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ ≤ C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact boxSlotOf_slotProj1_self_bdd hmeas hbdd hsupp horth hint hΘm hΘb
  · exact slotProj1_boxSlotOf_self_bdd hmeas hbdd hsupp horth hint hΘm hΘb
  · exact boxSlotOf_slotProj1_comm_bdd hmeas hbdd hsupp horth hint hΘm hΘb
  · intro l l' j
    obtain ⟨hm, hb⟩ := boxSlotOf_measurable_bounded_weak hmeas hbdd hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘm hΘb
    refine ⟨hm, ?_⟩
    obtain ⟨C, hC⟩ := hb
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

end

end Work.MB
