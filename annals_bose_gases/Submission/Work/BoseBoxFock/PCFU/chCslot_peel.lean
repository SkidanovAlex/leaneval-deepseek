import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.CslotPairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chCslot_peel`

The measure-theoretic splitting identity behind the `(C)`-alias-slot estimate.

For `i ≠ j` the map `(w, w', x') ↦ chCcfg i j w w' x'` (write `w` into slot `i`, `w'` into slot
`j`, keep `x'` elsewhere) is a measure-preserving bijection
`E3 × E3 × ({k // k ≠ i ∧ k ≠ j} → E3) ≃ X n`, and the peel identities

    ∫_x F x = ∫_{x'} ∫_w ∫_{w'} F (chCcfg i j w w' x')

are recorded here in the order in which the slot estimate consumes them (`w'` innermost, so that
its integral collapses against the state).  Both the Bochner (`Integrable F`) and the `∫⁻`
(`Measurable G`) forms are provided; the `∫⁻` form needs the measurability hypothesis, without
which the identity is false (`lintegral_prod` is the only Mathlib tool converting a product
integral into an iterated one).
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {n : ℕ} {i j : Fin n}

/-- The product splitting of `Fin n` at the two slots `i ≠ j`. -/
lemma prod_univ_slots {i j : Fin n} (hij : i ≠ j) (f : Fin n → ENNReal) :
    ∏ k : Fin n, f k = (∏ k : {k : Fin n // k ≠ i ∧ k ≠ j}, f k.1) * (f i * f j) := by
  classical
  have h1 : (Finset.univ : Finset (Fin n)).prod f
      = (Finset.univ.filter (fun k : Fin n => k ≠ i ∧ k ≠ j)).prod f
        * (Finset.univ.filter (fun k : Fin n => ¬ (k ≠ i ∧ k ≠ j))).prod f :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
      (fun k : Fin n => k ≠ i ∧ k ≠ j) f).symm
  have h2 : (Finset.univ.filter (fun k : Fin n => k ≠ i ∧ k ≠ j)).prod f
      = ∏ k : {k : Fin n // k ≠ i ∧ k ≠ j}, f k.1 :=
    Finset.prod_subtype _ (fun k => by simp) f
  have h3 : (Finset.univ.filter (fun k : Fin n => ¬ (k ≠ i ∧ k ≠ j))).prod f
      = f i * f j := by
    have hset : Finset.univ.filter (fun k : Fin n => ¬ (k ≠ i ∧ k ≠ j))
        = ({i, j} : Finset (Fin n)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        by_contra hc
        push Not at hc
        exact h ⟨hc.1, hc.2⟩
      · rintro (rfl | rfl)
        · intro h; exact h.1 rfl
        · intro h; exact h.2 rfl
    rw [hset, Finset.prod_pair hij]
  rw [h1, h2, h3]

/-- The `(i,j)`-slot splitting map, with the remaining coordinates on the outside. -/
def chCsplit {n : ℕ} (i j : Fin n) :
    (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 → Submission.BoseGases.X n :=
  fun p => chCcfg i j p.1.2 p.2 p.1.1

/-- The product measure on the domain of `chCsplit`. -/
def chCdom {n : ℕ} (i j : Fin n) :
    Measure ((({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3) :=
  (((volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))).prod (volume : Measure E3)).prod
    (volume : Measure E3)

@[simp] lemma chCsplit_apply {i j : Fin n}
    (p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3) :
    chCsplit i j p = chCcfg i j p.1.2 p.2 p.1.1 := rfl

lemma chCsplit_measurable (i j : Fin n) : Measurable (chCsplit i j) := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hki : k = i
  · rw [show (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
        chCsplit i j p k) = fun p => p.1.2 from by
      funext p; simp only [chCsplit_apply, chCcfg, dif_pos hki]]
    exact measurable_snd.comp measurable_fst
  · by_cases hkj : k = j
    · rw [show (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
          chCsplit i j p k) = fun p => p.2 from by
        funext p; simp only [chCsplit_apply, chCcfg, dif_neg hki, dif_pos hkj]]
      exact measurable_snd
    · rw [show (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
          chCsplit i j p k) = fun p => p.1.1 ⟨k, hki, hkj⟩ from by
        funext p; simp only [chCsplit_apply, chCcfg, dif_neg hki, dif_neg hkj]]
      exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)

lemma chCsplit_preimage {i j : Fin n} (hij : i ≠ j) (s : Fin n → Set E3) :
    chCsplit i j ⁻¹' Set.univ.pi s
      = ((Set.univ.pi (fun k : {k : Fin n // k ≠ i ∧ k ≠ j} => s k.1)) ×ˢ (s i)) ×ˢ (s j) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, chCsplit_apply]
  constructor
  · intro h
    refine ⟨⟨fun k => ?_, ?_⟩, ?_⟩
    · have hk := h k.1
      rw [chCcfg_other (i := i) (j := j) (k := k.1) p.1.2 p.2 p.1.1 k.2.1 k.2.2] at hk
      exact hk
    · simpa using h i
    · have hhj := h j
      rw [chCcfg_j hij] at hhj
      exact hhj
  · rintro ⟨⟨h1, h2⟩, h3⟩ k
    by_cases hki : k = i
    · rw [hki]; simpa using h2
    · by_cases hkj : k = j
      · rw [hkj, chCcfg_j hij]
        exact h3
      · rw [chCcfg_other (i := i) (j := j) (k := k) p.1.2 p.2 p.1.1 hki hkj]
        exact h1 ⟨k, hki, hkj⟩

lemma chCcfg_map {i j : Fin n} (hij : i ≠ j) :
    Measure.map (chCsplit i j) (chCdom i j) = (volume : Measure (Submission.BoseGases.X n)) := by
  classical
  have hT : Measurable (chCsplit (n := n) i j) := chCsplit_measurable i j
  have key : Measure.map (chCsplit i j) (chCdom i j)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3)) := by
    refine (Measure.pi_eq (fun s hs => ?_)).symm
    rw [Measure.map_apply hT (MeasurableSet.univ_pi hs), chCsplit_preimage hij]
    show (chCdom i j)
        (((Set.univ.pi (fun k : {k : Fin n // k ≠ i ∧ k ≠ j} => s k.1)) ×ˢ (s i)) ×ˢ (s j))
      = ∏ k : Fin n, (volume : Measure E3) (s k)
    rw [chCdom, Measure.prod_prod, Measure.prod_prod]
    rw [show (volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))
        = Measure.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => (volume : Measure E3)) from rfl]
    rw [Measure.pi_pi, prod_univ_slots hij]
    rw [mul_assoc]
  rw [key]
  rfl

theorem chCcfg_measurePreserving {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (chCsplit i j) (chCdom i j)
      (volume : Measure (Submission.BoseGases.X n)) :=
  ⟨chCsplit_measurable i j, chCcfg_map hij⟩

theorem chCcfg_lintegral_peel {i j : Fin n} (hij : i ≠ j)
    {G : Submission.BoseGases.X n → ENNReal} (hG : Measurable G) :
    (∫⁻ x : Submission.BoseGases.X n, G x)
      = ∫⁻ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3),
          ∫⁻ w : E3, ∫⁻ w' : E3, G (chCcfg i j w w' x') := by
  classical
  have hmp := chCcfg_measurePreserving (i := i) (j := j) hij
  rw [← hmp.lintegral_comp hG]
  have hA : AEMeasurable (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
      G (chCsplit i j p)) (chCdom i j) :=
    (hG.comp (chCsplit_measurable i j)).aemeasurable
  have hq : Measurable (fun q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3 =>
      ∫⁻ w' : E3, G (chCsplit i j (q, w')) ∂(volume : Measure E3)) := by
    refine Measurable.lintegral_prod_right
      (ν := (volume : Measure E3))
      (f := fun q (w' : E3) => G (chCsplit i j (q, w'))) ?_
    show Measurable (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
      G (chCsplit i j p))
    exact hG.comp (chCsplit_measurable i j)
  rw [show (∫⁻ p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3,
        G (chCsplit i j p) ∂(chCdom i j))
      = ∫⁻ q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3, ∫⁻ w' : E3,
          G (chCsplit i j (q, w')) ∂(volume : Measure E3)
          ∂((volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)).prod
            (volume : Measure E3)) from by
    rw [chCdom]
    exact lintegral_prod _ hA]
  rw [show (∫⁻ q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3, ∫⁻ w' : E3,
        G (chCsplit i j (q, w')) ∂(volume : Measure E3)
          ∂((volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)).prod (volume : Measure E3)))
      = ∫⁻ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3), ∫⁻ w : E3, ∫⁻ w' : E3,
          G (chCcfg i j w w' x') from by
    rw [lintegral_prod _ hq.aemeasurable]
    refine lintegral_congr fun x' => ?_
    refine lintegral_congr fun w => ?_
    refine lintegral_congr fun w' => ?_
    rw [chCsplit_apply]]

theorem chCcfg_integral_peel {i j : Fin n} (hij : i ≠ j) {F : Submission.BoseGases.X n → ℂ}
    (hF : Integrable F (volume : Measure (Submission.BoseGases.X n))) :
    (∫ x : Submission.BoseGases.X n, F x)
      = ∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3),
          ∫ w : E3, ∫ w' : E3, F (chCcfg i j w w' x') := by
  classical
  have hmp := chCcfg_measurePreserving (i := i) (j := j) hij
  have hInt : Integrable (fun p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3 =>
      F (chCsplit i j p)) (chCdom i j) :=
    (hmp.integrable_comp hF.aestronglyMeasurable).mpr hF
  have h1 : (∫ x : Submission.BoseGases.X n, F x)
      = ∫ p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3, F (chCsplit i j p)
          ∂(chCdom i j) := by
    rw [show (∫ x : Submission.BoseGases.X n, F x)
        = ∫ x, F x ∂(Measure.map (chCsplit i j) (chCdom i j)) from by rw [hmp.map_eq]]
    exact integral_map hmp.aemeasurable (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
  have h2 : (∫ p : (({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3) × E3, F (chCsplit i j p)
        ∂(chCdom i j))
      = ∫ q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3, ∫ w' : E3,
          F (chCsplit i j (q, w')) ∂(volume : Measure E3)
          ∂((volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)).prod
            (volume : Measure E3)) := by
    rw [chCdom]
    exact integral_prod _ hInt
  have h3 : (∫ q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3, ∫ w' : E3,
        F (chCsplit i j (q, w')) ∂(volume : Measure E3)
          ∂((volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)).prod (volume : Measure E3)))
      = ∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3), ∫ w : E3, ∫ w' : E3,
          F (chCcfg i j w w' x') := by
    have hI2 : Integrable (fun q : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) × E3 => ∫ w' : E3,
        F (chCsplit i j (q, w')) ∂(volume : Measure E3))
        ((volume : Measure ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)).prod (volume : Measure E3)) :=
      Integrable.integral_prod_left hInt
    rw [integral_prod _ hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
    beta_reduce
    rw [chCsplit_apply]
  rw [h1, h2, h3]

theorem chCcfg_integral_peel_real {i j : Fin n} (hij : i ≠ j) {f : Submission.BoseGases.X n → ℝ}
    (hf : Integrable f (volume : Measure (Submission.BoseGases.X n))) :
    (∫ x : Submission.BoseGases.X n, f x)
      = ∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3),
          ∫ w : E3, ∫ w' : E3, f (chCcfg i j w w' x') := by
  set Fc : Submission.BoseGases.X n → ℂ := fun x => ((f x : ℝ) : ℂ) with hFcdef
  have hFcint : Integrable Fc (volume : Measure (Submission.BoseGases.X n)) := hf.ofReal
  have h := chCcfg_integral_peel (i := i) (j := j) hij hFcint
  have e1 : (∫ x : Submission.BoseGases.X n, Fc x) = ((∫ x : Submission.BoseGases.X n, f x : ℝ) : ℂ) := by
    rw [hFcdef]; exact integral_ofReal
  have e2 : (∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3), ∫ w : E3, ∫ w' : E3,
        Fc (chCcfg i j w w' x'))
      = ((∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3), ∫ w : E3, ∫ w' : E3,
          f (chCcfg i j w w' x') : ℝ) : ℂ) := by
    rw [hFcdef]
    have h1 : ∀ (x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3)) (w : E3),
        (∫ w' : E3, ((f (chCcfg i j w w' x') : ℝ) : ℂ))
          = ((∫ w' : E3, f (chCcfg i j w w' x') : ℝ) : ℂ) := fun x' w => integral_ofReal
    simp only [h1]
    have h2 : ∀ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3),
        (∫ w : E3, ((∫ w' : E3, f (chCcfg i j w w' x') : ℝ) : ℂ))
          = ((∫ w : E3, ∫ w' : E3, f (chCcfg i j w w' x') : ℝ) : ℂ) := fun x' => integral_ofReal
    simp only [h2]
    exact integral_ofReal
  have hh : ((∫ x : Submission.BoseGases.X n, f x : ℝ) : ℂ)
      = ((∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → E3), ∫ w : E3, ∫ w' : E3,
          f (chCcfg i j w w' x') : ℝ) : ℂ) := by
    rw [← e1, h, e2]
  exact Complex.ofReal_injective hh

/-- A bounded, measurable function supported in a set of finite measure is in `L²`. -/
lemma memLp_of_support_bound {E : Type*} [NormedAddCommGroup E] {f : E3 → E} {s : Set E3}
    (hs : MeasurableSet s) (hsf : ∀ x, x ∉ s → f x = 0) (hsfin : (volume : Measure E3) s < ⊤)
    (C : ℝ) (hm : AEStronglyMeasurable f (volume : Measure E3)) (hb : ∀ x, ‖f x‖ ≤ C) :
    MemLp f 2 (volume : Measure E3) := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hsfin⟩
  have hbase : MemLp f 2 ((volume : Measure E3).restrict s) :=
    MemLp.of_bound hm.restrict C (Filter.Eventually.of_forall fun x => hb x)
  have heq : f = s.indicator f := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsf x hx]
  rw [heq]
  exact (memLp_indicator_iff_restrict hs).mpr hbase

/-- `z ↦ chCcfg i j 0 z x'` is measurable. -/
lemma measurable_chCcfg_zero (i j : Fin n)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    Measurable (fun z : E3 => chCcfg i j 0 z x') := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hki : k = i
  · simp only [chCcfg, dif_pos hki]; exact measurable_const
  · by_cases hkj : k = j
    · simp only [chCcfg, dif_neg hki, dif_pos hkj]; exact measurable_id
    · simp only [chCcfg, dif_neg hki, dif_neg hkj]; exact measurable_const

/-- `(w, w') ↦ chCcfg i j w w' x'` is measurable. -/
lemma measurable_chCcfg_pair (i j : Fin n)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    Measurable (fun p : E3 × E3 => chCcfg i j p.1 p.2 x') := by
  classical
  refine measurable_pi_iff.mpr fun k => ?_
  by_cases hki : k = i
  · simp only [chCcfg, dif_pos hki]; exact measurable_fst
  · by_cases hkj : k = j
    · simp only [chCcfg, dif_neg hki, dif_pos hkj]; exact measurable_snd
    · simp only [chCcfg, dif_neg hki, dif_neg hkj]; exact measurable_const

end Work.BoseBoxFock.PCFU
