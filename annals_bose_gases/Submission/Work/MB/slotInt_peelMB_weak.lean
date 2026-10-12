import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.slotInt_peelMB_weak` — the peel identity in the weak (measurable/bounded) class

This is the measurable/bounded twin of `Work.BoseBoxFock.slotInt_peelMB`
(`Submission/Work/BoseBoxFock/slotInt_peelMB.lean`), which proves the same identity for a mode
family that is *continuous* with *compact support*.  The weak class substitutes

* `Continuous (e l)` by `Measurable (e l)`,
* `HasCompactSupport (e l)` by `∃ C, ∀ x, ‖e l x‖ ≤ C` together with the box support
  `Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ`,
* `Continuous Φ` / `HasCompactSupport Φ` by `Measurable Φ` / `∃ C, ∀ y, ‖Φ y‖ ≤ C`,

which is exactly the class of the honest modes of the box ↔ model bridge (the strong hypotheses
are *unsatisfiable* there, see `FINDING_continuous_hypotheses_UNSATISFIABLE.md`).

The proof is the same: change variables along the measure preserving splitting
`Eeq hi : (↑S → Ω) × Ω ≃ᵐ ↑(S ∪ {i}) → Ω` (`Eeq_measurePreserving`), rewrite the kernel product
and the configuration with `prod_Eeq` / `updateFinset_Eeq`, and exchange the two integrations with
`integral_prod_symm` (Fubini).  The only change is *how* the integrability of the slot integrand is
obtained:

* `Work.MB.integrable_slotKernel_weak` (proved below) — the slot integrand
  `z ↦ (∏ i : ↑U, PV e (x i.1) (z i)) · G (updateFinset x U z)` of a *measurable, bounded* state
  `G` is integrable: it is measurable, bounded, and supported in the product of boxes
  `Set.univ.pi (fun _ : ↑U => boxL ℓ)`, which has finite measure
  (`Work.MB.volume_univ_pi_boxL_ne_top`).  This replaces the continuous/compactly supported
  argument `Work.BoseBoxFock.integrable_mul_of_continuous_hasCompactSupport_of_bounded`.
* the `Integrable` statement on the product space `(↑S → Ω) × Ω` is then the transport of the
  `↑(S ∪ {i})`-slot integrand along the measure preserving `Eeq hi`
  (`MeasurePreserving.integrable_comp_emb`), and Fubini (`MeasureTheory.integral_prod_symm`)
  finishes.

No orthonormality of the modes, and no continuity, are used.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- The product of the corpus boxes `boxL ℓ` over an arbitrary finite index type has finite
volume. -/
theorem volume_univ_pi_boxL_ne_top {ι : Type*} [Fintype ι] (ℓ : ℝ) :
    (volume : Measure (ι → Ω))
      (Set.univ.pi (fun _ : ι => Work.BoseK15.corpusBox.boxL ℓ)) ≠ ⊤ := by
  have h : (volume : Measure (ι → Ω)) = Measure.pi (fun _ : ι => (volume : Measure Ω)) :=
    volume_pi
  rw [h, Measure.pi_pi]
  exact ENNReal.prod_ne_top fun i _ =>
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne

/-- **Integrability of the slot integrand in the weak class.**  For a measurable, everywhere
bounded, box supported mode family `e`, a configuration `x`, and a measurable, everywhere bounded
state `G`, the `U`-slot integrand

`z ↦ (∏ i : ↑U, PV e (x i.1) (z i)) * G (Function.updateFinset x U z)`

is integrable.  It is measurable, bounded, and supported in the product of the boxes
`Set.univ.pi (fun _ : ↑U => boxL ℓ)`, of finite measure. -/
theorem integrable_slotKernel_weak {m : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι : Type*} [DecidableEq ι] (U : Finset ι) (x : ι → Ω)
    {G : (ι → Ω) → ℂ} (hGm : Measurable G) (hGb : ∃ C, ∀ y, ‖G y‖ ≤ C) :
    Integrable (fun z : (↑U → Ω) =>
      (∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) *
        G (Function.updateFinset x U z)) (volume : Measure (↑U → Ω)) := by
  classical
  obtain ⟨K, hK0, hK⟩ := Work.MB.PV_weak_bound hbdE
  obtain ⟨C, hC⟩ := hGb
  have hmeasK : Measurable (fun z : ↑U → Ω =>
      ∏ i : ↑U, Work.BoseBoxFock.PV e (x i.1) (z i)) :=
    Finset.measurable_prod Finset.univ fun i _ =>
      (Work.MB.PV_weak_measurable hmeas).comp
        (measurable_const.prodMk (measurable_pi_apply i))
  have hmeasG : Measurable (fun z : ↑U → Ω => G (Function.updateFinset x U z)) :=
    hGm.comp ((Work.BoseBoxFock.measurable_updateFinset_pair U).comp
      (measurable_const.prodMk (measurable_id : Measurable (fun z : ↑U → Ω => z))))
  refine Work.MB.integrable_of_bdd_of_support
    (S := Set.univ.pi (fun _ : ↑U => Work.BoseK15.corpusBox.boxL ℓ))
    (MeasurableSet.pi Set.countable_univ fun _ _ =>
      Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)
    (volume_univ_pi_boxL_ne_top (ι := ↑U) ℓ)
    (hmeasK.mul hmeasG).aestronglyMeasurable
    (C := K ^ U.card * max C 0) ?_ ?_
  · intro z
    rw [norm_mul, norm_prod]
    refine mul_le_mul ?_ ((hC _).trans (le_max_left C 0)) (norm_nonneg _)
      (pow_nonneg hK0 _)
    calc ∏ i : ↑U, ‖Work.BoseBoxFock.PV e (x i.1) (z i)‖ ≤ ∏ _i : ↑U, K :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hK _ _
      _ = K ^ U.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  · intro z hz
    have hz' : ∃ i : ↑U, z i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
      by_contra h
      exact hz (Set.mem_univ_pi.mpr fun i => not_not.mp (not_exists.mp h i))
    obtain ⟨i, hi⟩ := hz'
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp hi), zero_mul]

/-! ## The peel identity -/

theorem slotInt_peelMB_weak {m : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (Φ : (ι → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    Work.BoseBoxFock.slotInt e (S ∪ {i}) Φ
      = Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotInt e S Φ) := by
  classical
  funext x
  -- the common integrand, written as a function of the `S`-slots and of the extra slot `i`
  let G : (↑S → Ω) → Ω → ℂ := fun z' w =>
    (∏ u : ↑S, Work.BoseBoxFock.PV e (x u.1) (z' u)) *
      (Work.BoseBoxFock.PV e (x i) w *
        Φ (Function.update (Function.updateFinset x S z') i w))
  -- the integrand of `slotInt e (S ∪ {i}) Φ x`, viewed on the `S ∪ {i}`-configuration space
  let g : (↑(S ∪ {i}) → Ω) → ℂ := fun z =>
    (∏ u : ↑(S ∪ {i}), Work.BoseBoxFock.PV e (x u.1) (z u)) *
      Φ (Function.updateFinset x (S ∪ {i}) z)
  have hmp : MeasurePreserving (Work.BoseBoxFock.Eeq hi) (volume : Measure ((↑S → Ω) × Ω))
      (volume : Measure (↑(S ∪ {i}) → Ω)) := Work.BoseBoxFock.Eeq_measurePreserving hi
  have hemb : MeasurableEmbedding (Work.BoseBoxFock.Eeq hi) :=
    (Work.BoseBoxFock.Eeq hi).measurableEmbedding
  -- the two faces of the integrand agree along the splitting equivalence
  have hcomp : ∀ p : (↑S → Ω) × Ω, g (Work.BoseBoxFock.Eeq hi p) = G p.1 p.2 := by
    rintro ⟨z', w⟩
    simp only [g, G]
    rw [Work.BoseBoxFock.prod_Eeq e hi x z' w, Work.BoseBoxFock.updateFinset_Eeq hi x z' w]
    ring
  have hg : Integrable g volume := by
    simpa only [g] using
      integrable_slotKernel_weak hmeas hbdE hsupp (S ∪ {i}) x (G := Φ) hΦm hΦb
  have hInt : Integrable (fun q : (↑S → Ω) × Ω => G q.1 q.2) (volume.prod volume) :=
    ((hmp.integrable_comp_emb hemb).mpr hg).congr (Filter.Eventually.of_forall hcomp)
  -- left-hand side: change of variables along `Eeq`
  have hL : Work.BoseBoxFock.slotInt e (S ∪ {i}) Φ x = ∫ q : (↑S → Ω) × Ω, G q.1 q.2 := by
    have h1 : Work.BoseBoxFock.slotInt e (S ∪ {i}) Φ x = ∫ z : ↑(S ∪ {i}) → Ω, g z := rfl
    rw [h1, ← hmp.integral_comp hemb g]
    exact integral_congr_ae (Filter.Eventually.of_forall hcomp)
  -- right-hand side: expand the inner `slotInt` and pull out the factor of the slot `i`
  have hR : Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotInt e S Φ) x =
      ∫ w : Ω, ∫ z' : ↑S → Ω, G z' w := by
    rw [Work.BoseBoxFock.slotProj1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Work.BoseBoxFock.slotInt]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)
    simp only [G]
    have hprod : (∏ u : ↑S, Work.BoseBoxFock.PV e (Function.update x i w u.1) (z' u))
        = ∏ u : ↑S, Work.BoseBoxFock.PV e (x u.1) (z' u) :=
      Finset.prod_congr rfl fun u _ => by
        rw [Function.update_of_ne (show u.1 ≠ i from fun h => hi (h ▸ u.2))]
    have hcfg : Function.updateFinset (Function.update x i w) S z' =
        Function.update (Function.updateFinset x S z') i w := by
      funext j
      by_cases hj : j ∈ S
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp [Function.updateFinset, Function.update_of_ne hji, hj]
      · by_cases hji : j = i
        · subst hji
          simp [Function.updateFinset, hj]
        · simp [Function.updateFinset, Function.update_of_ne hji, hj]
    rw [hprod, hcfg]
    ring
  -- Fubini: the product integral of `G` as the iterated integral over the last slot first
  rw [hL, hR]
  exact integral_prod_symm (fun q : (↑S → Ω) × Ω => G q.1 q.2) hInt

end Work.MB
