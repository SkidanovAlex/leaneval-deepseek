import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotInt_peel
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.slotProj_peel_ae`

The slot projection `slotProj e S Ψ x = ∫ z, (∏_{i∈S} PV e (x i) (z i)) · Ψ (x[S ↦ z])`
(`SlotProjDefs`) satisfies the peel identity

`slotProj e (insert i U) Ψ =ᵐ slotProj1 e i (slotProj e U Ψ)`,   `i ∉ U`,

for a state that is only `L^∞` (`MemLp Ψ ⊤`) and modes that are only `L^∞` and supported in
the box `boxL ℓ`.  The a.e. qualifier is essential: the Bochner integral of a non-integrable
integrand is the junk value `0`, and the slot integrand of an `L^∞` state is only honest
off a null set of configurations.

The proof has three parts.

* **`slotProj_peel_bdd`** — the identity is *pointwise* for an everywhere bounded measurable
  state `g`: the joint integrand on the product space `(↑U → Ω) × Ω` is integrable by
  `integrable_slotKernel_joint` (the `(U ∪ {i})`-slot integrand of
  `integrable_slotKernel_finset`, transported along the measure preserving splitting `Eeq`),
  and `MeasureTheory.integral_prod_symm` exchanges the two integrations.
* **`slotProj1_ae_eq_congr`** — `slotProj1 e i` is insensitive to null modifications, exactly
  as `slotProj_ae_eq_congr` is, the insertion map `(x,w) ↦ update x i w` being
  quasi-measure-preserving (`updateFinset_qmp` at the singleton `{i}`, transported along
  `MeasurableEquiv.funUnique`).
* the target follows by replacing `Ψ` by an everywhere bounded strongly measurable
  representative (`exists_bdd_sm_repr_aux`) and transporting along the two a.e. equalities.

Everything is built on the existing infrastructure of `SlotProjAux` (`Eeq`, `prod_Eeq`,
`updateFinset_Eeq`), `slotProj_adjoint` (`slotSwapMeas`), `slotProj_finsetSum_ae`
(`updateFinset_qmp`, `slotProj_ae_eq_congr`, `integrable_slotKernel_finset`,
`exists_bdd_sm_repr_aux`) and `slotInt_measurable_bounded` (`measurable_updateFinset_pair`).
-/

/-! ## 1. Elementary helpers -/

/-- If every mode `e l` is a.e. bounded by `M l`, then on the configuration space `ι → Ω` the
values of the modes at *all* slots are a.e. bounded by the same constants. -/
theorem ae_forall_eval_le {ι : Type*} [Fintype ι] {m : ℕ} {e : Fin m → Ω → ℂ}
    {M : Fin m → ℝ} (hM : ∀ l, ∀ᵐ y ∂(volume : Measure Ω), ‖e l y‖ ≤ M l) :
    ∀ᵐ x ∂(volume : Measure (ι → Ω)), ∀ (l : Fin m) (i : ι), ‖e l (x i)‖ ≤ M l := by
  rw [Filter.eventually_all]
  intro l
  rw [Filter.eventually_all]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => (volume : Measure Ω)) (i := i)).eventually
    (hM l)

/-- Overwriting the singleton slot `{i}` with the constant fibre `fun _ ↦ w` is the update of the
slot `i` by `w`. -/
theorem updateFinset_singleton_eq_update {N : ℕ} (i : Fin N) (x : Fin N → Ω) (w : Ω) :
    Function.updateFinset x ({i} : Finset (Fin N))
      (fun _ : ↥({i} : Finset (Fin N)) => w) = Function.update x i w := by
  funext j
  rw [Function.updateFinset_def, Function.update_apply]
  simp only [Finset.mem_singleton]
  by_cases hj : j = i <;> simp [hj]

/-- The inverse of the `Unique`-function-space equivalence is the constant function. -/
theorem funUnique_symm_apply_singleton {N : ℕ} (i : Fin N) (w : Ω) :
    (MeasurableEquiv.funUnique (↥({i} : Finset (Fin N))) Ω).symm w = fun _ => w := by
  funext z
  simp [MeasurableEquiv.funUnique_symm_apply]

/-! ## 2. The single-slot insertion map is quasi-measure-preserving -/

/-- The single-slot insertion map `(x,w) ↦ update x i w` is quasi-measure-preserving: it is
`updateFinset` at the singleton `{i}`, composed with the measure preserving identification
`Ω ≃ᵐ Ω^{↥{i}}`. -/
theorem qmp_update_single {N : ℕ} (i : Fin N) :
    Measure.QuasiMeasurePreserving (fun p : (Fin N → Ω) × Ω => Function.update p.1 i p.2)
      (volume : Measure ((Fin N → Ω) × Ω)) (volume : Measure (Fin N → Ω)) := by
  have h1 : (fun p : (Fin N → Ω) × Ω => Function.update p.1 i p.2)
      = (fun p : (Fin N → Ω) × (↥({i} : Finset (Fin N)) → Ω) =>
          Function.updateFinset p.1 ({i} : Finset (Fin N)) p.2) ∘
        (fun p : (Fin N → Ω) × Ω =>
          (p.1, (MeasurableEquiv.funUnique (↥({i} : Finset (Fin N))) Ω).symm p.2)) := by
    funext p
    simp only [Function.comp_apply]
    rw [funUnique_symm_apply_singleton i p.2]
    exact (updateFinset_singleton_eq_update i p.1 p.2).symm
  rw [h1]
  have hqmp : Measure.QuasiMeasurePreserving
      (fun p : (Fin N → Ω) × Ω =>
        (p.1, (MeasurableEquiv.funUnique (↥({i} : Finset (Fin N))) Ω).symm p.2))
      (volume : Measure ((Fin N → Ω) × Ω))
      (volume : Measure ((Fin N → Ω) × (↥({i} : Finset (Fin N)) → Ω))) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (volume : Measure (Fin N → Ω)))
      ((MeasurePreserving.symm (MeasurableEquiv.funUnique (↥({i} : Finset (Fin N))) Ω)
        (volume_preserving_funUnique _ Ω)).quasiMeasurePreserving)
  exact (updateFinset_qmp ({i} : Finset (Fin N))).comp hqmp

/-! ## 3. Insensitivity of `slotProj1` to null modifications -/

/-- **`slotProj1 e i` is insensitive to null modifications of the state.**  No hypothesis on the
modes is needed: the argument is `integral_congr_ae` applied to the a.e. equality of the
integrands, which follows from the fact that a null set of configurations pulls back to a null
set of the product measure along the single-slot insertion map (`qmp_update_single`), plus
Fubini. -/
theorem slotProj1_ae_eq_congr_aux {m N : ℕ} (e : Fin m → Ω → ℂ) (i : Fin N)
    {f g : (Fin N → Ω) → ℂ} (h : f =ᵐ[(volume : Measure (Fin N → Ω))] g) :
    slotProj1 e i f =ᵐ[(volume : Measure (Fin N → Ω))] slotProj1 e i g := by
  have hae : ∀ᵐ p ∂(volume : Measure ((Fin N → Ω) × Ω)),
      f (Function.update p.1 i p.2) = g (Function.update p.1 i p.2) :=
    (qmp_update_single i).ae h
  have hiter := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hiter] with x hx
  rw [slotProj1]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hx] with w hw
  rw [hw]

/-! ## 4. The joint slot kernel of a bounded measurable state is integrable -/

/-- **Integrability of the peeled joint kernel.**  For an everywhere bounded measurable state `g`,
the integrand on the product space `(↑U → Ω) × Ω` of the peel identity is integrable: it is the
`(U ∪ {i})`-slot integrand of `integrable_slotKernel_finset` transported along the measure
preserving splitting `Eeq hi`. -/
theorem integrable_slotKernel_joint {m N : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin N)} {i : Fin N} (hi : i ∉ U)
    {g : (Fin N → Ω) → ℂ} (hgm : Measurable g) {C : ℝ} (hgb : ∀ y, ‖g y‖ ≤ C)
    (x : Fin N → Ω) :
    Integrable (fun q : (↑U → Ω) × Ω =>
      (∏ u : ↑U, PV e (x u.1) (q.1 u)) * (PV e (x i) q.2 *
        g (Function.update (Function.updateFinset x U q.1) i q.2)))
      (volume : Measure ((↑U → Ω) × Ω)) := by
  have h1 : Integrable (fun w : ↑(U ∪ {i}) → Ω =>
      (∏ u : ↑(U ∪ {i}), PV e (x u.1) (w u)) * g (Function.updateFinset x (U ∪ {i}) w))
      (volume : Measure (↑(U ∪ {i}) → Ω)) :=
    integrable_slotKernel_finset (B := Work.BoseK15.corpusBox) e (U ∪ {i}) hbdd hsupp hgm hgb
  have hmp := Eeq_measurePreserving (S := U) (i := i) hi
  have h2 : Integrable (fun q : (↑U → Ω) × Ω =>
      (∏ u : ↑(U ∪ {i}), PV e (x u.1) ((Eeq (S := U) (i := i) hi) q u)) *
        g (Function.updateFinset x (U ∪ {i}) ((Eeq (S := U) (i := i) hi) q)))
      (volume : Measure ((↑U → Ω) × Ω)) :=
    (hmp.integrable_comp_emb (Eeq (S := U) (i := i) hi).measurableEmbedding).mpr h1
  refine h2.congr ?_
  filter_upwards with q
  obtain ⟨q1, q2⟩ := q
  show (∏ u : ↑(U ∪ {i}), PV e (x u.1) ((Eeq (S := U) (i := i) hi) (q1, q2) u)) *
        g (Function.updateFinset x (U ∪ {i}) ((Eeq (S := U) (i := i) hi) (q1, q2))) =
      (∏ u : ↑U, PV e (x u.1) (q1 u)) * (PV e (x i) q2 *
        g (Function.update (Function.updateFinset x U q1) i q2))
  rw [prod_Eeq e hi x q1 q2, updateFinset_Eeq (S := U) (i := i) hi x q1 q2]
  ring

/-- The measurability of the peeled insertion map (with the configuration `x` fixed). -/
theorem measurable_update_updateFinset {N : ℕ} (x : Fin N → Ω) (U : Finset (Fin N)) (i : Fin N) :
    Measurable (fun q : (↑U → Ω) × Ω =>
      Function.update (Function.updateFinset x U q.1) i q.2) := by
  have hg : Measurable (fun q : (↑U → Ω) × Ω => Function.updateFinset x U q.1) :=
    (measurable_updateFinset_pair U).comp (measurable_const.prodMk measurable_fst)
  refine measurable_pi_iff.mpr (fun j => ?_)
  by_cases hji : j = i
  · have h : (fun q : (↑U → Ω) × Ω =>
        Function.update (Function.updateFinset x U q.1) i q.2 j) = fun q => q.2 := by
      funext q
      rw [Function.update_apply, if_pos hji]
    rw [h]
    exact measurable_snd
  · have h : (fun q : (↑U → Ω) × Ω =>
        Function.update (Function.updateFinset x U q.1) i q.2 j)
        = fun q => Function.updateFinset x U q.1 j := by
      funext q
      rw [Function.update_of_ne hji]
    rw [h]
    exact (measurable_pi_apply j).comp hg

/-- **The peel identity for an everywhere bounded measurable state** (pointwise in `x`). -/
theorem slotProj_peel_bdd {m N : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin N)} {i : Fin N} (hi : i ∉ U)
    {g : (Fin N → Ω) → ℂ} (hgm : Measurable g) {C : ℝ} (hgb : ∀ y, ‖g y‖ ≤ C) :
    slotProj e (insert i U) g = slotProj1 e i (slotProj e U g) := by
  funext x
  have hUW : (insert i U : Finset (Fin N)) = U ∪ {i} := (Finset.union_singleton i U).symm
  rw [hUW, slotProj_eq_slotInt, slotProj_eq_slotInt_fun e U g]
  have hInt : Integrable (fun q : (↑U → Ω) × Ω =>
      (∏ u : ↑U, PV e (x u.1) (q.1 u)) * (PV e (x i) q.2 *
        g (Function.update (Function.updateFinset x U q.1) i q.2)))
      (volume : Measure ((↑U → Ω) × Ω)) :=
    integrable_slotKernel_joint hbdd hsupp hi hgm hgb x
  have hL : slotInt e (U ∪ {i}) g x = ∫ q : (↑U → Ω) × Ω,
      (∏ u : ↑U, PV e (x u.1) (q.1 u)) * (PV e (x i) q.2 *
        g (Function.update (Function.updateFinset x U q.1) i q.2)) := by
    have h1 : slotInt e (U ∪ {i}) g x = ∫ w : ↑(U ∪ {i}) → Ω,
        (∏ u : ↑(U ∪ {i}), PV e (x u.1) (w u)) * g (Function.updateFinset x (U ∪ {i}) w) :=
      rfl
    rw [h1, ← (Eeq_measurePreserving (S := U) (i := i) hi).integral_comp
      ((Eeq (S := U) (i := i) hi).measurableEmbedding)
      (fun w : ↑(U ∪ {i}) → Ω =>
        (∏ u : ↑(U ∪ {i}), PV e (x u.1) (w u)) * g (Function.updateFinset x (U ∪ {i}) w))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨q1, q2⟩ := q
    show (∏ u : ↑(U ∪ {i}), PV e (x u.1) ((Eeq (S := U) (i := i) hi) (q1, q2) u)) *
        g (Function.updateFinset x (U ∪ {i}) ((Eeq (S := U) (i := i) hi) (q1, q2))) =
      (∏ u : ↑U, PV e (x u.1) (q1 u)) * (PV e (x i) q2 *
        g (Function.update (Function.updateFinset x U q1) i q2))
    rw [prod_Eeq e hi x q1 q2, updateFinset_Eeq (S := U) (i := i) hi x q1 q2]
    ring
  have hR : slotProj1 e i (slotInt e U g) x = ∫ w : Ω, ∫ z' : ↑U → Ω,
      (∏ u : ↑U, PV e (x u.1) (z' u)) * (PV e (x i) w *
        g (Function.update (Function.updateFinset x U z') i w)) := by
    rw [slotProj1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [slotInt]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)
    show PV e (x i) w * ((∏ u : ↑U, PV e (Function.update x i w u.1) (z' u)) *
        g (Function.updateFinset (Function.update x i w) U z')) =
      (∏ u : ↑U, PV e (x u.1) (z' u)) * (PV e (x i) w *
        g (Function.update (Function.updateFinset x U z') i w))
    rw [Finset.prod_congr rfl (fun u _ => by
        rw [Function.update_of_ne (show u.1 ≠ i from fun h => hi (h ▸ u.2))]),
      updateFinset_update_eq (S := U) (i := i) hi x z' w]
    ring
  have hFub : (∫ q : (↑U → Ω) × Ω, (∏ u : ↑U, PV e (x u.1) (q.1 u)) * (PV e (x i) q.2 *
        g (Function.update (Function.updateFinset x U q.1) i q.2)))
      = ∫ w : Ω, ∫ z' : ↑U → Ω, (∏ u : ↑U, PV e (x u.1) (z' u)) * (PV e (x i) w *
        g (Function.update (Function.updateFinset x U z') i w)) :=
    MeasureTheory.integral_prod_symm _ hInt
  rw [hL, hFub, hR]

/-! ## 5. The target -/

theorem slotProj_peel_ae {m N : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {U : Finset (Fin N)} {i : Fin N} (hi : i ∉ U)
    {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΨ : MeasureTheory.MemLp Ψ ⊤) :
    (fun x => Work.BoseBoxFock.slotProj e (insert i U) Ψ x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3)))]
      (fun x => Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotProj e U Ψ) x) := by
  classical
  obtain ⟨g, C, hCnn, hCb, hgsm, hgeq⟩ :=
    exists_bdd_sm_repr_aux (volume : Measure (Fin N → Ω)) hΨ
  have hpeel : slotProj e (insert i U) g = slotProj1 e i (slotProj e U g) :=
    slotProj_peel_bdd hbdd hsupp hi hgsm.measurable hCb
  have h1 : (fun x => slotProj e (insert i U) Ψ x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => slotProj e (insert i U) g x) :=
    slotProj_ae_eq_congr e (insert i U) hgeq
  have h2 : (fun x => slotProj e (insert i U) g x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => slotProj1 e i (slotProj e U g) x) :=
    Filter.Eventually.of_forall (fun x => congrFun hpeel x)
  have h3 : (fun x => slotProj1 e i (slotProj e U g) x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => slotProj1 e i (slotProj e U Ψ) x) :=
    slotProj1_ae_eq_congr_aux e i (slotProj_ae_eq_congr e U hgeq.symm)
  exact h1.trans (h2.trans h3)

end Work.BoseBoxFock
