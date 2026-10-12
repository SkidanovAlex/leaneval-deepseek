import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.style.haveILetI false

/-!
# `Work.BoseBoxFock.lintegral_fibre_two_p`

The `lintegral` (i.e. `ℝ≥0∞`-valued, with no integrability hypothesis) two-slot fibre decomposition
of the configuration-space integral: for a pair of distinct slots `p : Fin n × Fin n`, the integral
over `x : Fin n → ℝ³` equals the iterated integral over the two slot values `w`, `a` and the
remaining configuration `x'' : Fib2 p`, with respect to the measure-preserving equivalence

`((w, a), x'') ↦ upd2 p a w x''`.

This is the `lintegral` analogue of `Work.BoseBoxFock.integral_fibre_two`.  The change of variables
along the measure-preserving equivalence is `MeasurePreserving.lintegral_map_equiv` (which requires
no measurability of the integrand); the two Fubini exchanges are `MeasureTheory.lintegral_prod`.

Care is needed with the *order* of the Fubini exchanges: the equivalence is built with the
association `(w, a, x'') ↦ (E3 × E3) × Fib2` (rather than the nested `E3 × (E3 × Fib2)`) precisely
because the second exchange then needs only the *joint* almost-everywhere measurability of the
partially integrated function (`AEMeasurable.lintegral_prod_right`), not the a.e. measurability of
an individual slice, which is not available.
-/

/-- The one-coordinate peeling equivalence `(ι → E3) ≃ᵐ E3 × ({k // k ≠ a} → E3)`. -/
private def peelEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → E3) ≃ᵐ E3 × ({k : ι // k ≠ a} → E3) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} E3).prodCongr (MeasurableEquiv.refl _))

private theorem peelEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → E3) :
    peelEquiv ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

private theorem peelEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (p : E3 × ({k : ι // k ≠ a} → E3)) :
    (peelEquiv ι a).symm p = fibreIns a p.1 p.2 := by
  refine (Equiv.symm_apply_eq (peelEquiv ι a).toEquiv).mpr ?_
  change p = peelEquiv ι a (fibreIns a p.1 p.2)
  rw [peelEquiv_apply]
  refine Prod.ext ?_ ?_
  · simp only [fibreIns]
    rw [dif_pos trivial]
  · funext k
    simp only [fibreIns]
    rw [dif_neg k.2]

private theorem peelEquiv_fun_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ⇑(peelEquiv ι a) = fun x : ι → E3 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} E3)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelEquiv_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply, Prod.map_apply,
    MeasurableEquiv.funUnique_apply]
  rfl

private theorem measurePreserving_peelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelEquiv ι a) (volume : Measure (ι → E3))
      (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => E3)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → E3)))
  refine (h₃.comp h₁).congr (peelEquiv ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelEquiv_fun_eq (ι := ι) a) x

/-- The flattening of the nested fibre `{y : {k // k ≠ i} // y ≠ ⟨j, _⟩}` onto
`{k // k ≠ i ∧ k ≠ j}`. -/
private def flatEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    {y : {k : Fin n // k ≠ i} // y ≠ (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i})} ≃
      {k : Fin n // k ≠ i ∧ k ≠ j} where
  toFun y := ⟨y.1.1, y.1.2, fun h => y.2 (Subtype.ext h)⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

/-- The formula for the inverse of a `piCongrLeft` along an index equivalence. -/
private theorem piCongrLeft_symm_fun {δ δ' : Type*} (P : δ' → Type*)
    [∀ a, MeasurableSpace (P a)] (e : δ ≃ δ') (x : (a : δ') → P a) :
    (MeasurableEquiv.piCongrLeft P e).symm x = fun b => x (e b) := by
  funext b
  exact Equiv.piCongrLeft_symm_apply P e x b

/-- The two-coordinate insertion over the nested fibre, with the innermost variable reindexed
along the flattening equivalence, is the insertion of the coarser `upd2`-form. -/
private theorem fibreIns_comp_flat {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w w' : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    fibreIns i w (fibreIns (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i}) w'
      (fun y => x' (flatEquiv i j hij y)))
      = fun k => if h : k = i then w else if h' : k = j then w' else x' ⟨k, h, h'⟩ := by
  funext k
  simp only [fibreIns]
  by_cases h : k = i
  · simp only [dif_pos h]
  · simp only [dif_neg h]
    by_cases h' : k = j
    · have hh : (⟨k, h⟩ : {k : Fin n // k ≠ i}) = (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i}) :=
        Subtype.ext h'
      simp only [dif_pos hh, dif_pos h']
    · have hh : ¬ ((⟨k, h⟩ : {k : Fin n // k ≠ i}) =
          (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i})) :=
        fun hc => h' (congrArg Subtype.val hc)
      simp only [dif_neg hh, dif_neg h', flatEquiv]
      exact congrArg x' (Subtype.ext rfl)

/-- The fibre `{k // k ≠ i} → E3` split at the second slot `j`. -/
private def peelFibreEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ({k : Fin n // k ≠ i} → E3) ≃ᵐ
      E3 × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) :=
  (peelEquiv (ι := {k : Fin n // k ≠ i}) ⟨j, Ne.symm hij⟩).trans
    ((MeasurableEquiv.refl E3).prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => E3)
        (flatEquiv i j hij)))

private theorem peelFibreEquiv_symm_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : E3)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    (peelFibreEquiv i j hij).symm (a, x')
      = fibreIns (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i}) a
          (fun y => x' (flatEquiv i j hij y)) := by
  rw [peelFibreEquiv, MeasurableEquiv.trans_symm, MeasurableEquiv.trans_apply]
  rw [show ((MeasurableEquiv.refl E3).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => E3)
          (flatEquiv i j hij))).symm (a, x')
      = (a, (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => E3)
          (flatEquiv i j hij)).symm x') from rfl]
  rw [peelEquiv_symm_apply, piCongrLeft_symm_fun]

private theorem measurePreserving_peelFibreEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (peelFibreEquiv i j hij) volume volume := by
  have h1 := measurePreserving_peelEquiv (ι := {k : Fin n // k ≠ i}) ⟨j, Ne.symm hij⟩
  have h2 : MeasurePreserving ((MeasurableEquiv.refl E3).prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => E3)
        (flatEquiv i j hij))) volume volume :=
    (MeasurePreserving.id (volume : Measure E3)).prod
      (volume_measurePreserving_piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => E3)
        (flatEquiv i j hij))
  rw [peelFibreEquiv]
  exact h2.comp h1

/-- The composed equivalence `((w, a), x') ↦ upd2`-like, as a measurable equivalence
`(E3 × E3) × Fib2 ≃ᵐ (Fin n → E3)`. -/
private def twoSlotEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) ≃ᵐ (Fin n → E3) :=
  (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl E3).prodCongr (peelFibreEquiv i j hij).symm)).trans
    (peelEquiv (ι := Fin n) i).symm

private theorem twoSlotEquiv_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (w a : E3) (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3) :
    twoSlotEquiv i j hij ((w, a), x')
      = fun k => if h : k = i then w else if h' : k = j then a else x' ⟨k, h, h'⟩ := by
  rw [twoSlotEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  rw [show MeasurableEquiv.prodAssoc ((w, a), x') = (w, (a, x')) from rfl]
  rw [show ((MeasurableEquiv.refl E3).prodCongr (peelFibreEquiv i j hij).symm) (w, (a, x'))
      = (w, (peelFibreEquiv i j hij).symm (a, x')) from rfl]
  rw [peelEquiv_symm_apply, peelFibreEquiv_symm_apply, fibreIns_comp_flat hij]

private theorem measurePreserving_twoSlotEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (twoSlotEquiv i j hij) volume volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) ≃ᵐ
        E3 × (E3 × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3))) volume volume :=
    volume_preserving_prodAssoc
  have h2 : MeasurePreserving ((MeasurableEquiv.refl E3).prodCongr
      (peelFibreEquiv i j hij).symm) volume volume :=
    (MeasurePreserving.id (volume : Measure E3)).prod
      (measurePreserving_peelFibreEquiv i j hij).symm
  have h3 : MeasurePreserving (peelEquiv (ι := Fin n) i).symm volume volume :=
    (measurePreserving_peelEquiv (ι := Fin n) i).symm
  rw [twoSlotEquiv]
  exact h3.comp (h2.comp h1)

/-- The two-slot fibre decomposition of the `ℝ≥0∞`-valued integral, in the coordinates of the
splitting at the slots `i` then `j`. -/
private theorem lintegral_fibre_two_gen {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {F : (Fin n → E3) → ENNReal} (hF : AEMeasurable F) :
    ∫⁻ x : Fin n → E3, F x
      = ∫⁻ w : E3, ∫⁻ a : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          F (fun k => if h : k = i then w else if h' : k = j then a
              else x' ⟨k, h, h'⟩) := by
  classical
  have hΨ : MeasurePreserving (twoSlotEquiv i j hij) volume volume :=
    measurePreserving_twoSlotEquiv i j hij
  -- Almost-everywhere measurability of the pulled-back integrand.
  have hG : AEMeasurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) =>
      F (twoSlotEquiv i j hij z)) ((volume.prod volume).prod volume) := by
    exact (hΨ.aemeasurable_comp_iff (twoSlotEquiv i j hij).measurableEmbedding).mpr hF
  -- Step 1: the change of variables along the composed equivalence.
  have e1 : (∫⁻ x : Fin n → E3, F x)
      = ∫⁻ z : (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3),
          F (twoSlotEquiv i j hij z) :=
    hΨ.lintegral_map_equiv F (twoSlotEquiv i j hij)
  -- Step 2: Fubini, splitting off the last factor.
  have e2 : (∫⁻ z : (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3),
          F (twoSlotEquiv i j hij z))
      = ∫⁻ p : E3 × E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          F (twoSlotEquiv i j hij (p, x')) :=
    lintegral_prod (fun z : (E3 × E3) × ({k : Fin n // k ≠ i ∧ k ≠ j} → E3) =>
      F (twoSlotEquiv i j hij z)) hG
  -- Step 3: Fubini on `E3 × E3`.
  have hK : AEMeasurable (fun p : E3 × E3 => ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
      F (twoSlotEquiv i j hij (p, x'))) (volume.prod volume) :=
    AEMeasurable.lintegral_prod_right hG
  have e3 : (∫⁻ p : E3 × E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          F (twoSlotEquiv i j hij (p, x')))
      = ∫⁻ w : E3, ∫⁻ a : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          F (twoSlotEquiv i j hij ((w, a), x')) :=
    lintegral_prod (fun p : E3 × E3 => ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
      F (twoSlotEquiv i j hij (p, x'))) hK
  -- Step 4: the pointwise formula for the composed equivalence.
  have e4 : (∫⁻ w : E3, ∫⁻ a : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          F (twoSlotEquiv i j hij ((w, a), x')))
      = ∫⁻ w : E3, ∫⁻ a : E3, ∫⁻ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → E3,
          F (fun k => if h : k = i then w else if h' : k = j then a
              else x' ⟨k, h, h'⟩) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
    beta_reduce
    rw [twoSlotEquiv_apply hij w a x']
  exact e1.trans (e2.trans (e3.trans e4))

theorem lintegral_fibre_two_p {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {F : (Fin n → EuclideanSpace ℝ (Fin 3)) → ENNReal} (hF : AEMeasurable F) : ∫⁻ x : Fin n → EuclideanSpace ℝ (Fin 3), F x = ∫⁻ w : EuclideanSpace ℝ (Fin 3), ∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ x'' : Work.BoseBoxFock.Fib2 p, F (Work.BoseBoxFock.upd2 p a w x'') := by
  have h := lintegral_fibre_two_gen (i := p.2) (j := p.1) (Ne.symm hp) (F := F) hF
  exact h

end Work.BoseBoxFock
