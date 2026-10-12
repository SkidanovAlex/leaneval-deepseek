import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.B13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lintegral_fibre_p1`

The `lintegral` fibre splitting at the slot `p.1` of a `Fib1 p`-configuration:

`∫⁻ x' : Fib1 p, F x' = ∫⁻ a, ∫⁻ x'' : Fib2 p, F (upd1 p a x'')`,

i.e. the `ENNReal`-valued conditional-expectation identity along the fibre over the slot `p.1`.

It is the `lintegral` analogue of `integral_fibre_one`/`integral_fibre_two` (which are stated for
`ℂ`-valued integrable functions) and is proved in the same two steps:

* `lintegral_fibre_one_aux` — splitting off one coordinate of `ι → E3` as a separate factor, by
  transporting along the measure-preserving equivalence `peelME` (the peel
  `piEquivPiSubtypeProd` followed by the identification of the one-point fibre with `E3`) and then
  applying Tonelli;
* the reindexing of the remaining coordinates `Fib2 p → E3` back to the nested fibre
  `{y : I1 p // y ≠ ⟨p.1, hp⟩} → E3` along the index equivalence `unfoldI2`, using
  `volume_measurePreserving_piCongrLeft`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Splitting off one coordinate, for `ENNReal`-valued functions -/

/-- Splitting off the coordinate `a` of `ι → E3` as a separate factor, as a measurable
equivalence. -/
private def peelME (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → E3) ≃ᵐ E3 × ({k : ι // k ≠ a} → E3) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} E3).prodCongr (MeasurableEquiv.refl _))

private theorem peelME_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → E3) :
    peelME ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelME, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

private theorem peelME_fun_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ⇑(peelME ι a) = fun x : ι → E3 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} E3)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelME_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply, Prod.map_apply,
    MeasurableEquiv.funUnique_apply]
  rfl

private theorem peelME_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (p : E3 × ({k : ι // k ≠ a} → E3)) :
    (peelME ι a).symm p = fibreIns a p.1 p.2 := by
  refine (Equiv.symm_apply_eq (peelME ι a).toEquiv).mpr ?_
  change p = peelME ι a (fibreIns a p.1 p.2)
  rw [peelME_apply]
  refine Prod.ext ?_ ?_
  · simp only [fibreIns]
    rw [dif_pos trivial]
  · funext k
    simp only [fibreIns]
    rw [dif_neg k.2]

private theorem measurePreserving_peelME {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelME ι a) (volume : Measure (ι → E3))
      (volume : Measure (E3 × ({k : ι // k ≠ a} → E3))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => E3) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => E3)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → E3)))
  refine (h₃.comp h₁).congr (peelME ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelME_fun_eq (ι := ι) a) x

/-- The one-coordinate splitting of a `lintegral` over `ι → E3`. -/
private theorem lintegral_fibre_one_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    {F : (ι → E3) → ENNReal} (hF : AEMeasurable F) :
    (∫⁻ x : ι → E3, F x) = ∫⁻ w : E3, ∫⁻ y : {k : ι // k ≠ a} → E3, F (fibreIns a w y) := by
  have hmp := measurePreserving_peelME (ι := ι) a
  have hsymm := MeasurePreserving.symm (peelME ι a) hmp
  have h1 : (∫⁻ x : ι → E3, F x)
      = ∫⁻ q : E3 × ({k : ι // k ≠ a} → E3), F ((peelME ι a).symm q) :=
    (hsymm.lintegral_comp_emb (peelME ι a).symm.measurableEmbedding F).symm
  rw [h1]
  have hF2 : AEMeasurable (fun q : E3 × ({k : ι // k ≠ a} → E3) => F ((peelME ι a).symm q)) :=
    (hsymm.aemeasurable_comp_iff (peelME ι a).symm.measurableEmbedding (g := F)).mpr hF
  rw [MeasureTheory.Measure.volume_eq_prod E3 ({k : ι // k ≠ a} → E3)]
  rw [lintegral_prod _ hF2]
  refine lintegral_congr fun w => lintegral_congr fun y => ?_
  show F ((peelME ι a).symm (w, y)) = F (fibreIns a w y)
  rw [peelME_symm_apply]

/-! ## The flattening of the nested fibre -/

/-- The flattening of the nested fibre `{y : I1 p // y ≠ ⟨p.1, hp⟩}` onto
`I2 p = {k // k ≠ p.2 ∧ k ≠ p.1}`. -/
private def unfoldI2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    {y : I1 p // y ≠ (⟨p.1, hp⟩ : I1 p)} ≃ I2 p where
  toFun y := ⟨y.1.1, y.1.2, fun h => y.2 (Subtype.ext h)⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

/-- The formula for the inverse of a `piCongrLeft` along an index equivalence. -/
private theorem piCongrLeft_symm_apply' {δ δ' : Type*} (P : δ' → Type*)
    [∀ a, MeasurableSpace (P a)] (e : δ ≃ δ') (x : (a : δ') → P a) :
    (MeasurableEquiv.piCongrLeft P e).symm x = fun b => x (e b) := by
  funext b
  exact Equiv.piCongrLeft_symm_apply P e x b

/-- Inserting `w` at the slot `p.1` of a `Fib2 p`-configuration, after reindexing along
`unfoldI2`, is `upd1 p w`. -/
private theorem fibreIns_p1 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (w : E3)
    (x'' : I2 p → E3) :
    fibreIns (⟨p.1, hp⟩ : I1 p) w (fun b => x'' (unfoldI2 p hp b)) = upd1 p w x'' := by
  funext k
  rw [fibreIns]
  by_cases h : k = (⟨p.1, hp⟩ : I1 p)
  · rw [dif_pos h, upd1, dif_pos (congrArg Subtype.val h)]
  · rw [dif_neg h, upd1, dif_neg (fun hh => h (Subtype.ext hh))]
    exact congrArg x'' (Subtype.ext rfl)

/-- The `lintegral` fibre splitting at the slot `p.1`. -/
theorem lintegral_fibre_p1 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {F : Work.BoseBoxFock.Fib1 p → ENNReal} (hF : AEMeasurable F) : ∫⁻ x' : Work.BoseBoxFock.Fib1 p, F x' = ∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ x'' : Work.BoseBoxFock.Fib2 p, F (Work.BoseBoxFock.upd1 p a x'') := by
  classical
  rw [lintegral_fibre_one_aux (ι := I1 p) (a := (⟨p.1, hp⟩ : I1 p)) hF]
  refine lintegral_congr fun w => ?_
  have hφ : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : I2 p => E3) (unfoldI2 p hp)).symm
      (volume : Measure (I2 p → E3))
      (volume : Measure ({y : I1 p // y ≠ (⟨p.1, hp⟩ : I1 p)} → E3)) :=
    (volume_measurePreserving_piCongrLeft (fun _ : I2 p => E3) (unfoldI2 p hp)).symm
  rw [← hφ.lintegral_comp_emb
      (MeasurableEquiv.piCongrLeft (fun _ : I2 p => E3) (unfoldI2 p hp)).symm.measurableEmbedding
      (fun y : {y : I1 p // y ≠ (⟨p.1, hp⟩ : I1 p)} → E3 =>
        F (fibreIns (⟨p.1, hp⟩ : I1 p) w y))]
  refine lintegral_congr fun x'' => ?_
  rw [piCongrLeft_symm_apply']
  rw [fibreIns_p1 p hp w x'']

end Work.BoseBoxFock
