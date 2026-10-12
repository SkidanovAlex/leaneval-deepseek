import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ## Splitting off one coordinate

We prove the one-coordinate fibre splitting

`∫ x : ι → 𝔼, F x = ∫ w, ∫ y : {k // k ≠ a} → 𝔼, F (fun k => if k = a then w else y ⟨k, _⟩)`

for an arbitrary finite index type `ι`, by transporting along the measure preserving
equivalence `peelEquiv` (a `piEquivPiSubtypeProd` split followed by the identification of the
one-point fibre `{k // k = a} → 𝔼` with `𝔼`) and then applying Fubini. -/

/-- Insert the value `w` in the coordinate `a`. -/
def fibreIns {ι : Type*} [DecidableEq ι] (a : ι) (w : 𝔼) (y : {k : ι // k ≠ a} → 𝔼) :
    ι → 𝔼 :=
  fun k => if h : k = a then w else y ⟨k, h⟩

/-- Splitting off the coordinate `a` as a factor `𝔼`. -/
private def peelEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → 𝔼) ≃ᵐ 𝔼 × ({k : ι // k ≠ a} → 𝔼) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} 𝔼).prodCongr (MeasurableEquiv.refl _))

private theorem peelEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → 𝔼) :
    peelEquiv ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

private theorem peelEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (p : 𝔼 × ({k : ι // k ≠ a} → 𝔼)) :
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
    ⇑(peelEquiv ι a) = fun x : ι → 𝔼 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} 𝔼)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelEquiv_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply, Prod.map_apply,
    MeasurableEquiv.funUnique_apply]
  rfl

private theorem measurePreserving_peelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelEquiv ι a) (volume : Measure (ι → 𝔼))
      (volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => 𝔼)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → 𝔼)))
  refine (h₃.comp h₁).congr (peelEquiv ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelEquiv_fun_eq (ι := ι) a) x

private theorem integrable_fibreIns {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    {F : (ι → 𝔼) → ℂ} (hF : Integrable F) :
    Integrable (fun p : 𝔼 × ({k : ι // k ≠ a} → 𝔼) => F (fibreIns a p.1 p.2))
      ((volume : Measure 𝔼).prod (volume : Measure ({k : ι // k ≠ a} → 𝔼))) := by
  have hmp := measurePreserving_peelEquiv (ι := ι) a
  have hsymm := MeasurePreserving.symm (peelEquiv ι a) hmp
  have h : Integrable (fun p : 𝔼 × ({k : ι // k ≠ a} → 𝔼) => F ((peelEquiv ι a).symm p))
      ((volume : Measure 𝔼).prod (volume : Measure ({k : ι // k ≠ a} → 𝔼))) :=
    (hsymm.integrable_comp hF.aestronglyMeasurable).mpr hF
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  show F ((peelEquiv ι a).symm p) = F (fibreIns a p.1 p.2)
  rw [peelEquiv_symm_apply]

/-- The one-coordinate fibre splitting. -/
theorem integral_fibre_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    {F : (ι → 𝔼) → ℂ} (hF : Integrable F) :
    (∫ x : ι → 𝔼, F x) = ∫ w : 𝔼, ∫ y : {k : ι // k ≠ a} → 𝔼, F (fibreIns a w y) := by
  have hmp := measurePreserving_peelEquiv (ι := ι) a
  have hsymm := MeasurePreserving.symm (peelEquiv ι a) hmp
  have h1 : (∫ x : ι → 𝔼, F x)
      = ∫ p : 𝔼 × ({k : ι // k ≠ a} → 𝔼), F ((peelEquiv ι a).symm p) :=
    (hsymm.integral_comp' F).symm
  rw [h1]
  have h2 : Integrable (fun p : 𝔼 × ({k : ι // k ≠ a} → 𝔼) => F ((peelEquiv ι a).symm p))
      ((volume : Measure 𝔼).prod (volume : Measure ({k : ι // k ≠ a} → 𝔼))) :=
    (hsymm.integrable_comp hF.aestronglyMeasurable).mpr hF
  have h3 : (∫ p : 𝔼 × ({k : ι // k ≠ a} → 𝔼), F ((peelEquiv ι a).symm p))
      = ∫ w : 𝔼, ∫ y : {k : ι // k ≠ a} → 𝔼, F ((peelEquiv ι a).symm (w, y)) :=
    MeasureTheory.integral_prod _ h2
  rw [h3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show F ((peelEquiv ι a).symm (w, y)) = F (fibreIns a w y)
  rw [peelEquiv_symm_apply]

/-! ## The two-coordinate splitting -/

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
along the flattening equivalence, is the insertion of the target statement. -/
private theorem fibreIns_comp_flat {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w w' : 𝔼)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → 𝔼) :
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

theorem integral_fibre_two {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {G : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (hG : MeasureTheory.Integrable G) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), G x)
      = ∫ w : EuclideanSpace ℝ (Fin 3), ∫ w' : EuclideanSpace ℝ (Fin 3),
          ∫ x' : {k : Fin n // k ≠ i ∧ k ≠ j} → EuclideanSpace ℝ (Fin 3),
            G (fun k => if h : k = i then w
                        else if h' : k = j then w' else x' ⟨k, h, h'⟩) := by
  classical
  rw [integral_fibre_one (ι := Fin n) i hG]
  have hae : ∀ᵐ w ∂(volume : Measure 𝔼),
      Integrable (fun y : {k : Fin n // k ≠ i} → 𝔼 => G (fibreIns i w y))
        (volume : Measure ({k : Fin n // k ≠ i} → 𝔼)) :=
    (integrable_fibreIns (ι := Fin n) i hG).prod_right_ae
  refine integral_congr_ae ?_
  filter_upwards [hae] with w hw
  rw [integral_fibre_one (ι := {k : Fin n // k ≠ i})
    (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i}) hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
  beta_reduce
  have hmp := measurePreserving_piCongrLeft
    (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => (volume : Measure 𝔼)) (flatEquiv i j hij)
  have htr := (MeasurePreserving.symm
    (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => 𝔼) (flatEquiv i j hij))
    hmp).integral_comp'
      (g := fun u : {y : {k : Fin n // k ≠ i} // y ≠ (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i})} → 𝔼 =>
        G (fibreIns i w (fibreIns (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i}) w' u)))
  refine htr.symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  beta_reduce
  rw [piCongrLeft_symm_fun]
  rw [fibreIns_comp_flat hij]

end Work.BoseBoxFock
