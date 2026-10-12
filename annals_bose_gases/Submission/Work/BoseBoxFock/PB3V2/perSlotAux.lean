import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3V2.energy_fibre_le
import Submission.Work.BoseBoxFock.PB3V2.fibreOneBody
import Submission.Work.BoseBoxFock.PB3V2.mf_L2_le
import Submission.Work.BoseBoxFock.PB3V2.slotForm_slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.perSlotAux` — the per-slot fibre vocabulary of the block-III frame tail

This module makes the per-slot (`j`-fibre) bookkeeping of the block-III frame-tail comparison
**self-contained**: everything the per-slot bound `Work.BoseBoxFock.PB3V2.perSlot_bound` needs
about the slice forms of `limSlotForm` / `frameSlotForm`, about the fibre quantities
`fibreMassFree` / `fibreWave` and about the continuity/boundedness of the fibre integrands is
provided here, from the modules `PB3Defs`, `PB3FibreQ`, `kernelExpandedAux`, `boxSmoothAux`,
`PB3V2.slotForm_slice`, `PB3V2.fibreOneBody` and `PB3V2.energy_fibre_le` only.

The two fibre quantities `fibreMassFree` and `fibreWave` are the ones the per-slot bound pays with;
they are the copies of the corresponding definitions of the block-III chapter (`fibreMassFree`, the
`χ²`-free fibre box mass, and `fibreWave`, the `χ²`-weighted fibre Dirichlet content), verbatim so
that the two modules are interchangeable wherever the *values* are concerned.

The `PS` namespace collects the fibre-slicing lemmas (`limSlotForm_eq_fibreMass`, the frame form
`frameSlotForm_eq_sum`, the fibre coefficients and their continuity/bounds).
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory

namespace Work.BoseBoxFock

namespace PB3V2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. The fibre quantities paid by the per-slot bound -/

/-- The unweighted fibre box mass of the slot-`j` sections. -/
noncomputable def fibreMassFree {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ) : ℝ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ, ∫ w in boxL ℓ, ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2

/-- The fibre Dirichlet content of the slot-`j` sections. -/
noncomputable def fibreWave {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ) : ℝ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
    ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
      ∑ m : Fin 3, ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j w x')
        (Work.BoseBoxFock.slotDirVec j m)‖ ^ 2

namespace PS

/-! ## 2. The complex box restriction -/

/-- The complex box restriction `Ψ · 1_{abox n ℓ}` of a complex state. -/
noncomputable def boxRestrictCX {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℂ) : Xn n → ℂ :=
  fun x => Ψ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℂ)) x

lemma boxRestrictCX_of_mem {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℂ} {x : Xn n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) : boxRestrictCX ℓ Ψ x = Ψ x := by
  simp only [boxRestrictCX, Set.indicator_of_mem hx, mul_one]

lemma boxRestrictCX_of_notMem {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℂ} {x : Xn n}
    (hx : x ∉ Submission.BoseGases.abox n ℓ) : boxRestrictCX ℓ Ψ x = 0 := by
  simp only [boxRestrictCX, Set.indicator_of_notMem hx, mul_zero]

/-- The complex box restriction of a real state is the corpus's `boxRestrictC`. -/
lemma boxRestrictCX_ofReal {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    boxRestrictCX ℓ (fun x => ((Φ x : ℝ) : ℂ)) = boxRestrictC ℓ Φ := by
  funext x
  simp only [boxRestrictCX, boxRestrictC, Complex.ofReal_mul]
  congr 1
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-! ## 3. Boxes: the cube of the `j`-th coordinate -/

lemma update_mem_abox {n : ℕ} {ℓ : ℝ} {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ)
    (j : Fin n) {y : E3} (hy : y ∈ Submission.BoseGases.acube ℓ) :
    Function.update x j y ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro i
  by_cases h : i = j
  · subst h; rw [Function.update_self]; exact hy
  · rw [Function.update_of_ne h]; exact hx i

/-- A configuration all of whose inserted positions lie in the box is a point of the slice box. -/
lemma mem_boxPiSet_of_insertCoord_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) (u : E3)
    {x' : {l : Fin n // l ≠ j} → E3}
    (h : Work.BoseBoxFock.insertCoord j u x' ∈ Submission.BoseGases.abox n ℓ) :
    x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ := by
  rw [mem_boxPiSet, corpusBox_boxL_eq_acube hℓ]
  intro l
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ (Work.BoseBoxFock.insertCoord j u x')).mp h l.1
  rwa [show Work.BoseBoxFock.insertCoord j u x' l.1 = x' l from by
    rw [Work.BoseBoxFock.insertCoord_eq]; simp only [dif_neg l.2]] at h1

/-- Conversely, an inserted point with `u` outside the cube is outside the box. -/
lemma insertCoord_notMem_abox_of_notMem_acube {n : ℕ} {ℓ : ℝ} (j : Fin n) {u : E3}
    {x' : {l : Fin n // l ≠ j} → E3} (hu : u ∉ Submission.BoseGases.acube ℓ) :
    Work.BoseBoxFock.insertCoord j u x' ∉ Submission.BoseGases.abox n ℓ := by
  intro hcon
  refine hu ?_
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ
    (Work.BoseBoxFock.insertCoord j u x')).mp hcon j
  rwa [Work.BoseBoxFock.insertCoord_self] at h1

/-- On the box, the slot-`j` box projection of the box-restricted state is that of the state. -/
lemma boxQ_boxRestrictCX {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) (Ψ : Xn n → ℂ)
    {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    Work.BoseBoxFock.boxQ ℓ j (boxRestrictCX ℓ Ψ) x = Work.BoseBoxFock.boxQ ℓ j Ψ x := by
  have h1 : boxRestrictCX ℓ Ψ x = Ψ x := boxRestrictCX_of_mem hx
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        boxRestrictCX ℓ Ψ (Function.update x j y))
      = ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x j y) := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y hy => ?_)
    exact boxRestrictCX_of_mem (update_mem_abox hx j hy)
  simp only [Work.BoseBoxFock.boxQ, h1, h2]

/-! ## 4. The limit slot form is the fibre box mass -/

theorem limSlotForm_slice {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseBoxFock.limSlotForm ℓ j (boxRestrictCX ℓ Ψ)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
          ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
            * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2 := by
  have h1 : Work.BoseBoxFock.limSlotForm ℓ j (boxRestrictCX ℓ Ψ)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
            * ‖Work.BoseBoxFock.boxQ ℓ j Ψ x‖ ^ 2 := by
    rw [Work.BoseBoxFock.limSlotForm]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x hx => ?_)
    rw [boxQ_boxRestrictCX hℓ j Ψ hx]
  rw [h1]
  exact Work.BoseBoxFock.fibre_part2 j hℓ hΨ

/-- The `χ²`-weighted fibre box mass. -/
noncomputable def fibreMass {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ) : ℝ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
    ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
      * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2

/-- The limit slot form is the fibre box mass. -/
theorem limSlotForm_eq_fibreMass {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseBoxFock.limSlotForm ℓ j (boxRestrictCX ℓ Ψ) = fibreMass ℓ j Ψ :=
  limSlotForm_slice j hℓ hΨ

/-! ## 5. The pointwise fibre quantities -/

/-- The `χ²`-weighted box mass of the slot-`j` fibre of the state `Θ`. -/
noncomputable def fibreBox {n : ℕ} (ℓ : ℝ) (j : Fin n) (Θ : Xn n → ℂ)
    (x' : {l : Fin n // l ≠ j} → E3) : ℝ :=
  ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
    * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Θ) w‖ ^ 2

/-- The unweighted box mass of the slot-`j` fibre of `Ψ`. -/
noncomputable def fibreBoxFree {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ)
    (x' : {l : Fin n // l ≠ j} → E3) : ℝ :=
  ∫ w in boxL ℓ, ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2

/-- The `χ²`-weighted Dirichlet content of the slot-`j` fibre of `Ψ`. -/
noncomputable def fibreDir {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ)
    (x' : {l : Fin n // l ≠ j} → E3) : ℝ :=
  ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
    * ∑ m : Fin 3, ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j w x')
        (Work.BoseBoxFock.slotDirVec j m)‖ ^ 2

lemma fibreMass_eq_integral_fibreBox {n : ℕ} {ℓ : ℝ} (j : Fin n) (Ψ : Xn n → ℂ) :
    fibreMass ℓ j Ψ = ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, fibreBox ℓ j Ψ x' := rfl

lemma fibreMassFree_eq_integral {n : ℕ} {ℓ : ℝ} (j : Fin n) (Ψ : Xn n → ℂ) :
    PB3V2.fibreMassFree ℓ j Ψ
      = ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, fibreBoxFree ℓ j Ψ x' := rfl

lemma fibreWave_eq_integral {n : ℕ} {ℓ : ℝ} (j : Fin n) (Ψ : Xn n → ℂ) :
    PB3V2.fibreWave ℓ j Ψ = ∫ x' in boxPiSet ({l : Fin n // l ≠ j}) ℓ, fibreDir ℓ j Ψ x' := rfl

/-- Two states agreeing on the box have the same mean-free part there. -/
lemma mf_congr_on_box {ℓ : ℝ} {f g : E3 → ℂ} (h : ∀ w ∈ boxL ℓ, f w = g w)
    {w : E3} (hw : w ∈ boxL ℓ) : Work.BoseBoxFock.mf ℓ f w = Work.BoseBoxFock.mf ℓ g w := by
  have hI : (∫ y in boxL ℓ, f y) = ∫ y in boxL ℓ, g y :=
    MeasureTheory.setIntegral_congr_fun
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) h
  unfold Work.BoseBoxFock.mf
  rw [h w hw, hI]

/-- The full-space integral defining the fibre box mass is a box integral. -/
lemma integral_fibreBox_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) (Θ : Xn n → ℂ)
    (x' : {l : Fin n // l ≠ j} → E3) :
    (∫ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Θ) w‖ ^ 2)
      = fibreBox ℓ j Θ x' :=
  (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := boxL ℓ) (f := fun w : E3 =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Θ) w‖ ^ 2)
    (fun w hw => by rw [Work.BoseBoxFock.chiScale_eq_zero_of_notMem hℓ hw]; ring)).symm

/-- On the slice box the two sections agree on the box. -/
lemma sect_congr {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} {x' : {l : Fin n // l ≠ j} → E3}
    (hx' : x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ) :
    ∀ w ∈ boxL ℓ, Work.BoseBoxFock.sect j x' (boxRestrictC ℓ Φ) w
      = Work.BoseBoxFock.sect j x' (fun x => ((Φ x : ℝ) : ℂ)) w := by
  intro w hw
  have h2 : Work.BoseBoxFock.insertCoord j w x' ∈ Submission.BoseGases.abox n ℓ := by
    rw [Submission.BoseGases.mem_abox_iff]
    intro i
    by_cases hi : i = j
    · subst hi
      rw [Work.BoseBoxFock.insertCoord_eq]
      simp only [dif_pos rfl]
      rwa [corpusBox_boxL_eq_acube hℓ] at hw
    · rw [Work.BoseBoxFock.insertCoord_eq]
      simp only [dif_neg hi]
      have h3 := (mem_boxPiSet.mp hx') ⟨i, hi⟩
      rwa [corpusBox_boxL_eq_acube hℓ] at h3
  show boxRestrictC ℓ Φ (Work.BoseBoxFock.insertCoord j w x')
    = ((Φ (Work.BoseBoxFock.insertCoord j w x') : ℝ) : ℂ)
  simp only [boxRestrictC, Set.indicator_of_mem h2, mul_one, Complex.ofReal_one]

/-- On the slice box the two box masses of the restricted and the smooth state agree. -/
lemma fibreBox_congr {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} {x' : {l : Fin n // l ≠ j} → E3}
    (hx' : x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ) :
    fibreBox ℓ j (boxRestrictC ℓ Φ) x'
      = fibreBox ℓ j (fun x => ((Φ x : ℝ) : ℂ)) x' := by
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
  rw [mf_congr_on_box (sect_congr hℓ j hx') hw]

/-! ## 6. Continuity of the fibre integrands -/

lemma continuous_insertCoord_pair {n : ℕ} (j : Fin n) :
    Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      Work.BoseBoxFock.insertCoord j q.2 q.1 :=
  (Work.BoseBoxFock.continuous_insertCoord j).comp (continuous_snd.prodMk continuous_fst)

lemma continuous_mean_sect {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ} (hΨ : Continuous Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
      ∫ v in boxL ℓ, Ψ (Work.BoseBoxFock.insertCoord j v x') := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (v : E3) =>
      Ψ (Work.BoseBoxFock.insertCoord j v x')) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (v : E3) =>
      Ψ (Work.BoseBoxFock.insertCoord j v x'))
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
        Ψ (Work.BoseBoxFock.insertCoord j q.2 q.1) := rfl
  rw [h]
  exact hΨ.comp (continuous_insertCoord_pair j)

lemma continuous_mf_sect {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ} (hΨ : Continuous Ψ) :
    Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j q.1 Ψ) q.2‖ ^ 2 := by
  have h1 : Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      Ψ (Work.BoseBoxFock.insertCoord j q.2 q.1) :=
    hΨ.comp (continuous_insertCoord_pair j)
  have h2 : Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      ∫ v in boxL ℓ, Ψ (Work.BoseBoxFock.insertCoord j v q.1) :=
    (continuous_mean_sect (ℓ := ℓ) j hΨ).comp continuous_fst
  have hcont : Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      ‖Ψ (Work.BoseBoxFock.insertCoord j q.2 q.1)
        - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)
          * (∫ v in boxL ℓ, Ψ (Work.BoseBoxFock.insertCoord j v q.1))‖ ^ 2 :=
    ((h1.sub (continuous_const.mul h2))).norm.pow 2
  simpa only [Work.BoseBoxFock.mf, Work.BoseBoxFock.sect] using hcont

lemma continuous_fibreBoxFree {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : Continuous Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 => fibreBoxFree ℓ j Ψ x' := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
        ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j q.1 Ψ) q.2‖ ^ 2 := rfl
  rw [h]
  exact continuous_mf_sect j hΨ

lemma continuous_fibreBox {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : Continuous Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 => fibreBox ℓ j Ψ x' := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
        (Submission.BoseGases.chiScale ℓ q.2) ^ 2
          * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j q.1 Ψ) q.2‖ ^ 2 := rfl
  rw [h]
  exact (((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).pow 2).mul
    (continuous_mf_sect j hΨ)

lemma continuous_fibreDir {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 => fibreDir ℓ j Ψ x' := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ∑ m : Fin 3, ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j w x')
            (Work.BoseBoxFock.slotDirVec j m)‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ∑ m : Fin 3, ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j w x')
            (Work.BoseBoxFock.slotDirVec j m)‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
        (Submission.BoseGases.chiScale ℓ q.2) ^ 2
          * ∑ m : Fin 3, ‖fderiv ℝ Ψ (Work.BoseBoxFock.insertCoord j q.2 q.1)
              (Work.BoseBoxFock.slotDirVec j m)‖ ^ 2 := rfl
  rw [h]
  exact (((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).pow 2).mul
    (continuous_finsetSum _ (fun m _ =>
      (((Work.BoseBoxFock.continuous_fderiv_apply hΨ
        (Work.BoseBoxFock.slotDirVec j m)).comp
        (continuous_insertCoord_pair j)).norm).pow 2))

/-! ## 7. The frame slot form as a fibre sum -/

lemma measurable_boxRestrictC {n : ℕ} (ℓ : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Measurable Φ) : Measurable (boxRestrictC ℓ Φ) := by
  have h1 : Measurable (fun x : Xn n => ((Φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hΦ
  have h2 : Measurable (fun x : Xn n =>
      ((( Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))
  exact h1.mul h2

lemma bdd_boxRestrictC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) : ∃ C : ℝ, ∀ x, ‖boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · have h1 : boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) := by
      simp [boxRestrictC, hx]
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hC x hx) (le_max_left _ _)
  · have h1 : boxRestrictC ℓ Φ x = 0 := by
      simp [boxRestrictC, hx]
    rw [h1, norm_zero]
    exact le_max_right _ _

lemma support_boxRestrictC {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra h
  exact hx (by simp [boxRestrictC, h])

/-- The real part of `∫ conj(A x)·A x` is `∫ ‖A x‖²`. -/
lemma re_integral_conj_mul_self {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : α → ℂ}
    (hint : Integrable (fun x => (starRingEnd ℂ) (A x) * A x) μ) :
    (∫ x, (starRingEnd ℂ) (A x) * A x ∂μ).re = ∫ x, ‖A x‖ ^ 2 ∂μ := by
  have h1 : ∫ x, Complex.reCLM ((starRingEnd ℂ) (A x) * A x) ∂μ
      = (∫ x, (starRingEnd ℂ) (A x) * A x ∂μ).re := by
    simpa only [Complex.reCLM_apply] using
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hint)
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  change Complex.reCLM ((starRingEnd ℂ) (A x) * A x) = ‖A x‖ ^ 2
  rw [Complex.reCLM_apply, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The fibre coefficient `x' ↦ ∫_u conj(w u)·Θ(x'[j↦u])` is integrable against its own
conjugate: it is bounded and supported in the slice box. -/
lemma integrable_fibre_conj_mul {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {w : E3 → ℂ}
    {Θ : Xn n → ℂ} (hwm : Measurable w) (hwb : ∃ C : ℝ, ∀ u, ‖w u‖ ≤ C)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    Integrable (fun x' : {l : Fin n // l ≠ j} → E3 =>
      (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (w u)
        * Θ (Work.BoseBoxFock.insertCoord j u x'))
        * (∫ u : E3, (starRingEnd ℂ) (w u)
          * Θ (Work.BoseBoxFock.insertCoord j u x'))) volume := by
  obtain ⟨Cw, hCw⟩ := hwb
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ (Classical.arbitrary (Xn n)))
  have hCw0 : 0 ≤ Cw := le_trans (norm_nonneg _) (hCw 0)
  set F : ({l : Fin n // l ≠ j} → E3) → ℂ := fun x' => ∫ u : E3,
    (starRingEnd ℂ) (w u) * Θ (Work.BoseBoxFock.insertCoord j u x') with hFdef
  have hFm : Measurable F := by
    rw [hFdef]
    have hjoint : StronglyMeasurable (fun p : ({l : Fin n // l ≠ j} → E3) × E3 =>
        (starRingEnd ℂ) (w p.2) * Θ (Work.BoseBoxFock.insertCoord j p.2 p.1)) :=
      (((Complex.continuous_conj.measurable.comp hwm).stronglyMeasurable).comp_measurable
        measurable_snd).mul
        (hΘm.stronglyMeasurable.comp_measurable
          ((Work.BoseBoxFock.continuous_insertCoord j).comp continuous_swap).measurable)
    exact (StronglyMeasurable.integral_prod_right hjoint).measurable
  have hFbd : ∀ x', ‖F x'‖ ≤ Cw * CΘ * ℓ ^ 3 := by
    intro x'
    have hmaj : Integrable (fun u : E3 => (Cw * CΘ) *
        (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u) volume := by
      refine Integrable.const_mul ?_ _
      refine IntegrableOn.integrable_indicator (integrableOn_const ?_ (by simp))
        (Submission.BoseGases.acube_measurable _)
      exact (Submission.BoseGases.acube_lt_top ℓ hℓ.le).ne
    have hbd : ∀ u : E3, ‖(starRingEnd ℂ) (w u)
        * Θ (Work.BoseBoxFock.insertCoord j u x')‖
        ≤ (Cw * CΘ) * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u := by
      intro u
      rw [norm_mul, Complex.norm_conj]
      by_cases hu : u ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hu, mul_one]
        exact mul_le_mul (hCw u) (hCΘ _) (norm_nonneg _) hCw0
      · rw [theta_zero_of_notMem_abox hΘs
          (insertCoord_notMem_abox_of_notMem_acube j hu),
          norm_zero, mul_zero, Set.indicator_of_notMem hu, mul_zero]
    have haesm : AEStronglyMeasurable (fun u : E3 =>
        ‖(starRingEnd ℂ) (w u) * Θ (Work.BoseBoxFock.insertCoord j u x')‖) volume :=
      ((((Complex.continuous_conj.measurable.comp hwm).aestronglyMeasurable).mul
        ((hΘm.comp ((Work.BoseBoxFock.continuous_insertCoord j).comp
          (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable))).norm
    rw [hFdef]
    calc ‖∫ u : E3, (starRingEnd ℂ) (w u)
            * Θ (Work.BoseBoxFock.insertCoord j u x')‖
        ≤ ∫ u : E3, ‖(starRingEnd ℂ) (w u)
            * Θ (Work.BoseBoxFock.insertCoord j u x')‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u : E3, (Cw * CΘ) *
            (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u :=
          integral_mono (Integrable.mono' hmaj haesm
            (Filter.Eventually.of_forall (fun u => by simpa using hbd u))) hmaj hbd
      _ = (Cw * CΘ) * ℓ ^ 3 := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ),
            MeasureTheory.setIntegral_const, Measure.real,
            Submission.BoseGases.acube_volume ℓ hℓ.le,
            ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
          ring
  have hFsupp : Function.support F ⊆ boxPiSet ({l : Fin n // l ≠ j}) ℓ := by
    intro x' hx'
    rw [Function.mem_support] at hx'
    by_contra hb
    refine hx' ?_
    rw [hFdef]
    show (∫ u : E3, (starRingEnd ℂ) (w u)
      * Θ (Work.BoseBoxFock.insertCoord j u x')) = 0
    have h0 : (fun u : E3 => (starRingEnd ℂ) (w u)
        * Θ (Work.BoseBoxFock.insertCoord j u x')) = fun _ => 0 := by
      funext u
      by_cases hmem : Work.BoseBoxFock.insertCoord j u x' ∈ Submission.BoseGases.abox n ℓ
      · exact absurd (mem_boxPiSet_of_insertCoord_mem_abox hℓ j u hmem) hb
      · rw [theta_zero_of_notMem_abox hΘs hmem, mul_zero]
    rw [h0]
    simp
  have hint : Integrable (fun x' : {l : Fin n // l ≠ j} → E3 =>
      (starRingEnd ℂ) (F x') * F x') volume := by
    refine Integrable.mono' (g := fun x' : {l : Fin n // l ≠ j} → E3 =>
      (Cw * CΘ * ℓ ^ 3) ^ 2 *
        (boxPiSet ({l : Fin n // l ≠ j}) ℓ).indicator (fun _ => (1 : ℝ)) x') ?_ ?_ ?_
    · refine Integrable.const_mul ?_ _
      refine IntegrableOn.integrable_indicator (integrableOn_const ?_ (by simp))
        ((isCompact_boxPiSet (ι := {l : Fin n // l ≠ j}) hℓ).measurableSet)
      exact (isCompact_boxPiSet (ι := {l : Fin n // l ≠ j}) hℓ).measure_lt_top.ne
    · exact ((Complex.continuous_conj.measurable.comp hFm).mul hFm).aestronglyMeasurable
    · filter_upwards with x'
      rw [norm_mul, Complex.norm_conj]
      by_cases hx : x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ
      · rw [Set.indicator_of_mem hx, mul_one]
        have h1 := hFbd x'
        have h2 : 0 ≤ Cw * CΘ * ℓ ^ 3 := by positivity
        nlinarith [norm_nonneg (F x')]
      · rw [Function.notMem_support.mp (fun hc => hx (hFsupp hc)), norm_zero, mul_zero,
          Set.indicator_of_notMem hx, mul_zero]
  exact hint

/-- **The frame slot form is the sum of the fibre frame masses.** -/
theorem frameSlotForm_eq_sum {n : ℕ} {v : E3 → ℝ} {μ : ℝ} (N : ℕ) (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseBoxFock.frameSlotForm v μ N j (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      = ∑ k : Lab N, ∫ x' : {k : Fin n // k ≠ j} → E3,
          ‖∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
            * (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
                (Work.BoseBoxFock.insertCoord j u x')‖ ^ 2 := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hΘm : Measurable (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ) :=
    measurable_boxRestrictC _ hΦ.continuous.measurable
  obtain ⟨CΘ, hCΘ⟩ := bdd_boxRestrictC hℓ hΦ.continuous
  have hΘs : Function.support (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) := support_boxRestrictC _ _
  have hmeq : ∀ k : Lab N,
      (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
          (starRingEnd ℂ) (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ x)
            * (Work.BoseBoxFock.pinQ v μ N k (x j)
              * (∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
                    (Function.update x j u))))
        = ∫ x' : {k : Fin n // k ≠ j} → E3,
            (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
                    (Work.BoseBoxFock.insertCoord j u x'))
              * (∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
                    (Work.BoseBoxFock.insertCoord j u x')) := by
    intro k
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) (f := fun x => (starRingEnd ℂ)
        (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ x)
          * (Work.BoseBoxFock.pinQ v μ N k (x j)
            * (∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
              * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
                  (Function.update x j u)))) (fun x hx => by
        rw [theta_zero_of_notMem_abox hΘs hx, map_zero, zero_mul])]
    exact slotForm_slice j hΘm ⟨CΘ, hCΘ⟩ hΘs
      (Work.BoseBoxFock.pinQ_measurable v μ N k).aestronglyMeasurable
      ((Work.BoseBoxFock.pinQ_bdd v μ N k).imp fun C h => h.2)
  have hsum : Work.BoseBoxFock.frameSlotForm v μ N j
        (boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      = (∑ k : Lab N, ∫ x' : {k : Fin n // k ≠ j} → E3,
          (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
              * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
                  (Work.BoseBoxFock.insertCoord j u x'))
            * (∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
              * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
                  (Work.BoseBoxFock.insertCoord j u x'))).re := by
    rw [Work.BoseBoxFock.frameSlotForm]
    exact congrArg Complex.re (Finset.sum_congr rfl (fun k _ => hmeq k))
  rw [hsum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine re_integral_conj_mul_self (A := fun x' : {l : Fin n // l ≠ j} → E3 =>
    ∫ u : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
      * boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ
          (Work.BoseBoxFock.insertCoord j u x')) ?_
  exact integrable_fibre_conj_mul hℓ j (Work.BoseBoxFock.pinQ_measurable v μ N k)
    ((Work.BoseBoxFock.pinQ_bdd v μ N k).imp fun C h => h.2) hΘm ⟨CΘ, hCΘ⟩ hΘs

end PS

end PB3V2

end Work.BoseBoxFock
