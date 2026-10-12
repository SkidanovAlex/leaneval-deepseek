import ChallengeDeps
import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.BoseBoxFock.PB3V2.perSlot_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3SecondHalfV2` — the frame-tail bound of the block-III row

This is the corrected form of `Work.BoseBoxFock.PB3SecondHalf` (whose frozen statement is **false**
at `μ · a v = 0`: there `sideAt μ (a v) = 0` while `ellH v μ = 1`, and `normB` collapses to a
measure-zero box, see `FINDING_PB3SecondHalf_FALSE.md`).  Here the guard `0 < μ`, `0 < a v` (hence
`0 < sideAt μ (a v) = ellH v μ`) and `0 < normB v μ n Φ` make the statement the honest one.

The content: for every `N ≥ 1`, every smooth symmetric box state `Φ` of the box of side
`ℓ = sideAt μ (a v)`, the **frame tail**

    Σ_j limSlotForm ℓ j Θ − Σ_j frameSlotForm v μ N j Θ

(the difference of the localised-mode frame sums over the `n` slots) is bounded by the
`N⁻²`-decaying payers `C·(ℓ/(2πN))²·pinDirChi ℓ Φ + C·n·‖Φ‖²/N²`, where `Θ = boxRestrictC ℓ Φ`.

## Route

Per slot `j`, both forms slice along the `j`-th coordinate (`fibre_part2` for the limit form, the
rank-one fibre identity `fibre_part1` for the frame form):

    limSlotForm ℓ j Θ   = ∫_{x'} ∫_{w ∈ boxL} χ(w)²‖mf ℓ (sect j x' Φ) w‖²
    frameSlotForm … N j = Σ_{k : Lab N} ∫_{x'} ‖∫_u conj(pinQ_k u)·Θ(x'[j↦u]) du‖²

so the difference is, per fibre `x'`, the **tail of the tight frame** of the one-body state
`sect j x' Φ`.  The tail costs `Λ⁻²` at the cut-off `Λ = 2π(N+1)/ℓ ≤ ‖κ_k‖` for `k ∉ labSet N`
(`norm_ge_of_not_mem_labSet`), and the resulting Dirichlet energy of the fibres is
`2·pinDirChi + 6δ²·n·‖Φ‖²` by the product rule, the slice identity
`setIntegral_insertCoord_slice_weight` and `δ := ‖∇χ_ℓ‖_∞`.
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

/-! ## 1. The complex box restriction -/

/-- The complex box restriction `Ψ · 1_{abox n ℓ}` of a complex state. -/
noncomputable def boxRestrictCX {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℂ) : Xn n → ℂ :=
  fun x => Ψ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℂ)) x

lemma boxRestrictCX_of_mem {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℂ} {x : Xn n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) : boxRestrictCX ℓ Ψ x = Ψ x := by
  simp only [boxRestrictCX, Set.indicator_of_mem hx, mul_one]

lemma boxRestrictCX_of_notMem {n : ℕ} {ℓ : ℝ} {Ψ : Xn n → ℂ} {x : Xn n}
    (hx : x ∉ Submission.BoseGases.abox n ℓ) : boxRestrictCX ℓ Ψ x = 0 := by
  simp only [boxRestrictCX, Set.indicator_of_notMem hx, mul_zero]

lemma boxRestrictCX_support {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℂ) :
    Function.support (boxRestrictCX ℓ Ψ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (boxRestrictCX_of_notMem h)

/-- The complex box restriction of a real state is the corpus's `boxRestrictC`. -/
lemma boxRestrictCX_ofReal {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    boxRestrictCX ℓ (fun x => ((Φ x : ℝ) : ℂ)) = boxRestrictC ℓ Φ := by
  funext x
  simp only [boxRestrictCX, boxRestrictC, Complex.ofReal_mul]
  congr 1
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-! ## 2. Boxes: the cube of the `j`-th coordinate -/

lemma update_mem_abox {n : ℕ} {ℓ : ℝ} {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ)
    (j : Fin n) {y : E3} (hy : y ∈ Submission.BoseGases.acube ℓ) :
    Function.update x j y ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro i
  by_cases h : i = j
  · subst h; rw [Function.update_self]; exact hy
  · rw [Function.update_of_ne h]; exact hx i

lemma insertCoord_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {w : E3}
    {x' : {k : Fin n // k ≠ j} → E3} {y : E3} (hy : y ∈ Submission.BoseGases.acube ℓ)
    (hx' : x' ∈ boxPiSet ({k : Fin n // k ≠ j}) ℓ) :
    Function.update (insertCoord j w x') j y ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff]
  intro i
  by_cases h : i = j
  · subst h; rw [Function.update_self]; exact hy
  · rw [Function.update_of_ne h, insertCoord_eq]
    simp only [dif_neg h]
    have h1 : x' ⟨i, h⟩ ∈ boxL ℓ := (mem_boxPiSet.mp hx') ⟨i, h⟩
    rwa [corpusBox_boxL_eq_acube hℓ] at h1

/-! ## 3. `boxQ` is insensitive to the box restriction -/

/-- On the box, the slot-`j` box projection of the box-restricted state is that of the state. -/
lemma boxQ_boxRestrictCX {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) (Ψ : Xn n → ℂ)
    {x : Xn n} (hx : x ∈ Submission.BoseGases.abox n ℓ) :
    boxQ ℓ j (boxRestrictCX ℓ Ψ) x = boxQ ℓ j Ψ x := by
  have h1 : boxRestrictCX ℓ Ψ x = Ψ x := boxRestrictCX_of_mem hx
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        boxRestrictCX ℓ Ψ (Function.update x j y))
      = ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x j y) := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y hy => ?_)
    exact boxRestrictCX_of_mem (update_mem_abox hx j hy)
  simp only [boxQ, h1, h2]

/-! ## 4. The limit slot form is the fibre box mass -/

theorem limSlotForm_slice {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    limSlotForm ℓ j (boxRestrictCX ℓ Ψ)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
          ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
            * ‖mf ℓ (sect j x' Ψ) w‖ ^ 2 := by
  have h1 : limSlotForm ℓ j (boxRestrictCX ℓ Ψ)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * ‖boxQ ℓ j Ψ x‖ ^ 2 := by
    rw [limSlotForm]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x hx => ?_)
    rw [boxQ_boxRestrictCX hℓ j Ψ hx]
  rw [h1]
  exact fibre_part2 j hℓ hΨ

/-! ## 5. Derivative calculus of the fibre insertion -/

lemma fderiv_insertCoord_cx {n : ℕ} (i : Fin n) {Ψ : Xn n → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (x' : {k : Fin n // k ≠ i} → E3) (w : E3) :
    fderiv ℝ (fun z : E3 => Ψ (insertCoord i z x')) w
      = (fderiv ℝ Ψ (insertCoord i w x')).comp (insCLM i) := by
  have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (insertCoord i w x')) (insertCoord i w x') :=
    ((hΨ.differentiable (by simp)) (insertCoord i w x')).hasFDerivAt
  have h1 : HasFDerivAt (fun z : E3 => insertCoord i z x') (insCLM i) w :=
    hasFDerivAt_insertCoord (i, i) (x', w) w
  exact (hd.comp w h1).fderiv

lemma fderiv_sect_single {n : ℕ} (i : Fin n) {Ψ : Xn n → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (x' : {k : Fin n // k ≠ i} → E3) (w : E3) (m : Fin 3) :
    fderiv ℝ (fun z : E3 => Ψ (insertCoord i z x')) w (EuclideanSpace.single m 1)
      = fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m) := by
  rw [fderiv_insertCoord_cx i hΨ x' w, ContinuousLinearMap.comp_apply]
  exact congrArg _ (by rw [insCLM_apply]; rfl)

lemma fderiv_mf_apply {ℓ : ℝ} (h : E3 → ℂ) (w v : E3) :
    fderiv ℝ (mf ℓ h) w v = fderiv ℝ h w v := by
  have hc : mf ℓ h
      = fun x => h x - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ y in boxL ℓ, h y) := rfl
  rw [hc, fderiv_sub_const]

lemma fderiv_mf_sect_single {n : ℕ} {ℓ : ℝ} (i : Fin n) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (x' : {k : Fin n // k ≠ i} → E3) (w : E3) (m : Fin 3) :
    fderiv ℝ (mf ℓ (sect i x' Ψ)) w (EuclideanSpace.single m 1)
      = fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m) := by
  rw [show mf ℓ (sect i x' Ψ)
      = mf ℓ (fun z : E3 => Ψ (insertCoord i z x')) from rfl]
  rw [show fderiv ℝ (mf ℓ (fun z : E3 => Ψ (insertCoord i z x'))) w
      = fderiv ℝ (fun z : E3 => Ψ (insertCoord i z x')) w from fderiv_sub_const _]
  exact fderiv_sect_single i hΨ x' w m

/-- The complexification's derivative, applied. -/
lemma fderiv_ofReal_apply {n : ℕ} {Φ : Xn n → ℝ} {x : Xn n} (hΦ : DifferentiableAt ℝ Φ x)
    (v : Xn n) :
    fderiv ℝ (fun y => ((Φ y : ℝ) : ℂ)) x v = ((fderiv ℝ Φ x v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y : Xn n => ((Φ y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ Φ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hΦ.hasFDerivAt
  rw [h1.fderiv, ContinuousLinearMap.comp_apply]
  rfl

lemma norm_fderiv_ofReal {n : ℕ} {Φ : Xn n → ℝ} {x : Xn n} (hΦ : DifferentiableAt ℝ Φ x)
    (v : Xn n) :
    ‖fderiv ℝ (fun y => ((Φ y : ℝ) : ℂ)) x v‖ ^ 2 = (fderiv ℝ Φ x v) ^ 2 := by
  rw [fderiv_ofReal_apply hΦ v, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## 6. The fibre quantities and their continuity -/

/-- The `χ²`-weighted fibre box mass of the slot-`j` sections, i.e. the limit slot form. -/
noncomputable def fibreMass {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ) : ℝ :=
  ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
    ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖mf ℓ (sect j x' Ψ) w‖ ^ 2

/- The two fibre quantities paid by the per-slot bound, `fibreMassFree` (the unweighted fibre box
mass, the payer of the window mass) and `fibreWave` (the `χ²`-weighted fibre Dirichlet content),
are **not** defined here: they are supplied, verbatim and under the same names
`Work.BoseBoxFock.PB3V2.fibreMassFree` / `Work.BoseBoxFock.PB3V2.fibreWave`, by the module
`Submission.Work.BoseBoxFock.PB3V2.perSlotAux` (imported through `PB3V2.perSlot_bound`), so that the
per-slot bound `Work.BoseBoxFock.PB3V2.perSlot_bound` — stated in terms of them — is directly
consumable below.  Their values are

    fibreMassFree ℓ j Ψ = ∫_{x' ∈ boxPiSet} ∫_{boxL ℓ} ‖mf ℓ (sect j x' Ψ) w‖² ,
    fibreWave ℓ j Ψ     = ∫_{x' ∈ boxPiSet} ∫_{boxL ℓ} χ_ℓ(w)² Σ_m ‖∂_{j,m}Ψ(insertCoord j w x')‖² .

-/

/-- The limit slot form is the fibre box mass. -/
theorem limSlotForm_eq_fibreMass {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    limSlotForm ℓ j (boxRestrictCX ℓ Ψ) = fibreMass ℓ j Ψ :=
  limSlotForm_slice j hℓ hΨ

lemma continuous_insertCoord_pair {n : ℕ} (j : Fin n) :
    Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 => insertCoord j q.2 q.1 :=
  (continuous_insertCoord j).comp (continuous_snd.prodMk continuous_fst)

lemma continuous_mean_sect {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ} (hΨ : Continuous Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
      ∫ v in boxL ℓ, Ψ (insertCoord j v x') := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (v : E3) => Ψ (insertCoord j v x')) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (v : E3) =>
      Ψ (insertCoord j v x'))
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 => Ψ (insertCoord j q.2 q.1) := rfl
  rw [h]
  exact hΨ.comp (continuous_insertCoord_pair j)

lemma continuous_mf_sect {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ} (hΨ : Continuous Ψ) :
    Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      ‖mf ℓ (sect j q.1 Ψ) q.2‖ ^ 2 := by
  have h1 : Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      Ψ (insertCoord j q.2 q.1) :=
    hΨ.comp (continuous_insertCoord_pair j)
  have h2 : Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      ∫ v in boxL ℓ, Ψ (insertCoord j v q.1) :=
    (continuous_mean_sect (ℓ := ℓ) j hΨ).comp continuous_fst
  have hcont : Continuous fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
      ‖Ψ (insertCoord j q.2 q.1)
        - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ v in boxL ℓ, Ψ (insertCoord j v q.1))‖ ^ 2 :=
    ((h1.sub (continuous_const.mul h2))).norm.pow 2
  simpa only [mf, sect] using hcont

lemma continuous_fibreMassFree {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : Continuous Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
      ∫ w in boxL ℓ, ‖mf ℓ (sect j x' Ψ) w‖ ^ 2 := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      ‖mf ℓ (sect j x' Ψ) w‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      ‖mf ℓ (sect j x' Ψ) w‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 => ‖mf ℓ (sect j q.1 Ψ) q.2‖ ^ 2 := rfl
  rw [h]
  exact continuous_mf_sect j hΨ

lemma continuous_sect_mass {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ} (hΨ : Continuous Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
      ∫ w in boxL ℓ, ‖Ψ (insertCoord j w x')‖ ^ 2 := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      ‖Ψ (insertCoord j w x')‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      ‖Ψ (insertCoord j w x')‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 => ‖Ψ (insertCoord j q.2 q.1)‖ ^ 2 := rfl
  rw [h]
  exact ((hΨ.comp (continuous_insertCoord_pair j))).norm.pow 2

lemma continuous_fibreWave_single {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (m : Fin 3) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
      ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
        (Submission.BoseGases.chiScale ℓ q.2) ^ 2 *
          ‖fderiv ℝ Ψ (insertCoord j q.2 q.1) (slotDirVec j m)‖ ^ 2 := rfl
  rw [h]
  exact (((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).pow 2).mul
    ((((continuous_fderiv_apply hΨ (slotDirVec j m)).comp
      (continuous_insertCoord_pair j)).norm).pow 2)

lemma continuous_fibreWave {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
      ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 := by
  refine continuous_parametric_integral_of_continuous
    (f := fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2) ?_
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
  have h : Function.uncurry (fun (x' : {k : Fin n // k ≠ j} → E3) (w : E3) =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 *
        ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2)
      = fun q : ({k : Fin n // k ≠ j} → E3) × E3 =>
        (Submission.BoseGases.chiScale ℓ q.2) ^ 2 *
          ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord j q.2 q.1) (slotDirVec j m)‖ ^ 2 := rfl
  rw [h]
  exact (((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).pow 2).mul
    (continuous_finsetSum _ (fun m _ =>
      (((continuous_fderiv_apply hΨ (slotDirVec j m)).comp
        (continuous_insertCoord_pair j)).norm).pow 2))

lemma integrable_fibreWave_w {n : ℕ} (j : Fin n) {ℓ : ℝ} {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (m : Fin 3) (x' : {k : Fin n // k ≠ j} → E3) :
    IntegrableOn (fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2 *
      ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2) (boxL ℓ) := by
  refine ((((Submission.BoseGases.chiScale_continuous ℓ).pow 2).mul
    ((((continuous_fderiv_apply hΨ (slotDirVec j m)).comp
      ((continuous_insertCoord j).comp
        (continuous_id.prodMk continuous_const))).norm).pow 2))).continuousOn.integrableOn_compact
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)

/-! ## 7. The Dirichlet content of the fibres -/

theorem sum_fibreWave_eq_pinDirChi {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Xn n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∑ j : Fin n, fibreWave ℓ j (fun x => ((Φ x : ℝ) : ℂ))
      = pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ)) := by
  set Ψ : Xn n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΨdef
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [hΨdef]; exact Complex.ofRealCLM.contDiff.comp hΦ
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hpt : ∀ (j : Fin n) (m : Fin 3) (x' : {k : Fin n // k ≠ j} → E3) (w : E3),
      ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2
        = (fderiv ℝ (fun z : E3 => Φ (insertCoord j z x')) w
            (Submission.BoseGases.kcStdBasis m)) ^ 2 := by
    intro j m x' w
    have h1 : fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)
        = ((fderiv ℝ Φ (insertCoord j w x') (slotDirVec j m) : ℝ) : ℂ) := by
      rw [hΨdef]
      exact fderiv_ofReal_apply (hdiff (insertCoord j w x')) (slotDirVec j m)
    rw [h1]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [fderiv_insertCoord_slice j hΦ x' w m]
  have hj : ∀ j : Fin n, fibreWave ℓ j Ψ
      = ∑ m : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * ‖fderiv ℝ Ψ x (slotDirVec j m)‖ ^ 2 := by
    intro j
    have hGm : ∀ m : Fin 3, Continuous fun x' : {k : Fin n // k ≠ j} → E3 =>
        ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
          ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 :=
      fun m => continuous_fibreWave_single j hΨcd m
    calc fibreWave ℓ j Ψ
        = ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            ∑ m : Fin 3, ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 := by
          unfold fibreWave
          refine setIntegral_congr_fun (isCompact_boxPiSet hℓ).measurableSet (fun x' _ => ?_)
          rw [show (∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
                ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2)
              = ∫ w in boxL ℓ, ∑ m : Fin 3, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
                ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 from by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
            simp only [Finset.mul_sum]]
          rw [integral_finsetSum Finset.univ (fun m _ => integrable_fibreWave_w j hΨcd m x')]
      _ = ∑ m : Fin 3, ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 := by
          rw [integral_finsetSum Finset.univ (fun m _ =>
            (hGm m).continuousOn.integrableOn_compact (isCompact_boxPiSet hℓ))]
      _ = ∑ m : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have hcontG : Continuous (Function.uncurry fun (w : E3)
              (x' : {k : Fin n // k ≠ j} → E3) =>
              (Submission.BoseGases.chiScale ℓ w) ^ 2 *
                ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2) := by
            have h : Continuous fun q : E3 × ({k : Fin n // k ≠ j} → E3) =>
                (Submission.BoseGases.chiScale ℓ q.1) ^ 2 *
                  ‖fderiv ℝ Ψ (insertCoord j q.1 q.2) (slotDirVec j m)‖ ^ 2 :=
              (((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_fst).pow 2).mul
                ((((continuous_fderiv_apply hΨcd (slotDirVec j m)).comp
                  (continuous_insertCoord j)).norm).pow 2)
            exact h
          exact (boxL_boxPiSet_integral_swapR hℓ j (G := fun w x' =>
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              ‖fderiv ℝ Ψ (insertCoord j w x') (slotDirVec j m)‖ ^ 2) hcontG).symm
      _ = ∑ m : Fin 3, ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : E3 => Φ (insertCoord j z x')) w
                (Submission.BoseGases.kcStdBasis m)) ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          refine setIntegral_congr_fun
            (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w _ => ?_)
          refine setIntegral_congr_fun (isCompact_boxPiSet hℓ).measurableSet (fun x' _ => ?_)
          rw [hpt j m x' w]
      _ = ∑ m : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 *
              ‖fderiv ℝ Ψ x (slotDirVec j m)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [hΨdef]
          exact (pinDirChi_slot_slice hℓ hΦ j m).symm
  rw [Finset.sum_congr rfl (fun j _ => hj j), pinDirChi]
  refine (Finset.sum_congr rfl (fun j _ =>
    (integral_finsetSum Finset.univ (fun m _ => ?_)).symm)).trans ?_
  · refine integrableOn_abox_of_continuous hℓ ?_
    exact ((((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)).pow 2).mul
      (((continuous_fderiv_apply hΨcd (slotDirVec j m)).norm).pow 2))
  · refine (integral_finsetSum Finset.univ (fun j _ => ?_)).symm.trans ?_
    · refine integrableOn_abox_of_continuous hℓ ?_
      exact continuous_finsetSum _ (fun m _ => ((((Submission.BoseGases.chiScale_continuous ℓ).comp
        (continuous_apply j)).pow 2).mul
        (((continuous_fderiv_apply hΨcd (slotDirVec j m)).norm).pow 2)))
    · rfl

/-! ## 8. The mass of the fibres -/

theorem sum_fibreMassFree_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℂ} (hΨ : Continuous Ψ) :
    ∑ j : Fin n, fibreMassFree ℓ j Ψ
      ≤ (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ^ 2 := by
  have hstep : ∀ j : Fin n, fibreMassFree ℓ j Ψ
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ^ 2 := by
    intro j
    have hmono : fibreMassFree ℓ j Ψ
        ≤ ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            ∫ w in boxL ℓ, ‖Ψ (insertCoord j w x')‖ ^ 2 := by
      refine setIntegral_mono_on ?_ ?_
        (isCompact_boxPiSet hℓ).measurableSet (fun x' _ => ?_)
      · exact (continuous_fibreMassFree j hΨ).continuousOn.integrableOn_compact
          (isCompact_boxPiSet hℓ)
      · exact (continuous_sect_mass j hΨ).continuousOn.integrableOn_compact
          (isCompact_boxPiSet hℓ)
      · exact mf_L2_le hℓ
          ((hΨ.comp (continuous_insertCoord j)).comp (continuous_id.prodMk continuous_const))
    have hcontG : Continuous (Function.uncurry fun (w : E3)
        (x' : {k : Fin n // k ≠ j} → E3) => ‖Ψ (insertCoord j w x')‖ ^ 2) := by
      have h : Continuous fun q : E3 × ({k : Fin n // k ≠ j} → E3) =>
          ‖Ψ (insertCoord j q.1 q.2)‖ ^ 2 :=
        ((hΨ.comp (continuous_insertCoord j))).norm.pow 2
      exact h
    have hswap : (∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
          ∫ w in boxL ℓ, ‖Ψ (insertCoord j w x')‖ ^ 2)
        = ∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
            ‖Ψ (insertCoord j w x')‖ ^ 2 :=
      (boxL_boxPiSet_integral_swapR hℓ j hcontG).symm
    have hslice : (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
          ‖Ψ (insertCoord j w x')‖ ^ 2)
        = ∫ x in Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ^ 2 :=
      setIntegral_insertCoord_slice hℓ j (hΨ.norm.pow 2)
    rw [hswap, hslice] at hmono
    exact hmono
  calc ∑ j : Fin n, fibreMassFree ℓ j Ψ
      ≤ ∑ _j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => hstep j)
    _ = (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, ‖Ψ x‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 9. The frame slot form as a fibre sum -/

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

/-- A configuration all of whose inserted positions lie in the box is a point of the slice box. -/
lemma mem_boxPiSet_of_insertCoord_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) (u : E3)
    {x' : {l : Fin n // l ≠ j} → E3}
    (h : insertCoord j u x' ∈ Submission.BoseGases.abox n ℓ) :
    x' ∈ boxPiSet ({l : Fin n // l ≠ j}) ℓ := by
  rw [mem_boxPiSet, corpusBox_boxL_eq_acube hℓ]
  intro l
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ (insertCoord j u x')).mp h l.1
  rwa [show insertCoord j u x' l.1 = x' l from by
    rw [insertCoord_eq]; simp only [dif_neg l.2]] at h1

/-- Conversely, an inserted point with `u` outside the cube is outside the box. -/
lemma insertCoord_notMem_abox_of_notMem_acube {n : ℕ} {ℓ : ℝ} (j : Fin n) {u : E3}
    {x' : {l : Fin n // l ≠ j} → E3} (hu : u ∉ Submission.BoseGases.acube ℓ) :
    insertCoord j u x' ∉ Submission.BoseGases.abox n ℓ := by
  intro hcon
  refine hu ?_
  have h1 := (Submission.BoseGases.mem_abox_iff n ℓ (insertCoord j u x')).mp hcon j
  rwa [insertCoord_self] at h1

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
      (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (insertCoord j u x'))
        * (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (insertCoord j u x'))) volume := by
  obtain ⟨Cw, hCw⟩ := hwb
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ (Classical.arbitrary (Xn n)))
  have hCw0 : 0 ≤ Cw := le_trans (norm_nonneg _) (hCw 0)
  set F : ({l : Fin n // l ≠ j} → E3) → ℂ := fun x' => ∫ u : E3,
    (starRingEnd ℂ) (w u) * Θ (insertCoord j u x') with hFdef
  have hFm : Measurable F := by
    rw [hFdef]
    have hjoint : StronglyMeasurable (fun p : ({l : Fin n // l ≠ j} → E3) × E3 =>
        (starRingEnd ℂ) (w p.2) * Θ (insertCoord j p.2 p.1)) :=
      (((Complex.continuous_conj.measurable.comp hwm).stronglyMeasurable).comp_measurable
        measurable_snd).mul
        (hΘm.stronglyMeasurable.comp_measurable
          ((continuous_insertCoord j).comp continuous_swap).measurable)
    exact (StronglyMeasurable.integral_prod_right hjoint).measurable
  have hFbd : ∀ x', ‖F x'‖ ≤ Cw * CΘ * ℓ ^ 3 := by
    intro x'
    have hmaj : Integrable (fun u : E3 => (Cw * CΘ) *
        (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u) volume := by
      refine Integrable.const_mul ?_ _
      refine IntegrableOn.integrable_indicator (integrableOn_const ?_ (by simp))
        (Submission.BoseGases.acube_measurable _)
      exact (Submission.BoseGases.acube_lt_top ℓ hℓ.le).ne
    have hbd : ∀ u : E3, ‖(starRingEnd ℂ) (w u) * Θ (insertCoord j u x')‖
        ≤ (Cw * CΘ) * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) u := by
      intro u
      rw [norm_mul, Complex.norm_conj]
      by_cases hu : u ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hu, mul_one]
        exact mul_le_mul (hCw u) (hCΘ _) (norm_nonneg _) hCw0
      · rw [theta_zero_of_notMem_abox hΘs (insertCoord_notMem_abox_of_notMem_acube j hu),
          norm_zero, mul_zero, Set.indicator_of_notMem hu, mul_zero]
    have haesm : AEStronglyMeasurable (fun u : E3 =>
        ‖(starRingEnd ℂ) (w u) * Θ (insertCoord j u x')‖) volume :=
      ((((Complex.continuous_conj.measurable.comp hwm).aestronglyMeasurable).mul
        ((hΘm.comp ((continuous_insertCoord j).comp
          (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable))).norm
    rw [hFdef]
    calc ‖∫ u : E3, (starRingEnd ℂ) (w u) * Θ (insertCoord j u x')‖
        ≤ ∫ u : E3, ‖(starRingEnd ℂ) (w u) * Θ (insertCoord j u x')‖ :=
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
    show (∫ u : E3, (starRingEnd ℂ) (w u) * Θ (insertCoord j u x')) = 0
    have h0 : (fun u : E3 => (starRingEnd ℂ) (w u) * Θ (insertCoord j u x')) = fun _ => 0 := by
      funext u
      by_cases hmem : insertCoord j u x' ∈ Submission.BoseGases.abox n ℓ
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
    frameSlotForm v μ N j (boxRestrictC (ellH v μ) Φ)
      = ∑ k : Lab N, ∫ x' : {k : Fin n // k ≠ j} → E3,
          ‖∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
            * (boxRestrictC (ellH v μ) Φ) (insertCoord j u x')‖ ^ 2 := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hΘm : Measurable (boxRestrictC (ellH v μ) Φ) :=
    measurable_boxRestrictC _ hΦ.continuous.measurable
  obtain ⟨CΘ, hCΘ⟩ := bdd_boxRestrictC hℓ hΦ.continuous
  have hΘs : Function.support (boxRestrictC (ellH v μ) Φ)
      ⊆ Submission.BoseGases.abox n (ellH v μ) := support_boxRestrictC _ _
  have hmeq : ∀ k : Lab N,
      (∫ x in Submission.BoseGases.abox n (ellH v μ),
          (starRingEnd ℂ) (boxRestrictC (ellH v μ) Φ x)
            * (pinQ v μ N k (x j) * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                * boxRestrictC (ellH v μ) Φ (Function.update x j u))))
        = ∫ x' : {k : Fin n // k ≠ j} → E3,
            (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                * boxRestrictC (ellH v μ) Φ (insertCoord j u x'))
              * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                * boxRestrictC (ellH v μ) Φ (insertCoord j u x')) := by
    intro k
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox n (ellH v μ)) (f := fun x => (starRingEnd ℂ)
        (boxRestrictC (ellH v μ) Φ x)
          * (pinQ v μ N k (x j) * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
              * boxRestrictC (ellH v μ) Φ (Function.update x j u)))) (fun x hx => by
        rw [theta_zero_of_notMem_abox hΘs hx, map_zero, zero_mul])]
    exact slotForm_slice j hΘm ⟨CΘ, hCΘ⟩ hΘs
      (pinQ_measurable v μ N k).aestronglyMeasurable ((pinQ_bdd v μ N k).imp fun C h => h.2)
  have hsum : frameSlotForm v μ N j (boxRestrictC (ellH v μ) Φ)
      = (∑ k : Lab N, ∫ x' : {k : Fin n // k ≠ j} → E3,
          (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
              * boxRestrictC (ellH v μ) Φ (insertCoord j u x'))
            * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
              * boxRestrictC (ellH v μ) Φ (insertCoord j u x'))).re := by
    rw [frameSlotForm]
    exact congrArg Complex.re (Finset.sum_congr rfl (fun k _ => hmeq k))
  rw [hsum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine re_integral_conj_mul_self (A := fun x' : {l : Fin n // l ≠ j} → E3 =>
    ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
      * boxRestrictC (ellH v μ) Φ (insertCoord j u x')) ?_
  exact integrable_fibre_conj_mul hℓ j (pinQ_measurable v μ N k)
    ((pinQ_bdd v μ N k).imp fun C h => h.2) hΘm ⟨CΘ, hCΘ⟩ hΘs

/-! ## 10. The product-rule energy bound of the fibre -/

lemma kcStdBasis_eq_single (m : Fin 3) :
    Submission.BoseGases.kcStdBasis m = EuclideanSpace.single m (1 : ℝ) := rfl

lemma fderiv_chiScale_eq_zero_of_notMem {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∉ boxL ℓ) : fderiv ℝ (Submission.BoseGases.chiScale ℓ) x = 0 := by
  have hclosed : IsClosed (boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed
  have hmem : (fun y : E3 => Submission.BoseGases.chiScale ℓ y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    exact Work.BoseBoxFock.chiScale_eq_zero_of_notMem hℓ hy
  rw [hmem.fderiv_eq]
  simp

lemma fderiv_ofReal_chiScale {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) :
    fderiv ℝ (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)) x
      = Complex.ofRealCLM.comp (fderiv ℝ (Submission.BoseGases.chiScale ℓ) x) := by
  have h1 : HasFDerivAt (fun z : E3 => Submission.BoseGases.chiScale ℓ z)
      (fderiv ℝ (Submission.BoseGases.chiScale ℓ) x) x :=
    (((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable (by simp)) x).hasFDerivAt
  exact (Complex.ofRealCLM.hasFDerivAt.comp x h1).fderiv

lemma secondMoment_single {g : E3 → ℂ} (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = ∑ m : Fin 3, ∫ z : E3, ‖fderiv ℝ g z (EuclideanSpace.single m 1)‖ ^ 2 := by
  simpa only [kcStdBasis_eq_single] using L1Tails.secondMomentPlancherelOne hg hgs

/-- A continuous real function vanishing off the box is integrable. -/
lemma integrable_of_continuous_eqZero_off {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ}
    (hf : Continuous f) (hs : ∀ z : E3, z ∉ boxL ℓ → f z = 0) : Integrable f volume :=
  (integrableOn_iff_integrable_of_support_subset (fun z hz => by
    rw [Function.mem_support] at hz
    by_contra h
    exact hz (hs z h))).mp
    (hf.continuousOn.integrableOn_compact
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ))

lemma continuous_fderiv_chiScale_single {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin 3) :
    Continuous (fun z : E3 => fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
      (EuclideanSpace.single m 1)) :=
  ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous_fderiv
    (by simp)).clm_apply continuous_const

theorem fibreEnergy_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Ψ : Xn n → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x v : E3, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v| ≤ D * ‖v‖)
    (x' : {k : Fin n // k ≠ i} → E3) :
    ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT
          (fun w : E3 => ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * mf ℓ (sect i x' Ψ) w) p‖ ^ 2
      ≤ 6 * D ^ 2 * (∫ w in boxL ℓ, ‖mf ℓ (sect i x' Ψ) w‖ ^ 2)
        + 2 * ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
            ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m)‖ ^ 2 := by
  have hins : ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => insertCoord i z x') := by
    have h1 : (fun z : E3 => insertCoord i z x')
        = fun z => insCLM i z + insertCoord i 0 x' := by
      funext z
      exact insertCoord_eq_insCLM (i, i) (x', z) z
    rw [h1]
    exact (insCLM i).contDiff.add contDiff_const
  have hφcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => Ψ (insertCoord i y x')) := hΨ.comp hins
  set g : E3 → ℂ := fun z => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
    * mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z with hgdef
  have hgc : ContDiff ℝ 1 g := by
    rw [hgdef]
    exact chiMf_contDiff hℓ (hφcd.of_le (by simp))
  have hgs : HasCompactSupport g := by
    rw [hgdef]
    exact IsCompact.of_isClosed_subset
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ) (isClosed_tsupport _)
      (chiMf_tsupport_subset hℓ (fun y : E3 => Ψ (insertCoord i y x')))
  have hconv : ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT
          (fun w : E3 => ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * mf ℓ (sect i x' Ψ) w) p‖ ^ 2
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := rfl
  rw [hconv, secondMoment_single hgc hgs]
  -- the pointwise derivative identity
  have hderiv : ∀ (m : Fin 3) (z : E3), fderiv ℝ g z (EuclideanSpace.single m 1)
      = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
          * fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)
        + (mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z)
          * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ) : ℂ) := by
    intro m z
    have hdiff1 : DifferentiableAt ℝ
        (fun y : E3 => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) z :=
      ((Complex.ofRealCLM.contDiff.comp
        (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ))).differentiable (by simp)) z
    have hdiff2 : DifferentiableAt ℝ (mf ℓ (fun y : E3 => Ψ (insertCoord i y x'))) z := by
      have heq : mf ℓ (fun y : E3 => Ψ (insertCoord i y x'))
          = fun y : E3 => (fun y : E3 => Ψ (insertCoord i y x')) y
              - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ y in boxL ℓ, Ψ (insertCoord i y x')) := rfl
      rw [heq]
      exact ((hφcd.differentiable (by simp)) z).sub_const _
    have hgfun : g = (fun y : E3 => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
        * mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) := rfl
    rw [hgfun, fderiv_mul hdiff1 hdiff2, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    have h1 : fderiv ℝ (mf ℓ (fun y : E3 => Ψ (insertCoord i y x'))) z
        (EuclideanSpace.single m 1)
        = fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m) := by
      show fderiv ℝ (mf ℓ (sect i x' Ψ)) z (EuclideanSpace.single m 1) = _
      exact fderiv_mf_sect_single i hΨ x' z m
    have h2 : fderiv ℝ (fun y : E3 => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)) z
        (EuclideanSpace.single m 1)
        = ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
            (EuclideanSpace.single m 1) : ℝ) : ℂ) := by
      rw [fderiv_ofReal_chiScale hℓ z, ContinuousLinearMap.comp_apply]
      rfl
    rw [h1, h2, smul_eq_mul, smul_eq_mul]
  -- the pointwise norm bound
  have hbd : ∀ (m : Fin 3) (z : E3), ‖fderiv ℝ g z (EuclideanSpace.single m 1)‖ ^ 2
      ≤ 2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
          * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2
        + 2 * ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖ ^ 2
          * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ)‖ ^ 2 := by
    intro m z
    rw [hderiv m z]
    have h1 : ‖((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
          * (fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)
          + (mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z)
            * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1) : ℝ) : ℂ)‖
        ≤ |Submission.BoseGases.chiScale ℓ z|
            * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
          + ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
            * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1))| := by
      calc ‖((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
              * (fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)
            + (mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z)
              * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ) : ℂ)‖
          ≤ ‖((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
              * (fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
            + ‖(mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z)
              * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |Submission.BoseGases.chiScale ℓ z|
              * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
            + ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
              * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1))| := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
              Real.norm_eq_abs]
    have h2 : ‖((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
          * (fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)
          + (mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z)
            * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1) : ℝ) : ℂ)‖ ^ 2
        ≤ (|Submission.BoseGases.chiScale ℓ z|
            * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
          + ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
            * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1))|) ^ 2 := by
      nlinarith [h1,
        norm_nonneg (((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
          * (fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)
          + (mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z)
            * ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1) : ℝ) : ℂ)),
        abs_nonneg (Submission.BoseGases.chiScale ℓ z),
        norm_nonneg ((fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)),
        norm_nonneg (mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z),
        abs_nonneg (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (EuclideanSpace.single m 1))]
    have h3 : (|Submission.BoseGases.chiScale ℓ z|
            * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
          + ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
            * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1))|) ^ 2
        ≤ 2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
            * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖ ^ 2
          + 2 * ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖ ^ 2
            * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1) : ℝ)‖ ^ 2 := by
      have hχ2 : |Submission.BoseGases.chiScale ℓ z| ^ 2
          = (Submission.BoseGases.chiScale ℓ z) ^ 2 := sq_abs _
      have hA2 : |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
            (EuclideanSpace.single m 1))|
          = ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ)‖ := (Real.norm_eq_abs _).symm
      have hstep : (|Submission.BoseGases.chiScale ℓ z|
              * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
            + ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
              * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1))|) ^ 2
          ≤ 2 * (|Submission.BoseGases.chiScale ℓ z|
                * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖) ^ 2
            + 2 * (‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
                * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                    (EuclideanSpace.single m 1))|) ^ 2 := by
        nlinarith [sq_nonneg (|Submission.BoseGases.chiScale ℓ z|
              * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖
            - ‖mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) z‖
              * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1))|)]
      refine hstep.trans ?_
      rw [mul_pow, mul_pow, hχ2, hA2]
      linarith [le_refl (Submission.BoseGases.chiScale ℓ z ^ 2
        * ‖(fderiv ℝ Ψ (insertCoord i z x')) (slotDirVec i m)‖ ^ 2 * 2)]
    exact h2.trans h3
  -- integrability: each piece is continuous and vanishes off `boxL ℓ`
  have hmfc : Continuous (fun z : E3 => ‖mf ℓ (sect i x' Ψ) z‖ ^ 2) :=
    (continuous_mf_sect i hΨ.continuous).comp
      ((continuous_const : Continuous fun _ : E3 => x').prodMk continuous_id)
  have hInt_χL : ∀ m : Fin 3, Integrable (fun z : E3 => (Submission.BoseGases.chiScale ℓ z) ^ 2
      * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2) volume := by
    intro m
    refine integrable_of_continuous_eqZero_off hℓ ?_ ?_
    · exact (((Submission.BoseGases.chiScale_continuous ℓ).pow 2).mul
        (((continuous_fderiv_apply hΨ (slotDirVec i m)).comp
          ((continuous_insertCoord i).comp
            (continuous_id.prodMk continuous_const))).norm.pow 2))
    · intro z hz
      rw [Work.BoseBoxFock.chiScale_eq_zero_of_notMem hℓ hz]
      ring
  have hInt_mfA : ∀ m : Fin 3, Integrable (fun z : E3 => ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
      * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (EuclideanSpace.single m 1) : ℝ)‖ ^ 2)
      volume := by
    intro m
    refine integrable_of_continuous_eqZero_off hℓ ?_ ?_
    · exact hmfc.mul ((continuous_fderiv_chiScale_single hℓ m).norm.pow 2)
    · intro z hz
      rw [show fderiv ℝ (Submission.BoseGases.chiScale ℓ) z = 0 from
        fderiv_chiScale_eq_zero_of_notMem hℓ hz]
      simp
  have hInt_g : ∀ m : Fin 3, Integrable (fun z : E3 =>
      ‖fderiv ℝ g z (EuclideanSpace.single m 1)‖ ^ 2) volume := by
    intro m
    refine integrable_of_continuous_eqZero_off hℓ ?_ ?_
    · exact (((hgc.continuous_fderiv (by norm_num)).clm_apply
        continuous_const).norm.pow 2)
    · intro z hz
      have hclosed : IsClosed (boxL ℓ) :=
        (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).isClosed
      have hev : g =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hclosed.isOpen_compl.mem_nhds hz] with y hy
        show ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
          * mf ℓ (fun y : E3 => Ψ (insertCoord i y x')) y = 0
        rw [Work.BoseBoxFock.chiScale_eq_zero_of_notMem hℓ hy]
        simp
      rw [hev.fderiv_eq]
      simp
  -- the pointwise bound holds for every `z`, so integrate it
  have hbound : ∀ m : Fin 3,
      ∫ z : E3, ‖fderiv ℝ g z (EuclideanSpace.single m 1)‖ ^ 2
        ≤ 2 * (∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2) := by
    intro m
    have hIntR : Integrable (fun z : E3 => 2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
        * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2
        + 2 * ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
          * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ)‖ ^ 2) volume := by
      refine Integrable.add ?_ ?_
      · simpa only [mul_assoc] using (hInt_χL m).const_mul 2
      · simpa only [mul_assoc] using (hInt_mfA m).const_mul 2
    have hmono := integral_mono (hInt_g m) hIntR (fun z => hbd m z)
    have hsplit : (∫ z : E3, (2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
          * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2
        + 2 * ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
          * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ)‖ ^ 2))
        = 2 * (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * (∫ z : E3, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
              * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ)‖ ^ 2) := by
      simp only [mul_assoc]
      rw [MeasureTheory.integral_add ((hInt_χL m).const_mul 2) ((hInt_mfA m).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hχbox : (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2
          * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
        = ∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
            * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := boxL ℓ) (f := fun z : E3 => (Submission.BoseGases.chiScale ℓ z) ^ 2
          * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
        (fun z hz => by
          rw [Work.BoseBoxFock.chiScale_eq_zero_of_notMem hℓ hz]; ring)).symm
    have hAbox : (∫ z : E3, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
          * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ)‖ ^ 2)
        ≤ D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2) := by
      rw [(MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := boxL ℓ) (f := fun z : E3 => ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
          * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single m 1) : ℝ)‖ ^ 2)
        (fun z hz => by
          rw [show fderiv ℝ (Submission.BoseGases.chiScale ℓ) z = 0 from
            fderiv_chiScale_eq_zero_of_notMem hℓ hz]; simp)).symm]
      calc (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
            * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single m 1) : ℝ)‖ ^ 2)
          ≤ ∫ z in boxL ℓ, D ^ 2 * ‖mf ℓ (sect i x' Ψ) z‖ ^ 2 := by
            refine setIntegral_mono_on ?_ ?_ (Work.BoseB4.BoxData.boxL_measurableSet
              Work.BoseK15.corpusBox ℓ) (fun z _ => ?_)
            · exact ((hmfc.mul ((continuous_fderiv_chiScale_single hℓ m).norm.pow 2)
                |>.continuousOn.integrableOn_compact
                (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)))
            · exact (((hmfc.const_mul (D ^ 2))
                |>.continuousOn.integrableOn_compact
                (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)))
            · have h1 : ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ)‖ ≤ D := by
                rw [Real.norm_eq_abs]
                calc |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                      (EuclideanSpace.single m 1)|
                    ≤ D * ‖EuclideanSpace.single m (1 : ℝ)‖ := hD z _
                  _ = D * 1 := by rw [EuclideanSpace.norm_single, norm_one]
                  _ = D := mul_one D
              calc ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
                    * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                        (EuclideanSpace.single m 1) : ℝ)‖ ^ 2
                  ≤ ‖mf ℓ (sect i x' Ψ) z‖ ^ 2 * D ^ 2 :=
                    mul_le_mul_of_nonneg_left (by
                      nlinarith [h1, norm_nonneg (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                        (EuclideanSpace.single m 1)), hD0]) (sq_nonneg _)
                _ = D ^ 2 * ‖mf ℓ (sect i x' Ψ) z‖ ^ 2 := by ring
        _ = D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2) := by
            rw [MeasureTheory.integral_const_mul]
    calc ∫ z : E3, ‖fderiv ℝ g z (EuclideanSpace.single m 1)‖ ^ 2
        ≤ ∫ z : E3, (2 * (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2
            + 2 * ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
              * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ)‖ ^ 2) := hmono
      _ = 2 * (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * (∫ z : E3, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
              * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ)‖ ^ 2) := hsplit
      _ = 2 * (∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * (∫ z : E3, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2
              * ‖(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (EuclideanSpace.single m 1) : ℝ)‖ ^ 2) := by rw [hχbox]
      _ ≤ 2 * (∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * (D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2)) := by
        linarith [hAbox]
      _ = 2 * (∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2) := by ring
  have hsumfibre : (∑ m : Fin 3, ∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
        * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
      = ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
          * ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m)‖ ^ 2 := by
    rw [← integral_finsetSum Finset.univ (fun m _ => (hInt_χL m).integrableOn)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    show (∑ m : Fin 3, (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ‖fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m)‖ ^ 2)
      = (Submission.BoseGases.chiScale ℓ w) ^ 2
        * ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m)‖ ^ 2
    rw [Finset.mul_sum]
  calc ∑ m : Fin 3, ∫ z : E3, ‖fderiv ℝ g z (EuclideanSpace.single m 1)‖ ^ 2
      ≤ ∑ m : Fin 3, (2 * (∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 2 * D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2)) :=
        Finset.sum_le_sum (fun m _ => hbound m)
    _ = 2 * (∑ m : Fin 3, ∫ z in boxL ℓ, (Submission.BoseGases.chiScale ℓ z) ^ 2
              * ‖fderiv ℝ Ψ (insertCoord i z x') (slotDirVec i m)‖ ^ 2)
          + 6 * D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = 6 * D ^ 2 * (∫ z in boxL ℓ, ‖mf ℓ (sect i x' Ψ) z‖ ^ 2)
          + 2 * (∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2
              * ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m)‖ ^ 2) := by
        rw [hsumfibre]
        ring
    _ = 6 * D ^ 2 * (∫ w in boxL ℓ, ‖mf ℓ (sect i x' Ψ) w‖ ^ 2)
          + 2 * ∫ w in boxL ℓ, (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              ∑ m : Fin 3, ‖fderiv ℝ Ψ (insertCoord i w x') (slotDirVec i m)‖ ^ 2 := by
        rfl


/-! ## 11. The final arithmetic -/

lemma arith_bound {ℓ D M pin C : ℝ} {N : ℕ} (hℓ : 0 < ℓ) (hN : 1 ≤ N)
    (hM : 0 ≤ M) (hpin : 0 ≤ pin) (hC2 : 2 ≤ C)
    (hCD : 6 * D ^ 2 * ℓ ^ 2 / (2 * Real.pi) ^ 2 ≤ C) :
    ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2 * M + 2 * pin)
      ≤ C * (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin + C * M / ((N : ℝ) ^ 2) := by
  have hR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hsq : (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2
      = ℓ ^ 2 / (2 * Real.pi) ^ 2 / (N : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, div_div]
  have hΛ2 : (2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2
      = (2 * Real.pi * ((N : ℝ) + 1)) ^ 2 / ℓ ^ 2 := by
    rw [div_pow]
  -- the reciprocal of `Λ²` is dominated by `(ℓ/(2πN))²`
  have hB : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹
      ≤ (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 := by
    rw [hΛ2, hsq, inv_div, div_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    have h3 : (2 * Real.pi) ^ 2 * (N : ℝ) ^ 2 = (2 * Real.pi * (N : ℝ)) ^ 2 := by ring
    rw [h3]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [hpi, hR]) 2
  -- first row
  have hrow1 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2 * M)
      ≤ C * M / ((N : ℝ) ^ 2) := by
    have h6 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2)
        ≤ C / ((N : ℝ) ^ 2) := by
      have h8 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2)
          ≤ (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * (6 * D ^ 2) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      have h9 : (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * (6 * D ^ 2)
          = 6 * D ^ 2 * ℓ ^ 2 / (2 * Real.pi) ^ 2 / (N : ℝ) ^ 2 := by
        rw [hsq]; ring
      have h10 : 6 * D ^ 2 * ℓ ^ 2 / (2 * Real.pi) ^ 2 / (N : ℝ) ^ 2
          ≤ C / ((N : ℝ) ^ 2) := by
        rw [div_le_div_iff_of_pos_right (by positivity)]
        exact hCD
      linarith [h8, h9, h10]
    have h11 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2 * M)
        = (((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2)) * M := by ring
    have h12 : C * M / ((N : ℝ) ^ 2) = (C / ((N : ℝ) ^ 2)) * M := by ring
    rw [h11, h12]
    exact mul_le_mul_of_nonneg_right h6 hM
  -- second row
  have hrow2 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (2 * pin)
      ≤ C * (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin := by
    have h8 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * pin
        ≤ (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin :=
      mul_le_mul_of_nonneg_right hB hpin
    have h10 : 2 * (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin
        ≤ C * (ℓ / (2 * Real.pi * (N : ℝ))) ^ 2 * pin :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2 (by positivity)) hpin
    have h12 : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (2 * pin)
        = 2 * (((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * pin) := by ring
    rw [h12]
    linarith [h8, h10]
  have hsplit : ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2 * M + 2 * pin)
      = ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (6 * D ^ 2 * M)
        + ((2 * Real.pi * ((N : ℝ) + 1) / ℓ) ^ 2)⁻¹ * (2 * pin) := by ring
  rw [hsplit]
  linarith [hrow1, hrow2]

/-! ## 13. The per-slot tail bound and the assembly -/

/-- **The per-slot frame-tail bound**: the `PB3V2`-internal re-export of the proved
`Work.BoseBoxFock.PB3V2.perSlot_bound` (its statement mentions the same `fibreMassFree`/`fibreWave`
of `PB3V2.perSlotAux`). -/
theorem perSlot_bound_aux {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (N : ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {D Λ : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x w : EuclideanSpace ℝ (Fin 3),
        |fderiv ℝ (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ)) x w| ≤ D * ‖w‖)
    (hΛ : 0 < Λ)
    (hΛk : ∀ k : Fin 3 → ℤ, k ∉ Work.BoseBoxFock.labSet N →
        Λ ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k‖)
    (j : Fin n) :
    Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      - Work.BoseBoxFock.frameSlotForm v μ N j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * Work.BoseBoxFock.PB3V2.fibreMassFree
            (Work.BoseBoxFock.ellH v μ) j (fun x => ((Φ x : ℝ) : ℂ))
          + 2 * Work.BoseBoxFock.PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j
            (fun x => ((Φ x : ℝ) : ℂ))) :=
  Work.BoseBoxFock.PB3V2.perSlot_bound N hΦ hD0 hD hΛ hΛk j

end PB3V2

theorem PB3SecondHalfV2 {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))},
      0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
      (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBox.sideAt μ (BoseGases.a v)) j
          (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X n → ℝ)))
        - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
            (Work.BoseBoxFock.boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Φ : Submission.BoseGases.X n → ℝ)))
        ≤ C * (Work.BoseBox.sideAt μ (BoseGases.a v) / (2 * Real.pi * (N : ℝ))) ^ 2
              * Work.BoseBoxFock.pinDirChi (Work.BoseBox.sideAt μ (BoseGases.a v))
                  (fun x => (((Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ))
          + C * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
              / ((N : ℝ) ^ 2) := by
  have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hℓE : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hℓpos]
  obtain ⟨Cchi, D, hCchi0, hD0, hCchi, hD⟩ :=
    Work.BSKinetic.exists_chiScale_bound (s := Work.BoseBox.sideAt μ (BoseGases.a v))
      (ne_of_gt hℓpos)
  refine ⟨max 2 (6 * D ^ 2 * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 2 / (2 * Real.pi) ^ 2),
    le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left (2 : ℝ) _), ?_⟩
  intro N hN Φ hnorm
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  set Ψ : Work.BoseDict.Xn n → ℂ :=
    fun x => (((Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ) with hΨdef
  let Λ : ℝ := 2 * Real.pi * ((N : ℝ) + 1) / Work.BoseBoxFock.ellH v μ
  have hΛpos : 0 < Λ :=
    div_pos (by positivity) (Work.BoseBoxFock.ellH_pos v μ)
  have hD' : ∀ x w : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ)) x w| ≤ D * ‖w‖ := by
    intro x w
    rw [hℓE]
    exact hD x w
  have hΛk : ∀ k : Fin 3 → ℤ, k ∉ Work.BoseBoxFock.labSet N →
      Λ ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k‖ := by
    intro k hk
    have h1 : (N : ℝ) + 1 ≤ ‖Work.BoseBoxFock.latVec k‖ :=
      Work.BoseBoxFock.norm_ge_of_not_mem_labSet hk
    have h2 : ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k‖
        = 2 * Real.pi * ‖Work.BoseBoxFock.latVec k‖ / Work.BoseBoxFock.ellH v μ := by
      rw [show Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k
            = (Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec k from rfl, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Work.BoseBoxFock.ellH_pos v μ).le),
        Work.BoseBoxFock.L1Tails.norm_vec_eq_latVec, inv_mul_eq_div]
    rw [show Λ = 2 * Real.pi * ((N : ℝ) + 1) / Work.BoseBoxFock.ellH v μ from rfl, h2,
      div_le_div_iff_of_pos_right (Work.BoseBoxFock.ellH_pos v μ)]
    nlinarith [Real.pi_pos, h1]
  -- the per-slot bound
  have hper : ∀ j : Fin n,
      Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
          (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ))
        - Work.BoseBoxFock.frameSlotForm v μ N j
            (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))
        ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ
            + 2 * PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ) := by
    intro j
    have h := PB3V2.perSlot_bound_aux (v := v) (μ := μ) N
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hΦcd hD0 hD' hΛpos hΛk j
    simpa only [hΨdef] using h
  -- the sum over the slots
  have hsum : (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ)))
      - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ)))
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
          + 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)) := by
    rw [← Finset.sum_sub_distrib]
    calc (∑ j : Fin n, (Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
            (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))
          - Work.BoseBoxFock.frameSlotForm v μ N j
              (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ))))
        ≤ ∑ j : Fin n, (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ
            + 2 * PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ) :=
          Finset.sum_le_sum (fun j _ => hper j)
      _ = (Λ ^ 2)⁻¹ * (∑ j : Fin n, (6 * D ^ 2 * PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ
            + 2 * PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)) := by rw [Finset.mul_sum]
      _ = (Λ ^ 2)⁻¹ * (6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
            + 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the two state functionals
  have hnormB : (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), ‖Ψ x‖ ^ 2)
      = Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hℓE]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n _)
      (fun x _ => ?_)
    rw [hΨdef]
    simp only []
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hM : (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
      ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have hcont : Continuous Ψ := by
      rw [hΨdef]
      exact Complex.continuous_ofReal.comp hΦcd.continuous
    have h := PB3V2.sum_fibreMassFree_le (ℓ := Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ) hcont
    rw [hnormB] at h
    exact h
  have hG : (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)
      = Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ := by
    have h := PB3V2.sum_fibreWave_eq_pinDirChi (ℓ := Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ) hΦcd
    simpa only [hΨdef] using h
  -- assembly
  have hkey : (Λ ^ 2)⁻¹ * (6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
        + 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ))
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n
            (Φ : Submission.BoseGases.X n → ℝ))
          + 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg Λ))
    have h1 : 6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
        ≤ 6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n
            (Φ : Submission.BoseGases.X n → ℝ)) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have h2 : 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)
        ≤ 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ := by rw [hG]
    linarith [h1, h2]
  have hfin : (Λ ^ 2)⁻¹ * (6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n
          (Φ : Submission.BoseGases.X n → ℝ))
        + 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ)
      ≤ max 2 (6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2)
          * (Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
          * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ
        + max 2 (6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2)
          * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
          / ((N : ℝ) ^ 2) :=
    PB3V2.arith_bound (ℓ := Work.BoseBoxFock.ellH v μ) (D := D)
      (M := (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      (pin := Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ)
      (C := max 2 (6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2))
      (Work.BoseBoxFock.ellH_pos v μ) hN (mul_nonneg (Nat.cast_nonneg n) hnorm.le)
      (Work.BoseBoxFock.pinDirChi_nonneg _ Ψ) (le_max_left (2 : ℝ) _) (le_max_right (2 : ℝ) _)
  have hmain : (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ)))
      - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ)))
      ≤ max 2 (6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2)
          * (Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
          * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ
        + max 2 (6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2)
          * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
          / ((N : ℝ) ^ 2) :=
    le_trans hsum (le_trans hkey hfin)
  rw [hℓE] at hmain
  exact hmain

end Work.BoseBoxFock
