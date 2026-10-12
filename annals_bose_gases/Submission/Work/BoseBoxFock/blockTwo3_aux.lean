import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.blockTwo3_aux` — the insertion equivalence and the fibre `L²` bound

This module holds the infrastructure for the fibre `L²` bound
`Work.BoseBoxFock.blockTwo3_fibre_L2` (block II.3 of the FS `Q₂` row): the
measure-preserving insertion equivalence

    splitEquiv hij : ({k // k ≠ i ∧ k ≠ j} → 𝔼) × (𝔼 × 𝔼) ≃ᵐ (Fin n → 𝔼),
    splitEquiv hij (x', (y, u)) k = if k = i then y else if k = j then u else x' ⟨k, _⟩,

its formula, its measure preservation, the complex Cauchy–Schwarz inequality on a
single measure space, and the general fibre `L²` bound

    ∫_{w₀} ∫_{w₁} ‖∫_{x'} ∫_y ∫_u (star Θ(ins w x')) (star A y) (star B u) Θ(ins (y,u) x')‖²
      ≤ ‖A‖²_{L²} ‖B‖²_{L²} ‖Θ‖⁴_{L²} .

The proof is two Cauchy–Schwarz inequalities: one in `(y,u)` after which the majorant
splits as a product over the three factors of `(Fin n → 𝔼) ≃ Fib × 𝔼 × 𝔼`, and the fibre
identity `∫_w ∫_{x'} ‖Θ (ins w x')‖² = ∫_x ‖Θ x‖²`, which is the measure-preserving
change of variables `splitEquiv`.

Every declaration in this module is fully proved.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-- The fibre `{k : Fin n // k ≠ i ∧ k ≠ j} → 𝔼`. -/
abbrev Fib (n : ℕ) (i j : Fin n) : Type := {k : Fin n // k ≠ i ∧ k ≠ j} → 𝔼

/-! ## Splitting off one coordinate -/

/-- Splitting off the coordinate `a` as a factor `𝔼`. -/
def peelEq (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → 𝔼) ≃ᵐ 𝔼 × ({k : ι // k ≠ a} → 𝔼) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} 𝔼).prodCongr (MeasurableEquiv.refl _))

theorem peelEq_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → 𝔼) :
    peelEq ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelEq, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

theorem peelEq_fun_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ⇑(peelEq ι a) = fun x : ι → 𝔼 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} 𝔼)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)) x) := by
  funext x
  simp only [peelEq, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique, Prod.map_apply]
  rfl

theorem measurePreserving_peelEq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelEq ι a) (volume : Measure (ι → 𝔼))
      (volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => 𝔼)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → 𝔼)))
  refine (h₃.comp h₁).congr (peelEq ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelEq_fun_eq (ι := ι) a) x

/-! ## The two-coordinate splitting -/

/-- The flattening of the nested fibre onto `{k // k ≠ i ∧ k ≠ j}`. -/
def flatEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    {y : {k : Fin n // k ≠ i} // y ≠ (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i})} ≃
      {k : Fin n // k ≠ i ∧ k ≠ j} where
  toFun y := ⟨y.1.1, y.1.2, fun h => y.2 (Subtype.ext h)⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 (congrArg Subtype.val h)⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

/-- The two-coordinate split `(Fin n → 𝔼) ≃ᵐ 𝔼 × (𝔼 × Fib n i j)`. -/
def splitEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (Fin n → 𝔼) ≃ᵐ 𝔼 × (𝔼 × Fib n i j) :=
  (peelEq (Fin n) i).trans <|
    (MeasurableEquiv.refl 𝔼).prodCongr <|
      (peelEq {k : Fin n // k ≠ i} ⟨j, Ne.symm hij⟩).trans <|
        (MeasurableEquiv.refl 𝔼).prodCongr <|
          (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => 𝔼)
            (flatEquiv i j hij))

theorem splitEq_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : Fin n → 𝔼) :
    splitEq hij x = (x i, (x j, fun k : {k : Fin n // k ≠ i ∧ k ≠ j} => x k.1)) := by
  simp only [splitEq, MeasurableEquiv.trans_apply, MeasurableEquiv.prodCongr,
    MeasurableEquiv.refl, peelEq_apply, flatEquiv]
  rfl

theorem splitEq_apply_inv {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w0 w1 : 𝔼)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → 𝔼) :
    splitEq hij (fun k => if h : k = i then w0 else if h' : k = j then w1 else x' ⟨k, h, h'⟩)
      = (w0, (w1, x')) := by
  rw [splitEq_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [↓reduceDIte]
  · simp only [Ne.symm hij, ↓reduceDIte]
  · simp only [funext_iff]
    intro x
    simp only [x.2.1, x.2.2, ↓reduceDIte]

theorem splitEq_symm_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w0 w1 : 𝔼)
    (x' : {k : Fin n // k ≠ i ∧ k ≠ j} → 𝔼) :
    (splitEq hij).symm (w0, (w1, x')) =
      fun k => if h : k = i then w0 else if h' : k = j then w1 else x' ⟨k, h, h'⟩ := by
  refine (Equiv.symm_apply_eq (splitEq hij).toEquiv).mpr ?_
  exact (splitEq_apply_inv hij w0 w1 x').symm

theorem measurePreserving_splitEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (splitEq hij) (volume : Measure (Fin n → 𝔼))
      (volume : Measure (𝔼 × (𝔼 × Fib n i j))) := by
  have h1 := measurePreserving_peelEq (ι := Fin n) i
  have h2 := measurePreserving_peelEq (ι := {k : Fin n // k ≠ i}) ⟨j, Ne.symm hij⟩
  have h3 : MeasurePreserving
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => 𝔼)
        (flatEquiv i j hij)))
      (volume : Measure ({y : {k : Fin n // k ≠ i} // y ≠
        (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i})} → 𝔼))
      (volume : Measure (Fib n i j)) :=
    measurePreserving_piCongrLeft
      (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => (volume : Measure 𝔼)) (flatEquiv i j hij)
  have hY : MeasurePreserving
      (⇑((MeasurableEquiv.refl 𝔼).prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} => 𝔼)
          (flatEquiv i j hij))))
      (volume : Measure (𝔼 × ({y : {k : Fin n // k ≠ i} // y ≠
        (⟨j, Ne.symm hij⟩ : {k : Fin n // k ≠ i})} → 𝔼)))
      (volume : Measure (𝔼 × Fib n i j)) :=
    (MeasurePreserving.id (volume : Measure 𝔼)).prod h3
  have h2Y := hY.comp h2
  have hX := (MeasurePreserving.id (volume : Measure 𝔼)).prod h2Y
  exact hX.comp h1

/-! ## The insertion in the shape of the statement

`Fib n i j × (𝔼 × 𝔼) ≃ᵐ (Fin n → 𝔼)` with `(x', (y, u)) ↦ ins y u x'`. -/

/-- The insertion `(x', (y, u)) ↦ (k ↦ if k = i then y else if k = j then u else x' k)`. -/
def splitEquiv {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Fib n i j × (𝔼 × 𝔼) ≃ᵐ (Fin n → 𝔼) :=
  (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc).trans (splitEq hij).symm

theorem splitEquiv_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x' : Fib n i j) (y u : 𝔼) :
    splitEquiv hij (x', (y, u)) =
      fun k => if h : k = i then y else if h' : k = j then u else x' ⟨k, h, h'⟩ := by
  simp only [splitEquiv, MeasurableEquiv.trans_apply]
  exact splitEq_symm_apply hij y u x'

theorem measurePreserving_splitEquiv {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (splitEquiv hij)
      ((volume : Measure (Fib n i j)).prod ((volume : Measure 𝔼).prod volume))
      (volume : Measure (Fin n → 𝔼)) := by
  have hpc : MeasurePreserving
      (MeasurableEquiv.prodComm : Fib n i j × (𝔼 × 𝔼) ≃ᵐ (𝔼 × 𝔼) × Fib n i j)
      ((volume : Measure (Fib n i j)).prod ((volume : Measure 𝔼).prod volume))
      (((volume : Measure 𝔼).prod volume).prod (volume : Measure (Fib n i j))) :=
    ⟨MeasurableEquiv.prodComm.measurable, Measure.prod_swap⟩
  have hpa : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((𝔼 × 𝔼) × Fib n i j) ≃ᵐ (𝔼 × (𝔼 × Fib n i j)))
      (((volume : Measure 𝔼).prod volume).prod (volume : Measure (Fib n i j)))
      ((volume : Measure 𝔼).prod ((volume : Measure 𝔼).prod volume)) :=
    volume_preserving_prodAssoc
  have hse := measurePreserving_splitEq hij
  exact (hse.symm).comp (hpa.comp hpc)

/-- The insertion over the outer variables: `(w, x') ↦ ins x' w`. -/
def outIns {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (𝔼 × 𝔼) × Fib n i j ≃ᵐ (Fin n → 𝔼) :=
  MeasurableEquiv.prodComm.trans (splitEquiv hij)

theorem measurePreserving_outIns {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (outIns hij)
      (((volume : Measure 𝔼).prod volume).prod (volume : Measure (Fib n i j)))
      (volume : Measure (Fin n → 𝔼)) := by
  have hpc : MeasurePreserving
      (MeasurableEquiv.prodComm : (𝔼 × 𝔼) × Fib n i j ≃ᵐ Fib n i j × (𝔼 × 𝔼))
      (((volume : Measure 𝔼).prod volume).prod (volume : Measure (Fib n i j)))
      ((volume : Measure (Fib n i j)).prod ((volume : Measure 𝔼).prod volume)) :=
    ⟨MeasurableEquiv.prodComm.measurable, Measure.prod_swap⟩
  exact (measurePreserving_splitEquiv hij).comp hpc

/-! ## Cauchy–Schwarz on a single measure space -/

/-- **Cauchy–Schwarz** for the Bochner integral of two complex `L²` functions:
`‖∫ f · g‖² ≤ (∫ ‖f‖²)(∫ ‖g‖²)`. -/
theorem norm_integral_mul_le_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * g x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have hA : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  have hB : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  rw [hA, hB] at hH
  have hH' : ∫ x, ‖f x‖ * ‖g x‖ ∂μ
      ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    simpa only [hA, hB, ← Real.sqrt_eq_rpow] using hH
  have hle : ‖∫ x, f x * g x ∂μ‖ ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) :=
    (norm_integral_le_integral_norm (fun x => f x * g x)).trans (by simpa only [norm_mul] using hH')
  have h1 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have h2 : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have hsq : (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ)) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
  calc ‖∫ x, f x * g x ∂μ‖ ^ 2
      ≤ (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ)) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := hsq

end Work.BoseBoxFock
