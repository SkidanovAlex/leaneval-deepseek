import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ATOM.zdesc
import Submission.Work.ATOM.zfree_iso_pt_biprod_zred
import Submission.Work.ANALYTIC.EA_natural

/-!
# Setup for the truncation tower `F : P ⊗ ∏^bnd ℤ ⟶ ∏^bnd ℤ`

This file collects the definitions used by `Work.ANALYTIC.exists_tower_F`:

* `truncCoeff m : ℕ∪{∞} → ℤ`, the characteristic function of `{k : k ≤ m}`, zero at `∞`;
* `truncElem S x`, the element of `∏^bnd ℤ` over `(ℕ∪{∞}) ⊗ S` whose `m`-th component is
  `(k,s) ↦ x_m(s)·[k ≤ m]`;
* `cSlice S k : S ⟶ (ℕ∪{∞}) ⊗ S`, the slice `s ↦ (k,s)`;
* `phi S x`, the morphism `ℤ[(ℕ∪{∞}) × S] ⟶ ∏^bnd ℤ` with section `truncElem S x`;
* `psi S x`, its descent along `EA S` to `P ⊗ ℤ[S] ⟶ ∏^bnd ℤ`.

The mathematical content of `exists_tower_F` is that the family `ψ` (which is linear in `x` and
natural in `S`) is induced by a morphism `curry F : ∏^bnd ℤ ⟶ (P ⟹ ∏^bnd ℤ)`, and that this `F`
is a retraction of `e_0 ⊗ -`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-! ## The truncation coefficients -/

/-- `truncCoeff m k = 1` if `k = n` for some `n ≤ m`, and `0` otherwise (in particular at `∞`). -/
def truncCoeff (m : ℕ) : OnePoint ℕ → ℤ := fun k => k.elim 0 (fun n => if n ≤ m then 1 else 0)

theorem truncCoeff_infty (m : ℕ) : truncCoeff m (∞ : OnePoint ℕ) = 0 := rfl

theorem truncCoeff_coe (m n : ℕ) :
    truncCoeff m ((n : ℕ) : OnePoint ℕ) = if n ≤ m then 1 else 0 := rfl

theorem abs_truncCoeff_le_one (m : ℕ) (k : OnePoint ℕ) : |truncCoeff m k| ≤ 1 := by
  cases k with
  | infty => simp only [truncCoeff, OnePoint.elim_infty, abs_zero]; norm_num
  | coe n => rw [truncCoeff, OnePoint.elim_some]; split <;> norm_num

theorem truncCoeff_continuous (m : ℕ) : Continuous (truncCoeff m) := by
  rw [OnePoint.continuous_iff_from_nat]
  rw [show truncCoeff m ∞ = 0 from rfl]
  refine Filter.Tendsto.congr'
    (Filter.eventually_atTop.mpr ⟨m+1, fun j hj => ?_⟩) tendsto_const_nhds
  show (0:ℤ) = truncCoeff m (j : ℕ∪{∞})
  rw [truncCoeff, OnePoint.elim_some, if_neg (by omega : ¬ j ≤ m)]

/-! ## The element `(m,(k,s)) ↦ x_m(s)·[k ≤ m]` -/

/-- **The `F`-section.**  For `x ∈ ∏^bnd ℤ(S)`, the element of `∏^bnd ℤ` over `(ℕ∪{∞}) × S` whose
`m`-th component is `(k,s) ↦ x_m(s)·[k ≤ m]`.  It vanishes on the `∞`-slice and is uniformly
bounded by the bound of `x`. -/
def truncElem (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    ↥(boundedSeq.obj.obj (Opposite.op (Work.ATOM.NS S))) :=
  ⟨fun m => ⟨fun p => x.1 m p.2 * truncCoeff m p.1,
      ((x.1 m).continuous.comp continuous_snd).mul
        ((truncCoeff_continuous m).comp continuous_fst)⟩,
   ⟨Classical.choose x.2, fun m p => by
      have h := Classical.choose_spec x.2 m p.2
      have h1 : |truncCoeff m p.1| ≤ 1 := abs_truncCoeff_le_one m p.1
      calc |x.1 m p.2 * truncCoeff m p.1| = |x.1 m p.2| * |truncCoeff m p.1| := abs_mul _ _
        _ ≤ |x.1 m p.2| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |x.1 m p.2| := mul_one _
        _ ≤ Classical.choose x.2 := h⟩⟩

@[simp] theorem truncElem_val (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ) (p : ↥(Work.ATOM.NS S)) :
    (truncElem S x).1 m p = x.1 m p.2 * truncCoeff m p.1 := rfl

/-! ## The slices `s ↦ (k,s)` -/

/-- The slice `S ⟶ (ℕ∪{∞}) ⊗ S`, `s ↦ (k,s)`. -/
def cSlice (S : LightProfinite.{0}) (k : ℕ) : S ⟶ Work.ATOM.NS S :=
  (λ_ S).inv ≫ (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (((k : ℕ) : ℕ∪{∞})) ▷ S)

/-- The slice map is `s ↦ (k,s)` on points. -/
theorem cSlice_apply (S : LightProfinite.{0}) (k : ℕ) (s : ↥S) :
    (cSlice S k) s = (((k : ℕ) : ℕ∪{∞}), s) := by
  have h : (λ_ S).hom ((λ_ S).inv s) = s := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have h2 : ((λ_ S).inv s).2 = s := by
    simpa only [show ∀ q : ↥(𝟙_ LightProfinite ⊗ S), (λ_ S).hom q = q.2 from fun q => rfl] using h
  show (Work.ATOM.ptAt (S := LightProfinite.NatUnionInfty) (((k : ℕ) : ℕ∪{∞})) ▷ S)
      ((λ_ S).inv s) = _
  have hp : (λ_ S).inv s = (((λ_ S).inv s).1, s) := Prod.ext rfl h2
  rw [hp]
  rfl

/-! ## The morphisms `φ` and `ψ` -/

/-- The morphism `ℤ[(ℕ∪{∞}) × S] ⟶ ∏^bnd ℤ` whose section over `(ℕ∪{∞}) × S` is `truncElem S x`. -/
noncomputable def phi (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zfree (Work.ATOM.NS S) ⟶ boundedSeq :=
  (Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq).symm (truncElem S x)

theorem homFreeEquiv_phi (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.homFreeEquiv (Work.ATOM.NS S) boundedSeq (phi S x) = truncElem S x :=
  Equiv.apply_symm_apply _ _

end Work.ANALYTIC
