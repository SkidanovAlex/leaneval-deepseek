import Mathlib
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ATOM.Toolkit.PS_desc
import Submission.Work.ATOM.projective_P

/-!
# Setup for the unprimed null-sequence tower of REFS/03 §2

This file collects the concrete definitions used by `Work.ANALYTIC.exists_unprimedTower` and by the
lemmas delegated to prove it:

* `coordTimesDelta S x k` is the element `x_k · δ_k` of `∏^bnd ℤ` over `S`;
* the truncation endomorphism `truncZ k` of `∏^bnd ℤ` and its concrete description.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-- `x_k · δ_k ∈ ∏^bnd ℤ` over `S`: the `k`-th coordinate function of `x` times the `k`-th basis
vector `δ_k`.  Its `m`-th component is the function `s ↦ x_k(s)·[m = k]`. -/
def coordTimesDelta (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (k : ℕ) :
    ↥(boundedSeq.obj.obj (Opposite.op S)) :=
  ⟨fun m => ⟨fun s => x.1 k s * (if m = k then (1 : ℤ) else 0), by
      refine Continuous.mul (x.1 k).continuous continuous_const⟩,
    ⟨Classical.choose x.2, fun m s => by
      have h := Classical.choose_spec x.2 k s
      have hle : (if m = k then (1 : ℤ) else 0) ≤ 1 := by split <;> norm_num
      have hnn : (0 : ℤ) ≤ (if m = k then (1 : ℤ) else 0) := by split <;> norm_num
      calc |x.1 k s * (if m = k then (1 : ℤ) else 0)|
          = |x.1 k s| * |(if m = k then (1 : ℤ) else 0)| := abs_mul _ _
        _ ≤ |x.1 k s| * 1 := mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hnn]; exact hle)
              (abs_nonneg _)
        _ = |x.1 k s| := mul_one _
        _ ≤ Classical.choose x.2 := h⟩⟩

@[simp]
theorem coordTimesDelta_val (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (k m : ℕ) (s : ↥S.toTop) :
    (coordTimesDelta S x k).1 m s = x.1 k s * (if m = k then (1 : ℤ) else 0) := rfl

/-- The element of `∏^bnd ℤ` over `S` whose `m`-th component is `s ↦ x_m(s)·[f s = m]`, for a
continuous map `f : S ⟶ ℕ∪{∞}`.  For `f = const k` this is `coordTimesDelta S x k`. -/
def coordTimesDeltaAt (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (f : S ⟶ (ℕ∪{∞})) :
    ↥(boundedSeq.obj.obj (Opposite.op S)) :=
  ⟨fun m => ⟨fun s => x.1 m s * deltaFun m (f s),
      Continuous.mul (x.1 m).continuous
        ((deltaFun m).continuous.comp (ConcreteCategory.hom f).continuous)⟩,
    ⟨Classical.choose x.2, fun m s => by
      have h := Classical.choose_spec x.2 m s
      have h1 : |deltaFun m (f s)| ≤ 1 := by
        rw [deltaFun_eq]; split <;> norm_num
      calc |x.1 m s * deltaFun m (f s)| = |x.1 m s| * |deltaFun m (f s)| := abs_mul _ _
        _ ≤ |x.1 m s| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |x.1 m s| := mul_one _
        _ ≤ Classical.choose x.2 := h⟩⟩

/-- The `k`-th truncation endomorphism of `∏^bnd ℤ`: `x ↦ π_{≥k} x`, `(π_{≥k}x)_m = x_m·[m ≥ k]`,
i.e. `x_m·[k ≤ m]`. -/
def truncZ (k : ℕ) : boundedSeq ⟶ boundedSeq :=
  ObjectProperty.homMk
    { app := fun S => ModuleCat.ofHom
        { toFun := fun x =>
            ⟨fun m => ⟨fun s => x.1 m s * (if k ≤ m then (1 : ℤ) else 0), by
                refine Continuous.mul (x.1 m).continuous continuous_const⟩,
             ⟨Classical.choose x.2, fun m s => by
                have h := Classical.choose_spec x.2 m s
                have hle : (if k ≤ m then (1 : ℤ) else 0) ≤ 1 := by split <;> norm_num
                have hnn : (0 : ℤ) ≤ (if k ≤ m then (1 : ℤ) else 0) := by split <;> norm_num
                calc |x.1 m s * (if k ≤ m then (1 : ℤ) else 0)|
                    = |x.1 m s| * |(if k ≤ m then (1 : ℤ) else 0)| := abs_mul _ _
                  _ ≤ |x.1 m s| * 1 := mul_le_mul_of_nonneg_left
                        (by rw [abs_of_nonneg hnn]; exact hle) (abs_nonneg _)
                  _ = |x.1 m s| := mul_one _
                  _ ≤ Classical.choose x.2 := h⟩⟩
          map_add' := by
            intro a b
            apply Subtype.ext
            funext m
            apply ContinuousMap.ext
            intro s
            simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_mk, ContinuousMap.coe_mk,
              ContinuousMap.add_apply]
            ring
          map_smul' := by
            intro c a
            apply Subtype.ext
            funext m
            apply ContinuousMap.ext
            intro s
            simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_mk, ContinuousMap.coe_mk,
              ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
            ring }
      naturality := by
        intro S T f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        funext m
        apply ContinuousMap.ext
        intro s
        rfl }

theorem truncZ_val (k : ℕ) (S : (LightProfinite.{0})ᵒᵖ)
    (x : ↥(boundedSeq.obj.obj S)) (m : ℕ) (s : ↥(S.unop.toTop)) :
    ((truncZ k).hom.app S x).1 m s = x.1 m s * (if k ≤ m then (1 : ℤ) else 0) := rfl


/-! The point `e_0`, the section `s = e_0 ⊗ -`, and the "counterexample" element. -/

/-- The point `e_k : 𝟙_ ⟶ P` (the class of the point `k` of `ℕ∪{∞}` in `P`).  This is
`Work.ANALYTIC.ePoint k` of `cBounded_solidEquiv.lean`, restated here so that this file does not
depend on a module that is currently under construction. -/
noncomputable def ePointZ (k : ℕ) : 𝟙_ LightCondAb ⟶ LightCondensed.P :=
  Work.ATOM.unitIso.hom ≫
    (Work.ATOM.zmap (Work.ATOM.ptAt (OnePoint.some k)) ≫ LightCondensed.P_proj)

/-- The section `s = e_0 ⊗ - : ∏^bnd ℤ ⟶ P ⊗ ∏^bnd ℤ` (restated version of `sBounded`). -/
noncomputable def sBoundedZ :
    boundedSeq ⟶ LightCondensed.P ⊗ boundedSeq :=
  (λ_ boundedSeq).inv ≫ (ePointZ 0 ▷ boundedSeq)

/-- The element of `∏^bnd ℤ` over `ℕ∪{∞}` whose `m`-th component is the constant function
`k ↦ [m even]`; this is the "counterexample" data for the disputed general statement
(`f = 𝟙`, `x_m = [m even]`). -/
def evenOddElem :
    ↥(boundedSeq.obj.obj (Opposite.op LightProfinite.NatUnionInfty)) :=
  ⟨fun m => ⟨fun _ => if m % 2 = 0 then (1 : ℤ) else 0, continuous_const⟩,
    ⟨1, fun m s => by
      show |(if m % 2 = 0 then (1 : ℤ) else 0)| ≤ 1
      split_ifs <;> norm_num⟩⟩

@[simp]
theorem evenOddElem_val (m : ℕ) (s : ↥(LightProfinite.NatUnionInfty).toTop) :
    (evenOddElem).1 m s = if m % 2 = 0 then (1 : ℤ) else 0 := rfl


/-! The two `Prop`s characterizing the wanted `F` of the unprimed tower, stated here (rather than
in the delegated file) so that the delegated statement stays free of `≫`/`𝟙`/`▷`/`λ_` notation. -/

/-- `F` is a retraction of the section `s = e_0 ⊗ -` (identity `h₂` of the scheme of REFS/03 §1). -/
def IsRetraction (F : LightCondensed.P ⊗ boundedSeq ⟶ boundedSeq) : Prop :=
  sBoundedZ ≫ F = 𝟙 boundedSeq

/-- `F`'s null family is the family of truncations `π_{≥k}`: for every light profinite `S`,
`x ∈ ∏^bnd ℤ(S)` and `k : ℕ`, the `k`-th component of the `S`-point of `F` at `x` is `π_{≥k} x`,
i.e. the section with `m`-th component `s ↦ x_m(s)·[k ≤ m]`. -/
def IsTruncTower (F : LightCondensed.P ⊗ boundedSeq ⟶ boundedSeq) : Prop :=
  ∀ (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (k : ℕ),
    (ePointZ k ▷ Work.ATOM.zfree S) ≫
        (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
          ((MonoidalClosed.curry F).hom.app (Opposite.op S) x)) =
      (λ_ (Work.ATOM.zfree S)).hom ≫
        (Work.ATOM.homFreeEquiv S boundedSeq).symm
          ((truncZ k).hom.app (Opposite.op S) x)


/-! The shift-equivariance of `EA` (needed on the `T = (1-S) ⊗ id` side of the tower). -/

/-- `EA S` intertwines `(1 - S) ⊗ id` on `P ⊗ ℤ[S]` with `1 - ℤ[shift ▷ S]` on `ℤ[(ℕ∪∞) × S]`.
Stated as a `Prop` so that the delegated statement stays free of `≫`/`▷`/`𝟙` notation. -/
def EA_shiftProp (S : LightProfinite.{0}) : Prop :=
  Work.ATOM.EA S ≫ (LightCondensed.oneMinusShift ▷ Work.ATOM.zfree S) =
    (𝟙 _ - Work.ATOM.zmap (LightProfinite.shift ▷ S)) ≫ Work.ATOM.EA S


/-- The element of `∏^bnd ℤ` over `(ℕ∪∞) × S` whose `m`-th component is
`(k,s) ↦ x_m(s)·[k ≤ m]`; this is the "truncation data" of the null family `π_{≥k}`.  The
coefficient is written as `1 - ∏_{i ≤ m}(1 - deltaFun i k)`, which equals `[k ≤ m]` and has the
advantage that the uniform bound is immediate.  It is legitimate because `{k : k ≤ m}` is finite,
hence clopen in `ℕ∪∞`, and it vanishes at `k = ∞`. -/
def truncDataElem (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    ↥(boundedSeq.obj.obj (Opposite.op ((ℕ∪{∞}) ⊗ S))) :=
  ⟨fun m => ⟨fun p => x.1 m p.2 *
        (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1)), by
      refine Continuous.mul ((x.1 m).continuous.comp continuous_snd) ?_
      refine Continuous.sub continuous_const (continuous_finset_prod _ fun i _ => ?_)
      exact Continuous.sub continuous_const ((deltaFun i).continuous.comp continuous_fst)⟩,
    ⟨Classical.choose x.2, fun m p => by
      have h := Classical.choose_spec x.2 m p.2
      have hδ : ∀ i : ℕ, |deltaFun i (p.1 : OnePoint ℕ)| ≤ 1 := fun i => by
        rw [deltaFun_eq]; split <;> norm_num
      have hle : ∀ i : ℕ, deltaFun i (p.1 : OnePoint ℕ) ≤ 1 := fun i => (abs_le.mp (hδ i)).2
      have hge0 : ∀ i : ℕ, (0 : ℤ) ≤ deltaFun i (p.1 : OnePoint ℕ) := fun i => by
        rw [deltaFun_eq]; split <;> norm_num
      have h0 : ∀ i ∈ Finset.range (m + 1), (0 : ℤ) ≤ 1 - deltaFun i p.1 :=
        fun i _ => sub_nonneg.mpr (hle i)
      have hP0 : (0 : ℤ) ≤ ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1) :=
        Finset.prod_nonneg h0
      have hP1 : ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1) ≤ 1 := by
        have aux : ∀ s : Finset ℕ, (∀ i ∈ s, (0 : ℤ) ≤ 1 - deltaFun i p.1) →
            (∏ i ∈ s, (1 - deltaFun i p.1)) ≤ 1 := by
          intro s
          induction s using Finset.induction with
          | empty => intro _; simp
          | insert a s ha ih =>
            intro hs
            rw [Finset.prod_insert ha]
            have h1 : (∏ i ∈ s, (1 - deltaFun i p.1)) ≤ 1 :=
              ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
            have h2 : (0 : ℤ) ≤ ∏ i ∈ s, (1 - deltaFun i p.1) :=
              Finset.prod_nonneg fun i hi => hs i (Finset.mem_insert_of_mem hi)
            have h3 : (0 : ℤ) ≤ 1 - deltaFun a p.1 := hs a (Finset.mem_insert_self a s)
            have h4 : (1 : ℤ) - deltaFun a p.1 ≤ 1 := by
              have := hge0 a; omega
            nlinarith
        exact aux _ h0
      have hc : |1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc |x.1 m p.2 * (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1))|
          = |x.1 m p.2| * |1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1)| := abs_mul _ _
        _ ≤ |x.1 m p.2| * 1 := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = |x.1 m p.2| := mul_one _
        _ ≤ Classical.choose x.2 := h⟩⟩

@[simp]
theorem truncDataElem_val (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ)
    (p : ↥((ℕ∪{∞}) ⊗ S).toTop) :
    (truncDataElem S x).1 m p = x.1 m p.2 *
      (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1)) := rfl

/-- The `EA`-form of the truncation data: `F`'s null family is the family of truncations, stated
as an identity after applying `EA S` (the quotient projection `ℤ[(ℕ∪∞) × S] ⟶ P ⊗ ℤ[S]`). -/
def IsTruncEAdata (F : LightCondensed.P ⊗ boundedSeq ⟶ boundedSeq) : Prop :=
  ∀ (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    Work.ATOM.EA S ≫
        (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
          ((MonoidalClosed.curry F).hom.app (Opposite.op S) x)) =
      (Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) boundedSeq).symm (truncDataElem S x)


/-! The classified element of `T ≫ F` (the `EA`-form of the shift side). -/

/-- The first projection `(ℕ∪∞) ⊗ S ⟶ ℕ∪∞`. -/
def fstNS (S : LightProfinite.{0}) : (ℕ∪{∞}) ⊗ S ⟶ (ℕ∪{∞}) :=
  ConcreteCategory.ofHom ⟨fun p => p.1, continuous_fst⟩

/-- The second projection `(ℕ∪∞) ⊗ S ⟶ S`. -/
def sndNS (S : LightProfinite.{0}) : (ℕ∪{∞}) ⊗ S ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.2, continuous_snd⟩

/-- The pullback of a bounded family `x` over `S` to `(ℕ∪∞) ⊗ S` (along the second projection). -/
def pullbackX (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    ↥(boundedSeq.obj.obj (Opposite.op ((ℕ∪{∞}) ⊗ S))) :=
  boundedSeq.obj.map (sndNS S).op x

/-- **The classified element of the `S`-point of `T ≫ F`, in `EA`-form.**  For `F` whose null
family is the truncations (`Work.ANALYTIC.IsTruncEAdata F`), applying `EA S` to the `S`-point
`θF_S(x) : P ⊗ ℤ[S] ⟶ ∏^bnd ℤ` precomposed with `oneMinusShift ▷ ℤ[S]` gives the morphism
classified by `coordTimesDeltaAt ((ℕ∪∞) ⊗ S) (pullbackX S x) (fstNS S)`: its `m`-th component is
`(k,s) ↦ x_m(s)·[k = m]`.  (Uses the workspace* `EA_shift` and `[k ≤ m] − [k+1 ≤ m] = [k = m]`.) -/
def EAdataShift (F : LightCondensed.P ⊗ boundedSeq ⟶ boundedSeq) : Prop :=
  ∀ (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))),
    Work.ATOM.EA S ≫
        (CategoryTheory.CategoryStruct.comp
          (MonoidalCategory.whiskerRight LightCondensed.oneMinusShift (Work.ATOM.zfree S))
          (LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
            ((MonoidalClosed.curry F).hom.app (Opposite.op S) x))) =
      (Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) boundedSeq).symm
        (coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S))

end Work.ANALYTIC

end
