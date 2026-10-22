import Mathlib
import Submission.Work.ANALYTIC.qElemSetup
import Submission.Work.ATOM.Toolkit.PS_desc
import Submission.Work.ANALYTIC.mono_cBounded
import Submission.Work.ANALYTIC.EA_natural
import Submission.Work.ANALYTIC.towerFEAsetup
import Submission.Work.ANALYTIC.coordTimesDelta_mem_range
import Submission.Work.ANALYTIC.eadataShift_of_truncEAdata

/-!
# The null family `G` of REFS/03 §2: descent of the data `(k,x) ↦ x_k·e_k`

This file builds, from the element `Work.ANALYTIC.qElem S x ∈ P((ℕ∪∞) ⊗ S)` (the data
`(k,s) ↦ x_k(s)·e_k` of the null family of `G`), the family of morphisms

`gPsi S x : P ⊗ ℤ[S] ⟶ P`

whose null family is `(k,x) ↦ x_k·e_k`.  It is the descent of the morphism
`chiG S x : ℤ[(ℕ∪∞) ⊗ S] ⟶ P` classified by `qElem S x` along the epimorphism
`EA S : ℤ[(ℕ∪∞) ⊗ S] ⟶ P ⊗ ℤ[S]` (`Work.ATOM.Toolkit.PS_desc`), which is possible because
`chiG S x` kills the `∞`-slice.

Everything after the descent (additivity, `ℤ`-linearity and naturality of `gPsi` in the test
object, and the key identity `gPsi S x ≫ cBounded = ((1-S) ⊗ id) ≫ θF_S(x)`) is *derived* from the
single element-level input `Work.ANALYTIC.QElemCBounded` together with the fact that `cBounded` is
a monomorphism (`Work.ANALYTIC.mono_cBounded`): an equation between morphisms out of `ℤ[(ℕ∪∞)⊗S]`
or out of `P` may be checked after postcomposition with `cBounded`.

* `chiG S x` is the sum `Σ_{j ∈ [-N,N]} j·[g_j]` over the free generators `[g_j]`, `N = qBound S x`,
  with `g_j((k,s)) = k` if `x_k(s) = j` and `∞` otherwise;
* `phiG S x` is the morphism `ℤ[(ℕ∪∞) ⊗ S] ⟶ ∏^bnd ℤ` classified by
  `coordTimesDeltaAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S)`, i.e. by the family
  `(m,(k,s)) ↦ x_m(s)·[k = m]` — the `EA`-data of `T ≫ F`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

attribute [local instance] Classical.propDecidable

/-! ## Elementary evaluations of the projection maps -/

section Evaluations

variable {S T : LightProfinite.{0}}

@[simp] theorem fstNS_val (p : ↥((ℕ∪{∞}) ⊗ S)) : fstNS S p = p.1 := rfl

@[simp] theorem sndNS_val (p : ↥((ℕ∪{∞}) ⊗ S)) : sndNS S p = p.2 := rfl

@[simp] theorem pair_fst (k : OnePoint ℕ) (s : ↥S) :
    (⟨k, s⟩ : ↥((ℕ∪{∞}) ⊗ S)).1 = k := rfl

@[simp] theorem pair_snd (k : OnePoint ℕ) (s : ↥S) :
    (⟨k, s⟩ : ↥((ℕ∪{∞}) ⊗ S)).2 = s := rfl

@[simp] theorem whiskerLeft_val (g : T ⟶ S) (p : ↥((ℕ∪{∞}) ⊗ T)) :
    (MonoidalCategory.whiskerLeft (ℕ∪{∞}) g) p = (⟨p.1, g p.2⟩ : ↥((ℕ∪{∞}) ⊗ S)) := rfl

@[simp] theorem whiskerRight_iota_val (p : ↥(Work.ATOM.pt ⊗ S)) :
    (MonoidalCategory.whiskerRight LightCondensed.ι S) p = (⟨∞, p.2⟩ : ↥((ℕ∪{∞}) ⊗ S)) := rfl

@[simp] theorem pullbackX_val (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (m : ℕ)
    (p : ↥((ℕ∪{∞}) ⊗ S)) : (pullbackX S x).1 m p = x.1 m p.2 := rfl

end Evaluations

/-! ## Additivity of `pullbackX` -/

/-- `pullbackX S` is additive (it is the action of a morphism of `ℤ`-modules). -/
theorem pullbackX_add (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    pullbackX S (x + y) = pullbackX S x + pullbackX S y := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [Work.ANALYTIC.coe_add_apply ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (pullbackX S y) m p]
  show ((x + y).1 m) p.2 = ((x.1 m) p.2) + ((y.1 m) p.2)
  rw [Work.ANALYTIC.coe_add_apply S x y m p.2]

/-- `pullbackX S` commutes with integer multiples. -/
theorem pullbackX_smul (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    pullbackX S (c • x) = c • pullbackX S x := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [Work.ANALYTIC.coe_smul_apply ((ℕ∪{∞}) ⊗ S) c (pullbackX S x) m p]
  show ((c • x).1 m) p.2 = c * ((x.1 m) p.2)
  rw [Work.ANALYTIC.coe_smul_apply S c x m p.2]

/-- `pullbackX S` vanishes on the zero family. -/
theorem pullbackX_zero (S : LightProfinite.{0}) :
    pullbackX S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  rw [Work.ANALYTIC.coe_zero_apply ((ℕ∪{∞}) ⊗ S) m p]
  show ((0 : ↥(boundedSeq.obj.obj (Opposite.op S))).1 m) p.2 = 0
  rw [Work.ANALYTIC.coe_zero_apply S m p.2]

/-- `cBounded` is a monomorphism, so it is injective on sections and cancellable on the right. -/
theorem cBounded_mono : CategoryTheory.Mono Work.ANALYTIC.cBounded := mono_cBounded

/-- **Injectivity of `cBounded` on the sections over a light profinite set.** -/
theorem cBounded_apply_injective {T : LightProfinite.{0}}
    {p q : ↥(LightCondensed.P.obj.obj (op T))}
    (h : cBounded.hom.app (op T) p = cBounded.hom.app (op T) q) : p = q := by
  haveI : Mono cBounded := cBounded_mono
  have hu : (Work.ATOM.homFreeEquiv T LightCondensed.P).symm p ≫ cBounded
      = (Work.ATOM.homFreeEquiv T LightCondensed.P).symm q ≫ cBounded := by
    apply (Work.ATOM.homFreeEquiv T boundedSeq).injective
    rw [Work.ATOM.homFreeEquiv_naturality_target T cBounded
        ((Work.ATOM.homFreeEquiv T LightCondensed.P).symm p),
      Work.ATOM.homFreeEquiv_naturality_target T cBounded
        ((Work.ATOM.homFreeEquiv T LightCondensed.P).symm q)]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, h]
  have h2 := (cancel_mono cBounded).mp hu
  have h3 := congrArg (Work.ATOM.homFreeEquiv T LightCondensed.P) h2
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h3

/-- **The data of the null family `(k,x) ↦ x_k·e_k` as a morphism `ℤ[(ℕ∪∞)⊗S] ⟶ P`**: the sum
`Σ_{j ∈ [-N,N]} j·[g_j]` with `N = qBound S x` and `g_j = gAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S) j`.
Its `homFreeEquiv`-class is `Work.ANALYTIC.qElem S x`. -/
noncomputable def chiG (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zfree ((ℕ∪{∞}) ⊗ S) ⟶ LightCondensed.P :=
  ∑ j ∈ Finset.Icc (-(qBound S x)) (qBound S x),
    j • (Work.ATOM.zmap (gAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S) j) ≫
      LightCondensed.P_proj)

/-- `chiG` is classified by `qElem`. -/
theorem homFreeEquiv_chiG (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ANALYTIC.freeHomEquiv ((ℕ∪{∞}) ⊗ S) LightCondensed.P (chiG S x) = qElem S x := rfl

/-- The `Work.ATOM` form of `homFreeEquiv_chiG`. -/
theorem homFreeEquiv_chiG_atom (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) LightCondensed.P (chiG S x) = qElem S x :=
  homFreeEquiv_chiG S x

/-- **The `EA`-data of `T ≫ F`**: the morphism `ℤ[(ℕ∪∞)⊗S] ⟶ ∏^bnd ℤ` classified by
`coordTimesDeltaAt ((ℕ∪∞)⊗S) (pullbackX S x) (fstNS S)`, i.e. by the family
`(m,(k,s)) ↦ x_m(s)·[k = m]`. -/
noncomputable def phiG (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zfree ((ℕ∪{∞}) ⊗ S) ⟶ boundedSeq :=
  (Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) boundedSeq).symm
    (coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S))

/-- `phiG` is classified by `coordTimesDeltaAt`. -/
theorem homFreeEquiv_phiG (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) boundedSeq (phiG S x)
      = coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S) :=
  Equiv.apply_symm_apply _ _

/-! ## The element-level computations

These are the only genuinely computational inputs; everything else is abstract. -/

/-- **Additivity of `coordTimesDeltaAt` in the family.** -/
theorem coordTimesDeltaAt_add (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) (f : S ⟶ (ℕ∪{∞})) :
    coordTimesDeltaAt S (x + y) f = coordTimesDeltaAt S x f + coordTimesDeltaAt S y f := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro s
  rw [Work.ANALYTIC.coe_add_apply S (coordTimesDeltaAt S x f) (coordTimesDeltaAt S y f) m s,
    Work.ANALYTIC.coordTimesDeltaAt_apply, Work.ANALYTIC.coordTimesDeltaAt_apply,
    Work.ANALYTIC.coordTimesDeltaAt_apply, Work.ANALYTIC.coe_add_apply S x y m s]
  ring

/-- **`ℤ`-linearity of `coordTimesDeltaAt` in the family.** -/
theorem coordTimesDeltaAt_smul (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) (f : S ⟶ (ℕ∪{∞})) :
    coordTimesDeltaAt S (c • x) f = c • coordTimesDeltaAt S x f := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro s
  rw [Work.ANALYTIC.coe_smul_apply S c (coordTimesDeltaAt S x f) m s,
    Work.ANALYTIC.coordTimesDeltaAt_apply, Work.ANALYTIC.coordTimesDeltaAt_apply,
    Work.ANALYTIC.coe_smul_apply S c x m s]
  ring

/-- **Vanishing of `coordTimesDeltaAt` on the zero family.** -/
theorem coordTimesDeltaAt_zero (S : LightProfinite.{0}) (f : S ⟶ (ℕ∪{∞})) :
    coordTimesDeltaAt S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) f = 0 := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro s
  rw [Work.ANALYTIC.coordTimesDeltaAt_apply, Work.ANALYTIC.coe_zero_apply S m s]
  ring

/-- **Naturality of `coordTimesDeltaAt` in the test object.** -/
theorem coordTimesDeltaAt_nat (T S : LightProfinite.{0}) (g : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    boundedSeq.obj.map (MonoidalCategory.whiskerLeft (ℕ∪{∞}) g).op
        (coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S)) =
      coordTimesDeltaAt ((ℕ∪{∞}) ⊗ T) (pullbackX T (boundedSeq.obj.map g.op x)) (fstNS T) := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro t
  show (x.1 m) (g t.2) * deltaFun m t.1 = (x.1 m) (g t.2) * deltaFun m t.1
  rfl

/-- **The `∞`-slice of `coordTimesDeltaAt` vanishes**: its `m`-th component at `(∞,s)` is
`x_m(s)·[∞ = m] = 0`. -/
theorem coordTimesDeltaAt_slice (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    boundedSeq.obj.map (MonoidalCategory.whiskerRight LightCondensed.ι S).op
      (coordTimesDeltaAt ((ℕ∪{∞}) ⊗ S) (pullbackX S x) (fstNS S)) = 0 := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro t
  rw [Work.ANALYTIC.coe_zero_apply (Work.ATOM.pt ⊗ S) m t]
  show (x.1 m) t.2 * deltaFun m (∞ : OnePoint ℕ) = (0 : ℤ)
  rw [deltaFun_infty, mul_zero]

/-! ## The morphism-level consequences -/

/-- **`chiG` maps to `phiG` under `cBounded`** — the element-level input `QElemCBounded`. -/
theorem chiG_comp_cBounded (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) : chiG S x ≫ cBounded = phiG S x := by
  apply (Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality_target, homFreeEquiv_chiG_atom, homFreeEquiv_phiG]
  exact hQ S x

/-- **`phiG` is additive in the family.** -/
theorem phiG_add (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    phiG S (x + y) = phiG S x + phiG S y := by
  rw [phiG, phiG, phiG, pullbackX_add, coordTimesDeltaAt_add, homFreeEquiv_symm_add_aux]

/-- **`phiG` is `ℤ`-linear in the family.** -/
theorem phiG_smul (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    phiG S (c • x) = c • phiG S x := by
  rw [phiG, phiG, pullbackX_smul, coordTimesDeltaAt_smul, homFreeEquiv_symm_zsmul_aux]

/-- **`phiG` vanishes on the zero family.** -/
theorem phiG_zero (S : LightProfinite.{0}) :
    phiG S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  apply (Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ S) boundedSeq).injective
  rw [homFreeEquiv_phiG, pullbackX_zero, coordTimesDeltaAt_zero]
  exact (Work.ANALYTIC.homFreeEquiv_zero' _ _).symm

/-- **Naturality of `phiG` in the test object.** -/
theorem phiG_nat (T S : LightProfinite.{0}) (g : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) g) ≫ phiG S x
      = phiG T (boundedSeq.obj.map g.op x) := by
  apply (Work.ATOM.homFreeEquiv ((ℕ∪{∞}) ⊗ T) boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality, homFreeEquiv_phiG, coordTimesDeltaAt_nat,
    homFreeEquiv_phiG]

/-- **`chiG` is additive in the family** (`cBounded` is mono, so it suffices to compare the
`cBounded`-images `phiG`). -/
theorem chiG_add (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    chiG S (x + y) = chiG S x + chiG S y := by
  haveI : Mono cBounded := cBounded_mono
  apply (cancel_mono cBounded).mp
  rw [Preadditive.add_comp, chiG_comp_cBounded hQ, chiG_comp_cBounded hQ, chiG_comp_cBounded hQ,
    phiG_add]

/-- **`chiG` is `ℤ`-linear in the family.** -/
theorem chiG_smul (hQ : QElemCBounded) (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    chiG S (c • x) = c • chiG S x := by
  haveI : Mono cBounded := cBounded_mono
  apply (cancel_mono cBounded).mp
  rw [Linear.smul_comp, chiG_comp_cBounded hQ, chiG_comp_cBounded hQ, phiG_smul]

/-- **`chiG` vanishes on the zero family.** -/
theorem chiG_zero (hQ : QElemCBounded) (S : LightProfinite.{0}) :
    chiG S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  haveI : Mono cBounded := cBounded_mono
  apply (cancel_mono cBounded).mp
  rw [chiG_comp_cBounded hQ, phiG_zero, zero_comp]

/-- **Naturality of `chiG` in the test object.** -/
theorem chiG_nat (hQ : QElemCBounded) (T S : LightProfinite.{0}) (g : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) g) ≫ chiG S x
      = chiG T (boundedSeq.obj.map g.op x) := by
  haveI : Mono cBounded := cBounded_mono
  apply (cancel_mono cBounded).mp
  rw [Category.assoc, chiG_comp_cBounded hQ, phiG_nat, chiG_comp_cBounded hQ]

/-- **`phiG` kills the `∞`-slice.** -/
theorem zmap_slice_phiG (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫ phiG S x = 0 := by
  apply (Work.ATOM.homFreeEquiv (Work.ATOM.pt ⊗ S) boundedSeq).injective
  rw [Work.ATOM.homFreeEquiv_naturality, homFreeEquiv_phiG, coordTimesDeltaAt_slice]
  exact (Work.ANALYTIC.homFreeEquiv_zero' _ _).symm

/-- **`chiG` kills the `∞`-slice** — the hypothesis of `Work.ATOM.Toolkit.PS_desc`. -/
theorem chiG_infty (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫ chiG S x = 0 := by
  haveI : Mono cBounded := cBounded_mono
  apply (cancel_mono cBounded).mp
  rw [Category.assoc, chiG_comp_cBounded hQ, zmap_slice_phiG, zero_comp]

/-! ## The descent `gPsi S x : P ⊗ ℤ[S] ⟶ P` -/

/-- **The `S`-point of `G`**: the descent of `chiG S x` along the epimorphism `EA S`.  Its null
family is `(k,x) ↦ x_k·e_k`. -/
noncomputable def gPsi (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ LightCondensed.P :=
  (Work.ATOM.Toolkit.PS_desc S (chiG S x) (chiG_infty hQ S x)).choose

/-- The characterizing property of `gPsi`. -/
theorem gPsi_spec (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    Work.ATOM.EA S ≫ gPsi hQ S x = chiG S x :=
  (Classical.choose_spec (Work.ATOM.Toolkit.PS_desc S (chiG S x) (chiG_infty hQ S x))).1

/-- Uniqueness of the descent: a morphism whose composite with `EA S` is `chiG S x` equals
`gPsi hQ S x`. -/
theorem eq_gPsi (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x : ↥(boundedSeq.obj.obj (Opposite.op S)))
    {ψ : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S) ⟶ LightCondensed.P}
    (h : Work.ATOM.EA S ≫ ψ = chiG S x) : ψ = gPsi hQ S x :=
  (Classical.choose_spec (Work.ATOM.Toolkit.PS_desc S (chiG S x) (chiG_infty hQ S x))).2 ψ h

/-- **`gPsi` is additive in the family.** -/
theorem gPsi_add (hQ : QElemCBounded) (S : LightProfinite.{0})
    (x y : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    gPsi hQ S (x + y) = gPsi hQ S x + gPsi hQ S y := by
  have h : Work.ATOM.EA S ≫ (gPsi hQ S x + gPsi hQ S y) = chiG S (x + y) := by
    rw [Preadditive.comp_add, gPsi_spec, gPsi_spec, chiG_add hQ]
  exact (eq_gPsi hQ S (x + y) h).symm

/-- **`gPsi` is `ℤ`-linear in the family.** -/
theorem gPsi_smul (hQ : QElemCBounded) (S : LightProfinite.{0}) (c : ℤ)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    gPsi hQ S (c • x) = c • gPsi hQ S x := by
  have h : Work.ATOM.EA S ≫ (c • gPsi hQ S x) = chiG S (c • x) := by
    rw [Preadditive.comp_zsmul, gPsi_spec, chiG_smul hQ]
  exact (eq_gPsi hQ S (c • x) h).symm

/-- **`gPsi` vanishes on the zero family.** -/
theorem gPsi_zero (hQ : QElemCBounded) (S : LightProfinite.{0}) :
    gPsi hQ S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) = 0 := by
  have h : Work.ATOM.EA S ≫ (0 : Work.ATOM.tmul LightCondensed.P (Work.ATOM.zfree S)
      ⟶ LightCondensed.P) = chiG S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) := by
    rw [comp_zero, chiG_zero hQ]
  exact (eq_gPsi hQ S (0 : ↥(boundedSeq.obj.obj (Opposite.op S))) h).symm

/-- **Naturality of `gPsi` in the test object.** -/
theorem gPsi_nat (hQ : QElemCBounded) (T S : LightProfinite.{0}) (g : T ⟶ S)
    (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    (LightCondensed.P ◁ Work.ATOM.zmap g) ≫ gPsi hQ S x
      = gPsi hQ T (boundedSeq.obj.map g.op x) := by
  have h : Work.ATOM.EA T ≫ ((LightCondensed.P ◁ Work.ATOM.zmap g) ≫ gPsi hQ S x)
      = chiG T (boundedSeq.obj.map g.op x) := by
    rw [← Category.assoc, EA_natural g, Category.assoc, gPsi_spec, chiG_nat hQ]
  exact eq_gPsi hQ T (boundedSeq.obj.map g.op x) h

/-- **The key identity of the unprimed tower at the level of `S`-points**: the composite of the
`S`-point of `G` with `cBounded` is the `S`-point of `T ≫ F`, i.e.
`((1-S) ⊗ id_{ℤ[S]}) ≫ θF_S(x)`.

Both sides become `phiG S x` after composition with `EA S` (`chiG_comp_cBounded` for the left-hand
side, `Work.ANALYTIC.EAdataShift` for the right-hand side), and morphisms out of `P ⊗ ℤ[S]` whose
composite with `EA S` agree are equal (`Work.ATOM.Toolkit.PS_desc`'s uniqueness applied to the
common morphism `phiG S x` into `∏^bnd ℤ`). -/
theorem gPsi_point (hQ : QElemCBounded)
    (F : LightCondensed.P ⊗ boundedSeq ⟶ boundedSeq) (hF : IsTruncEAdata F)
    (S : LightProfinite.{0}) (x : ↥(boundedSeq.obj.obj (Opposite.op S))) :
    gPsi hQ S x ≫ cBounded =
      MonoidalCategory.whiskerRight LightCondensed.oneMinusShift (Work.ATOM.zfree S) ≫
        LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
          ((MonoidalClosed.curry F).hom.app (Opposite.op S) x) := by
  have ha : Work.ATOM.EA S ≫ (gPsi hQ S x ≫ cBounded) = phiG S x := by
    rw [← Category.assoc, gPsi_spec, chiG_comp_cBounded hQ]
  have hb : Work.ATOM.EA S ≫
      (MonoidalCategory.whiskerRight LightCondensed.oneMinusShift (Work.ATOM.zfree S) ≫
        LightCondensed.ihomPoints ℤ LightCondensed.P boundedSeq S
          ((MonoidalClosed.curry F).hom.app (Opposite.op S) x)) = phiG S x :=
    eadataShift_of_truncEAdata F hF S x
  have hφ : Work.ATOM.zmap (MonoidalCategory.whiskerRight LightCondensed.ι S) ≫ phiG S x = 0 := by
    rw [← chiG_comp_cBounded hQ, ← Category.assoc, chiG_infty hQ, zero_comp]
  obtain ⟨ψ, -, huniq⟩ := Work.ATOM.Toolkit.PS_desc S (phiG S x) hφ
  exact (huniq _ ha).trans (huniq _ hb).symm

end Work.ANALYTIC

end
