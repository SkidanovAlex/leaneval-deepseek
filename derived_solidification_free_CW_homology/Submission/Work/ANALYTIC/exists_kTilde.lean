import Mathlib
import Submission.Work.ANALYTIC.kTildeDefs
import Submission.Work.ANALYTIC.HaarDefs
import Submission.Work.ANALYTIC.HaarBasisDefs
import Submission.Work.ATOM.Main
import Submission.Work.ATOM.ZS.Unred.LocallyConstantIndicator
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.bijective_schemeD
import Submission.Work.ANALYTIC.cBounded_solidEquiv
import Submission.Work.ANALYTIC.Unconditional
import Submission.Work.TOOLKIT.Main
import Submission.Work.ANALYTIC.haar_phi_fCyl
import Submission.Work.ANALYTIC.prodZModel_isoCoord

/-!
# `Work.ANALYTIC.exists_kTilde` — the reduced null sequence `ℤ̃[T] ⟶ ∏ℤ` is a solid-equivalence

REFS/03 §4 (with the reduction `qred` of `Work.ATOM.zred`): for an infinite light profinite set
`T` there is a morphism

`k : ℤ̃[T] = ℤ[T]/ℤ[s₀] ⟶ ∏_ℕ ℤ`

which is a solid-equivalence.  Its `j`-th coordinate is the "Haar" functional
`κ̃_j : ℤ̃[T] ⟶ ℤ` obtained from the locally constant function `fCyl T j`
(`Submission/Work/ANALYTIC/HaarDefs.lean`, via
`Submission/Work/ATOM/ZS/Unred/LocallyConstantIndicator.lean`), so that

`gRed ≫ k = (standard map P ⟶ ∏^bnd ℤ ⟶ ∏ℤ)`

where `gRed : P ⟶ ℤ̃[T]` is the reduced null sequence of REFS/03 §1.  Since `gRed` is a
solid-equivalence (`kT_solidEquiv_gRed`) and the standard map is one (AN1 `cBounded_solidEquiv`
+ AN2 `solidEquiv_boundedSeqIncl` + the model isomorphism `prodZModel_isoC`, packaged in
`Work.ANALYTIC.prodZModel_isoCoord`), two-out-of-three finishes the proof.

All identifications of coordinates are done with the `LCZ`-model of `ℤ`
(`Submission/Work/ATOM/ZS/Unred/LCZ.lean`), whose sections are *definitionally* locally constant
functions, and transported to `Z` through `Work.ANALYTIC.ZisoLCZ` at the very end.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite OnePoint

noncomputable section

namespace Work.ANALYTIC

/-! ## Generalities on `SolidEquiv` and on `gRed` -/

/-- Postcomposition with an isomorphism is a bijection. -/
theorem kT_postcomp_bijective {C : Type*} [Category C] {Y Z Z' : C} (e : Z ≅ Z') :
    Function.Bijective (fun g : Y ⟶ Z => g ≫ e.hom) := by
  refine ⟨fun a b h => ?_, fun b => ⟨b ≫ e.inv, ?_⟩⟩
  · have h' := congrArg (fun k => k ≫ e.inv) h
    simpa [Category.assoc] using h'
  · simp [Category.assoc]

/-- Bijectivity of a precomposition map is invariant under replacing the target by an isomorphic
object. -/
theorem kT_precomp_iso_target {C : Type*} [Category C] {X Y Z Z' : C} (f : X ⟶ Y)
    (e : Z ≅ Z') :
    Function.Bijective (fun g : Y ⟶ Z => f ≫ g) ↔
      Function.Bijective (fun g' : Y ⟶ Z' => f ≫ g') := by
  constructor
  · intro h
    have hcomp : (fun g' : Y ⟶ Z' => f ≫ g') =
        (fun k : X ⟶ Z => k ≫ e.hom) ∘ (fun g : Y ⟶ Z => f ≫ g) ∘
          (fun g' : Y ⟶ Z' => g' ≫ e.inv) := by
      funext g'
      simp only [Function.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hcomp]
    exact (kT_postcomp_bijective e).comp (h.comp (kT_postcomp_bijective e.symm))
  · intro h
    have hcomp : (fun g : Y ⟶ Z => f ≫ g) =
        (fun k : X ⟶ Z' => k ≫ e.inv) ∘ (fun g' : Y ⟶ Z' => f ≫ g') ∘
          (fun g : Y ⟶ Z => g ≫ e.hom) := by
      funext g
      simp only [Function.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hcomp]
    exact (kT_postcomp_bijective e.symm).comp (h.comp (kT_postcomp_bijective e))

/-- `SolidEquiv` may be tested on the images `Q (ιC N)` of complexes of solid objects: every
object of `D(Solid)` is isomorphic to some `Q M`, and `derivedInclusion (Q M) ≅ Q (ιC M)`. -/
theorem kT_solidEquiv_of_bijective_Q {W : LightCondAb} (g : P ⟶ W)
    (h : ∀ N : CochainComplex Solid ℤ,
      Function.Bijective (fun ψ : DerivedCategory.Q.obj ((Work.ATOM.singleC 0).obj W) ⟶
          DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
        DerivedCategory.Q.map ((Work.ATOM.singleC 0).map g) ≫ ψ)) :
    Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map g) := by
  intro N'
  let M := DerivedCategory.Q.objPreimage N'
  let e := DerivedCategory.Q.objObjPreimageIso N'
  let φ : derivedInclusion.obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj M) :=
    (isSolid.ι.mapDerivedCategoryFactors).app M
  have hM := h M
  refine (kT_precomp_iso_target
    ((DerivedCategory.singleFunctor LightCondAb 0).map g) (derivedInclusion.mapIso e)).mp ?_
  exact (kT_precomp_iso_target
    ((DerivedCategory.singleFunctor LightCondAb 0).map g) φ).mpr hM

/-- **The reduced null sequence `gRed T` is a solid-equivalence** (the `D`-half of the
null-sequence scheme of REFS/03 §1). -/
theorem kT_solidEquiv_gRed (T : LightProfinite.{0}) [Infinite T] :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ATOM.gRed T)) := by
  haveI : CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.MonoidalCategory.tensorLeft P) := Work.ATOM.flat_tensorLeft_P
  exact kT_solidEquiv_of_bijective_Q (Work.ATOM.gRed T)
    (bijective_schemeD T 0 (Work.ATOM.gRed T) (Work.ATOM.F T) (Work.ATOM.s T) (Work.ATOM.G T)
      (Work.ATOM.FP T) (Work.ATOM.sP) (Work.ATOM.m T)
      (Work.ATOM.ZS.h_one T) (Work.ATOM.ZS.h_two T) (Work.ATOM.ZS.h_three T)
      (Work.ATOM.ZS.h_four T) (Work.ATOM.ZS.h_five T) (Work.ATOM.h_six T)
      (Work.ATOM.ZS.h_seven T))

/-! ## Sections of the `LCZ`-model of `ℤ` -/

/-- Coercion of a section of the `LCZ`-model of `ℤ` to a locally constant function (the two types
are definitionally equal; the coercion is there so that the function structure is available). -/
def LCZcoe (S : LightProfinite) (x : ↥(Work.ATOM.ZS.Unred.LCZ.obj.obj (op S))) :
    LocallyConstant ↥S.toTop ℤ := x

/-- The value of a section of `LCZ` at a point. -/
theorem LCZcoe_map_apply (S : LightProfinite) (t : ↥S)
    (F : ↥(Work.ATOM.ZS.Unred.LCZ.obj.obj (op S))) :
    (LCZcoe S F) t =
      (LCZcoe Work.ATOM.pt (Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.ptAt t).op F)) PUnit.unit := by
  rw [show LCZcoe Work.ATOM.pt (Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.ptAt t).op F) =
      (LCZcoe S F).comap (TopCat.Hom.hom (Work.ATOM.ptAt t).hom) from by
    rw [Work.ATOM.ZS.Unred.LCZ_obj_map S (Work.ATOM.ptAt t)]
    rfl]
  rfl

/-- A section of `LCZ` over the point is the constant function at its value. -/
theorem LCZcoe_smul_oneLCZ (c : ℤ) :
    LCZcoe Work.ATOM.pt (c • Work.ATOM.ZS.Unred.oneLCZ) =
      LocallyConstant.const ↥(Work.ATOM.pt.toTop) c := by
  rw [show LCZcoe Work.ATOM.pt (c • Work.ATOM.ZS.Unred.oneLCZ) =
      c • (LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)) from rfl]
  apply LocallyConstant.ext
  intro x
  show (c • (LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)) :
      LocallyConstant ↥(Work.ATOM.pt.toTop) ℤ) x =
    (LocallyConstant.const ↥(Work.ATOM.pt.toTop) c : LocallyConstant ↥(Work.ATOM.pt.toTop) ℤ) x
  rw [show ((c • (LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)) :
        LocallyConstant ↥(Work.ATOM.pt.toTop) ℤ)) x =
      c • ((LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)) :
        ↥(Work.ATOM.pt.toTop) → ℤ) x from rfl]
  rw [show ((LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)) :
      ↥(Work.ATOM.pt.toTop) → ℤ) x = 1 from rfl]
  rw [show ((LocallyConstant.const ↥(Work.ATOM.pt.toTop) c :
      LocallyConstant ↥(Work.ATOM.pt.toTop) ℤ)) x = c from rfl]
  simp

theorem LCZcoe_smul_oneLCZ_val (c : ℤ) :
    (LCZcoe Work.ATOM.pt (c • Work.ATOM.ZS.Unred.oneLCZ)) PUnit.unit = c := by
  rw [LCZcoe_smul_oneLCZ]
  rfl

/-- Two sections over the point are equal as soon as their values at the (unique) point are. -/
theorem LCZcoe_pt_eq_const (A : ↥(Work.ATOM.ZS.Unred.LCZ.obj.obj (op Work.ATOM.pt))) (c : ℤ)
    (h : (LCZcoe Work.ATOM.pt A) PUnit.unit = c) :
    LCZcoe Work.ATOM.pt A = LocallyConstant.const ↥(Work.ATOM.pt.toTop) c := by
  apply LocallyConstant.ext
  intro x
  rw [Subsingleton.elim x PUnit.unit, h]
  rfl

/-! ## The Haar functionals `κ_j` and the map `k` -/

/-- The "Haar" functional `ℤ[T] ⟶ ℤ[∗]` evaluating at the locally constant function
`fCyl T j` (`Submission/Work/ATOM/ZS/Unred/LocallyConstantIndicator.lean`). -/
noncomputable def kBig (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    Work.ATOM.zfree T ⟶ Work.ATOM.zfree Work.ATOM.pt :=
  Classical.choose (Work.ATOM.ZS.Unred.LocallyConstantIndicator T (Haar.fCyl T j))

/-- The defining pointwise property of `kBig`. -/
theorem kBig_spec (T : LightProfinite.{0}) [Infinite T] (j : ℕ) (t : ↥T) :
    Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ kBig T j =
      ((Haar.fCyl T j) t) • 𝟙 (Work.ATOM.zfree Work.ATOM.pt) :=
  Classical.choose_spec (Work.ATOM.ZS.Unred.LocallyConstantIndicator T (Haar.fCyl T j)) t

/-- The identification `ℤ[∗] ≅ LCZ` carrying the generator `e₁` to the constant function `1`. -/
noncomputable def LCZisoPt : Work.ATOM.zfree Work.ATOM.pt ≅ Work.ATOM.ZS.Unred.LCZ :=
  Classical.choose (Work.ATOM.ZS.Unred.LCZ_iso)

theorem LCZisoPt_e1 :
    (LCZisoPt.hom.hom.app (Opposite.op Work.ATOM.pt)) Work.ATOM.ZS.Unred.e1
      = Work.ATOM.ZS.Unred.oneLCZ :=
  Classical.choose_spec (Work.ATOM.ZS.Unred.LCZ_iso)

/-- **The Haar functional** `κ_j : ℤ[T] ⟶ LCZ`. -/
noncomputable def kappaLCZ (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    Work.ATOM.zfree T ⟶ Work.ATOM.ZS.Unred.LCZ :=
  kBig T j ≫ LCZisoPt.hom

/-- The defining property of `κ_j` at a point. -/
theorem kappaLCZ_pt (T : LightProfinite.{0}) [Infinite T] (j : ℕ) (t : ↥T) :
    Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ kappaLCZ T j =
      ((Haar.fCyl T j) t) • LCZisoPt.hom := by
  rw [kappaLCZ, ← Category.assoc, kBig_spec T j t, Preadditive.zsmul_comp, Category.id_comp]

/-- `homFreeEquiv` is linear on the multiples of the canonical generator `LCZisoPt.hom`. -/
theorem homFreeEquiv_smul_LCZisoPt (c : ℤ) :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ (c • LCZisoPt.hom)
      = c • Work.ATOM.ZS.Unred.oneLCZ := by
  have hstep : Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
      (c • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)) = c • Work.ATOM.ZS.Unred.e1 := by
    rw [show c • 𝟙 (Work.ATOM.zfree Work.ATOM.pt) =
        𝟙 (Work.ATOM.zfree Work.ATOM.pt) ≫ (c • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)) from
      (Category.id_comp _).symm]
    rw [Work.ATOM.ZS.Unred.homFreeEquiv_comp]
    rw [show Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
        (𝟙 (Work.ATOM.zfree Work.ATOM.pt)) = Work.ATOM.ZS.Unred.e1 from rfl]
    exact Work.ATOM.ZS.Unred.smul_id_section (Work.ATOM.zfree Work.ATOM.pt) Work.ATOM.pt c
      Work.ATOM.ZS.Unred.e1
  rw [show c • LCZisoPt.hom =
      (c • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)) ≫ LCZisoPt.hom from by
    rw [Preadditive.zsmul_comp, Category.id_comp]]
  rw [Work.ATOM.ZS.Unred.homFreeEquiv_comp, hstep, Work.ATOM.ZS.Unred.section_map_smul,
    LCZisoPt_e1]

/-- The value of `κ_j` at a point `t` under `homFreeEquiv`. -/
theorem homFreeEquiv_kappaLCZ_pt (T : LightProfinite.{0}) [Infinite T] (j : ℕ) (t : ↥T) :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
        (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ kappaLCZ T j)
      = ((Haar.fCyl T j) t) • Work.ATOM.ZS.Unred.oneLCZ := by
  rw [kappaLCZ_pt T j t, homFreeEquiv_smul_LCZisoPt]

/-- **The descent of `κ_j`** to `ℤ̃[T] = ℤ[T]/ℤ[s₀]`: it kills the basis vector `[s₀]` because
`fCyl T j s₀ = 0`. -/
noncomputable def kappaTilde (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ Work.ATOM.ZS.Unred.LCZ :=
  cokernel.desc (Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀)) (kappaLCZ T j)
    (by rw [kappaLCZ_pt, Haar.fCyl_s₀, zero_smul])

theorem kappaTilde_spec (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    Work.ATOM.qred T (Work.ATOM.levelData T).s₀ ≫ kappaTilde T j = kappaLCZ T j :=
  cokernel.π_desc _ _ _

/-- The candidate map, with values in the `LCZ`-model `∏ᶜ LCZ` of `∏ℤ`. -/
noncomputable def kLCZ (T : LightProfinite.{0}) [Infinite T] :
    Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ prodLCZ :=
  Limits.Pi.lift fun j : ℕ => kappaTilde T j

/-! ## The comparison `g ≫ κ_j = cBounded ≫ coord_j` -/

/-- The point `(m, a_m)` of `T' = {(j,a_j)} ∪ {∞} × T`. -/
noncomputable def tPoint (T : LightProfinite.{0}) [Infinite T] (m : ℕ) : ↥(Work.ATOM.T' T) :=
  ⟨Work.ATOM.mkNS T (m : ℕ∪{∞}) ((Work.ATOM.levelData T).a m),
    Work.ATOM.mem_tSet_graph (S := T) m⟩

@[simp] theorem tProj_tPoint (T : LightProfinite.{0}) [Infinite T] (m : ℕ) :
    Work.ATOM.tProj T (tPoint T m) = (m : ℕ∪{∞}) := rfl

@[simp] theorem pr₂T_tPoint (T : LightProfinite.{0}) [Infinite T] (m : ℕ) :
    Work.ATOM.pr₂T T (tPoint T m) = (Work.ATOM.levelData T).a m := rfl

/-- `β` at the point `(m, a_m)` is the "parent" `par T m` of the Haar basis of `C(T,ℤ)`. -/
theorem betaT_tPoint (T : LightProfinite.{0}) [Infinite T] (m : ℕ) :
    Work.ATOM.betaT T (tPoint T m) = Haar.par T m := by
  show Work.ATOM.betaFun T (Work.ATOM.mkNS T (m : ℕ∪{∞}) ((Work.ATOM.levelData T).a m)) =
    Haar.par T m
  rw [Work.ATOM.betaFun, Haar.par]
  rfl

/-- Two morphisms `ℤ[S] ⟶ LCZ` which agree at every point of `S` are equal: the sections of `LCZ`
are locally constant functions and `LCZ.obj.map (ptAt t)` is evaluation at `t`. -/
theorem zfree_ext_pointwise {S : LightProfinite.{0}}
    {θ θ' : Work.ATOM.zfree S ⟶ Work.ATOM.ZS.Unred.LCZ}
    (h : ∀ t : ↥S, LCZcoe Work.ATOM.pt
        (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
          (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ θ))
      = LCZcoe Work.ATOM.pt
        (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
          (Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ θ'))) : θ = θ' := by
  have hmain : LCZcoe S (Work.ATOM.homFreeEquiv S Work.ATOM.ZS.Unred.LCZ θ) =
      LCZcoe S (Work.ATOM.homFreeEquiv S Work.ATOM.ZS.Unred.LCZ θ') := by
    apply LocallyConstant.ext
    intro t
    have h1 := h t
    rw [Work.ATOM.homFreeEquiv_naturality (Work.ATOM.ptAt t) θ,
      Work.ATOM.homFreeEquiv_naturality (Work.ATOM.ptAt t) θ'] at h1
    rw [LCZcoe_map_apply S t (Work.ATOM.homFreeEquiv S Work.ATOM.ZS.Unred.LCZ θ),
      LCZcoe_map_apply S t (Work.ATOM.homFreeEquiv S Work.ATOM.ZS.Unred.LCZ θ'), h1]
  apply (Work.ATOM.homFreeEquiv S Work.ATOM.ZS.Unred.LCZ).injective
  exact hmain

/-- Evaluation of the `j`-th coordinate of the model on a section. -/
theorem coordLCZ_apply (j : ℕ) (S : LightProfinite)
    (x : ↥(Work.ANALYTIC.boundedSeq.obj.obj (Opposite.op S))) (s : ↥S) :
    (LCZcoe S ((coordLCZ j).hom.app (Opposite.op S) x)) s = (x.1 j) s := rfl

/-- The value of `coordLCZ j` on the null sequence `n ↦ δ_n` is `n ↦ δ_{nj}`. -/
theorem coordLCZ_deltaElem (j m : ℕ) :
    (LCZcoe (LightProfinite.NatUnionInfty)
      ((coordLCZ j).hom.app (Opposite.op (LightProfinite.NatUnionInfty)) deltaElem)) (m : ℕ∪{∞})
      = if m = j then 1 else 0 := by
  show deltaFun j (m : ℕ∪{∞}) = _
  rw [deltaFun_eq]
  simp only [OnePoint.some_eq_iff]

/-- `zmap` of the point at infinity, followed by `P_proj`, is zero. -/
theorem zmap_ptAt_infty_P_proj :
    Work.ATOM.zmap (Work.ATOM.ptAt (∞ : ℕ∪{∞})) ≫ LightCondensed.P_proj = 0 := by
  rw [show Work.ATOM.ptAt (∞ : ℕ∪{∞}) = LightCondensed.ι from by
    apply ConcreteCategory.hom_ext
    intro x
    rfl]
  exact cokernel.condition LightCondensed.P_map

/-- `P_proj` is an epimorphism (it is the projection onto a cokernel). -/
theorem P_proj_epi : Epi (LightCondensed.P_proj) :=
  ⟨fun a b h => Cofork.IsColimit.hom_ext
    (Limits.cokernelIsCokernel (LightCondensed.P_map))
    (show LightCondensed.P_proj ≫ a = LightCondensed.P_proj ≫ b from h)⟩

/-- **The comparison of the two null sequences.**  On the reduced object, the composite with the
Haar functional `κ_j` is the `j`-th coordinate of the standard map `P ⟶ ∏^bnd ℤ ⟶ ∏ᶜ LCZ`. -/
theorem g_kappaLCZ (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    Work.ATOM.g T ≫ kappaLCZ T j = cBounded ≫ coordLCZ j := by
  haveI : Epi (LightCondensed.P_proj) := P_proj_epi
  refine (cancel_epi (LightCondensed.P_proj)).mp ?_
  rw [show LightCondensed.P_proj ≫ (Work.ATOM.g T ≫ kappaLCZ T j)
      = (LightCondensed.P_proj ≫ Work.ATOM.g T) ≫ kappaLCZ T j from
    (Category.assoc _ _ _).symm, Work.ATOM.g_spec T]
  refine zfree_ext_pointwise ?_
  intro n
  rcases n with _ | m
  · -- the point `∞`
    have hL : Work.ATOM.zmap (Work.ATOM.ptAt (∞ : ℕ∪{∞})) ≫
        (Work.ATOM.gBig T ≫ kappaLCZ T j) = 0 := by
      rw [show Work.ATOM.ptAt (∞ : ℕ∪{∞}) = LightCondensed.ι from by
        apply ConcreteCategory.hom_ext
        intro x
        rfl]
      rw [← Category.assoc, Work.ATOM.gBig_aug T, zero_comp]
    have hR : Work.ATOM.zmap (Work.ATOM.ptAt (∞ : ℕ∪{∞})) ≫
        (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j) = 0 := by
      rw [← Category.assoc, zmap_ptAt_infty_P_proj, zero_comp]
    have hvv : Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
        (Work.ATOM.zmap (Work.ATOM.ptAt (∞ : ℕ∪{∞})) ≫
          (Work.ATOM.gBig T ≫ kappaLCZ T j))
        = Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
          (Work.ATOM.zmap (Work.ATOM.ptAt (∞ : ℕ∪{∞})) ≫
            (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j)) := by
      rw [hL, hR]
    exact congrArg (LCZcoe Work.ATOM.pt) hvv
  · -- the finite points
    have hzed : Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree T)
        (Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫ Work.ATOM.gBig T)
        = Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree T)
          (Work.ATOM.zmap (Work.ATOM.ptAt (tPoint T m)) ≫ Work.ATOM.gHat T) :=
      Work.ATOM.Toolkit.homFreeEquiv_value_of_descend (Work.ATOM.tProj T) (Work.ATOM.gHat T)
        (Work.ATOM.gBig T) (Work.ATOM.gBig_spec T) (tPoint T m)
    have hdesc0 : LCZcoe Work.ATOM.pt (Work.ATOM.homFreeEquiv Work.ATOM.pt
          Work.ATOM.ZS.Unred.LCZ
          ((Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫ Work.ATOM.gBig T) ≫
            kappaLCZ T j))
        = LCZcoe Work.ATOM.pt (Work.ATOM.homFreeEquiv Work.ATOM.pt
          Work.ATOM.ZS.Unred.LCZ
          ((Work.ATOM.zmap (Work.ATOM.ptAt (tPoint T m)) ≫ Work.ATOM.gHat T) ≫
            kappaLCZ T j)) := by
      rw [Work.ATOM.ZS.Unred.homFreeEquiv_comp, Work.ATOM.ZS.Unred.homFreeEquiv_comp]
      exact congrArg (fun x =>
        LCZcoe Work.ATOM.pt ((kappaLCZ T j).hom.app (Opposite.op Work.ATOM.pt) x)) hzed
    have hsplit : Work.ATOM.zmap (Work.ATOM.ptAt (tPoint T m)) ≫ Work.ATOM.gHat T =
        Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.pr₂T T (tPoint T m))) -
          Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.betaT T (tPoint T m))) := by
      rw [Work.ATOM.gHat, Preadditive.comp_sub,
        ← Work.ATOM.zmap_comp_zfree (Work.ATOM.ptAt (tPoint T m)) (Work.ATOM.pr₂T T),
        ← Work.ATOM.zmap_comp_zfree (Work.ATOM.ptAt (tPoint T m)) (Work.ATOM.betaT T),
        Work.ATOM.Toolkit.ptAt_comp, Work.ATOM.Toolkit.ptAt_comp]
    have hL : LCZcoe Work.ATOM.pt
        (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
          (Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫
            (Work.ATOM.gBig T ≫ kappaLCZ T j)))
        = LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Haar.phi T m (Haar.fCyl T j)) := by
      have h1 := hdesc0
      have h2 : LCZcoe Work.ATOM.pt (Work.ATOM.homFreeEquiv Work.ATOM.pt
            Work.ATOM.ZS.Unred.LCZ
            ((Work.ATOM.zmap (Work.ATOM.ptAt (tPoint T m)) ≫ Work.ATOM.gHat T) ≫
              kappaLCZ T j))
          = LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Haar.phi T m (Haar.fCyl T j)) := by
        rw [hsplit, Preadditive.sub_comp,
          kappaLCZ_pt T j (Work.ATOM.pr₂T T (tPoint T m)),
          kappaLCZ_pt T j (Work.ATOM.betaT T (tPoint T m)), ← sub_smul,
          homFreeEquiv_smul_LCZisoPt, LCZcoe_smul_oneLCZ]
        congr 1
      rw [show Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫
            (Work.ATOM.gBig T ≫ kappaLCZ T j)
          = (Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫ Work.ATOM.gBig T) ≫
            kappaLCZ T j from (Category.assoc _ _ _).symm]
      exact h1.trans h2
    have hR : LCZcoe Work.ATOM.pt
        (Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
          (Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫
            (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j)))
        = LocallyConstant.const ↥(Work.ATOM.pt.toTop) (Haar.phi T m (Haar.fCyl T j)) := by
      rw [Work.ATOM.homFreeEquiv_naturality (Work.ATOM.ptAt (m : ℕ∪{∞}))
        (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j)]
      refine LCZcoe_pt_eq_const _ _ ?_
      rw [show (LCZcoe Work.ATOM.pt (Work.ATOM.ZS.Unred.LCZ.obj.map
            (Work.ATOM.ptAt (m : ℕ∪{∞})).op
            (Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
              (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j)))) PUnit.unit
          = (LCZcoe (LightProfinite.NatUnionInfty)
              (Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
                (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j))) (m : ℕ∪{∞}) from by
        rw [show LCZcoe Work.ATOM.pt (Work.ATOM.ZS.Unred.LCZ.obj.map
              (Work.ATOM.ptAt (m : ℕ∪{∞})).op
              (Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
                (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j))) =
            (LCZcoe (LightProfinite.NatUnionInfty)
              (Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
                (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j))).comap
              (TopCat.Hom.hom (Work.ATOM.ptAt (m : ℕ∪{∞})).hom) from by
          rw [Work.ATOM.ZS.Unred.LCZ_obj_map (LightProfinite.NatUnionInfty)
            (Work.ATOM.ptAt (m : ℕ∪{∞}))]
          rfl]
        rfl]
      rw [show Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
            (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j)
          = Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
            ((LightCondensed.P_proj ≫ cBounded) ≫ coordLCZ j) from by
        rw [Category.assoc],
        show Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) Work.ATOM.ZS.Unred.LCZ
            ((LightCondensed.P_proj ≫ cBounded) ≫ coordLCZ j)
          = (coordLCZ j).hom.app (Opposite.op (LightProfinite.NatUnionInfty)) deltaElem from by
        rw [show LightCondensed.P_proj ≫ cBounded =
            (Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty) boundedSeq).symm
              deltaElem from P_proj_cBounded,
          Work.ATOM.ZS.Unred.homFreeEquiv_comp]
        exact congrArg (fun x =>
          (coordLCZ j).hom.app (Opposite.op (LightProfinite.NatUnionInfty)) x)
          (Equiv.apply_symm_apply (Work.ATOM.homFreeEquiv (LightProfinite.NatUnionInfty)
            boundedSeq) deltaElem)]
      rw [coordLCZ_deltaElem, haar_phi_fCyl T m j]
    have hvv : Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
        (Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫ (Work.ATOM.gBig T ≫ kappaLCZ T j))
        = Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
          (Work.ATOM.zmap (Work.ATOM.ptAt (m : ℕ∪{∞})) ≫
            (LightCondensed.P_proj ≫ cBounded ≫ coordLCZ j)) := by
      exact hL.trans hR.symm
    exact congrArg (LCZcoe Work.ATOM.pt) hvv

/-! ## The main theorem -/

theorem exists_kTilde (T : LightProfinite.{0}) [Infinite T] :
    ∃ k : Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ Work.ANALYTIC.prodZ,
      Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map k) := by
  obtain ⟨e, he⟩ := prodZModel_isoCoord
  haveI : CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.MonoidalCategory.tensorLeft P) := Work.ATOM.flat_tensorLeft_P
  -- the standard map `P ⟶ ∏ᶜ LCZ` and the comparison with `gRed ≫ kLCZ`
  let stdLCZ : P ⟶ prodLCZ := cBounded ≫ boundedSeqIncl ≫ e.hom
  have hcomp : Work.ATOM.gRed T ≫ kLCZ T = stdLCZ := by
    refine Limits.Pi.hom_ext _ _ fun j => ?_
    have h1 : (Work.ATOM.gRed T ≫ kLCZ T) ≫
        CategoryTheory.Limits.Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j
        = Work.ATOM.g T ≫ kappaLCZ T j := by
      rw [kLCZ, Category.assoc, Limits.Pi.lift_comp_π,
        show Work.ATOM.gRed T =
          Work.ATOM.g T ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀ from rfl,
        Category.assoc, kappaTilde_spec]
    have h2 : stdLCZ ≫ CategoryTheory.Limits.Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j
        = cBounded ≫ coordLCZ j := by
      rw [show stdLCZ = cBounded ≫ boundedSeqIncl ≫ e.hom from rfl, Category.assoc, he j]
    rw [h1, h2]
    exact g_kappaLCZ T j
  -- the three ingredients of the standard map are solid-equivalences
  have hcb : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map cBounded) := cBounded_solidEquiv
  have hincl : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map boundedSeqIncl) :=
    solidEquiv_boundedSeqIncl Work.TOOLKIT.toolkit_prop
  have heh : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map e.hom) :=
    Work.TOOLKIT.toolkit_prop.of_iso _ (Functor.map_isIso _ e.hom)
  have hstd : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map stdLCZ) := by
    have h1 : Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map
          (cBounded ≫ boundedSeqIncl ≫ e.hom)) := by
      rw [Functor.map_comp, Functor.map_comp]
      exact Work.TOOLKIT.toolkit_prop.comp _ _ hcb
        (Work.TOOLKIT.toolkit_prop.comp _ _ hincl heh)
    simpa only [stdLCZ] using h1
  have hgr : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ATOM.gRed T)) :=
    kT_solidEquiv_gRed T
  have hgk : Submission.Blueprint.SolidEquiv
      (((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ATOM.gRed T)) ≫
        ((DerivedCategory.singleFunctor LightCondAb 0).map (kLCZ T))) := by
    rw [← Functor.map_comp, hcomp]
    exact hstd
  have hk : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (kLCZ T)) :=
    Work.TOOLKIT.toolkit_prop.of_comp_left
      ((DerivedCategory.singleFunctor LightCondAb 0).map (Work.ATOM.gRed T))
      ((DerivedCategory.singleFunctor LightCondAb 0).map (kLCZ T)) hgr hgk
  refine ⟨kLCZ T ≫ prodZisoProdLCZ.inv, ?_⟩
  rw [Functor.map_comp]
  refine Work.TOOLKIT.toolkit_prop.comp _ _ hk ?_
  exact Work.TOOLKIT.toolkit_prop.of_iso _ (Functor.map_isIso _ prodZisoProdLCZ.inv)

end Work.ANALYTIC
