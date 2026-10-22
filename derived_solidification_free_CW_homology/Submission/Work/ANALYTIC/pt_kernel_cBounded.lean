import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.evenOddDefs
import Submission.Work.FLAT.Setup
import Submission.Work.ATOM.ZS.Unred.LCZ_iso
import Submission.Work.ANALYTIC.ptGenerators

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

/-!
# The kernel of `P_proj ≫ cBounded` at the one-point space

We compute the kernel at `∗` of the composite `ℤ[ℕ∪{∞}] --P_proj--> P --cBounded--> ∏^bnd ℤ`.

The route is through the sheafification unit at the point.  `zfree ∞ = ℤ[ℕ∪{∞}]` is the
sheafification of the sectionwise free presheaf `Q ∞ = S ↦ ℤ[ℕ∪{∞}(S)]`, so every element `x` of
`ℤ[ℕ∪{∞}](∗)` is the image of some `y ∈ Q ∞(∗) = (∗ ⟶ ℕ∪{∞}) →₀ ℤ` under the unit; and the unit at
`∗` is `ℤ`-linear and sends the generator at `𝟙 ∗` to `k • [id]` for some `k : ℤ`
(`zfree_pt_value`, `unit_sheafify_eq_smul_Gm` below).  Hence `x = k • Gm ∞ y`, where `Gm ∞` is the
linear extension of the generators `[u]` for `u : ∗ ⟶ ℕ∪{∞}`.  On generators,
`cBounded (P_proj [u]) = δ_{u}` (`cBounded_homFreeEquiv_zmap`), so the hypothesis `hx` reads
`k • (∑_u y u • δ_u) = 0`, whose `m`-th coordinate is `k * y (ptAt m)` (`finsupp_coord`).  If `k ≠ 0`
all the coefficients at finite points vanish and the collapse lemma `finsupp_collapse_NUI` expresses
`Gm ∞ y` as `(y ι) • [ι]`, whence `x = (k * y ι) • [const ∞]`.

The lemmas proved here (`Gm_apply_finsupp`, `Tm_apply_finsupp`, `unit_sheafify_single`,
`unit_sheafify_eq_smul_Gm`, `proj_cBounded_homFreeEquiv_zmap`, `Gm_comp_cBounded_eq_Tm`) are the
computations along this route.
-/

-- The library's light condensed objects are built by transporting module structures along several
-- layers of definitions; making definitional equality transparency-agnostic removes a spurious
-- mismatch between `↥((Q S).obj (op ∗))` and its unfolded form `(∗ ⟶ S) →₀ ℤ`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- `Gm ℕ∪{∞}`, the linear extension of the generators `[u]` of `ℤ[ℕ∪{∞}](∗)`, on a general finite
combination of generators, as a `Finsupp.sum` over the support. -/
theorem Gm_apply_finsupp (c : (Work.ATOM.pt ⟶ NUI) →₀ ℤ) :
    (Gm NUI) c = c.sum (fun u n => n • Work.ATOM.homFreeEquiv Work.ATOM.pt
      (Work.ATOM.zfree NUI) (Work.ATOM.zmap u)) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero_module, Finsupp.sum_zero_index]
  | add f g ihf ihg =>
      rw [map_add_module,
        Finsupp.sum_add_index' (fun a => by rw [zero_smul])
          (fun a b₁ b₂ => carrier_add_smul b₁ b₂ _),
        ihf, ihg]
  | single a b =>
      rw [Finsupp.sum_single_index (by rw [zero_smul])]
      rw [show (Finsupp.single a b) = b • (Finsupp.single a 1 : (Work.ATOM.pt ⟶ NUI) →₀ ℤ) from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      rw [map_zsmul_module, Gm_freeMk]

/-- `Tm`, the linear extension of the elements `δ_u` (`u : ∗ ⟶ ℕ∪{∞}`) of `∏^bnd ℤ(∗)`, on a
general finite combination of generators, as a `Finsupp.sum` over the support. -/
theorem Tm_apply_finsupp (c : (Work.ATOM.pt ⟶ NUI) →₀ ℤ) :
    Tm c = c.sum (fun u n => n • Work.ANALYTIC.boundedSeq.obj.map u.op
      Work.ANALYTIC.deltaElem) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero_module, Finsupp.sum_zero_index]
  | add f g ihf ihg =>
      rw [map_add_module,
        Finsupp.sum_add_index' (fun a => by rw [zero_smul])
          (fun a b₁ b₂ => carrier_add_smul b₁ b₂ _),
        ihf, ihg]
  | single a b =>
      rw [Finsupp.sum_single_index (by rw [zero_smul])]
      rw [show (Finsupp.single a b) = b • (Finsupp.single a 1 : (Work.ATOM.pt ⟶ NUI) →₀ ℤ) from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      rw [map_zsmul_module, Tm_freeMk]

/-- The sheafification unit at `∗` on a single generator `[u]` of `Q S(∗)` is the pullback along
`ℤ[u]` of the value at the canonical generator `[𝟙 ∗]` of `Q ∗(∗)`: naturality of `toSheafify` in
the presheaf, together with `(Qmap u)([𝟙 ∗]) = [u]`. -/
theorem unit_sheafify_single {S : LightProfinite.{0}} (u : Work.ATOM.pt ⟶ S) :
    ((CategoryTheory.toSheafify J (Q S)).app (op Work.ATOM.pt))
        (Finsupp.single u 1)
      = ((Work.ATOM.zmap u).hom.app (op Work.ATOM.pt))
          (((CategoryTheory.toSheafify J (Q Work.ATOM.pt)).app (op Work.ATOM.pt))
            (Finsupp.single (𝟙 Work.ATOM.pt) 1)) := by
  have h := congrArg (fun (φ : Q Work.ATOM.pt ⟶ CategoryTheory.sheafify J (Q S)) =>
      (φ.app (op Work.ATOM.pt)) (Finsupp.single (𝟙 Work.ATOM.pt) 1))
    (CategoryTheory.toSheafify_naturality (J := J) (D := ModuleCat.{0} ℤ) (Qmap u))
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply] at h
  rw [← zmap_hom_sheafifyMap u] at h
  rw [Qmap_single u] at h
  exact h

/-- The sheafification unit at `∗` is `ℤ`-linear, so if it sends the canonical generator `[𝟙 ∗]` of
`ℤ[∗](∗)` to `k • [id]`, then it sends every element of `ℤ[ℕ∪{∞}](∗)` to the `k`-multiple of its
image under the linear extension `Gm ℕ∪{∞}` of the generators. -/
theorem unit_sheafify_eq_smul_Gm (k : ℤ)
    (hk : ((CategoryTheory.toSheafify J (Q Work.ATOM.pt)).app (op Work.ATOM.pt))
        (Finsupp.single (𝟙 Work.ATOM.pt) 1)
      = k • Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
          (Work.ATOM.zmap (𝟙 Work.ATOM.pt))) (y : ↥((Q NUI).obj (op Work.ATOM.pt))) :
    ((CategoryTheory.toSheafify J (Q NUI)).app (op Work.ATOM.pt)) y = k • ((Gm NUI) y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero_module, carrier_smul_zero]
  | add y₁ y₂ h₁ h₂ =>
      rw [map_add_module, h₁, h₂, map_add_module, carrier_smul_add]
  | single u n =>
      have hgen : ((CategoryTheory.toSheafify J (Q NUI)).app (op Work.ATOM.pt))
          (Finsupp.single u 1)
          = k • Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree NUI)
              (Work.ATOM.zmap u) := by
        rw [unit_sheafify_single u, hk]
        rw [Work.ATOM.ZS.Unred.section_map_smul]
        congr 1
        rw [← Work.ATOM.ZS.Unred.homFreeEquiv_comp (Work.ATOM.zmap (𝟙 Work.ATOM.pt))
          (Work.ATOM.zmap u)]
        congr 1
        rw [← CategoryTheory.Functor.map_comp, CategoryTheory.Category.id_comp]
      rw [show Finsupp.single u n = n • (Finsupp.single u 1 : (Work.ATOM.pt ⟶ NUI) →₀ ℤ) from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      rw [map_zsmul_module, map_zsmul_module, hgen, Gm_freeMk]
      rw [carrier_smul_comm]

/-- `(P_proj ≫ cBounded)` sends the class `[u]` of a map `u : ∗ ⟶ ℕ∪{∞}` to `δ_u`.  This is
`cBounded_homFreeEquiv_zmap` at the one-point space. -/
theorem proj_cBounded_homFreeEquiv_zmap (u : Work.ATOM.pt ⟶ NUI) :
    ((LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app (op Work.ATOM.pt))
        (Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree NUI) (Work.ATOM.zmap u))
      = Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem :=
  Work.ANALYTIC.cBounded_homFreeEquiv_zmap Work.ATOM.pt u

/-- At the one-point space the composite `Gm ℕ∪{∞} ≫ (P_proj ≫ cBounded)` equals `Tm`: both are
`ℤ`-linear and send the generator `[u]` of `Q ℕ∪{∞}(∗)` to `δ_u`. -/
theorem Gm_comp_cBounded_eq_Tm :
    Gm NUI ≫ (LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app (op Work.ATOM.pt)
      = Tm := by
  apply ModuleCat.free_hom_ext
  intro u
  have h1 : (Gm NUI) (ModuleCat.freeMk u)
      = Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree NUI) (Work.ATOM.zmap u) :=
    Gm_freeMk NUI u
  have h2 : Tm (ModuleCat.freeMk u)
      = Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem := Tm_freeMk u
  calc (ConcreteCategory.hom (Gm NUI ≫ (LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app
          (op Work.ATOM.pt))) (ModuleCat.freeMk u)
      = (ConcreteCategory.hom ((LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app
          (op Work.ATOM.pt))) ((ConcreteCategory.hom (Gm NUI)) (ModuleCat.freeMk u)) :=
        CategoryTheory.comp_apply _ _ _
    _ = Work.ANALYTIC.boundedSeq.obj.map u.op Work.ANALYTIC.deltaElem := by
        rw [h1, proj_cBounded_homFreeEquiv_zmap u]
    _ = (ConcreteCategory.hom Tm) (ModuleCat.freeMk u) := h2.symm

/-- The kernel of `P_proj ≫ cBounded` at the one-point space is exactly the line spanned by the
class of the constant map `pt ⟶ ℕ∪{∞}` (the element `[const ∞]`, here
`homFreeEquiv pt ℤ[ℕ∪{∞}] (zmap ι)`), where `Work.ANALYTIC.cBounded : P ⟶ ∏^bnd ℤ` is the null
sequence `e_n ↦ δ_n` and `P_proj : ℤ[ℕ∪{∞}] ⟶ P` is the quotient projection. -/
theorem pt_kernel_cBounded
    (x : ↥((Work.ATOM.zfree (LightProfinite.NatUnionInfty)).obj.obj (Opposite.op Work.ATOM.pt)))
    (hx : (Work.ANALYTIC.cBounded).hom.app (Opposite.op Work.ATOM.pt)
            ((LightCondensed.P_proj).hom.app (Opposite.op Work.ATOM.pt) x) = 0) :
    ∃ n : ℤ, x = n • (Work.ATOM.homFreeEquiv Work.ATOM.pt
        (Work.ATOM.zfree (LightProfinite.NatUnionInfty)) (Work.ATOM.zmap (LightCondensed.ι))) := by
  -- Lift `x` along the sheafification unit at `∗`.
  obtain ⟨y, hy⟩ := surjective_toSheafify_app_pt cover_pt_eq_top (Q NUI) x
  -- The unit at `∗` is `k • [id]` on the canonical generator.
  obtain ⟨k, hk0⟩ := zfree_pt_value
    (((CategoryTheory.toSheafify J (Q Work.ATOM.pt)).app (op Work.ATOM.pt))
      (Finsupp.single (𝟙 Work.ATOM.pt) 1))
  have hk : ((CategoryTheory.toSheafify J (Q Work.ATOM.pt)).app (op Work.ATOM.pt))
        (Finsupp.single (𝟙 Work.ATOM.pt) 1)
      = k • Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
          (Work.ATOM.zmap (𝟙 Work.ATOM.pt)) := by
    simpa only [zmap_id] using hk0
  -- Work with the retyped copy `Y` of `y`, whose index type is `∗ ⟶ ℕ∪{∞}`.
  let Y : (Work.ATOM.pt ⟶ NUI) →₀ ℤ := y
  have hΦ : x = k • ((Gm NUI) Y) := by
    rw [← hy]
    exact unit_sheafify_eq_smul_Gm k hk Y
  have hGm : (Gm NUI) Y = Y.sum (fun u n => n • Work.ATOM.homFreeEquiv Work.ATOM.pt
      (Work.ATOM.zfree NUI) (Work.ATOM.zmap u)) := Gm_apply_finsupp Y
  have hTm : Tm Y = Y.sum (fun u n => n • Work.ANALYTIC.boundedSeq.obj.map u.op
      Work.ANALYTIC.deltaElem) := Tm_apply_finsupp Y
  have hcomp : ((LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app (op Work.ATOM.pt))
      ((Gm NUI) Y) = Tm Y := by
    rw [show ((LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app (op Work.ATOM.pt))
        ((Gm NUI) Y)
        = (Gm NUI ≫ (LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app
            (op Work.ATOM.pt)) Y from rfl, Gm_comp_cBounded_eq_Tm]
  -- The hypothesis, transported along the above computations.
  have hx1 : ((LightCondensed.P_proj ≫ Work.ANALYTIC.cBounded).hom.app (op Work.ATOM.pt)) x
      = k • (Y.sum (fun u n => n • Work.ANALYTIC.boundedSeq.obj.map u.op
          Work.ANALYTIC.deltaElem)) := by
    rw [hΦ, map_zsmul_module, hcomp, hTm]
  have hf : k • (Y.sum (fun u n => n • Work.ANALYTIC.boundedSeq.obj.map u.op
      Work.ANALYTIC.deltaElem)) = 0 := by
    rw [← hx1]
    exact hx
  -- Reading off the `m`-th coordinate gives `k * y (ptAt m) = 0`.
  have hcoord : ∀ m : ℕ, k * Y (Work.ATOM.ptAt (OnePoint.some m)) = 0 := by
    intro m
    have h2 := congrArg (fun z : ↥((Work.ANALYTIC.boundedSeq).obj.obj (op Work.ATOM.pt)) =>
      (z.1 m PUnit.unit)) hf
    rw [Work.ANALYTIC.coe_smul_apply, Work.ANALYTIC.coe_zero_apply,
      finsupp_coord Y m PUnit.unit] at h2
    exact h2
  by_cases hk0' : k = 0
  · -- If `k = 0` then `x = 0 • [id]`.
    refine ⟨0, ?_⟩
    rw [hΦ, hk0']
    simp only [zero_smul]
  · -- Otherwise all coefficients at finite points vanish and `Gm ℕ∪{∞} Y = (Y ι) • [ι]`.
    have hy0 : ∀ m : ℕ, Y (Work.ATOM.ptAt (OnePoint.some m)) = 0 := fun m =>
      (mul_eq_zero.mp (hcoord m)).resolve_left hk0'
    refine ⟨k * Y LightCondensed.ι, ?_⟩
    rw [hΦ]
    exact (congrArg (fun z => k • z) (hGm.trans (finsupp_collapse_NUI Y hy0))).trans
      (carrier_smul_smul k (Y LightCondensed.ι)
        (Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree NUI)
          (Work.ATOM.zmap LightCondensed.ι)))

end

end Work.ANALYTIC
