import Mathlib
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.ChartOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The two models of the restriction of a Thom class to a fibre

The fibre-generator condition for a class `σ ∈ H^n(E,E∖0;ℤ)` of a real bundle `Z → B`
(`Work.ThomBordism.IsFibreGenerator`) is stated in terms of the restriction
`Work.ThomBordism.fibreRes Z b n σ`, i.e. of the pullback of `σ` along the inclusion
`(Z_b, Z_b∖0) ↪ (E, E∖0)` of the **fibre pair**.

The concrete computations of the workspace (for instance
`Work.Tubular.localThomOfChart_fibre_span_top`, `Work.Tubular.thomClass_fibre_span_top_of_chart`)
produce the same statement for the *piece* model `Work.Thom.PieceCoh Z {b} n` of the relative
cohomology of the pair over the singleton `{b} ⊆ B`, i.e. for
`(Work.Thom.PieceRes Z {b} n) σ`.

The two modules `RelCoh ℤ n ↥(fibre Z b) (fibrePunctSub Z b)` and
`PieceCoh Z {b} n = pdCohSub (Z.TotalSpace) (zeroComplement Z) (Z.proj ⁻¹' {b})` describe the
relative cohomology of *the same pair* — the difference is only that the punctured fibre
`fibrePunctSub Z b` carries the redundant condition `p.1 = b` on top of `p.2 ≠ 0`, so that the two
excluded sets are extensionally equal but not syntactically equal.  The canonical identification is
the map induced on relative cohomology by the identity of the punctured fibre, which is an
isomorphism of pairs (`Work.Thom.bijective_relCohMap_of_homeomorphA`), and this file proves that
under it the two restrictions correspond:

`(id)^* (fibreRes Z b n x) = (PieceRes Z {b} n) x`.

Consequently `fibreRes Z b n x` generates its module if and only if `(PieceRes Z {b} n) x`
generates its own, which is the content of the main theorem `fibreRes_span_iff`.
-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} {n : ℕ}

/-- **The punctured fibre, described as the fibre intersected with the complement of the zero
section.**  This is the excluded set of the *piece* model of the fibre pair: it is the same set as
`fibrePunctSub Z b`, but the (redundant) condition `p.1 = b` of the latter is replaced by the
membership of the point in the fibre. -/
private abbrev fibreZeroSub (Z : RealBundle B F ι) (b : B) : Set ↥(fibre Z b) :=
  (Subtype.val : ↥(fibre Z b) → Z.TotalSpace) ⁻¹' (Work.Thom.zeroComplement Z)

/-- Membership in `fibreZeroSub Z b`, unfolded. -/
private lemma mem_fibreZeroSub (Z : RealBundle B F ι) (b : B) (y : ↥(fibre Z b)) :
    y ∈ fibreZeroSub Z b ↔ (show F from (y : Z.TotalSpace).2) ≠ 0 := Iff.rfl

/-- Membership in the punctured fibre `fibrePunctSub Z b`: the condition `p.1 = b` is automatic on
the fibre, so only `p.2 ≠ 0` remains. -/
private lemma mem_fibrePunctSub (Z : RealBundle B F ι) (b : B) (y : ↥(fibre Z b)) :
    y ∈ fibrePunctSub Z b ↔ (show F from (y : Z.TotalSpace).2) ≠ 0 :=
  ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩

/-! ## A single element generates if and only if its image under a bijection does -/

/-- If `f` is surjective and `a` generates `M`, then `f a` generates `N`. -/
private lemma span_singleton_eq_top_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {a : M}
    (h : Submodule.span ℤ {a} = ⊤) : Submodule.span ℤ {f a} = ⊤ := by
  have h1 : Submodule.span ℤ {f a} = Submodule.map f (Submodule.span ℤ {a}) := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [h1, h, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

/-- **A bijective `ℤ`-linear map sends generators to generators and nothing else.** -/
private lemma span_singleton_eq_top_iff_of_bijective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Bijective f) (a : M) :
    Submodule.span ℤ {f a} = ⊤ ↔ Submodule.span ℤ {a} = ⊤ := by
  refine ⟨fun h => ?_, fun h => span_singleton_eq_top_of_surjective f hf.2 h⟩
  have hs : ∀ x : M, f x ∈ Submodule.span ℤ {f a} → x ∈ Submodule.span ℤ {a} := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, hf.1 ?_⟩
    rw [← hm]
    simp
  rw [Submodule.eq_top_iff']
  intro y
  exact hs y (by rw [h]; exact Submodule.mem_top)

/-! ## The two models of the restriction to a fibre agree -/

/-- **The restriction of a class of the Thom pair to the fibre, in the two models.**  The identity
of the punctured fibre `(↥(fibre Z b), fibreZeroSub Z b) → (↥(fibre Z b), fibrePunctSub Z b)` is an
isomorphism of pairs (`he`), and pulling back along it identifies the two descriptions of the
restriction of `x` to the fibre: `fibreRes` (the fibre-pair model) and `PieceRes` (the piece model
over the singleton `{b}`). -/
private lemma fibreRes_eq_PieceRes (Z : RealBundle B F ι) (b : B) (x : Work.Thom.OpenThom Z n)
    (he : ∀ y : ↥(fibre Z b),
      y ∈ fibreZeroSub Z b ↔ (Homeomorph.refl ↥(fibre Z b)) y ∈ fibrePunctSub Z b) :
    (ModuleCat.Hom.hom (Work.Thom.relCohMap
        ((Homeomorph.refl ↥(fibre Z b)) : C(↥(fibre Z b), ↥(fibre Z b)))
        (fibreZeroSub Z b) (fibrePunctSub Z b) (fun y hy => (he y).mp hy) ℤ n))
        (fibreRes Z b n x)
      = (ModuleCat.Hom.hom (Work.Thom.PieceRes Z ({b} : Set B) n)) x := by
  have hgf : ∀ y ∈ fibreZeroSub Z b,
      (fibreIncl Z b) (((Homeomorph.refl ↥(fibre Z b)) : C(↥(fibre Z b), ↥(fibre Z b))) y)
        ∈ Work.Thom.zeroComplement Z :=
    fun y hy => fibreIncl_mem Z b _ ((he y).mp hy)
  -- Functoriality of the pullback of relative cohomology for the composite of maps of pairs
  -- `fibreIncl Z b ∘ id = subtypeMap (Z.proj ⁻¹' {b})`.
  have hcomp := Work.Thom.relCohMap_compA (fibreZeroSub Z b) (fibrePunctSub Z b)
    (Work.Thom.zeroComplement Z)
    ((Homeomorph.refl ↥(fibre Z b)) : C(↥(fibre Z b), ↥(fibre Z b)))
    (fibreIncl Z b) (fun y hy => (he y).mp hy) (fibreIncl_mem Z b) hgf ℤ n
  have h1 := congrArg (fun m => (ModuleCat.Hom.hom m) x) hcomp
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  -- the first factor is `fibreRes`
  have hX : (ModuleCat.Hom.hom (Work.Thom.relCohMap (fibreIncl Z b) (fibrePunctSub Z b)
      (Work.Thom.zeroComplement Z) (fibreIncl_mem Z b) ℤ n)) x = fibreRes Z b n x := rfl
  -- the second factor is `PieceRes`, by the definition of the piece model
  have hmor : Work.Thom.relCohMap ((fibreIncl Z b).comp
        ((Homeomorph.refl ↥(fibre Z b)) : C(↥(fibre Z b), ↥(fibre Z b))))
        (fibreZeroSub Z b) (Work.Thom.zeroComplement Z) hgf ℤ n
      = Work.Thom.PieceRes Z ({b} : Set B) n := by
    rw [Work.Thom.relCohMap_congrA (fibreZeroSub Z b) (Work.Thom.zeroComplement Z)
      (f := ((fibreIncl Z b).comp
        ((Homeomorph.refl ↥(fibre Z b)) : C(↥(fibre Z b), ↥(fibre Z b)))))
      (f' := Work.Thom.subtypeMap (Z.proj ⁻¹' ({b} : Set B))) rfl hgf (fun y hy => hy) ℤ n]
    rfl
  rw [hX] at h1
  rw [hmor] at h1
  exact h1

theorem fibreRes_span_iff {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (b : B) (x : Work.Thom.OpenThom Z n) :
    Submodule.span ℤ {Work.ThomBordism.fibreRes Z b n x} = ⊤ ↔
      Submodule.span ℤ
        {(ModuleCat.Hom.hom (Work.Thom.PieceRes Z ({b} : Set B) n)) x} = ⊤ := by
  have he : ∀ y : ↥(fibre Z b),
      y ∈ fibreZeroSub Z b ↔ (Homeomorph.refl ↥(fibre Z b)) y ∈ fibrePunctSub Z b :=
    fun y => (mem_fibreZeroSub Z b y).trans
      (Iff.symm (mem_fibrePunctSub Z b ((Homeomorph.refl ↥(fibre Z b)) y)))
  -- the identity of the punctured fibre is an isomorphism of pairs
  have hbij : Function.Bijective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      ((Homeomorph.refl ↥(fibre Z b)) : C(↥(fibre Z b), ↥(fibre Z b)))
      (fibreZeroSub Z b) (fibrePunctSub Z b) (fun y hy => (he y).mp hy) ℤ n)) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (fibreZeroSub Z b) (fibrePunctSub Z b)
      (Homeomorph.refl ↥(fibre Z b)) he ℤ n
  -- under it, the two restrictions correspond
  have hkey := fibreRes_eq_PieceRes Z b x he
  exact (span_singleton_eq_top_iff_of_bijective _ hbij (fibreRes Z b n x)).symm.trans
    (Iff.of_eq (congrArg (fun v => Submodule.span ℤ {v} = ⊤) hkey))

end

end Work.ThomBordism
