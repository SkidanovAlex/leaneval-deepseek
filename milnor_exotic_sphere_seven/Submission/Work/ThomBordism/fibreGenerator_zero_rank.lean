import Mathlib
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.chartCoeffAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# The fibre-generator condition for a Thom class of a rank-`0` bundle

This is the case `n = 0` of `Work.ThomBordism.thomClass_fibreGenerator`: a real bundle whose model
fibre is `0`-dimensional has empty complement of the zero section, so the cohomology of its Thom
pair is the absolute cohomology of the total space, and the `π^*`-isomorphism together with the
Thom isomorphism force the Thom class to be a *unit* of the ring `H⁰(E;ℤ)` — in particular its
restriction to every fibre (a single point) generates `H⁰(pt;ℤ) = ℤ`.

The file contains the rank-`0` bundle machinery (empty punctured locus, the fibre is a point, the
forgetful map `relToAbs` is an isomorphism for an empty excluded set) together with the main
theorem `Work.ThomBordism.fibreGenerator_zero_rank`.
-/

namespace Work.ThomBordism

open CategoryTheory

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-! ## Rank-zero preparations -/

/-- A finite-dimensional real vector space of dimension `0` is a subsingleton. -/
theorem subsingleton_of_finrank_zero [FiniteDimensional ℝ F] (h : Module.finrank ℝ F = 0) :
    Subsingleton F := by
  rw [Module.finrank_eq_zero_iff] at h
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha, hax⟩ := h (x - y)
  have hxy : x - y = 0 := (smul_eq_zero.mp hax).resolve_left ha
  exact sub_eq_zero.mp hxy

/-- The complement of the zero section of a bundle with a subsingleton fibre is empty. -/
theorem zeroComplement_eq_empty [Subsingleton F] (Z : RealBundle B F ι) :
    Work.Thom.zeroComplement Z = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
  rw [Work.Thom.mem_zeroComplement] at hp
  exact hp (Subsingleton.elim _ _)

/-- The punctured fibre of a bundle with a subsingleton fibre is empty. -/
theorem fibrePunctSub_eq_empty [Subsingleton F] (Z : RealBundle B F ι) (b : B) :
    fibrePunctSub Z b = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
  exact hp.2 (Subsingleton.elim (show F from (p : Z.TotalSpace).2) (0 : F))

/-- The fibre of a bundle with a subsingleton fibre is a subsingleton. -/
theorem subsingleton_fibre [Subsingleton F] (Z : RealBundle B F ι) (b : B) :
    Subsingleton ↥(fibre Z b) := by
  refine ⟨fun p q => ?_⟩
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · exact p.2.trans q.2.symm
  · exact heq_of_eq (Subsingleton.elim (show F from (p : Z.TotalSpace).2)
      (show F from (q : Z.TotalSpace).2))

/-- The fibre of a bundle is nonempty. -/
theorem nonempty_fibre (Z : RealBundle B F ι) (b : B) : Nonempty ↥(fibre Z b) :=
  ⟨⟨(⟨b, (0 : F)⟩ : Z.TotalSpace), rfl⟩⟩

/-- **The forgetful map of a pair with empty excluded set is an isomorphism.** -/
theorem isIso_relToAbs_of_eq_empty {X : Type} [TopologicalSpace X] {A : Set X} (h : A = ∅)
    (n : ℕ) : IsIso (Work.Thom.relToAbs ℤ A n) := by
  subst h
  exact Work.Cohomology.relComplex_empty_homology_iso (TopCat.of X) n

/-- **The forgetful map of a pair with empty excluded set is bijective.** -/
theorem bijective_relToAbs_of_eq_empty {X : Type} [TopologicalSpace X] {A : Set X} (h : A = ∅)
    (n : ℕ) : Function.Bijective ((Work.Thom.relToAbs ℤ A n).hom) := by
  haveI := isIso_relToAbs_of_eq_empty h n
  exact CategoryTheory.ConcreteCategory.bijective_of_isIso _

/-! ## Generators, bijections and negation

The two `ℤ`-scalar multiplications on an abelian group (the canonical `zsmul` and the one coming
from a `Module ℤ` structure) are identified by `int_smul_eq_zsmul`; the statement below is phrased
in the canonical form so that it matches the statements produced by the point evaluations
(`Work.Thom.ptEv_eq_smul_oneH`). -/

/-- A `ℤ`-module is spanned by a single element iff every element is an integer multiple of it. -/
private theorem span_singleton_eq_top_iff_zsmul {M : Type*} [AddCommGroup M] [Module ℤ M]
    (x : M) : Submodule.span ℤ {x} = ⊤ ↔ ∀ z : M, ∃ a : ℤ, z = a • x := by
  have bridge : ∀ (a : ℤ), (LinearMap.toSpanSingleton ℤ M x) a = (a • x : M) := by
    intro a
    rw [LinearMap.toSpanSingleton_apply]
    exact int_smul_eq_zsmul (inferInstance : Module ℤ M) a x
  constructor
  · intro h z
    have hmem : z ∈ Submodule.span ℤ {x} := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have ha' : (LinearMap.toSpanSingleton ℤ M x) a = z := by
      rw [LinearMap.toSpanSingleton_apply]; exact ha
    exact ⟨a, by rw [← ha', bridge]⟩
  · intro h
    rw [Submodule.eq_top_iff']
    intro z
    obtain ⟨a, ha⟩ := h z
    rw [ha, ← bridge a]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton x))

/-- If `f` is surjective and `a` generates `M`, then `f a` generates `N`. -/
private theorem span_singleton_eq_top_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {a : M}
    (h : Submodule.span ℤ {a} = ⊤) : Submodule.span ℤ {f a} = ⊤ := by
  have h1 : Submodule.span ℤ {f a} = Submodule.map f (Submodule.span ℤ {a}) := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [h1, h, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

/-- **A bijective `ℤ`-linear map sends generators to generators and nothing else.** -/
private theorem span_singleton_eq_top_iff_of_bijective {M N : Type*} [AddCommGroup M] [Module ℤ M]
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

/-- **The span of `-x` is the span of `x`.** -/
private theorem span_singleton_eq_top_of_eq_neg {M : Type*} [AddCommGroup M] [Module ℤ M]
    {x y : M} (h : Submodule.span ℤ {x} = ⊤) (hxy : y = -x) :
    Submodule.span ℤ {y} = ⊤ := by
  rw [hxy]
  rw [span_singleton_eq_top_iff_zsmul] at h ⊢
  intro z
  obtain ⟨a, ha⟩ := h z
  refine ⟨-a, ?_⟩
  rw [ha]
  simp only [zsmul_neg', neg_neg]

/-! ## The point evaluation of the absolute Thom class of a rank-`0` bundle -/

/-- **The absolute Thom class of a rank-`0` bundle evaluates to `±1` at every point.**

Let `E` be the total space of a real bundle with a subsingleton model fibre, so that the
complement `E∖0` of the zero section is empty and `H⁰(E,E∖0;ℤ) = H⁰(E;ℤ)`.  The Thom isomorphism
makes `τ` a *unit* of the ring `H⁰(E;ℤ)`: the preimage of the unit class `1 ∈ H⁰(E;ℤ)` under the
Thom map is some `π^*(x)` (`x ∈ H⁰(B;ℤ)`), so `π^*x ⌣ τ = 1`; evaluating at a point `e` gives
`ptEv (π e) x · ptEv e τ = 1`, whence `ptEv e τ = ±1`. -/
theorem ptEv_relToAbs_thomClass_zero [Subsingleton F] (Z : RealBundle B F ι)
    (T : Work.Thom.ThomClass Z 0) :
    ∀ e : Z.TotalSpace,
      Work.Thom.ptEv e ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) 0).hom T.τ) = 1 ∨
      Work.Thom.ptEv e ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) 0).hom T.τ) = -1 := by
  have hA : Work.Thom.zeroComplement Z = ∅ := zeroComplement_eq_empty Z
  have hbij : Function.Bijective ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) 0).hom) :=
    bijective_relToAbs_of_eq_empty hA 0
  obtain ⟨η, hη⟩ := hbij.2 (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)))
  obtain ⟨x, hx⟩ := (T.isThom 0).2 η
  have hkey : (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 0 0
        ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ 0).hom x))
        ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) 0).hom T.τ)
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) := by
    rw [← Work.Thom.mixedCup_relToAbs (Work.Thom.zeroComplement Z) 0 0
      ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ 0).hom x) T.τ]
    rw [← Work.Thom.thomMap_apply Z 0 T.τ 0 x, hx, hη]
  intro e
  have h1 : Work.Thom.ptEv e
      (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace))) = 1 :=
    Work.Thom.ptEv_one e
  rw [← hkey] at h1
  rw [Work.Thom.ptEv_cup] at h1
  exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact h1)

/-! ## The main theorem -/

theorem fibreGenerator_zero_rank {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.ThomClass Z n)
    (hn : n = Module.finrank ℝ F) (h0 : n = 0) :
    Work.ThomBordism.IsFibreGenerator Z n T.τ := by
  subst h0
  have hF : Subsingleton F := subsingleton_of_finrank_zero hn.symm
  haveI := hF
  intro b
  obtain ⟨p⟩ := nonempty_fibre Z b
  haveI : Subsingleton ↥(fibre Z b) := subsingleton_fibre Z b
  have hA : fibrePunctSub Z b = ∅ := fibrePunctSub_eq_empty Z b
  have hbij : Function.Bijective ((Work.Thom.relToAbs ℤ (fibrePunctSub Z b) 0).hom) :=
    bijective_relToAbs_of_eq_empty hA 0
  have hchain : (Work.Thom.relToAbs ℤ (fibrePunctSub Z b) 0).hom (fibreRes Z b 0 T.τ)
      = (Work.Thom.CohMap (fibreIncl Z b) ℤ 0).hom
          ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) 0).hom T.τ) := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (Work.Thom.relCohMap_relToAbs (fibreIncl Z b) (fibrePunctSub Z b)
        (Work.Thom.zeroComplement Z) (fibreIncl_mem Z b) ℤ 0)) T.τ
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, fibreRes] using h
  let u : Work.Thom.Coh ℤ 0 ↥(fibre Z b) :=
    Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(fibre Z b)))
  let x : Work.Thom.Coh ℤ 0 ↥(fibre Z b) :=
    (Work.Thom.relToAbs ℤ (fibrePunctSub Z b) 0).hom (fibreRes Z b 0 T.τ)
  have hspanone : Submodule.span ℤ {u} = ⊤ :=
    (span_singleton_eq_top_iff_zsmul u).mpr (fun z =>
      ⟨Work.Thom.ptEv p z, Work.Thom.ptEv_eq_smul_oneH p z⟩)
  have hpt : Work.Thom.ptEv p x = 1 ∨ Work.Thom.ptEv p x = -1 := by
    show Work.Thom.ptEv p
        ((Work.Thom.relToAbs ℤ (fibrePunctSub Z b) 0).hom (fibreRes Z b 0 T.τ)) = 1 ∨
      Work.Thom.ptEv p
        ((Work.Thom.relToAbs ℤ (fibrePunctSub Z b) 0).hom (fibreRes Z b 0 T.τ)) = -1
    rw [hchain, Work.Thom.ptEv_pullback]
    exact ptEv_relToAbs_thomClass_zero Z T (fibreIncl Z b p)
  have hspan : Submodule.span ℤ {x} = ⊤ := by
    rcases hpt with hone | hneg
    · have hx : x = u := Work.Thom.ptEv_ext (fun q => by
        rw [Subsingleton.elim q p, hone, Work.Thom.ptEv_one])
      rw [hx]; exact hspanone
    · have hx : x = -u := Work.Thom.ptEv_ext (fun q => by
        rw [Subsingleton.elim q p, hneg, Work.Thom.ptEv_neg, Work.Thom.ptEv_one])
      exact span_singleton_eq_top_of_eq_neg hspanone hx
  have hspan' : Submodule.span ℤ
      {((Work.Thom.relToAbs ℤ (fibrePunctSub Z b) 0).hom (fibreRes Z b 0 T.τ))} = ⊤ := hspan
  exact (span_singleton_eq_top_iff_of_bijective _ hbij (fibreRes Z b 0 T.τ)).mp hspan'

end

end Work.ThomBordism
