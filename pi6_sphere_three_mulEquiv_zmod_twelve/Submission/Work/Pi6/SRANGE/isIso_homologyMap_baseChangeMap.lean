import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Pi6.SRANGE.HomQuot
import Submission.Work.Pi6.SRANGE.homQuot_bridge
import Submission.Work.Pi6.SRANGE.intR_map_injective_of_torsionFree
import Submission.Work.Pi6.SRANGE.intR_map_ker_eq_range
import Submission.Work.Pi6.SRANGE.intR_ker_map_bijective
import Submission.Work.Pi6.SRANGE.intR_presentation_bijective
import Submission.Work.Pi6.SRANGE.bijective_mapQ_iff

set_option maxHeartbeats 8000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

attribute [local instance 10] AddCommGroup.toIntModule

namespace Work.Pi6.SRANGE

noncomputable section

/-! ## Cycles and boundaries of a chain complex of `ℤ`-modules -/

/-- The cycles in degree `i`. -/
abbrev Cyc (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) : Submodule ℤ ↥(A.X i) :=
  LinearMap.ker (A.d i (i-1)).hom

/-- The boundaries in degree `i`. -/
abbrev Bdry (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) : Submodule ℤ ↥(A.X i) :=
  LinearMap.range (A.d (i+1) i).hom

/-- The boundaries in degree `i`, viewed as a submodule of the cycles in degree `i`. -/
def b2c (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :=
  (Bdry A i).subtype.codRestrict (Cyc A i) (fun x => by
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp x.2
    rw [Cyc, LinearMap.mem_ker]
    have hx : (Bdry A i).subtype x = (A.d (i+1) i).hom w := hw.symm
    rw [hx]
    have h := HomologicalComplex.d_comp_d A (i+1) i (i-1)
    have h' := congrArg (fun (g : A.X (i+1) ⟶ A.X (i-1)) => g.hom w) h
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h')

/-- The boundaries in degree `i`, as a submodule of the cycles in degree `i`. -/
abbrev BcOf (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) := LinearMap.range (b2c A i)

/-- The inclusion of the boundaries in degree `i` into the cycles in degree `i`. -/
abbrev mum (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) := b2c A i

lemma mum_range (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    LinearMap.range (mum A i) = BcOf A i := rfl

lemma b2c_coe (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) (x : ↥(Bdry A i)) :
    ((b2c A i x : ↥(Cyc A i)) : ↥(A.X i)) = (x : ↥(A.X i)) := by
  rw [show b2c A i = (Bdry A i).subtype.codRestrict (Cyc A i) _ from rfl]
  rw [LinearMap.codRestrict_apply]
  rw [show ((Bdry A i).subtype x : ↥(A.X i)) = (x : ↥(A.X i)) from rfl]

lemma mum_injective (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    Function.Injective (mum A i) := by
  intro x y hxy
  have h1 : (x : ↥(A.X i)) = (y : ↥(A.X i)) := by
    have h := congrArg (fun t => ((t : ↥(Cyc A i)) : ↥(A.X i))) hxy
    rwa [b2c_coe, b2c_coe] at h
  exact Subtype.ext h1

lemma mem_BcOf_iff (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) (x : ↥(Cyc A i)) :
    x ∈ BcOf A i ↔ (x : ↥(A.X i)) ∈ LinearMap.range (A.d (i+1) i).hom := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [b2c_coe]
    exact w.2
  · intro hx
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hx
    refine ⟨⟨(A.d (i+1) i).hom v, ⟨v, rfl⟩⟩, Subtype.ext ?_⟩
    rw [b2c_coe]
    exact hv

/-- The projection of `A_{i+1}` onto the boundaries in degree `i`. -/
abbrev qm (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) := (A.d (i+1) i).hom.rangeRestrict

lemma qm_surjective (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    Function.Surjective (qm A i) := LinearMap.surjective_rangeRestrict _

lemma ker_qm (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    LinearMap.ker (qm A i) = Cyc A (i+1) := by
  rw [qm, LinearMap.ker_rangeRestrict]
  rfl

lemma qm_coe (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) (x : ↥(A.X (i+1))) :
    ((qm A i x : ↥(Bdry A i)) : ↥(A.X i)) = (A.d (i+1) i).hom x :=
  LinearMap.codRestrict_apply _ _ x

/-- The factorization `d_{i+1} = q_i · μ_i · (cycles ↪ A)`. -/
lemma d_eq_comp (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    (A.d (i+1) i).hom = (Cyc A i).subtype.comp ((mum A i).comp (qm A i)) := by
  rw [← LinearMap.comp_assoc]
  rw [show (Cyc A i).subtype.comp (mum A i) =
      (Cyc A i).subtype.comp ((Bdry A i).subtype.codRestrict (Cyc A i) _) from rfl]
  rw [LinearMap.subtype_comp_codRestrict]
  exact LinearMap.subtype_comp_rangeRestrict _

/-- The factorization of `d_{i+1}` as a morphism of `ℤ`-modules. -/
lemma d_eq_comp' (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    A.d (i+1) i = ModuleCat.ofHom (qm A i) ≫ ModuleCat.ofHom (mum A i)
      ≫ ModuleCat.ofHom (Cyc A i).subtype := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  exact d_eq_comp A i

/-! ## The maps induced by a chain map on cycles and boundaries -/

variable {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) (i : ℕ)

/-- The restriction of a chain map to the cycles. -/
def cycMap :=
  LinearMap.restrict (f.f i).hom (p := Cyc C i) (q := Cyc D i) (fun x hx => by
    rw [Cyc, LinearMap.mem_ker] at hx ⊢
    have h := congrArg (fun (g : C.X i ⟶ D.X (i-1)) => g.hom (x : ↥(C.X i))) (f.comm i (i-1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hx, map_zero])

lemma cycMap_coe (x : ↥(Cyc C i)) :
    ((cycMap f i x : ↥(Cyc D i)) : ↥(D.X i)) = (f.f i).hom (x : ↥(C.X i)) :=
  LinearMap.coe_restrict_apply _ x

/-- The map induced by a chain map on the boundaries. -/
def bndMapOf :=
  ((f.f i).hom.comp (Bdry C i).subtype).codRestrict (Bdry D i) (fun y => by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp y.2
    refine ⟨(f.f (i+1)).hom v, ?_⟩
    have h := congrArg (fun (g : C.X (i+1) ⟶ D.X i) => g.hom v) (f.comm (i+1) i)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    calc (ModuleCat.Hom.hom (D.d (i+1) i)) ((ModuleCat.Hom.hom (f.f (i+1))) v)
        = (ModuleCat.Hom.hom (f.f i)) ((ModuleCat.Hom.hom (C.d (i+1) i)) v) := h
      _ = (ModuleCat.Hom.hom (f.f i)) ((Bdry C i).subtype y) := by
            rw [hv]
            rfl)

lemma bndMapOf_coe (y : ↥(Bdry C i)) :
    ((bndMapOf f i y : ↥(Bdry D i)) : ↥(D.X i)) = (f.f i).hom (y : ↥(C.X i)) :=
  LinearMap.codRestrict_apply _ _ y

/-- The induced maps on boundaries and on cycles are compatible. -/
lemma cycMap_mum :
    (cycMap f i).comp (mum C i) = (mum D i).comp (bndMapOf f i) := by
  ext y
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show ((cycMap f i (mum C i y) : ↥(Cyc D i)) : ↥(D.X i))
      = ((mum D i (bndMapOf f i y) : ↥(Cyc D i)) : ↥(D.X i))
  rw [cycMap_coe, b2c_coe, b2c_coe, bndMapOf_coe]

/-- Naturality of the restriction to the cycles. -/
lemma cycMap_subtype_naturality :
    ((Cyc D i).subtype).comp (cycMap f i) = (f.f i).hom.comp (Cyc C i).subtype := by
  ext x
  show ((cycMap f i x : ↥(Cyc D i)) : ↥(D.X i)) = (f.f i).hom ((x : ↥(Cyc C i)) : ↥(C.X i))
  rw [cycMap_coe]

/-- Naturality of the restriction to the cycles, as morphisms of `ℤ`-modules. -/
lemma cycMap_naturality :
    ModuleCat.ofHom (cycMap f i) ≫ ModuleCat.ofHom (Cyc D i).subtype
      = ModuleCat.ofHom (Cyc C i).subtype ≫ f.f i := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  exact cycMap_subtype_naturality f i

/-- Naturality of the projection onto the boundaries. -/
lemma qm_naturality :
    f.f (i+1) ≫ ModuleCat.ofHom (qm D i)
      = ModuleCat.ofHom (qm C i) ≫ ModuleCat.ofHom (bndMapOf f i) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  ext x
  show ((qm D i) ((f.f (i+1)).hom x) : ↥(D.X i)) = ((bndMapOf f i) ((qm C i) x) : ↥(D.X i))
  rw [qm_coe, bndMapOf_coe, qm_coe]
  have h := congrArg (fun (g : C.X (i+1) ⟶ D.X i) => g.hom x) (f.comm (i+1) i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h


/-- The elementwise form of the naturality of the projection onto the boundaries. -/
lemma qm_naturality_apply (R : Type) [CommRing R] {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) (j : ℕ) (x : ↥((IntR R).obj (C.X (j+1)))) :
    ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm D j)))
        (ModuleCat.Hom.hom ((IntR R).map (f.f (j+1))) x)
      = ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (bndMapOf f j)))
          (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm C j))) x) := by
  have hmap : (IntR R).map (f.f (j+1) ≫ ModuleCat.ofHom (qm D j))
      = (IntR R).map (ModuleCat.ofHom (qm C j) ≫ ModuleCat.ofHom (bndMapOf f j)) := by
    rw [qm_naturality f j]
  have h := congrArg (fun (g : (IntR R).obj (C.X (j+1)) ⟶
      (IntR R).obj (ModuleCat.of ℤ ↥(Bdry D j))) => ModuleCat.Hom.hom g x) hmap
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The cycles in degree `i+1` are killed by `d_{i+1}`. -/
lemma d_comp_cyc (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    ModuleCat.ofHom (Cyc A (i+1)).subtype ≫ A.d (i+1) i = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  ext x
  show (A.d (i+1) i).hom ((x : ↥(Cyc A (i+1))) : ↥(A.X (i+1))) = 0
  exact x.2

/-- Elementwise naturality of the restriction to the cycles. -/
lemma cycMap_naturality_apply (R : Type) [CommRing R] {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) (i : ℕ) (x : ↥((IntR R).obj (ModuleCat.of ℤ ↥(Cyc C i)))) :
    ModuleCat.Hom.hom ((IntR R).map (f.f i))
        (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc C i).subtype)) x)
      = ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc D i).subtype))
          (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (cycMap f i))) x) := by
  have hmap : (IntR R).map (ModuleCat.ofHom (cycMap f i) ≫ ModuleCat.ofHom (Cyc D i).subtype)
      = (IntR R).map (ModuleCat.ofHom (Cyc C i).subtype ≫ f.f i) := by
    rw [cycMap_naturality f i]
  have h := congrArg (fun (g : (IntR R).obj (ModuleCat.of ℤ ↥(Cyc C i)) ⟶
      (IntR R).obj (D.X i)) => ModuleCat.Hom.hom g x) hmap
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- A differential composed with the projection onto the boundaries is zero. -/
lemma d_comp_qm (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    A.d (i+2) (i+1) ≫ ModuleCat.ofHom (qm A i) = 0 := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  ext x
  show (A.d (i+1) i).hom ((A.d (i+2) (i+1)).hom x) = 0
  have h := HomologicalComplex.d_comp_d A (i+2) (i+1) i
  have h' := congrArg (fun (g : A.X (i+2) ⟶ A.X i) => g.hom x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h'

/-! ## The base-changed complex -/

variable (R : Type) [CommRing R]

/-- The cycles of the base-changed complex. -/
abbrev CycR (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :=
  LinearMap.ker ((baseChange R A).d i (i-1)).hom

/-- The boundaries of the base-changed complex, as a submodule of its cycles. -/
abbrev BcR (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :=
  (LinearMap.range ((baseChange R A).d (i+1) i).hom).comap (CycR R A i).subtype

lemma homQuotR_eq (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    (homQuot R (baseChange R A) i) = (↥(CycR R A i) ⧸ BcR R A i) := rfl

/-- The quotient `A_i ⧸ cycles` is torsion-free when `A_i` is. -/
lemma torsionFree_quot_cyc (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ)
    (hA : ∀ k : ℕ, Module.IsTorsionFree ℤ ↥(A.X k)) :
    Module.IsTorsionFree ℤ (↥(A.X i) ⧸ Cyc A i) := by
  haveI := hA i
  haveI : Module.IsTorsionFree ℤ ↥(LinearMap.range (A.d i (i-1)).hom) := inferInstance
  haveI := hA (i-1)
  exact Function.Injective.moduleIsTorsionFree
    (LinearMap.quotKerEquivRange (A.d i (i-1)).hom)
    (LinearMap.quotKerEquivRange (A.d i (i-1)).hom).injective
    (fun r m => (LinearMap.quotKerEquivRange (A.d i (i-1)).hom).map_smul r m)

/-- The comparison `F (cycles) ↪ F (A_i)`. -/
lemma intR_cyc_injective (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ)
    (hA : ∀ k : ℕ, Module.IsTorsionFree ℤ ↥(A.X k)) :
    Function.Injective
      (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc A i).subtype))) :=
  intR_map_injective_of_torsionFree R (Cyc A i).subtype Subtype.coe_injective (hA i)
    (by
      rw [Submodule.range_subtype]
      convert torsionFree_quot_cyc A i hA using 1
      exact Subsingleton.elim _ _)

/-- The cycles comparison: `F (cycles_i) = ker (F d_i)`. -/
lemma intR_qm_ker (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    LinearMap.ker (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm A i))))
      = LinearMap.range
          (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc A (i+1)).subtype))) :=
  intR_map_ker_eq_range R (qm A i) (qm_surjective A i) (Cyc A (i+1)).subtype
    ((Submodule.range_subtype _).trans (ker_qm A i).symm)

/-- The kernel of the base-changed differential, described via the projection to boundaries. -/
lemma intR_d_ker_iff (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ)
    (hA : ∀ k : ℕ, Module.IsTorsionFree ℤ ↥(A.X k))
    (x : ↥((IntR R).obj (A.X (i+1)))) :
    ModuleCat.Hom.hom ((IntR R).map (A.d (i+1) i)) x = 0 ↔
      ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm A i))) x
        ∈ LinearMap.ker (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (mum A i)))) := by
  have hfac : ModuleCat.Hom.hom ((IntR R).map (A.d (i+1) i))
      = (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc A i).subtype))).comp
        ((ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (mum A i)))).comp
          (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm A i))))) := by
    rw [d_eq_comp' A i, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp,
      ModuleCat.hom_comp]
    ext x
    rfl
  rw [hfac, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker]
  constructor
  · intro hx
    exact intR_cyc_injective R A i hA hx
  · intro hx
    rw [hx, map_zero]

/-- The range of the base-changed differential. -/
lemma intR_d_range (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (A.d (i+1) i)))
      = Submodule.map (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc A i).subtype)))
          (LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (mum A i))))) := by
  have hfac : ModuleCat.Hom.hom ((IntR R).map (A.d (i+1) i))
      = (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc A i).subtype))).comp
        ((ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (mum A i)))).comp
          (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm A i))))) := by
    rw [d_eq_comp' A i, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp,
      ModuleCat.hom_comp]
    ext x
    rfl
  rw [hfac, LinearMap.range_comp, LinearMap.range_comp]
  haveI : Epi (ModuleCat.ofHom (qm A i)) :=
    (ModuleCat.epi_iff_surjective _).mpr (qm_surjective A i)
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm A i)))) :=
    (ModuleCat.epi_iff_surjective _).mp (Functor.map_epi (IntR R) (ModuleCat.ofHom (qm A i)))
  rw [LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

/-! ## The hypotheses of the presentation lemmas -/

lemma mem_bcOf_iff_comap (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) (x : ↥(Cyc A i)) :
    x ∈ (LinearMap.range (A.d (i+1) i).hom).comap (Cyc A i).subtype ↔ x ∈ BcOf A i := by
  rw [Submodule.mem_comap, mem_BcOf_iff]
  constructor <;> intro h <;> simpa using h

lemma quo_mk_eq_zero_iff (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i : ℕ) (x : ↥(Cyc A i)) :
    (Submodule.Quotient.mk x = (0 : homQuot ℤ A i)) ↔ x ∈ BcOf A i := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_bcOf_iff_comap A i x

/-- The two hypotheses of the presentation lemmas, deduced from the bijectivity of the map
induced on `cycles/boundaries`. -/
lemma h12_of_bijective (hb : Function.Bijective (homQuotMap ℤ f i)) :
    (∀ x : ↥(Cyc C i), cycMap f i x ∈ LinearMap.range (mum D i) →
        x ∈ LinearMap.range (mum C i)) ∧
      (∀ w : ↥(Cyc D i), ∃ w' : ↥(Cyc C i), ∃ v : ↥(Bdry D i),
        cycMap f i w' + mum D i v = w) := by
  have hmap : ∀ x : ↥(Cyc C i),
      homQuotMap ℤ f i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (cycMap f i x) := by
    intro x
    rw [homQuotMap_mk]
    rfl
  constructor
  · intro x hx
    have hx' : cycMap f i x ∈ BcOf D i := by rwa [mum_range D i] at hx
    have h0 : homQuotMap ℤ f i (Submodule.Quotient.mk x) = 0 := by
      rw [hmap x, (quo_mk_eq_zero_iff D i (cycMap f i x)).mpr hx']
    have h1 : Submodule.Quotient.mk x = (0 : homQuot ℤ C i) := hb.1 (by rw [h0, map_zero])
    rw [mum_range C i]
    exact (quo_mk_eq_zero_iff C i x).mp h1
  · intro w
    obtain ⟨y, hy⟩ := hb.2 (Submodule.Quotient.mk w)
    obtain ⟨x, rfl⟩ := Quotient.exists_rep y
    have h1 : (Submodule.Quotient.mk (cycMap f i x) : homQuot ℤ D i) = Submodule.Quotient.mk w :=
      (hmap x).symm.trans hy
    have h2 : cycMap f i x - w ∈ BcOf D i := by
      rw [← quo_mk_eq_zero_iff D i (cycMap f i x - w)]
      have hq : (Submodule.mkQ ((LinearMap.range (D.d (i+1) i).hom).comap (Cyc D i).subtype))
            (cycMap f i x - w) = 0 := by
        rw [map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, h1, sub_self]
      exact hq
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (by rwa [← mum_range D i] at h2)
    refine ⟨x, -v, ?_⟩
    rw [map_neg, hv]
    abel

/-- **Concrete description of the homology**: `Hᵢ` is `cycles/boundaries`, naturally. -/
theorem isIso_homologyMap_iff (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (h : K ⟶ L) (i : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap h i) ↔
      Function.Bijective (homQuotMap R h i) :=
  homQuot_bridge R h i

/-! ## The main theorem -/

theorem isIso_homologyMap_baseChangeMap (R : Type) [CommRing R]
    (C D : ChainComplex (ModuleCat.{0} ℤ) ℕ) (f : C ⟶ D) (N : ℕ)
    (hC : forall i : ℕ, Module.IsTorsionFree ℤ (C.X i))
    (hD : forall i : ℕ, Module.IsTorsionFree ℤ (D.X i))
    (h : forall i : ℕ, i < N → CategoryTheory.IsIso (HomologicalComplex.homologyMap f i)) :
    (forall i : ℕ, i < N → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap R f) i)) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    have hb := (homQuot_bridge ℤ f 0).mp (h 0 hi)
    obtain ⟨h10, h20⟩ := h12_of_bijective f 0 hb
    have htop : ∀ (A : ChainComplex (ModuleCat.{0} ℤ) ℕ), Cyc A 0 = ⊤ := by
      intro A
      rw [Cyc, show A.d 0 (0-1) = 0 from
        HomologicalComplex.shape A 0 0 (by simp [ComplexShape.down])]
      rw [ModuleCat.hom_zero, LinearMap.ker_zero]
    have hsurj : ∀ (A : ChainComplex (ModuleCat.{0} ℤ) ℕ),
        Function.Surjective (ModuleCat.Hom.hom ((IntR R).map
          (ModuleCat.ofHom (Cyc A 0).subtype))) := by
      intro A
      haveI : Epi (ModuleCat.ofHom (Cyc A 0).subtype) :=
        (ModuleCat.epi_iff_surjective _).mpr fun x =>
          ⟨⟨x, by rw [htop A]; exact Submodule.mem_top⟩, rfl⟩
      exact (ModuleCat.epi_iff_surjective _).mp
        (Functor.map_epi (IntR R) (ModuleCat.ofHom (Cyc A 0).subtype))
    rw [isIso_homologyMap_iff R (baseChangeMap R f) 0]
    rw [homQuotMap, bijective_mapQ_iff]
    constructor
    · intro x y hxy
      have key0 : ∀ z : ↥(CycR R C 0),
          ((baseChangeMap R f).f 0).hom (z : ↥((baseChange R C).X 0))
            ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (D.d 1 0))) →
          (z : ↥((baseChange R C).X 0))
            ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (C.d 1 0))) := by
        intro z hz
        obtain ⟨z₁, hz₁⟩ := hsurj C (z : ↥((baseChange R C).X 0))
        rw [← hz₁] at hz
        rw [show (baseChangeMap R f).f 0 = (IntR R).map (f.f 0) from rfl] at hz
        rw [cycMap_naturality_apply R f 0 z₁] at hz
        rw [intR_d_range R D 0] at hz
        obtain ⟨v, hv1, hv2⟩ := Submodule.mem_map.mp hz
        have hv3 : v = ModuleCat.Hom.hom ((IntR R).map
            (ModuleCat.ofHom (cycMap f 0))) z₁ := intR_cyc_injective R D 0 hD hv2
        rw [hv3] at hv1
        have hL4 := (intR_presentation_bijective R (b2c C 0) (mum_injective C 0)
          (b2c D 0) (mum_injective D 0) (bndMapOf f 0) (cycMap f 0)
          (cycMap_mum f 0) h10 h20).1
        have hz2 := hL4 z₁ hv1
        rw [← hz₁, intR_d_range R C 0]
        exact Submodule.mem_map.mpr ⟨z₁, hz2, rfl⟩
      have hz : ((baseChangeMap R f).f 0).hom
            ((x - y : ↥(CycR R C 0)) : ↥((baseChange R C).X 0))
          ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (D.d 1 0))) := by
        have h := Submodule.mem_comap.mp hxy
        simpa [map_sub, LinearMap.coe_restrict_apply] using h
      exact Submodule.mem_comap.mpr (by simpa using key0 (x - y) hz)
    · intro w
      have keyS0 : ∃ z : ↥(CycR R C 0),
          ((baseChangeMap R f).f 0).hom (z : ↥((baseChange R C).X 0))
            - (w : ↥((baseChange R D).X 0))
            ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (D.d 1 0))) := by
        obtain ⟨w₁, hw₁⟩ := hsurj D (w : ↥((baseChange R D).X 0))
        -- h2 at degree 0
        have hL4 := (intR_presentation_bijective R (b2c C 0) (mum_injective C 0)
          (b2c D 0) (mum_injective D 0) (bndMapOf f 0) (cycMap f 0)
          (cycMap_mum f 0) h10 h20).2
        obtain ⟨x₁, hx₁⟩ := hL4 w₁
        have hnat := cycMap_naturality_apply R f 0 x₁
        refine ⟨⟨ModuleCat.Hom.hom ((IntR R).map
            (ModuleCat.ofHom (Cyc C 0).subtype)) x₁, ?_⟩, ?_⟩
        · rw [CycR, LinearMap.mem_ker]
          rw [show (baseChange R C).d 0 (0-1) = 0 from by
            rw [show (baseChange R C).d 0 (0-1) = (IntR R).map (C.d 0 (0-1)) from rfl]
            rw [show C.d 0 (0-1) = 0 from
              HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down])]
            rw [Functor.map_zero]]
          rw [ModuleCat.hom_zero, LinearMap.zero_apply]
        · rw [show (baseChangeMap R f).f 0 = (IntR R).map (f.f 0) from rfl]
          rw [hnat]
          rw [← hw₁]
          rw [intR_d_range R D 0]
          exact Submodule.mem_map.mpr ⟨ModuleCat.Hom.hom ((IntR R).map
            (ModuleCat.ofHom (cycMap f 0))) x₁ - w₁, hx₁, by rw [map_sub]⟩
      obtain ⟨z, hz⟩ := keyS0
      exact ⟨z, Submodule.mem_comap.mpr (by simpa using hz)⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hipos).symm⟩
    have hjN : j < N := by omega
    obtain ⟨h1j, h2j⟩ := h12_of_bijective f j ((homQuot_bridge ℤ f j).mp (h j hjN))
    obtain ⟨h1i, h2i⟩ := h12_of_bijective f (j+1)
      ((homQuot_bridge ℤ f (j+1)).mp (h (j+1) hi))
    rw [isIso_homologyMap_iff R (baseChangeMap R f) (j+1)]
    rw [homQuotMap, bijective_mapQ_iff]
    constructor
    · intro x y hxy
      have key : ∀ z : ↥(CycR R C (j+1)),
          ((baseChangeMap R f).f (j+1)).hom (z : ↥((baseChange R C).X (j+1)))
            ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (D.d (j+2) (j+1)))) →
          (z : ↥((baseChange R C).X (j+1)))
            ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (C.d (j+2) (j+1)))) := by
        intro z hz
        have hz1 : ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm C j)))
              (z : ↥((baseChange R C).X (j+1)))
            ∈ LinearMap.ker (ModuleCat.Hom.hom
              ((IntR R).map (ModuleCat.ofHom (b2c C j)))) :=
          (intR_d_ker_iff R C j hC (z : ↥((baseChange R C).X (j+1)))).mp z.2
        have hz2 : ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (bndMapOf f j)))
              (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm C j)))
                (z : ↥((baseChange R C).X (j+1)))) = 0 := by
          rw [← qm_naturality_apply R f j (z : ↥((baseChange R C).X (j+1)))]
          obtain ⟨u, hu⟩ := hz
          rw [show (baseChangeMap R f).f (j+1) = (IntR R).map (f.f (j+1)) from rfl] at hu
          rw [← hu]
          have h0 : ModuleCat.Hom.hom ((IntR R).map (D.d (j+2) (j+1) ≫
              ModuleCat.ofHom (qm D j))) u = 0 := by
            rw [d_comp_qm D j, Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
          rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h0
          exact h0
        haveI := hC j
        haveI : Module.IsTorsionFree ℤ ↥(Cyc C j) := inferInstance
        haveI := hD j
        haveI : Module.IsTorsionFree ℤ ↥(Cyc D j) := inferInstance
        have hL3 := (intR_ker_map_bijective R (b2c C j) (mum_injective C j)
          (inferInstance : Module.IsTorsionFree ℤ ↥(Cyc C j))
          (b2c D j) (mum_injective D j)
          (inferInstance : Module.IsTorsionFree ℤ ↥(Cyc D j))
          (bndMapOf f j) (cycMap f j) (cycMap_mum f j) h1j h2j).1
        have hz3 : ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm C j)))
              (z : ↥((baseChange R C).X (j+1))) = 0 :=
          hL3 _ 0 hz1 (by simp) (by rw [hz2, map_zero])
        obtain ⟨z₁, hz₁⟩ := LinearMap.mem_range.mp (by
          rw [← intR_qm_ker R C j, LinearMap.mem_ker]
          exact hz3)
        have hz4 : ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (cycMap f (j+1)))) z₁
            ∈ LinearMap.range
              (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (b2c D (j+1))))) := by
          rw [← hz₁] at hz
          rw [show ((baseChangeMap R f).f (j+1) : (baseChange R C).X (j+1) ⟶
              (baseChange R D).X (j+1)) = (IntR R).map (f.f (j+1)) from rfl] at hz
          rw [cycMap_naturality_apply R f (j+1) z₁] at hz
          rw [intR_d_range R D (j+1)] at hz
          obtain ⟨v, hv1, hv2⟩ := Submodule.mem_map.mp hz
          rw [← intR_cyc_injective R D (j+1) hD hv2]
          exact hv1
        have hL4 := (intR_presentation_bijective R (b2c C (j+1)) (mum_injective C (j+1))
          (b2c D (j+1)) (mum_injective D (j+1)) (bndMapOf f (j+1)) (cycMap f (j+1))
          (cycMap_mum f (j+1)) h1i h2i).1
        have hz5 : z₁ ∈ LinearMap.range
            (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (b2c C (j+1))))) :=
          hL4 z₁ hz4
        rw [← hz₁]
        rw [intR_d_range R C (j+1)]
        exact Submodule.mem_map.mpr ⟨z₁, hz5, rfl⟩
      have hz : ((baseChangeMap R f).f (j+1)).hom
            ((x - y : ↥(CycR R C (j+1))) : ↥((baseChange R C).X (j+1)))
          ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (D.d (j+2) (j+1)))) := by
        have h := Submodule.mem_comap.mp hxy
        simpa [map_sub, LinearMap.coe_restrict_apply] using h
      exact Submodule.mem_comap.mpr (by simpa using key (x - y) hz)
    · intro w
      have keyS : ∃ z : ↥(CycR R C (j+1)),
          ((baseChangeMap R f).f (j+1)).hom (z : ↥((baseChange R C).X (j+1)))
            - (w : ↥((baseChange R D).X (j+1)))
            ∈ LinearMap.range (ModuleCat.Hom.hom ((IntR R).map (D.d (j+2) (j+1)))) := by
        have hw1 : ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm D j)))
              (w : ↥((baseChange R D).X (j+1)))
            ∈ LinearMap.ker (ModuleCat.Hom.hom
              ((IntR R).map (ModuleCat.ofHom (b2c D j)))) :=
          (intR_d_ker_iff R D j hD (w : ↥((baseChange R D).X (j+1)))).mp w.2
        haveI := hC j
        haveI : Module.IsTorsionFree ℤ ↥(Cyc C j) := inferInstance
        haveI := hD j
        haveI : Module.IsTorsionFree ℤ ↥(Cyc D j) := inferInstance
        have hL3 := intR_ker_map_bijective R (b2c C j) (mum_injective C j)
          (inferInstance : Module.IsTorsionFree ℤ ↥(Cyc C j))
          (b2c D j) (mum_injective D j)
          (inferInstance : Module.IsTorsionFree ℤ ↥(Cyc D j))
          (bndMapOf f j) (cycMap f j) (cycMap_mum f j) h1j h2j
        obtain ⟨y', hy'1, hy'2⟩ := hL3.2 _ hw1
        haveI : Epi (ModuleCat.ofHom (qm C j)) :=
          (ModuleCat.epi_iff_surjective _).mpr (qm_surjective C j)
        obtain ⟨x₀, hx₀⟩ := (ModuleCat.epi_iff_surjective _).mp
          (Functor.map_epi (IntR R) (ModuleCat.ofHom (qm C j))) y'
        have hfacC : ModuleCat.Hom.hom ((IntR R).map (C.d (j+1) j))
            = (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc C j).subtype))).comp
              ((ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (b2c C j)))).comp
                (ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm C j))))) := by
          rw [d_eq_comp' C j, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp,
            ModuleCat.hom_comp]
          ext x
          rfl
        have hcyc : ModuleCat.Hom.hom ((IntR R).map (C.d (j+1) j)) x₀ = 0 := by
          rw [hfacC, LinearMap.comp_apply, LinearMap.comp_apply, hx₀, hy'1, map_zero]
        have hnatD := qm_naturality_apply R f j x₀
        have hstep : ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (qm D j)))
              (((baseChangeMap R f).f (j+1)).hom x₀ - (w : ↥((baseChange R D).X (j+1)))) = 0 := by
          rw [show (baseChangeMap R f).f (j+1) = (IntR R).map (f.f (j+1)) from rfl]
          rw [map_sub, hnatD, hx₀, hy'2, sub_self]
        obtain ⟨w₁, hw₁⟩ := LinearMap.mem_range.mp (by
          rw [← intR_qm_ker R D j, LinearMap.mem_ker]
          exact hstep)
        have hL4 := (intR_presentation_bijective R (b2c C (j+1)) (mum_injective C (j+1))
          (b2c D (j+1)) (mum_injective D (j+1)) (bndMapOf f (j+1)) (cycMap f (j+1))
          (cycMap_mum f (j+1)) h1i h2i).2
        obtain ⟨x₁, hx₁⟩ := hL4 w₁
        have hcyc2 : ModuleCat.Hom.hom ((IntR R).map (C.d (j+1) j))
              (ModuleCat.Hom.hom ((IntR R).map
                (ModuleCat.ofHom (Cyc C (j+1)).subtype)) x₁) = 0 := by
          have hF : (IntR R).map (ModuleCat.ofHom (Cyc C (j+1)).subtype ≫ C.d (j+1) j) = 0 := by
            rw [d_comp_cyc C j, Functor.map_zero]
          have h := congrArg (fun (g : (IntR R).obj (ModuleCat.of ℤ ↥(Cyc C (j+1))) ⟶
              (IntR R).obj (C.X j)) => ModuleCat.Hom.hom g x₁) hF
          rw [Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_zero,
            LinearMap.zero_apply, LinearMap.comp_apply] at h
          exact h
        have hnat2 := cycMap_naturality_apply R f (j+1) x₁
        refine ⟨⟨(x₀ : ↥((baseChange R C).X (j+1)))
            - ModuleCat.Hom.hom ((IntR R).map (ModuleCat.ofHom (Cyc C (j+1)).subtype)) x₁, ?_⟩, ?_⟩
        · rw [CycR, LinearMap.mem_ker]
          rw [map_sub]
          rw [show ModuleCat.Hom.hom ((baseChange R C).d (j+1) (j+1-1)) x₀ = 0 from hcyc]
          rw [show ModuleCat.Hom.hom ((baseChange R C).d (j+1) (j+1-1))
                (ModuleCat.Hom.hom ((IntR R).map
                  (ModuleCat.ofHom (Cyc C (j+1)).subtype)) x₁) = 0 from hcyc2]
          rw [sub_zero]
        · rw [map_sub]
          rw [show ((baseChangeMap R f).f (j+1)).hom
                (ModuleCat.Hom.hom ((IntR R).map
                  (ModuleCat.ofHom (Cyc C (j+1)).subtype)) x₁)
              = ModuleCat.Hom.hom ((IntR R).map (f.f (j+1)))
                (ModuleCat.Hom.hom ((IntR R).map
                  (ModuleCat.ofHom (Cyc C (j+1)).subtype)) x₁) from rfl]
          rw [hnat2]
          rw [intR_d_range R D (j+1)]
          refine Submodule.mem_map.mpr ⟨-(ModuleCat.Hom.hom ((IntR R).map
              (ModuleCat.ofHom (cycMap f (j+1)))) x₁ - w₁), Submodule.neg_mem _ hx₁, ?_⟩
          rw [map_neg, map_sub, hw₁]
          simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, add_left_comm, add_comm,
            add_neg_cancel_comm_assoc, add_neg_cancel, neg_zero, zero_add, add_zero]
      obtain ⟨z, hz⟩ := keyS
      exact ⟨z, Submodule.mem_comap.mpr (by simpa using hz)⟩
end

end Work.Pi6.SRANGE
