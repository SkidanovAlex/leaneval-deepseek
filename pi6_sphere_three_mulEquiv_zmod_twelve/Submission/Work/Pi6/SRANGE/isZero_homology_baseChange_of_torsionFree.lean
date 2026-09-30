import Mathlib
import Submission.Work.Pi6.SRANGE.Defs
import Submission.Work.Cohomology.uctDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Base change along `ℤ → R` preserves vanishing of homology in low degrees

If `C` is a chain complex of torsion-free `ℤ`-modules which is acyclic in degrees `≤ N`, then for
every commutative ring `R` the base changed complex `C ⊗[ℤ] R` is acyclic in degrees `≤ N`.

This is the elementary part of the universal coefficient theorem.  Writing `Zₙ = ker dₙ` and
`Bₙ = im d_{n+1}`, the two relevant short exact sequences
`0 → Zₙ → Cₙ → B_{n-1} → 0` and `0 → Bₙ → Zₙ → Hₙ → 0` stay exact after `- ⊗[ℤ] R`: every
`Zₙ`, `Bₙ` and `Cₙ ⧸ Zₙ ≅ B_{n-1}` is a subquotient of a torsion-free `ℤ`-module, hence flat.
Since `Hₙ = 0` and `H_{n-1} = 0` give `Bₙ = Zₙ` and `B_{n-1} = Z_{n-1}`, the kernels and images
in degree `n` still agree after base change.

The main steps are
* `range_bcMap_eq_ker_bcMap`: base change of an exact pair of `ℤ`-linear maps stays exact as soon
  as the cokernel is torsion-free (this is where flatness is used);
* `uctB_eq_uctZ_iff`: `Hₙ = 0` is exactness at `n`, i.e. `im d_{n+1} = ker dₙ`;
* `isTorsionFree_quotient_range_of_exact`: a quotient by the range of an exact map is a submodule
  of a torsion-free module, hence torsion-free.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.SRANGE

noncomputable section

-- Make the module structures on submodules and quotients the ones induced from the ambient
-- module, so that the various `Submodule` constructions are `defeq`-compatible.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-! ## Base change of `ℤ`-modules and of `ℤ`-linear maps -/

/-- `R` as a `ℤ`-module, in the form used by `ModuleCat.extendScalars`
(via `ModuleCat.restrictScalars`). -/
abbrev Rmod (R : Type) [CommRing R] : Type :=
  ↥((ModuleCat.restrictScalars (Int.castRingHom R)).obj (ModuleCat.of R R))

/-- Extension of scalars applied to a `ℤ`-module, as an object of `ModuleCat R`. -/
abbrev BC (R : Type) [CommRing R] (M : ModuleCat.{0} ℤ) : ModuleCat.{0} R :=
  (ModuleCat.extendScalars (Int.castRingHom R)).obj M

/-- The underlying `R`-linear map of the extension of scalars of a morphism of `ℤ`-modules. -/
def bcMap (R : Type) [CommRing R] {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) :
    ↥(BC R M) →ₗ[R] ↥(BC R N) :=
  @LinearMap.baseChange ℤ R ↥M ↥N _ _ ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra
    _ _ _ _ f.hom

/-- Base change is functorial. -/
lemma bcMap_comp_tf {R : Type} [CommRing R] {L M N : ModuleCat.{0} ℤ} (f : L ⟶ M) (g : M ⟶ N) :
    bcMap R (f ≫ g) = (bcMap R g).comp (bcMap R f) := by
  simp only [bcMap, ModuleCat.hom_comp, LinearMap.baseChange_comp]

/-- On the underlying functions, the base change of `f` is `LinearMap.lTensor`. -/
lemma bcMap_fun_eq_lTensor {R : Type} [CommRing R] {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) :
    ⇑(bcMap R f) = ⇑(LinearMap.lTensor (Rmod R) f.hom) := by
  rw [bcMap]
  exact @LinearMap.baseChange_eq_ltensor ℤ R ↥M ↥N _ _
    ((algebraMap R R).comp (Int.castRingHom R)).toAlgebra _ _ _ _ f.hom

/-- Base change preserves surjectivity. -/
lemma bcMap_surjective {R : Type} [CommRing R] {M N : ModuleCat.{0} ℤ} (f : M ⟶ N)
    (hf : Function.Surjective ⇑f.hom) : Function.Surjective ⇑(bcMap R f) := by
  have h1 : Function.Surjective ⇑(LinearMap.lTensor (Rmod R) f.hom) :=
    LinearMap.lTensor_surjective (Rmod R) hf
  rwa [← bcMap_fun_eq_lTensor] at h1

/-- **The differential of a base changed chain complex** is the base change of the differential. -/
theorem baseChange_d_eq_bcMap (R : Type) [CommRing R] (C : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i j : ℕ) : ModuleCat.Hom.hom ((baseChange R C).d i j) = bcMap R (C.d i j) := rfl

/-! ## The core linear algebra statement -/

/-- **Base change of an exact pair.**  If the range of `f` is the kernel of `g` and the cokernel of
`g` is torsion-free (hence flat over `ℤ`), then the same is true after `- ⊗[ℤ] R`. -/
theorem range_bcMap_eq_ker_bcMap (R : Type) [CommRing R] {A B C : ModuleCat.{0} ℤ}
    (f : A ⟶ B) (g : B ⟶ C) (h : LinearMap.range f.hom = LinearMap.ker g.hom)
    (hC : Module.IsTorsionFree ℤ (↥C ⧸ LinearMap.range g.hom)) :
    LinearMap.range (bcMap R f) = LinearMap.ker (bcMap R g) := by
  haveI htfC : Module.IsTorsionFree ℤ (↥C ⧸ LinearMap.range g.hom) := hC
  haveI hflatC : Module.Flat ℤ (↥C ⧸ LinearMap.range g.hom) := inferInstance
  -- bundle the range of `g` and the factorisation `g = q ≫ ι`
  let Q := ModuleCat.of ℤ ↥(LinearMap.range g.hom)
  let ι : Q ⟶ C := ModuleCat.ofHom (LinearMap.range g.hom).subtype
  let q : B ⟶ Q := ModuleCat.ofHom g.hom.rangeRestrict
  have hι : ι.hom = (LinearMap.range g.hom).subtype := rfl
  have hq : q.hom = g.hom.rangeRestrict := rfl
  have hfac : g = q ≫ ι := ModuleCat.hom_ext (by
    rw [ModuleCat.hom_comp, hq, hι, LinearMap.subtype_comp_rangeRestrict])
  -- the base change of the inclusion `range g ⊆ C` is injective
  have hinj : Function.Injective ⇑(bcMap R ι) := by
    have hlt : Function.Injective
        ⇑(LinearMap.lTensor (Rmod R) (LinearMap.range g.hom).subtype) :=
      LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range g.hom).mkQ
        (Submodule.mkQ_surjective _) (LinearMap.range g.hom).subtype
        (Submodule.subtype_injective _) (LinearMap.exact_subtype_mkQ _) (Rmod R)
    have hfun : ⇑(bcMap R ι)
        = ⇑(LinearMap.lTensor (Rmod R) (LinearMap.range g.hom).subtype) := by
      rw [bcMap_fun_eq_lTensor, hι]
    rwa [← hfun] at hlt
  -- hence the kernel of the base change of `g` is that of the surjection `B ↠ range g`
  have hker1 : LinearMap.ker (bcMap R g) = LinearMap.ker (bcMap R q) := by
    rw [hfac, bcMap_comp_tf, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hinj, Submodule.comap_bot]
  -- the kernel of the base change of the surjection `q` is the base change of its kernel
  have hsurjq : Function.Surjective ⇑q.hom := by
    intro y
    obtain ⟨a, ha⟩ := y.2
    exact ⟨a, Subtype.ext ha⟩
  have hkq : LinearMap.ker q.hom = LinearMap.ker g.hom := by rw [hq, LinearMap.ker_rangeRestrict]
  have hex2 : Function.Exact ⇑(bcMap R (ModuleCat.ofHom (LinearMap.ker q.hom).subtype))
      ⇑(bcMap R q) := by
    have h1 := lTensor_exact (Rmod R) (LinearMap.exact_subtype_ker_map q.hom) hsurjq
    have e1 : ⇑(bcMap R (ModuleCat.ofHom (LinearMap.ker q.hom).subtype))
        = ⇑(LinearMap.lTensor (Rmod R) (LinearMap.ker q.hom).subtype) := by
      rw [bcMap_fun_eq_lTensor]
      rfl
    have e2 : ⇑(bcMap R q) = ⇑(LinearMap.lTensor (Rmod R) q.hom) := bcMap_fun_eq_lTensor q
    rw [e1, e2]
    exact h1
  have hker2 : LinearMap.ker (bcMap R q)
      = LinearMap.range (bcMap R (ModuleCat.ofHom (LinearMap.ker q.hom).subtype)) :=
    LinearMap.exact_iff.mp hex2
  -- the range of the base change of `f` is that of the base change of `ker q ⊆ B`
  have hrg : LinearMap.range f.hom = LinearMap.ker q.hom := by rw [hkq, ← h]
  have hmem : ∀ a : ↥A, f.hom a ∈ LinearMap.ker q.hom := by
    intro a
    rw [← hrg]
    exact ⟨a, rfl⟩
  let f' : A ⟶ ModuleCat.of ℤ ↥(LinearMap.ker q.hom) :=
    ModuleCat.ofHom (f.hom.codRestrict (LinearMap.ker q.hom) hmem)
  have hf' : f = f' ≫ ModuleCat.ofHom (LinearMap.ker q.hom).subtype := ModuleCat.hom_ext (by
    rw [ModuleCat.hom_comp]
    ext a
    rfl)
  have hsurjf' : Function.Surjective ⇑f'.hom := by
    intro y
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (by rw [hrg]; exact y.2)
    exact ⟨a, Subtype.ext ha⟩
  have hrange : LinearMap.range (bcMap R f)
      = LinearMap.range (bcMap R (ModuleCat.ofHom (LinearMap.ker q.hom).subtype)) := by
    rw [hf', bcMap_comp_tf, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (bcMap_surjective _ hsurjf'), Submodule.map_top]
  rw [hker1, hker2, hrange]

/-! ## Homology, cycles and boundaries -/

/-- **Vanishing of `Hₙ` is exactness at `n`.** -/
theorem uctB_eq_uctZ_iff (S : Type) [CommRing S] (E : ChainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    CategoryTheory.Limits.IsZero (E.homology n) ↔
      LinearMap.range ((E.d (n+1) n).hom) = LinearMap.ker ((E.d n (n-1)).hom) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' (K := E) (i := n+1) (j := n) (k := n-1)
    (Work.Cohomology.down_prev n) (Work.Cohomology.down_next n)]
  exact ShortComplex.moduleCat_exact_iff_range_eq_ker _

/-- **A quotient by an exact range is torsion-free.**  If `range f = ker h` and `D` is torsion-free,
then so is `C ⧸ range f`. -/
theorem isTorsionFree_quotient_range_of_exact {B C D : Type*}
    [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] [AddCommGroup D] [Module ℤ D]
    (f : B →ₗ[ℤ] C) (h : C →ₗ[ℤ] D) (hex : LinearMap.range f = LinearMap.ker h)
    (hD : Module.IsTorsionFree ℤ D) :
    Module.IsTorsionFree ℤ (C ⧸ LinearMap.range f) := by
  haveI : Module.IsTorsionFree ℤ D := hD
  haveI htf : Module.IsTorsionFree ℤ ↥(LinearMap.range h) := inferInstance
  let e : (C ⧸ LinearMap.range f) ≃ₗ[ℤ] ↥(LinearMap.range h) :=
    Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker h) hex ≪≫ₗ LinearMap.quotKerEquivRange h
  refine Function.Injective.moduleIsTorsionFree (N := ↥(LinearMap.range h))
    (e : (C ⧸ LinearMap.range f) → ↥(LinearMap.range h)) e.injective ?_
  intro r y
  exact e.map_smul r y

/-! ## The main theorem -/

theorem isZero_homology_baseChange_of_torsionFree (R : Type) [CommRing R] {N : ℕ}
    (C : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (htf : ∀ i : ℕ, Module.IsTorsionFree ℤ (C.X i))
    (h : ∀ i : ℕ, i ≤ N → CategoryTheory.Limits.IsZero (C.homology i)) :
    ∀ i : ℕ, i ≤ N → CategoryTheory.Limits.IsZero ((Work.Pi6.SRANGE.baseChange R C).homology i) := by
  intro n hn
  rw [uctB_eq_uctZ_iff R (baseChange R C) n]
  simp only [baseChange_d_eq_bcMap]
  rcases Nat.eq_zero_or_pos n with hn0 | hpos
  · subst hn0
    have h00 : (C.d 0 0).hom = 0 := by
      rw [HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down])]
      rfl
    have hex0 : LinearMap.range ((C.d 1 0).hom) = LinearMap.ker ((C.d 0 0).hom) :=
      (uctB_eq_uctZ_iff ℤ C 0).mp (h 0 (Nat.zero_le N))
    haveI htf0 : Module.IsTorsionFree ℤ (↥(C.X 0) ⧸ LinearMap.range ((C.d 0 0).hom)) := by
      rw [h00, LinearMap.range_zero]
      have h' := isTorsionFree_quotient_range_of_exact (⊥ : Submodule ℤ ↥(C.X 0)).subtype
        LinearMap.id (by rw [Submodule.range_subtype, LinearMap.ker_id]) (htf 0)
      rwa [Submodule.range_subtype] at h'
    exact range_bcMap_eq_ker_bcMap R (C.d 1 0) (C.d 0 0) hex0 htf0
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hexn : LinearMap.range ((C.d ((m+1)+1) (m+1)).hom) = LinearMap.ker ((C.d (m+1) m).hom) :=
      (uctB_eq_uctZ_iff ℤ C (m+1)).mp (h (m+1) hn)
    have hexm : LinearMap.range ((C.d (m+1) m).hom) = LinearMap.ker ((C.d m (m-1)).hom) :=
      (uctB_eq_uctZ_iff ℤ C m).mp (h m (by omega))
    have htfq : Module.IsTorsionFree ℤ (↥(C.X m) ⧸ LinearMap.range ((C.d (m+1) m).hom)) :=
      isTorsionFree_quotient_range_of_exact ((C.d (m+1) m).hom) ((C.d m (m-1)).hom) hexm
        (htf (m-1))
    exact range_bcMap_eq_ker_bcMap R (C.d ((m+1)+1) (m+1)) (C.d (m+1) m) hexn htfq

end

end Work.Pi6.SRANGE
