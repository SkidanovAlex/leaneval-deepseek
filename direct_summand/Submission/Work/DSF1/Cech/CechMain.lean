import Mathlib
import Submission.Work.DSF1.Cech.CechDefs
import Submission.Work.DSF1.Cech.CoaugCycle
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.basicOpen_localization_facts

/-!
# Assembly of the affine Čech exactness (`cechSpec_quasiIso`)

Let `R` be a commutative ring, `f : ι → R` a finite family generating the unit ideal,
`X = Spec R`, `U i = D (f i)`, `P` the structure sheaf of `X` as a presheaf of
`R`-modules and `𝒞 = cechSpec f` its Čech complex along `U`.

The coaugmentation `coaug0 f : R ⟶ 𝒞⁰` is a morphism of complexes
(`coaug0_comp_d`), hence defines a chain map `coaugMap f` from the complex
`R[0] = single₀ R`.  This file proves that `coaugMap f` is a quasi-isomorphism,
assuming the *localized* statements for the complexes `𝒞ᵢ` (which are supplied by
`UnitCase`/`isIsoDeletion_Qi`) and the two "clearing denominators" lemmas
(`exists_pow_smul_mem_range_loc`, `eq_zero_of_loc_eq_zero`) for the comparison maps
`loc f i : 𝒞 ⟶ 𝒞ᵢ`, together with the two degree zero statements
`coaug0_injective` and `coaug0_surjective_ker`.

The proof of the quasi-isomorphism has two halves:

* in positive degrees, `𝒞` is exact; this is deduced from the exactness of the
  localizations `𝒞ᵢ` by "clearing denominators" and the partition of unity
  (`exists_d_eq_of_localized`);
* in degree zero, `coaugMap f` induces `H⁰(𝒞) ≅ R`, which is reduced to the
  injectivity of `coaug0 f` and its surjectivity onto the cycles.

Finally the result is transported from `ℕ`-graded to `ℤ`-graded complexes using
`HomologicalComplex.extendMap` and `HomologicalComplex.extendSingleIso`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {R : Type u} [CommRing R] {ι : Type u}

/-! ## The coaugmentation is a chain map -/

/-- The coaugmentation `R ⟶ 𝒞⁰` of the Čech complex is a cycle. -/
theorem coaug0_comp_d (f : ι → R) : coaug0 f ≫ (cechSpec f).d 0 1 = 0 := by
  rw [← unitTop_comp_coaugQ f, Category.assoc,
    show coaugQ f ≫ (cechSpec f).d 0 1 = 0 from CoaugCycle (basicOpens f) (specPresheaf R)]
  simp

/-- The coaugmentation as a chain map `R[0] ⟶ 𝒞` (`ℕ`-graded). -/
noncomputable def coaugMap (f : ι → R) :
    (CochainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶ cechSpec f :=
  (CochainComplex.fromSingle₀Equiv (cechSpec f) (ModuleCat.of R R)).symm
    ⟨coaug0 f, coaug0_comp_d f⟩

lemma coaugMap_f_zero (f : ι → R) : (coaugMap f).f 0 = coaug0 f := by
  rw [coaugMap]
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-! ## Exactness in positive degrees -/

/-- Exactness of an `ℕ`-graded cochain complex of modules in positive degrees is the
elementwise statement that every cycle of positive degree is a boundary. -/
theorem exactAt_succ_iff (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.ExactAt (n + 1) ↔ ∀ s : K.X (n + 1), (K.d (n + 1) (n + 2)).hom s = 0 →
      ∃ t : K.X n, (K.d n (n + 1)).hom t = s := by
  have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (by rfl)
  have hn : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
    ComplexShape.next_eq' (c := ComplexShape.up ℕ) (by rfl)
  rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) hp hn,
    ShortComplex.moduleCat_exact_iff]
  rfl

/-! ## Descent of exactness along the localized complexes -/

/-- **Descent of exactness along `locᵢ`.**  If `locᵢ s` is a boundary in `𝒞ᵢ`, then
some `f i ^ k • s` is a boundary in `𝒞`. -/
theorem exists_pow_smul_mem_range_d (f : ι → R) (i : ι) (n : ℕ)
    (s : (cechSpec f).X (n + 1))
    (H : ∃ t : (cechSpecQi f i).X n,
      ((cechSpecQi f i).d n (n + 1)).hom t = (loc f i).f (n + 1) s)
    (hC1 : ∀ (m : ℕ) (z : (cechSpecQi f i).X m), ∃ (k : ℕ) (t : (cechSpec f).X m),
      (loc f i).f m t = f i ^ k • z)
    (hC2 : ∀ (m : ℕ) (t : (cechSpec f).X m), (loc f i).f m t = 0 →
      ∃ k : ℕ, f i ^ k • t = 0) :
    ∃ (k : ℕ) (t : (cechSpec f).X n), ((cechSpec f).d n (n + 1)).hom t = f i ^ k • s := by
  obtain ⟨t_i, ht_i⟩ := H
  obtain ⟨k, t, ht⟩ := hC1 n t_i
  have hcomm := (loc f i).comm' n (n + 1) (by simp)
  have h1 : (loc f i).f (n + 1) (((cechSpec f).d n (n + 1)).hom t) =
      f i ^ k • ((loc f i).f (n + 1) s) := by
    have hh : ((loc f i).f (n + 1)) (((cechSpec f).d n (n + 1)) t) =
        ((cechSpecQi f i).d n (n + 1)) ((loc f i).f n t) := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) t
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
    rw [hh, ht, map_smul, ht_i]
  have h2 : (loc f i).f (n + 1)
      ((((cechSpec f).d n (n + 1)).hom t) - f i ^ k • s) = 0 := by
    rw [map_sub, h1, map_smul, sub_self]
  obtain ⟨l, hl⟩ := hC2 (n + 1) _ h2
  refine ⟨k + l, f i ^ l • t, ?_⟩
  have h3 : f i ^ l • ((((cechSpec f).d n (n + 1)).hom t) - f i ^ k • s) = 0 := hl
  have h5 : f i ^ l • (((cechSpec f).d n (n + 1)).hom t) = f i ^ (l + k) • s := by
    have hh := h3
    rw [smul_sub, smul_smul, ← pow_add] at hh
    exact sub_eq_zero.mp hh
  rw [map_smul, h5, Nat.add_comm l k]

/-- **Exactness in positive degrees, deduced from the localizations.**  If each `𝒞ᵢ` is
exact in positive degrees, then so is `𝒞`: this is "clearing denominators" together
with the partition of unity. -/
theorem exact_of_localized (f : ι → R) (h : Ideal.span (Set.range f) = ⊤)
    (H : ∀ i : ι, ∀ n : ℕ, ∀ s : (cechSpecQi f i).X (n + 1),
      ((cechSpecQi f i).d (n + 1) (n + 2)).hom s = 0 →
        ∃ t : (cechSpecQi f i).X n, ((cechSpecQi f i).d n (n + 1)).hom t = s)
    (hC1 : ∀ i : ι, ∀ (m : ℕ) (z : (cechSpecQi f i).X m), ∃ (k : ℕ) (t : (cechSpec f).X m),
      (loc f i).f m t = f i ^ k • z)
    (hC2 : ∀ i : ι, ∀ (m : ℕ) (t : (cechSpec f).X m), (loc f i).f m t = 0 →
      ∃ k : ℕ, f i ^ k • t = 0) :
    ∀ n : ℕ, ∀ s : (cechSpec f).X (n + 1), ((cechSpec f).d (n + 1) (n + 2)).hom s = 0 →
      ∃ t : (cechSpec f).X n, ((cechSpec f).d n (n + 1)).hom t = s := by
  intro n s hs
  refine exists_d_eq_of_localized f h n s (fun i => ?_)
  have hcomm := (loc f i).comm' (n + 1) (n + 2) (by simp)
  have hcyc : ((cechSpecQi f i).d (n + 1) (n + 2)).hom ((loc f i).f (n + 1) s) = 0 := by
    have hh : ((loc f i).f (n + 2)) (((cechSpec f).d (n + 1) (n + 2)) s) =
        ((cechSpecQi f i).d (n + 1) (n + 2)) ((loc f i).f (n + 1) s) := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) s
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
    rw [← hh, hs, map_zero]
  obtain ⟨tᵢ, htᵢ⟩ := H i n _ hcyc
  exact exists_pow_smul_mem_range_d f i n s ⟨tᵢ, htᵢ⟩ (hC1 i) (hC2 i)

/-! ## The degree zero part -/

/-- If the coaugmentation is injective and surjective onto the cycles in degree zero,
then it induces an isomorphism on `H⁰`. -/
theorem isIso_homologyMap_coaugMap_zero (f : ι → R)
    (h1 : ∀ q : R, (coaug0 f).hom q = 0 → q = 0)
    (h2 : ∀ s : (cechSpec f).X 0, ((cechSpec f).d 0 1).hom s = 0 →
      ∃ q : R, (coaug0 f).hom q = s) :
    IsIso (HomologicalComplex.homologyMap (coaugMap f) 0) := by
  have hhom : HomologicalComplex.homologyMap (coaugMap f) 0 =
      (CochainComplex.isoHomologyπ₀ ((CochainComplex.single₀ (ModuleCat.{u} R)).obj
          (ModuleCat.of R R))).inv ≫ HomologicalComplex.cyclesMap (coaugMap f) 0 ≫
        (CochainComplex.isoHomologyπ₀ (cechSpec f)).hom := by
    rw [← cancel_mono (CochainComplex.isoHomologyπ₀ (cechSpec f)).inv]
    rw [CochainComplex.isoHomologyπ₀_inv_naturality]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  set g : ModuleCat.of R R ⟶ (cechSpec f).cycles 0 :=
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (ModuleCat.of R R)).inv ≫
      HomologicalComplex.cyclesMap (coaugMap f) 0 with hg
  have hstep : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
      (ModuleCat.of R R)).inv ≫
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R R)).iCycles 0 =
      𝟙 (ModuleCat.of R R) := by
    rw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles, CochainComplex.single₀ObjXSelf]
    rfl
  have hgi : g ≫ (cechSpec f).iCycles 0 = coaug0 f := by
    rw [hg, Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, hstep,
      Category.id_comp, coaugMap_f_zero]
  have hcyc : HomologicalComplex.cyclesMap (coaugMap f) 0 =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0
        (ModuleCat.of R R)).hom ≫ g := by
    rw [hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hinj : Function.Injective g.hom := by
    intro x y hxy
    have hx : ((cechSpec f).iCycles 0).hom (g.hom x) = (coaug0 f).hom x := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgi) x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
    have hy : ((cechSpec f).iCycles 0).hom (g.hom y) = (coaug0 f).hom y := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgi) y
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
    have hsub : (coaug0 f).hom (x - y) = 0 := by
      rw [map_sub, ← hx, ← hy, hxy, sub_self]
    exact sub_eq_zero.mp (h1 (x - y) hsub)
  have hsurj : Function.Surjective g.hom := by
    intro y
    have hcyc' : ((cechSpec f).d 0 1).hom (((cechSpec f).iCycles 0).hom y) = 0 := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.iCycles_d (K := cechSpec f) (i := 0) (j := 1))) y
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    obtain ⟨q, hq⟩ := h2 (((cechSpec f).iCycles 0).hom y) hcyc'
    refine ⟨q, ?_⟩
    have hmono : Function.Injective ((cechSpec f).iCycles 0).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hmono
    rw [← hq]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hgi) q
  haveI : IsIso g := by
    rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective]
    exact ⟨hinj, hsurj⟩
  rw [hhom, hcyc]
  infer_instance

/-! ## The quasi-isomorphism -/

/-- **The coaugmentation is a quasi-isomorphism.**  The hypothesis `hexact` is the
exactness in positive degrees of `𝒞` (obtained from the localized complexes by clearing
denominators and the partition of unity), and `h1`, `h2` are the two degree zero
statements. -/
theorem quasiIso_coaugMap (f : ι → R)
    (hexact : ∀ n : ℕ, ∀ s : (cechSpec f).X (n + 1), ((cechSpec f).d (n + 1) (n + 2)).hom s = 0 →
      ∃ t : (cechSpec f).X n, ((cechSpec f).d n (n + 1)).hom t = s)
    (h1 : ∀ q : R, (coaug0 f).hom q = 0 → q = 0)
    (h2 : ∀ s : (cechSpec f).X 0, ((cechSpec f).d 0 1).hom s = 0 →
      ∃ q : R, (coaug0 f).hom q = s) :
    QuasiIso (coaugMap f) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_homologyMap_coaugMap_zero f h1 h2
  | succ n =>
    rw [quasiIsoAt_iff_exactAt (coaugMap f) (n + 1)
        (CochainComplex.exactAt_succ_single_obj (ModuleCat.of R R) n),
      exactAt_succ_iff (cechSpec f) n]
    exact hexact n

/-! ## Transport to `ℤ`-graded complexes -/

/-- The chain map `R[0] ⟶ cechZ` obtained from the coaugmentation, in the `ℤ`-graded
world: it is the composite of the identification of the extension of `R[0]` with the
`ℤ`-graded `R[0]` and the extension of `coaugMap f`. -/
noncomputable def cechZCC (f : ι → R) :
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R R) ⟶
      (cechSpec f).extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpNat) (ModuleCat.of R R)
    0 0 rfl).inv ≫ HomologicalComplex.extendMap (coaugMap f) ComplexShape.embeddingUpNat

/-- The `ℤ`-graded chain map `cechZCC f` is a quasi-isomorphism as soon as `coaugMap f`
is: it is the composite of the isomorphism `HomologicalComplex.extendSingleIso` with the
extension of `coaugMap f`. -/
theorem quasiIso_cechZCC (f : ι → R) (h : QuasiIso (coaugMap f)) : QuasiIso (cechZCC f) := by
  haveI := h
  rw [cechZCC]
  haveI : QuasiIso (HomologicalComplex.extendMap (coaugMap f) ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff (coaugMap f) ComplexShape.embeddingUpNat).2 h
  infer_instance

end Work.DSF1.Cech
