import Mathlib
import Submission.Work.Cohomology.DualComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cycles, boundaries and homology of a `ℕ`-indexed chain complex of `ℤ`-modules

This file sets up the elementary linear algebra (splitting lemmas, cycles, boundaries) that the
proof of the dual universal coefficient theorem `Work.Cohomology.uctDual` needs.
-/

set_option backward.isDefEq.respectTransparency false

-- The module structure on a submodule (resp. a quotient by a submodule) of a `ℤ`-module is the one
-- induced from the ambient module, rather than the one coming from `AddCommGroup.toIntModule`:
-- this makes the various `Submodule`-constructions defeq-compatible.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Generic linear algebra -/

/-- An isomorphism of `R`-modules, as a linear equivalence of the underlying modules. -/
def uctIsoToLinearEquiv {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) : ↥M ≃ₗ[R] ↥N :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

lemma liftQ_add {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (f g : M →ₗ[R] N)
    (hf : p ≤ f.ker) (hg : p ≤ g.ker) (hfg : p ≤ (f + g).ker) :
    p.liftQ (f + g) hfg = p.liftQ f hf + p.liftQ g hg := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := p.mkQ_surjective x
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.add_apply]

lemma liftQ_smul {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (a : R) (f : M →ₗ[R] N)
    (hf : p ≤ f.ker) (haf : p ≤ (a • f).ker) :
    p.liftQ (a • f) haf = a • p.liftQ f hf := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := p.mkQ_surjective x
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]

lemma liftQ_eq_zero_imp {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (f : M →ₗ[R] N) (hf : p ≤ f.ker)
    (h : p.liftQ f hf = 0) : f = 0 := by
  ext x
  have h2 := congrArg (fun (g : M ⧸ p →ₗ[R] N) => g (p.mkQ x)) h
  simpa [Submodule.liftQ_apply, Submodule.mkQ_apply] using h2

lemma liftQ_zero {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (p : Submodule R M) (h : p ≤ (0 : M →ₗ[R] N).ker) :
    p.liftQ 0 h = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := p.mkQ_surjective x
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.zero_apply]

/-- If the range of `f : M →ₗ[R] N` is projective, the surjection `M → range f` splits, and hence
`M` retracts onto `ker f`. -/
theorem exists_retraction_ker {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (h : Module.Projective R ↥(LinearMap.range f)) :
    ∃ ρ : M →ₗ[R] ↥(LinearMap.ker f), ρ ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
  let k : M →ₗ[R] ↥(LinearMap.range f) := f.codRestrict (LinearMap.range f) (fun x => ⟨x, rfl⟩)
  have hk : Function.Surjective k := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := Module.projective_lifting_property k
    (LinearMap.id : ↥(LinearMap.range f) →ₗ[R] ↥(LinearMap.range f)) hk
  have hik : ∀ x : M, f (i (k x)) = f x := by
    intro x
    have h2 := LinearMap.congr_fun hi (k x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    have h3 := congrArg Subtype.val h2
    simpa [k, LinearMap.codRestrict_apply] using h3
  have hmem : ∀ x : M, ((LinearMap.id : M →ₗ[R] M) - i.comp k) x ∈ LinearMap.ker f := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hik x, sub_self]
  refine ⟨LinearMap.codRestrict (LinearMap.ker f) ((LinearMap.id : M →ₗ[R] M) - i.comp k) hmem, ?_⟩
  refine LinearMap.ext (fun x => Subtype.ext ?_)
  change ((LinearMap.id : M →ₗ[R] M) - i.comp k) (x : M) = (x : M)
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  have hx : k (x : M) = 0 := by
    refine Subtype.ext ?_
    rw [LinearMap.codRestrict_apply, LinearMap.mem_ker.mp x.2]
    rfl
  rw [hx, map_zero, sub_zero]

/-- If `M ⧸ p` is projective, the quotient map `M → M ⧸ p` splits, and hence `M` retracts onto
`p`. -/
theorem exists_retraction_onto_of_projective_quotient {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] (p : Submodule R M)
    (h : Module.Projective R (M ⧸ p)) :
    ∃ r : M →ₗ[R] ↥p, r ∘ₗ p.subtype = LinearMap.id := by
  obtain ⟨i, hi⟩ := Module.projective_lifting_property p.mkQ (LinearMap.id : M ⧸ p →ₗ[R] M ⧸ p)
    p.mkQ_surjective
  have hmem : ∀ x : M, ((LinearMap.id : M →ₗ[R] M) - i.comp p.mkQ) x ∈ p := by
    intro x
    have h2 : p.mkQ (i (p.mkQ x)) = p.mkQ x := by
      rw [← LinearMap.comp_apply, LinearMap.congr_fun hi (p.mkQ x), LinearMap.id_apply]
    have h1 : p.mkQ (((LinearMap.id : M →ₗ[R] M) - i.comp p.mkQ) x) = 0 := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h2, sub_self]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h1
    exact h1
  refine ⟨(LinearMap.codRestrict p ((LinearMap.id : M →ₗ[R] M) - i.comp p.mkQ) hmem), ?_⟩
  refine LinearMap.ext (fun x => Subtype.ext ?_)
  change ((LinearMap.id : M →ₗ[R] M) - i.comp p.mkQ) (x : M) = (x : M)
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  have hx : p.mkQ (x : M) = 0 := by
    rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero p).mpr x.2
  rw [hx, map_zero, sub_zero]

/-! ## The shape of the complexes -/

lemma up_next (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 := by
  rw [ComplexShape.next_eq' _ (rfl : n + 1 = n + 1)]

lemma up_prev (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  rcases n with _ | n
  · rw [ComplexShape.prev_eq_self' _ _ (fun k hk => Nat.succ_ne_zero k hk)]
  · rw [ComplexShape.prev_eq' _ (rfl : n + 1 = n + 1)]
    exact (Nat.succ_sub_one n).symm

lemma down_next (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | n
  · rw [ComplexShape.next_eq_self' _ _ (fun k hk => Nat.succ_ne_zero k hk)]
  · rw [ComplexShape.next_eq' _ (rfl : n + 1 = n + 1)]
    exact (Nat.succ_sub_one n).symm

lemma down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 := by
  rw [ComplexShape.prev_eq' _ (rfl : n + 1 = n + 1)]

/-! ## Cycles and boundaries -/

universe u

variable (E : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ)

/-- The `n`-cycles of `E`. -/
def uctZ (n : ℕ) : Submodule ℤ ↥(E.X n) := LinearMap.ker (E.d n (n - 1)).hom

/-- The `n`-boundaries of `E`. -/
def uctB (n : ℕ) : Submodule ℤ ↥(E.X n) := LinearMap.range (E.d (n + 1) n).hom

/-- The `n`-boundaries, as a submodule of the `n`-cycles. -/
def uctH (n : ℕ) : Submodule ℤ ↥(uctZ E n) :=
  LinearMap.range (((E.d (n + 1) n).hom).codRestrict (uctZ E n) (fun x => by
    show (E.d n (n - 1)).hom ((E.d (n + 1) n).hom x) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 1) n (n - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x))

/-- The image of the `n`-th differential, as a submodule of `E_{n-1}`. -/
def uctR (n : ℕ) : Submodule ℤ ↥(E.X (n - 1)) := LinearMap.range (E.d n (n - 1)).hom

lemma uctR_apply (n : ℕ) : uctR E (n + 1) = uctB E n := rfl

lemma subsingleton_bot {M : Type*} [AddCommGroup M] [Module ℤ M] :
    Subsingleton ↥(⊥ : Submodule ℤ M) :=
  ⟨fun a b => Subtype.ext (by
    have ha : (a : M) = 0 := a.2
    have hb : (b : M) = 0 := b.2
    rw [ha, hb])⟩

/-- The zero submodule is projective. -/
lemma projective_bot {M : Type*} [AddCommGroup M] [Module ℤ M] :
    Module.Projective ℤ ↥(⊥ : Submodule ℤ M) := by
  haveI := subsingleton_bot (M := M)
  exact Module.Projective.of_free (R := ℤ) (P := ↥(⊥ : Submodule ℤ M))

/-- `M` retracts onto the zero submodule. -/
lemma exists_retraction_bot {M : Type*} [AddCommGroup M] [Module ℤ M] :
    ∃ r : M →ₗ[ℤ] ↥(⊥ : Submodule ℤ M),
      r ∘ₗ (⊥ : Submodule ℤ M).subtype = LinearMap.id := by
  haveI := subsingleton_bot (M := M)
  exact ⟨0, by ext⟩

lemma uctR_zero : uctR E 0 = ⊥ := by
  rw [uctR, show E.d 0 (0 - 1) = 0 from
    HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down]), ModuleCat.hom_zero,
    LinearMap.range_zero]

lemma uctB_le_uctZ (n : ℕ) : uctB E n ≤ uctZ E n := by
  rintro x ⟨y, rfl⟩
  show (E.d n (n - 1)).hom ((E.d (n + 1) n).hom y) = 0
  have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 1) n (n - 1))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h y

lemma uctH_eq_comap (n : ℕ) : uctH E n = (uctB E n).comap (uctZ E n).subtype := by
  rw [uctH, uctB, LinearMap.range_codRestrict]

lemma mem_uctH (n : ℕ) (x : ↥(uctZ E n)) : x ∈ uctH E n ↔ (x : ↥(E.X n)) ∈ uctB E n := by
  rw [uctH]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    show (E.d (n + 1) n).hom y = (x : ↥(E.X n))
    exact hy

lemma uctZ_zero : uctZ E 0 = ⊤ := by
  have h : E.d 0 (0 - 1) = 0 := HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down])
  rw [uctZ, h]
  exact LinearMap.ker_zero

/-! ## The dual complex -/

/-- The additive equivalence underlying a `ℤ`-linear functional, used to view an element of
`(dualComplex ℤ E).X n` as a functional on `Eₙ`. -/
def dval (n : ℕ) (φ : ↥((dualComplex ℤ E).X n)) : (↥(E.X n) →ₗ[ℤ] ℤ) := φ

lemma uct_d_dual (n : ℕ) : (dualComplex ℤ E).d n (n + 1) = dualDiff ℤ E n :=
  CochainComplex.of_d (dualObj ℤ E) (dualDiff ℤ E) n

lemma uct_d_apply (n : ℕ) (φ : ↥((dualComplex ℤ E).X n)) :
    ((dualComplex ℤ E).d n (n + 1)).hom φ = (dval E n φ).comp (E.d (n + 1) n).hom := by
  rw [show (dualComplex ℤ E).d n (n + 1) = dualDiff ℤ E n from
    CochainComplex.of_d (dualObj ℤ E) (dualDiff ℤ E) n]
  rfl

lemma uct_d_pred_apply_succ (m : ℕ) (y : ↥((dualComplex ℤ E).X m)) :
    ((dualComplex ℤ E).d m (m + 1)).hom y = (dval E m y).comp (E.d (m + 1) m).hom := by
  rw [show (dualComplex ℤ E).d m (m + 1) = dualDiff ℤ E m from
    CochainComplex.of_d (dualObj ℤ E) (dualDiff ℤ E) m]
  rfl

lemma uct_d_pred_apply (n : ℕ) (y : ↥((dualComplex ℤ E).X (n - 1))) :
    ((dualComplex ℤ E).d (n - 1) n).hom y = (dval E (n - 1) y).comp (E.d n (n - 1)).hom := by
  rcases n with _ | m
  · rw [HomologicalComplex.shape (dualComplex ℤ E) 0 0 (by simp [ComplexShape.up]),
      HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down])]
    simp [ModuleCat.hom_zero]
  · show ((dualComplex ℤ E).d m (m + 1)).hom y = (dval E m y).comp (E.d (m + 1) m).hom
    exact uct_d_pred_apply_succ E m y

/-- The differential of the dual complex, as a linear map (used to identify the "image of `dᵀ`"
inside the cocycles of the dual complex). -/
def uctPre (n : ℕ) : Submodule ℤ ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) :=
  LinearMap.range
    (((dualComplex ℤ E).d (n - 1) n).hom.codRestrict
      (LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) (fun x => by
        rw [LinearMap.mem_ker]
        have h := congrArg ModuleCat.Hom.hom
          (HomologicalComplex.d_comp_d (dualComplex ℤ E) (n - 1) n (n + 1))
        simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact LinearMap.congr_fun h x))

/-! ## The homology of `E` and the homology of the dual complex -/

/-- The homology of `E` in degree `n` is the quotient `Zₙ ⧸ Bₙ`. -/
theorem homology_iso_H (n : ℕ) :
    Nonempty (E.homology n ≅ ModuleCat.of ℤ (↥(uctZ E n) ⧸ uctH E n)) :=
  ⟨(E.homologyIsoSc' (n + 1) n (n - 1) (down_prev n) (down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (E.sc' (n + 1) n (n - 1))⟩

/-- The cohomology of the dual complex in degree `n` is `ker dⁿ ⧸ im dⁿ⁻¹`. -/
theorem homology_dual_iso (n : ℕ) :
    Nonempty ((dualComplex ℤ E).homology n ≅
      ModuleCat.of ℤ (↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) ⧸ uctPre E n)) :=
  ⟨((dualComplex ℤ E).homologyIsoSc' (n - 1) n (n + 1) (up_prev n) (up_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso ((dualComplex ℤ E).sc' (n - 1) n (n + 1))⟩

end

end Work.Cohomology
