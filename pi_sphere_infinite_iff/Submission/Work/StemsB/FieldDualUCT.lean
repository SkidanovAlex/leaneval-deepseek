import Mathlib
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Cohomology.DualComplex

/-!
# The universal coefficient theorem over a field: `Hⁿ(Hom(C,F)) ≅ Hom(Hₙ(C),F)`

For a **field** `F` and a `ℕ`-indexed chain complex `C` of `F`-vector spaces, the cohomology of the
dual complex `Hom_F(C,F)` is the `F`-dual of the homology:

  `fieldDualUCT : Hⁿ(dualComplex F C) ≅ Hom_F(Hₙ(C), F)`.

Unlike the integral universal coefficient theorem (`Work.Cohomology.uctDual`), no projectivity or
finiteness hypothesis is needed: over a field every module is free, every surjection splits, and
`Hom_F(-,F)` is an exact functor.  This is the tool that turns a *homological* computation over `ℚ`
into a computation of *cohomology* over `ℚ`, which is what subproject SERRE's `C2` odd step needs
from the Wang sequence over a sphere.

The proof is the classical one, transcribed from `Work.Cohomology.uctDual` (the `ℤ` case):

* the comparison map `fdPsi : ker(dⁿ) →ₗ ((Zₙ ⧸ Bₙ) →ₗ F)`, `f ↦ (z ↦ f z)`, has kernel the image
  of the transposed differential `dⁿ⁻¹` and is surjective;
* both facts reduce, over a field, to the splitting of subspace inclusions
  (`exists_retraction_subspace_field`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

namespace Work.StemsB

noncomputable section

/-! ## Splitting lemma over a field -/

/-- Over a field every subspace is a direct summand: the inclusion `p ↪ M` admits a retraction. -/
theorem exists_retraction_subspace_field (F : Type) [Field F] {M : Type*} [AddCommGroup M]
    [Module F M] (p : Submodule F M) :
    ∃ r : M →ₗ[F] ↥p, r ∘ₗ p.subtype = LinearMap.id :=
  Work.Cohomology.exists_retraction_onto_of_projective_quotient p
    (inferInstance : Module.Projective F (M ⧸ p))

/-- The same splitting stated through `Module.Projective` of the range of a linear map. -/
theorem exists_retraction_ker_field (F : Type) [Field F] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] [Module F M] [Module F N] (f : M →ₗ[F] N) :
    ∃ ρ : M →ₗ[F] ↥(LinearMap.ker f), ρ ∘ₗ (LinearMap.ker f).subtype = LinearMap.id :=
  Work.Cohomology.exists_retraction_ker f
    (inferInstance : Module.Projective F ↥(LinearMap.range f))

/-! ## Cycles, boundaries, homology -/

variable (F : Type) [Field F]

/-- The `n`-cycles of a chain complex of `F`-vector spaces. -/
def fdZ (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) : Submodule F ↥(E.X n) :=
  LinearMap.ker (E.d n (n - 1)).hom

/-- The `n`-boundaries of a chain complex of `F`-vector spaces. -/
def fdB (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) : Submodule F ↥(E.X n) :=
  LinearMap.range (E.d (n + 1) n).hom

/-- The `n`-boundaries, as a submodule of the `n`-cycles. -/
def fdH (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) : Submodule F ↥(fdZ F E n) :=
  LinearMap.range (((E.d (n + 1) n).hom).codRestrict (fdZ F E n) (fun x => by
    show (E.d n (n - 1)).hom ((E.d (n + 1) n).hom x) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 1) n (n - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x))

/-- The image of the `n`-th differential, as a submodule of `E_{n-1}`. -/
def fdR (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) : Submodule F ↥(E.X (n - 1)) :=
  LinearMap.range (E.d n (n - 1)).hom

lemma fdB_le_fdZ (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) : fdB F E n ≤ fdZ F E n := by
  rintro x ⟨y, rfl⟩
  show (E.d n (n - 1)).hom ((E.d (n + 1) n).hom y) = 0
  have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 1) n (n - 1))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h y

lemma fdH_eq_comap (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    fdH F E n = (fdB F E n).comap (fdZ F E n).subtype := by
  rw [fdH, fdB, LinearMap.range_codRestrict]

lemma mem_fdH (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) (x : ↥(fdZ F E n)) :
    x ∈ fdH F E n ↔ (x : ↥(E.X n)) ∈ fdB F E n := by
  rw [fdH, fdB]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    show (E.d (n + 1) n).hom y = (x : ↥(E.X n))
    exact hy

lemma fdZ_zero (E : ChainComplex (ModuleCat.{0,0} F) ℕ) : fdZ F E 0 = ⊤ := by
  have h : E.d 0 (0 - 1) = 0 := HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down])
  rw [fdZ, h]
  exact LinearMap.ker_zero

lemma fdR_zero (E : ChainComplex (ModuleCat.{0,0} F) ℕ) : fdR F E 0 = ⊥ := by
  rw [fdR, show E.d 0 (0 - 1) = 0 from
    HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down]), ModuleCat.hom_zero,
    LinearMap.range_zero]

/-- The homology of a chain complex of `F`-vector spaces is the quotient of cycles by
boundaries. -/
theorem homology_iso_H_field (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    Nonempty (E.homology n ≅ ModuleCat.of F (↥(fdZ F E n) ⧸ fdH F E n)) :=
  ⟨(E.homologyIsoSc' (n + 1) n (n - 1)
      (Work.Cohomology.down_prev n) (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (E.sc' (n + 1) n (n - 1))⟩

/-! ## The dual complex -/

/-- An element of the degree `n` part of the dual complex, viewed as a functional on `Eₙ`. -/
def fdVal (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (φ : ↥((dualComplex F E).X n)) : (↥(E.X n) →ₗ[F] F) := φ

lemma fd_d_dual (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    (dualComplex F E).d n (n + 1) = dualDiff F E n :=
  CochainComplex.of_d (dualObj F E) (dualDiff F E) n

lemma fd_d_apply (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (φ : ↥((dualComplex F E).X n)) :
    ((dualComplex F E).d n (n + 1)).hom φ = (fdVal F E n φ).comp (E.d (n + 1) n).hom := by
  rw [show (dualComplex F E).d n (n + 1) = dualDiff F E n from fd_d_dual F E n]
  rfl

lemma fd_d_pred_apply_succ (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (m : ℕ)
    (y : ↥((dualComplex F E).X m)) :
    ((dualComplex F E).d m (m + 1)).hom y = (fdVal F E m y).comp (E.d (m + 1) m).hom :=
  fd_d_apply F E m y

lemma fd_d_pred_apply (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (y : ↥((dualComplex F E).X (n - 1))) :
    ((dualComplex F E).d (n - 1) n).hom y = (fdVal F E (n - 1) y).comp (E.d n (n - 1)).hom := by
  rcases n with _ | m
  · rw [HomologicalComplex.shape (dualComplex F E) 0 0 (by simp [ComplexShape.up]),
      HomologicalComplex.shape E 0 0 (by simp [ComplexShape.down])]
    simp [ModuleCat.hom_zero]
  · show ((dualComplex F E).d m (m + 1)).hom y
      = (fdVal F E m y).comp (E.d (m + 1) m).hom
    exact fd_d_pred_apply_succ F E m y

/-- The "coboundaries" of the dual complex, as a submodule of the cocycles. -/
def fdPre (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    Submodule F ↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom) :=
  LinearMap.range
    (((dualComplex F E).d (n - 1) n).hom.codRestrict
      (LinearMap.ker ((dualComplex F E).d n (n + 1)).hom) (fun x => by
        rw [LinearMap.mem_ker]
        have h := congrArg ModuleCat.Hom.hom
          (HomologicalComplex.d_comp_d (dualComplex F E) (n - 1) n (n + 1))
        simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
        exact LinearMap.congr_fun h x))

/-- The cohomology of the dual complex as cocycles modulo coboundaries. -/
theorem homology_dual_iso_field (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    Nonempty ((dualComplex F E).homology n ≅
      ModuleCat.of F (↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom) ⧸ fdPre F E n)) :=
  ⟨((dualComplex F E).homologyIsoSc' (n - 1) n (n + 1)
      (Work.Cohomology.up_prev n) (Work.Cohomology.up_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso ((dualComplex F E).sc' (n - 1) n (n + 1))⟩

/-! ## The comparison map `Ψ` -/

lemma fdD_kill (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (f : ↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom)) :
    fdH F E n ≤ LinearMap.ker ((fdVal F E n f.1).comp (fdZ F E n).subtype) := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  change (fdVal F E n f.1) ↑x = 0
  have hx' : (↑x : ↥(E.X n)) ∈ fdB F E n := (mem_fdH F E n x).1 hx
  obtain ⟨y, hy⟩ := hx'
  have h2 : (fdVal F E n f.1) ((E.d (n + 1) n).hom y) = 0 := by
    have hf : ((dualComplex F E).d n (n + 1)).hom f.1 = 0 := LinearMap.mem_ker.mp f.2
    rw [fd_d_apply F E n] at hf
    exact LinearMap.congr_fun hf y
  rw [show (↑x : ↥(E.X n)) = (E.d (n + 1) n).hom y from hy.symm]
  exact h2

/-- **The comparison map** from the cocycles of the dual complex to the dual of the homology. -/
def fdPsi (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    (↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom)) →ₗ[F]
      ((↥(fdZ F E n) ⧸ fdH F E n) →ₗ[F] F) where
  toFun f := (fdH F E n).liftQ ((fdVal F E n f.1).comp (fdZ F E n).subtype) (fdD_kill F E n f)
  map_add' f g := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (fdH F E n).mkQ_surjective w
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, fdVal,
      Submodule.coe_add, Submodule.subtype_apply]
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (fdH F E n).mkQ_surjective w
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, fdVal,
      Submodule.coe_smul, Submodule.subtype_apply, RingHom.id_apply]
    rfl

lemma fdPsi_apply (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (f : ↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom)) (x : ↥(fdZ F E n)) :
    fdPsi F E n f ((fdH F E n).mkQ x) = (fdVal F E n f.1) x := by
  show (fdH F E n).liftQ ((fdVal F E n f.1).comp (fdZ F E n).subtype) _ ((fdH F E n).mkQ x)
    = (fdVal F E n f.1) x
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply]
  rfl

/-- `Ψ` is surjective: over a field every functional on the cycles extends to the whole module. -/
theorem fdPsi_surj (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (hZ : ∃ ρ : ↥(E.X n) →ₗ[F] ↥(fdZ F E n),
      ρ ∘ₗ (fdZ F E n).subtype = LinearMap.id) :
    Function.Surjective (fdPsi F E n) := by
  obtain ⟨ρ, hρ⟩ := hZ
  intro g
  let f0 : ↥((dualComplex F E).X n) := g.comp ((fdH F E n).mkQ.comp ρ)
  have hf0 : ((dualComplex F E).d n (n + 1)).hom f0 = 0 := by
    rw [fd_d_apply F E n]
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    show g ((fdH F E n).mkQ (ρ ((E.d (n + 1) n).hom y))) = 0
    have hy : ((E.d (n + 1) n).hom y : ↥(E.X n)) ∈ fdB F E n := ⟨y, rfl⟩
    have hz : ρ ((E.d (n + 1) n).hom y) = ⟨(E.d (n + 1) n).hom y, fdB_le_fdZ F E n hy⟩ := by
      have h := congrArg (fun (φ : ↥(fdZ F E n) →ₗ[F] ↥(fdZ F E n)) =>
        φ ⟨(E.d (n + 1) n).hom y, fdB_le_fdZ F E n hy⟩) hρ
      simpa using h
    have hmem : (⟨(E.d (n + 1) n).hom y, fdB_le_fdZ F E n hy⟩ : ↥(fdZ F E n)) ∈ fdH F E n :=
      (mem_fdH F E n _).mpr hy
    rw [hz, show (fdH F E n).mkQ ⟨(E.d (n + 1) n).hom y, fdB_le_fdZ F E n hy⟩ = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hmem, map_zero]
  refine ⟨⟨f0, hf0⟩, ?_⟩
  apply LinearMap.ext
  intro w
  obtain ⟨z, rfl⟩ := (fdH F E n).mkQ_surjective w
  rw [fdPsi_apply]
  have hz : ρ (z : ↥(E.X n)) = z := by
    have h := congrArg (fun (φ : ↥(fdZ F E n) →ₗ[F] ↥(fdZ F E n)) => φ z) hρ
    simpa using h
  rw [show (fdVal F E n f0) = g.comp ((fdH F E n).mkQ.comp ρ) from rfl]
  simp only [LinearMap.comp_apply, hz]

/-- The kernel of the comparison map is the image of the transposed differential. -/
theorem fdPsi_ker (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ)
    (hR : ∃ r : ↥(E.X (n - 1)) →ₗ[F] ↥(fdR F E n),
      r ∘ₗ (fdR F E n).subtype = LinearMap.id) :
    LinearMap.ker (fdPsi F E n) = fdPre F E n := by
  obtain ⟨r, hr⟩ := hR
  apply le_antisymm
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    have hkill : (fdVal F E n f.1).comp (fdZ F E n).subtype = 0 :=
      Work.Cohomology.liftQ_eq_zero_imp (fdH F E n) _ (fdD_kill F E n f) hf
    have hkill' : ∀ x : ↥(E.X n), x ∈ fdZ F E n → (fdVal F E n f.1) x = 0 := by
      intro x hx
      have h := LinearMap.congr_fun hkill ⟨x, hx⟩
      simpa [LinearMap.comp_apply] using h
    let fbar : (↥(E.X n) ⧸ fdZ F E n) →ₗ[F] F :=
      (fdZ F E n).liftQ (fdVal F E n f.1) (fun x hx => hkill' x hx)
    let e := (E.d n (n - 1)).hom.quotKerEquivRange
    let y : ↥((dualComplex F E).X (n - 1)) :=
      (show ↥(E.X (n - 1)) →ₗ[F] F from (fbar.comp e.symm.toLinearMap).comp r)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    show ((dualComplex F E).d (n - 1) n).hom y = f.1
    rw [fd_d_pred_apply F E n]
    apply LinearMap.ext
    intro x
    show fbar (e.symm (r ((E.d n (n - 1)).hom x))) = (fdVal F E n f.1) x
    rw [show r ((E.d n (n - 1)).hom x) = ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩ from by
      have h := congrArg (fun (φ : ↥(fdR F E n) →ₗ[F] ↥(fdR F E n)) =>
        φ ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩) hr
      simpa using h]
    show fbar (e.symm ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩) = (fdVal F E n f.1) x
    rw [show e.symm ⟨(E.d n (n - 1)).hom x, ⟨x, rfl⟩⟩ = (fdZ F E n).mkQ x from
      LinearMap.quotKerEquivRange_symm_apply_image _ x ⟨x, rfl⟩]
    show fbar ((fdZ F E n).mkQ x) = (fdVal F E n f.1) x
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  · intro f hf
    rw [LinearMap.mem_ker]
    obtain ⟨y, hy⟩ := hf
    have hval : ((dualComplex F E).d (n - 1) n).hom y = f.1 := by
      have h := congrArg Subtype.val hy
      simpa [LinearMap.codRestrict_apply] using h
    apply LinearMap.ext
    intro w
    obtain ⟨x, rfl⟩ := (fdH F E n).mkQ_surjective w
    rw [fdPsi_apply, LinearMap.zero_apply, ← hval]
    show (fdVal F E n (((dualComplex F E).d (n - 1) n).hom y)) ↑x = 0
    rw [fd_d_pred_apply F E n]
    show (fdVal F E (n - 1) y) ((E.d n (n - 1)).hom (x : ↥(E.X n))) = 0
    rw [show (E.d n (n - 1)).hom (x : ↥(E.X n)) = 0 from LinearMap.mem_ker.mp x.2, map_zero]

/-- **The middle isomorphism**: the cohomology of the dual complex is computed from the cycles and
boundaries. -/
noncomputable def fdMiddle (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    (↥(LinearMap.ker ((dualComplex F E).d n (n + 1)).hom) ⧸ fdPre F E n) ≃ₗ[F]
      ((↥(fdZ F E n) ⧸ fdH F E n) →ₗ[F] F) :=
  (Submodule.quotEquivOfEq (fdPre F E n) (LinearMap.ker (fdPsi F E n))
      (fdPsi_ker F E n
        (exists_retraction_subspace_field F (fdR F E n))).symm).trans
    (LinearMap.quotKerEquivOfSurjective (fdPsi F E n)
      (fdPsi_surj F E n (exists_retraction_subspace_field F (fdZ F E n))))

/-! ## The main theorem -/

/-- **The universal coefficient theorem over a field**: for a `ℕ`-indexed chain complex `E` of
`F`-vector spaces, the cohomology of the dual complex `Hom_F(E,F)` is the `F`-dual of the
homology. -/
theorem fieldDualUCT (E : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    Nonempty ((dualComplex F E).homology n ≅
      ModuleCat.of F (↥(E.homology n) →ₗ[F] F)) := by
  obtain ⟨eD⟩ := homology_dual_iso_field F E n
  obtain ⟨eE⟩ := homology_iso_H_field F E n
  refine ⟨eD ≪≫ LinearEquiv.toModuleIso (fdMiddle F E n) ≪≫
    (LinearEquiv.dualMap (Work.Cohomology.uctIsoToLinearEquiv eE)).toModuleIso⟩

/-- The universal coefficient theorem over `ℚ`, in the form requested by subproject SERRE. -/
theorem ratDualUCT (C : ChainComplex (ModuleCat.{0,0} ℚ) ℕ) (n : ℕ) :
    Nonempty ((dualComplex ℚ C).homology n ≅
      ModuleCat.of ℚ (↥(C.homology n) →ₗ[ℚ] ℚ)) :=
  fieldDualUCT ℚ C n

end

end Work.StemsB
