import Mathlib
import Submission.Work.Cohomology.uctDual

/-!
# The dual universal coefficient isomorphism, evaluated on cycles

The dual universal coefficient theorem `Work.Cohomology.uctDual` produces *some* isomorphism
`Hⁿ(Hom(E, ℤ)) ≅ Hom(Hₙ(E), ℤ)`.  For the applications in this development one needs the
isomorphism to be the *canonical* one: the class of a cocycle `z` must correspond to the
functional `[c] ↦ z(c)`, the evaluation of the cocycle on a cycle representing the homology class.

This file fixes a particular such isomorphism, `uctDualEvalEquiv`, and records the computation rule
`uctDualEvalEquiv_apply_apply` (packaged as `Work.Cohomology.uctDual_evaluation`): for every
cocycle `z` of the dual complex and every cycle `c` of `E`,

`e (π z) (π c) = dval E n (iCycles z) (iCycles c)`,

where `π` are the projections onto (co)homology and `iCycles` are the inclusions of the
(co)cycles.

## Strategy

The isomorphism is the comparison map of `Work.Cohomology.uctDual`, rewritten in terms of the
*concrete* cycles and boundaries of `E`:

* `cycIsoZ` and `cycIsoDual` identify the abstract cycles introduced by the homology API of
  Mathlib (`E.cycles n`, `(dualComplex ℤ E).cycles n`) with the concrete modules
  `Zₙ = ker dₙ`, in such a way that the underlying element of the original complex is unchanged
  (`cycIsoZ_hom_val`, `cycIsoDual_hom_val`);
* `homologyZIso` and `homologyDualIso` identify the homology with the concrete quotients
  `Zₙ ⧸ Bₙ` and `ker dⁿ ⧸ im dⁿ⁻¹`, and the computation rules
  `homologyZIso_apply`, `homologyDualIso_apply` say that the class of a cycle is the class of the
  same element;
* `uctMiddle_mkQ` evaluates the middle isomorphism `uctMiddle` of `uctDual` on such a class, where
  it is the comparison map `uctPsi` of that file, whose value on a cycle is the evaluation of the
  cocycle (`uctPsi_apply`).

Combining these computation rules gives the evaluation rule for the composite.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- The module structure on a submodule (resp. a quotient by a submodule) of a `ℤ`-module is the one
-- induced from the ambient module, rather than the one coming from `AddCommGroup.toIntModule`:
-- this makes the various `Submodule`-constructions defeq-compatible.
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

universe u

variable (E : ChainComplex (ModuleCat.{u, 0} ℤ) ℕ)

/-! ## The concrete cycles -/

/-- The `n`-cycles of `E`, identified with the concrete submodule `Zₙ = ker dₙ`. -/
def cycIsoZ (n : ℕ) : E.cycles n ≅ ModuleCat.of ℤ ↥(uctZ E n) :=
  (E.cyclesIsoSc' (n + 1) n (n - 1) (down_prev n) (down_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso (E.sc' (n + 1) n (n - 1))

/-- The `n`-cocycles of the dual complex, identified with the concrete submodule
`ker (dⁿ : Hom(Eₙ, ℤ) ⟶ Hom(E_{n+1}, ℤ))`. -/
def cycIsoDual (n : ℕ) : (dualComplex ℤ E).cycles n ≅
    ModuleCat.of ℤ ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) :=
  ((dualComplex ℤ E).cyclesIsoSc' (n - 1) n (n + 1) (up_prev n) (up_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso ((dualComplex ℤ E).sc' (n - 1) n (n + 1))

/-- A `ModuleCat`-isomorphism is sent to itself by `uctIsoToLinearEquiv`. -/
lemma uctIsoToLinearEquiv_apply {M N : ModuleCat ℤ} (e : M ≅ N) (x : ↥M) :
    uctIsoToLinearEquiv e x = e.hom.hom x := rfl

lemma cycIsoZ_hom_i (n : ℕ) :
    (cycIsoZ E n).hom ≫ (ShortComplex.moduleCatLeftHomologyData (E.sc' (n + 1) n (n - 1))).i
      = E.iCycles n := by
  rw [cycIsoZ, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

lemma cycIsoDual_hom_i (n : ℕ) :
    (cycIsoDual E n).hom ≫
      (ShortComplex.moduleCatLeftHomologyData ((dualComplex ℤ E).sc' (n - 1) n (n + 1))).i
      = (dualComplex ℤ E).iCycles n := by
  rw [cycIsoDual, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `cycIsoZ` does not change the underlying element. -/
lemma cycIsoZ_hom_val (n : ℕ) (c : ↥(E.cycles n)) :
    ((cycIsoZ E n).hom c : ↥(E.X n)) = (E.iCycles n).hom c := by
  have h := congrArg (fun (m : E.cycles n ⟶ E.X n) => ModuleCat.Hom.hom m c) (cycIsoZ_hom_i E n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- `cycIsoDual` does not change the underlying element. -/
lemma cycIsoDual_hom_val (n : ℕ) (z : ↥((dualComplex ℤ E).cycles n)) :
    ((cycIsoDual E n).hom z : ↥((dualComplex ℤ E).X n))
      = ((dualComplex ℤ E).iCycles n).hom z := by
  have h := congrArg (fun (m : (dualComplex ℤ E).cycles n ⟶ (dualComplex ℤ E).X n) =>
      ModuleCat.Hom.hom m z) (cycIsoDual_hom_i E n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-! ## The homology as a concrete quotient -/

/-- The `n`-th homology of `E` is the quotient `Zₙ ⧸ Bₙ`. -/
def homologyZIso (n : ℕ) : E.homology n ≅ ModuleCat.of ℤ (↥(uctZ E n) ⧸ uctH E n) :=
  (E.homologyIsoSc' (n + 1) n (n - 1) (down_prev n) (down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (E.sc' (n + 1) n (n - 1))

/-- The `n`-th cohomology of the dual complex is the quotient `ker dⁿ ⧸ im dⁿ⁻¹`. -/
def homologyDualIso (n : ℕ) : (dualComplex ℤ E).homology n ≅
    ModuleCat.of ℤ (↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) ⧸ uctPre E n) :=
  ((dualComplex ℤ E).homologyIsoSc' (n - 1) n (n + 1) (up_prev n) (up_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso ((dualComplex ℤ E).sc' (n - 1) n (n + 1))

/-- The projection onto the left homology data of `E` is the quotient map onto `Zₙ ⧸ Bₙ`. -/
lemma LHD_pi_eq (n : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData (E.sc' (n + 1) n (n - 1))).π
      = ModuleCat.ofHom ((uctH E n).mkQ) := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

/-- The projection onto the left homology data of the dual complex is the quotient map onto
`ker dⁿ ⧸ im dⁿ⁻¹`. -/
lemma LHD_pi_eq_dual (n : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData ((dualComplex ℤ E).sc' (n - 1) n (n + 1))).π
      = ModuleCat.ofHom ((uctPre E n).mkQ) := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

lemma homologyZIso_comp (n : ℕ) :
    (E.homologyπ n) ≫ (homologyZIso E n).hom
      = (cycIsoZ E n).hom ≫ ModuleCat.ofHom ((uctH E n).mkQ) := by
  simp only [homologyZIso, Iso.trans_hom, Category.assoc, cycIsoZ,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  rw [LHD_pi_eq E n]

lemma homologyDualIso_comp (n : ℕ) :
    ((dualComplex ℤ E).homologyπ n) ≫ (homologyDualIso E n).hom
      = (cycIsoDual E n).hom ≫ ModuleCat.ofHom ((uctPre E n).mkQ) := by
  simp only [homologyDualIso, Iso.trans_hom, Category.assoc, cycIsoDual,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  rw [LHD_pi_eq_dual E n]

/-- The computation rule for `homologyZIso`: the class of a cycle is the class of the same
element of `Zₙ ⧸ Bₙ`. -/
lemma homologyZIso_apply (n : ℕ) (c : ↥(E.cycles n)) :
    (homologyZIso E n).hom.hom ((E.homologyπ n).hom c)
      = (uctH E n).mkQ ((cycIsoZ E n).hom c) := by
  have h := congrArg (fun (m : E.cycles n ⟶ ModuleCat.of ℤ (↥(uctZ E n) ⧸ uctH E n)) =>
      ModuleCat.Hom.hom m c) (homologyZIso_comp E n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h

/-- The computation rule for `homologyDualIso`: the class of a cocycle is the class of the same
element of `ker dⁿ ⧸ im dⁿ⁻¹`. -/
lemma homologyDualIso_apply (n : ℕ) (z : ↥((dualComplex ℤ E).cycles n)) :
    (homologyDualIso E n).hom.hom (((dualComplex ℤ E).homologyπ n).hom z)
      = (uctPre E n).mkQ ((cycIsoDual E n).hom z) := by
  have h := congrArg (fun (m : (dualComplex ℤ E).cycles n ⟶
      ModuleCat.of ℤ (↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) ⧸ uctPre E n)) =>
      ModuleCat.Hom.hom m z) (homologyDualIso_comp E n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h

/-! ## The comparison map on the middle quotient -/

/-- The middle comparison map of `Work.Cohomology.uctDual` is `uctPsi` on representatives. -/
lemma uctMiddle_mkQ (n : ℕ)
    (hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id)
    (hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n), r ∘ₗ (uctR E n).subtype = LinearMap.id)
    (x : ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom)) :
    uctMiddle E n hZ hR ((uctPre E n).mkQ x) = uctPsi E n x := by
  rw [uctMiddle, LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk (uctPsi E n) (uctPsi_surj E n hZ) x

/-! ## The isomorphism -/

/-- The dual universal coefficient isomorphism of `Work.Cohomology.uctDual`, made explicit: the
composite of the identification of the cohomology of the dual complex with `ker dⁿ ⧸ im dⁿ⁻¹`, the
comparison map `uctMiddle`, and the `ℤ`-dual of the identification `Hₙ(E) ≅ Zₙ ⧸ Bₙ`. -/
def uctDualEvalEquiv (n : ℕ)
    (hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id)
    (hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n), r ∘ₗ (uctR E n).subtype = LinearMap.id) :
    ↥((dualComplex ℤ E).homology n) ≃ₗ[ℤ] (↥(E.homology n) →ₗ[ℤ] ℤ) :=
  (uctIsoToLinearEquiv (homologyDualIso E n)).trans <|
    (uctMiddle E n hZ hR).trans <|
      LinearEquiv.dualMap (uctIsoToLinearEquiv (homologyZIso E n))

/-- **The dual universal coefficient isomorphism, evaluated on cycles.**  The value of the class of
a cocycle `z` at the class of a cycle `c` is the evaluation of `z` on `c`. -/
theorem uctDualEvalEquiv_apply_apply (n : ℕ)
    (hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id)
    (hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n), r ∘ₗ (uctR E n).subtype = LinearMap.id)
    (z : ↥((dualComplex ℤ E).cycles n)) (c : ↥(E.cycles n)) :
    uctDualEvalEquiv E n hZ hR (((dualComplex ℤ E).homologyπ n).hom z)
        ((E.homologyπ n).hom c)
      = dval E n (((dualComplex ℤ E).iCycles n).hom z) ((E.iCycles n).hom c) := by
  change (uctIsoToLinearEquiv (homologyDualIso E n)).trans
      ((uctMiddle E n hZ hR).trans (LinearEquiv.dualMap (uctIsoToLinearEquiv (homologyZIso E n))))
      (((dualComplex ℤ E).homologyπ n).hom z) ((E.homologyπ n).hom c) = _
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    uctIsoToLinearEquiv_apply, uctIsoToLinearEquiv_apply, homologyDualIso_apply,
    homologyZIso_apply, uctMiddle_mkQ, uctPsi_apply, cycIsoDual_hom_val, cycIsoZ_hom_val]

/-! ## The requested statement -/

theorem uctDual_evaluation (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hproj : ∀ n, Module.Projective ℤ ↥(E.X n))
    (hfree : ∀ n, Module.Free ℤ ↥(E.homology n)) (n : ℕ) :
    ∃ e : (Work.Cohomology.dualComplex ℤ E).homology n ≅
        ModuleCat.of ℤ (↥(E.homology n) →ₗ[ℤ] ℤ),
      ∀ (z : ↥((Work.Cohomology.dualComplex ℤ E).cycles n)) (c : ↥(E.cycles n)),
        e.hom (((Work.Cohomology.dualComplex ℤ E).homologyπ n).hom z)
            (((E.homologyπ n).hom c))
          = Work.Cohomology.dval E n
              (((Work.Cohomology.dualComplex ℤ E).iCycles n).hom z)
              ((E.iCycles n).hom c) := by
  have hH : ∀ k, Module.Projective ℤ (↥(uctZ E k) ⧸ uctH E k) := by
    intro k
    obtain ⟨e⟩ := homology_iso_H E k
    haveI : Module.Free ℤ ↥(E.homology k) := hfree k
    exact Module.Projective.of_equiv' (uctIsoToLinearEquiv e)
  have hB : ∀ k, Module.Projective ℤ ↥(uctB E k) := uctB_projective E hproj hH
  have hRp : ∀ k, Module.Projective ℤ ↥(uctR E k) := fun k => uctR_projective E hB k
  have hZ : ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id :=
    exists_retraction_cycles E n (hRp n)
  have hR : ∃ r : ↥(E.X (n - 1)) →ₗ[ℤ] ↥(uctR E n),
      r ∘ₗ (uctR E n).subtype = LinearMap.id :=
    exists_retraction_R E n (fun m => exists_retraction_bounds E m (hRp m) (hH m))
  refine ⟨LinearEquiv.toModuleIso (uctDualEvalEquiv E n hZ hR), ?_⟩
  intro z c
  simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
  exact uctDualEvalEquiv_apply_apply E n hZ hR z c

end

end Work.Cohomology
