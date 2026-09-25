import Mathlib
import Submission.Work.CFTLib.ContCohomology.Inhomogeneous
import Submission.Work.CFT.MaxProP.ContCohomology.Defs
import Submission.Work.CFTLib.Topology.factorThroughFiniteQuotient

/-!
# The inhomogeneous complex and the finite quotients

This file collects the vocabulary relating the inhomogeneous complex of continuous cochains of a
profinite group `Γ` (with trivial `𝔽_p`-coefficients) to the abstract cohomology of its finite
quotients `Γ ⧸ U`, `U ▷ Γ` open normal.

The main theorem of the area,
`Work.CFTLib.ContCohomology.iComplex_homology_two_iso_H2FpCont`, states that the second homology of
the inhomogeneous complex is the filtered colimit of the `H²` of the finite quotients.  The present
file provides the objects occurring in its proof:

* `iK p Γ` — the module of continuous `2`-cocycles of `Γ` (`ker (iDiff p 2)`);
* `iConc p Γ` — the concrete model `Z²/B²` of `H²` of the inhomogeneous complex;
* `iConcEquiv` — the identification of `↥((iComplex p Γ).homology 2)` with `iConc p Γ`;
* `H2Conc p Q` — the concrete model `Z²/B² = cocycles₂/coboundaries₂` of `H²(Q, 𝔽_p)`;
* `pbZ p Γ U` — the pullback of a `2`-cocycle of `Γ ⧸ U` to a continuous `2`-cocycle of `Γ`.
-/

namespace Work.CFTLib.ContCohomology

noncomputable section

open CategoryTheory groupCohomology

/-- The trivial `𝔽_p`-representation of a group `Q`. -/
abbrev Aq (p : ℕ) (Q : Type) [Group Q] : Rep (ZMod p) Q := Rep.trivial (ZMod p) Q (ZMod p)

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## The concrete model of `H²` of the inhomogeneous complex -/

/-- The continuous `2`-cocycles of the inhomogeneous complex, as a submodule of `iCochain 2`. -/
abbrev iZ (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Submodule (ZMod p) ↥(iCochain (Γ := Γ) p 2) := LinearMap.ker (iDiff (Γ := Γ) p 2)

/-- The continuous `2`-coboundaries of the inhomogeneous complex. -/
abbrev iB (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    Submodule (ZMod p) ↥(iCochain (Γ := Γ) p 2) := LinearMap.range (iDiff (Γ := Γ) p 1)

/-- The `2`-coboundaries are `2`-cocycles. -/
lemma iB_le_iZ (p : ℕ) : iB p Γ ≤ iZ p Γ := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact iDiff_comp_iDiff (Γ := Γ) p 1 y

/-- The short complex `iCochain 1 → iCochain 2 → iCochain 3` of the inhomogeneous complex,
whose homology in the middle is `H²`. -/
abbrev iShort (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    ShortComplex (ModuleCat (ZMod p)) :=
  ShortComplex.mk (ModuleCat.ofHom (iDiff (Γ := Γ) p 1)) (ModuleCat.ofHom (iDiff (Γ := Γ) p 2))
    (ModuleCat.hom_ext (LinearMap.ext fun f => by
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      exact iDiff_comp_iDiff (Γ := Γ) p 1 f))

lemma iComplex_d_1_2 (p : ℕ) :
    (iComplex (Γ := Γ) p).d 1 2 = ModuleCat.ofHom (iDiff (Γ := Γ) p 1) := by
  change CochainComplex.of.d (fun n => ModuleCat.of (ZMod p) ↥(iCochain (Γ := Γ) p n))
    (fun n => ModuleCat.ofHom (iDiff (Γ := Γ) p n)) 1 2 = _
  exact CochainComplex.of_d _ _ 1

lemma iComplex_d_2_3 (p : ℕ) :
    (iComplex (Γ := Γ) p).d 2 3 = ModuleCat.ofHom (iDiff (Γ := Γ) p 2) := by
  change CochainComplex.of.d (fun n => ModuleCat.of (ZMod p) ↥(iCochain (Γ := Γ) p n))
    (fun n => ModuleCat.ofHom (iDiff (Γ := Γ) p n)) 2 3 = _
  exact CochainComplex.of_d _ _ 2

/-- The canonical isomorphism `(iComplex p Γ).sc' 1 2 3 ≅ iShort p Γ`. -/
def iScIso (p : ℕ) :
    (iComplex (Γ := Γ) p).sc' 1 2 3 ≅ iShort p Γ :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      show (iShort p Γ).f = (iComplex (Γ := Γ) p).d 1 2
      rw [iComplex_d_1_2])
    (by
      simp only [Iso.refl_hom]
      show (iShort p Γ).g = (iComplex (Γ := Γ) p).d 2 3
      rw [iComplex_d_2_3])

/-- **`H²` of the inhomogeneous complex is the homology of the short complex
`iCochain 1 → iCochain 2 → iCochain 3`.** -/
def iComplexHomologyTwoIso (p : ℕ) :
    (iComplex (Γ := Γ) p).homology 2 ≅ (iShort p Γ).homology :=
  (HomologicalComplex.homologyIsoSc' (iComplex (Γ := Γ) p) 1 2 3
      (ComplexShape.prev_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk 1 2 rfl))
      (ComplexShape.next_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk 2 3 rfl))) ≪≫
    ShortComplex.homologyMapIso (iScIso p)

/-- The kernel of `iDiff p 2`, i.e. the module of continuous `2`-cocycles, in the shape used by
`ShortComplex.moduleCatLeftHomologyData`. -/
abbrev iK (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : Type :=
  ↥((iShort p Γ).moduleCatLeftHomologyData.K)

/-- The concrete model of `H²` of the inhomogeneous complex: the `2`-cocycles modulo the
`2`-coboundaries. -/
abbrev iConc (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : Type :=
  ↥((iShort p Γ).moduleCatLeftHomologyData.H)

/-- The quotient map `Z²(Γ) → H²(Γ)` of the inhomogeneous complex. -/
abbrev piI (p : ℕ) : iK p Γ →ₗ[ZMod p] iConc p Γ :=
  ((iShort p Γ).moduleCatLeftHomologyData.π).hom

set_option backward.isDefEq.respectTransparency false in
/-- An element of the concrete `H²` of the inhomogeneous complex vanishes exactly when the
corresponding cocycle is a coboundary. -/
lemma piI_eq_zero_iff (p : ℕ) (z : ↥(iZ p Γ)) :
    piI (Γ := Γ) p z = 0 ↔ (z : ↥(iCochain (Γ := Γ) p 2)) ∈ iB p Γ := by
  have h : piI (Γ := Γ) p z = (iShort p Γ).moduleCatToCycles.range.mkQ z := by
    rw [show piI (Γ := Γ) p = ((iShort p Γ).moduleCatLeftHomologyData.π).hom from rfl,
      ShortComplex.moduleCatLeftHomologyData_π_hom]
    rfl
  rw [h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [show (iShort p Γ).moduleCatToCycles.range = (iB p Γ).comap (iZ p Γ).subtype from by
    simp only [ShortComplex.moduleCatToCycles, ModuleCat.hom_ofHom]
    rw [LinearMap.range_codRestrict]]
  exact Submodule.mem_comap

set_option backward.isDefEq.respectTransparency false in
/-- The quotient map `Z²(Γ) → H²(Γ)` of the inhomogeneous complex is surjective. -/
lemma piI_surjective (p : ℕ) : Function.Surjective (piI (Γ := Γ) p) := by
  have h : piI (Γ := Γ) p = (iShort p Γ).moduleCatToCycles.range.mkQ := by
    rw [show piI (Γ := Γ) p = ((iShort p Γ).moduleCatLeftHomologyData.π).hom from rfl,
      ShortComplex.moduleCatLeftHomologyData_π_hom]
  rw [h]
  exact Submodule.mkQ_surjective _

/-- The identification of `H²` of the inhomogeneous complex with its concrete model `iConc`. -/
def iConcEquiv (p : ℕ) :
    ↥((iComplex (Γ := Γ) p).homology 2) ≃ₗ[ZMod p] iConc p Γ :=
  (iComplexHomologyTwoIso (Γ := Γ) p ≪≫ (iShort p Γ).moduleCatHomologyIso).toLinearEquiv

/-! ## Reindexing between `Fin n` and products -/

/-- The reindexing `(Fin 1 → Q) → 𝔽 ≃ (Q → 𝔽)` of `1`-cochains. -/
noncomputable def rx1 (p : ℕ) (Q : Type) [Group Q] :
    ((Fin 1 → Q) → ZMod p) ≃ₗ[ZMod p] (Q → ZMod p) :=
  (cochainsIso₁ (Aq p Q)).toLinearEquiv

/-- The reindexing `(Fin 2 → Q) → 𝔽 ≃ (Q × Q → 𝔽)` of `2`-cochains. -/
noncomputable def rx2 (p : ℕ) (Q : Type) [Group Q] :
    ((Fin 2 → Q) → ZMod p) ≃ₗ[ZMod p] (Q × Q → ZMod p) :=
  (cochainsIso₂ (Aq p Q)).toLinearEquiv

/-- The reindexing `(Fin 3 → Q) → 𝔽 ≃ (Q × Q × Q → 𝔽)` of `3`-cochains. -/
noncomputable def rx3 (p : ℕ) (Q : Type) [Group Q] :
    ((Fin 3 → Q) → ZMod p) ≃ₗ[ZMod p] (Q × Q × Q → ZMod p) :=
  (cochainsIso₃ (Aq p Q)).toLinearEquiv

omit [IsTopologicalGroup Γ] in
lemma rx1_apply (p : ℕ) (Q : Type) [Group Q] (x : (Fin 1 → Q) → ZMod p) (g : Q) :
    rx1 p Q x g = x (fun _ => g) := by
  show (ConcreteCategory.hom ((cochainsIso₁ (Aq p Q)).hom)) x g = _
  simp only [cochainsIso₁, Iso.symm_hom, LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom,
    LinearEquiv.funCongrLeft_symm, LinearEquiv.coe_toLinearMap, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, Equiv.funUnique_symm_apply]
  congr 1

omit [IsTopologicalGroup Γ] in
lemma rx2_apply (p : ℕ) (Q : Type) [Group Q] (x : (Fin 2 → Q) → ZMod p) (g h : Q) :
    rx2 p Q x (g, h) = x (fun i => if i = 0 then g else h) := by
  show (ConcreteCategory.hom ((cochainsIso₂ (Aq p Q)).hom)) x (g, h) = _
  simp only [cochainsIso₂, Iso.symm_hom, LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom,
    LinearEquiv.funCongrLeft_symm, LinearEquiv.coe_toLinearMap, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]
  congr 1
  ext i; fin_cases i <;> rfl

omit [IsTopologicalGroup Γ] in
lemma rx3_apply (p : ℕ) (Q : Type) [Group Q] (x : (Fin 3 → Q) → ZMod p) (g h k : Q) :
    rx3 p Q x (g, h, k) = x (fun i => if i = 0 then g else if i = 1 then h else k) := by
  show (ConcreteCategory.hom ((cochainsIso₃ (Aq p Q)).hom)) x (g, h, k) = _
  simp only [cochainsIso₃, Iso.symm_hom, LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom,
    LinearEquiv.funCongrLeft_symm, LinearEquiv.coe_toLinearMap, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]
  congr 1
  ext i; fin_cases i <;> rfl

omit [IsTopologicalGroup Γ] in
/-- The reindexing `rx2` intertwines the inhomogeneous differential `d 1 2` on `Fin`-indexed
cochains with the differential `d₁₂` on product-indexed cochaines. -/
lemma d₁₂_comm (p : ℕ) (Q : Type) [Group Q] (x : (Fin 1 → Q) → ZMod p) :
    rx2 p Q ((inhomogeneousCochains (Aq p Q)).d 1 2 x) = d₁₂ (Aq p Q) (rx1 p Q x) := by
  have h := congrArg
    (fun (φ : (inhomogeneousCochains (Aq p Q)).X 1 ⟶ ModuleCat.of (ZMod p) (Q × Q → ZMod p)) =>
      ModuleCat.Hom.hom φ x) (comp_d₁₂_eq (Aq p Q))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

omit [IsTopologicalGroup Γ] in
/-- The reindexing `rx3` intertwines the inhomogeneous differential `d 2 3` on `Fin`-indexed
cochains with the differential `d₂₃` on product-indexed cochaines. -/
lemma d₂₃_comm (p : ℕ) (Q : Type) [Group Q] (x : (Fin 2 → Q) → ZMod p) :
    rx3 p Q ((inhomogeneousCochains (Aq p Q)).d 2 3 x) = d₂₃ (Aq p Q) (rx2 p Q x) := by
  have h := congrArg
    (fun (φ : (inhomogeneousCochains (Aq p Q)).X 2 ⟶
      ModuleCat.of (ZMod p) (Q × Q × Q → ZMod p)) => ModuleCat.Hom.hom φ x)
    (comp_d₂₃_eq (Aq p Q))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-! ## The abstract side: `H²(Q, 𝔽_p)` as cocycles modulo coboundaries -/

/-- The short complex of product-indexed cochains `Fun(Q, 𝔽_p) → Fun(Q², 𝔽_p) → Fun(Q³, 𝔽_p)`. -/
abbrev S2 (p : ℕ) (Q : Type) [Group Q] : ShortComplex (ModuleCat (ZMod p)) :=
  shortComplexH2 (Aq p Q)

/-- The concrete model `Z²(Q)/B²(Q)` of `H²(Q, 𝔽_p)`. -/
abbrev H2Conc (p : ℕ) (Q : Type) [Group Q] : Type := ↥((S2 p Q).moduleCatLeftHomologyData.H)

/-- The identification of `H²(Q, 𝔽_p)` with its concrete model `H2Conc`. -/
noncomputable def H2ConcEquiv (p : ℕ) (Q : Type) [Group Q] :
    ↥(Work.Tower.Shafarevich.H2Fp p Q) ≃ₗ[ZMod p] H2Conc p Q :=
  (groupCohomology.H2Iso (Aq p Q)).toLinearEquiv

/-- The quotient map `Z²(Q, 𝔽_p) → H²(Q, 𝔽_p)`. -/
noncomputable def gQ (p : ℕ) (Q : Type) [Group Q] :
    ↥(cocycles₂ (Aq p Q)) →ₗ[ZMod p] H2Conc p Q :=
  (H2ConcEquiv p Q).toLinearMap.comp (groupCohomology.H2π (Aq p Q)).hom

lemma gQ_apply (p : ℕ) (Q : Type) [Group Q] (c : ↥(cocycles₂ (Aq p Q))) :
    gQ p Q c = H2ConcEquiv p Q (groupCohomology.H2π (Aq p Q) c) := rfl

lemma gQ_surjective (p : ℕ) (Q : Type) [Group Q] : Function.Surjective (gQ p Q) := by
  intro y
  obtain ⟨z, hz⟩ := (H2ConcEquiv p Q).surjective y
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H2π (Aq p Q))).mp inferInstance z
  exact ⟨c, by rw [gQ_apply]; exact hz⟩

/-- The kernel of `gQ` consists of the `2`-coboundaries. -/
lemma mem_gQ_ker (p : ℕ) (Q : Type) [Group Q] (c : ↥(cocycles₂ (Aq p Q))) :
    c ∈ (gQ p Q).ker ↔ (c : Q × Q → ZMod p) ∈ coboundaries₂ (Aq p Q) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h1 : H2ConcEquiv p Q (groupCohomology.H2π (Aq p Q) c) = 0 := h
    rw [← map_zero (H2ConcEquiv p Q)] at h1
    exact (groupCohomology.H2π_eq_zero_iff (A := Aq p Q) c).mp
      ((H2ConcEquiv p Q).injective h1)
  · intro h
    rw [show gQ p Q c = H2ConcEquiv p Q (groupCohomology.H2π (Aq p Q) c) from rfl,
      (groupCohomology.H2π_eq_zero_iff (A := Aq p Q) c).mpr h, map_zero]

/-! ## Pullbacks of cochains along a homomorphism `Γ → Q` -/

/-- Precomposition of `1`-cochains `Q → 𝔽_p` along a homomorphism. -/
def precompFun1 (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) :
    (Q → ZMod p) →ₗ[ZMod p] (Γ → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) π

/-- Precomposition of `3`-cochains `Q³ → 𝔽_p` along a homomorphism. -/
def precompFun3 (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) :
    (Q × Q × Q → ZMod p) →ₗ[ZMod p] (Γ × Γ × Γ → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) (Prod.map π (Prod.map π π))

omit [IsTopologicalGroup Γ] in
@[simp] lemma precompFun1_apply (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) (y : Q → ZMod p)
    (g : Γ) : precompFun1 (Γ := Γ) p π y g = y (π g) := rfl

omit [IsTopologicalGroup Γ] in
lemma rx1_symm_apply (p : ℕ) (Q : Type) [Group Q] (y : Q → ZMod p) (x : Fin 1 → Q) :
    (rx1 p Q).symm y x = y (x 0) := by
  conv_lhs => rw [show x = (fun _ : Fin 1 => x 0) from by funext i; fin_cases i <;> rfl]
  rw [← rx1_apply p Q ((rx1 p Q).symm y) (x 0), LinearEquiv.apply_symm_apply]

omit [IsTopologicalGroup Γ] in
lemma rx2_symm_apply (p : ℕ) (Q : Type) [Group Q] (y : Q × Q → ZMod p) (x : Fin 2 → Q) :
    (rx2 p Q).symm y x = y (x 0, x 1) := by
  conv_lhs => rw [show x = (fun i : Fin 2 => if i = 0 then x 0 else x 1) from by
    funext i; fin_cases i <;> rfl]
  rw [← rx2_apply p Q ((rx2 p Q).symm y) (x 0) (x 1), LinearEquiv.apply_symm_apply]

omit [IsTopologicalGroup Γ] in
lemma rx3_symm_apply (p : ℕ) (Q : Type) [Group Q] (y : Q × Q × Q → ZMod p) (x : Fin 3 → Q) :
    (rx3 p Q).symm y x = y (x 0, x 1, x 2) := by
  conv_lhs => rw [show x = (fun i : Fin 3 => if i = 0 then x 0 else if i = 1 then x 1 else x 2)
    from by funext i; fin_cases i <;> rfl]
  rw [← rx3_apply p Q ((rx3 p Q).symm y) (x 0) (x 1) (x 2), LinearEquiv.apply_symm_apply]

/-- Precomposition of `1`-cochains along `π`, reindexed as `Fin 1`-indexed cochains. -/
noncomputable def pull1 (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) :
    (Q → ZMod p) →ₗ[ZMod p] ((Fin 1 → Γ) → ZMod p) :=
  (rx1 p Γ).symm.toLinearMap.comp (precompFun1 p π)

/-- Precomposition of `2`-cochains along `π`, reindexed as `Fin 2`-indexed cochains. -/
noncomputable def pull2 (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) :
    (Q × Q → ZMod p) →ₗ[ZMod p] ((Fin 2 → Γ) → ZMod p) :=
  (rx2 p Γ).symm.toLinearMap.comp (Work.CFT.KochTransfer.precompFun π)

/-- Precomposition of `3`-cochains along `π`, reindexed as `Fin 3`-indexed cochains. -/
noncomputable def pull3 (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) :
    (Q × Q × Q → ZMod p) →ₗ[ZMod p] ((Fin 3 → Γ) → ZMod p) :=
  (rx3 p Γ).symm.toLinearMap.comp (precompFun3 p π)

omit [IsTopologicalGroup Γ] in
@[simp] lemma pull1_apply (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) (y : Q → ZMod p)
    (x : Fin 1 → Γ) : pull1 (Γ := Γ) p π y x = y (π (x 0)) := by
  show (rx1 p Γ).symm (precompFun1 p π y) x = y (π (x 0))
  rw [rx1_symm_apply]
  rfl

omit [IsTopologicalGroup Γ] in
@[simp] lemma pull2_apply (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) (y : Q × Q → ZMod p)
    (x : Fin 2 → Γ) : pull2 (Γ := Γ) p π y x = y (π (x 0), π (x 1)) := by
  show (rx2 p Γ).symm (Work.CFT.KochTransfer.precompFun π y) x = y (π (x 0), π (x 1))
  rw [rx2_symm_apply]
  rfl

omit [IsTopologicalGroup Γ] in
@[simp] lemma pull3_apply (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) (y : Q × Q × Q → ZMod p)
    (x : Fin 3 → Γ) : pull3 (Γ := Γ) p π y x = y (π (x 0), π (x 1), π (x 2)) := by
  show (rx3 p Γ).symm (precompFun3 p π y) x = y (π (x 0), π (x 1), π (x 2))
  rw [rx3_symm_apply]
  rfl

omit [IsTopologicalGroup Γ] in
/-- The differential `d₁₂` commutes with the pullback of `1`-cochains. -/
lemma precompFun_d₁₂ (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) (y : Q → ZMod p) :
    Work.CFT.KochTransfer.precompFun π (d₁₂ (Aq p Q) y) =
      d₁₂ (Aq p Γ) (precompFun1 p π y) := by
  funext x
  obtain ⟨g, h⟩ := x
  simp [Work.CFT.KochTransfer.precompFun_apply, d₁₂_hom_apply, precompFun1, map_mul]

omit [IsTopologicalGroup Γ] in
/-- The differential `d₂₃` commutes with the pullback of `2`-cochains. -/
lemma precompFun_d₂₃ (p : ℕ) {Q : Type} [Group Q] (π : Γ →* Q) (y : Q × Q → ZMod p) :
    precompFun3 p π (d₂₃ (Aq p Q) y) =
      d₂₃ (Aq p Γ) (Work.CFT.KochTransfer.precompFun π y) := by
  funext x
  obtain ⟨g, h, k⟩ := x
  simp [Work.CFT.KochTransfer.precompFun_apply, d₂₃_hom_apply, precompFun3, map_mul]

omit [IsTopologicalGroup Γ] in
/-- The inverse reindexing `rx2⁻¹` intertwines `d₁₂` with the inhomogeneous differential. -/
lemma d₁₂_comm_inv (p : ℕ) (Q : Type) [Group Q] (y : Q → ZMod p) :
    (rx2 p Q).symm (d₁₂ (Aq p Q) y) =
      (inhomogeneousCochains (Aq p Q)).d 1 2 ((rx1 p Q).symm y) := by
  have h := congrArg
    (fun (φ : ModuleCat.of (ZMod p) (Q → ZMod p) ⟶
      (inhomogeneousCochains (Aq p Q)).X 2) => ModuleCat.Hom.hom φ y)
    (eq_d₁₂_comp_inv (Aq p Q))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

omit [IsTopologicalGroup Γ] in
/-- The inverse reindexing `rx3⁻¹` intertwines `d₂₃` with the inhomogeneous differential. -/
lemma d₂₃_comm_inv (p : ℕ) (Q : Type) [Group Q] (y : Q × Q → ZMod p) :
    (rx3 p Q).symm (d₂₃ (Aq p Q) y) =
      (inhomogeneousCochains (Aq p Q)).d 2 3 ((rx2 p Q).symm y) := by
  have h := congrArg
    (fun (φ : ModuleCat.of (ZMod p) (Q × Q → ZMod p) ⟶
      (inhomogeneousCochains (Aq p Q)).X 3) => ModuleCat.Hom.hom φ y)
    (eq_d₂₃_comp_inv (Aq p Q))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-! ## Continuity of the pullbacks

For a discrete group `Q`, every function on `Q` is continuous, so the pullback of any cochain
along a continuous homomorphism `Γ → Q` is again continuous. -/

section Continuous

variable {Q : Type} [Group Q] [TopologicalSpace Q]

lemma continuous_pull1 (p : ℕ) (hQ : DiscreteTopology Q) (π : Γ →* Q) (hπ : Continuous π)
    (y : Q → ZMod p) : Continuous (pull1 (Γ := Γ) p π y) := by
  haveI := hQ
  have h : pull1 (Γ := Γ) p π y = fun x : Fin 1 → Γ => y (π (x 0)) :=
    funext fun x => pull1_apply p π y x
  rw [h]
  exact (continuous_of_discreteTopology (f := y)).comp (hπ.comp (continuous_apply 0))

lemma continuous_pull2 (p : ℕ) (hQ : DiscreteTopology Q) (π : Γ →* Q) (hπ : Continuous π)
    (y : Q × Q → ZMod p) : Continuous (pull2 (Γ := Γ) p π y) := by
  haveI := hQ
  have h : pull2 (Γ := Γ) p π y = fun x : Fin 2 → Γ => y (π (x 0), π (x 1)) :=
    funext fun x => pull2_apply p π y x
  rw [h]
  exact (continuous_of_discreteTopology (f := y)).comp
    ((hπ.comp (continuous_apply 0)).prodMk (hπ.comp (continuous_apply 1)))

lemma continuous_pull3 (p : ℕ) (hQ : DiscreteTopology Q) (π : Γ →* Q) (hπ : Continuous π)
    (y : Q × Q × Q → ZMod p) : Continuous (pull3 (Γ := Γ) p π y) := by
  haveI := hQ
  have h : pull3 (Γ := Γ) p π y = fun x : Fin 3 → Γ => y (π (x 0), π (x 1), π (x 2)) :=
    funext fun x => pull3_apply p π y x
  rw [h]
  exact (continuous_of_discreteTopology (f := y)).comp
    ((hπ.comp (continuous_apply 0)).prodMk
      ((hπ.comp (continuous_apply 1)).prodMk (hπ.comp (continuous_apply 2))))

end Continuous

/-- The inhomogeneous differential `iDiff` agrees with the differential of Mathlib's
inhomogeneous cochain complex of the trivial representation (in degrees `n → n+1`). -/
lemma iDiff_eq_d' (p : ℕ) (n : ℕ) (f : ↥(iCochain (Γ := Γ) p n)) :
    (iDiff p n f).1 = ((inhomogeneousCochains (Aq p Γ)).d n (n+1)).hom f.1 := by
  rw [iDiff_eq_d, ← inhomogeneousCochains.d_def]

/-! ## The pullback of `2`-cocycles along `Γ → Γ ⧸ U` -/

/-- The quotient homomorphism `Γ → Γ ⧸ U` is continuous. -/
lemma continuous_quotientMk' (U : Work.CFT.MaxProP.OpenNormal Γ) :
    Continuous (QuotientGroup.mk' U.carrier : Γ → Γ ⧸ U.carrier) := by
  have h : (QuotientGroup.mk' U.carrier : Γ → Γ ⧸ U.carrier) = QuotientGroup.mk := rfl
  rw [h]
  exact QuotientGroup.continuous_mk

/-- The map `OpenNormal.quotientMap` evaluated on a coset. -/
@[simp] lemma OpenNormal.quotientMap_mk'_apply {U V : Work.CFT.MaxProP.OpenNormal Γ} (h : U ≤ V)
    (g : Γ) : Work.CFT.MaxProP.OpenNormal.quotientMap U V h (QuotientGroup.mk' V.carrier g)
      = QuotientGroup.mk' U.carrier g := rfl

/-- The `2`-cocycle condition for the inhomogeneous complex. -/
lemma iDiff_eq_zero_iff (p : ℕ) (n : ℕ) (f : ↥(iCochain (Γ := Γ) p n)) :
    iDiff p n f = 0 ↔ ((inhomogeneousCochains (Aq p Γ)).d n (n+1)).hom f.1 = 0 := by
  rw [Subtype.ext_iff, iDiff_eq_d']
  rfl

/-- The coercion of an element of the module of `2`-cocycles to the ambient module of continuous
functions `(Fin 2 → Γ) → 𝔽_p`. -/
instance instCoeOutIK (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    CoeOut (iK p Γ) (↥(iCochain (Γ := Γ) p 2)) := ⟨fun z => (show ↥(iZ p Γ) from z)⟩

set_option backward.isDefEq.respectTransparency false in
/-- An element of the concrete `H²` vanishes exactly when the corresponding cocycle is a
coboundary. -/
lemma piI_eq_zero_iff' (p : ℕ) (z : iK p Γ) :
    piI (Γ := Γ) p z = 0 ↔ (z : ↥(iCochain (Γ := Γ) p 2)) ∈ iB p Γ :=
  piI_eq_zero_iff (Γ := Γ) p (show ↥(iZ p Γ) from z)

/-- The pullback of `2`-cochains to continuous `2`-cochains of `Γ`, along `Γ → Γ ⧸ U`. -/
noncomputable def pbZfun (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ) :
    ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier))) →ₗ[ZMod p] ↥(iCochain (Γ := Γ) p 2) :=
  ((pull2 (Γ := Γ) p (QuotientGroup.mk' U.carrier)).comp
      (cocycles₂ (Aq p (Γ ⧸ U.carrier))).subtype).codRestrict (iCochain (Γ := Γ) p 2)
    (fun c => continuous_pull2 (Γ := Γ) p (QuotientGroup.discreteTopology U.isOpen) _
      (continuous_quotientMk' U) _)

lemma pbZfun_apply (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ)
    (c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier)))) (x : Fin 2 → Γ) :
    (pbZfun p U c).1 x = (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p)
        (QuotientGroup.mk' U.carrier (x 0), QuotientGroup.mk' U.carrier (x 1)) := by
  rw [show (pbZfun p U c).1 = pull2 (Γ := Γ) p (QuotientGroup.mk' U.carrier)
      (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p) from rfl, pull2_apply]

/-- The pullback of a `2`-cocycle is a `2`-cocycle. -/
lemma iDiff_pbZfun (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ)
    (c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier)))) : iDiff p 2 (pbZfun p U c) = 0 := by
  apply Subtype.ext
  rw [iDiff_eq_d']
  have hfun : ((inhomogeneousCochains (Aq p Γ)).d 2 3).hom (pbZfun p U c).1 = 0 := by
    rw [show (pbZfun p U c).1 = pull2 (Γ := Γ) p (QuotientGroup.mk' U.carrier)
        (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p) from rfl]
    rw [show pull2 (Γ := Γ) p (QuotientGroup.mk' U.carrier)
        (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p)
        = (rx2 p Γ).symm (Work.CFT.KochTransfer.precompFun (QuotientGroup.mk' U.carrier)
            (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p)) from rfl]
    rw [← d₂₃_comm_inv, ← precompFun_d₂₃]
    rw [show d₂₃ (Aq p (Γ ⧸ U.carrier))
        (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p) = 0 from c.2]
    rw [map_zero, map_zero]
  rw [hfun]
  rfl

/-- **The pullback of a `2`-cocycle of `Γ ⧸ U` to a continuous `2`-cocycle of `Γ`.** -/
noncomputable def pbZ (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ) :
    ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier))) →ₗ[ZMod p] iK p Γ :=
  (pbZfun p U).codRestrict (iZ p Γ) (fun c => iDiff_pbZfun p U c)

lemma pbZ_apply (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ)
    (c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier)))) (x : Fin 2 → Γ) :
    ((pbZ p U c : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1 x
      = (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p)
          (QuotientGroup.mk' U.carrier (x 0), QuotientGroup.mk' U.carrier (x 1)) := by
  rw [show ((pbZ p U c : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)) = pbZfun p U c from rfl,
    pbZfun_apply]

/-- The pullbacks of `2`-cocycles are compatible with the inflation maps. -/
lemma pbZ_natural (p : ℕ) {U V : Work.CFT.MaxProP.OpenNormal Γ} (h : U ≤ V)
    (c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier)))) :
    pbZ p V (Work.CFT.KochTransfer.precompCocycle
        (Work.CFT.MaxProP.OpenNormal.quotientMap U V h) c) = pbZ p U c := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [pbZ_apply, pbZ_apply, Work.CFT.KochTransfer.precompCocycle_apply,
    Work.CFT.KochTransfer.precompFun_apply]
  rw [OpenNormal.quotientMap_mk'_apply h (x 0), OpenNormal.quotientMap_mk'_apply h (x 1)]

/-- The pullback of a `2`-coboundary is a `2`-coboundary. -/
lemma gQ_ker_le (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ) :
    (gQ p (Γ ⧸ U.carrier)).ker ≤ ((piI (Γ := Γ) p).comp (pbZ p U)).ker := by
  intro c hc
  rw [LinearMap.mem_ker, LinearMap.comp_apply, piI_eq_zero_iff']
  have hcb : (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p) ∈
      coboundaries₂ (Aq p (Γ ⧸ U.carrier)) := (mem_gQ_ker p _ c).mp hc
  rw [coboundaries₂, LinearMap.mem_range] at hcb
  obtain ⟨w, hw⟩ := hcb
  have hkey : ((pbZ p U c : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1
      = ((inhomogeneousCochains (Aq p Γ)).d 1 2)
          ((rx1 p Γ).symm (precompFun1 p (QuotientGroup.mk' U.carrier) w)) := by
    rw [show ((pbZ p U c : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1
        = pull2 (Γ := Γ) p (QuotientGroup.mk' U.carrier)
            (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p) from rfl]
    rw [← hw]
    rw [show pull2 (Γ := Γ) p (QuotientGroup.mk' U.carrier)
        (d₁₂ (Aq p (Γ ⧸ U.carrier)) w)
        = (rx2 p Γ).symm (Work.CFT.KochTransfer.precompFun (QuotientGroup.mk' U.carrier)
            (d₁₂ (Aq p (Γ ⧸ U.carrier)) w)) from rfl]
    rw [precompFun_d₁₂, d₁₂_comm_inv]
  rw [iB]
  refine LinearMap.mem_range.mpr ⟨⟨(rx1 p Γ).symm (precompFun1 p (QuotientGroup.mk' U.carrier) w),
    ?_⟩, ?_⟩
  · rw [show (rx1 p Γ).symm (precompFun1 p (QuotientGroup.mk' U.carrier) w)
        = pull1 (Γ := Γ) p (QuotientGroup.mk' U.carrier) w from rfl]
    exact continuous_pull1 (Γ := Γ) p (QuotientGroup.discreteTopology U.isOpen) _
      (continuous_quotientMk' U) w
  · apply Subtype.ext
    rw [iDiff_eq_d', hkey]

/-- The pullback of `2`-cocycles induces a map `H²(Γ ⧸ U, 𝔽_p) → H²(iComplex)`. -/
noncomputable def pbConc (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ) :
    H2Conc p (Γ ⧸ U.carrier) →ₗ[ZMod p] iConc p Γ :=
  (Submodule.liftQ (gQ p (Γ ⧸ U.carrier)).ker
      ((piI (Γ := Γ) p).comp (pbZ p U)) (gQ_ker_le p U)).comp
    (LinearMap.quotKerEquivOfSurjective (gQ p (Γ ⧸ U.carrier))
      (gQ_surjective p _)).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
lemma pbConc_apply (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ)
    (c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier)))) :
    pbConc p U (gQ p (Γ ⧸ U.carrier) c) = piI (Γ := Γ) p (pbZ p U c) := by
  have h1 : ((LinearMap.quotKerEquivOfSurjective (gQ p (Γ ⧸ U.carrier))
      (gQ_surjective p _)).symm.toLinearMap) (gQ p (Γ ⧸ U.carrier) c)
        = Submodule.Quotient.mk c :=
    LinearMap.quotKerEquivOfSurjective_symm_apply _ _ c
  rw [pbConc, LinearMap.comp_apply, h1, Submodule.liftQ_apply]
  rfl

/-- A continuous `2`-cocycle is killed by the inhomogeneous differential `d 2 3`. -/
lemma iZ_d_zero (p : ℕ) (z : ↥(iZ p Γ)) :
    ((inhomogeneousCochains (Aq p Γ)).d 2 3).hom (z : ↥(iCochain (Γ := Γ) p 2)) = 0 := by
  have h : iDiff (Γ := Γ) p 2 (show ↥(iCochain (Γ := Γ) p 2) from z) = 0 :=
    LinearMap.mem_ker.mp z.2
  simpa using (iDiff_eq_zero_iff p 2 (show ↥(iCochain (Γ := Γ) p 2) from z)).mp h

set_option backward.isDefEq.respectTransparency false in
/-- The inflation squares are compatible with the identification `H2ConcEquiv` of `H²` with its
concrete model: the transition maps `contMap` correspond to the pullback of `2`-cocycles. -/
lemma contMap_H2ConcEquiv_symm (p : ℕ) {U W : Work.CFT.MaxProP.OpenNormal Γ} (h : U ≤ W)
    (c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier)))) :
    Work.CFT.MaxProP.contMap p Γ U W h
        ((H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) c))
      = (H2ConcEquiv p (Γ ⧸ W.carrier)).symm
          (gQ p (Γ ⧸ W.carrier) (Work.CFT.KochTransfer.precompCocycle
            (Work.CFT.MaxProP.OpenNormal.quotientMap U W h) c)) := by
  rw [show (H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) c)
      = groupCohomology.H2π (Aq p (Γ ⧸ U.carrier)) c from by
    rw [gQ_apply, LinearEquiv.symm_apply_apply]]
  rw [show Work.CFT.MaxProP.contMap p Γ U W h = Work.CFT.KochTransfer.infl
      (Work.CFT.MaxProP.OpenNormal.quotientMap U W h) from rfl,
    Work.CFT.KochTransfer.infl_H2π]
  rw [show (H2ConcEquiv p (Γ ⧸ W.carrier)).symm
      (gQ p (Γ ⧸ W.carrier) (Work.CFT.KochTransfer.precompCocycle
        (Work.CFT.MaxProP.OpenNormal.quotientMap U W h) c))
      = groupCohomology.H2π (Aq p (Γ ⧸ W.carrier)) (Work.CFT.KochTransfer.precompCocycle
        (Work.CFT.MaxProP.OpenNormal.quotientMap U W h) c) from by
    rw [gQ_apply, LinearEquiv.symm_apply_apply]]

/-- The pullback of `1`-cochains along `Γ → Γ ⧸ W` evaluated on a function that factors through
`Γ ⧸ V` with `V ≤ W`. -/
lemma pull1_eq_of_factor (p : ℕ) {V W : Work.CFT.MaxProP.OpenNormal Γ} (h : V ≤ W)
    (bV : (Fin 1 → Γ ⧸ V.carrier) → ZMod p) (b : ↥(iCochain (Γ := Γ) p 1))
    (hb : ∀ x : Fin 1 → Γ, b.1 x = bV (fun i => QuotientGroup.mk (x i))) :
    b.1 = pull1 (Γ := Γ) p (QuotientGroup.mk' W.carrier)
      (fun y : Γ ⧸ W.carrier =>
        bV (fun _ : Fin 1 => Work.CFT.MaxProP.OpenNormal.quotientMap V W h y)) := by
  funext x
  rw [hb, pull1_apply]
  rw [show Work.CFT.MaxProP.OpenNormal.quotientMap V W h (QuotientGroup.mk' W.carrier (x 0))
      = QuotientGroup.mk' V.carrier (x 0) from OpenNormal.quotientMap_mk'_apply h (x 0)]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The value of `pbZ` on an element presented as a pair `⟨c, hc⟩`. -/
lemma pbZ_mk_apply (p : ℕ) (U : Work.CFT.MaxProP.OpenNormal Γ)
    (c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p)
    (hc : c ∈ cocycles₂ (Aq p (Γ ⧸ U.carrier))) (x : Fin 2 → Γ) :
    ((pbZ p U ⟨c, hc⟩ : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1 x
      = c (QuotientGroup.mk' U.carrier (x 0), QuotientGroup.mk' U.carrier (x 1)) := by
  rw [pbZ_apply]
  rfl

/-- The differential `d₁₂` on `Γ × Γ` expressed through the reindexing `rx2`. -/
lemma d₁₂_eq_rx2 (p : ℕ) (y : Γ → ZMod p) :
    d₁₂ (Aq p Γ) y = (rx2 p Γ)
      ((inhomogeneousCochains (Aq p Γ)).d 1 2 ((rx1 p Γ).symm y)) := by
  rw [← LinearEquiv.apply_symm_apply (rx2 p Γ) (d₁₂ (Aq p Γ) y), d₁₂_comm_inv]

end

end Work.CFTLib.ContCohomology
