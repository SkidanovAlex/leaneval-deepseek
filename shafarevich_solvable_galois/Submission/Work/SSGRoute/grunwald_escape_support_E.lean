import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import Submission.Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionL1K
import Submission.Work.SSGRoute.local_transport
import Submission.Work.SSGRoute.overK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD 09-30: new Step-4 route (design: _NOTE_STEP4_DESIGN.md at the workspace root; read the section for your node). step4_yLarge_exists was FALSE (it asks for an everywhere-unramified y); Step4YPrescribed with the escape at D.Λ is right. Frattini argument for i ≥ 2 (N1), Grünwald with escape (N2, pairing-free; do NOT use kummerChar_eq_zero_iff_local_powClass, which has a sorry), the E-valued version (N3), local data (N4), and the (1,1) → (2,1) step via shafarevich_existence (N5). No Hochschild–Serre transgression and no Poitou–Tate input. Import sibling nodes you depend on (sorried until they land).
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise Topology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {p : ℕ}

/-! ## Transport of the local data along `K.fixingSubgroup ≃* Gal(ℚ̄/↥K)` -/

/-- Two `ℚ`-algebra automorphisms of `ℚ̄` with the same underlying function act in the same way on
places (the actions are the pointwise actions over `↥K` and over `ℚ`). -/
theorem ges_smul_eq_of_coe_eq {K : IntermediateField ℚ SSGRoute.QBar}
    {φ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar} {ψ : SSGRoute.GalQ} (h : ⇑φ = ⇑ψ)
    (A : ValuationSubring SSGRoute.QBar) : φ • A = ψ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩

/-- The group isomorphism `K.fixingSubgroup ≃* Gal(ℚ̄/↥K)` acts on places through the underlying
function: it preserves the `ℚ`-conjugate. -/
theorem ges_smul_fixingSubgroupEquiv (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (τ : ↥(K.fixingSubgroup)) :
    ((IntermediateField.fixingSubgroupEquiv K) τ) • A = (τ : SSGRoute.GalQ) • A :=
  ges_smul_eq_of_coe_eq (φ := (IntermediateField.fixingSubgroupEquiv K) τ)
    (ψ := (τ : SSGRoute.GalQ)) (by funext x; rfl) A

/-- `↥K`-conjugacy of places is conjugacy by an element of `K.fixingSubgroup`. -/
theorem ges_isConjPlace_iff (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A B : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsConjPlace ↥K A B ↔ ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : SSGRoute.GalQ),
      ((IntermediateField.fixingSubgroupEquiv K).symm σ).2, ?_⟩
    rw [← ges_smul_fixingSubgroupEquiv K A ((IntermediateField.fixingSubgroupEquiv K).symm σ),
      MulEquiv.apply_symm_apply]
    exact hσ
  · rintro ⟨τ, hτ, hτA⟩
    exact ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩,
      (ges_smul_fixingSubgroupEquiv K A ⟨τ, hτ⟩).trans hτA⟩

/-- An element of `decomp ↥K A` corresponds, under `fixingSubgroupEquiv`, to an element of
`decomp ℚ A` (the two places have the same decomposition group on `K.fixingSubgroup`). -/
theorem ges_decomp_of_mem (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)
    (hδ : δ ∈ SSGRoute.decomp ↥K A) :
    (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) ∈ SSGRoute.decomp ℚ A := by
  have hδ' : δ • A = A := hδ
  have hgoal : (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) • A = A := by
    rw [← ges_smul_fixingSubgroupEquiv K A ((IntermediateField.fixingSubgroupEquiv K).symm δ),
      MulEquiv.apply_symm_apply]
    exact hδ'
  exact hgoal

/-- The converse direction of `ges_decomp_of_mem`. -/
theorem ges_decomp_of_mem_gal (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup)
    (h : σ ∈ SSGRoute.decomp ℚ A) :
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) ∈ SSGRoute.decomp ↥K A := by
  have h' : σ • A = A := h
  have hgoal : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) • A = A := by
    rw [ges_smul_fixingSubgroupEquiv K A ⟨σ, hσ⟩]
    exact h'
  exact hgoal

/-- Inertia transports from the base `↥K` to the base `ℚ`. -/
theorem ges_isInertia_of_mem (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (B : ValuationSubring SSGRoute.QBar) (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)
    (hδ : SSGRoute.IsInertia ↥K B δ) :
    SSGRoute.IsInertia ℚ B
      (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) := by
  have h1 : δ ∈ SSGRoute.decomp ↥K B := hδ.1
  have h2 : ∀ x : SSGRoute.QBar, x ∈ B → B.valuation (δ x - x) < 1 := hδ.2
  exact ⟨ges_decomp_of_mem K B δ h1, fun x hx => h2 x hx⟩


/-- `fixingSubgroupEquiv K` applied to the element of `K.fixingSubgroup` underlying `δ` gives back
`δ`.  Stated with the explicit subtype so that it can be used by `rw`. -/
theorem ges_apply_symm (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) :
    (IntermediateField.fixingSubgroupEquiv K)
      (⟨(↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ),
        ((IntermediateField.fixingSubgroupEquiv K).symm δ).2⟩ : ↥(K.fixingSubgroup)) = δ := by
  rw [show (⟨(↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ),
      ((IntermediateField.fixingSubgroupEquiv K).symm δ).2⟩ : ↥(K.fixingSubgroup)) =
      (IntermediateField.fixingSubgroupEquiv K).symm δ from Subtype.ext rfl,
    MulEquiv.apply_symm_apply]

/-- Complete splitting in `L/ℚ` is invariant under `ℚ`-conjugation of the place. -/
theorem ges_isSplitIn_smul (L : IntermediateField ℚ SSGRoute.QBar) [IsGalois ℚ L]
    (Q B : ValuationSubring SSGRoute.QBar) (τ : SSGRoute.GalQ) (hτ : τ • Q = B)
    (hQ : SSGRoute.IsSplitIn ℚ L Q) : SSGRoute.IsSplitIn ℚ L B := by
  haveI hAlg : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hBar : IsGalois ℚ SSGRoute.QBar := inferInstance
  haveI h2 : IsGalois ℚ ↥L := ‹IsGalois ℚ L›
  have hNorm : (L.fixingSubgroup : Subgroup SSGRoute.GalQ).Normal :=
    @IsGalois.fixingSubgroup_normal_of_isGalois ℚ SSGRoute.QBar _ _ _ L hBar h2
  rw [← hτ]
  exact (Work.SSGRoute.isSplitIn_conj L hNorm Q τ).mpr hQ

/-- The fixing subgroup of `overK K L hKL`, seen over `ℚ`, is the fixing subgroup of `L`. -/
theorem ges_fixingSubgroup_restrictScalars_overK (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] (L : IntermediateField ℚ SSGRoute.QBar) (hKL : K ≤ L) :
    ((overK K L hKL).restrictScalars ℚ).fixingSubgroup = L.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h x (by rw [IntermediateField.mem_restrictScalars]; exact hx)
  · intro h x hx
    rw [IntermediateField.mem_restrictScalars] at hx
    exact h x hx

/-- Ramification of `B` in `L/↥K` is ramification of `B` in `L/ℚ`, expressed through the elements
of `K.fixingSubgroup`. -/
theorem ges_isRamifiedIn_overK_iff (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (L : IntermediateField ℚ SSGRoute.QBar) (hKL : K ≤ L) (B : ValuationSubring SSGRoute.QBar) :
    SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B ↔
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ ∧ σ ∉ L.fixingSubgroup := by
  rw [Work.SSGRoute.local_transport_isRamifiedIn K (overK K L hKL) B,
    ges_fixingSubgroup_restrictScalars_overK K L hKL]

/-! ## Two topological tools -/

/-- Every open subgroup `U₀` of `Gal(ℚ̄/↥K)` contains the faithful image of an open subgroup `U` of
`Gal(ℚ̄/ℚ)`: take `U` to be the fixing subgroup of a finite `ℚ`-subfield containing the finite
`↥K`-subfield cut out by `U₀`. -/
theorem ges_openSubgroup_pullback (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (U₀ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar))
    (hU₀ : IsOpen (U₀ : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar))) :
    ∃ U : Subgroup SSGRoute.GalQ, IsOpen (U : Set SSGRoute.GalQ) ∧
      ∀ x : ↥(K.fixingSubgroup), (x : SSGRoute.GalQ) ∈ U →
        (IntermediateField.fixingSubgroupEquiv K x) ∈ U₀ := by
  have hnhds : (U₀ : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∈
      𝓝 (1 : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) :=
    hU₀.mem_nhds (Subgroup.one_mem U₀)
  rw [krullTopology_mem_nhds_one_iff ↥K SSGRoute.QBar U₀] at hnhds
  obtain ⟨N, hNfin, hNU⟩ := hnhds
  haveI : FiniteDimensional ↥K N := hNfin
  have hMfin : FiniteDimensional ℚ (N.restrictScalars ℚ) := FiniteDimensional.trans ℚ ↥K ↥N
  refine ⟨(N.restrictScalars ℚ).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen (N.restrictScalars ℚ), ?_⟩
  intro x hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hx
  have hxN : ((IntermediateField.fixingSubgroupEquiv K) x) ∈ N.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact hx y (by rw [IntermediateField.mem_restrictScalars]; exact hy)
  exact hNU hxN

/-- Local constancy on `K.fixingSubgroup` (for the subspace Krull topology) transports to local
constancy on the whole of `Gal(ℚ̄/↥K)`. -/
theorem ges_isLocConstOn_transport (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    {M : Type} [AddCommGroup M] {z : SSGRoute.GalQ → M}
    (hz : SSGRoute.IsLocConstOn K.fixingSubgroup z) :
    SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar))
      (fun x => z (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ)) := by
  classical
  obtain ⟨U₀, hU₀open, hU₀⟩ := hz
  have hVopen : IsOpen ((U₀.comap (Subgroup.subtype (K.fixingSubgroup)) :
      Subgroup ↥(K.fixingSubgroup)) : Set ↥(K.fixingSubgroup)) := by
    rw [Subgroup.coe_comap]
    exact hU₀open.preimage continuous_subtype_val
  refine ⟨(U₀.comap (Subgroup.subtype (K.fixingSubgroup))).map
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom, ?_, ?_⟩
  · exact isOpen_map_fixingSubgroupEquiv K _ hVopen
  · intro x hx u hu huH
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
    have hvu₂ : (IntermediateField.fixingSubgroupEquiv K) v = u := hvu
    have hvU : (v : SSGRoute.GalQ) ∈ U₀ := by simpa using (Subgroup.mem_comap.mp hv)
    have hcoe : (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * u)) : SSGRoute.GalQ)
        = (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ) *
          (↑v : SSGRoute.GalQ) := by
      rw [← hvu₂, map_mul, MulEquiv.symm_apply_apply]
      rfl
    show z (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * u)) : SSGRoute.GalQ)
      = z (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ)
    rw [hcoe]
    exact hU₀ _ ((IntermediateField.fixingSubgroupEquiv K).symm x).2 _ hvU v.2

/-! ## The `𝔽_p`-valued datum on `G_ℚ` associated with a `↥K`-side datum -/

/-- The local datum `f A` on `Gal(ℚ̄/↥K)`, transported to `G_ℚ` by zero extension off
`K.fixingSubgroup`. -/
noncomputable def gesLocalDatum (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p)
    (A : ValuationSubring SSGRoute.QBar) (σ : SSGRoute.GalQ) : ZMod p := by
  classical
  exact if hσ : σ ∈ K.fixingSubgroup then
    f A (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩) else 0

/-- The defining property of `gesLocalDatum` on `K.fixingSubgroup`. -/
theorem gesLocalDatum_apply (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p)
    (A : ValuationSubring SSGRoute.QBar) (σ : SSGRoute.GalQ) (hσ : σ ∈ K.fixingSubgroup) :
    gesLocalDatum K f A σ = f A (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩) := by
  classical
  rw [gesLocalDatum]
  exact dif_pos hσ

/-- `gesLocalDatum` is additive on the decomposition group. -/
theorem gesLocalDatum_add (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p)
    (A : ValuationSubring SSGRoute.QBar)
    (hf : ∀ x ∈ SSGRoute.decomp ↥K A, ∀ y ∈ SSGRoute.decomp ↥K A,
      f A (x * y) = f A x + f A y)
    (x : SSGRoute.GalQ) (hx : x ∈ SSGRoute.decomp ℚ A ⊓ K.fixingSubgroup)
    (y : SSGRoute.GalQ) (hy : y ∈ SSGRoute.decomp ℚ A ⊓ K.fixingSubgroup) :
    gesLocalDatum K f A (x * y) = gesLocalDatum K f A x + gesLocalDatum K f A y := by
  classical
  have hxy : (⟨x * y, K.fixingSubgroup.mul_mem hx.2 hy.2⟩ : ↥(K.fixingSubgroup)) =
      ⟨x, hx.2⟩ * ⟨y, hy.2⟩ := Subtype.ext rfl
  have h1 : gesLocalDatum K f A (x * y) = f A ((IntermediateField.fixingSubgroupEquiv K)
      ⟨x * y, K.fixingSubgroup.mul_mem hx.2 hy.2⟩) :=
    gesLocalDatum_apply K f A (x * y) (K.fixingSubgroup.mul_mem hx.2 hy.2)
  have h2 : gesLocalDatum K f A x = f A ((IntermediateField.fixingSubgroupEquiv K)
      ⟨x, hx.2⟩) := gesLocalDatum_apply K f A x hx.2
  have h3 : gesLocalDatum K f A y = f A ((IntermediateField.fixingSubgroupEquiv K)
      ⟨y, hy.2⟩) := gesLocalDatum_apply K f A y hy.2
  rw [h1, h2, h3, hxy, map_mul]
  exact hf _ (ges_decomp_of_mem_gal K A x hx.2 hx.1) _
    (ges_decomp_of_mem_gal K A y hy.2 hy.1)

/-! ## Transporting a character of `Gal(ℚ̄/↥K)` that kills `Gal(ℚ̄/L)` -/

/-- A `ZMod p`-valued additive function on `K.fixingSubgroup` killing `L.fixingSubgroup` transports
to an additive function on `Gal(ℚ̄/↥K)` killing `Gal(ℚ̄/L)`, with the same values. -/
theorem ges_transfer_chi (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (L : IntermediateField ℚ SSGRoute.QBar) (hKL : K ≤ L)
    (χ : SSGRoute.GalQ → ZMod p)
    (hadd : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y)
    (hkill : ∀ σ ∈ L.fixingSubgroup, χ σ = 0) :
    ∃ χ' : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
      (∀ x y, χ' (x * y) = χ' x + χ' y) ∧
      (∀ δ ∈ (overK K L hKL).fixingSubgroup, χ' δ = 0) ∧
      (∀ x : ↥(K.fixingSubgroup), χ' ((IntermediateField.fixingSubgroupEquiv K) x) = χ x) := by
  refine ⟨fun δ => χ ↑((IntermediateField.fixingSubgroupEquiv K).symm δ), ?_, ?_, ?_⟩
  · intro x y
    have h1 : (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * y)) : SSGRoute.GalQ)
        = (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ) *
          (↑((IntermediateField.fixingSubgroupEquiv K).symm y) : SSGRoute.GalQ) := by
      rw [map_mul]
      rfl
    show χ (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * y)) : SSGRoute.GalQ)
      = χ ↑((IntermediateField.fixingSubgroupEquiv K).symm x)
        + χ ↑((IntermediateField.fixingSubgroupEquiv K).symm y)
    rw [h1]
    exact hadd _ ((IntermediateField.fixingSubgroupEquiv K).symm x).2 _
      ((IntermediateField.fixingSubgroupEquiv K).symm y).2
  · intro δ hδ
    refine hkill _ ?_
    rw [IntermediateField.mem_fixingSubgroup_iff] at hδ ⊢
    intro x hx
    exact hδ x hx
  · intro x
    show χ (↑((IntermediateField.fixingSubgroupEquiv K).symm
      ((IntermediateField.fixingSubgroupEquiv K) x)) : SSGRoute.GalQ) = χ ↑x
    rw [MulEquiv.symm_apply_apply]

/-! ## Grünwald with escape, case `L₁ = K` and `g = 0`

The escape core of node N2 in the specialisation used by `grunwald_escape_support_E`: the global
datum `g` is `0` and the escaping field is `L₂ = L` itself, with `L₁ = K`.

In this case the orthogonality of the correction needs no product formula.  Indeed, write `χ` for
the Kummer character of the local datum: at a place `A ∈ T` where the datum `h A` is not zero, every
character killing `Gal(Ω/L)` kills the decomposition group by hypothesis (`horth`, whose second
disjunct is exactly the `hsupp` of `grunwald_escape_support_E`), and where `h A` is zero the local
class of the Grünwald element is a `p`-th power.  The first element is Grünwald + Kummer theory
(`GrunwaldEscapeCore.grunwald_kummer_first_element`), the correction is
`GrunwaldEscapeCore.gesCorrectionL1K`, and the class realising the datum is the zero extension
`ZSplit.nodeKummerCocharZMod` of the Kummer character of the corrected element. -/

/-- **Grünwald with escape**, case `L₁ = K`, `g = 0`: the conclusion of
`Work.SSGRoute.grunwald_escape_relative_core` with `(L₁, L₂, g)` specialised to `(K, L, 0)` and the
splitting condition required on `L` alone. -/
theorem ges_smul_form_L1K (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0)) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k L Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set ζK : ↥K := ⟨ζ, hζK⟩ with hζKdef
  have hζK' : IsPrimitiveRoot ζK p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the datum `h` is realised by a Kummer element of `Kˣ` (Grünwald + Kummer theory)
  obtain ⟨a, ha⟩ :=
    GrunwaldEscapeCore.grunwald_kummer_first_element p k Ω K ζK hζK' hKimag T hTfin hTdisj
      (fun _ => 0) (fun x hx y hy => by simp)
      ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun x hx u hu hu' => rfl⟩
      h hh hhc
  -- the class-field-theoretic correction
  obtain ⟨Q, b, hQfin, hQsplit, hQnotT, hagree, hesc⟩ :=
    GrunwaldEscapeCore.gesCorrectionL1K p k Ω K ζK hζK' hKimag L hKL T hTfin hTdisj hTcov
      h hh hhc horth a (fun A hA σ => by simpa using ha A hA σ)
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, Q, hQfin, hQsplit, hQnotT, ?_, ?_, ?_, ?_⟩
  · exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
      (β := b) hσK]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσK⟩ =
        Work.SSGRoute.gesLocalToGalK K ⟨σ, hσ⟩ := rfl
    rw [hto, hagree A hA ⟨σ, hσ⟩]
    simpa using (ha A hA ⟨σ, hσ⟩).symm
  · intro B hB hnotT hnotQ σ hσ hI
    rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := b) hσ]
    have hto : (IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ =
        Work.SSGRoute.gesGalKOfFixing K σ hσ := rfl
    rw [hto]
    exact hesc B hB hnotT hnotQ σ hσ hI

/-! ## Grünwald with escape, `ZMod p`-valued -/

/-- The `ZMod p`-valued case of `grunwald_escape_support_E`, proved from
`grunwald_escape_relative` at the base field `ℚ`. -/
theorem ges_grunwald_escape_support_zmod (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring SSGRoute.QBar))
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace ↥K A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ↥K A B → A = B)
    (hTcov : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
      (B.valuation (p : SSGRoute.QBar) < 1 ∨ SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B) →
      ∃ A ∈ T, SSGRoute.IsConjPlace ↥K A B)
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p)
    (hf : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp ↥K A, ∀ y ∈ SSGRoute.decomp ↥K A,
      f A (x * y) = f A x + f A y)
    (hfc : ∀ A ∈ T, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp ↥K A → f A x = 0)
    (hsupp : ∀ A ∈ T, (∀ δ ∈ SSGRoute.decomp ↥K A, f A δ = 0) ∨
      ∀ χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y) →
        (∀ δ ∈ (overK K L hKL).fixingSubgroup, χ δ = 0) →
        ∀ δ ∈ SSGRoute.decomp ↥K A, χ δ = 0) :
    ∃ ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
      (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y) ∧
      SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε ∧
      (∀ A ∈ T, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (∀ A ∈ T, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ L B →
        ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) := by
  classical
  haveI hGalK : IsGalois ℚ K := IsGalois.mk
  haveI hAlgQ : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  obtain ⟨z, Q, _hQfin, hQsplit, _hQT, hzadd, hzloc, hzpres, hzunr⟩ :=
    @ges_smul_form_L1K p (inferInstance : Fact p.Prime) ℚ SSGRoute.QBar
      (inferInstance : Field ℚ) (inferInstance : NumberField ℚ)
      (inferInstance : Field SSGRoute.QBar) (inferInstance : Algebra ℚ SSGRoute.QBar)
      (inferInstance : IsAlgClosure ℚ SSGRoute.QBar)
      K (inferInstance : FiniteDimensional ℚ K) hGalK
      ζ hζ hζK
      (fun hp c hc hc2 => hKimag hp c hc2 hc)
      L (inferInstance : FiniteDimensional ℚ L) (inferInstance : IsGalois ℚ L) hKL
      T
      (fun A hA => (local_transport_isFinPlace K A).mp (hTfin A hA))
      (fun A hA B hB hconj => hTdisj A hA B hB ((ges_isConjPlace_iff K A B).mpr hconj))
      (fun B hB hcase => by
        have hcase' : B.valuation (p : SSGRoute.QBar) < 1 ∨
            SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B := by
          rcases hcase with h | h
          · exact Or.inl h
          · obtain ⟨σ, hσ, hI, hσnot⟩ := h
            exact Or.inr ((ges_isRamifiedIn_overK_iff K L hKL B).mpr ⟨σ, hσ, hI, hσnot⟩)
        obtain ⟨A, hA, hconj⟩ := hTcov B ((local_transport_isFinPlace K B).mpr hB) hcase'
        exact ⟨A, hA, (ges_isConjPlace_iff K A B).mp hconj⟩)
      (gesLocalDatum K f)
      (fun A hA => gesLocalDatum_add K f A (hf A hA))
      (fun A hA => by
        obtain ⟨U₀, hU₀open, hU₀⟩ := hfc A hA
        obtain ⟨U, hUopen, hUpull⟩ := ges_openSubgroup_pullback K U₀ hU₀open
        refine ⟨U, hUopen, ?_⟩
        intro x hxU hxmem
        rw [gesLocalDatum_apply K f A x hxmem.2]
        exact hU₀ _ (hUpull ⟨x, hxmem.2⟩ hxU)
          (ges_decomp_of_mem_gal K A x hxmem.2 hxmem.1))
      (fun A hA => by
        rcases hsupp A hA with hzero | hχ
        · left
          intro σ hσ
          rw [gesLocalDatum_apply K f A σ hσ.2]
          exact hzero _ (ges_decomp_of_mem_gal K A σ hσ.2 hσ.1)
        · right
          intro χ hχadd hχkill σ hσ
          obtain ⟨χ', hχ'add, hχ'kill, hχ'val⟩ := ges_transfer_chi K L hKL χ hχadd hχkill
          have h3 := hχ χ' hχ'add hχ'kill
            ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ.2⟩)
            (ges_decomp_of_mem_gal K A σ hσ.2 hσ.1)
          rw [hχ'val ⟨σ, hσ.2⟩] at h3
          exact h3)
  -- the escape place `Q` is split completely in `L = K ⊔ L`
  have hQsplitL : SSGRoute.IsSplitIn ℚ L Q := hQsplit
  refine ⟨fun x => z (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ),
    ?_, ?_, ?_, ?_⟩
  · intro x y
    have h1 : (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * y)) : SSGRoute.GalQ)
        = (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ) *
          (↑((IntermediateField.fixingSubgroupEquiv K).symm y) : SSGRoute.GalQ) := by
      rw [map_mul]
      rfl
    show z (↑((IntermediateField.fixingSubgroupEquiv K).symm (x * y)) : SSGRoute.GalQ)
      = z (↑((IntermediateField.fixingSubgroupEquiv K).symm x) : SSGRoute.GalQ)
        + z (↑((IntermediateField.fixingSubgroupEquiv K).symm y) : SSGRoute.GalQ)
    rw [h1]
    exact hzadd _ ((IntermediateField.fixingSubgroupEquiv K).symm x).2 _
      ((IntermediateField.fixingSubgroupEquiv K).symm y).2
  · exact ges_isLocConstOn_transport K hzloc
  · intro A hA δ hδ
    have hmem : (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ)
        ∈ SSGRoute.decomp ℚ A ⊓ K.fixingSubgroup :=
      ⟨ges_decomp_of_mem K A δ hδ, ((IntermediateField.fixingSubgroupEquiv K).symm δ).2⟩
    have h1 : z (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ)
        = gesLocalDatum K f A
          (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) := by
      have h2 := hzpres A hA
        (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) hmem
      simpa using h2
    show z (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ) = f A δ
    rw [h1, gesLocalDatum_apply K f A _ ((IntermediateField.fixingSubgroupEquiv K).symm δ).2,
      ges_apply_symm K δ]
  · intro B hBfin hBconj hBsplit δ hδI
    have hnotT : ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B := by
      intro A hA hconj
      exact hBconj A hA ((ges_isConjPlace_iff K A B).mpr hconj)
    have hnotQ : ¬ Work.SSGRoute.gesKConj K Q B := by
      rintro ⟨τ, hτ, hτQ⟩
      exact hBsplit (ges_isSplitIn_smul L Q B τ hτQ hQsplitL)
    exact hzunr B ((local_transport_isFinPlace K B).mp hBfin) hnotT hnotQ
      (↑((IntermediateField.fixingSubgroupEquiv K).symm δ) : SSGRoute.GalQ)
      ((IntermediateField.fixingSubgroupEquiv K).symm δ).2
      (ges_isInertia_of_mem K B δ hδI)

/-- Grünwald with escape at a field `L ⊇ K`, `E`-valued, over the base field `↥K`, in the support
form used by Step 4 and by `scholz_two_one`.

`T` is one place per prime of `K`, and covers the places over `p` and the places ramified in `L/K`.
The local datum `f A` at `A ∈ T` is additive with open kernel on `decomp ↥K A`.  At each `A ∈ T`,
either `f A` vanishes, or every additive `ZMod p`-valued function on `Gal(ℚ̄/↥K)` that kills
`Gal(ℚ̄/L)` vanishes on `decomp ↥K A`.

Conclusion: an additive, locally constant `ε : Gal(ℚ̄/↥K) → E` with the prescribed local data.  It
is unramified at every finite place outside the classes of `T` that is not completely split in
`L` over `ℚ`.

Proof: coordinatewise (as in `step4_grunwald_E_coordinatewise`) from `grunwald_escape_relative`
at `k := ℚ`, with `L₁ := K`, `L₂ := L`, `g := 0`. Its conclusion is transported from
`K.fixingSubgroup` to `Gal(ℚ̄/↥K)` by `IntermediateField.fixingSubgroupEquiv K`,
`local_transport_decomp` and `local_transport_isInertia`.  Use `L₁ ⊔ L₂ = L`. -/
theorem grunwald_escape_support_E (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring SSGRoute.QBar))
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace ↥K A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ↥K A B → A = B)
    (hTcov : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
      (B.valuation (p : SSGRoute.QBar) < 1 ∨ SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B) →
      ∃ A ∈ T, SSGRoute.IsConjPlace ↥K A B)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E)
    (hf : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp ↥K A, ∀ y ∈ SSGRoute.decomp ↥K A,
      f A (x * y) = f A x + f A y)
    (hfc : ∀ A ∈ T, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp ↥K A → f A x = 0)
    (hsupp : ∀ A ∈ T, (∀ δ ∈ SSGRoute.decomp ↥K A, f A δ = 0) ∨
      ∀ χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y) →
        (∀ δ ∈ (overK K L hKL).fixingSubgroup, χ δ = 0) →
        ∀ δ ∈ SSGRoute.decomp ↥K A, χ δ = 0) :
    ∃ ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E,
      (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y) ∧
      SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε ∧
      (∀ A ∈ T, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (∀ A ∈ T, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ L B →
        ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) := by
  classical
  have hfin : Module.Finite (ZMod p) E := Module.Finite.of_finite
  let eL : E ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) E) → ZMod p) :=
    (Module.finBasis (ZMod p) E).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin (Module.finrank (ZMod p) E)))
  -- coordinatewise construction of the `E`-valued class from the `ZMod p`-valued one
  have hcoord : ∀ k : Fin (Module.finrank (ZMod p) E),
      ∃ ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y) ∧
        SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε ∧
        (∀ A ∈ T, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = (eL (f A δ)) k) ∧
        (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
          (∀ A ∈ T, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ L B →
          ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) := by
    intro k
    refine ges_grunwald_escape_support_zmod p K ζ hζ hζK hKimag L hKL T hTfin hTdisj hTcov
      (fun A δ => (eL (f A δ)) k) ?_ ?_ ?_
    · intro A hA x hx y hy
      simp only [hf A hA x hx y hy, map_add, Pi.add_apply]
    · intro A hA
      obtain ⟨U, hUo, hU⟩ := hfc A hA
      exact ⟨U, hUo, fun x hx hx' => by simp [hU x hx hx']⟩
    · intro A hA
      rcases hsupp A hA with h | h
      · exact Or.inl (fun δ hδ => by simp [h δ hδ])
      · exact Or.inr h
  choose ε hadd hloc hpres hunr using hcoord
  refine ⟨fun x => eL.symm (fun k => ε k x), ?_, ?_, ?_, ?_⟩
  · -- additivity
    intro a b
    change eL.symm (fun k => ε k (a * b)) = eL.symm (fun k => ε k a) + eL.symm (fun k => ε k b)
    have h1 : (fun k => ε k (a * b)) = (fun k => ε k a) + (fun k => ε k b) := by
      funext k; exact hadd k a b
    rw [h1]
    exact map_add eL.symm _ _
  · -- local constancy: the finite intersection of the coordinatewise open subgroups
    have hloc' : ∀ k, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
        IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
        ∀ a ∈ (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)), ∀ u ∈ U,
          u ∈ (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) → ε k (a * u) = ε k a :=
      fun k => hloc k
    choose U hUo hU using hloc'
    refine ⟨⨅ k, U k, ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite (fun k => hUo k)
    · intro a ha u hu huH
      have hu' : ∀ k, u ∈ U k := fun k => (Subgroup.mem_iInf.mp hu) k
      have h1 : (fun k => ε k (a * u)) = (fun k => ε k a) := by
        funext k; exact hU k a ha u (hu' k) huH
      show eL.symm (fun k => ε k (a * u)) = eL.symm (fun k => ε k a)
      rw [h1]
  · -- the prescribed local data
    intro A hA δ hδ
    show eL.symm (fun k => ε k δ) = f A δ
    apply eL.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    exact hpres k A hA δ hδ
  · -- unramified outside the classes of `T`, away from the completely split places
    intro B hB hconj hsplit δ hδI
    show eL.symm (fun k => ε k δ) = 0
    rw [show (fun k => ε k δ) = 0 from funext fun k => hunr k B hB hconj hsplit δ hδI,
      map_zero]


end Work.SSGRoute
