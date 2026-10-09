import Mathlib
import Submission.Work.SSGRoute.Nakayama.br_pTorsion
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PT.H2Transfer
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PTembedding.hilbert90_decomp
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.SSGRoute.exists_openSubgroup_comap_le
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
import Submission.Work.SSGRoute.PT.cardH2Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open Work.AbsoluteKummer

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## The structural reduction: open subgroups of `D_A` are decomposition groups over number
fields -/

/-- **Every open subgroup of a decomposition group is the decomposition group over a number
field.**  For `U ≤ D_A = decomp k A` open there is a finite extension `K/k` inside `Ω` with
`U = D_A ∩ Gal(Ω/K)`.

Proof.  `Ũ := U.map (decomp k A).subtype` is closed in `Gal(Ω/k)` (an open subgroup of the compact
group `↥(decomp k A)`, pushed forward along the continuous inclusion), so its fixed field `L` has
`L.fixingSubgroup = Ũ`.  A Krull basis argument (`exists_openSubgroup_comap_le` plus
`krullTopology_mem_nhds_one_iff`) produces `K₀/k` finite with
`D_A ∩ G_{K₀} ≤ Ũ`, whence `L ≤ K₀ ⊔ F₀` (`F₀ = Ω^{D_A}`), so `[L : F₀] < ∞`.  A finite set `S`
generating `L` over `F₀` gives `K := k(S)`, finite over `k`, with `K ⊔ F₀ = L`; then
`D_A ∩ Gal(Ω/K) = (K ⊔ F₀).fixingSubgroup = L.fixingSubgroup = Ũ`. -/
theorem exists_numberField_decomp_eq (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧
      U.map (SSGRoute.decomp k A).subtype = SSGRoute.decomp k A ⊓ K.fixingSubgroup := by
  classical
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hAlgΩ : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  set F₀ : IntermediateField k Ω := Work.SSGRoute.mup.decompField k Ω A with hF₀
  have hF₀fix : F₀.fixingSubgroup = SSGRoute.decomp k A :=
    Work.SSGRoute.PTembedding.fixingSubgroup_decompField k Ω A
  -- `Ũ` is closed
  have hŨclosed : IsClosed ((U.map (SSGRoute.decomp k A).subtype : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := isClosed_map_subtype_decomp_of_isOpen A hA U hU
  -- `L = Ω^Ũ`
  set L : IntermediateField k Ω := IntermediateField.fixedField (U.map (SSGRoute.decomp k A).subtype)
    with hL
  have hLfix : L.fixingSubgroup = U.map (SSGRoute.decomp k A).subtype :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨_, hŨclosed⟩
  -- the Krull basis: some finite `K₀` with `D_A ⊓ G_{K₀} ≤ Ũ`
  obtain ⟨K₀, hK₀fin, hK₀le⟩ : ∃ K₀ : IntermediateField k Ω, FiniteDimensional k K₀ ∧
      SSGRoute.decomp k A ⊓ K₀.fixingSubgroup ≤ U.map (SSGRoute.decomp k A).subtype := by
    obtain ⟨V, hVopen, hVle⟩ :=
      Work.SSGRoute.exists_openSubgroup_comap_le (K := k) (L := Ω) (SSGRoute.decomp k A) U hU
    obtain ⟨K₀, hK₀fin, hK₀le⟩ :=
      (krullTopology_mem_nhds_one_iff k Ω V).mp (hVopen.mem_nhds V.one_mem)
    refine ⟨K₀, hK₀fin, ?_⟩
    intro σ hσ
    obtain ⟨hσD, hσK⟩ := hσ
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσD⟩, hVle (by
      rw [Subgroup.mem_comap]
      exact hK₀le hσK), rfl⟩
  haveI hK₀finI : FiniteDimensional k ↥K₀ := hK₀fin
  -- `F₀ ≤ L`
  have hŨle : U.map (SSGRoute.decomp k A).subtype ≤ F₀.fixingSubgroup := by
    rw [hF₀fix]
    exact (Subgroup.map_le_iff_le_comap).mpr (fun x _ => x.2)
  have hF₀leL : F₀ ≤ L :=
    (IntermediateField.le_iff_le (U.map (SSGRoute.decomp k A).subtype) F₀).mpr hŨle
  -- `L ≤ K₀ ⊔ F₀`
  have hsub : (K₀ ⊔ F₀).fixingSubgroup ≤ L.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, hF₀fix, hLfix, inf_comm]
    exact hK₀le
  have hLle : L ≤ K₀ ⊔ F₀ := by
    calc L = IntermediateField.fixedField L.fixingSubgroup :=
          (InfiniteGalois.fixedField_fixingSubgroup L).symm
      _ ≤ IntermediateField.fixedField (K₀ ⊔ F₀).fixingSubgroup :=
          IntermediateField.fixedField_le hsub
      _ = K₀ ⊔ F₀ := InfiniteGalois.fixedField_fixingSubgroup (K₀ ⊔ F₀)
  -- `[L : F₀]` is finite
  haveI hMfin : FiniteDimensional ↥F₀ ↥(relField F₀ (K₀ ⊔ F₀) le_sup_right) :=
    finiteDimensional_relField_sup F₀ K₀
  haveI hLfin : FiniteDimensional ↥F₀ ↥(relField F₀ L hF₀leL) := by
    have hle' : relField F₀ L hF₀leL ≤ relField F₀ (K₀ ⊔ F₀) le_sup_right := hLle
    let f : ↥(relField F₀ L hF₀leL) →ₗ[↥F₀] ↥(relField F₀ (K₀ ⊔ F₀) le_sup_right) :=
      { toFun := fun x => ⟨(x : Ω), hle' x.2⟩
        map_add' := fun x y => Subtype.ext rfl
        map_smul' := fun c x => Subtype.ext rfl }
    refine FiniteDimensional.of_injective f ?_
    intro x y h
    refine Subtype.ext ?_
    show (x : Ω) = (y : Ω)
    exact congrArg (Subtype.val : ↥(relField F₀ (K₀ ⊔ F₀) le_sup_right) → Ω) h
  -- a finite generating set of `L` over `F₀`
  obtain ⟨S, hSfin, hSgen⟩ : ∃ S : Set Ω, S.Finite ∧
      IntermediateField.adjoin ↥F₀ S = relField F₀ L hF₀leL :=
    exists_finite_generating_set _
  haveI hSfinI : Finite S := hSfin
  have hInt : ∀ x ∈ S, IsIntegral k x := fun x _ => IsAlgebraic.isIntegral (hAlgΩ.isAlgebraic x)
  haveI hKfin : FiniteDimensional k ↥(IntermediateField.adjoin k S) :=
    IntermediateField.finiteDimensional_adjoin hInt
  refine ⟨IntermediateField.adjoin k S, hKfin, ?_⟩
  have hKsup : F₀ ⊔ IntermediateField.adjoin k S = L := by
    apply SetLike.coe_injective
    show ((F₀ ⊔ IntermediateField.adjoin k S : IntermediateField k Ω) : Set Ω) = (L : Set Ω)
    have h := congrArg (fun M : IntermediateField k Ω => (M : Set Ω))
      (IntermediateField.restrictScalars_adjoin_eq_sup (F := k) (K := F₀) (S := S))
    rw [IntermediateField.coe_restrictScalars, hSgen] at h
    rw [relField_coe] at h
    exact h.symm
  have h2 : SSGRoute.decomp k A ⊓ (IntermediateField.adjoin k S).fixingSubgroup
      = L.fixingSubgroup := by
    rw [← hF₀fix, ← IntermediateField.fixingSubgroup_sup, hKsup]
  exact (h2.trans hLfix).symm

/-! ## The transfer of `H²` along the identification `U = D_A ⊓ Gal(Ω/K)` -/

/-- The two natural actions of a Galois group and of a smaller one on the units agree when the
automorphisms agree as functions. -/
theorem algEquivUnitsMapOfField_congr {k F Ω : Type} [Field k] [Field F] [Field Ω] [Algebra k Ω]
    [Algebra F Ω] [Algebra k F] [IsScalarTower k F Ω] (σ : Ω ≃ₐ[k] Ω) (τ : Ω ≃ₐ[F] Ω)
    (h : ∀ x : Ω, τ x = σ x) (u : Units Ω) :
    algEquivUnitsMapOfField k Ω σ u = algEquivUnitsMapOfField F Ω τ u := by
  refine Units.ext ?_
  simp only [algEquivUnitsMapOfField_coe]
  exact (h (u : Ω)).symm

/-- The `p`-torsion of an abelian group is transported by an additive equivalence. -/
theorem natCard_ptorsion_eq_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (p : ℕ) :
    Nat.card {x : A // p • x = 0} = Nat.card {x : B // p • x = 0} := by
  have hns : ∀ (n : ℕ) (a : A), e (n • a) = n • e a :=
    fun n a => map_nsmul e.toAddMonoidHom n a
  refine Nat.card_congr (Equiv.ofBijective (fun y : {x : A // p • x = 0} =>
    (⟨e y.1, by rw [← hns p y.1, y.2, map_zero]⟩ : {x : B // p • x = 0})) ?_)
  refine ⟨?_, ?_⟩
  · intro y₁ y₂ h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro z
    have hz : p • (e.symm z.1) = 0 := by
      have h1 : e (p • (e.symm z.1)) = 0 := by
        rw [hns p (e.symm z.1), AddEquiv.apply_symm_apply, z.2]
      exact (AddEquiv.map_eq_zero_iff e).mp h1
    exact ⟨⟨e.symm z.1, hz⟩, Subtype.ext (AddEquiv.apply_symm_apply e z.1)⟩

/-- **The `p`-torsion of the local Brauer group at an arbitrary open subgroup of a decomposition
group** — Milne, *ADT*, (1.1b) at the level `U`: for `A` a finite place of `Ω = k̄` over the number
field `k` and `U ≤ D_A = decomp k A` an open subgroup, the `p`-torsion of `H²(U, \bar k^×)` has
exactly `p` elements.

The case `U = D_A` is `Work.SSGRoute.Nakayama.br_pTorsion`.  Mathematically: `U` is closed in
`Gal(Ω/k)` with `U = Gal(Ω/Ω^U)`, so `H²(U, Ω^×)` is the `p`-torsion of the Brauer group of a
finite extension of the local field `k_v`, hence `ℤ/p`.

Formal proof: by `exists_numberField_decomp_eq` there is a number field `K ⊆ Ω` (finite over `k`)
with `U = D_A ∩ Gal(Ω/K)`; the base-change isomorphism of decomposition groups
(`Work.SSGRoute.decompEquiv_fok`, a homeomorphism) identifies `U` with `decomp ↥K A`, and
`H²` is transported along this homeomorphism of profinite groups (`PT.h2Transfer`, with the
identity coefficient equivalence); finally `br_pTorsion` at the number field `↥K` computes the
`p`-torsion. -/
theorem cardH2_units_openSubgroup_decomp
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) :
    Nat.card {x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • x = 0} = p := by
  classical
  obtain ⟨K, hKfin, hUeq⟩ := exists_numberField_decomp_eq k Ω A hA U hU
  haveI hKfinI : FiniteDimensional k ↥K := hKfin
  -- the base-change of the decomposition group to the number field `↥K`
  haveI hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hAlgK : Algebra.IsAlgebraic ↥K Ω := inferInstance
  haveI hAlgClK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  have hAK : SSGRoute.IsFinPlace ↥K A := by
    intro h
    apply hA
    rw [eq_top_iff]
    intro x _
    rw [ValuationSubring.mem_comap]
    have hx : algebraMap k ↥K x ∈ A.comap (algebraMap ↥K Ω) := by rw [h]; trivial
    rwa [ValuationSubring.mem_comap] at hx
  have hbr := Work.SSGRoute.Nakayama.br_pTorsion p ↥K Ω A hAK
  -- the group identification `U ≃* decomp ↥K A`
  set V : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup with hV
  have hVle : V ≤ SSGRoute.decomp k A := inf_le_left
  have hUV : U = V.subgroupOf (SSGRoute.decomp k A) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rw [← hUeq]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      rw [← hUeq] at hx
      obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hx
      have : u = x := Subtype.ext hu'
      rwa [this] at hu
  have hEx : ∀ y : ↥V, ∃ u : ↥U, (u : Ω ≃ₐ[k] Ω) = (y : Ω ≃ₐ[k] Ω) := by
    intro y
    have hy : (y : Ω ≃ₐ[k] Ω) ∈ U.map (SSGRoute.decomp k A).subtype := by
      rw [hUeq]; exact y.2
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨u, hu⟩, hu'⟩
  let toV : ↥U → ↥V := fun x => ⟨(x : Ω ≃ₐ[k] Ω), by
    have hx : (x : Ω ≃ₐ[k] Ω) ∈ U.map (SSGRoute.decomp k A).subtype :=
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
    rwa [hUeq] at hx⟩
  have htoV : ∀ x : ↥U, ((toV x : ↥V) : Ω ≃ₐ[k] Ω) = (x : Ω ≃ₐ[k] Ω) := fun _ => rfl
  let e₁ : ↥U ≃* ↥V :=
    { toFun := toV
      invFun := fun y => Classical.choose (hEx y)
      left_inv := fun x =>
        Subtype.ext (Subtype.ext ((Classical.choose_spec (hEx (toV x))).trans (htoV x)))
      right_inv := fun y =>
        Subtype.ext ((htoV (Classical.choose (hEx y))).trans (Classical.choose_spec (hEx y)))
      map_mul' := fun x y => Subtype.ext rfl }
  have he₁ : IsHomeomorph (e₁ : ↥U → ↥V) := by
    haveI hcD : CompactSpace ↥(SSGRoute.decomp k A) := by
      haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
      have hc : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
        Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A
      exact isCompact_iff_compactSpace.mp hc.isCompact
    haveI hcU : CompactSpace ↥U := by
      have hUc : IsClosed (U : Set ↥(SSGRoute.decomp k A)) := Subgroup.isClosed_of_isOpen U hU
      exact isCompact_iff_compactSpace.mp hUc.isCompact
    refine (isHomeomorph_iff_continuous_bijective).mpr ⟨?_, e₁.bijective⟩
    refine Continuous.subtype_mk (f := fun x : ↥U => ((e₁ x : ↥V) : Ω ≃ₐ[k] Ω)) ?_ (fun x => (e₁ x).2)
    show Continuous (fun x : ↥U => (((x : ↥U) : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω))
    exact continuous_subtype_val.comp continuous_subtype_val
  let e₂ : ↥V ≃* ↥(SSGRoute.decomp ↥K A) := Work.SSGRoute.decompEquiv_fok k Ω K A
  have he₂ : IsHomeomorph (e₂ : ↥V → ↥(SSGRoute.decomp ↥K A)) :=
    Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A
  let e : ↥U ≃* ↥(SSGRoute.decomp ↥K A) := e₁.trans e₂
  have he : IsHomeomorph (e : ↥U → ↥(SSGRoute.decomp ↥K A)) :=
    NK.Mine.isHomeomorph_trans e₁ e₂ he₁ he₂
  -- compatibility of the coefficient actions
  have hcompat : ∀ (g' : ↥U) (m' : Additive (Units Ω)),
      (AddEquiv.refl (Additive (Units Ω))) (g' • m') =
        e g' • (AddEquiv.refl (Additive (Units Ω))) m' := by
    intro g' m'
    obtain ⟨u, rfl⟩ := Additive.ofMul.surjective m'
    simp only [AddEquiv.refl_apply]
    rw [show g' • Additive.ofMul u
        = (((g' : ↥U) : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • Additive.ofMul u from rfl,
      show e g' • Additive.ofMul u
        = ((e g' : ↥(SSGRoute.decomp ↥K A)) : Ω ≃ₐ[↥K] Ω) • Additive.ofMul u from rfl]
    exact congrArg Additive.ofMul (algEquivUnitsMapOfField_congr (k := k) (F := ↥K) _ _
      (fun x => rfl) u)
  -- the transfer
  have htr : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) ≃+
      Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp ↥K A) (Additive (Units Ω)) :=
    h2Transfer (G' := ↥U) (G := ↥(SSGRoute.decomp ↥K A))
      (M' := Additive (Units Ω)) (M := Additive (Units Ω)) e he (AddEquiv.refl _) hcompat
  rw [natCard_ptorsion_eq_of_addEquiv htr p]
  exact hbr

end

end Work.SSGRoute.PT
