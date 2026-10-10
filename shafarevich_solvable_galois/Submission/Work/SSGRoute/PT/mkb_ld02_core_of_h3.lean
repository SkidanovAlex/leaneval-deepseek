import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Connected.Separation
import Submission.Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor
import Submission.Work.SSGRoute.PT.br_pTorsion_openSubgroup
import Submission.Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp
import Submission.Work.SSGRoute.PT.conjHomSES_maps
import Submission.Work.SSGRoute.PT.decompK_subgroupOf_facts
import Submission.Work.SSGRoute.PT.devissageLinear
import Submission.Work.SSGRoute.PT.finite_dualMod_tensor
import Submission.Work.SSGRoute.PT.finrank_eq_of_alphaTwo_bijective
import Submission.Work.SSGRoute.PT.h3_H3_subsingleton_of_image
import Submission.Work.SSGRoute.PT.hcor_of_corH2_ptorsion
import Submission.Work.SSGRoute.PT.kummerSES
import Submission.Work.SSGRoute.PT.range_invariantsHom_eq_ker
import Submission.Work.SSGRoute.PT.resH2_eq_zero_of_index_nsmul_eq_zero
import Submission.Work.SSGRoute.PT.retraction_invariantsHom
import Submission.Work.SSGRoute.PT.retraction_range_invariantsHom
import Submission.Work.SSGRoute.PTdualControl.h3Exactness
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `mkb_ld02_core_of_h3` — Milne I.2.3 at `r = 0` from `cd_p(D_A) ≤ 2`

## Route (Milne, *ADT*, I.1.8 at `r = 2`, run through the `α²`-dévissage)

For every finite place `A` and every finite `𝔽_p[Gal(K/k)]`-module `M`, the target is obtained
from

`Function.Bijective (alphaTwo (G := ↥(decomp k A)) (N := DualMod p (M ⊗ T)) (C := Additive Ωˣ))`

via `PT.finrank_eq_of_alphaTwo_bijective`, this in turn from the `α²`-dévissage
`PT.alphaTwo_bijective_of_devissage` along the short exact sequence
`0 → N → Coind_U^{D_A} N → N₁ → 0` for `U = D_A ⊓ K.fixingSubgroup`, whose inputs are

* **base case** `hN₂` (`PT.alphaTwo_coind_bijective_of_cor`): the trivial-action base case over `U`
  (`PT.alphaTwo_trivAction_of_trivMod`, `PT.alphaTwo_trivMod_bijective`) together with
  **`hcor`**, the corestriction `cor : H²(U, Ωˣ) → H²(D_A, Ωˣ)` being bijective on the `p`-torsion
  of the invariants.  This is Milne's class-formation axiom **(1.1b)** — the compatibility
  `inv_{D_A} ∘ cor = inv_U` of the local invariant maps;
* **first pass** `hN₁` (`PT.alphaTwo_surjective_of_precomp`), again from the base case;
* **`htop`**: `Subsingleton (H³(D_A, Hom_ℤ(N₁, Ωˣ)))`, from `h3` (`PT.h3_H3_conjHom_subsingleton`);
* **`hbot`/`hg'`**: the exactness of the dual of the invariants sequence, from the retraction
  lemmas.

## Status

`hcor` is the single genuinely missing input: for `p ∤ [D_A : U]` it follows from
`PT.corH2_resH2_eq_index` plus the two `p`-torsion cardinalities
(`Nakayama.br_pTorsion`, `PT.br_pTorsion_openSubgroup_v2`), and that is
`PT.corH2_ptorsion_bijective_of_coprime_index`.  When `p | [D_A : K₀]` (`K₀` the kernel of the
action of `D_A` on `N`) no `U ⊆ K₀` has index prime to `p`, and `hcor` needs the genuine
invariant-map compatibility, which is *not yet formalised* in this workspace.  Building it is the
remaining obligation.
-/

open Classical

namespace Work.SSGRoute.PT
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- `ConjHom.precomp` is contravariant. -/
theorem mkb_precomp_comp {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    {C : Type} [AddCommGroup C] (φ : N₁ →+ N₂) (ψ : N₂ →+ N₃) :
    (ConjHom.precomp (C := C) φ).comp (ConjHom.precomp (C := C) ψ)
      = ConjHom.precomp (C := C) (ψ.comp φ) := by
  apply AddMonoidHom.ext
  intro f
  apply ConjHom.ext_apply
  intro n
  rfl

/-- `ConjHom.precomp` of the zero map is zero. -/
theorem mkb_precomp_zero {N₁ N₂ : Type} [AddCommGroup N₁] [AddCommGroup N₂] {C : Type}
    [AddCommGroup C] :
    ConjHom.precomp (C := C) (0 : N₁ →+ N₂) = 0 := by
  apply AddMonoidHom.ext
  intro f
  apply ConjHom.ext_apply
  intro n
  simp

/-- `mapH2` of the zero coefficient map is zero. -/
theorem mkb_mapH2_zero {M N : Type} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup N] [DistribMulAction G N]
    (h : Work.GroupCohomology.IsEquivariant G (0 : M →+ N)) :
    Work.AbsoluteKummer.mapH2 (0 : M →+ N) h = 0 := by
  apply AddMonoidHom.ext
  intro x
  show Work.AbsoluteKummer.mapH2 (0 : M →+ N) h x = 0
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  rw [← hc]
  show Work.AbsoluteKummer.H2π G N (Work.AbsoluteKummer.mapZ2 (0 : M →+ N) h c) = 0
  rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
  have hz : ((Work.AbsoluteKummer.mapZ2 (0 : M →+ N) h c :
      Work.AbsoluteKummer.Z2 G N) : G × G → N) = 0 := by
    funext p
    rw [Work.AbsoluteKummer.mapZ2_apply]
    rfl
  rw [hz]
  exact (Work.AbsoluteKummer.B2 G N).zero_mem

/-- `Ext³ = 0` makes the coefficient map on `H²` surjective. -/
theorem mkb_mapH2_surjective_of_subsingleton_H3 {M N P : Type} [AddCommGroup M]
    [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N] [AddCommGroup P]
    [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (h3 : Subsingleton (Work.SSGRoute.H3 (M := M) G)) :
    Function.Surjective (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant) := by
  rw [← AddMonoidHom.range_eq_top, Work.SSGRoute.range_mapH2_eq_ker_deltaH3 S]
  rw [AddSubgroup.eq_top_iff']
  intro x
  rw [AddMonoidHom.mem_ker]
  exact Subsingleton.elim (S.deltaH3 x) 0


/-! ## Hilbert 90 at an open subgroup of a decomposition group -/

/-- **Hilbert 90 at an open subgroup of a decomposition group**: `H¹(U, Ωˣ) = 0`.  Mirrors
`Work.SSGRoute.PTembedding.MupCard.hilbert90_decompH1`, using
`Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup` for the closed subgroup `U ≤ Gal(Ω/k)`. -/
theorem mkb_hilbert90_openSubgroup
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A))) :
    Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) := by
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hCZ : CharZero k := inferInstance
  have hDcl : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.PTembedding.isClosed_decomp' k Ω A
  have hUcl : IsClosed (U : Set ↥(SSGRoute.decomp k A)) := Subgroup.isClosed_of_isOpen U hUo
  have hHcl : IsClosed ((U.map (Subgroup.subtype (SSGRoute.decomp k A)) :
      Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.PT.bropenIsClosedMapSubtype (SSGRoute.decomp k A) hDcl U hUcl
  have h90 : Subsingleton (Work.AbsoluteKummer.H1
      ↥(U.map (Subgroup.subtype (SSGRoute.decomp k A))) (Additive (Units Ω))) :=
    Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup (k := k) (Ω := Ω) _ hHcl
  have hΦ : IsHomeomorph ((Work.SSGRoute.PT.bropenSubgroupMapValEquiv (SSGRoute.decomp k A) U :
      ↥U → ↥(U.map (Subgroup.subtype (SSGRoute.decomp k A))))) :=
    Work.SSGRoute.PT.bropenIsHomeomorphSubgroupMapValEquiv (SSGRoute.decomp k A) hDcl U hUcl
  have h := Work.SSGRoute.PT.h1Transfer
    (G := ↥(U.map (Subgroup.subtype (SSGRoute.decomp k A)))) (G' := ↥U)
    (M := Additive (Units Ω)) (M' := Additive (Units Ω))
    (Work.SSGRoute.PT.bropenSubgroupMapValEquiv (SSGRoute.decomp k A) U) hΦ
    (AddEquiv.refl (Additive (Units Ω))) (fun _ _ => rfl)
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩

/-! ## Discreteness of `Additive Ωˣ` over an open subgroup of `D_A` -/

/-- **Discreteness of `Additive Ωˣ` over an open subgroup `U ≤ D_A`.**  The stabiliser of a unit
is the preimage of its stabiliser in `Gal(Ω/k)`, an open subgroup because `Ω/k` is algebraic. -/
theorem mkb_isDiscreteModule_units_openSubgroup
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (U : Subgroup ↥(SSGRoute.decomp k A)) :
    Work.AbsoluteKummer.IsDiscreteModule ↥U (Additive (Units Ω)) := by
  have hD : Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A) (Additive (Units Ω)) :=
    Work.SSGRoute.PTembedding.MupCard.isDiscreteModule_decomp_addUnits (k := k) (Ω := Ω) A
  intro c
  show IsOpen (MulAction.stabilizer ↥U c : Set ↥U)
  have hset : (MulAction.stabilizer ↥U c : Set ↥U)
      = Subtype.val ⁻¹' ((MulAction.stabilizer ↥(SSGRoute.decomp k A) c) :
          Set ↥(SSGRoute.decomp k A)) := by
    ext u
    show (u : ↥U) • c = c ↔ (u : ↥(SSGRoute.decomp k A)) • c = c
    exact Iff.rfl
  rw [hset]
  exact (hD c).preimage continuous_subtype_val

/-! ## The base case of the dévissage over `U` -/

/-- **The base case of the `α²`-dévissage over `U`.**  For a finite `𝔽_p[U]`-module `N` with
trivial `U`-action and `C = Additive Ωˣ`, the map `α²(U, N)` is bijective — Kummer plus Hilbert 90
at `U` (`PT.kummerSES`, `PT.alphaTwo_trivMod_bijective`, `PT.alphaTwo_trivAction_of_trivMod`). -/
theorem mkb_alphaTwo_base_of_trivAction
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction ↥U N] [Finite N]
    (htriv : ∀ (u : ↥U) (n : N), u • n = n) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥U) (N := N)
      (C := Additive (Units Ω))) := by
  haveI : IsTopologicalGroup ↥U := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- the coefficient module `Additive Ωˣ` is `p`-divisible and discrete
  have hdiv : ∀ c : Additive (Units Ω), ∃ c' : Additive (Units Ω), p • c' = c := by
    intro c
    obtain ⟨c', hc'⟩ := Work.SSGRoute.PTembedding.MupCard.powPi_surjective (p := p) (Ω := Ω) c
    exact ⟨c', by rw [← Work.SSGRoute.PTembedding.MupCard.powPi_eq_nsmul (p := p) (Ω := Ω)]; exact hc'⟩
  have hdisc : Work.AbsoluteKummer.IsDiscreteModule ↥U (Additive (Units Ω)) :=
    mkb_isDiscreteModule_units_openSubgroup k Ω A U
  have h1 : Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) :=
    mkb_hilbert90_openSubgroup k Ω A hA U hUo
  -- the Kummer sequence and the trivial-coefficient base case
  obtain ⟨S, hSι, hSπ⟩ := Work.SSGRoute.PT.kummerSES (G := ↥U) p hdiv hdisc
  have hTrivMod : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥U)
      (N := Work.SSGRoute.PT.TrivMod ↥U p) (C := Additive (Units Ω))) :=
    Work.SSGRoute.PT.alphaTwo_trivMod_bijective (G := ↥U) p S hSι hSπ h1
  exact Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod (G := ↥U) p htriv hTrivMod

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

set_option linter.unusedSectionVars false

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- The coefficient sequence of a short exact sequence of `G`-modules is a complex on `H²`. -/
theorem mkb_hcomp_of_comp_eq_zero {C : Type} [AddCommGroup C] [DistribMulAction G C]
    {N N₁ N₂ : Type} [AddCommGroup N] [DistribMulAction G N]
    [AddCommGroup N₁] [DistribMulAction G N₁] [AddCommGroup N₂] [DistribMulAction G N₂]
    (φ : N →+ N₂) (ψ : N₂ →+ N₁) (hψφ : ψ.comp φ = 0)
    (hpreφ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ))
    (hpreψ : Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) ψ)) :
    ∀ x : Work.AbsoluteKummer.H2 G (ConjHom N₁ C),
      Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) φ) hpreφ
        (Work.AbsoluteKummer.mapH2 (ConjHom.precomp (C := C) ψ) hpreψ x) = 0 := by
  intro x
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G (ConjHom N₁ C)).comap
      (Work.AbsoluteKummer.Z2 G (ConjHom N₁ C)).subtype) x
  rw [← hc]
  show Work.AbsoluteKummer.H2π G (ConjHom N C)
      (Work.AbsoluteKummer.mapZ2 (ConjHom.precomp (C := C) φ) hpreφ
        (Work.AbsoluteKummer.mapZ2 (ConjHom.precomp (C := C) ψ) hpreψ c)) = 0
  rw [Work.AbsoluteKummer.H2π_eq_zero_iff]
  have hz : (Work.AbsoluteKummer.mapZ2 (ConjHom.precomp (C := C) φ) hpreφ
      (Work.AbsoluteKummer.mapZ2 (ConjHom.precomp (C := C) ψ) hpreψ c) :
        Work.AbsoluteKummer.Z2 G (ConjHom N C)) = 0 := by
    refine Subtype.ext (funext fun p => ?_)
    rw [Work.AbsoluteKummer.mapZ2_apply, Work.AbsoluteKummer.mapZ2_apply]
    have hcomm : (ConjHom.precomp (C := C) φ)
          ((ConjHom.precomp (C := C) ψ) ((c : G × G → ConjHom N₁ C) p))
        = (ConjHom.precomp (C := C) (ψ.comp φ)) ((c : G × G → ConjHom N₁ C) p) := by
      rw [← AddMonoidHom.comp_apply, mkb_precomp_comp (C := C) φ ψ]
    rw [hcomm, hψφ, mkb_precomp_zero (C := C)]
    simp
  rw [hz]
  exact (Work.AbsoluteKummer.B2 G (ConjHom N C)).zero_mem


/-- `hbot` from a retraction of the range of the second map. -/
theorem mkb_precompHom_ker_le_range_of_retraction {A B C X : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup X]
    (f : A →+ B) (g : B →+ C) (hgk : f.range = g.ker)
    (r : C →+ ↥(g.range)) (hr : ∀ x : ↥(g.range), r (x : C) = x) :
    (precompHom (X := X) f).ker ≤ (precompHom (X := X) g).range := by
  intro χ hχ
  have hχ' : ∀ a : A, χ (f a) = 0 := by
    intro a
    have h := congrArg (fun (t : A →+ X) => t a) (AddMonoidHom.mem_ker.mp hχ)
    simpa using h
  obtain ⟨θ, hθ⟩ := ker_le_range_precompHom f g hgk r hr χ hχ'
  exact ⟨θ, hθ⟩

/-- `hg'` from a retraction. -/
theorem mkb_precompHom_surjective_of_retraction {A B X : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup X] (f : A →+ B) (r : B →+ A) (hr : ∀ x : A, r (f x) = x) :
    Function.Surjective (precompHom (X := X) f) := by
  intro χ
  refine ⟨χ.comp r, ?_⟩
  ext x
  show χ (r (f x)) = χ x
  rw [hr x]



/-- **`hcor` from the bijectivity of `cor` on the `p`-torsion.**  This is the bridge from the
arithmetic input (Milne, *ADT*, (1.1b) at `p`-torsion, i.e.
`Work.SSGRoute.PT.corH2_bijective_units_openSubgroup`) to the `hcor` hypothesis of
`Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor`: since the coefficient module `N` has exponent
`p`, every hom `φ : N^U →+ H²(U,C)` takes values in the `p`-torsion, so bijectivity of `cor` on the
`p`-torsion is exactly postcomposition by `cor` being bijective. -/
theorem mkb_hcor_of_corBij_ptorsion
    (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {N : Type} [AddCommGroup N] [DistribMulAction U N] (hNp : ∀ n : N, p • n = 0)
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (hc : Function.Bijective (fun z : {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} =>
      (⟨Work.SSGRoute.PT.corH2 U hUo C z.1, by rw [← map_nsmul, z.2, map_zero]⟩ :
        {x : Work.AbsoluteKummer.H2 G C // p • x = 0}))) :
    Function.Bijective (fun φ : ↥(Work.GroupCohomology.invariants U N) →+
        Work.AbsoluteKummer.H2 ↥U C => (Work.SSGRoute.PT.corH2 U hUo C).comp φ) := by
  refine comp_bijective_of_ptorsion_bijective p (V := ↥(Work.GroupCohomology.invariants U N))
    (fun v => ?_) (Work.SSGRoute.PT.corH2 U hUo C) hc
  exact Subtype.ext (hNp (v : N))

/-- **The base case `α²(G, Coind_U^G N)` of the dévissage, from the `p`-torsion form of the
corestriction input.**  Composite of `mkb_hcor_of_corBij_ptorsion` with
`Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor`. -/
theorem mkb_alphaTwo_coind_bijective
    (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {M : Type} [AddCommGroup M] [DistribMulAction U M]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (hc : Function.Bijective (fun z : {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} =>
      (⟨Work.SSGRoute.PT.corH2 U hUo C z.1, by rw [← map_nsmul, z.2, map_zero]⟩ :
        {x : Work.AbsoluteKummer.H2 G C // p • x = 0})))
    (hNp : ∀ n : M, p • n = 0)
    (hU : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := U) (N := M) (C := C))) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := G)
      (N := Work.SSGRoute.PT.Coind G U M) (C := C)) :=
  Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor (M := M) (C := C) U hUo
    (mkb_hcor_of_corBij_ptorsion p U hUo hNp hc) hU


/-! ## Triviality of the `U`-action on the coinduced module and its quotient -/

/-- **`U` acts trivially on `Coind_U^G N`** when `U ⊴ G` and `U` acts trivially on `N`.
With `(g • f) x = f (g⁻¹ * x)` (`PT.Coind.smul_apply`) and `f (g * u) = u⁻¹ • f g`
(`PT.Coind.coe_mul`), for `u ∈ U` one gets
`(u • f) x = f (u⁻¹ * x) = f (x * (x⁻¹ * u⁻¹ * x)) = (x⁻¹ * u⁻¹ * x)⁻¹ • f x = f x`. -/
theorem mkb_coind_smul_triv {G : Type} [Group G] {U : Subgroup G} [U.Normal]
    {N : Type} [AddCommGroup N] [DistribMulAction U N]
    (htriv : ∀ (u : U) (n : N), u • n = n) :
    ∀ (u : ↥U) (f : Work.SSGRoute.PT.Coind G U N), u • f = f := by
  intro u f
  ext x
  show f ((((u : ↥U) : G))⁻¹ * x) = f x
  have hw : x⁻¹ * (((u : ↥U) : G))⁻¹ * x ∈ U :=
    (inferInstance : U.Normal).conj_mem' ((((u : ↥U) : G))⁻¹) (U.inv_mem u.2) x
  let w : ↥U := ⟨x⁻¹ * (((u : ↥U) : G))⁻¹ * x, hw⟩
  have hwcoe : (w : G) = x⁻¹ * (((u : ↥U) : G))⁻¹ * x := rfl
  have hx : ((((u : ↥U) : G))⁻¹) * x = x * (w : G) := by
    rw [hwcoe]
    group
  calc f ((((u : ↥U) : G))⁻¹ * x)
      = f (x * (w : G)) := congrArg f hx
    _ = f x := by
      rw [Work.SSGRoute.PT.Coind.coe_mul f x w]
      exact htriv w⁻¹ (f x)

end Work.SSGRoute.PT
