import Mathlib
import Submission.NK.NUV2.ArtinBridge.levelPairIso
import Submission.NK.NUV2.ArtinBridge.isPGroup_sup_of_isPGroup
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.Reconstruct.ellRestrict_comp
import Submission.NK.Reconstruct.ellRestrict_surjective

/-!
# `LevelPairIso` implies the canonical Artin datum

`NK.NUV2.ArtinBridge.CanonicalArtinDatum K Ω ℓ` asks for a *coherent* system of Artin maps
`art L : C_K →* Γ_{L,ℓ}` on the `ℓ`-levels `L/K` of `Ω`, with kernel `N_{L/K}C_L` and surjective;
`NK.NUV2.ArtinBridge.LevelPairIso K Ω ℓ` asks, at every `ℓ`-level `M`, for an isomorphism
`C_K ⧸ N_{M/K}C_M ≅ Gal(M/K)^ab` taking the image of `N_{L/K}C_L` onto the kernel of the
restriction `Gal(M/K)^ab → Gal(L/K)^ab`, for every `ℓ`-sublevel `L ⊆ M`.

This file proves the implication `LevelPairIso K Ω ℓ → CanonicalArtinDatum K Ω ℓ` advertised in
the docstring of `Submission/Work/NUV2/ArtinBridge/levelPairIso.lean`.

## The construction, and why it is not a formal consequence of the levelwise data

The levelwise isomorphisms of `LevelPairIso` are only asserted to *exist*, and the systems
obtained from them at different levels need not be compatible with the transition maps: if `L ⊆ M`
are `ℓ`-levels and `e_M`, `e_L` are the chosen isomorphisms, then `e_L^{-1} ∘ r_{L,M} ∘ e_M` and
the quotient map `C_K ⧸ N_L → C_K ⧸ N_M` differ by an automorphism of `C_K ⧸ N_L` in general.
So a coherent system cannot be assembled level by level.

What can be done is:

* for a *single* level `N` and any `ℓ`-sublevel `L ⊆ N`, the restriction
  `art^N_L := ellRestrict L N ∘ e_N ∘ mk_N : C_K →* Γ_{L,ℓ}` has kernel `N_{L/K}C_L` and is
  surjective — so it is one of the admissible maps at level `L` (this is where the monotonicity
  `N_{N/K}C_N ⊆ N_{L/K}C_L` of the norm subgroups is used);
* these maps are *coherent*: `art^N_L = ellRestrict L M ∘ art^N_M` for `L ⊆ M ⊆ N`
  (functoriality of `ellRestrict`);
* hence every finite set of levels admits a coherent assignment of admissible maps, namely the
  one induced by the compositum of the levels in question — which *is* an `ℓ`-level
  (`NK.NUV2.ArtinBridge.isPGroup_sup_of_isPGroup`), so the `ℓ`-levels are directed.

A global coherent system is then extracted from the finite satisfiability by an ultrafilter
limit: fix an ultrafilter `U` on the directed set of `ℓ`-levels refining the filter of cofinal
sets, and set

  `art L (c) := lim_U (art^N_L (c))_{N ⊇ L}`

(the target is finite, so the ultralimit is a well-defined value).  This is a homomorphism
because ultralimits in a finite group commute with multiplication, and it is coherent because
`art^N_L = ellRestrict L M ∘ art^N_M` holds for *all* `N ⊇ M`.  Its kernel is computed from the
kernels of the `art^N_L`, all of which are `N_{L/K}C_L`.

## Main result

* `NK.NUV2.ArtinBridge.canonicalArtinDatum_of_levelPairIso` — the requested implication.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT (IdeleClassGroup)

noncomputable section

/-! ## 1. Ultrafilter limits of functions into finite types -/

/-- **An ultrafilter limit in a finite type**: for an ultrafilter `U` on `ι` and a function
`f : ι → β` into a finite type, some value is attained on a `U`-large set. -/
theorem exists_mem_preimage_eq {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β]
    (f : ι → β) : ∃ b : β, {i | f i = b} ∈ U := by
  classical
  letI := Fintype.ofFinite β
  have key : ∀ s : Finset β, (⋃ b ∈ s, {i | f i = b}) ∈ U →
      ∃ b ∈ s, {i | f i = b} ∈ U := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro h
      have h0 : (⋃ b ∈ (∅ : Finset β), {i | f i = b}) = (∅ : Set ι) := by simp
      rw [h0] at h
      exact absurd h (Ultrafilter.empty_notMem (f := U))
    | insert a s ha ih =>
      intro h
      rw [Finset.set_biUnion_insert] at h
      rcases Ultrafilter.union_mem_iff.mp h with h1 | h2
      · exact ⟨a, Finset.mem_insert_self a s, h1⟩
      · obtain ⟨b, hb, hbm⟩ := ih h2
        exact ⟨b, Finset.mem_insert_of_mem hb, hbm⟩
  have hcov : (⋃ b ∈ (Finset.univ : Finset β), {i | f i = b}) = Set.univ := by
    ext i; simp
  obtain ⟨b, -, hb⟩ := key Finset.univ (by rw [hcov]; exact Filter.univ_mem)
  exact ⟨b, hb⟩

/-- The value of `f` along the ultrafilter `U`, for `f` with values in a finite type. -/
def ulim {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] (f : ι → β) : β :=
  Classical.choose (exists_mem_preimage_eq U f)

/-- The defining property of the ultralimit: it is attained on a `U`-large set. -/
theorem ulim_spec {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] (f : ι → β) :
    {i | f i = ulim U f} ∈ U :=
  Classical.choose_spec (exists_mem_preimage_eq U f)

/-- A value attained on a `U`-large set is the ultralimit. -/
theorem ulim_eq {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] {f : ι → β} {b : β}
    (h : {i | f i = b} ∈ U) : ulim U f = b := by
  have h1 := ulim_spec U f
  have h2 := Filter.inter_mem h1 h
  obtain ⟨i, hi1, hi2⟩ := Filter.nonempty_of_mem h2
  simp only [Set.mem_setOf_eq] at hi1 hi2
  rw [← hi1, hi2]

/-- Two functions agreeing on a `U`-large set have the same ultralimit. -/
theorem ulim_congr {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] {f g : ι → β}
    (h : {i | f i = g i} ∈ U) : ulim U f = ulim U g := by
  have h1 := ulim_spec U f
  have h2 : {i | g i = ulim U f} ∈ U := by
    refine Filter.mem_of_superset (Filter.inter_mem h1 h) ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    rw [← hi.2, hi.1]
  exact (ulim_eq U h2).symm

/-- The ultralimit is multiplicative (for a finite *group* of values). -/
theorem ulim_mul {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] [Group β]
    (f g : ι → β) : ulim U (fun i => f i * g i) = ulim U f * ulim U g := by
  refine ulim_eq U ?_
  refine Filter.mem_of_superset (Filter.inter_mem (ulim_spec U f) (ulim_spec U g)) ?_
  intro i hi
  obtain ⟨h1, h2⟩ := hi
  show f i * g i = ulim U f * ulim U g
  rw [h1, h2]

/-- The ultralimit is natural with respect to a homomorphism into a finite group. -/
theorem ulim_map {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] {γ : Type*} [Finite γ]
    [MulOneClass β] [MulOneClass γ] (φ : β →* γ) (f : ι → β) :
    ulim U (fun i => φ (f i)) = φ (ulim U f) := by
  refine ulim_eq U ?_
  refine Filter.mem_of_superset (ulim_spec U f) ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  rw [hi]

/-- The ultralimit of a constant function. -/
theorem ulim_const {ι : Type*} (U : Ultrafilter ι) {β : Type*} [Finite β] (b : β) :
    ulim U (fun _ : ι => b) = b := by
  refine ulim_eq U ?_
  have : {i : ι | (fun _ : ι => b) i = b} = Set.univ := by ext i; simp
  rw [this]; exact Filter.univ_mem

/-! ## 1b. Monotonicity of the norm subgroups in an intermediate field

For `E ≤ F` finite intermediate fields of `Ω/K` one has `N_{F/K}C_F ≤ N_{E/K}C_E`, by the
transitivity of the norm `N_{F/K} = N_{E/K} ∘ N_{F/E}`.  This is the one number-theoretic input of
the construction: it is what makes the candidate map `ellRestrict x y ∘ e_y ∘ mk_y` at a level `x`
built from a larger level `y` have kernel exactly `N_{x/K}C_x` (the kernel of the image of the
norm group `N_{x/K}C_x` in `C_K ⧸ N_{y/K}C_y` is `N_{x/K}C_x · N_{y/K}C_y = N_{x/K}C_x`).

The on-disk theorem `NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower` is stated for a tower of
*extension types* `K ⊆ L ⊆ M`; here `E ≤ F` are subfields of `Ω`, so the tower structure
`Algebra ↥E ↥F` (there is no instance for it in Mathlib) and the accompanying `IsScalarTower` and
`FiniteDimensional ↥E ↥F` instances are supplied by hand.  The finiteness is proved from a
`K`-basis of `F`: the same finite set spans `F` over the larger field `E`. -/

section NormMono

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]

/-- **Monotonicity of the norm subgroup of the idèle class group in an intermediate field.** -/
theorem normClassSubgroup_le_of_le (E F : IntermediateField K Ω) (h : E ≤ F)
    [FiniteDimensional K E] [NumberField ↥E] [FiniteDimensional K F] [NumberField ↥F] :
    NK.GlobalCFT.Idele.normClassSubgroup K ↥F ≤
      NK.GlobalCFT.Idele.normClassSubgroup K ↥E := by
  letI : Algebra ↥E ↥F := RingHom.toAlgebra (IntermediateField.inclusion h).toRingHom
  have hAM : ∀ x : K, (algebraMap ↥E ↥F) (algebraMap K ↥E x) = algebraMap K ↥F x := by
    intro x
    exact (IntermediateField.inclusion h).commutes x
  haveI : IsScalarTower K ↥E ↥F := by
    constructor
    intro x y z
    simp only [Algebra.smul_def]
    rw [map_mul, hAM x]
    ring
  haveI : Module.Finite ↥E ↥F := by
    let b := Module.finBasis K ↥F
    let phi : (Fin (Module.finrank K ↥F) → ↥E) →ₗ[↥E] ↥F :=
      { toFun := fun v => ∑ i, v i • b i
        map_add' := by
          intro v w
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro a v
          simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply]
          rfl }
    refine Module.Finite.of_surjective phi ?_
    intro y
    refine ⟨fun i => algebraMap K ↥E (b.repr y i), ?_⟩
    show (∑ i, (algebraMap K ↥E) (b.repr y i) • b i) = y
    conv_rhs => rw [← b.sum_repr y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, hAM, Algebra.smul_def]
  exact NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower

end NormMono

/-! ## 2. The directed system of `ℓ`-levels -/

section Levels

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The bottom level `K ⊆ Ω` is an `ℓ`-level for every `ℓ`. -/
theorem subsingleton_gal_bot :
    Subsingleton (↥(⊥ : IntermediateField K Ω) ≃ₐ[K] ↥(⊥ : IntermediateField K Ω)) := by
  constructor
  intro f g
  ext x
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp x.2
  have hx : x = algebraMap K ↥(⊥ : IntermediateField K Ω) k := Subtype.ext hk.symm
  rw [hx, f.commutes, g.commutes]

/-- The bottom level as a `FrobLevel`. -/
noncomputable def botFrobLevel : NK.Reconstruct.FrobLevel K Ω where
  L := ⊥
  finite := inferInstance
  normal := inferInstance
  numberField := inferInstance

/-- **The type of `ℓ`-levels of `Ω/K`**: the finite normal levels whose Galois group over `K` is
an `ℓ`-group.  These are the levels at which `CanonicalArtinDatum` requires an Artin map. -/
abbrev EllLevel (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω]
    (ℓ : ℕ) := {L : NK.Reconstruct.FrobLevel K Ω // IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L)}

instance instPreorderEllLevel : Preorder (EllLevel K Ω ℓ) where
  le x y := x.1.L ≤ y.1.L
  le_refl _ := le_rfl
  le_trans _ _ _ h1 h2 := le_trans h1 h2

/-- The bottom level is an `ℓ`-level, so the `ℓ`-levels are nonempty. -/
noncomputable def botEllLevel : EllLevel K Ω ℓ :=
  ⟨botFrobLevel, by
    haveI : Subsingleton (Gal(↥(⊥ : IntermediateField K Ω)/K)) :=
      subsingleton_gal_bot (K := K) (Ω := Ω)
    show IsPGroup ℓ (Gal(↥(⊥ : IntermediateField K Ω)/K))
    exact IsPGroup.of_subsingleton ℓ _⟩

/-- **The `ℓ`-levels are directed**: the compositum of two `ℓ`-levels is an `ℓ`-level
(`NK.NUV2.ArtinBridge.isPGroup_sup_of_isPGroup`). -/
theorem ellLevel_directed (x y : EllLevel K Ω ℓ) :
    ∃ z : EllLevel K Ω ℓ, x ≤ z ∧ y ≤ z :=
  ⟨⟨x.1.sup y.1, isPGroup_sup_of_isPGroup ℓ x.1 y.1 x.2 y.2⟩,
    NK.Reconstruct.FrobLevel.le_sup_left x.1 y.1,
    NK.Reconstruct.FrobLevel.le_sup_right x.1 y.1⟩

end Levels

/-! ## 3. The candidate maps and their kernel

For an `ℓ`-level `x` and any `ℓ`-level `y ⊇ x`, the composite
`art^y_x := ellRestrict x y ∘ e_y ∘ mk_y : C_K →* Γ_{x,ℓ}` is an admissible map at level `x`.
-/

section Candidate

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The Artin isomorphism at an `ℓ`-level, chosen from `LevelPairIso`. -/
def artIso (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L ≃*
      NK.Reconstruct.LevelAbelianization x.1.L :=
  Classical.choose (h x.1 x.2)

/-- The defining property of the chosen Artin isomorphism: the image of the norm subgroup
`N_{L/K}C_L` under it is the kernel of the restriction map. -/
theorem artIso_spec (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ)
    (L : NK.Reconstruct.FrobLevel K Ω) (hL : IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L))
    (hle : L.L ≤ x.1.L) :
    Subgroup.map (artIso h x).toMonoidHom
      (Subgroup.map (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L))
        (NK.GlobalCFT.Idele.normClassSubgroup K ↥L.L)) =
      (NK.Reconstruct.levelRestrict L x.1 hle).ker :=
  Classical.choose_spec (h x.1 x.2) L hL hle

/-- The chosen Artin isomorphism, viewed as a map into the `ℓ`-part of the abelianisation (which
is all of it, the level being an `ℓ`-level). -/
def artIsoPart (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    IdeleClassGroup K →* ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) :=
  ((artIso h x).toMonoidHom.comp
      (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L))).codRestrict
    (NK.Reconstruct.LevelEllPart x.1.L ℓ) (fun _ => by
      have htop : NK.Reconstruct.LevelEllPart x.1.L ℓ = ⊤ :=
        ellPart_abelianization_eq_top ℓ x.2
      rw [htop]
      exact Subgroup.mem_top _)

theorem artIsoPart_coe (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) (c : IdeleClassGroup K) :
    ((artIsoPart h x c : ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ)) :
        NK.Reconstruct.LevelAbelianization x.1.L) =
      artIso h x (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L) c) := rfl

/-- The kernel of the chosen Artin isomorphism, viewed as a map into the `ℓ`-part, is the norm
subgroup `N_{x/K}C_x`. -/
theorem artIsoPart_ker (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    (artIsoPart h x).ker = NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L := by
  rw [artIsoPart, MonoidHom.ker_codRestrict, MonoidHom.ker_comp_of_injective _ _
    (artIso h x).injective]
  exact QuotientGroup.ker_mk' _

theorem artIsoPart_surjective (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    Function.Surjective (artIsoPart h x) := by
  intro z
  obtain ⟨q, hq⟩ := (artIso h x).surjective (z : NK.Reconstruct.LevelAbelianization x.1.L)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨c, Subtype.ext (by rw [artIsoPart_coe]; exact hq)⟩

/-- The candidate Artin map at the level `x` obtained from the Artin isomorphism at a larger
level `y ⊇ x`. -/
def artCandidate (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (hxy : x ≤ y) :
    IdeleClassGroup K →* ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) :=
  (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy).comp (artIsoPart h y)

theorem artCandidate_apply (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (hxy : x ≤ y)
    (c : IdeleClassGroup K) :
    artCandidate h x y hxy c =
      (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artIsoPart h y c) := rfl

/-- The candidate map is independent of the chosen proof of `x ≤ y`. -/
theorem artCandidate_congr (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (h₁ h₂ : x ≤ y) :
    artCandidate h x y h₁ = artCandidate h x y h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- **The candidate map at level `x` built from the level `y ⊇ x` has kernel `N_{x/K}C_x`.**

This uses the kernel condition of `LevelPairIso` at the level `y`, together with the monotonicity
`N_{y/K}C_y ⊆ N_{x/K}C_x` of the norm subgroups. -/
theorem artCandidate_ker (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (hxy : x ≤ y) :
    (artCandidate h x y hxy).ker = NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L := by
  have hmono : NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L ≤
      NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L :=
    normClassSubgroup_le_of_le x.1.L y.1.L hxy
  have key : ∀ z : ↥(NK.Reconstruct.LevelEllPart y.1.L ℓ),
      (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) z = 1 ↔
        ((z : NK.Reconstruct.LevelAbelianization y.1.L)) ∈
          (NK.Reconstruct.levelRestrict x.1 y.1 hxy).ker := by
    intro z
    rw [MonoidHom.mem_ker]
    constructor
    · intro hz
      have h1 : ((NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) z :
          NK.Reconstruct.LevelAbelianization x.1.L) = 1 := by rw [hz]; rfl
      rwa [NK.Reconstruct.ellRestrict_coe] at h1
    · intro hz
      exact Subtype.ext (by rw [NK.Reconstruct.ellRestrict_coe]; exact hz)
  ext c
  rw [MonoidHom.mem_ker, artCandidate_apply h x y hxy c, key (artIsoPart h y c),
    artIsoPart_coe, ← artIso_spec h y x x.2 hxy, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hae⟩
    rw [Subgroup.mem_map] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have hbc : QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L) b =
        QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L) c := by
      rw [hba]
      exact (artIso h y).injective hae
    have h1 : QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L) (b⁻¹ * c)
        = 1 := by
      rw [map_mul, map_inv, hbc, inv_mul_cancel]
    have hmem : b⁻¹ * c ∈ NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L := by
      rw [← QuotientGroup.ker_mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L),
        MonoidHom.mem_ker]
      exact h1
    have hc' : c = b * (b⁻¹ * c) := by group
    rw [hc']
    exact Subgroup.mul_mem _ hb (hmono hmem)
  · intro hc
    exact ⟨QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥y.1.L) c,
      Subgroup.mem_map_of_mem _ hc, rfl⟩

theorem artCandidate_surjective (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (hxy : x ≤ y) :
    Function.Surjective (artCandidate h x y hxy) :=
  (NK.Reconstruct.ellRestrict_surjective ℓ hxy).comp (artIsoPart_surjective h y)

/-- **Coherence of the candidate maps**: the candidate at level `x` obtained from a level `z`
agrees with the candidate at level `x` obtained from an intermediate level `y`, restricted. -/
theorem artCandidate_comp (h : LevelPairIso K Ω ℓ) (x y z : EllLevel K Ω ℓ) (hxy : x ≤ y)
    (hyz : y ≤ z) :
    artCandidate h x z (hxy.trans hyz) =
      (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy).comp (artCandidate h y z hyz) := by
  have h1 : NK.Reconstruct.ellRestrict ℓ x.1 z.1 (hxy.trans hyz) =
      (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy).comp
        (NK.Reconstruct.ellRestrict ℓ y.1 z.1 hyz) :=
    (NK.Reconstruct.ellRestrict_comp ℓ hxy hyz).symm
  rw [artCandidate, artCandidate, h1, MonoidHom.comp_assoc]

end Candidate

/-! ## 4. The ultrafilter limit over the cofinal system of levels -/

section Construction

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The cofinal filter of the (directed) system of `ℓ`-levels. -/
def cofinalFilter : Filter (EllLevel K Ω ℓ) :=
  ⨅ x : EllLevel K Ω ℓ, Filter.principal {y | x ≤ y}

theorem cofinalFilter_neBot : (cofinalFilter (K := K) (Ω := Ω) (ℓ := ℓ)).NeBot := by
  haveI : Nonempty (EllLevel K Ω ℓ) := ⟨botEllLevel⟩
  refine Filter.iInf_neBot_of_directed' ?_ ?_
  · intro x y
    obtain ⟨z, hxz, hyz⟩ := ellLevel_directed x y
    exact ⟨z, Filter.principal_mono.mpr (fun w hw => le_trans hxz hw),
      Filter.principal_mono.mpr (fun w hw => le_trans hyz hw)⟩
  · intro x
    exact Filter.principal_neBot_iff.mpr ⟨x, by show x ≤ x; exact le_rfl⟩

/-- **The ultrafilter used for the limit**: an ultrafilter on the `ℓ`-levels containing every
cofinal set `{N | x ≤ N}`.  Its existence is the properness of `cofinalFilter`, i.e. the
directedness of the `ℓ`-levels. -/
def chosenUltrafilter : Ultrafilter (EllLevel K Ω ℓ) :=
  haveI : (cofinalFilter (K := K) (Ω := Ω) (ℓ := ℓ)).NeBot :=
    cofinalFilter_neBot (K := K) (Ω := Ω) (ℓ := ℓ)
  Ultrafilter.of (cofinalFilter (K := K) (Ω := Ω) (ℓ := ℓ))

/-- Every cofinal set is large for `chosenUltrafilter`. -/
theorem mem_cofinalFilter_le (x : EllLevel K Ω ℓ) :
    {y : EllLevel K Ω ℓ | x ≤ y} ∈ chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) := by
  haveI : (cofinalFilter (K := K) (Ω := Ω) (ℓ := ℓ)).NeBot :=
    cofinalFilter_neBot (K := K) (Ω := Ω) (ℓ := ℓ)
  refine Filter.le_def.mp (Ultrafilter.of_le (cofinalFilter (K := K) (Ω := Ω) (ℓ := ℓ)))
    _ ?_
  exact Filter.mem_iInf_of_mem x (Filter.mem_principal.mpr subset_rfl)

/-- The net whose ultralimit defines the Artin map at a level.  Off the cofinal set it is given
the junk value `1`; this is irrelevant because the cofinal set is large. -/
def artNet (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) (c : IdeleClassGroup K) :
    EllLevel K Ω ℓ → ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) := by
  classical
  exact fun N => if hxN : x ≤ N then artCandidate h x N hxN c else 1

/-- **The value of the Artin map at a level `x`**: the ultralimit of the candidate values. -/
def artFun (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) (c : IdeleClassGroup K) :
    ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) :=
  ulim (chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ)) (artNet h x c)

theorem artFun_mul (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) (c c' : IdeleClassGroup K) :
    artFun h x (c * c') = artFun h x c * artFun h x c' := by
  classical
  have hfun : artNet h x (c * c') = fun N => artNet h x c N * artNet h x c' N := by
    funext N
    by_cases hxN : x ≤ N
    · simp only [artNet, dif_pos hxN, map_mul]
    · simp only [artNet, dif_neg hxN, one_mul]
  rw [artFun, hfun, ulim_mul]
  rfl

theorem artFun_one (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    artFun h x 1 = (1 : ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ)) := by
  classical
  have hfun : artNet h x 1 = fun _ : EllLevel K Ω ℓ =>
      (1 : ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ)) := by
    funext N
    by_cases hxN : x ≤ N
    · simp only [artNet, dif_pos hxN, map_one]
    · simp only [artNet, dif_neg hxN]
  rw [artFun, hfun]
  exact ulim_const _ _

/-- The Artin map at a level `x`. -/
def artHom (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    IdeleClassGroup K →* ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) where
  toFun := artFun h x
  map_one' := artFun_one h x
  map_mul' := artFun_mul h x

/-- **The kernel of the Artin map at a level is the norm group at that level.** -/
theorem artFun_eq_one_iff (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ)
    (c : IdeleClassGroup K) :
    artFun h x c = 1 ↔ c ∈ NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L := by
  classical
  constructor
  · intro hc
    have h1 : {N : EllLevel K Ω ℓ | artNet h x c N = 1} ∈
        chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) := by
      rw [← hc]; exact ulim_spec _ _
    have h2 : {N : EllLevel K Ω ℓ | x ≤ N} ∈
        chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) :=
      mem_cofinalFilter_le x
    obtain ⟨N, hN1, hN2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
    have hN2' : x ≤ N := hN2
    simp only [Set.mem_ofPred_eq] at hN1
    simp only [artNet, dif_pos hN2'] at hN1
    have hmem : c ∈ (artCandidate h x N hN2').ker := MonoidHom.mem_ker.mpr hN1
    rwa [artCandidate_ker h x N hN2'] at hmem
  · intro hc
    have hconst : artNet h x c = fun _ : EllLevel K Ω ℓ =>
        (1 : ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ)) := by
      funext N
      by_cases hxN : x ≤ N
      · simp only [artNet, dif_pos hxN]
        have hmem : c ∈ (artCandidate h x N hxN).ker := by
          rwa [artCandidate_ker h x N hxN]
        exact MonoidHom.mem_ker.mp hmem
      · simp only [artNet, dif_neg hxN]
    rw [artFun, hconst]
    exact ulim_const _ _

theorem artHom_ker (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    (artHom h x).ker = NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L := by
  ext c
  rw [MonoidHom.mem_ker]
  show artFun h x c = 1 ↔ c ∈ NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L
  exact artFun_eq_one_iff h x c

/-- **Coherence of the Artin maps.** -/
theorem artFun_coherent (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (hxy : x ≤ y)
    (c : IdeleClassGroup K) :
    (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artFun h y c) = artFun h x c := by
  classical
  have hA : {N : EllLevel K Ω ℓ | y ≤ N} ∈ chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) :=
    mem_cofinalFilter_le y
  have hB : {N : EllLevel K Ω ℓ | artNet h y c N = artFun h y c} ∈
      chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) := ulim_spec _ _
  have hC : {N : EllLevel K Ω ℓ | artNet h x c N = artFun h x c} ∈
      chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) := ulim_spec _ _
  have hD : {N : EllLevel K Ω ℓ |
      artNet h x c N =
        (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artNet h y c N)} ∈
      chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ) := by
    refine Filter.mem_of_superset (Filter.inter_mem hA (Filter.inter_mem hB hC)) ?_
    intro N hN
    obtain ⟨hNy, -, -⟩ := hN
    have hNy' : y ≤ N := hNy
    show artNet h x c N = (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artNet h y c N)
    simp only [artNet, dif_pos (hxy.trans hNy'), dif_pos hNy']
    rw [artCandidate_comp h x y N hxy hNy']
    rfl
  have h1 : artFun h x c =
      ulim (chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ))
        (fun N => (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artNet h y c N)) :=
    ulim_congr _ hD
  have h2 : ulim (chosenUltrafilter (K := K) (Ω := Ω) (ℓ := ℓ))
        (fun N => (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artNet h y c N)) =
      (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy) (artFun h y c) :=
    ulim_map _ _ _
  exact (h1.trans h2).symm

theorem artHom_coherent (h : LevelPairIso K Ω ℓ) (x y : EllLevel K Ω ℓ) (hxy : x ≤ y) :
    artHom h x = (NK.Reconstruct.ellRestrict ℓ x.1 y.1 hxy).comp (artHom h y) := by
  refine MonoidHom.ext (fun c => ?_)
  exact (artFun_coherent h x y hxy c).symm

/-- **Surjectivity of the Artin map at a level.**  It has kernel `N_{x/K}C_x`, so it induces an
injection `C_K ⧸ N_{x/K}C_x ↪ Γ_{x,ℓ}` between finite groups of the same order (the order being
the same by `LevelPairIso` at the level `x`); an injective endomorphism of a finite group is
surjective. -/
theorem artHom_surjective (h : LevelPairIso K Ω ℓ) (x : EllLevel K Ω ℓ) :
    Function.Surjective (artHom h x) := by
  classical
  let ee : IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L ≃*
      ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) :=
    (artIso h x).trans ((MulEquiv.subgroupCongr
      (ellPart_abelianization_eq_top ℓ x.2)).trans Subgroup.topEquiv).symm
  haveI : Finite (IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L) :=
    Finite.of_equiv _ ee.symm.toEquiv
  let lift : IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K ↥x.1.L →*
      ↥(NK.Reconstruct.LevelEllPart x.1.L ℓ) :=
    QuotientGroup.lift _ (artHom h x) (by rw [artHom_ker h x])
  have hcomp : lift.comp (QuotientGroup.mk' _) = artHom h x := QuotientGroup.lift_comp_mk' _ _ _
  have hinj : Function.Injective lift := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, artHom_ker h x,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hψ : Function.Injective (ee.symm.toMonoidHom.comp lift) :=
    ee.symm.injective.comp hinj
  have hψs : Function.Surjective (ee.symm.toMonoidHom.comp lift) :=
    (Finite.injective_iff_surjective).mp hψ
  have hls : Function.Surjective lift := by
    intro y
    obtain ⟨w, hw⟩ := hψs (ee.symm y)
    refine ⟨w, ?_⟩
    have h2 : ee (ee.symm (lift w)) = ee (ee.symm y) := congrArg (fun z => ee z) hw
    simpa using h2
  intro y
  obtain ⟨w, hw⟩ := hls y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ w
  exact ⟨c, by rw [← DFunLike.congr_fun hcomp c]; exact hw⟩

end Construction

/-! ## 5. The canonical Artin datum -/

/-- **`LevelPairIso` implies `CanonicalArtinDatum`.**  The coherent system is produced by an
ultrafilter limit over the directed system of `ℓ`-levels. -/
theorem canonicalArtinDatum_of_levelPairIso {K : Type} [Field K] [NumberField K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (h : NK.NUV2.ArtinBridge.LevelPairIso K Ω ℓ) :
    NK.NUV2.ArtinBridge.CanonicalArtinDatum K Ω ℓ := by
  refine ⟨fun L hL => artHom h ⟨L, hL⟩, ?_, ?_, ?_⟩
  · intro L M hL hM hle
    exact artHom_coherent h ⟨L, hL⟩ ⟨M, hM⟩ hle
  · intro L hL
    exact artHom_ker h ⟨L, hL⟩
  · intro L hL
    exact artHom_surjective h ⟨L, hL⟩

end

end NK.NUV2.ArtinBridge
