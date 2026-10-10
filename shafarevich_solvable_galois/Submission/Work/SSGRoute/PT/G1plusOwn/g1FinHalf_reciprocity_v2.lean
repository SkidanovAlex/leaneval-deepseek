import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E7cOmega.mem_orbit_of_liesOver_conj
import Submission.Work.SSGRoute.PT.G1plusOwn.exists_level_factors_unramified_v2
import Submission.Work.SSGRoute.PT.G1plusOwn.extHRestrict_infinite_eq_zero
import Submission.Work.SSGRoute.PT.G1plusOwn.goodPlaceUnder_finQW
import Submission.Work.SSGRoute.PT.G1plusOwn.isConjPlace_of_finQW_conj
import Submission.Work.SSGRoute.PT.G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero
import Submission.Work.SSGRoute.PT.G1plusOwn.unramifiedPairClause
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 8000000

namespace Work.SSGRoute.PT.G1plusOwn

/-! ## Helper lemmas for the finite-place reciprocity (clause (7))

The monotonicity lemmas are the ones the main proof needs in order to feed the *global* cocycle
data (`ha1`, `ha2`, `hb1`, `hb2`) into the *local* clauses of `hpair`/`hpair_unr` (which are stated
on `decomp k A`), and `finZF_eq_decompKRestrict` is the identification of the opaque local
dictionary map `PT.finZF` with the canonical place-glue `decompKRestrict` used by the proved
level-pairing naturalities (`Work.SSGRoute.levelPair_extLoc_eq_push`,
`Work.SSGRoute.PT.finZI_apply`, `E7cOmega.extLoc_push_ideleMap`). -/

/-- **Local constancy is monotone in the subgroup.** -/
theorem isLocConstOn_mono {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M] [DistribMulAction G M] {H H' : Subgroup Γ} (h : H' ≤ H) {f : Γ → M}
    (hf : SSGRoute.IsLocConstOn H f) : SSGRoute.IsLocConstOn H' f := by
  obtain ⟨U, hU, hc⟩ := hf
  exact ⟨U, hU, fun g hg u hu hu' => hc g (h hg) u hu (h hu')⟩

/-- **The cocycle condition is monotone in the subgroup.** -/
theorem isCocycleOn_mono {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] {act : Γ →* G} {H H' : Subgroup Γ} (h : H' ≤ H) {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) : SSGRoute.IsCocycleOn act H' f :=
  fun g hg h' hh => hf g (h hg) h' (h hh)

/-- **`PT.finZF` is the canonical place glue `decompKRestrict`.**  Both are monoid homomorphisms
into the decomposition group at the prime of `𝓞 K` below `A`, and both are characterised by
`σ ↦ galRes k ↥K ↥L σ` (`PT.finZF_spec`, `Work.SSGRoute.decompKRestrict_coe`). -/
theorem finZF_eq_decompKRestrict {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.PT.finZF hKL A hA =
      Work.SSGRoute.decompKRestrict k ↥K ↥L
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
        ((Work.SSGRoute.PT.place_glue_level k Ω K L hKL A hA (Work.SSGRoute.PT.finQ K A hA)
          (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
          (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)).1) := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  rw [Work.SSGRoute.PT.finZF_spec hKL A hA σ, Work.SSGRoute.decompKRestrict_coe]

/-- **A global factorisation of a cocycle is a crossed homomorphism.**  If a globally
locally-constant `1`-cocycle `b` (for the action of `Gal(Ω/k)` through `res k K`) factors through
the level `L` as `b = b₀ ∘ restrictNormalHom L`, then `b₀` satisfies the crossed-homomorphism
identity for the `galRes`-action, which is the `hψ` hypothesis of `PT.levelClassOf`.  This is the
step 1 obligation recorded in the docstring of `g1FinHalf_reciprocity_v2`. -/
theorem crossedHom_of_global_factorisation {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
    [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
    [IsScalarTower ↥K ↥L Ω]
    {M : Type} [AddCommGroup M] [DistribMulAction (↥K ≃ₐ[k] ↥K) M]
    (b : (Ω ≃ₐ[k] Ω) → M) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → M) (hfac : ∀ σ : Ω ≃ₐ[k] Ω, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    ∀ g h : ↥L ≃ₐ[k] ↥L, b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g := by
  intro g h
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω) (K₁ := L) g
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := Ω) (K₁ := L) h
  have h1 : b (σ * τ) = b σ + SSGRoute.res k K σ • b τ := hb σ trivial τ trivial
  rw [hfac (σ * τ), map_mul, hfac σ, hfac τ] at h1
  have h2 : SSGRoute.res k K σ
      = SSGRoute.PTExt.galRes k (↥K) (↥L) (AlgEquiv.restrictNormalHom L σ) :=
    (SSGRoute.PTExt.galRes_trans (k := k) (K := ↥K) (L := ↥L) (L' := Ω) σ).symm
  rw [h2] at h1
  exact h1.trans (add_comm _ _)

/-- **The local value vanishes at an infinite place** (odd `p`).

At an infinite place `v` of `L` the second slot of the local Yoneda product is `0`: the
decomposition group `decompK (ofInfinite v)` has order `≤ 2` (`PT.natCard_stabilizer_ofInfinite_le_two`)
and `2` is invertible on the `p`-torsion coefficient `DualMod p (M ⊗ T)` (`p` odd), so `H¹` — hence
`Ext¹_ℤ(ℤ, –)` — of it vanishes (`PT.G1plusOwn.extHRestrict_infinite_eq_zero`).  This is the
infinite-place half of the `hT` hypothesis of the sum decomposition (step 4 of the docstring of
`g1FinHalf_reciprocity_v2`). -/
theorem yonedaPair_extLoc_infinite_eq_zero
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (v : NumberField.InfinitePlace ↥L)
    (Z' : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
      (SSGRoute.PTExt.idelesK k ↥L) 1)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))) 1) :
    SSGRoute.PTExt.yonedaPair
        (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofInfinite v) Z')
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite v)) h) = 0 := by
  rw [extHRestrict_infinite_eq_zero p hp K L hKL M T v h]
  simp only [SSGRoute.PTExt.yonedaPair_zero_left, SSGRoute.PTExt.yonedaPair_zero_right]

/-- **Clause (7) of `G1⁺` at finite places, odd `p`, over the abstract dictionary interface.**

Restatement of `SSGRoute/PT/G1plusOwn/g1FinHalf_reciprocity` (H343-L4252): the filed version's
*type* mentioned `G1pOwn.g1FinHalf`, a `Classical.choose` out of the still-`sorry`
`E1aClean.localDictionary_natural_family`, so it can never certify (`#print axioms` traverses types
— measured: a complete `rfl`-proof of a type mentioning `PT.finZB` reports `sorryAx`).  Here the
local dictionary `βl`, the pairing `pair`, and the global dictionary `βg` are variables with the
clauses `hβl_*`, `hβl_unr`, `hpair`, `hpair_unr`, `hβg_add`, `hsq` (the `v4_0215` interface plus the
square).  The G1⁺ consumer instantiates `βl := PT.finZB …`, `βg := PT.finZBg …` (clauses from
`PT.finZB_spec`) and `pair := G1pOwn.g1FinHalf χ M` (its `hpair`, proved sorry-free in
`PT/G1plusOwn/g1FinHalf_hpair`; its `hpair_unr` is the restated `g1FinHalf_unramified`).

Odd `p` is needed: at `p = 2` the archimedean half is nonzero and only the *total* (finite +
archimedean) sum vanishes (`E7Arch.g1Assembly.pairGlue_reciprocity`'s docstring: `k = ℚ`, `p = 2`,
`M = 𝔽₂`, `a = b =` the sign character gives `1` for each half separately).  For odd `p` the
archimedean family vanishes identically (`E7Arch.pairArchFamily_eq_zero_of_ne_two`), so this is the
`hfin` input of `E7Arch.pairReciprocity_of_vanishing_involutions`, hence gives `G1⁺`'s clause (7).

## Route and state of the assembly (session records)

The four ingredients, with their status in the repository:

1. **The level and the global level class.**  Take `L ⊇ K` over which `b` factors *globally*
   (`PT.exists_level_factors_locConstOn` at `H = ⊤`), giving `b₀` with
   `b σ = b₀ (restrictNormalHom L σ)` for *all* `σ`; the global crossed-homomorphism property of
   `b₀` follows from `hb1` and the surjectivity of `AlgEquiv.restrictNormalHom` (helper obligation,
   a few lines).  The global level class is
   `h_L := PT.levelClassOf p k Ω K T M L b₀ hψ` (already on disk, sorry-free).

2. **The per-place value formula in its pushed form.**  For each `A`, `hpair` at the level `L`
   together with `hsq` and the (new) level-pairing push
   `Submission/Work/SSGRoute/PT/G1plusOwn/finZZ_push.lean` turn the summand into
   `χ L hKL (iota w_A (extLoc w_A (levelPair (galRes k ↥K ↥L) (idleRepMap k ↥K ↥L)
   (extToIdeles (βg a)) h_L)))`.  The only new mathematical content of that push is
   `finZH … = extHRestrict (decompK w_A) h_L`, i.e. the *group-naturality of `PT.levelClassOf`*
   under restriction to the decomposition group — available as the proved
   `Work.SSGRoute.extHMap_gammaHom_eq` (with `PT.finZF_eq_decompKRestrict` above and the pointwise
   characterisation of `PT.finZI`, v. `PT.finZI_apply`/`PT.localUnitsMapAt_spec`).

3. **The sum identity over the classes of `S'`.**  With `W := {w_A : A ∈ S'}` (pairwise
   non-`Gal(L/k)`-conjugate by `hS'disj`) sitting inside a transversal `R ⊇ W` of the places of `L`,
   the *proved* `PT.chi_pairK_eq_sum_iota` (`PT/localSumDecomposition.lean`, built on
   `PT.pairK_eq_sum_iotaLift`) gives
   `χ L hKL (pairK (extToClasses Z') h_L) = ∑_{w ∈ W} χ L hKL (iota w (yonedaPair (extLoc w Z')
   (extHRestrict (decompK w) h_L)))`, where `Z' := extHMap (galRes k ↥K ↥L) (idleRepMap k ↥K ↥L)
   (extToIdeles (βg a))`, provided (a) the local values vanish off the classes of `W` (`hT`) and
   (b) the `ι`-terms are `p`-torsion (from `E6Util.ext_nsmul_p_torsion_left`, the coefficient
   `DualMod p (M ⊗ T)` being `p`-torsion).  Finally `extToClasses Z' = 0`
   (`PT.extToClasses_idleRepMap` + `PT.extToClasses_extToIdeles`), so the value is `χ 0 = 0`
   (`PT.chi_zero_of_additive`).  *(Obligation: instantiate it at a transversal containing `W` —
   the set-theoretic construction of `R`.)*

4. **(hT) the vanishing off the classes of `S'`.**
   * Infinite places: `extHRestrict (decompK w) h_L = 0`.  The *reason* is **not** that the
     decomposition group is trivial (it is `ℤ/2` over a real place of `k`): rather, `Nat.card
     (decompK w) ≤ 2` (`PT.natCard_stabilizer_ofInfinite_le_two`) is invertible on the `p`-torsion
     coefficient `DualMod p (M ⊗ T)` (`p` odd), so `H¹` — equivalently `Ext¹_ℤ(ℤ, –)` — vanishes
     (`Work.GroupCohomology.H1_subsingleton_of_card_smul_bijective` + the `gammaHom` bridge).
     Filed as `Submission/Work/SSGRoute/PT/G1plusOwn/extHRestrict_infinite_eq_zero.lean`.
   * Finite good places `B`: the local value is `levelPair (finZF …) (finZI …) (βl B hB a) (finZH_B)`
     (reverse of the push of step 2), `βl B hB a` is unramified (`hβl_unr` + `hgood`) and
     `PT.levelPair_unramified_eq_zero` kills the value — **but that lemma additionally needs the
     level `L` to be unramified at `B`** (`hunr : ∀ σ, IsInertiaAt q' σ → σ = 1`, used through
     `ramificationIdx_under_eq_one_of_isInertiaAt` + `eq_zero_of_isUnramifiedExt_of_unramified`).
     This is the **crux level-existence obligation**: a level `L ⊇ K`, finite and normal over `k`,
     that both factors `b` globally and is unramified at *every* finite place outside the classes of
     `S'`.  Construction: let `U` be an open normal constancy subgroup of `b`
     (`hb2 : IsLocConstOn ⊤ b`) and take `L := K ⊔ Ω^{Gal(Ω/K) ∩ U}`.  Then
     `Gal(Ω/L) = Gal(Ω/K) ∩ U ⊆ U` (so `b` factors through `L`), while for a good `B` one has
     `I_B ⊆ Gal(Ω/K)` (`hgood`: `K/k` unramified at `B`) and `I_B ⊆ U`: for `σ ∈ I_B`, `τ ∈ D_B`,
     `b (σ τ) = b σ + σ • b τ = σ • b τ` and, `I_B` being normal in `D_B`,
     `b (σ τ σ⁻¹) = b τ`; hence `σ • b τ = b τ`, so `I_B ⊆ U`, and `I_B ⊆ Gal(Ω/L)`, i.e. the level
     `L` is unramified at `B`.  *(Obligation: the Galois-correspondence construction of
     `Ω^{Gal(Ω/K) ∩ U}` together with `[FiniteDimensional k L]`, `[Normal k L]`, `K ≤ L`.)*

Steps 1–4 assemble the theorem with `hpair`/`hpair_unr`/`hsq`/`hχadd` (and no use of
`hβl_add`/`hβl_ker`/`hβl_onto`/`hβg_add` at this level: they belong to the perfectness/kernel
clauses of `G1⁺`, not to clause (7)).

## Status of the four ingredients (filed as separate modules, verified in place)

| module | statement | status |
|---|---|---|
| `G1plusOwn.finZZ_push` | step 2 (push of `finZH`/`finZI`/`finZF`) | in progress |
| `G1plusOwn.extHRestrict_infinite_eq_zero` | step 4, infinite places | **proved** |
| `G1plusOwn.exists_level_factors_unramified_v2` | step 4, the crux level (factorisation + unramified outside `S'`, as `I_B ≤ L.fixingSubgroup`) | in progress |
| `G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero` | step 3 (the sum identity over the classes of `S'`) | in progress |

Auxiliary lemmas already on disk and sorry-free:
`PT.levelPair_unramified_eq_zero` (clause (6)), `PT.isInertiaAt_eq_one_of_inertiaSub_le`
(`PT/G1plusOwn/unramifiedPairClause.lean`, the bridge from `I_B ≤ L.fixingSubgroup` to the level
inertia `IsInertiaAt (finQW L B hB) σ → σ = 1` used by clause (6)),
`Work.SSGRoute.extHMap_gammaHom_eq`, `E9c.Core.extLoc_levelPair_idleRepMap_eq`,
`E7cOmega.extLoc_push_ideleMap`, `PT.chi_pairK_eq_sum_iota`, `PT.extToClasses_idleRepMap`,
`PT.extToClasses_extToIdeles`, `E6Util.ext_nsmul_p_torsion_left` (the `hp` of step 3), and
`PT.glue_helpers.exists_transversal_containing_set`/the `Finset`-transversal helper.

**Remaining assembly obligation** (the only piece not attributed to a module above): build the
`Finset` `W := {ofFinite (finQW L A hA) : A ∈ S'}` inside a transversal of the places of `L`,
match `∑_{A ∈ S'} pair (decomp k A) a b` with the sum over `W` (the map `A ↦ finQW L A hA` is
injective up to conjugacy: two such primes with the same place lie over the same prime of `𝓞 K`,
whence `IsConjPlace k A A'`, whence `A = A'` by `hS'disj`), instantiate
`sum_iota_eq_zero_of_extToClasses_zero` with `M' := Rep.res (galRes k ↥K ↥L) (modRep …)`,
`Z' := extHMap (galRes k ↥K ↥L) (idleRepMap k ↥K ↥L) (extToIdeles (βg a))` (`extToClasses Z' = 0` by
`PT.extToClasses_idleRepMap` + `PT.extToClasses_extToIdeles`), `h := h_L`, prove its `hT` with
`finZZ_push` + `PT.levelPair_unramified_eq_zero` (finite places, using the crux level and the bridge
above) and with `extHRestrict_infinite_eq_zero` (infinite places), and its `hp` from the
`p`-torsion of `DualMod p (M ⊗ T)` via `E6Util.ext_nsmul_p_torsion_left`
(`p • extLoc w Z' = 0`, then `p • yonedaPair = yonedaPair (p • ·) = 0`), and finally transport
`χ (iota w (extLoc w (levelPair (galRes k ↥K ↥L) (idleRepMap k ↥K ↥L) (extToIdeles (βg a)) h_L)))`
into `χ (iota w (yonedaPair (extLoc w Z') (extHRestrict (decompK w) h_L)))` by
`E9c.Core.extLoc_levelPair_idleRepMap_eq` + `extHMap_eq_extRes_comp`. -/
theorem g1FinHalf_reciprocity_v2 (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (hpair_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
        pair (SSGRoute.decomp k A) a b = 0)
    (βg : ((Ω ≃ₐ[k] Ω) → M) →
      CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
        (SSGRoute.PTExt.unitsK k K) 1)
    (hβg_add : ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
      βg (b + b') = βg b + βg b')
    (hsq : ∀ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
        SSGRoute.PTExt.extLoc (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (SSGRoute.PTExt.extToIdeles (k := k) (βg b)) = βl A hA b)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B)
    (hgood : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
        ∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) :
    ∑ A ∈ S', pair (SSGRoute.decomp k A) a b = 0 := by
  classical
  -- ## 1. The common level: a finite Galois level `L ⊇ K` factoring `b` globally and unramified
  -- at every finite place outside the classes of `S'`.
  obtain ⟨L, hLfin, hLnorm, hKL, ⟨b₀, hb₀⟩, hInertia⟩ :=
    exists_level_factors_unramified_v2 (p := p) (K := K)
      (M := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) b hb1 hb2 S' hS'fin
      (fun B hB hBnot => ⟨(hgood B hB hBnot).2.1,
        fun σ hσ => ((hgood B hB hBnot).2.2 σ hσ).2⟩)
  haveI : FiniteDimensional k L := hLfin
  haveI : Normal k L := hLnorm
  haveI hLnum : NumberField ↥L := NumberField.of_module_finite k ↥L
  haveI hLgal : IsGalois k ↥L :=
    isGalois_iff.mpr ⟨Algebra.IsSeparable.of_integral k ↥L, hLnorm⟩
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## 2. The crossed homomorphism and the global level class.
  have hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g :=
    crossedHom_of_global_factorisation K L hKL b hb1 b₀ hb₀
  let h_L := Work.SSGRoute.PT.levelClassOf p k Ω K T M L b₀ hψ
  -- ## 3. The global idèle class, its pushed localisation, and the local value function.
  let Z := SSGRoute.PTExt.extToIdeles (k := k) (βg a)
  let Z' := (SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) Z).comp
      (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L))) (add_zero 1)
  let g : NK.GlobalCFT.Place ↥L → ZMod p := fun w =>
    χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) w
      (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)))
  -- ## 4. The Finset of `L`-places attached to the classes of `S'`.
  let f : {A : ValuationSubring Ω // A ∈ S'} → NK.GlobalCFT.Place ↥L :=
    fun A => NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A.1 (hS'fin A.1 A.2))
  let W : Finset (NK.GlobalCFT.Place ↥L) := S'.attach.image f
  -- ## 5. `extToClasses Z' = 0`.
  have hZgen : ∀ {M0 : Rep.{0} SSGRoute.PTExt.Coeff (↥K ≃ₐ[k] ↥K)}
      (x : CategoryTheory.Abelian.Ext M0 (SSGRoute.PTExt.idelesK k ↥K) 1),
      SSGRoute.PTExt.extToClasses (k := k) (K := ↥L)
          ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) x).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L))) (add_zero 1))
        = (SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L))
              (SSGRoute.PTExt.extToClasses (k := k) (K := ↥K) x)).comp
            (CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.PTExt.classIncl k (↥K) (↥L))) (add_zero 1) := by
    intro M0 x
    simp only [SSGRoute.PTExt.extToClasses]
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← Work.SSGRoute.resMap_classGroupMap_comp_classIncl k (↥K) (↥L),
      ← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero,
      ← Work.SSGRoute.extRes_comp_mk₀]
  have hZ : SSGRoute.PTExt.extToClasses (k := k) (K := ↥L) Z' = 0 := by
    rw [hZgen (M0 := SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) Z,
      show SSGRoute.PTExt.extToClasses (k := k) (K := ↥K) Z = 0 from
        SSGRoute.PTExt.extToClasses_extToIdeles (k := k) (K := ↥K) (βg a),
      show SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L))
          (0 : CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
            (SSGRoute.PTExt.classesK k ↥K) 1) = 0 from
        Work.SSGRoute.E6Util.extRes_zero _]
    simp
  -- ## 6. The value at a place of `S'`, at the level `L`.
  have hval : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hmem : A ∈ S'),
      pair (SSGRoute.decomp k A) a b = g (f ⟨A, hmem⟩) := by
    intro A hA hmem
    have hbA : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b :=
      Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hb1
    have ha2' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a := Work.SSGRoute.isLocConstOn_mono le_top ha2
    have hb2' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b := Work.SSGRoute.isLocConstOn_mono le_top hb2
    rw [hpair A hA a b ha2' hb2' hbA L hKL b₀ (fun σ _ => hb₀ σ),
      ← hsq a ha1 ha2 A hA]
    exact congrArg (fun v => χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) v))
      (Work.SSGRoute.PT.vf_local_compare p k Ω K T M L hKL A hA Z
        (SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) Z)
        rfl h_L b₀ hψ rfl b (fun σ => hb₀ σ) hbA (fun σ _ => hb₀ σ)).symm
  -- ## 7. Reindexing the sum over `S'` as a sum over `W`.
  have hinj : Set.InjOn f ↑S'.attach := by
    intro A hA B hB h
    exact Subtype.ext (Work.SSGRoute.PT.G1plusOwn.isConjPlace_of_finQW_conj L S' hS'fin hS'disj
      (1 : ↥L ≃ₐ[k] ↥L) A.2 B.2 (by simpa [f] using h))
  have hW : ∀ w ∈ W, ∀ w' ∈ W, (∃ σ : ↥L ≃ₐ[k] ↥L, σ • w = w') → w = w' := by
    intro w hw w' hw' hconj
    obtain ⟨A, hAs, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨B, hBs, rfl⟩ := Finset.mem_image.mp hw'
    obtain ⟨σ, hσ⟩ := hconj
    exact congrArg f (Subtype.ext (Work.SSGRoute.PT.G1plusOwn.isConjPlace_of_finQW_conj L S' hS'fin
      hS'disj σ A.2 B.2 hσ))
  have hreindex : ∑ A ∈ S'.attach, g (f A) = ∑ w ∈ W, g w :=
    (Finset.sum_image (s := S'.attach) (g := f) hinj).symm
  -- ## 8. The vanishing of the local components off the classes of `S'`.
  have hT : ∀ w : NK.GlobalCFT.Place ↥L,
      (∀ w' ∈ W, ∀ σ : ↥L ≃ₐ[k] ↥L, σ • w' ≠ w) →
      SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L) = 0 := by
    intro w hw
    rcases w with v | q'
    · exact yonedaPair_extLoc_infinite_eq_zero p hp K L hKL M T v Z' h_L
    · obtain ⟨B, hB, hBq, hBnot⟩ := Work.SSGRoute.PT.G1plusOwn.goodPlaceUnder_finQW L S' hS'fin
        q' (fun A hA σ => hw (f ⟨A, hA⟩)
          (Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach S' _, rfl⟩) σ)
      have hunr : ∀ σ : ↥L ≃ₐ[k] ↥L,
          SSGRoute.PTExt.IsInertiaAt (Work.SSGRoute.PT.finQW L B hB) σ → σ = 1 :=
        fun σ hσ => Work.SSGRoute.PT.G1plusOwn.isInertiaAt_eq_one_of_inertiaSub_le k Ω B hB L
          (hInertia B hB hBnot) σ hσ
      have hgoodB := hgood B hB hBnot
      have hbB : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k B) b :=
        Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top hb1
      have hlB : SSGRoute.IsLocConstOn (SSGRoute.decomp k B) b := Work.SSGRoute.isLocConstOn_mono le_top hb2
      let u : NK.GlobalCFT.Place ↥K := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K B hB)
      let wB : NK.GlobalCFT.Place ↥L :=
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B hB)
      let hwB : NK.GlobalCFT.Place.LiesOver wB u :=
        (Work.SSGRoute.PT.place_glue_level k Ω K L hKL B hB (Work.SSGRoute.PT.finQ K B hB)
          (fun x => Work.SSGRoute.PT.finQ_spec K B hB x) (Work.SSGRoute.PT.finQW L B hB)
          (fun y => Work.SSGRoute.PT.finQW_spec L B hB y)).1
      have h1 : SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB
          (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
            (Work.SSGRoute.idleRepMap k (↥K) (↥L)) Z h_L)
          = SSGRoute.PTExt.levelPair
              (Work.SSGRoute.decompKRestrict k ↥K ↥L u wB hwB)
              (Work.SSGRoute.localUnitsMap k ↥K ↥L u wB hwB)
              (SSGRoute.PTExt.extLoc (k := k) (K := ↥K) u Z)
              (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L) := by
        rw [Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := ↥K) (L := ↥L)
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) Z h_L wB]
        rw [Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := ↥K) (L := ↥L) (z := Z)
          (u := u) (w := wB) (hw := hwB)
          (ι := Work.SSGRoute.localUnitsMap k ↥K ↥L u wB hwB)
          (hι := Work.SSGRoute.localUnitsMap_spec k ↥K ↥L u wB hwB)]
        rfl
      have hgoal : SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L)
          = SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB
              (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
                (Work.SSGRoute.idleRepMap k (↥K) (↥L)) Z h_L) :=
        (Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := ↥K) (L := ↥L)
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) Z h_L wB).symm
      have hfin : SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) wB Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L) = 0 := by
        rw [hgoal, h1, hsq a ha1 ha2 B hB]
        exact Work.SSGRoute.PT.levelPair_unramified_eq_zero k ↥K
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
          u ↥L (Work.SSGRoute.PT.finQW L B hB) hwB hunr
          (Work.SSGRoute.decompKRestrict k ↥K ↥L u wB hwB)
          (Work.SSGRoute.decompKRestrict_coe k ↥K ↥L u wB hwB)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L u wB hwB)
          (Work.SSGRoute.localUnitsMap_spec k ↥K ↥L u wB hwB)
          (βl B hB a)
          (hβl_unr B hB hgoodB.1 hgoodB.2.1 a
            (Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) le_top ha1)
            (Work.SSGRoute.isLocConstOn_mono le_top ha2)
            (fun σ hσ => (hgoodB.2.2 σ hσ).1))
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) wB) h_L)
      rw [← hBq]
      exact hfin
  -- ## 9. The `p`-torsion of the local values.
  have iota_nsmul : ∀ (w : NK.GlobalCFT.Place ↥L)
      (z : SSGRoute.PTExt.extH (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) w) 2) (n : ℕ),
      n • Work.SSGRoute.PT.iota (k := k) (L := ↥L) w z
        = Work.SSGRoute.PT.iota (k := k) (L := ↥L) w (n • z) := by
    intro w z n
    induction n with
    | zero => rw [zero_smul, zero_smul, Work.SSGRoute.PT.iota_zero]
    | succ n ih => rw [add_nsmul, one_smul, ih, ← Work.SSGRoute.PT.iota_add, add_nsmul, one_smul]
  have hp' : ∀ w ∈ W, p • Work.SSGRoute.PT.iota (k := k) (L := ↥L) w
      (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)) = 0 := by
    intro w hw
    have hX : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • x = 0 :=
      fun x => Work.SSGRoute.PT.nsmul_eq_zero_of_zmod' p x
    have hxl : p • SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z' = 0 :=
      Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX _
    have hy : p • SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L) = 0 := by
      rw [show p • SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
            (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)
          = SSGRoute.PTExt.yonedaPair
              (p • SSGRoute.PTExt.extLoc (k := k) (K := ↥L) w Z')
              (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L) from
        (AddMonoidHom.map_nsmul
          { toFun := fun x : CategoryTheory.Abelian.Ext
                (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
                  (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
                    (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
                      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))))
                (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) w) 1 =>
              SSGRoute.PTExt.yonedaPair x
                (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h_L)
            map_zero' := SSGRoute.PTExt.yonedaPair_zero_right _
            map_add' := fun x x' => SSGRoute.PTExt.yonedaPair_add_right x x' _ } p _).symm,
        hxl, SSGRoute.PTExt.yonedaPair_zero_right _]
    rw [iota_nsmul, hy, Work.SSGRoute.PT.iota_zero]
  -- ## 10. The sum identity.
  have hchild := Work.SSGRoute.PT.G1plusOwn.sum_iota_eq_zero_of_extToClasses_zero p
    (fun u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k ↥L) 2 => χ L hKL u)
    (fun u v hu hv => hχadd L hKL u v hu hv) Z' hZ h_L W hW hT hp'
  have hstep : ∑ A ∈ S'.attach, pair (SSGRoute.decomp k (A : ValuationSubring Ω)) a b
      = ∑ A ∈ S'.attach, g (f A) :=
    Finset.sum_congr rfl (fun A _ => hval A.1 (hS'fin A.1 A.2) A.2)
  rw [← Finset.sum_attach S' (fun A => pair (SSGRoute.decomp k A) a b), hstep, hreindex]
  exact hchild

end Work.SSGRoute.PT.G1plusOwn
