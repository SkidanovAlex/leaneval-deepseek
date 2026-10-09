import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# sha2_restrict_vanish  (Ш²(k,E) dies on G_K)

**Statement.** Every `c ∈ Z2loc p k Ω K E` is a continuous coboundary on `G_K = K.fixingSubgroup`.

**Proof (base change `k → K`).**  On `G_K` the action is trivial (namely `res k K σ = 1` for
`σ ∈ K.fixingSubgroup`) and `μ_p ⊆ K`.  The places of `Ω` over `K` have decomposition groups
`D_A ∩ G_K`, and the involutions of `G_K` are involutions of `G_k`; every finite place over `K`
is a finite place over `k` (a valuation subring containing `k` is `⊤`, by integral closedness and
the integrality of `K/k`).  Hence `c` restricted to `Ω ≃ₐ[K] Ω` satisfies the four `Z2loc`-at-base
`K` conditions with coefficients the trivially acted module `E`, so the base-field statement
(`Work.SSGRoute.sha2_trivial_vanish` at the base field `K`, i.e. a base case `Subsingleton (Sha2 p
K Ω ⊥ E)`) exhibits a primitive, which is transported back to `G_k`.

This file contains the *base change* part: the identification
`toGkHom : Gal(Ω/↥K) →* G_k`, the transport of the local data (decomposition groups, the
"finite place" predicate, cochain local constancy, the cocycle identity), and the reduction of the
statement to the base-field case `hbase` (`sha2_restrict_vanish_of_base`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open SSGRoute
open scoped Pointwise Classical

section BaseChange

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- `Gal(Ω/↥K) →* G_k`: the identification `Gal(Ω/↥K) ≃* ↥K.fixingSubgroup` followed by the
inclusion of the fixing subgroup in `G_k`. -/
def toGkHom (K : IntermediateField k Ω) : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[k] Ω) :=
  (Subgroup.subtype K.fixingSubgroup).comp
    (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom

@[simp] theorem toGkHom_apply (K : IntermediateField k Ω) (g : Ω ≃ₐ[K] Ω) (x : Ω) :
    toGkHom K g x = g x := rfl

theorem toGkHom_fixingSubgroupEquiv (K : IntermediateField k Ω) (x : ↥(K.fixingSubgroup)) :
    toGkHom K ((IntermediateField.fixingSubgroupEquiv K) x) = (x : Ω ≃ₐ[k] Ω) := by
  rw [toGkHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

theorem toGkHom_injective (K : IntermediateField k Ω) : Function.Injective (toGkHom K) := by
  intro g h hgh
  have h1 : (Subgroup.subtype K.fixingSubgroup)
      ((IntermediateField.fixingSubgroupEquiv K).symm g) =
      (Subgroup.subtype K.fixingSubgroup)
      ((IntermediateField.fixingSubgroupEquiv K).symm h) := hgh
  exact (IntermediateField.fixingSubgroupEquiv K).symm.injective (Subtype.val_injective h1)

/-- The transport of the decomposition groups: `g : Gal(Ω/↥K)` stabilises the place `A` of `Ω`
seen over `K` if and only if the corresponding element of `G_k` stabilises `A` seen over `k`.
The two actions only depend on the underlying function. -/
theorem toGkHom_mem_decomp (K : IntermediateField k Ω) (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) :
    toGkHom K g ∈ SSGRoute.decomp k A ↔ g ∈ SSGRoute.decomp K A := by
  have hsmul : toGkHom K g • A = g • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor <;> rintro ⟨s, hs, hx⟩ <;> refine ⟨s, hs, ?_⟩
    · rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl
    · rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; rfl
  rw [SSGRoute.decomp, SSGRoute.decomp, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, hsmul]

/-- On the subgroup `K.fixingSubgroup = G_K`, the restriction map `res k K` is trivial; this is
what makes the coefficient action there the trivial action. -/
theorem res_toGkHom (K : IntermediateField k Ω) [Normal k K] (g : Ω ≃ₐ[K] Ω) :
    SSGRoute.res k K (toGkHom K g) = 1 := by
  have hmem : toGkHom K g ∈ K.fixingSubgroup := Subtype.mem _
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
  exact hmem

/-- **Every finite place over `K` is a finite place over `k`**: if `A` contains (the image of) `k`
then `A = ⊤`, because `A` is integrally closed and `K/k` is integral, so `A ⊇ K`. -/
theorem isFinPlace_of_isFinPlace [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace K A) :
    SSGRoute.IsFinPlace k A := by
  intro h
  apply hA
  have hAlg : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have hInt : Algebra.IsIntegral k Ω := hAlg.isIntegral
  have hkA : ∀ r : k, algebraMap k Ω r ∈ A := fun r => by
    have : r ∈ A.comap (algebraMap k Ω) := by rw [h]; trivial
    rwa [ValuationSubring.mem_comap] at this
  have nice : ∀ y : Ω, (∀ r : k, algebraMap k Ω r ∈ A) → y ∈ A := by
    intro y hq
    have hIC : IsIntegrallyClosedIn ↥A.toSubring Ω :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring hz
    have hle : (integralClosure k Ω).toSubring ≤ A.toSubring := by
      rw [Subring.integralClosure_le_iff]
      intro r
      rw [ValuationSubring.mem_toSubring]
      exact hq r
    exact hle ((mem_integralClosure_iff k Ω).mpr (Algebra.IsIntegral.isIntegral y))
  rw [eq_top_iff]
  intro y _
  rw [ValuationSubring.mem_comap]
  exact nice _ hkA

/-- Transport of a local-constancy statement from `G_k` to `Gal(Ω/↥K)`: an open subgroup of `G_k`
pulls back to an open subgroup of `Gal(Ω/↥K)` (via the homeomorphism
`IntermediateField.fixingSubgroupEquiv K`), over which the transported cochain is constant. -/
theorem isLocConstOn_toGk {K : IntermediateField k Ω} {H : Subgroup (Ω ≃ₐ[K] Ω)}
    {H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H ≤ H'.comap (toGkHom K))
    {E : Type} [AddCommGroup E] {b : (Ω ≃ₐ[k] Ω) → E} (hb : SSGRoute.IsLocConstOn H' b) :
    SSGRoute.IsLocConstOn H (fun g => b (toGkHom K g)) := by
  obtain ⟨W, hWopen, hWc⟩ := hb
  refine ⟨(W.comap (Subgroup.subtype K.fixingSubgroup)).map
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom, ?_, ?_⟩
  · refine Work.SSGRoute.isOpen_map_fixingSubgroupEquiv K _ ?_
    exact hWopen.preimage continuous_subtype_val
  · intro g hg u hu huH
    obtain ⟨w, hwW, hwu⟩ := Subgroup.mem_map.mp hu
    have hwu' : (w : Ω ≃ₐ[k] Ω) = toGkHom K u := by
      rw [← hwu]
      exact (toGkHom_fixingSubgroupEquiv K w).symm
    show b (toGkHom K (g * u)) = b (toGkHom K g)
    rw [map_mul, ← hwu']
    exact hWc (toGkHom K g) (h hg) (w : Ω ≃ₐ[k] Ω) hwW (by rw [hwu']; exact h huH)

/-- Transport of the `2`-cocycle condition. -/
theorem isCocycle2_toGk (p : ℕ) (K : IntermediateField k Ω) [Normal k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    [DistribMulAction ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) E]
    [SMulCommClass ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) (ZMod p) E]
    (htriv : ∀ (g : (⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) (m : E),
      g • m = m)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hcoc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) :
    SSGRoute.IsCocycle2 (SSGRoute.res K (⊥ : IntermediateField K Ω))
      (fun g h => c (toGkHom K g) (toGkHom K h)) := by
  intro g h l
  have h1 := hcoc (toGkHom K g) (toGkHom K h) (toGkHom K l)
  rw [res_toGkHom, one_smul] at h1
  rw [htriv (SSGRoute.res K (⊥ : IntermediateField K Ω) g) (c (toGkHom K h) (toGkHom K l))]
  simpa only [map_mul] using h1


/-- **The reverse transport of local constancy.**  A cochain `b` on `Gal(Ω/↥K)` which is locally
constant (for the Krull topology) yields, by restriction to `K.fixingSubgroup`, a cochain on
`G_k` which is locally constant there: if `V ≤ Gal(Ω/↥K)` is an open constancy subgroup of `b`,
pick `M ≤ Ω` finite over `↥K` with `M.fixingSubgroup ≤ V` (Krull); viewing `M` as a field over `k`
(possible because `K ⊆ M` and `K/k` is finite), `M.fixingSubgroup ≤ G_k` is open, and an element
`u ∈ M.fixingSubgroup ∩ G_K` fixes `M`, so its image in `Gal(Ω/↥K)` lies in `M.fixingSubgroup ⊆ V`. -/
theorem isLocConstOn_extract {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsAlgClosure k Ω] {E : Type} [AddCommGroup E] {b : (Ω ≃ₐ[K] Ω) → E}
    (hb : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.IsLocConstOn (K.fixingSubgroup)
      (fun σ => if h : σ ∈ K.fixingSubgroup then
        b ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0) := by
  classical
  obtain ⟨V, hVopen, hVc⟩ := hb
  obtain ⟨M, hMfin, hMV⟩ :=
    (krullTopology_mem_nhds_one_iff (↥K) Ω (V : Set (Ω ≃ₐ[K] Ω))).mp
      (hVopen.mem_nhds V.one_mem)
  haveI : FiniteDimensional ↥K M := hMfin
  haveI hMk : FiniteDimensional k ↥M := FiniteDimensional.trans k ↥K ↥M
  haveI : FiniteDimensional k ↥(IntermediateField.restrictScalars k M) := hMk
  refine ⟨(IntermediateField.restrictScalars k M).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _, ?_⟩
  intro g hg u hu huH
  have hgu : g * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg huH
  show (if h : g * u ∈ K.fixingSubgroup then
      b ((IntermediateField.fixingSubgroupEquiv K) ⟨g * u, h⟩) else 0) =
    (if h : g ∈ K.fixingSubgroup then
      b ((IntermediateField.fixingSubgroupEquiv K) ⟨g, h⟩) else 0)
  rw [dif_pos hgu, dif_pos hg]
  have hcoe : ∀ x : Ω,
      ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩ : Ω ≃ₐ[K] Ω) x = u x := by
    intro x
    rw [← toGkHom_apply K ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩) x,
      toGkHom_fixingSubgroupEquiv]
  have huV : (IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩ ∈ V := by
    apply hMV
    refine (IntermediateField.mem_fixingSubgroup_iff M _).mpr ?_
    intro x hx
    rw [hcoe x]
    exact (IntermediateField.mem_fixingSubgroup_iff
      (IntermediateField.restrictScalars k M) u).mp hu x hx
  have hkey : ((IntermediateField.fixingSubgroupEquiv K) ⟨g * u, hgu⟩ : Ω ≃ₐ[K] Ω) =
      ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) *
      ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩) := by
    have h1 : (⟨g * u, hgu⟩ : ↥(K.fixingSubgroup)) = ⟨g, hg⟩ * ⟨u, huH⟩ := Subtype.ext rfl
    rw [h1, map_mul]
  rw [hkey]
  exact hVc _ trivial _ huV trivial

/-- Transport of local constancy of a `2`-cochain from `G_k` to `Gal(Ω/↥K)` (mirror of
`isLocConstOn_toGk`). -/
theorem isLocConst2_toGk {K : IntermediateField k Ω} [FiniteDimensional k K]
    {E : Type} [AddCommGroup E] {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E}
    (hc : SSGRoute.IsLocConst2 c) :
    SSGRoute.IsLocConst2 (fun g h => c (toGkHom K g) (toGkHom K h)) := by
  obtain ⟨U, hUopen, hUc⟩ := hc
  refine ⟨(U.comap (Subgroup.subtype K.fixingSubgroup)).map
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom, ?_, ?_⟩
  · refine Work.SSGRoute.isOpen_map_fixingSubgroupEquiv K _ ?_
    exact hUopen.preimage continuous_subtype_val
  · intro g h u v hu hv
    obtain ⟨w, hwU, hwu⟩ := Subgroup.mem_map.mp hu
    obtain ⟨w', hw'U, hw'v⟩ := Subgroup.mem_map.mp hv
    show c (toGkHom K (g * u)) (toGkHom K (h * v)) = c (toGkHom K g) (toGkHom K h)
    have hu' : (w : Ω ≃ₐ[k] Ω) = toGkHom K u := by
      rw [← hwu]; exact (toGkHom_fixingSubgroupEquiv K w).symm
    have hv' : (w' : Ω ≃ₐ[k] Ω) = toGkHom K v := by
      rw [← hw'v]; exact (toGkHom_fixingSubgroupEquiv K w').symm
    rw [map_mul, map_mul, ← hu', ← hv']
    exact hUc (toGkHom K g) (toGkHom K h) (w : Ω ≃ₐ[k] Ω) (w' : Ω ≃ₐ[k] Ω) hwU hw'U

/-- **Transport of a local coboundary, decomposition-group form.**  For a finite place `A` of `Ω`
over `k`, the restriction of a coboundary on `decomp k A` to `decomp K A ≤ Gal(Ω/↥K)` is a
coboundary; the coefficients act through `res k K`, which is trivial on
`Gal(Ω/↥K) = K.fixingSubgroup`. -/
theorem isCoboundary2On_toGk_place (K : IntermediateField k Ω) [FiniteDimensional k K]
    [Normal k K] (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    [DistribMulAction ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) E]
    (htriv : ∀ (g : (⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) (m : E),
      g • m = m)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (A : ValuationSubring Ω)
    (hcA : SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c) :
    SSGRoute.IsCoboundary2On (SSGRoute.res K (⊥ : IntermediateField K Ω))
      (SSGRoute.decomp K A) (fun g h => c (toGkHom K g) (toGkHom K h)) := by
  obtain ⟨b, hb, hbc⟩ := hcA
  refine ⟨fun g => b (toGkHom K g), isLocConstOn_toGk (fun _ hx => hx) hb, ?_⟩
  intro g hg h hh
  show c (toGkHom K g) (toGkHom K h) =
    SSGRoute.res K (⊥ : IntermediateField K Ω) g • b (toGkHom K h)
      - b (toGkHom K (g * h)) + b (toGkHom K g)
  have hg' : toGkHom K g ∈ SSGRoute.decomp k A := (toGkHom_mem_decomp K A g).mpr hg
  have hh' : toGkHom K h ∈ SSGRoute.decomp k A := (toGkHom_mem_decomp K A h).mpr hh
  rw [htriv (SSGRoute.res K (⊥ : IntermediateField K Ω) g) (b (toGkHom K h)),
    hbc (toGkHom K g) hg' (toGkHom K h) hh', res_toGkHom, one_smul, map_mul]

/-- **Transport of a local coboundary, involution form.** -/
theorem isCoboundary2On_toGk_involution (K : IntermediateField k Ω) [FiniteDimensional k K]
    [Normal k K] (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    [DistribMulAction ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) E]
    (htriv : ∀ (g : (⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) (m : E),
      g • m = m)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E) (σ : Ω ≃ₐ[K] Ω) (hσ : σ ^ 2 = 1)
    (hcσ : SSGRoute.IsCoboundary2On (SSGRoute.res k K)
      (Subgroup.zpowers (toGkHom K σ)) c) :
    SSGRoute.IsCoboundary2On (SSGRoute.res K (⊥ : IntermediateField K Ω))
      (Subgroup.zpowers σ) (fun g h => c (toGkHom K g) (toGkHom K h)) := by
  obtain ⟨b, hb, hbc⟩ := hcσ
  have hmem : ∀ x : Ω ≃ₐ[K] Ω, x ∈ Subgroup.zpowers σ →
      toGkHom K x ∈ Subgroup.zpowers (toGkHom K σ) := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx ⊢
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, by rw [map_zpow]⟩
  refine ⟨fun g => b (toGkHom K g), isLocConstOn_toGk hmem hb, ?_⟩
  intro g hg h hh
  show c (toGkHom K g) (toGkHom K h) =
    SSGRoute.res K (⊥ : IntermediateField K Ω) g • b (toGkHom K h)
      - b (toGkHom K (g * h)) + b (toGkHom K g)
  rw [htriv (SSGRoute.res K (⊥ : IntermediateField K Ω) g) (b (toGkHom K h)),
    hbc (toGkHom K g) (hmem g hg) (toGkHom K h) (hmem h hh), res_toGkHom, one_smul, map_mul]

/-- The group `Gal(K/K) = (⊥ : IntermediateField K Ω) ≃ₐ[K] ⊥` is trivial, hence so is every
`DistribMulAction` of it. -/
instance instSubsingletonBotAlgEquiv (K : IntermediateField k Ω) :
    Subsingleton ((⊥ : IntermediateField K Ω) ≃ₐ[K] (⊥ : IntermediateField K Ω)) where
  allEq σ τ := by
    ext x
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp x.2
    have hx : x = (algebraMap K (⊥ : IntermediateField K Ω)) c := Subtype.ext hc.symm
    rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]


end BaseChange

end Work.SSGRoute
