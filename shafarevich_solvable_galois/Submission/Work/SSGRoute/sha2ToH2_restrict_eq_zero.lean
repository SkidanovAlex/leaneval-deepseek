import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.sha2_restrict_vanish
import Submission.Work.SSGRoute.exists_sha2ToH2
import Submission.Work.GroupCohomology.Functoriality
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# The bridge `Ш²(k,M) → H²(G_k,M)` lands in `ker(res_K)` (E1a, design step 4)

`Work.SSGRoute.exists_sha2ToH2` produces, for every finite `𝔽_p[Gal(K/k)]`-module `M`, an additive
map `φ : Ш²(k,M) → H²(G_k,M)` (the *abstract* group cohomology of `G_k = Ω ≃ₐ[k] Ω` for the action
pulled back along `res k K : G_k →* Gal(K/k)`), computed on representatives by `H2π`.

The present file proves the **arithmetic vanishing** that makes it useful for the node
`Work.SSGRoute.ext_sha2_bridge` (E1a) of the Poitou–Tate design: the restriction of `φ b` to the
open fixing subgroup `G_K = K.fixingSubgroup` of `K` is zero,

  `resH2 (K.fixingSubgroup) (φ b) = 0`  for every `b : Ш²(k,M)`,

i.e. `im φ ⊆ ker(H²(k,M) → H²(K,M))`.  This is the cocycle-level form of E1a's design step 4
(`DESIGN_EXT.md` E1a):

> `Ш²(k,E)` maps into `Ш²(K,E)`, which is `0` (`sha2_restrict_vanish`).  So
> `Ш²(k,E) ⊆ ker(H²(k,E) → H²(K,E))`.

## Proof

Let `c ∈ Z²_loc` represent `b` (`Submodule.Quotient.induction_on`).  By the computation rule of the
bridge, `φ b = H2π c`; by `resH2_H2π`, `resH2 (φ b) = H2π (res c)`.  Now `sha2_restrict_vanish`
says that `c` *is* a coboundary on `K.fixingSubgroup`: there is a locally constant `a : G_k → M`
with `c g h = res k K g • a h - a (g * h) + a g` for all `g, h ∈ K.fixingSubgroup`.  Restricting
that primitive to the subgroup exhibits the restricted `2`-cocycle as an honest coboundary
`d¹ (a ∘ subtype)` of the group `K.fixingSubgroup` (whose action on `M` is the restriction of the
`G_k`-action, so that the two formulas agree), so its class in `H²` vanishes by
`H2pi_eq_zero_iff`/`mem_B2_iff`.

## Consumer

E1a's arithmetic half: the map `Ш²(k,M) → H²(k,M)` of `exists_sha2ToH2` factors through the kernel
of restriction to `K`, which the design identifies with `Ext²_G(E',Kˣ)` (through Hilbert 90 and the
Hochschild–Serre five-term sequence `Work.GroupCohomology.d₂_range`/`d2_ker`).
-/

namespace Work.SSGRoute

open Work.GroupCohomology

/-- **The bridge `Ш²(k,M) → H²(G_k,M)` dies on `G_K = K.fixingSubgroup`.**

For any additive map `φ` out of `Ш²(k,M)` into the abstract group cohomology `H²(G_k,M)` of
`G_k = Ω ≃ₐ[k] Ω` with coefficients in the `K`-torsion module `M` (the action pulled back along
`res k K`) whose value on the class of a locally trivial cocycle `c` is `H2π c`, one has

  `resH2 (K.fixingSubgroup) (φ b) = 0`  for every `b : Ш²(k,M)`,

i.e. `im φ ⊆ ker(H²(k,M) → H²(K,M))`. -/
theorem sha2ToH2_restrict_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (φ : Sha2 p k Ω K M →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)))
    (hφ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2,
                (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
                  (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2)).mp hc.1⟩)
    (b : Sha2 p k Ω K M) :
    @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) M _ _
        (DistribMulAction.compHom M (SSGRoute.res k K)) K.fixingSubgroup (φ b) = 0 := by
  classical
  -- the pulled-back action of `G_k` on the coefficients
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  -- reduce `b` to the class of a locally trivial `2`-cocycle `x.1`
  refine Submodule.Quotient.induction_on
    ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype) b fun x => ?_
  -- the computation rule of the bridge, and `resH2` of an `H2π`
  rw [hφ x.1 x.2, Work.GroupCohomology.resH2_H2π]
  -- the restricted cocycle is a coboundary on `K.fixingSubgroup`
  rw [Work.GroupCohomology.H2pi_eq_zero_iff, Work.GroupCohomology.mem_B2_iff]
  obtain ⟨a, _ha_loc, ha_eq⟩ :=
    Work.SSGRoute.sha2_restrict_vanish p k Ω K ζ hζ hζK M x.1 x.2
  refine ⟨fun h : K.fixingSubgroup => a (h : Ω ≃ₐ[k] Ω), ?_⟩
  funext q
  obtain ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ := q
  rw [Work.GroupCohomology.resZ2_coe, Work.GroupCohomology.resCochain2_apply]
  simp only [Work.GroupCohomology.d1_apply, Subgroup.smul_def]
  exact (ha_eq g hg h hh).symm

/-- **The bridge factors through `ker(res_K)`** (the `∃`-form of `sha2ToH2_restrict_eq_zero`, for the
canonical bridge of `Work.SSGRoute.exists_sha2ToH2`): for every finite `𝔽_p[Gal(K/k)]`-module `M`
there is `φ : Ш²(k,M) →+ H²(G_k,M)` whose image lies in the kernel of the restriction to `G_K`. -/
theorem exists_sha2ToH2_restrict_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ∃ φ : Sha2 p k Ω K M →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)),
      ∀ b : Sha2 p k Ω K M,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)) K.fixingSubgroup (φ b) = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_sha2ToH2 p k Ω K M
  exact ⟨φ, fun b => sha2ToH2_restrict_eq_zero p k Ω K ζ hζ hζK M φ hφ b⟩

/-- **The kernel of the bridge `Ш²(k,M) → H²(G_k,M)`.**  For an additive map `φ` out of `Ш²(k,M)`
into the abstract group cohomology `H²(G_k,M)` with the computation rule of the canonical bridge
(value `H2π c` on the class of a locally trivial cocycle `c`),

  `φ b = 0`  if and only if  `b` has a representative `c ∈ Z²_loc` whose underlying
  `2`-cochain is an *algebraic* `2`-coboundary of `G_k` (i.e. lies in `B² = range d¹`, with no
  continuity requirement on the primitive).

Equivalently, the kernel of `φ` is `(B² ∩ Z²_loc)/(B²_cont ∩ Z²_loc)`: the bridge is injective
exactly when every locally trivial cocycle that is an algebraic coboundary is a *continuous* one
(`B² ∩ Z²_loc = B²_cont ∩ Z²_loc`, the next theorem).  The `⊇` half is the definition of the
bridge, the `⊆` half is `H2pi_eq_zero_iff`.  This is the precise sense in which the defect of the
bridge is the difference between the algebraic and the continuous `B²` (compare
`Work.SSGRoute.PT.sha2ToH2contS`, whose target `H²_cont` uses the *same* denominators and which is
therefore injective). -/
theorem sha2ToH2_eq_zero_iff
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (φ : Sha2 p k Ω K M →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)))
    (hφ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2,
                (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
                  (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2)).mp hc.1⟩)
    (b : Sha2 p k Ω K M) :
    φ b = 0 ↔ ∃ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M),
      b = Submodule.Quotient.mk ⟨c, hc⟩ ∧
        ((fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.GroupCohomology.B2 (Ω ≃ₐ[k] Ω) M _ _
            (DistribMulAction.compHom M (SSGRoute.res k K))) := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  constructor
  · refine Submodule.Quotient.induction_on
      ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype) b (fun x => ?_)
    intro h
    refine ⟨x.1, x.2, ?_, ?_⟩
    · congr 1
    · rw [hφ x.1 x.2, Work.GroupCohomology.H2pi_eq_zero_iff] at h
      exact h
  · rintro ⟨c, hc, rfl, hmem⟩
    rw [hφ c hc, Work.GroupCohomology.H2pi_eq_zero_iff]
    exact hmem

/-- **When is the bridge `Ш²(k,M) → H²(G_k,M)` injective?**  Exactly when every locally trivial
`2`-cocycle of `G_k` that is an *algebraic* `2`-coboundary (i.e. whose class in the algebraic `H²`
is zero) is a *continuous* `2`-coboundary of `G_k`: this is the statement
`B² ∩ Z²_loc ⊆ B²_cont ∩ Z²_loc` (the reverse inclusion is the definition of `B²_cont`). -/
theorem sha2ToH2_injective_iff
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (φ : Sha2 p k Ω K M →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)))
    (hφ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2,
                (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
                  (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2)).mp hc.1⟩) :
    Function.Injective φ ↔ ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
      (hc : c ∈ Z2loc p k Ω K M),
      ((fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
        @Work.GroupCohomology.B2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)))
        → c ∈ B2top p k Ω K M := by
  classical
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  have hQ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M),
      (Submodule.Quotient.mk ⟨c, hc⟩ : Sha2 p k Ω K M) = 0 ↔ c ∈ B2top p k Ω K M := by
    intro c hc
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap
  constructor
  · intro hinj c hc hmem
    refine (hQ c hc).mp ?_
    have h0 : φ (Submodule.Quotient.mk ⟨c, hc⟩) = 0 :=
      (sha2ToH2_eq_zero_iff p k Ω K M φ hφ _).mpr ⟨c, hc, rfl, hmem⟩
    refine hinj ?_
    rw [h0, map_zero]
  · intro hdef b₁ b₂ h
    have h0 : φ (b₁ - b₂) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨c, hc, hbc, hmem⟩ :=
      (sha2ToH2_eq_zero_iff p k Ω K M φ hφ (b₁ - b₂)).mp h0
    have hzero : b₁ - b₂ = 0 := by
      rw [hbc]
      exact (hQ c hc).mpr (hdef c hc hmem)
    exact sub_eq_zero.mp hzero

end Work.SSGRoute
