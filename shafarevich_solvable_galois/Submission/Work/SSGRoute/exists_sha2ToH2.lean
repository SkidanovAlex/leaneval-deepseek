import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.bridge_isCocycle2_mem_Z2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **The cocycle-level bridge `Ш²(k,M) → H²(G_k, M)`** (piece 4 of the design of the node
`Work.SSGRoute.ext_sha2_bridge`, E1a): the `SSGRoute` locally trivial `2`-cocycles of
`G_k = Ω ≃ₐ[k] Ω` with coefficients in a `Gal(K/k)`-module `M` project to the *abstract* group
cohomology `H²(G_k, M)` for the action of `G_k` on `M` obtained by pulling back the
`Gal(K/k)`-action along `res k K : G_k →* Gal(K/k)`; the map respects the quotient
`Ш²(k,M) = Z²_loc / B²` and is computed on representatives by the quotient map `H2π`.

Here `Z2loc p k Ω K M` is the `SSGRoute` submodule of locally trivial `2`-cocycles and
`Sha2 p k Ω K M := ↥(Z2loc) ⧸ (B2top).comap (Z2loc).subtype`.

Proof route.  The cocycle condition is the bridge lemma
`Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K) : IsCocycle2 act c ↔ c ∈ Z²(G_k, M)`
for the pulled-back action `DistribMulAction.compHom M (SSGRoute.res k K)`.  Build the additive map
`↥(Z2loc) →+ H²(G_k,M)`, `x ↦ H2π ⟨fun q => x.1 q.1 q.2, _⟩`, and factor it through the quotient
with `QuotientAddGroup.lift` (the subgroup being the submodule `(B2top).comap (Z2loc).subtype`,
coerced to an `AddSubgroup`; the two quotient spellings `Submodule.Quotient` and
`QuotientAddGroup` agree definitionally because `Submodule.quotientRel`
is `QuotientAddGroup.leftRel p.toAddSubgroup`).  The vanishing on the coboundaries is
`IsCoboundary2On (res k K) ⊤ c` ⟹ `∃ b, d¹b = c` (`H2pi_eq_zero_iff` + `mem_B2_iff`).
Beware: a `local instance : DistribMulAction (Ω ≃ₐ[k] Ω) M :=
DistribMulAction.compHom M (SSGRoute.res k K)` is **rejected** by Lean ("cannot find
synthesization order": the subgroup `K` is not inferable from the type); use `letI` inside the
proof body and spell the instance out with `@` in the statement, as this statement does. -/
theorem exists_sha2ToH2 (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    ∃ φ : Work.SSGRoute.Sha2 p k Ω K M →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)),
      ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K M),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2,
                (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
                  (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2)).mp hc.1⟩ := by
  -- The pulled-back action of `G_k` on `M`, spelled out because it is not synthesizable.
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  -- The inclusion of the locally trivial `2`-cocycles into all `2`-cocycles: on values it is
  -- the identity, and the cocycle condition is transported by the bridge lemma.
  let inc : ↥(Z2loc p k Ω K M) →+ Work.GroupCohomology.Z2 (Ω ≃ₐ[k] Ω) M :=
    { toFun := fun x => ⟨fun q => x.1 q.1 q.2,
        (bridge_isCocycle2_mem_Z2 (SSGRoute.res k K) (fun q => x.1 q.1 q.2)).mp x.2.1⟩
      map_zero' := by
        apply Subtype.ext
        funext q
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        funext q
        simp }
  -- The map on cocycles, `H2π ∘ inc`.
  let f : ↥(Z2loc p k Ω K M) →+ @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
      (DistribMulAction.compHom M (SSGRoute.res k K)) :=
    (Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M).comp inc
  -- `f` kills the global coboundaries, so it descends to `Ш²(k,M)`.
  have hNA : ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype).toAddSubgroup ≤ f.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    change (Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M) (inc x) = 0
    rw [Work.GroupCohomology.H2pi_eq_zero_iff, Work.GroupCohomology.mem_B2_iff]
    obtain ⟨b, _hb, hbc⟩ := hx
    refine ⟨b, ?_⟩
    funext q
    obtain ⟨g, h⟩ := q
    simp only [Work.GroupCohomology.d1_apply]
    change (SSGRoute.res k K) g • b h - b (g * h) + b g = x.1 g h
    exact (hbc g trivial h trivial).symm
  refine ⟨QuotientAddGroup.lift
    ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype).toAddSubgroup f hNA, ?_⟩
  intro c hc
  -- The two spellings of the quotient class agree definitionally.
  have h1 : (Submodule.Quotient.mk ⟨c, hc⟩ : Sha2 p k Ω K M) =
      (QuotientAddGroup.mk (⟨c, hc⟩ : ↥(Z2loc p k Ω K M)) :
        ↥(Z2loc p k Ω K M) ⧸ ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype).toAddSubgroup) :=
    rfl
  rw [h1]
  exact (QuotientAddGroup.lift_mk
    ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype).toAddSubgroup hNA
    (⟨c, hc⟩ : ↥(Z2loc p k Ω K M))).trans rfl

end Work.SSGRoute
