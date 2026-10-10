import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.bridge_isCocycle2_mem_Z2
import Submission.Work.SSGRoute.bridge_isLocConst2_isLocallyConstant
import Submission.Work.SSGRoute.bridge_mem_B2_isCoboundary2On
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The bridge `Ш²(k,M) → H²(G_k, M)` with values in `Work.AbsoluteKummer.H2`

`Ш²(k,M) = Z²_loc / B²` is the quotient of the locally trivial continuous `2`-cocycles
`G_k = Ω ≃ₐ[k] Ω → Ω ≃ₐ[k] Ω → M` by the global coboundaries, while
`Work.AbsoluteKummer.H2 G M = Z²_c(G,M) / B²_c(G,M)` is the *continuous* group cohomology in
degree `2` (locally constant `2`-cocycles modulo `d¹` of locally constant `1`-cochains).

The natural map sends the class of a locally trivial `2`-cocycle `c` to its class in `H²_c`, and
this file proves that it is **injective**, together with its computation rule on a representative
(the degree-`2` companion of the degree-`1` bridge and of
`Submission.Work.SSGRoute.PT.sha2ToH2contS`).

The whole content is carried by the three `SSGRoute`/`Work.AbsoluteKummer` bridges:
`bridge_isCocycle2_mem_Z2` (the cocycle condition), `bridge_isLocConst2_isLocallyConstant`
(continuity) and — the essential one for both well-definedness and injectivity —
`bridge_mem_B2_isCoboundary2On`, which identifies the *global* coboundaries of `SSGRoute` with
`B²_c(G_k, M)`: both are `d¹` of a *locally constant* `1`-cochain.
-/

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false

set_option maxHeartbeats 8000000 in
theorem sha2_to_H2AK (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    ∃ φ : Work.SSGRoute.Sha2 p k Ω K M →+
        @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) M _ _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)),
      Function.Injective φ ∧
      (∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K M)
        (h : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
          @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M _ _ _
            (DistribMulAction.compHom M (SSGRoute.res k K))),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M _ _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, h⟩) := by
  classical
  -- The action of `G_k` on `M` is the one pulled back from `Gal(K/k)`; spelled out because it is
  -- not synthesizable from the type (`K` is not recoverable from `(Ω ≃ₐ[k] Ω) → Ω ≃ₐ[k] Ω → M`).
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  -- The inclusion of the locally trivial `2`-cocycles into the continuous `2`-cocycles: on values
  -- it is the identity (up to currying), the cocycle condition is transported by
  -- `bridge_isCocycle2_mem_Z2` and continuity by `bridge_isLocConst2_isLocallyConstant`.
  let inc : ↥(Work.SSGRoute.Z2loc p k Ω K M) →+ Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M :=
    { toFun := fun x =>
        ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2, by
          rw [Work.AbsoluteKummer.mem_Z2_iff]
          exact ⟨(Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
              (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2)).mp x.2.1,
            Work.SSGRoute.bridge_isLocConst2_isLocallyConstant (G := K ≃ₐ[k] K)
              (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2) x.2.2.1⟩⟩
      map_zero' := by
        apply Subtype.ext
        funext q
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        funext q
        simp }
  -- The map on cocycles: the quotient map `H²π` of the continuous `2`-cohomology.
  let f : ↥(Work.SSGRoute.Z2loc p k Ω K M) →+ Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) M :=
    (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M).comp inc
  -- The subgroup killed by `f`: precisely the global coboundaries.
  let S : AddSubgroup ↥(Work.SSGRoute.Z2loc p k Ω K M) :=
    ((Work.SSGRoute.B2top p k Ω K M).comap (Work.SSGRoute.Z2loc p k Ω K M).subtype).toAddSubgroup
  have hmem : ∀ x : ↥(Work.SSGRoute.Z2loc p k Ω K M),
      (x ∈ S) ↔ SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ x.1 := by
    intro x
    change x ∈ (Work.SSGRoute.B2top p k Ω K M).comap (Work.SSGRoute.Z2loc p k Ω K M).subtype ↔
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ x.1
    rw [Submodule.mem_comap]
    rfl
  -- Well-definedness **and** injectivity: a locally trivial `2`-cocycle dies in `H²_c` exactly when
  -- it is a global coboundary.  This is `bridge_mem_B2_isCoboundary2On`.
  have hkey : ∀ x : ↥(Work.SSGRoute.Z2loc p k Ω K M), x ∈ S ↔ f x = 0 := by
    intro x
    have h3 : ((inc x : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → M) ∈
        Work.AbsoluteKummer.B2 (Ω ≃ₐ[k] Ω) M) ↔
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ x.1 :=
      Work.SSGRoute.bridge_mem_B2_isCoboundary2On (SSGRoute.res k K)
        (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => x.1 q.1 q.2)
    rw [hmem x, ← h3]
    exact (Work.AbsoluteKummer.H2π_eq_zero_iff (inc x)).symm
  have hS : S ≤ f.ker := fun x hx => (hkey x).mp hx
  refine ⟨QuotientAddGroup.lift S f hS, ?_, ?_⟩
  · -- the induced map is injective because `ker f = S`.
    exact (QuotientAddGroup.injective_lift_iff S f hS).mpr
      (le_antisymm hS (fun x hx => (hkey x).mpr hx))
  · intro c hc h
    -- The two spellings of the class of `c` agree definitionally.
    have h1 : (Submodule.Quotient.mk ⟨c, hc⟩ : Work.SSGRoute.Sha2 p k Ω K M) =
        (QuotientAddGroup.mk (⟨c, hc⟩ : ↥(Work.SSGRoute.Z2loc p k Ω K M)) :
          ↥(Work.SSGRoute.Z2loc p k Ω K M) ⧸
            ((Work.SSGRoute.B2top p k Ω K M).comap
              (Work.SSGRoute.Z2loc p k Ω K M).subtype).toAddSubgroup) := rfl
    rw [h1]
    have he : inc ⟨c, hc⟩ = (⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, h⟩ :
        ↥(Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) M)) := Subtype.ext rfl
    refine (QuotientAddGroup.lift_mk (N := S) (HN := hS)
      (⟨c, hc⟩ : ↥(Work.SSGRoute.Z2loc p k Ω K M))).trans ?_
    show (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M) (inc ⟨c, hc⟩) =
      (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) M)
        ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, h⟩
    rw [he]

end Work.SSGRoute.PT
