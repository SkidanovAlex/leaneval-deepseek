import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.PT.ContModule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The natural map `Ш²(k,M) → H²_cont(G_k, M)`

`Ш²(k,M) = Z²_loc / B²` is the quotient of the locally trivial continuous `2`-cocycles
`G_k = Ω ≃ₐ[k] Ω → M` by the (global) coboundaries, while
`H²_cont(G_k, M) = Z²_cont / B²_cont` is the quotient of all continuous `2`-cocycles by the same
coboundaries (the carriers of `B2top` and `B2contS` are *identical*: both consist of the cochains
arising as a coboundary on `⊤`).

Since `Z²_loc ⊆ Z²_cont` and `B² = B²_cont ∩ Z²_loc`, the natural map sending the class of a
locally trivial cocycle to its class in `H²_cont` is well defined and injective; this file records
that map together with its computation rule on a representative.  This is the degree-`2` companion
of `Submission.Work.SSGRoute.PT.sha1ToH1contS`.
-/

namespace Work.SSGRoute.PT

set_option maxHeartbeats 8000000 in
theorem sha2ToH2contS
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    ∃ ι : Work.SSGRoute.Sha2 p k Ω K M →ₗ[ZMod p]
        Work.SSGRoute.H2contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤,
      Function.Injective ι ∧
      (∀ (c : ↥(Work.SSGRoute.Z2loc p k Ω K M)),
        ι (Submodule.Quotient.mk c) =
          QuotientAddGroup.mk (⟨(c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M), c.2.1, c.2.2.1⟩ :
            ↥(Work.SSGRoute.Z2cont (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K)))) := by
  classical
  -- The locally trivial cocycles and the continuous cocycles, as `ZMod p`-submodules.
  let A : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) := Work.SSGRoute.Z2loc p k Ω K M
  let C : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :=
    Work.SSGRoute.Z2contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K)
  -- The two denominators: global coboundaries inside `A`, inside `C`.  Their carriers agree.
  let P : Submodule (ZMod p) ↥A := (Work.SSGRoute.B2top p k Ω K M).comap A.subtype
  let Q : Submodule (ZMod p) ↥C :=
    (Work.SSGRoute.B2contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤).comap C.subtype
  -- The inclusion `Z²_loc ↪ Z²_cont` (the first two components of the membership).
  let F : ↥A →ₗ[ZMod p] ↥C :=
    (A.subtype).codRestrict C (fun x => ⟨x.2.1, x.2.2.1⟩)
  -- `P` is exactly the preimage of `Q`, so the induced map on quotients is injective.
  have hPQ : P ≤ Q.comap F := by
    intro x hx
    rw [Submodule.mem_comap, Submodule.mem_comap]
    exact hx
  have hcomap : Submodule.comap F Q = P := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_comap]
    exact Iff.rfl
  refine ⟨Submodule.mapQ P Q F hPQ, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    have hker : (Submodule.mapQ P Q F hPQ).ker =
        Submodule.map P.mkQ (Submodule.comap F Q) := Submodule.ker_mapQ P Q F hPQ
    rw [hker, hcomap]
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hyx, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  · intro c
    rw [Submodule.mapQ_apply]
    congr 1

end Work.SSGRoute.PT
