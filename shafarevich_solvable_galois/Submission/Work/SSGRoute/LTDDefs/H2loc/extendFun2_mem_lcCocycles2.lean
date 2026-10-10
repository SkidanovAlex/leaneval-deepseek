import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.H2locAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDDefs.H2loc

theorem extendFun2_mem_lcCocycles2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : ↥H × ↥H → M} (hc : c ∈ Work.AbsoluteKummer.Z2 ↥H M) :
    extendFun2 H c ∈ lcCocycles2 p k Ω K M H := by
  obtain ⟨hcocyc, hlcf⟩ := (Work.AbsoluteKummer.mem_Z2_iff c).mp hc
  refine ⟨?_, ?_⟩
  · -- the `2`-cocycle identity on `H`: on `H × H` the extension agrees with `c`
    intro g hg h hh l hl
    have h1 := hcocyc ⟨g, hg⟩ ⟨h, hh⟩ ⟨l, hl⟩
    rw [show (⟨g, hg⟩ * ⟨h, hh⟩ : ↥H) = ⟨g * h, H.mul_mem hg hh⟩ from Subtype.ext rfl,
      show (⟨h, hh⟩ * ⟨l, hl⟩ : ↥H) = ⟨h * l, H.mul_mem hh hl⟩ from Subtype.ext rfl] at h1
    rw [extendFun2_apply H c hh hl, extendFun2_apply H c (H.mul_mem hg hh) hl,
      extendFun2_apply H c hg (H.mul_mem hh hl), extendFun2_apply H c hg hh]
    rw [show SSGRoute.res k K g • c (⟨h, hh⟩, ⟨l, hl⟩) = (⟨g, hg⟩ : ↥H) • c (⟨h, hh⟩, ⟨l, hl⟩)
        from (hcompat ⟨g, hg⟩ _).symm]
    have h2 : (⟨g, hg⟩ : ↥H) • c (⟨h, hh⟩, ⟨l, hl⟩) - c (⟨g * h, H.mul_mem hg hh⟩, ⟨l, hl⟩)
        + c (⟨g, hg⟩, ⟨h * l, H.mul_mem hh hl⟩) - c (⟨g, hg⟩, ⟨h, hh⟩)
        = ((⟨g, hg⟩ : ↥H) • c (⟨h, hh⟩, ⟨l, hl⟩) + c (⟨g, hg⟩, ⟨h * l, H.mul_mem hh hl⟩))
          - (c (⟨g * h, H.mul_mem hg hh⟩, ⟨l, hl⟩) + c (⟨g, hg⟩, ⟨h, hh⟩)) := by abel
    rw [h2, ← h1, sub_self]
  · -- local constancy: `c` is uniformly locally constant on `↥H × ↥H`, so the extension by `0`
    -- is invariant under left translation by `U ∩ H` for a single open subgroup `U ≤ G_k`
    obtain ⟨U, hUo, hU⟩ := exists_openSubgroup_pair_mul_eq_of_isLocallyConstant k Ω H hH
      (f := c) hlcf
    refine ⟨U, hUo, ?_⟩
    intro g hg h hh u hu v hv huH hvH
    have h1 := hU ⟨g, hg⟩ ⟨h, hh⟩ u v huH hvH hu hv
    rw [show (⟨g, hg⟩ * ⟨u, huH⟩ : ↥H) = ⟨g * u, H.mul_mem hg huH⟩ from Subtype.ext rfl,
      show (⟨h, hh⟩ * ⟨v, hvH⟩ : ↥H) = ⟨h * v, H.mul_mem hh hvH⟩ from Subtype.ext rfl] at h1
    rw [extendFun2_apply H c (H.mul_mem hg huH) (H.mul_mem hh hvH),
      extendFun2_apply H c hg hh, h1]

end Work.SSGRoute.LTDDefs.H2loc
