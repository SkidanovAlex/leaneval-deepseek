import Mathlib
import Submission.Work.SSGRoute.LTDDefs.H3loc.Defs
import Submission.Work.SSGRoute.kummerBase_euler_h3loc
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.LTDDefs.H3bridge.tripleLocConst
import Submission.Work.SSGRoute.LTDDefs.H2locAux
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDDefs.H3bridge

open Classical

theorem extendFun3_mem_lcCocycles3 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : ↥H × ↥H × ↥H → M} (hc : c ∈ Work.SSGRoute.Z3 (M := M) ↥H) :
    Work.SSGRoute.LTDDefs.H3loc.extendFun3 H c ∈ Work.SSGRoute.lcCocycles3 p k Ω K M H := by
  obtain ⟨hcocyc, hlcf⟩ := (Work.SSGRoute.mem_Z3_iff (G := ↥H) (M := M)).mp hc
  refine ⟨?_, ?_⟩
  · -- the `3`-cocycle identity on `H`, transported from the `d³c = 0` of the model
    intro g hg h hh l hl m hm
    have h3 := congrFun hcocyc (⟨g, hg⟩, ⟨h, hh⟩, ⟨l, hl⟩, ⟨m, hm⟩)
    simp only [Pi.zero_apply, Work.SSGRoute.d3_apply] at h3
    rw [show (⟨g, hg⟩ * ⟨h, hh⟩ : ↥H) = ⟨g * h, H.mul_mem hg hh⟩ from Subtype.ext rfl,
      show (⟨h, hh⟩ * ⟨l, hl⟩ : ↥H) = ⟨h * l, H.mul_mem hh hl⟩ from Subtype.ext rfl,
      show (⟨l, hl⟩ * ⟨m, hm⟩ : ↥H) = ⟨l * m, H.mul_mem hl hm⟩ from Subtype.ext rfl] at h3
    rw [Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c hh hl hm,
      Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c (H.mul_mem hg hh) hl hm,
      Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c hg (H.mul_mem hh hl) hm,
      Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c hg hh (H.mul_mem hl hm),
      Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c hg hh hl,
      ← hcompat ⟨g, hg⟩ (c (⟨h, hh⟩, ⟨l, hl⟩, ⟨m, hm⟩))]
    exact h3
  · -- local constancy: `c` is uniformly locally constant on `↥H × ↥H × ↥H`
    obtain ⟨U, hUo, hU⟩ := tripleLocConst k Ω H hH hlcf
    refine ⟨U, hUo, ?_⟩
    intro g hg h hh l hl u hu v hv w hw huH hvH hwH
    have key := hU ⟨g, hg⟩ ⟨h, hh⟩ ⟨l, hl⟩ u v w huH hvH hwH hu hv hw
    rw [show (⟨g, hg⟩ * ⟨u, huH⟩ : ↥H) = ⟨g * u, H.mul_mem hg huH⟩ from Subtype.ext rfl,
      show (⟨h, hh⟩ * ⟨v, hvH⟩ : ↥H) = ⟨h * v, H.mul_mem hh hvH⟩ from Subtype.ext rfl,
      show (⟨l, hl⟩ * ⟨w, hwH⟩ : ↥H) = ⟨l * w, H.mul_mem hl hwH⟩ from Subtype.ext rfl] at key
    rw [Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c (H.mul_mem hg huH) (H.mul_mem hh hvH)
        (H.mul_mem hl hwH),
      Work.SSGRoute.LTDDefs.H3loc.extendFun3_apply H c hg hh hl]
    exact key

end Work.SSGRoute.LTDDefs.H3bridge
