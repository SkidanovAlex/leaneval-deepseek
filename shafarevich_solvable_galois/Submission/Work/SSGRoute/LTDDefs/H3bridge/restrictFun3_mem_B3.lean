import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.H3loc.Defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.kummerBase_euler_h3loc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of a `3`-coboundary on `H` is a continuous `3`-coboundary of `↥H`

`Work.SSGRoute.LTDDefs.H3loc.restrictFun3_mem_Z3` shows that the restriction `restrictFun3 H e`
of a locally constant `3`-cocycle on `H ≤ G_k` is a *continuous* `3`-cocycle of the group `↥H`
(an element of `Z3 ↥H`).  The present file proves the matching statement one degree of exactness
down: if `e` is a *coboundary*, namely the `d²` of a locally constant `2`-cochain on `H`, then its
restriction is `d²` of a locally constant `2`-cochain of `↥H`, i.e. lies in `B3 ↥H`.

This is the exact analogue of the degree-`2` statement
`Work.SSGRoute.LTDDefs.H2loc.restrictFun2_mem_B2`; the only difference is one more variable and the
extra boundary term `- b g h` of `d²`, which is handled by the same rewriting argument.
-/

namespace Work.SSGRoute.LTDDefs.H3bridge

open Classical

theorem restrictFun3_mem_B3 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (he : e ∈ Work.SSGRoute.lcCocycles3 p k Ω K M H)
    (hb : e ∈ Work.SSGRoute.coboundaries3 p k Ω K M H) :
    Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H e ∈ Work.SSGRoute.B3 (M := M) ↥H := by
  rw [Work.SSGRoute.mem_B3_iff]
  obtain ⟨b, hbloc, hbeq⟩ := (Work.SSGRoute.mem_coboundaries3 p k Ω K M H e).mp hb
  refine ⟨fun q : ↥H × ↥H => b (q.1 : Ω ≃ₐ[k] Ω) (q.2 : Ω ≃ₐ[k] Ω), ?_, ?_⟩
  · -- Local constancy of `(g, h) ↦ b g h` on `↥H × ↥H`.
    intro x
    obtain ⟨U, hUo, hU⟩ := hbloc
    refine ⟨{y : ↥H × ↥H |
        ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω)) ∈ U ∧
        ((x.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2 : Ω ≃ₐ[k] Ω)) ∈ U}, ?_, ?_, ?_⟩
    · refine IsOpen.inter ?_ ?_
      · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp continuous_fst)
      · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp continuous_snd)
    · exact ⟨by rw [inv_mul_cancel]; exact U.one_mem,
        by rw [inv_mul_cancel]; exact U.one_mem⟩
    · intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      have h1H : (x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω) ∈ H :=
        H.mul_mem (H.inv_mem x.1.2) y.1.2
      have h2H : (x.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2 : Ω ≃ₐ[k] Ω) ∈ H :=
        H.mul_mem (H.inv_mem x.2.2) y.2.2
      have key := hU (x.1 : Ω ≃ₐ[k] Ω) x.1.2 (x.2 : Ω ≃ₐ[k] Ω) x.2.2
        ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω)) hy1
        ((x.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2 : Ω ≃ₐ[k] Ω)) hy2 h1H h2H
      have e1 : (x.1 : Ω ≃ₐ[k] Ω) * ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω))
          = (y.1 : Ω ≃ₐ[k] Ω) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      have e2 : (x.2 : Ω ≃ₐ[k] Ω) * ((x.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2 : Ω ≃ₐ[k] Ω))
          = (y.2 : Ω ≃ₐ[k] Ω) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      show b (y.1 : Ω ≃ₐ[k] Ω) (y.2 : Ω ≃ₐ[k] Ω)
        = b (x.1 : Ω ≃ₐ[k] Ω) (x.2 : Ω ≃ₐ[k] Ω)
      rw [← e1, ← e2]
      exact key
  · -- `d²` of the restricted cochain is the restriction of `e`.
    funext q
    obtain ⟨g, h, l⟩ := q
    show (g : ↥H) • b (h : Ω ≃ₐ[k] Ω) (l : Ω ≃ₐ[k] Ω)
        - b ((g * h : ↥H) : Ω ≃ₐ[k] Ω) (l : Ω ≃ₐ[k] Ω)
        + b (g : Ω ≃ₐ[k] Ω) ((h * l : ↥H) : Ω ≃ₐ[k] Ω)
        - b (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω)
        = e (g : Ω ≃ₐ[k] Ω) (h : Ω ≃ₐ[k] Ω) (l : Ω ≃ₐ[k] Ω)
    rw [hcompat g (b (h : Ω ≃ₐ[k] Ω) (l : Ω ≃ₐ[k] Ω)), Subgroup.coe_mul, Subgroup.coe_mul,
      hbeq (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2 (l : Ω ≃ₐ[k] Ω) l.2,
      Work.SSGRoute.dCochain2_apply]

end Work.SSGRoute.LTDDefs.H3bridge
