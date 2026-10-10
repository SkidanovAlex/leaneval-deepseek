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
# Restriction of a locally constant `3`-cocycle on `H` to the group `H`

`LTDDefs/H3loc/Defs.lean` models the local cohomology `H3loc` of a subgroup
`H ≤ G_k = Ω ≃ₐ[k] Ω` by `3`-cochains on the whole group `G_k` satisfying the `3`-cocycle and
local-constancy conditions only on `H`.  The comparison with the workspace's continuous-cochain
model `Work.SSGRoute.H3 ↥H M` is built from the raw restriction map `restrictFun3 H` together with
the extension by `0` off `H`, exactly as in degree `2`
(`LTDDefs/H2loc/restrictFun2_mem_Z2.lean`).

Here we show that restriction of a locally constant `3`-cocycle on `H` (a function on `G_k³`) to
`H³` is a *continuous* `3`-cocycle of `H`, i.e. lies in `Work.SSGRoute.Z3 ↥H`:

* the three-variable `3`-cocycle identity on `H` follows from `IsCocycle3On` by evaluating on the
  coercions into `G_k` (`restrictFun3_isCocycle`), using `hcompat` to identify the `↥H`-action with
  the `Gal(K/k)`-action;
* local constancy on `↥H × ↥H × ↥H` follows from the uniform right-invariance recorded by
  `IsLocConst3On` (`restrictFun3_isLocallyConstant`).

## Main results

* `Work.SSGRoute.LTDDefs.H3loc.restrictFun3_isCocycle`;
* `Work.SSGRoute.LTDDefs.H3loc.restrictFun3_isLocallyConstant`;
* `Work.SSGRoute.LTDDefs.H3loc.restrictFun3_mem_Z3`.
-/

namespace Work.SSGRoute.LTDDefs.H3loc

open Classical

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]

/-- **The `3`-cocycle identity for the restriction.**  If `e` satisfies the `3`-cocycle identity
on `H` (viewed inside `G_k`, with `G_k` acting through `Gal(K/k)`), then its restriction
`restrictFun3 H e` satisfies the `3`-cocycle identity on the abstract group `↥H` for the given
action of `↥H` on `M`, i.e. `d³(restrictFun3 H e) = 0`. -/
lemma restrictFun3_isCocycle
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (he : IsCocycle3On p k Ω K M H e) :
    SSGRoute.d3 (restrictFun3 H e) = 0 := by
  funext q
  obtain ⟨g, h, l, m⟩ := q
  have h1 := he (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2 (l : Ω ≃ₐ[k] Ω) l.2
    (m : Ω ≃ₐ[k] Ω) m.2
  simp only [SSGRoute.d3_apply, restrictFun3_apply, Subgroup.coe_mul]
  rw [hcompat g (e h l m)]
  exact h1

/-- **Local constancy of the restriction.**  A `3`-cochain on `G_k` which is right invariant by an
open subgroup of `G_k` (uniformly over `H`) restricts to a locally constant function on the
topological space `↥H × ↥H × ↥H`. -/
lemma restrictFun3_isLocallyConstant
    {e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (he : IsLocConst3On p k Ω K M H e) :
    Work.AbsoluteKummer.IsLocallyConstant (restrictFun3 H e) := by
  obtain ⟨U, hUo, hU⟩ := he
  intro x
  refine ⟨{y : ↥H × ↥H × ↥H |
      ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω)) ∈ U ∧
      ((x.2.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.1 : Ω ≃ₐ[k] Ω)) ∈ U ∧
      ((x.2.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.2 : Ω ≃ₐ[k] Ω)) ∈ U}, ?_, ?_, ?_⟩
  · refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp continuous_fst)
    · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp
        continuous_snd.fst)
    · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp
        continuous_snd.snd)
  · exact ⟨by rw [inv_mul_cancel]; exact U.one_mem,
      by rw [inv_mul_cancel]; exact U.one_mem,
      by rw [inv_mul_cancel]; exact U.one_mem⟩
  · intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have h1H : (x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω) ∈ H :=
      H.mul_mem (H.inv_mem x.1.2) y.1.2
    have h2H : (x.2.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.1 : Ω ≃ₐ[k] Ω) ∈ H :=
      H.mul_mem (H.inv_mem x.2.1.2) y.2.1.2
    have h3H : (x.2.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.2 : Ω ≃ₐ[k] Ω) ∈ H :=
      H.mul_mem (H.inv_mem x.2.2.2) y.2.2.2
    have key := hU (x.1 : Ω ≃ₐ[k] Ω) x.1.2 (x.2.1 : Ω ≃ₐ[k] Ω) x.2.1.2
      (x.2.2 : Ω ≃ₐ[k] Ω) x.2.2.2
      ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω)) hy1
      ((x.2.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.1 : Ω ≃ₐ[k] Ω)) hy2
      ((x.2.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.2 : Ω ≃ₐ[k] Ω)) hy3 h1H h2H h3H
    have e1 : (x.1 : Ω ≃ₐ[k] Ω) * ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω))
        = (y.1 : Ω ≃ₐ[k] Ω) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    have e2 : (x.2.1 : Ω ≃ₐ[k] Ω) * ((x.2.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.1 : Ω ≃ₐ[k] Ω))
        = (y.2.1 : Ω ≃ₐ[k] Ω) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    have e3 : (x.2.2 : Ω ≃ₐ[k] Ω) * ((x.2.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2.2 : Ω ≃ₐ[k] Ω))
        = (y.2.2 : Ω ≃ₐ[k] Ω) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    show e (y.1 : Ω ≃ₐ[k] Ω) (y.2.1 : Ω ≃ₐ[k] Ω) (y.2.2 : Ω ≃ₐ[k] Ω)
      = e (x.1 : Ω ≃ₐ[k] Ω) (x.2.1 : Ω ≃ₐ[k] Ω) (x.2.2 : Ω ≃ₐ[k] Ω)
    rw [← e1, ← e2, ← e3]
    exact key

/-- **Restriction to `H` of a locally constant `3`-cocycle on `H` is a continuous `3`-cocycle of
the group `↥H`**: `restrictFun3 H e ∈ Z³_c(↥H, M)`. -/
theorem restrictFun3_mem_Z3 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (he : e ∈ Work.SSGRoute.lcCocycles3 p k Ω K M H) :
    Work.SSGRoute.LTDDefs.H3loc.restrictFun3 H e ∈ Work.SSGRoute.Z3 (M := M) ↥H := by
  refine (Work.SSGRoute.mem_Z3_iff (G := ↥H) (M := M)).2 ⟨?_, ?_⟩
  · exact restrictFun3_isCocycle p k Ω K M H hcompat he.1
  · exact restrictFun3_isLocallyConstant p k Ω K M H he.2

end Work.SSGRoute.LTDDefs.H3loc
