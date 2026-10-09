import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.H2locAux
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of a locally constant `2`-cocycle on `H` to the group `H`

`LTDDefs/Basic.lean` models the local cohomology `H2loc` of a subgroup
`H ≤ G_k = Ω ≃ₐ[k] Ω` by `2`-cochains on the whole group `G_k` satisfying the `2`-cocycle and
local-constancy conditions only on `H`.  The comparison with the workspace's continuous-cochain
model `Work.AbsoluteKummer.H2 ↥H M` (`LTDDefs/H2locEquivH2.lean`) is built from the raw
restriction map `restrictFun2 H` together with the extension by `0` off `H`.

The file `LTDDefs/H1loc_iso_H1cont.lean` performs the analogous one-degree analysis for
`1`-cocycles.  Here we show that restriction of a locally constant `2`-cocycle on `H`
(a function on `G_k × G_k`) to `H × H` is a *continuous* `2`-cocycle of `H`, i.e. lies in
`Work.AbsoluteKummer.Z2 ↥H M`:

* the two-variable `2`-cocycle identity on `H` follows from `IsCocycle2On` by evaluating on the
  coercions into `G_k` (`restrictFun2_isCocycle`), using `hcompat` to identify the
  `↥H`-action with the `Gal(K/k)`-action;
* local constancy on `↥H × ↥H` follows from the uniform right-invariance recorded by
  `IsLocConst2On` (`restrictFun2_isLocallyConstant`).

## Main results

* `Work.SSGRoute.LTDDefs.H2loc.restrictFun2_isCocycle`;
* `Work.SSGRoute.LTDDefs.H2loc.restrictFun2_isLocallyConstant`;
* `Work.SSGRoute.LTDDefs.H2loc.restrictFun2_mem_Z2`.
-/

namespace Work.SSGRoute.LTDDefs.H2loc

/-- An elementary rearrangement in an additive commutative group:
`a - b + c - d = 0` implies `b + d = a + c`. -/
private lemma add_eq_of_sub_add_sub_eq_zero {A : Type*} [AddCommGroup A] (a b c d : A)
    (h : a - b + c - d = 0) : b + d = a + c := by
  have h1 : a + c - (b + d) = 0 := by rw [← h]; abel
  exact (sub_eq_zero.mp h1).symm

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]

/-- **The `2`-cocycle identity for the restriction.**  If `c` satisfies the `2`-cocycle identity
on `H` (viewed inside `G_k`, with `G_k` acting through `Gal(K/k)`), then its restriction
`restrictFun2 H c` satisfies the `2`-cocycle identity on the abstract group `↥H` for the given
action of `↥H` on `M`. -/
lemma restrictFun2_isCocycle
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : IsCocycle2On p k Ω K M H c) :
    ∀ g h l : ↥H, restrictFun2 H c (g * h, l) + restrictFun2 H c (g, h)
      = g • restrictFun2 H c (h, l) + restrictFun2 H c (g, h * l) := by
  intro g h l
  have h1 := hc (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2 (l : Ω ≃ₐ[k] Ω) l.2
  simp only [restrictFun2_apply, Subgroup.coe_mul] at h1 ⊢
  rw [hcompat g (c h l)]
  exact add_eq_of_sub_add_sub_eq_zero _ _ _ _ h1

/-- **Local constancy of the restriction.**  A `2`-cochain on `G_k` which is right invariant by an
open subgroup of `G_k` (uniformly over `H`) restricts to a locally constant function on the
topological group `↥H × ↥H`. -/
lemma restrictFun2_isLocallyConstant {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (hc : IsLocConst2On p k Ω K M H c) :
    Work.AbsoluteKummer.IsLocallyConstant (restrictFun2 H c) := by
  obtain ⟨U, hUo, hU⟩ := hc
  intro x
  refine ⟨{y : ↥H × ↥H | ((x.1 : Ω ≃ₐ[k] Ω)⁻¹ * (y.1 : Ω ≃ₐ[k] Ω)) ∈ U ∧
      ((x.2 : Ω ≃ₐ[k] Ω)⁻¹ * (y.2 : Ω ≃ₐ[k] Ω)) ∈ U}, ?_, ?_, ?_⟩
  · refine IsOpen.inter ?_ ?_
    · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp continuous_fst)
    · exact hUo.preimage ((continuous_const.mul continuous_subtype_val).comp continuous_snd)
  · exact ⟨by rw [inv_mul_cancel]; exact U.one_mem, by rw [inv_mul_cancel]; exact U.one_mem⟩
  · intro y hy
    simp only [Set.mem_ofPred_eq] at hy
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
    show c (y.1 : Ω ≃ₐ[k] Ω) (y.2 : Ω ≃ₐ[k] Ω) = c (x.1 : Ω ≃ₐ[k] Ω) (x.2 : Ω ≃ₐ[k] Ω)
    rw [← e1, ← e2, key]

/-- **Restriction to `H` of a locally constant `2`-cocycle on `H` is a continuous `2`-cocycle of
the group `↥H`**: `restrictFun2 H c ∈ Z²_c(↥H, M)`. -/
theorem restrictFun2_mem_Z2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : c ∈ lcCocycles2 p k Ω K M H) :
    restrictFun2 H c ∈ Work.AbsoluteKummer.Z2 ↥H M := by
  rw [Work.AbsoluteKummer.mem_Z2_iff]
  exact ⟨restrictFun2_isCocycle p k Ω K M H hcompat hc.1,
    restrictFun2_isLocallyConstant p k Ω K M H hc.2⟩

end Work.SSGRoute.LTDDefs.H2loc
