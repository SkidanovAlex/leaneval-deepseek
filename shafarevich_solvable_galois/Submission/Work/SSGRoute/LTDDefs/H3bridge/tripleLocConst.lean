/-
# Uniform local constancy in three variables on a closed subgroup of `G_k`

This file proves `Work.SSGRoute.LTDDefs.H3bridge.tripleLocConst`, the degree-`3` analogue of
`Work.SSGRoute.exists_openSubgroup_pair_mul_eq_of_isLocallyConstant`
(`Submission/Work/SSGRoute/LTDDefs/H2locAux.lean`): a locally constant function on the third power
of a closed subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω` is right invariant, uniformly in the base point, under a
single open subgroup `U ≤ G_k`.

The proof is a direct application of the general uniform-local-constancy theorem
`Work.SSGRoute.exists_openSubgroup_forall_mul_eq` to the product group `↥H × ↥H × ↥H`, combined with
`Work.SSGRoute.exists_openSubgroup_inter_subset_of_isOpen`, which produces the open subgroup of the
ambient group `G_k` out of an open subgroup of `↥H`.  The only extra ingredient is the standard
"diagonal" construction: from an open subgroup `W` of the product group one obtains an open
subgroup `V ≤ ↥H` consisting of the elements `u` with `(u, 1)`, `(1, (u, 1))` and `(1, (1, u))`
all in `W`; then `(u, v, w) ∈ W` for all `u, v, w ∈ V`, because `(u, (v, w))` is the product of
those three elements.
-/
import Mathlib
import Submission.Work.SSGRoute.LTDDefs.H2locAux
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.LTDDefs.H3bridge

open Filter Topology
open scoped Pointwise

theorem tripleLocConst (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    {M : Type} {f : ↥H × ↥H × ↥H → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ (x y z : ↥H) (u v w : Ω ≃ₐ[k] Ω) (hu : u ∈ H) (hv : v ∈ H) (hw : w ∈ H),
        u ∈ U → v ∈ U → w ∈ U →
        f (x * ⟨u, hu⟩, y * ⟨v, hv⟩, z * ⟨w, hw⟩) = f (x, y, z) := by
  -- `↥H` is a compact totally disconnected group, hence so is `↥H × ↥H × ↥H`
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.mp hH.isCompact
  -- uniform local constancy on the product group: a single open subgroup `W` does the job
  obtain ⟨W, hWo, hW⟩ := Work.SSGRoute.exists_openSubgroup_forall_mul_eq
    (G := ↥H × ↥H × ↥H) (f := f) hf
  -- the three coordinate embeddings `↥H →* ↥H × ↥H × ↥H`
  let φ₁ : ↥H →* ↥H × ↥H × ↥H := MonoidHom.inl ↥H (↥H × ↥H)
  let φ₂ : ↥H →* ↥H × ↥H × ↥H := (MonoidHom.inr ↥H (↥H × ↥H)).comp (MonoidHom.inl ↥H ↥H)
  let φ₃ : ↥H →* ↥H × ↥H × ↥H := (MonoidHom.inr ↥H (↥H × ↥H)).comp (MonoidHom.inr ↥H ↥H)
  -- the "diagonal" open subgroup of `↥H`
  let V : Subgroup ↥H := (W.comap φ₁) ⊓ ((W.comap φ₂) ⊓ (W.comap φ₃))
  have hcomap : ∀ (φ : ↥H →* ↥H × ↥H × ↥H), Continuous (φ : ↥H → ↥H × ↥H × ↥H) →
      IsOpen ((W.comap φ : Subgroup ↥H) : Set ↥H) := by
    intro φ hφ
    rw [Subgroup.coe_comap]
    exact hWo.preimage hφ
  have hVo : IsOpen (V : Set ↥H) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]
    refine IsOpen.inter (hcomap φ₁ ?_) (IsOpen.inter (hcomap φ₂ ?_) (hcomap φ₃ ?_))
    · exact continuous_id.prodMk (continuous_const.prodMk continuous_const)
    · exact continuous_const.prodMk (continuous_id.prodMk continuous_const)
    · exact continuous_const.prodMk (continuous_const.prodMk continuous_id)
  -- lift `V` to an open subgroup `U` of the ambient group `G_k`
  obtain ⟨U, hUo, hU⟩ := Work.SSGRoute.exists_openSubgroup_inter_subset_of_isOpen k Ω H V hVo
  refine ⟨U, hUo, ?_⟩
  intro x y z u v w hu hv hw huU hvU hwU
  have hux : (⟨u, hu⟩ : ↥H) ∈ V := hU u huU hu
  have hvx : (⟨v, hv⟩ : ↥H) ∈ V := hU v hvU hv
  have hwx : (⟨w, hw⟩ : ↥H) ∈ V := hU w hwU hw
  have e1 : ((⟨u, hu⟩ : ↥H), ((1 : ↥H), (1 : ↥H))) ∈ W :=
    Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hux).1
  have e2 : ((1 : ↥H), ((⟨v, hv⟩ : ↥H), (1 : ↥H))) ∈ W :=
    Subgroup.mem_comap.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hvx).2).1
  have e3 : ((1 : ↥H), ((1 : ↥H), (⟨w, hw⟩ : ↥H))) ∈ W :=
    Subgroup.mem_comap.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hwx).2).2
  -- `(u, (v, w)) ∈ W` as a product of the three coordinate embeddings
  have hmem : ((⟨u, hu⟩ : ↥H), ((⟨v, hv⟩ : ↥H), (⟨w, hw⟩ : ↥H))) ∈ W := by
    have h := W.mul_mem (W.mul_mem e1 e2) e3
    rwa [show ((⟨u, hu⟩ : ↥H), ((1 : ↥H), (1 : ↥H))) *
        ((1 : ↥H), ((⟨v, hv⟩ : ↥H), (1 : ↥H))) *
        ((1 : ↥H), ((1 : ↥H), (⟨w, hw⟩ : ↥H))) =
        ((⟨u, hu⟩ : ↥H), ((⟨v, hv⟩ : ↥H), (⟨w, hw⟩ : ↥H))) from rfl] at h
  exact hW (x, y, z) (⟨u, hu⟩, (⟨v, hv⟩, ⟨w, hw⟩)) hmem

end Work.SSGRoute.LTDDefs.H3bridge
