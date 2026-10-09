import Mathlib
import Submission.Work.Tate.Basic
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Pointwise TensorProduct

set_option linter.style.haveILetI false

/-- If a group `G` acts additively on `M` and this action commutes with the `ZMod p`-scalars,
then for every `γ : G` the map `x ↦ γ • x` is `ZMod p`-linear. -/
def smulLinearMap (p : ℕ) (G : Type) [Group G] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (γ : G) : M →ₗ[ZMod p] M where
  toFun := fun x => γ • x
  map_add' := fun x y => smul_add γ x y
  map_smul' := fun c x => smul_comm γ c x

@[simp]
lemma smulLinearMap_apply (p : ℕ) (G : Type) [Group G] (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (γ : G) (x : M) :
    smulLinearMap p G M γ x = γ • x := rfl

theorem exists_finite_stable_submodule_family (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    (S : Set M) (hS : S.Finite) {ι : Type} [Fintype ι] (m : ι → M ⊗[ZMod p] T) :
    ∃ (W : Submodule (ZMod p) M), S ⊆ (W : Set M) ∧ (∀ (γ : G) (w : M), w ∈ W → γ • w ∈ W) ∧
      Finite ↥W ∧ ∃ (m' : ι → ↥W ⊗[ZMod p] T),
        ∀ i, TensorProduct.map W.subtype (LinearMap.id) (m' i) = m i := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- A finitely generated submodule of `M` whose tensor product with `T` already carries all `m i`.
  obtain ⟨M', hM'fin, hm'⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite (Set.range m) (Set.finite_range m)
  -- A finite generating set of `M'`.
  obtain ⟨S', hS'fin, hS'span⟩ := Submodule.fg_def.mp ((Module.Finite.iff_fg).mp hM'fin)
  -- The finite set `B = S ∪ S'` and its `G`-orbit `A`.
  set B : Set M := S ∪ S' with hBdef
  set A : Set M := ⋃ γ : G, γ • B with hAdef
  have hBfin : B.Finite := hS.union hS'fin
  have hAfin : A.Finite := Set.finite_iUnion fun γ : G => hBfin.smul_set
  set W : Submodule (ZMod p) M := Submodule.span (ZMod p) A with hWdef
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · -- `S ⊆ W`
    intro x hx
    exact Submodule.subset_span
      (Set.mem_iUnion.mpr ⟨1, Set.mem_smul_set.mpr ⟨x, Or.inl hx, one_smul G x⟩⟩)
  · -- `W` is `G`-stable
    intro γ w hw
    have hAA : (fun z => smulLinearMap p G M γ z) '' A ⊆ A := by
      rintro y ⟨z, hz, rfl⟩
      rw [hAdef] at hz ⊢
      obtain ⟨δ, hδ⟩ := Set.mem_iUnion.mp hz
      obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hδ
      exact Set.mem_iUnion.mpr ⟨γ * δ, Set.mem_smul_set.mpr ⟨b, hb, mul_smul γ δ b⟩⟩
    have hmaple : Submodule.map (smulLinearMap p G M γ) W ≤ W := by
      rw [hWdef, Submodule.map_span]
      exact Submodule.span_mono hAA
    exact hmaple (Submodule.mem_map_of_mem hw)
  · -- `W` is finite
    rw [hWdef]
    exact Set.Finite.submoduleSpan (ZMod p) hAfin
  · -- lifting the family `m`
    have hMW : M' ≤ W := by
      rw [← hS'span, hWdef]
      refine Submodule.span_le.mpr fun x hx => Submodule.subset_span ?_
      exact Set.mem_iUnion.mpr ⟨1, Set.mem_smul_set.mpr ⟨x, Or.inr hx, one_smul G x⟩⟩
    have hrange : LinearMap.range (LinearMap.rTensor T M'.subtype)
        ≤ LinearMap.range (LinearMap.rTensor T W.subtype) := by
      have heq : LinearMap.rTensor T M'.subtype
          = LinearMap.rTensor T W.subtype ∘ₗ LinearMap.rTensor T (Submodule.inclusion hMW) := by
        rw [show M'.subtype = W.subtype ∘ₗ Submodule.inclusion hMW from
          (Submodule.subtype_comp_inclusion M' W hMW).symm, LinearMap.rTensor_comp]
      rw [heq]
      exact LinearMap.range_comp_le_range _ _
    have hmem : ∀ i, m i ∈ LinearMap.range (LinearMap.rTensor T W.subtype) :=
      fun i => hrange (hm' (Set.mem_range_self i))
    refine ⟨fun i => (LinearMap.mem_range.mp (hmem i)).choose, fun i => ?_⟩
    have hspec := (LinearMap.mem_range.mp (hmem i)).choose_spec
    simpa only [LinearMap.rTensor_def] using hspec

end Work.SSGRoute
