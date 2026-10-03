import Mathlib
import Submission.Work.ORHomAlg.Map

namespace Work.ORHomAlg.Flat

open Work.ORHomAlg

universe u

/-- Auxiliary congruence for right exactness of the balanced tensor product: if `g b = g b'`
then the pure tensors `tmul m b` and `tmul m b'` differ by an element in the range of `lTensor f`,
because `b - b' ∈ ker g = range f`. -/
theorem sub_tmul_mem_range {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : f.range = g.ker)
    {b b' : B} (h : g b = g b') (m : M) :
    BalancedTensor.tmul R m b - BalancedTensor.tmul R m b' ∈
      (BalancedTensor.lTensor (M := M) f).range := by
  have hmem : b - b' ∈ f.range := by
    rw [hfg]
    show g (b - b') = 0
    rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := hmem
  have h1 : BalancedTensor.tmul R m b - BalancedTensor.tmul R m b'
      = BalancedTensor.tmul R m (b - b') := by
    rw [BalancedTensor.tmul_sub']
  rw [h1, ← ha]
  exact ⟨BalancedTensor.tmul R m a, by rw [BalancedTensor.lTensor_tmul]⟩

/-- **Right exactness of the balanced tensor product.**
If `A --f--> B --g--> C --> 0` is exact (`f.range = g.ker` and `g` surjective), then for every
right `R`-module `M` the induced sequence of abelian groups
`M ⊠[R] A --lTensor f--> M ⊠[R] B --lTensor g--> M ⊠[R] C`
is exact in the middle: `(lTensor f).range = (lTensor g).ker`.

Blueprint: this is the `Work.ORHomAlg.BalancedTensor` analogue of
`Work.ORFlatness.range_map_eq_ker_map` (file `Submission/Work/ORFlatness/range_map_eq_ker_map.lean`),
which is ALREADY PROVED for the parallel construction `Work.ORFlatness.BalTensor`; adapt that proof.
Uses `BalancedTensor.hom_ext`, `BalancedTensor.lift`/`lift_tmul`, `BalancedTensor.map_comp`,
`BalancedTensor.map_id`, `BalancedTensor.map_tmul`, `BalancedTensor.tmul_smul`,
`BalancedTensor.tmul_add`/`tmul_add'`, and `BalancedTensor.mk_zsmul` in place of the
`BalTensor.*` lemmas used there. All the `BalancedTensor` API is in
`Submission/Work/ORHomAlg/Basic.lean` and `Submission/Work/ORHomAlg/Map.lean`.
(`BalancedTensor.lTensor` is defined in `Submission/Work/ORHomAlg/Map.lean`.) -/
theorem lTensor_range_eq_ker {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    {A : Type u} [AddCommGroup A] [Module R A] {B : Type u} [AddCommGroup B] [Module R B]
    {C : Type u} [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hg : Function.Surjective g) (hfg : f.range = g.ker) :
    (Work.ORHomAlg.BalancedTensor.lTensor (M := M) f).range
      = (Work.ORHomAlg.BalancedTensor.lTensor (M := M) g).ker := by
  refine le_antisymm ?_ ?_
  · -- `(lTensor f).range ≤ (lTensor g).ker`
    rw [AddMonoidHom.range_le_ker_iff]
    rw [← BalancedTensor.lTensor_comp]
    have hgf : g.comp f = 0 := by
      ext a
      have : f a ∈ g.ker := by rw [← hfg]; exact LinearMap.mem_range_self f a
      simpa using this
    rw [hgf]
    rw [BalancedTensor.lTensor, BalancedTensor.map_zero_right]
  · -- `(lTensor g).ker ≤ (lTensor f).range`
    intro y hy
    let s : C → B := fun c => Classical.choose (hg c)
    have hs : ∀ c, g (s c) = c := fun c => Classical.choose_spec (hg c)
    let Q := BalancedTensor R M B ⧸ (BalancedTensor.lTensor (M := M) f).range
    let mkQ : BalancedTensor R M B →+ Q := QuotientAddGroup.mk' _
    have hQcongr : ∀ {b b' : B}, g b = g b' → ∀ m : M,
        mkQ (BalancedTensor.tmul R m b) = mkQ (BalancedTensor.tmul R m b') :=
      fun h m => QuotientAddGroup.eq_iff_sub_mem.mpr (sub_tmul_mem_range f g hfg h m)
    -- The balanced additive map `(m, c) ↦ mkQ (tmul m (s c))`.
    let β : M →+ C →+ Q :=
      { toFun := fun m =>
          { toFun := fun c => mkQ (BalancedTensor.tmul R m (s c))
            map_zero' := by
              show mkQ (BalancedTensor.tmul R m (s 0)) = 0
              have hgg : g (s 0) = g (0 : B) := by rw [hs, map_zero]
              rw [hQcongr hgg m, BalancedTensor.zero_tmul, map_zero]
            map_add' := fun c c' => by
              show mkQ (BalancedTensor.tmul R m (s (c + c'))) =
                mkQ (BalancedTensor.tmul R m (s c)) + mkQ (BalancedTensor.tmul R m (s c'))
              have hgg : g (s (c + c')) = g (s c + s c') := by rw [hs, map_add, hs, hs]
              rw [hQcongr hgg m, BalancedTensor.tmul_add', map_add] }
        map_zero' := by
          ext c
          show mkQ (BalancedTensor.tmul R (0 : M) (s c)) = 0
          rw [BalancedTensor.tmul_zero, map_zero]
        map_add' := fun m m' => by
          ext c
          show mkQ (BalancedTensor.tmul R (m + m') (s c)) =
            mkQ (BalancedTensor.tmul R m (s c)) + mkQ (BalancedTensor.tmul R m' (s c))
          rw [BalancedTensor.tmul_add, map_add] }
    have hbal : ∀ (m : M) (r : R) (c : C),
        β (MulOpposite.op r • m) c = β m (r • c) := by
      intro m r c
      show mkQ (BalancedTensor.tmul R (MulOpposite.op r • m) (s c))
        = mkQ (BalancedTensor.tmul R m (s (r • c)))
      have hgg : g (s (r • c)) = g (r • s c) := by rw [hs, map_smul, hs]
      rw [BalancedTensor.tmul_smul, hQcongr hgg m]
    let σ : BalancedTensor R M C →+ Q := BalancedTensor.lift β hbal
    have hσ : ∀ (m : M) (c : C), σ (BalancedTensor.tmul R m c) = mkQ (BalancedTensor.tmul R m (s c)) :=
      fun m c => BalancedTensor.lift_tmul β hbal m c
    have hσcomp : σ.comp (BalancedTensor.lTensor (M := M) g) = mkQ := by
      apply BalancedTensor.hom_ext
      intro m b
      rw [AddMonoidHom.comp_apply, BalancedTensor.lTensor_tmul, hσ]
      exact hQcongr (hs (g b)) m
    have hy0 : mkQ y = 0 := by
      have h1 : (σ.comp (BalancedTensor.lTensor (M := M) g)) y = mkQ y := by rw [hσcomp]
      rw [← h1, AddMonoidHom.comp_apply, hy, map_zero]
    exact (QuotientAddGroup.eq_zero_iff y).mp hy0

end Work.ORHomAlg.Flat
