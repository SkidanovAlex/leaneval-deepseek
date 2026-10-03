import Mathlib
import Submission.Work.ORHomAlg.Map

universe u v w w' w''

namespace Work.ORHomAlg.Tor

open Work.ORHomAlg

section Helpers

/-- A pure tensor `m ⊠ b` whose second factor dies under `g` lies in the range of `lTensor f`,
whenever `N →f N' →g N''` is exact. -/
theorem tmul_mem_range_of_exact {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N']
    [Module R N'] {N'' : Type*} [AddCommGroup N''] [Module R N'']
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (h : Function.Exact f g) {b : N'} (hb : g b = 0)
    (m : M) : BalancedTensor.tmul R m b ∈ (BalancedTensor.lTensor (M := M) f).range := by
  obtain ⟨a, ha⟩ := (h b).mp hb
  rw [← ha, ← BalancedTensor.lTensor_tmul (g := f) (m := m) (n := a)]
  exact ⟨BalancedTensor.tmul R m a, rfl⟩

/-- If `g b = g b'` then `m ⊠ b - m ⊠ b'` lies in the range of `lTensor f`, whenever
`N →f N' →g N''` is exact. -/
theorem tmul_sub_mem_range {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N']
    [Module R N'] {N'' : Type*} [AddCommGroup N''] [Module R N'']
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (h : Function.Exact f g) {b b' : N'}
    (hbb : g b = g b') (m : M) :
    BalancedTensor.tmul R m b - BalancedTensor.tmul R m b'
      ∈ (BalancedTensor.lTensor (M := M) f).range := by
  rw [← BalancedTensor.tmul_sub' (m := m) (n₁ := b) (n₂ := b')]
  exact tmul_mem_range_of_exact f g h (by rw [map_sub, hbb, sub_self]) m

/-- `lTensor` of the zero map is the zero map. -/
theorem lTensor_zero_apply {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*}
    [AddCommGroup N'] [Module R N'] (x : BalancedTensor R M N) :
    BalancedTensor.lTensor (M := M) (0 : N →ₗ[R] N') x = 0 := by
  induction x using BalancedTensor.induction_on with
  | H0 => simp
  | Hadd a b ha hb => rw [map_add, ha, hb, add_zero]
  | Htmul m n => simp

end Helpers

/-- Right exactness of the balanced tensor product `M ⊠[R] -`: if `N →f N' →g N'' → 0` is
exact (i.e. `g` is surjective and `range f = ker g`), then
`M ⊠[R] N → M ⊠[R] N' → M ⊠[R] N'' → 0` is exact. -/
theorem lTensor_exact_of_surjective {R : Type u} [Ring R] {M : Type v} [AddCommGroup M]
    [Module Rᵐᵒᵖ M] {N : Type w} [AddCommGroup N] [Module R N] {N' : Type w'}
    [AddCommGroup N'] [Module R N'] {N'' : Type w''} [AddCommGroup N''] [Module R N'']
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (hg : Function.Surjective g) (h : Function.Exact f g) :
    Function.Exact (Work.ORHomAlg.BalancedTensor.lTensor (M := M) f)
      (Work.ORHomAlg.BalancedTensor.lTensor (M := M) g) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : N'' → N', ∀ c, g (s c) = c := ⟨fun c => Classical.choose (hg c),
    fun c => Classical.choose_spec (hg c)⟩
  intro y
  constructor
  · -- `ker (lTensor g) ≤ range (lTensor f)`
    intro hy
    let Q := BalancedTensor R M N' ⧸ (BalancedTensor.lTensor (M := M) f).range
    let mkQ : BalancedTensor R M N' →+ Q := QuotientAddGroup.mk' _
    have hQcongr : ∀ {b b' : N'}, g b = g b' → ∀ m : M,
        mkQ (BalancedTensor.tmul R m b) = mkQ (BalancedTensor.tmul R m b') :=
      fun hbb m => QuotientAddGroup.eq_iff_sub_mem.mpr (tmul_sub_mem_range f g h hbb m)
    -- the balanced pairing `(m, c) ↦ mkQ (m ⊠ s c)`
    let β : M →+ N'' →+ Q :=
      { toFun := fun m =>
          { toFun := fun c => mkQ (BalancedTensor.tmul R m (s c))
            map_zero' := (QuotientAddGroup.eq_zero_iff _).mpr
              (tmul_mem_range_of_exact f g h (hs 0) m)
            map_add' := fun c c' => by
              have hgg : g (s (c + c')) = g (s c + s c') := by rw [hs, map_add, hs, hs]
              rw [hQcongr hgg m, BalancedTensor.tmul_add', map_add] }
        map_zero' := AddMonoidHom.ext (fun c => by simp)
        map_add' := fun m m' => AddMonoidHom.ext (fun c => by
          show mkQ (BalancedTensor.tmul R (m + m') (s c))
            = mkQ (BalancedTensor.tmul R m (s c)) + mkQ (BalancedTensor.tmul R m' (s c))
          rw [BalancedTensor.tmul_add, map_add]) }
    have hbal : ∀ (m : M) (r : R) (c : N''),
        (β (MulOpposite.op r • m)) c = (β m) (r • c) := by
      intro m r c
      show mkQ (BalancedTensor.tmul R (MulOpposite.op r • m) (s c))
        = mkQ (BalancedTensor.tmul R m (s (r • c)))
      rw [BalancedTensor.tmul_smul]
      have hgg : g (s (r • c)) = g (r • s c) := by rw [hs, map_smul, hs]
      rw [← hQcongr hgg m]
    let σ : BalancedTensor R M N'' →+ Q := (BalancedTensor.lift β hbal).toAddMonoidHom
    have hσ : ∀ (m : M) (c : N''), σ (BalancedTensor.tmul R m c)
        = mkQ (BalancedTensor.tmul R m (s c)) :=
      fun m c => BalancedTensor.lift_tmul β hbal m c
    have hσcomp : σ.comp (BalancedTensor.lTensor (M := M) g) = mkQ := by
      refine BalancedTensor.hom_ext (fun m b => ?_)
      rw [AddMonoidHom.comp_apply, BalancedTensor.lTensor_tmul, hσ]
      exact hQcongr (hs (g b)) m
    have hy0 : mkQ y = 0 := by
      have h1 : (σ.comp (BalancedTensor.lTensor (M := M) g)) y = mkQ y := by rw [hσcomp]
      rw [← h1, AddMonoidHom.comp_apply, hy, map_zero]
    exact (QuotientAddGroup.eq_zero_iff y).mp hy0
  · -- `range (lTensor f) ≤ ker (lTensor g)`
    intro hy
    obtain ⟨x, rfl⟩ := hy
    have h2 : ∀ a : N, g (f a) = 0 := fun a => (h (f a)).mpr ⟨a, rfl⟩
    have hzero : (BalancedTensor.lTensor (M := M) g).comp
        (BalancedTensor.lTensor (M := M) f) = 0 := by
      refine BalancedTensor.hom_ext (fun m n => ?_)
      rw [AddMonoidHom.comp_apply, BalancedTensor.lTensor_tmul, BalancedTensor.lTensor_tmul,
        h2 n, BalancedTensor.zero_tmul]
      rfl
    rw [← AddMonoidHom.comp_apply, hzero]
    rfl

end Work.ORHomAlg.Tor
