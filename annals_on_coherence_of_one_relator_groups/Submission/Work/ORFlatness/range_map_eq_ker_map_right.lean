import Mathlib
import Submission.Work.ORFlatness.Tensor

open TensorProduct MulOpposite

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORFlatness

universe u

/-- Auxiliary congruence for the right exactness of the balanced tensor product in its
second variable: if two elements `b b'` of a left `R`-module have the same image under `g`
(so that their difference lies in `g.ker = f.range`), then the corresponding pure tensors
are congruent modulo the image of `map id f`. -/
theorem sub_mk_mem_range_right {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : f.range = g.ker)
    {X : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X] {b b' : B} (h : g b = g b') (x : X) :
    BalTensor.mk R x b - BalTensor.mk R x b' ∈
      (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f).range := by
  have hmem : b - b' ∈ f.range := by
    rw [hfg]
    show g (b - b') = 0
    rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := hmem
  have h1 : BalTensor.mk R x b - BalTensor.mk R x b' = BalTensor.mk R x (b - b') := by
    rw [sub_eq_iff_eq_add, ← BalTensor.mk_add_right, sub_add_cancel]
  rw [h1, ← ha]
  exact ⟨BalTensor.mk R x a, by rw [BalTensor.map_mk]; rfl⟩

/-- Right exactness of `Work.ORFlatness.BalTensor` (the balanced tensor product `X ⊗[R] N` of a right `R`-module `X` and a left `R`-module `N`, defined in `Submission.Work.ORFlatness.Tensor`) in its **second** variable: if `A →ₗ[R] B →ₗ[R] C → 0` is an exact sequence of **left** `R`-modules (i.e. `g` is surjective and `f.range = g.ker`), then for every **right** `R`-module `X`, the sequence
`X ⊗[R] A → X ⊗[R] B → X ⊗[R] C → 0`
is exact, i.e. `(BalTensor.map R id f).range = (BalTensor.map R id g).ker`.
This is the mirror of the already-proved `Work.ORFlatness.range_map_eq_ker_map` (right exactness in the first variable) and is proved by the same argument with the two slots interchanged. -/
theorem range_map_eq_ker_map_right {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hg : Function.Surjective g)
    (hfg : f.range = g.ker) (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] :
    (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f).range =
      (Work.ORFlatness.BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g).ker := by
  refine le_antisymm ?_ ?_
  · -- `(map id f).range ≤ (map id g).ker`
    rw [AddMonoidHom.range_le_ker_iff]
    have hcomp : (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g).comp
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f)
        = BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) (g.comp f) := by
      rw [← BalTensor.map_comp R (f' := (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X))
        (g' := g) (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f]
      rfl
    rw [hcomp]
    have hgf : g.comp f = 0 := by
      ext a
      have : f a ∈ g.ker := by rw [← hfg]; exact LinearMap.mem_range_self f a
      simpa using this
    rw [hgf]
    refine BalTensor.ext R ?_
    intro x a
    rw [BalTensor.map_mk]
    simp
  · -- `(map id g).ker ≤ (map id f).range`
    intro y hy
    let s : C → B := fun c => Classical.choose (hg c)
    have hs : ∀ c, g (s c) = c := fun c => Classical.choose_spec (hg c)
    let Q := BalTensor R X B ⧸ (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) f).range
    let mkQ : BalTensor R X B →+ Q := QuotientAddGroup.mk' _
    have hQcongr : ∀ {b b' : B}, g b = g b' → ∀ x : X,
        mkQ (BalTensor.mk R x b) = mkQ (BalTensor.mk R x b') :=
      fun h x => QuotientAddGroup.eq_iff_sub_mem.mpr (sub_mk_mem_range_right f g hfg h x)
    -- The bilinear map `(x, c) ↦ mkQ (mk x (s c))` (well defined on the quotient by the
    -- image of `map id f`, using `hfg`).
    let β : X →ₗ[ℤ] C →ₗ[ℤ] Q :=
      { toFun := fun x =>
          { toFun := fun c => mkQ (BalTensor.mk R x (s c))
            map_add' := fun c c' => by
              show mkQ (BalTensor.mk R x (s (c + c'))) =
                mkQ (BalTensor.mk R x (s c)) + mkQ (BalTensor.mk R x (s c'))
              have hgg : g (s (c + c')) = g (s c + s c') := by rw [hs, map_add, hs, hs]
              rw [hQcongr hgg x, BalTensor.mk_add_right, map_add]
            map_smul' := fun z c => by
              show mkQ (BalTensor.mk R x (s (z • c))) = z • mkQ (BalTensor.mk R x (s c))
              have hgg : g (s (z • c)) = g (z • s c) := by rw [hs, map_zsmul, hs]
              rw [hQcongr hgg x, BalTensor.mk_zsmul_right, map_zsmul] }
        map_add' := fun x x' => by
          ext c
          show mkQ (BalTensor.mk R (x + x') (s c)) =
            mkQ (BalTensor.mk R x (s c)) + mkQ (BalTensor.mk R x' (s c))
          rw [BalTensor.mk_add_left, map_add]
        map_smul' := fun z x => by
          ext c
          show mkQ (BalTensor.mk R (z • x) (s c)) = z • mkQ (BalTensor.mk R x (s c))
          rw [BalTensor.mk_zsmul_left, map_zsmul] }
    have hbal : ∀ (x : X) (c : C) (r : R), β (op r • x) c = β x (r • c) := by
      intro x c r
      show mkQ (BalTensor.mk R (op r • x) (s c)) = mkQ (BalTensor.mk R x (s (r • c)))
      have hgg : g (s (r • c)) = g (r • s c) := by rw [hs, map_smul, hs]
      rw [hQcongr hgg x, BalTensor.mk_smul_right]
    let σ : BalTensor R X C →+ Q := BalTensor.lift R β hbal
    have hσ : ∀ (x : X) (c : C), σ (BalTensor.mk R x c) = mkQ (BalTensor.mk R x (s c)) :=
      fun x c => BalTensor.lift_mk R β hbal x c
    have hσcomp : σ.comp (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g) = mkQ := by
      refine BalTensor.ext R ?_
      intro x b
      rw [AddMonoidHom.comp_apply,
        show (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g) (BalTensor.mk R x b)
          = BalTensor.mk R x (g b) from by rw [BalTensor.map_mk]; rfl, hσ]
      exact hQcongr (hs (g b)) x
    have hy0 : mkQ y = 0 := by
      have h1 : (σ.comp (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g)) y = mkQ y := by
        rw [hσcomp]
      rw [← h1, AddMonoidHom.comp_apply, hy, map_zero]
    exact (QuotientAddGroup.eq_zero_iff y).mp hy0

end Work.ORFlatness
