import Mathlib
import Submission.Work.ORFlatness.Tensor

open TensorProduct MulOpposite

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORFlatness

universe u

/-- Auxiliary congruence for the right exactness of the balanced tensor product: if two
elements `b b'` of a right `R`-module have the same image under `g` (so that their
difference lies in `g.ker = f.range`), then the corresponding pure tensors are congruent
modulo the image of `map f id`. -/
theorem sub_mk_mem_range {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B]
    [AddCommGroup C] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (hfg : f.range = g.ker)
    {N : Type u} [AddCommGroup N] [Module R N] {b b' : B} (h : g b = g b') (n : N) :
    BalTensor.mk R b n - BalTensor.mk R b' n ∈
      (BalTensor.map R f (LinearMap.id : N →ₗ[R] N)).range := by
  have hmem : b - b' ∈ f.range := by
    rw [hfg]
    show g (b - b') = 0
    rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := hmem
  have h1 : BalTensor.mk R b n - BalTensor.mk R b' n = BalTensor.mk R (b - b') n := by
    rw [sub_eq_iff_eq_add, ← BalTensor.mk_add_left, sub_add_cancel]
  rw [h1, ← ha]
  exact ⟨BalTensor.mk R a n, by rw [BalTensor.map_mk]; rfl⟩

/-- Right exactness of the balanced tensor product `Work.ORFlatness.BalTensor` (the
tensor product of a right `R`-module and a left `R`-module over an arbitrary ring `R`,
defined in `Submission.Work.ORFlatness.Tensor`): if `A → B → C → 0` is an exact sequence
of right `R`-modules, then for every left `R`-module `N` the induced sequence
`A ⊗[R] N → B ⊗[R] N → C ⊗[R] N → 0` is exact. Here `BalTensor.map` takes the tensor of
the two given linear maps and `LinearMap.id` is the identity of `N`.

Proof sketch: `(map g id) ∘ (map f id) = map (g.comp f) id = 0` by
`Work.ORFlatness.BalTensor.map_comp` (using `BalTensor.map_mk`), whence
`(map f id).range ≤ (map g id).ker`. For the reverse inclusion take a set-theoretic
section `s : C → B` of `g` (`fun c => Classical.choose (hg c)`) and build, using
`Work.ORFlatness.BalTensor.lift` and `Work.ORFlatness.BalTensor.ext`, an additive map
`σ : Work.ORFlatness.BalTensor R C N →+ Work.ORFlatness.BalTensor R B N ⧸ (map f id).range`
sending `BalTensor.mk c n` to the class of `BalTensor.mk (s c) n`; the well-definedness
conditions use `hfg`, `BalTensor.mk_smul_right` and `BalTensor.mk_add_left/mk_add_right`.
Then `σ ((map g id) y) = mkQ y` for all `y` (check on generators `mk b n` using
`b - s (g b) ∈ range f`), so `y ∈ (map g id).ker` implies the class of `y` equals
`σ 0 = 0`, i.e. `y ∈ (map f id).range`. -/
theorem range_map_eq_ker_map {R : Type u} [Ring R] {A B C : Type u}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B]
    [AddCommGroup C] [Module Rᵐᵒᵖ C]
    (f : A →ₗ[Rᵐᵒᵖ] B) (g : B →ₗ[Rᵐᵒᵖ] C) (hg : Function.Surjective g)
    (hfg : f.range = g.ker) (N : Type u) [AddCommGroup N] [Module R N] :
    (Work.ORFlatness.BalTensor.map R f (LinearMap.id : N →ₗ[R] N)).range
      = (Work.ORFlatness.BalTensor.map R g (LinearMap.id : N →ₗ[R] N)).ker := by
  refine le_antisymm ?_ ?_
  · -- `(map f id).range ≤ (map g id).ker`
    rw [AddMonoidHom.range_le_ker_iff]
    have hcomp : (BalTensor.map R g (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R f (LinearMap.id : N →ₗ[R] N))
        = BalTensor.map R (g.comp f) (LinearMap.id : N →ₗ[R] N) := by
      rw [← BalTensor.map_comp R (f' := g) (g' := LinearMap.id) f (LinearMap.id : N →ₗ[R] N)]
      rfl
    rw [hcomp]
    have hgf : g.comp f = 0 := by
      ext a
      have : f a ∈ g.ker := by rw [← hfg]; exact LinearMap.mem_range_self f a
      simpa using this
    rw [hgf]
    refine BalTensor.ext R ?_
    intro x n
    rw [BalTensor.map_mk]
    simp
  · -- `(map g id).ker ≤ (map f id).range`
    intro y hy
    let s : C → B := fun c => Classical.choose (hg c)
    have hs : ∀ c, g (s c) = c := fun c => Classical.choose_spec (hg c)
    let Q := BalTensor R B N ⧸ (BalTensor.map R f (LinearMap.id : N →ₗ[R] N)).range
    let mkQ : BalTensor R B N →+ Q := QuotientAddGroup.mk' _
    have hQcongr : ∀ {b b' : B}, g b = g b' → ∀ n : N,
        mkQ (BalTensor.mk R b n) = mkQ (BalTensor.mk R b' n) :=
      fun h n => QuotientAddGroup.eq_iff_sub_mem.mpr (sub_mk_mem_range f g hfg h n)
    -- The bilinear map `(c, n) ↦ mkQ (mk (s c) n)` (well defined on the quotient by
    -- the image of `map f id`, using `hfg`).
    let β : C →ₗ[ℤ] N →ₗ[ℤ] Q :=
      { toFun := fun c =>
          { toFun := fun n => mkQ (BalTensor.mk R (s c) n)
            map_add' := fun n n' => by rw [BalTensor.mk_add_right, map_add]
            map_smul' := fun z n => by rw [BalTensor.mk_zsmul_right, map_zsmul]; simp }
        map_add' := fun c c' => by
          ext n
          show mkQ (BalTensor.mk R (s (c + c')) n) = mkQ (BalTensor.mk R (s c) n) + mkQ (BalTensor.mk R (s c') n)
          have hgg : g (s (c + c')) = g (s c + s c') := by rw [hs, map_add, hs, hs]
          rw [hQcongr hgg n, BalTensor.mk_add_left, map_add]
        map_smul' := fun z c => by
          ext n
          show mkQ (BalTensor.mk R (s (z • c)) n) = z • mkQ (BalTensor.mk R (s c) n)
          have hgg : g (s (z • c)) = g (z • s c) := by rw [hs, map_zsmul, hs]
          rw [hQcongr hgg n, BalTensor.mk_zsmul_left, map_zsmul] }
    have hbal : ∀ (c : C) (n : N) (r : R), β (op r • c) n = β c (r • n) := by
      intro c n r
      show mkQ (BalTensor.mk R (s (op r • c)) n) = mkQ (BalTensor.mk R (s c) (r • n))
      have hgg : g (s (op r • c)) = g (op r • s c) := by rw [hs, map_smul, hs]
      rw [hQcongr hgg n, BalTensor.mk_smul_right]
    let σ : BalTensor R C N →+ Q := BalTensor.lift R β hbal
    have hσ : ∀ (c : C) (n : N), σ (BalTensor.mk R c n) = mkQ (BalTensor.mk R (s c) n) :=
      fun c n => BalTensor.lift_mk R β hbal c n
    have hσcomp : σ.comp (BalTensor.map R g (LinearMap.id : N →ₗ[R] N)) = mkQ := by
      refine BalTensor.ext R ?_
      intro b n
      rw [AddMonoidHom.comp_apply, show (BalTensor.map R g (LinearMap.id : N →ₗ[R] N)) (BalTensor.mk R b n)
          = BalTensor.mk R (g b) n from by rw [BalTensor.map_mk]; rfl, hσ]
      exact hQcongr (hs (g b)) n
    have hy0 : mkQ y = 0 := by
      have h1 : (σ.comp (BalTensor.map R g (LinearMap.id : N →ₗ[R] N))) y = mkQ y := by rw [hσcomp]
      rw [← h1, AddMonoidHom.comp_apply, hy, map_zero]
    exact (QuotientAddGroup.eq_zero_iff y).mp hy0

end Work.ORFlatness
