import Mathlib

/-!
# Tools for smoothing the seam

This file contains self-contained tools used in the formalisation of the dimension-one
classification of manifolds ("smoothing the seam"):

* `isLocalDiffeomorphAt_congr` — `IsLocalDiffeomorphAt` is insensitive to changing a function on a
  neighbourhood;
* `isLocalDiffeomorphAt_germ` — the explicit germ `s ↦ s / (A + B * s)` (`A ≠ 0`) which glues the
  chart at the seam to the stereographic coordinate of the circle is a local diffeomorphism at `0`,
  with explicit inverse `w ↦ A * w / (1 - B * w)`.
-/

namespace Work.OneDim

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

/-- `IsLocalDiffeomorphAt` is invariant under pointwise eventual equality. -/
theorem isLocalDiffeomorphAt_congr {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (h : f =ᶠ[𝓝 x] g) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨Φ, hx, hEq⟩ := hf
  obtain ⟨U, hU, hU'⟩ := Filter.eventually_iff_exists_mem.1 h
  obtain ⟨W, hWsub, hWopen, hxW⟩ :=
    mem_nhds_iff.1 (Filter.inter_mem hU (Φ.open_source.mem_nhds hx))
  have hWsrc : W ⊆ Φ.source := fun y hy => (hWsub hy).2
  refine ⟨{
    toPartialEquiv := {
      toFun := Φ.toFun
      invFun := Φ.invFun
      source := W
      target := Φ.toFun '' W
      map_source' := fun y hy => ⟨y, hy, rfl⟩
      map_target' := fun y hy => by
        obtain ⟨y', hy', rfl⟩ := hy
        rw [(Φ.toPartialEquiv).left_inv' (hWsrc hy')]
        exact hy'
      left_inv' := fun y hy => (Φ.toPartialEquiv).left_inv' (hWsrc hy)
      right_inv' := fun y hy => by
        obtain ⟨y', hy', rfl⟩ := hy
        rw [(Φ.toPartialEquiv).left_inv' (hWsrc hy')] }
    open_source := hWopen
    open_target := (Φ.toOpenPartialHomeomorph).isOpen_image_iff_of_subset_source hWsrc |>.2 hWopen
    contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono hWsrc
    contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono (fun y hy => by
      obtain ⟨y', hy', rfl⟩ := hy
      exact Φ.map_source (hWsrc hy')) },
    hxW, fun y hy => (hU' y (hWsub hy).1).symm.trans (hEq (hWsub hy).2)⟩

/-- The germ `s ↦ s / (A + B * s)` (`A ≠ 0`) is a local diffeomorphism at `0`, with explicit
inverse `w ↦ A * w / (1 - B * w)`. -/
theorem isLocalDiffeomorphAt_germ (A B : ℝ) (hA : A ≠ 0) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ∞
      (fun s : ℝ => s / (A + B * s)) 0 := by
  have hcont₁ : Continuous fun s : ℝ => A + B * s :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hcont₂ : Continuous fun w : ℝ => 1 - B * w :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have key1 : ∀ s : ℝ, A + B * s ≠ 0 →
      1 - B * (s / (A + B * s)) = A / (A + B * s) := by
    intro s hs
    rw [eq_div_iff hs, sub_mul, one_mul, mul_assoc, div_mul_cancel₀ s hs]; ring
  have key2 : ∀ w : ℝ, 1 - B * w ≠ 0 →
      A + B * (A * w / (1 - B * w)) = A / (1 - B * w) := by
    intro w hw
    rw [eq_div_iff hw, add_mul, mul_assoc, div_mul_cancel₀ (A * w) hw]; ring
  refine ⟨{
    toPartialEquiv := {
      toFun := fun s : ℝ => s / (A + B * s)
      invFun := fun w : ℝ => A * w / (1 - B * w)
      source := {s : ℝ | A + B * s ≠ 0}
      target := {w : ℝ | 1 - B * w ≠ 0}
      map_source' := fun s hs => by
        show 1 - B * (s / (A + B * s)) ≠ 0
        rw [key1 s (by simpa using hs)]; exact div_ne_zero hA (by simpa using hs)
      map_target' := fun w hw => by
        show A + B * (A * w / (1 - B * w)) ≠ 0
        rw [key2 w (by simpa using hw)]; exact div_ne_zero hA (by simpa using hw)
      left_inv' := fun s hs => by
        show A * (s / (A + B * s)) / (1 - B * (s / (A + B * s))) = s
        have hs0 : A + B * s ≠ 0 := by simpa using hs
        have hs' : A + s * B ≠ 0 := by rw [mul_comm B s] at hs0; exact hs0
        rw [key1 s hs0, div_div_eq_mul_div]
        field_simp
      right_inv' := fun w hw => by
        show (A * w / (1 - B * w)) / (A + B * (A * w / (1 - B * w))) = w
        have hw0 : 1 - B * w ≠ 0 := by simpa using hw
        have hw' : 1 - w * B ≠ 0 := by rw [mul_comm w B]; exact hw0
        rw [key2 w hw0, div_div_eq_mul_div]
        field_simp }
    open_source := by
      show IsOpen {s : ℝ | A + B * s ≠ 0}
      exact isOpen_ne.preimage hcont₁
    open_target := by
      show IsOpen {w : ℝ | 1 - B * w ≠ 0}
      exact isOpen_ne.preimage hcont₂
    contMDiffOn_toFun := by
      intro s hs
      exact (contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
        (by simpa using hs)).contMDiffAt.contMDiffWithinAt
    contMDiffOn_invFun := by
      intro w hw
      exact (contDiffAt_const.mul contDiffAt_id |>.div
        (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id))
        (by simpa using hw)).contMDiffAt.contMDiffWithinAt },
    by simpa using hA, fun s _ => rfl⟩

end

end Work.OneDim
