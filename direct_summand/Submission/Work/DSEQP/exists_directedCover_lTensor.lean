import Mathlib

namespace Work.DSEQP

theorem exists_directedCover_lTensor {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    [IsDirectedOrder ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {M : Type*} [AddCommGroup M] [Module R M]
    (g : ∀ i, G i →ₗ[R] M) (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
    (hcompat : ∀ i j (h : i ≤ j) (x : G i), g j (f i j h x) = g i x)
    (hcover : ∀ m : M, ∃ i x, g i x = m)
    (I : Ideal R) (z : TensorProduct R I M) :
    ∃ (j : ι) (y : TensorProduct R I (G j)), LinearMap.lTensor I (g j) y = z := by
  classical
  -- Compatibility of the transition maps with the covering maps, after tensoring by `I`.
  have key : ∀ (i j : ι) (h : i ≤ j) (y : TensorProduct R I (G i)),
      LinearMap.lTensor I (g j) (LinearMap.lTensor I (f i j h) y)
        = LinearMap.lTensor I (g i) y := by
    intro i j h y
    rw [← LinearMap.lTensor_comp_apply,
      show (g j) ∘ₗ (f i j h) = g i from LinearMap.ext (fun x => hcompat i j h x)]
  -- Reduce to simple tensors and their sums.
  refine TensorProduct.inductionOn z (fun a m => ?_) (fun z₁ z₂ ih₁ ih₂ => ?_)
  · -- simple tensor `a ⊗ₜ m`: cover `m` by some `g i x`.
    obtain ⟨i, x, hx⟩ := hcover m
    exact ⟨i, a ⊗ₜ[R] x, by rw [LinearMap.lTensor_tmul, hx]⟩
  · -- a sum: transport both summands to a common index using directedness.
    obtain ⟨j₁, y₁, hy₁⟩ := ih₁
    obtain ⟨j₂, y₂, hy₂⟩ := ih₂
    obtain ⟨j, hj₁, hj₂⟩ := exists_ge_ge j₁ j₂
    exact ⟨j, LinearMap.lTensor I (f j₁ j hj₁) y₁ + LinearMap.lTensor I (f j₂ j hj₂) y₂,
      by rw [map_add, key j₁ j hj₁ y₁, key j₂ j hj₂ y₂, hy₁, hy₂]⟩

end Work.DSEQP
