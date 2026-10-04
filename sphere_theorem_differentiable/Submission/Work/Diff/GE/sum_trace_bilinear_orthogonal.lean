import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

/-- **Trace invariance of a bilinear form under an "orthogonal" family.**

Let `β : X → X → ℝ` be a form that is additive and homogeneous in each variable for *binary*
linear combinations (`h₁`, `h₂`; this is all that is needed, symmetry of `β` is not required).
Let `A : ι → ι → ℝ` have `∑_m A m j * A m k = δ_{jk}` (the columns of `A` are orthonormal, `hA`),
and let `e₀ : ι → X`.

Then the "trace" `∑_m β (∑_j A m j • e₀ j) (∑_k A m k • e₀ k)` of `β` in the transformed family
`m ↦ ∑_j A m j • e₀ j` equals the trace `∑_j β (e₀ j) (e₀ j)` in the original family.

Proof: expand both arguments of `β` into finite sums using `h₁`/`h₂` (the auxiliary `hsum₁`/`hsum₂`
extend the two-term linearity to arbitrary finite sums by induction), giving
`∑_m ∑_j ∑_k A m j * A m k * β (e₀ j) (e₀ k)`; rewrite `A m j * A m k = A m k * A m j` and commute the
three sums so that the contraction `∑_m A m j * A m k = δ_{jk}` (`hA`) can be used, leaving
`∑_j ∑_k δ_{jk} * β (e₀ j) (e₀ k) = ∑_j β (e₀ j) (e₀ j)`. -/
theorem sum_trace_bilinear_orthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [AddCommMonoid X] [Module ℝ X]
    (β : X → X → ℝ)
    (h₁ : ∀ (r s : ℝ) (u₁ u₂ w : X), β (r • u₁ + s • u₂) w = r * β u₁ w + s * β u₂ w)
    (h₂ : ∀ (r s : ℝ) (u v₁ v₂ : X), β u (r • v₁ + s • v₂) = r * β u v₁ + s * β u v₂)
    (A : ι → ι → ℝ) (e₀ : ι → X)
    (hA : ∀ j k, ∑ m, A m j * A m k = if j = k then 1 else 0) :
    ∑ m, β (∑ j, A m j • e₀ j) (∑ k, A m k • e₀ k) = ∑ j, β (e₀ j) (e₀ j) := by
  classical
  -- `β` vanishes when one argument is `0`.
  have hβ0 : ∀ w : X, β 0 w = 0 := by
    intro w
    simpa using h₁ 0 0 (0 : X) (0 : X) w
  have h0β : ∀ u : X, β u 0 = 0 := by
    intro u
    simpa using h₂ 0 0 u (0 : X) (0 : X)
  -- Linearity of `β` in each variable, extended to finite sums.
  have hsum₁ : ∀ (s : Finset ι) (c : ι → ℝ) (v : ι → X) (w : X),
      β (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * β (v i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c v w; simp [hβ0]
    | insert k s hk ih =>
        intro c v w
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        have h := h₁ (c k) 1 (v k) (∑ i ∈ s, c i • v i) w
        simp only [one_smul, one_mul] at h
        rw [h, ih c v w]
  have hsum₂ : ∀ (s : Finset ι) (c : ι → ℝ) (v : ι → X) (w : X),
      β w (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * β w (v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c v w; simp [h0β]
    | insert k s hk ih =>
        intro c v w
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        have h := h₂ (c k) 1 w (v k) (∑ i ∈ s, c i • v i)
        simp only [one_smul, one_mul] at h
        rw [h, ih c v w]
  calc ∑ m, β (∑ j, A m j • e₀ j) (∑ k, A m k • e₀ k)
      = ∑ m, ∑ j, A m j * β (e₀ j) (∑ k, A m k • e₀ k) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        exact hsum₁ Finset.univ (fun j => A m j) e₀ (∑ k, A m k • e₀ k)
    _ = ∑ m, ∑ j, A m j * (∑ k, A m k * β (e₀ j) (e₀ k)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hsum₂ Finset.univ (fun k => A m k) e₀ (e₀ j)]
    _ = ∑ m, ∑ j, ∑ k, A m j * A m k * β (e₀ j) (e₀ k) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring
    _ = ∑ j, ∑ k, (∑ m, A m j * A m k) * β (e₀ j) (e₀ k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ j, ∑ k, (if j = k then 1 else 0) * β (e₀ j) (e₀ k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hA j k]
    _ = ∑ j, β (e₀ j) (e₀ j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          simp [show ¬ (j = k) from fun h => hk h.symm]
        · intro hj
          exact absurd (Finset.mem_univ j) hj

end Work.Diff.GE
