import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter

namespace Work.Diff.EXT

/-- Pointwise (i.e. `ContDiffAt`) version of Mathlib's `norm_iteratedFDeriv_comp_le`: if `f` is
smooth at `x` and `g` is smooth at `f x`, and the iterated derivatives of `g` at `f x` up to order
`k` are bounded by `C` while those of `f` at `x` (of order `≥ 1`) are bounded by `D ^ i`, then the
`k`-th iterated derivative of `g ∘ f` at `x` is bounded by `k! * C * D ^ k`.

The proof reduces to the local (`ContDiffOn`) form of Mathlib's lemma on an open neighbourhood of
`x` mapped into an open neighbourhood of `f x`, where `iteratedFDerivWithin` agrees with
`iteratedFDeriv` because the sets are open. -/
lemma norm_iteratedFDeriv_comp_le_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : E → X} {g : X → ℝ} {x : E} {k : ℕ} {C D : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (f x))
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ (Nat.factorial k : ℝ) * C * D ^ k := by
  obtain ⟨u₁, hu₁, hgu₁⟩ := hg.contDiffOn (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_top)
    (fun h => absurd h (by simp))
  obtain ⟨u₂, hu₂, hfu₂⟩ := hf.contDiffOn (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_top)
    (fun h => absurd h (by simp))
  obtain ⟨t, htsub, htopen, hft⟩ := mem_nhds_iff.mp hu₁
  have hg_on : ContDiffOn ℝ (k : WithTop ℕ∞) g t := hgu₁.mono htsub
  have hpre : f ⁻¹' t ∈ nhds x := hf.continuousAt.preimage_mem_nhds (htopen.mem_nhds hft)
  obtain ⟨u, huV, huopen, hxu⟩ := mem_nhds_iff.mp (inter_mem hu₂ hpre)
  have hf_on : ContDiffOn ℝ (k : WithTop ℕ∞) f u :=
    hfu₂.mono (fun y hy => (huV hy).1)
  have hmu : Set.MapsTo f u t := fun y hy => (huV hy).2
  have hC' : ∀ i, i ≤ k → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i htopen hft]
    exact hC i hi
  have hD' : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDerivWithin ℝ i f u x‖ ≤ D ^ i := by
    intro i hi1 hik
    rw [iteratedFDerivWithin_of_isOpen i huopen hxu]
    exact hD i hi1 hik
  have hmain := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := k) (N := (k : WithTop ℕ∞))
    hg_on hf_on le_rfl (htopen.uniqueDiffOn) (huopen.uniqueDiffOn) hmu hxu hC' hD'
  rw [iteratedFDerivWithin_of_isOpen k huopen hxu] at hmain
  simpa using hmain

end Work.Diff.EXT
