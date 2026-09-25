import Mathlib

/-!
# The `k`-th real iterated derivative of `f` along a complex line

This is the auxiliary chain-rule identity needed for the Cauchy estimates for holomorphic
functions: the `k`-th real Fréchet derivative of `f` at `z` evaluated on the constant tuple `y`,
equals the `k`-th derivative at `0` of the one-variable function `t ↦ f (z + t • y)`.
-/

namespace Work.CR.Flat.Cauchy

open ContinuousMultilinearMap

theorem iteratedFDeriv_slice {n k : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f Ω)
    {z : Fin n → ℂ} (hz : z ∈ Ω) (v : Fin n → ℂ) :
    iteratedFDeriv ℝ k (fun t : ℂ => f (z + t • v)) 0 (fun _ => 1)
      = iteratedFDeriv ℝ k f z (fun _ => v) := by
  set s : Set (Fin n → ℂ) := (fun w : Fin n → ℂ => z + w) ⁻¹' Ω with hsdef
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ) v
  have hL0 : L 0 = 0 := by simp [L]
  have hL1 : L 1 = v := by simp [L]
  have hs_open : IsOpen s := by rw [hsdef]; exact hΩ.preimage (by continuity)
  have h0s : (0 : Fin n → ℂ) ∈ s := by rw [hsdef]; simpa using hz
  have hf' : ContDiffOn ℝ (k : WithTop ℕ∞) (fun w : Fin n → ℂ => f (z + w)) s := by
    refine hf.comp ?_ ?_
    · exact (by fun_prop : ContDiffOn ℝ (k : WithTop ℕ∞) (fun w : Fin n → ℂ => z + w) s)
    · intro w hw; exact hw
  have hpre_open : IsOpen (L ⁻¹' s) := hs_open.preimage L.continuous
  have hmem0 : (0 : ℂ) ∈ L ⁻¹' s := by rw [Set.mem_preimage, hL0]; exact h0s
  have hkey := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hf' hs_open.uniqueDiffOn
    hpre_open.uniqueDiffOn (x := 0) hmem0 (i := k) (le_refl (k : WithTop ℕ∞))
  have hfun : ((fun w : Fin n → ℂ => f (z + w)) ∘ L) = (fun t : ℂ => f (z + t • v)) := by
    funext t; simp [L]
  have hLHS : iteratedFDerivWithin ℝ k ((fun w : Fin n → ℂ => f (z + w)) ∘ L) (L ⁻¹' s) 0
      = iteratedFDeriv ℝ k (fun t : ℂ => f (z + t • v)) 0 := by
    rw [hfun, iteratedFDerivWithin_of_isOpen k hpre_open hmem0]
  have hRHS : iteratedFDerivWithin ℝ k (fun w : Fin n → ℂ => f (z + w)) s (L 0)
      = iteratedFDeriv ℝ k f z := by
    rw [hL0, iteratedFDerivWithin_of_isOpen k hs_open h0s]
    simpa using iteratedFDeriv_comp_add_left (𝕜 := ℝ) k z 0 (f := f)
  have hmain : iteratedFDeriv ℝ k (fun t : ℂ => f (z + t • v)) 0
      = (iteratedFDeriv ℝ k f z).compContinuousLinearMap (fun _ => L) := by
    rw [← hLHS, hkey, hRHS]
  rw [hmain, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [hL1]

end Work.CR.Flat.Cauchy
