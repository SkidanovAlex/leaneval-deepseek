import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Scaling a rational kernel vector: if the rational vector `ξ` is killed by `M` and pairs
nontrivially with `u : Fin N → ℤ`, there is a complex vector `z` killed by `M` with `⟨u, z⟩ ∉ ℤ`.
(Suggested route: set `q : ℚ := ∑ m, (u m : ℚ) * ξ m` (`q ≠ 0`), `c : ℂ := Complex.I / (q : ℂ)` and
`z m := c * (ξ m : ℂ)`; then `∑ m, (M j m : ℂ) * z m = c * ((∑ m, (M j m : ℚ) * ξ m : ℚ) : ℂ) = 0`
and `∑ m, (u m : ℂ) * z m = Complex.I`, which is not an integer since its imaginary part is `1`.) -/
theorem exists_cplx_kernel_notMem_int {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (u : Fin N → ℤ)
    (ξ : Fin N → ℚ) (hA : ∀ j, ∑ m, (M j m : ℚ) * ξ m = 0)
    (hu : (∑ m, (u m : ℚ) * ξ m) ≠ 0) :
    ∃ z : Fin N → ℂ, (∀ j, ∑ m, (M j m : ℂ) * z m = 0) ∧
      ¬ ∃ n : ℤ, ∑ m, (u m : ℂ) * z m = (n : ℂ) := by
  let q : ℚ := ∑ m, (u m : ℚ) * ξ m
  let c : ℂ := Complex.I / (q : ℂ)
  let z : Fin N → ℂ := fun m => c * (ξ m : ℂ)
  have hqne : q ≠ 0 := hu
  have hcq : c * (q : ℂ) = Complex.I := by
    simp only [c]
    rw [div_mul_cancel₀]
    exact_mod_cast hqne
  have key : ∀ v : Fin N → ℚ,
      ∑ m, (v m : ℂ) * z m = c * ((∑ m, v m * ξ m : ℚ) : ℂ) := by
    intro v
    simp only [z]
    rw [show (∑ m, (v m : ℂ) * (c * (ξ m : ℂ)))
          = ∑ m, c * ((v m : ℂ) * (ξ m : ℂ)) from
        Finset.sum_congr rfl (fun m _ => by ring)]
    rw [← Finset.mul_sum]
    congr 1
    push_cast
    rfl
  refine ⟨z, ?_, ?_⟩
  · intro j
    have h1 : ∑ m, (M j m : ℂ) * z m = c * ((∑ m, (M j m : ℚ) * ξ m : ℚ) : ℂ) := by
      have hk := key (fun m => (M j m : ℚ))
      push_cast at hk ⊢
      exact hk
    rw [h1, hA j]
    simp
  · rintro ⟨n, hn⟩
    have h1 : ∑ m, (u m : ℂ) * z m = c * (q : ℂ) := by
      rw [show (q : ℂ) = ((∑ m, (u m : ℚ) * ξ m : ℚ) : ℂ) from rfl]
      have hk := key (fun m => (u m : ℚ))
      push_cast at hk ⊢
      exact hk
    have hI : ∑ m, (u m : ℂ) * z m = Complex.I := by
      rw [h1]; exact hcq
    rw [hI] at hn
    have := congrArg Complex.im hn
    simp at this

end Work.BW
