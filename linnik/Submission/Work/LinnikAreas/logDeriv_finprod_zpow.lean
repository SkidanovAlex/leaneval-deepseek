import Mathlib

namespace Work.LinnikAreas

open scoped BigOperators

/-- The logarithmic derivative of a finite product of integer powers of the linear factors
`(w - u)` is the corresponding weighted sum of the inverses `(z - u)⁻¹`.

Specifically, for `d : ℂ → ℤ` with finite support and `z` outside the support of `d`
(i.e. `d z = 0`), the function `w ↦ ∏ᶠ u, (w - u) ^ d u` is finite and nonzero at `z` and

  `logDeriv (fun w => ∏ᶠ u, (w - u) ^ d u) z = ∑ᶠ u, (d u : ℂ) * (z - u)⁻¹`. -/
theorem logDeriv_finprod_zpow {d : ℂ → ℤ} (hd : (Function.support d).Finite) {z : ℂ}
    (hz : d z = 0) :
    logDeriv (fun w : ℂ => ∏ᶠ u : ℂ, (w - u) ^ d u) z =
      ∑ᶠ u : ℂ, (d u : ℂ) * (z - u)⁻¹ := by
  -- `z - u ≠ 0` for every `u` in the support of `d`, since `d z = 0`.
  have hz_ne : ∀ u ∈ hd.toFinset, z - u ≠ 0 := by
    intro u hu
    have hu' : d u ≠ 0 := by
      have h1 := (hd.mem_toFinset).1 hu
      rwa [Function.mem_support] at h1
    intro h
    exact hu' (by rw [← sub_eq_zero.mp h, hz])
  -- Rewrite the finite product over all of `ℂ` as a finite product over the support of `d`.
  have hf : (fun w : ℂ => ∏ᶠ u : ℂ, (w - u) ^ d u)
      = (fun w : ℂ => ∏ u ∈ hd.toFinset, (w - u) ^ d u) := by
    funext w
    rw [finprod_eq_prod_of_mulSupport_subset]
    intro u hu
    rw [hd.coe_toFinset, Function.mem_support]
    intro h
    exact hu (by simp [h])
  -- The summand is supported on the support of `d` as well.
  have hsub : Function.support (fun u : ℂ => (d u : ℂ) * (z - u)⁻¹) ⊆ ↑hd.toFinset := by
    intro u hu
    rw [hd.coe_toFinset, Function.mem_support]
    intro h
    exact hu (by simp [h])
  calc logDeriv (fun w : ℂ => ∏ᶠ u : ℂ, (w - u) ^ d u) z
      = logDeriv (fun w : ℂ => ∏ u ∈ hd.toFinset, (w - u) ^ d u) z := by rw [hf]
    _ = ∑ u ∈ hd.toFinset, logDeriv (fun w : ℂ => (w - u) ^ d u) z :=
        by
          have h := logDeriv_prod (s := hd.toFinset) (f := fun u w => (w - u) ^ d u) (x := z)
            (fun u hu => zpow_ne_zero _ (hz_ne u hu))
            (fun u hu => (differentiableAt_id.sub_const u).zpow (Or.inl (hz_ne u hu)))
          simp only [Finset.prod_fn] at h
          exact h
    _ = ∑ u ∈ hd.toFinset, (d u : ℂ) * (z - u)⁻¹ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [logDeriv_fun_zpow (f := fun w : ℂ => w - u) (by fun_prop) (d u)]
        congr 1
        rw [logDeriv_apply]; simp [one_div]
    _ = ∑ᶠ u : ℂ, (d u : ℂ) * (z - u)⁻¹ :=
        (finsum_eq_sum_of_support_subset _ hsub).symm

end Work.LinnikAreas
