import Mathlib

namespace Work.DSM2p

/-- In a valuation ring `V ⊆ K`, for a nonzero nonunit `u` the intersection of the
descending chain of principal ideals `(u) ⊇ (u²) ⊇ ⋯` is a prime ideal which does not
contain `u`.

The ideal is the "limit" ideal `{x | x ∈ (uⁿ) for all n}`; it is prime because in a
valuation ring any two elements are comparable under divisibility: if `x ∉ I` then
`x ∤ uᵐ` for some `m`, hence `x ∣ uᵐ` (comparability), and any `x * y ∈ I` together
with `x ∣ uᵐ` forces `y ∈ I`. -/
theorem valex_iInf_span_pow {K : Type*} [Field K] (V : ValuationSubring K) (u : V)
    (hu0 : u ≠ 0) (hu : ¬ IsUnit u) :
    (⨅ n : ℕ, Ideal.span {u ^ n}).IsPrime ∧ u ∉ (⨅ n : ℕ, Ideal.span {u ^ n}) := by
  set I : Ideal V := ⨅ n : ℕ, Ideal.span {u ^ n} with hI
  -- membership in the intersection, characterized by divisibility by all powers of `u`
  have hmem : ∀ x : V, x ∈ I ↔ ∀ n : ℕ, u ^ n ∣ x := by
    intro x
    rw [hI, Ideal.mem_iInf]
    simp only [Ideal.mem_span_singleton]
  -- `u` itself is not in the intersection, else `u² ∣ u` would make `u` a unit
  have hnotmem : u ∉ I := by
    intro h
    have h2 : u ^ 2 ∣ u := (hmem u).mp h 2
    obtain ⟨c, hc⟩ : ∃ c, u = u ^ 2 * c := h2
    have huc : u * c = 1 := by
      have hh : u * (u * c) = u := by
        rw [← mul_assoc, ← pow_two]
        exact hc.symm
      have : u * (u * c) = u * 1 := by rw [mul_one]; exact hh
      exact mul_left_cancel₀ hu0 this
    exact hu (isUnit_iff_exists.mpr ⟨c, huc, by rw [mul_comm]; exact huc⟩)
  refine ⟨?_, hnotmem⟩
  refine ⟨?_, ?_⟩
  · intro htop
    exact hnotmem (by rw [htop]; exact Submodule.mem_top)
  · -- primality: if `x * y ∈ I` then `x ∈ I` or `y ∈ I`
    intro x y hxy
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hx, hy⟩ := hcon
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ I.zero_mem)
    -- since `x ∉ I` there is `m` with `uᵐ ∤ x`, hence (comparability) `x ∣ uᵐ`
    have hxm : ∃ m : ℕ, ¬ u ^ m ∣ x := by
      by_contra hc
      exact hx ((hmem x).mpr fun m => not_not.mp (not_exists.mp hc m))
    obtain ⟨m, hm⟩ := hxm
    have hxdvd : x ∣ u ^ m := (ValuationRing.dvd_total x (u ^ m)).resolve_right hm
    obtain ⟨c, hc⟩ : ∃ c, u ^ m = x * c := hxdvd
    -- then `x * y ∈ I` forces `y ∈ I`, a contradiction
    have hym : ∀ n : ℕ, u ^ n ∣ y := by
      intro n
      obtain ⟨d, hd⟩ : ∃ d, x * y = u ^ (m + n) * d := (hmem (x * y)).mp hxy (m + n)
      refine ⟨c * d, ?_⟩
      have key : x * y = x * (u ^ n * (c * d)) := by
        calc x * y = u ^ (m + n) * d := hd
          _ = (u ^ m * u ^ n) * d := by rw [pow_add]
          _ = (x * c * u ^ n) * d := by rw [hc]
          _ = x * (u ^ n * (c * d)) := by ring
      exact mul_left_cancel₀ hx0 key
    exact hy ((hmem y).mpr hym)

end Work.DSM2p
