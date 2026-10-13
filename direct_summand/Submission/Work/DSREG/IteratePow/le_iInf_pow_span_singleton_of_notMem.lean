import Mathlib

namespace Work.DSREG.IteratePow

theorem le_iInf_pow_span_singleton_of_notMem {R : Type*} [CommRing R] {p : Ideal R} [p.IsPrime]
    {x : R} (hx : x ∉ p) (h : p ≤ Ideal.span {x}) :
    p ≤ ⨅ k : ℕ, Ideal.span {x} ^ k := by
  -- Every element of `p` is divisible by arbitrarily high powers of `x`.
  have key : ∀ k, p ≤ (Ideal.span {x}) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro a ha
      -- `a ∈ p ⊆ (x)`, so `a = x * c`.
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (h ha)
      -- Since `p` is prime and `x ∉ p`, the cofactor `c` lies in `p` as well.
      have hxc : x * c ∈ p := hc ▸ ha
      have hcp : c ∈ p := by
        rcases Ideal.IsPrime.mem_or_mem' hxc with hx' | hc'
        · exact absurd hx' hx
        · exact hc'
      -- Hence `a = x * c ∈ (x) * (x)^k = (x)^(k+1)`.
      have hmem : x * c ∈ (Ideal.span {x}) ^ (k + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul (Ideal.mem_span_singleton.mpr (dvd_refl x)) (ih hcp)
      rw [hc]; exact hmem
  exact le_iInf key

end Work.DSREG.IteratePow
