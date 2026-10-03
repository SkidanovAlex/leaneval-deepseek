/-
# `Submission.Work.FIArea5.S16Hecke.gabC_ofReal_alt`

The complex sequence `GabC a b` (the four-fold Cauchy product of the geometric sequences of
`1, a, b, ab`, see `conv_defs`) is, for **real** `a, b`, the complexification of the real
sequence `Gab a b` (`hecke_prod_local`):

  `Gab a b k = Σ_{m ≤ k/2} (ab)^m S a (k-2m) S b (k-2m)`
  `         = Σ_{n2+n3+n4 ≤ k} a^(n2+n4) b^(n3+n4)`   (`Gab_cauchy`).

Indeed both are the coefficient sequence of `1/((1-T)(1-aT)(1-bT)(1-abT))`:
`GabC_unfold` writes `GabC a b k` as a nested sum over `n3 ≤ n2 ≤ n1 ≤ k` with summand
`x^(n2-n3) y^(n1-n2) (xy)^(k-n1)`; `GabC_flat` reindexes it, by the bijection
`(n1,n2,n3) ↦ (n2-n3, n1-n2, k-n1)` between `{n3 ≤ n2 ≤ n1 ≤ k}` and
`{n2+n3+n4 ≤ k}`, into the `Gab` simplex sum.  This transports `Gab_nonneg` to `GabC`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.conv_defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke
open Finset
open scoped BigOperators

noncomputable section

/-- Extending a partial range sum to a full one, with an indicator. -/
lemma sum_range_extend (f : ℕ → ℂ) {m k : ℕ} (hm : m ≤ k) :
    (∑ i ∈ Finset.range (m+1), f i)
      = ∑ i ∈ Finset.range (k+1), (if i ≤ m then f i else 0) := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma GabC_unfold (x y : ℂ) (k : ℕ) :
    GabC x y k = ∑ n1 ∈ Finset.range (k+1), ∑ n2 ∈ Finset.range (n1+1),
      ∑ n3 ∈ Finset.range (n2+1), x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1) := by
  have h : GabC x y k
      = ∑ n1 ∈ Finset.range (k+1), (∑ n2 ∈ Finset.range (n1+1),
          ∑ n3 ∈ Finset.range (n2+1), x^(n2-n3) * y^(n1-n2)) * (x*y)^(k-n1) := by
    simp only [GabC, cvs, gc, one_pow, one_mul]
    refine Finset.sum_congr rfl fun n1 _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun n2 _ => ?_
    simp only [Finset.sum_mul]
  rw [h]
  refine Finset.sum_congr rfl fun n1 _ => ?_
  simp only [Finset.sum_mul]

lemma GabC_flat (x y : ℂ) (k : ℕ) :
    GabC x y k = ∑ n2 ∈ Finset.range (k+1), ∑ n3 ∈ Finset.range (k+1),
      ∑ n4 ∈ Finset.range (k+1),
      (if n2 + n3 + n4 ≤ k then x^(n2+n4) * y^(n3+n4) else 0) := by
  set P : Finset (ℕ × ℕ × ℕ) :=
    (Finset.range (k+1) ×ˢ Finset.range (k+1) ×ˢ Finset.range (k+1)).filter
      (fun p => p.2.1 ≤ p.1 ∧ p.2.2 ≤ p.2.1) with hP
  set Q : Finset (ℕ × ℕ × ℕ) :=
    (Finset.range (k+1) ×ˢ Finset.range (k+1) ×ˢ Finset.range (k+1)).filter
      (fun q => q.1 + q.2.1 + q.2.2 ≤ k) with hQ
  have e1 : (∑ n1 ∈ Finset.range (k+1), ∑ n2 ∈ Finset.range (n1+1),
        ∑ n3 ∈ Finset.range (n2+1), x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1))
      = ∑ p ∈ P, x^(p.2.1 - p.2.2) * y^(p.1 - p.2.1) * (x*y)^(k - p.1) := by
    have hA : (∑ n1 ∈ Finset.range (k+1), ∑ n2 ∈ Finset.range (n1+1),
          ∑ n3 ∈ Finset.range (n2+1), x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1))
        = ∑ n1 ∈ Finset.range (k+1), ∑ n2 ∈ Finset.range (n1+1),
          ∑ n3 ∈ Finset.range (k+1),
            (if n3 ≤ n2 then x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1) else 0) := by
      refine Finset.sum_congr rfl fun n1 h1 => ?_
      refine Finset.sum_congr rfl fun n2 h2 => ?_
      simp only [Finset.mem_range] at h1 h2
      exact sum_range_extend (k := k) (m := n2)
        (f := fun n3 => x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1)) (by omega)
    have hB : (∑ n1 ∈ Finset.range (k+1), ∑ n2 ∈ Finset.range (n1+1),
          ∑ n3 ∈ Finset.range (k+1),
            (if n3 ≤ n2 then x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1) else 0))
        = ∑ n1 ∈ Finset.range (k+1), ∑ n2 ∈ Finset.range (k+1),
            (if n2 ≤ n1 then (∑ n3 ∈ Finset.range (k+1),
              (if n3 ≤ n2 then x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1) else 0)) else 0) := by
      refine Finset.sum_congr rfl fun n1 h1 => ?_
      simp only [Finset.mem_range] at h1
      exact sum_range_extend (k := k) (m := n1)
        (f := fun n2 => ∑ n3 ∈ Finset.range (k+1),
          (if n3 ≤ n2 then x^(n2-n3) * y^(n1-n2) * (x*y)^(k-n1) else 0)) (by omega)
    simp only [hA, hB]
    simp only [hP, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun n1 _ => ?_
    refine Finset.sum_congr rfl fun n2 _ => ?_
    by_cases hb : n2 ≤ n1
    · rw [if_pos hb]
      refine Finset.sum_congr rfl fun n3 _ => ?_
      by_cases hc : n3 ≤ n2
      · rw [if_pos hc, if_pos ⟨hb, hc⟩]
      · rw [if_neg hc, if_neg (fun h : n2 ≤ n1 ∧ n3 ≤ n2 => hc h.2)]
    · rw [if_neg hb,
        Finset.sum_eq_zero (fun n3 _ => if_neg (fun h : n2 ≤ n1 ∧ n3 ≤ n2 => hb h.1))]
  have e2 : (∑ p ∈ P, x^(p.2.1 - p.2.2) * y^(p.1 - p.2.1) * (x*y)^(k - p.1))
      = ∑ q ∈ Q, x^(q.1 + q.2.2) * y^(q.2.1 + q.2.2) := by
    refine Finset.sum_bij' (fun p _ => (p.2.1 - p.2.2, p.1 - p.2.1, k - p.1))
      (fun q _ => (k - q.2.2, k - q.2.1 - q.2.2, k - q.1 - q.2.1 - q.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hP, hQ, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hp
      exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    · intro q hq
      simp only [hP, hQ, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hq
      exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hp
      have e1' : k - (k - p.1) = p.1 := by omega
      have e2' : k - (p.1 - p.2.1) - (k - p.1) = p.2.1 := by omega
      have e3' : k - (p.2.1 - p.2.2) - (p.1 - p.2.1) - (k - p.1) = p.2.2 := by omega
      simp only [e1', e2', e3']
    · intro q hq
      simp only [hQ, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hq
      have e1' : (k - q.2.1 - q.2.2) - (k - q.1 - q.2.1 - q.2.2) = q.1 := by omega
      have e2' : (k - q.2.2) - (k - q.2.1 - q.2.2) = q.2.1 := by omega
      have e3' : k - (k - q.2.2) = q.2.2 := by omega
      simp only [e1', e2', e3']
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hp
      calc x ^ (p.2.1 - p.2.2) * y ^ (p.1 - p.2.1) * (x * y) ^ (k - p.1)
          = (x ^ (p.2.1 - p.2.2) * x ^ (k - p.1)) * (y ^ (p.1 - p.2.1) * y ^ (k - p.1)) := by
            rw [mul_pow]; ring
        _ = x ^ ((p.2.1 - p.2.2) + (k - p.1)) * y ^ ((p.1 - p.2.1) + (k - p.1)) := by
            rw [← pow_add, ← pow_add]
  have e3 : (∑ q ∈ Q, x^(q.1 + q.2.2) * y^(q.2.1 + q.2.2))
      = ∑ n2 ∈ Finset.range (k+1), ∑ n3 ∈ Finset.range (k+1),
        ∑ n4 ∈ Finset.range (k+1),
        (if n2 + n3 + n4 ≤ k then x^(n2+n4) * y^(n3+n4) else 0) := by
    simp only [hQ, Finset.sum_filter, Finset.sum_product]
  rw [GabC_unfold, e1, e2, e3]

theorem gabC_ofReal_alt (a b : ℝ) (k : ℕ) :
    GabC ((a : ℂ)) ((b : ℂ)) k = ((Gab a b k : ℝ) : ℂ) := by
  have h1 : GabC ((a : ℂ)) ((b : ℂ)) k
      = ∑ n2 ∈ Finset.range (k+1), ∑ n3 ∈ Finset.range (k+1),
        ∑ n4 ∈ Finset.range (k+1),
        (if n2 + n3 + n4 ≤ k then ((a^(n2+n4) * b^(n3+n4) : ℝ) : ℂ) else 0) := by
    rw [GabC_flat]
    refine Finset.sum_congr rfl fun n2 _ => ?_
    refine Finset.sum_congr rfl fun n3 _ => ?_
    refine Finset.sum_congr rfl fun n4 _ => ?_
    by_cases h : n2 + n3 + n4 ≤ k
    · rw [if_pos h, if_pos h, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
    · rw [if_neg h, if_neg h]
  rw [h1, Gab_cauchy]
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n2 _ => ?_
  refine Finset.sum_congr rfl fun n3 _ => ?_
  refine Finset.sum_congr rfl fun n4 _ => ?_
  by_cases h : n2 + n3 + n4 ≤ k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Complex.ofReal_zero]

end
end Work.FIArea5.S16Hecke
