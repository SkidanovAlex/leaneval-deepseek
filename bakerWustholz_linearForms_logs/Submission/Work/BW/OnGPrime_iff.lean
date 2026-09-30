import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.RB.A4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- The product of all the cone coordinates: `∏_i X_{i,0} · ∏_i X_{i+1,1}`.  Its non-vanishing
at a point is exactly `OnG N` at that point. -/
noncomputable def coneProd (N : ℕ) : MR N :=
  (∏ i : Fin (N + 1), MvPolynomial.X (i, 0)) * (∏ i : Fin N, MvPolynomial.X (i.succ, 1))

lemma aeval_coneProd {N : ℕ} (x : Fin (N + 1) × Fin 2 → ℂ) :
    MvPolynomial.aeval x (coneProd N) =
      (∏ i : Fin (N + 1), x (i, 0)) * (∏ i : Fin N, x (i.succ, 1)) := by
  simp [coneProd]

/-- For a prime `p`, meeting the cone over `G = G_a × G_m^N` is the same as avoiding all the
cone coordinates `X_{i,0}` (`i : Fin (N+1)`) and `X_{i,1}` (`i ≥ 1`, i.e. `i = j.succ`).

The forward implication is immediate: if `X_{i,j} ∈ p ≤ ptIdeal x` then `X_{i,j}(x) = 0`, contrary
to `OnG N x`.  For the converse, note that `V(p)` is an irreducible closed subset of the affine
space which is not contained in `V(∏ X_{ij} ∩ cone coords)` (otherwise `p` would contain the product
and hence one factor, as `p` is prime); hence `V(p)` meets the open set of points with all cone
coordinates nonzero, and such a point `x` satisfies `p ≤ vanishingIdeal {x} = ptIdeal x` by the
Nullstellensatz (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, using `p` prime). -/
theorem OnGPrime_iff {N : ℕ} (p : Ideal (MR N)) (hp : p.IsPrime) :
    OnGPrime N p ↔
      (∀ i : Fin (N + 1), MvPolynomial.X (i, 0) ∉ p) ∧
        (∀ i : Fin N, MvPolynomial.X (i.succ, 1) ∉ p) := by
  constructor
  · rintro ⟨x, hx, hle⟩
    -- every cone coordinate vanishing on `V(p)` forces a zero coordinate of `x`
    have key : ∀ v : Fin (N + 1) × Fin 2, MvPolynomial.X v ∈ p → x v = 0 := by
      intro v hv
      have h1 : MvPolynomial.X v ∈ ptIdeal N x := hle hv
      have h2 : MvPolynomial.eval x (MvPolynomial.X v) = 0 := by
        simpa [ptIdeal] using h1
      simpa using h2
    constructor
    · intro i hi
      have hxi : x (i, 0) = 0 := key (i, 0) hi
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
      · rw [h] at hxi
        exact hx.1 hxi
      · rw [h] at hxi
        exact (hx.2 j).1 hxi
    · intro i hi
      exact (hx.2 i).2 (key (i.succ, 1) hi)
  · rintro ⟨hX0, hX1⟩
    haveI := hp
    -- the product of the cone coordinates is not in the prime ideal `p`
    have hF : coneProd N ∉ p := by
      intro hc
      have hc' : (∏ i : Fin (N + 1), MvPolynomial.X (i, 0)) *
          (∏ i : Fin N, MvPolynomial.X (i.succ, 1)) ∈ p := by
        simpa [coneProd] using hc
      rcases hp.mem_or_mem hc' with h1 | h2
      · rw [Ideal.IsPrime.prod_mem_iff] at h1
        obtain ⟨i, -, hi⟩ := h1
        exact hX0 i hi
      · rw [Ideal.IsPrime.prod_mem_iff] at h2
        obtain ⟨i, -, hi⟩ := h2
        exact hX1 i hi
    -- Nullstellensatz: if the whole of `V(p)` were a zero of that product, the product would
    -- lie in `p`; hence some point of `V(p)` has all cone coordinates nonzero
    have hex : ∃ x ∈ MvPolynomial.zeroLocus ℂ p, MvPolynomial.aeval x (coneProd N) ≠ 0 := by
      by_contra hcon
      have hmem : coneProd N ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ p) := by
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro x hx
        by_contra hxne
        exact hcon ⟨x, hx, hxne⟩
      rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (k := ℂ) (K := ℂ) p] at hmem
      exact hF hmem
    obtain ⟨x, hx, hFx⟩ := hex
    have hFx' : (∏ i : Fin (N + 1), x (i, 0)) * (∏ i : Fin N, x (i.succ, 1)) ≠ 0 := by
      rw [← aeval_coneProd x]
      exact hFx
    obtain ⟨hne1, hne2⟩ := mul_ne_zero_iff.mp hFx'
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · intro h
      exact hne1 (Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (N + 1))) h)
    · intro i
      exact ⟨fun h => hne1 (Finset.prod_eq_zero (Finset.mem_univ i.succ) h),
        fun h => hne2 (Finset.prod_eq_zero (Finset.mem_univ i) h)⟩
    · intro f hf
      have h1 : MvPolynomial.eval x f = 0 := by
        have := (MvPolynomial.mem_zeroLocus_iff.mp hx) f hf
        simpa using this
      simpa [ptIdeal] using h1

end Work.BW
