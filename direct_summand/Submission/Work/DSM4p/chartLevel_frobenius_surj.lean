import Mathlib
import Submission.Work.DSM4p.Chart

/-!
# DSM4p — Frobenius is surjective modulo `p` on the chart levels

`Work.DSM4p.chartRing hgr Q.ϖ n` is the `n`-th level `B[ϖ_k^n / g_k] ⊆ B[1/g]` of the
Riemann extension tower of the node `DSMap.Mix2.area_M4p` (`DSM4p/Chart.lean`).  This file
proves that Frobenius is *surjective modulo* `p` on each level:

`∀ x : chartRing hgr Q.ϖ n, ∃ y, x - y ^ p ∈ Ideal.span {(p : chartRing hgr Q.ϖ n)}`,

i.e. that `chartRing hgr Q.ϖ n / p` is a perfect ring.  This is item 5 of the list of facts
about the completed levels in `DSM4p/Completion.lean` (there stated for the `p`-adic
completion, which it is deduced from through the `modPow` comparison).

## The argument

The set

`T = {x : A | ∃ y : A, x - y ^ p ∈ Ideal.span {(p : A)}}`

is a `B`-subalgebra of any `B`-algebra `A`:

* it is closed under addition because Frobenius is additive modulo `p`
  (`frobDiff_add`: `(x + y) ^ p - x ^ p - y ^ p = p · x · y · r`, the `p` intermediate
  binomial coefficients being divisible by `p` — Mathlib's `exists_add_pow_prime_eq`);
* it is closed under multiplication because `(x * y) ^ p = x ^ p * y ^ p` (`mul_pow`);
* it contains `1` and `0` trivially;
* it contains the image of `B` if `B` itself has Frobenius surjective modulo `p`
  (`algebraMap_frobDiff`, from `Q.frobSurj`).

Hence it suffices that the chart level be generated as a `B`-algebra by elements which are
themselves `p`-th powers modulo `p`.  This is exactly the case here: by `chartGen_succ_pow`,
the `k`-th chart generator `x_k = ϖ_k^n / g_k` is the *exact* `p`-th power of the next
generator `x_{k+1}` (from the compatibility `gr (k+1) ^ p = gr k` of the root system and the
compatible system `Q.ϖ` of pseudo-uniformisers), so its Frobenius difference is `0`.  Since
`chartLevel hgr ϖ n = Algebra.adjoin B (Set.range (chartGen …))` by definition, and `B`'s
image is already inside `T` by `Q.frobSurj`, the subalgebra `T` is all of the level.
-/

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section Generic

variable {A : Type a} [CommRing A] {p : ℕ} [Fact p.Prime]

/-- **Frobenius is additive modulo `p`**: for `p` prime, `(x + y) ^ p - x ^ p - y ^ p` is a
multiple of `p`.  (`exists_add_pow_prime_eq` writes the difference as `p * x * y * r`.) -/
theorem frobDiff_add (x y : A) :
    (x + y) ^ p - (x ^ p + y ^ p) ∈ Ideal.span {(p : A)} := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := A) (p := p) (Fact.out : p.Prime) x y
  rw [hr]
  have key : x ^ p + y ^ p + p * x * y * r - (x ^ p + y ^ p) = (x * y * r) * (p : A) := by
    ring
  rw [key]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Generic

section Transfer

variable {A : Type a} [CommRing A] {B : Type a} [CommRing B] [Algebra B A]

/-- **Frobenius surjectivity modulo `p` transfers along `B → A`**: the image in `A` of an
element of `B` which is congruent to a `p`-th power modulo `p` is again congruent to a
`p`-th power modulo `p`. -/
theorem algebraMap_frobDiff {p : ℕ} (hb : ∀ b : B, ∃ y : B, b - y ^ p ∈ Ideal.span {(p : B)})
    (b : B) : ∃ y : A, algebraMap B A b - y ^ p ∈ Ideal.span {(p : A)} := by
  obtain ⟨y, hy⟩ := hb b
  refine ⟨algebraMap B A y, ?_⟩
  have hspan : (Ideal.span {(p : B)}).map (algebraMap B A) ≤ Ideal.span {(p : A)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hmem := hspan (Ideal.mem_map_of_mem (algebraMap B A) hy)
  rwa [map_sub, map_pow] at hmem

end Transfer

section Subalgebra

variable {A : Type a} [CommRing A] {B : Type a} [CommRing B] [Algebra B A]
variable {p : ℕ} [Fact p.Prime]

/-- The `B`-subalgebra of elements of `A` which are congruent modulo `p` to a `p`-th power,
assuming that this holds for the image of `B` (which makes the set stable under
`algebraMap`; the other closure properties are unconditional). -/
def frobSubalgebra
    (hB : ∀ b : B, ∃ y : A, algebraMap B A b - y ^ p ∈ Ideal.span {(p : A)}) :
    Subalgebra B A where
  carrier := {x | ∃ y : A, x - y ^ p ∈ Ideal.span {(p : A)}}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    have key : x * y - (a * b) ^ p = (x - a ^ p) * y + a ^ p * (y - b ^ p) := by
      rw [mul_pow]
      ring
    rw [key]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have key : x + y - (a + b) ^ p =
        (x - a ^ p) + (y - b ^ p) - ((a + b) ^ p - (a ^ p + b ^ p)) := by
      ring
    rw [key]
    exact sub_mem (add_mem ha hb) (frobDiff_add a b)
  zero_mem' := ⟨0, by
    rw [zero_pow (n := p) (Fact.out : p.Prime).ne_zero, sub_zero]
    exact Ideal.zero_mem _⟩
  algebraMap_mem' := hB

end Subalgebra

section Chart

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] {gr : ℕ → B}

/-- The `k`-th chart generator `x_k = ϖ_k^n / g_k`, regarded as an element of the `n`-th
chart level `chartRing hgr ϖ n` (rather than of the ambient ring `B[1/g]`). -/
noncomputable def chartGenIn (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (n k : ℕ) :
    chartRing hgr ϖ n :=
  ⟨chartGen hgr ϖ n k, chartGen_mem hgr ϖ n k⟩

/-- The root relation read inside the level: `x_k (n) = x_{k+1}(n) ^ p`. -/
theorem chartGenIn_pow (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (hϖ : IsRootSystem p ϖ)
    (n k : ℕ) :
    chartGenIn hgr ϖ n k = chartGenIn hgr ϖ n (k + 1) ^ p :=
  Subtype.ext (chartGen_succ_pow hgr hϖ n k)

/-- The `n`-th chart level is generated as a `B`-algebra by its own chart generators
`chartGenIn hgr ϖ n k` (the images of the `chartGen hgr ϖ n k` generating
`chartLevel hgr ϖ n = Algebra.adjoin B (Set.range (chartGen hgr ϖ n))`). -/
theorem adjoin_chartGenIn_eq_top (hgr : IsRootSystem p gr) (ϖ : ℕ → B) (n : ℕ) :
    Algebra.adjoin B (Set.range (chartGenIn hgr ϖ n)) = ⊤ := by
  have key : (Algebra.adjoin B (Set.range (chartGen hgr ϖ n)) : Subalgebra B (ChartAmbient gr))
      ≤ (Algebra.adjoin B (Set.range (chartGenIn hgr ϖ n))).map
          (Subalgebra.val (chartLevel hgr ϖ n)) := by
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_le_iff.mpr ?_
    rintro z ⟨k, rfl⟩
    exact Algebra.subset_adjoin ⟨chartGenIn hgr ϖ n k, Set.mem_range_self k, rfl⟩
  refine eq_top_iff.mpr ?_
  intro x _
  have hx := key x.2
  rw [Subalgebra.mem_map] at hx
  obtain ⟨s, hs, hsv⟩ := hx
  rwa [← (Subtype.ext hsv : s = x)]

end Chart

theorem chartLevel_frobenius_surj {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    (Q : DSMap.PerfectoidData p B) (gr : ℕ → B) (hgr : Work.DSM4p.IsRootSystem p gr) (n : ℕ) :
    ∀ x : Work.DSM4p.chartRing hgr Q.ϖ n, ∃ y, x - y ^ p ∈
      Ideal.span {((p : Work.DSM4p.chartRing hgr Q.ϖ n))} := by
  intro x
  have hB : ∀ b : B, ∃ y : chartRing hgr Q.ϖ n,
      algebraMap B (chartRing hgr Q.ϖ n) b - y ^ p ∈
        Ideal.span {(p : chartRing hgr Q.ϖ n)} :=
    fun b => algebraMap_frobDiff (A := chartRing hgr Q.ϖ n) (p := p) Q.frobSurj b
  let T := frobSubalgebra (B := B) (p := p) hB
  have hgen : ∀ k, chartGenIn hgr Q.ϖ n k ∈ T := by
    intro k
    exact ⟨chartGenIn hgr Q.ϖ n (k + 1), by
      rw [chartGenIn_pow hgr Q.ϖ Q.root n k, sub_self]
      exact Ideal.zero_mem _⟩
  have hx : x ∈ Algebra.adjoin B (Set.range (chartGenIn hgr Q.ϖ n)) := by
    rw [adjoin_chartGenIn_eq_top hgr Q.ϖ n]
    exact trivial
  exact (Algebra.adjoin_le_iff.mpr (Set.range_subset_iff.mpr hgen)) hx

end Work.DSM4p
