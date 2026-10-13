import Mathlib

/-!
# Elements of an `Away` localization that are `p^n`-th powers in the base

If `R` is a perfect ring of prime characteristic `p`, `C = R_f` is the localization of `R`
away from `f`, and `u : C` satisfies `u ^ p ^ n = algebraMap R C σ` for some `σ : R`, then
`u` already lies in the image of `R`.

The proof is short and uses only two ingredients:

* A perfect ring of prime characteristic is reduced (`isReduced_of_perfect`), and reducedness
  is preserved by localization; hence `C` is reduced.
* In any commutative ring `S` in which `p = 0` (here `C`, because `(p : C) = algebraMap R C p = 0`,
  even when `C` is the zero ring) the `p^n`-th power map satisfies
  `(x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n` (`sub_pow_pow_of_natCast_eq_zero`), so that
  `x ^ p ^ n = y ^ p ^ n` forces `x = y` as soon as `S` is reduced.

We then take `τ` to be the `p^n`-th root of `σ` in the perfect ring `R`.
-/

namespace Work.DSM4p

/-- In a commutative ring `S` with `(p : S) = 0`, where `p` is prime, the iterated Frobenius
map `x ↦ x ^ p ^ n` is additive on differences: `(x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n`.

Note that this needs only `(p : S) = 0`, not `CharP S p`; it therefore also applies to the
zero ring. -/
lemma sub_pow_pow_of_natCast_eq_zero {S : Type*} [CommRing S] {p : ℕ} (hp : p.Prime)
    (hS : (p : S) = 0) (n : ℕ) (x y : S) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  have hadd : ∀ a b : S, (a + b) ^ p ^ n = a ^ p ^ n + b ^ p ^ n := by
    intro a b
    obtain ⟨r, hr⟩ := (Commute.all a b).exists_add_pow_prime_pow_eq hp n
    rw [hr]; simp [hS]
  have hneg : ∀ b : S, (-b) ^ p ^ n = -(b ^ p ^ n) := by
    intro b
    have h1 : (-b) ^ p ^ n + b ^ p ^ n = 0 := by
      rw [← hadd (-b) b, neg_add_cancel, zero_pow (pow_ne_zero n hp.ne_zero)]
    exact eq_neg_of_add_eq_zero_left h1
  rw [sub_eq_add_neg, hadd, hneg, sub_eq_add_neg]

/-- A perfect ring of prime characteristic is reduced: if `x ^ n = 0`, choose `k` with
`n ≤ p ^ k`, then `x ^ p ^ k = 0`, and the bijective `p ^ k`-th power map forces `x = 0`. -/
lemma isReduced_of_perfect {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    [PerfectRing R p] : IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  have hle : n ≤ p ^ n :=
    le_of_lt (Nat.lt_pow_self (n := n) (a := p) (Fact.out : p.Prime).one_lt)
  have hz : x ^ p ^ n = 0 := by
    rw [← Nat.add_sub_cancel' hle, pow_add, hn, zero_mul]
  exact (iterateFrobeniusEquiv R p n).injective (by
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, hz,
      zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)])

universe a
theorem exists_eq_algebraMap_of_pow_pow {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R]
    [CharP R p] [PerfectRing R p] {f : R} {C : Type a} [CommRing C] [Algebra R C]
    [IsLocalization.Away f C] {n : ℕ} {u : C} {σ : R}
    (h : u ^ p ^ n = algebraMap R C σ) : ∃ τ : R, u = algebraMap R C τ := by
  -- `R` is reduced, hence so is its localization `C`.
  have hRred : IsReduced R := isReduced_of_perfect
  have hCred : IsReduced C := isReduced_localizationPreserves (Submonoid.powers f) C hRred
  -- `p = 0` in `C`, since `C` is an `R`-algebra and `p = 0` in `R`.
  have hCp : (p : C) = 0 := by
    rw [← map_natCast (algebraMap R C) p, CharP.cast_eq_zero, map_zero]
  -- `σ` has a `p ^ n`-th root `τ` in the perfect ring `R`.
  obtain ⟨τ, hτ⟩ := (iterateFrobeniusEquiv R p n).surjective σ
  rw [iterateFrobeniusEquiv_def] at hτ
  refine ⟨τ, ?_⟩
  have h1 : u ^ p ^ n = (algebraMap R C τ) ^ p ^ n := by
    rw [← map_pow, hτ]; exact h
  have h0 : (u - algebraMap R C τ) ^ p ^ n = 0 := by
    rw [sub_pow_pow_of_natCast_eq_zero (Fact.out : p.Prime) hCp n u (algebraMap R C τ),
      h1, sub_self]
  exact sub_eq_zero.mp (@eq_zero_of_pow_eq_zero C _ _ _ hCred _ h0)

end Work.DSM4p
