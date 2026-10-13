/-
DSSER: the `p`-divided cross-term of a list of ring elements.

If `l = [a₁, …, aₙ]` in a commutative ring `S` and `p` is prime, the binomial expansion of
`(S0 + a₁ + … + aₙ)^p` has, besides the `p`-th powers `S0^p, a₁^p, …, aₙ^p`, only terms whose
multinomial coefficient is divisible by `p`.  `crossAux p S0 l` collects those terms divided by `p`.
-/
import Submission.Work.DSSER.Basic

universe u v

namespace Work.DSSER

/-- The binomial expansion of `(x + y)^p` for prime `p`, with the "cross terms" divided by `p`. -/
theorem add_pow_prime {S : Type v} [CommRing S] (p : ℕ) [Fact p.Prime] (x y : S) :
    (x + y) ^ p = x ^ p + y ^ p + (p : S) *
      ∑ i ∈ Finset.range (p - 1),
        ((p.choose (i + 1) / p : ℕ) : S) * x ^ (i + 1) * y ^ (p - (i + 1)) := by
  have hp : p.Prime := Fact.out
  have hcoeff : ∀ i ∈ Finset.range (p - 1),
      ((p.choose (i + 1) : ℕ) : S) = (p : S) * ((p.choose (i + 1) / p : ℕ) : S) := by
    intro i hi
    have hi' : i + 1 < p := by
      have := Finset.mem_range.mp hi
      omega
    have hdvd : p ∣ p.choose (i + 1) := hp.dvd_choose (by omega) (by omega) (le_refl p)
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  have hterm : ∀ i ∈ Finset.range (p - 1),
      x ^ (i + 1) * y ^ (p - (i + 1)) * ((p.choose (i + 1) : ℕ) : S) =
        (p : S) * (((p.choose (i + 1) / p : ℕ) : S) * x ^ (i + 1) * y ^ (p - (i + 1))) := by
    intro i hi; rw [hcoeff i hi]; ring
  have hp1 : 1 ≤ p := hp.one_le
  rw [add_pow, Finset.sum_range_succ]
  rw [show Finset.range p = Finset.range (p - 1 + 1) from by rw [Nat.sub_add_cancel hp1],
    Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero,
    Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_self, Nat.choose_self]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- The second component of the fold is affine in its initial second component. -/
theorem foldl_snd_add {S : Type v} [CommRing S] (p : ℕ) (S0 H0 : S) (l : List S) :
    (l.foldl (crossStep (S := S) p) (S0, H0)).2 =
      H0 + (l.foldl (crossStep (S := S) p) (S0, 0)).2 := by
  induction l generalizing S0 H0 with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.foldl_cons,
      ih (crossStep (S := S) p (S0, 0) a).1 (crossStep (S := S) p (S0, 0) a).2]
    simp only [crossStep]
    ring

/-- One step of `crossAux`. -/
theorem crossAux_cons {S : Type v} [CommRing S] (p : ℕ) (S0 : S) (a : S) (l : List S) :
    crossAux p S0 (a :: l) = crossAux p (S0 + a) l +
      ∑ i ∈ Finset.range (p - 1),
        ((p.choose (i + 1) / p : ℕ) : S) * S0 ^ (i + 1) * a ^ (p - (i + 1)) := by
  simp only [crossAux, List.foldl_cons, crossStep]
  rw [foldl_snd_add]
  ring

/-- The defining property of `crossAux`: `p`-th powers plus `p` times the divided cross terms. -/
theorem crossAux_spec {S : Type v} [CommRing S] (p : ℕ) [Fact p.Prime] (S0 : S) (l : List S) :
    (S0 + l.sum) ^ p = S0 ^ p + (l.map (fun a => a ^ p)).sum + (p : S) * crossAux p S0 l := by
  induction l generalizing S0 with
  | nil => simp [crossAux]
  | cons a l ih =>
    rw [List.sum_cons, ← add_assoc, ih, List.map_cons, List.sum_cons, crossAux_cons,
      add_pow_prime p S0 a]
    ring

/-- Appending two lists splits the cross term. -/
theorem crossAux_append {S : Type v} [CommRing S] (p : ℕ) (S0 : S) (l₁ l₂ : List S) :
    crossAux p S0 (l₁ ++ l₂) = crossAux p (S0 + l₁.sum) l₂ + crossAux p S0 l₁ := by
  induction l₁ generalizing S0 with
  | nil => simp [crossAux]
  | cons a l ih =>
    rw [List.cons_append, crossAux_cons, List.sum_cons, crossAux_cons, ih (S0 + a)]
    ring

/-- If every element of `l` lies in the ideal `J`, then so does the whole cross term. -/
theorem crossAux_mem {S : Type v} [CommRing S] (p : ℕ) [Fact p.Prime] (J : Ideal S) (S0 : S)
    {l : List S} (hl : ∀ a ∈ l, a ∈ J) : crossAux p S0 l ∈ J := by
  induction l generalizing S0 with
  | nil => simp [crossAux]
  | cons a l ih =>
    rw [crossAux_cons]
    refine J.add_mem (ih (S0 + a) (fun b hb => hl b (List.mem_cons_of_mem _ hb))) ?_
    refine Ideal.sum_mem _ fun i hi => ?_
    have hle : 1 ≤ p - (i + 1) := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : a ^ (p - (i + 1)) ∈ J := by
      have h2 := Ideal.pow_le_pow_right hle
        (Ideal.pow_mem_pow (hl a (List.mem_cons_self ..)) (p - (i + 1)))
      simpa using h2
    exact J.mul_mem_left (((p.choose (i + 1) / p : ℕ) : S) * S0 ^ (i + 1)) h1

/-- The main consequence: the `p`-th power of the sum of a list is the sum of the `p`-th powers plus
`p` times the cross term. -/
theorem crossElt_sum_pow {S : Type v} [CommRing S] (p : ℕ) [Fact p.Prime] (l : List S) :
    (l.sum) ^ p = (l.map (fun a => a ^ p)).sum + (p : S) * crossElt p l := by
  have h := crossAux_spec p (0 : S) l
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simpa [crossElt, zero_pow hp.ne'] using h

/-- Appending a list all of whose elements lie in `J` changes the cross term by an element of `J`. -/
theorem crossElt_append_sub_mem {S : Type v} [CommRing S] (p : ℕ) [Fact p.Prime] (J : Ideal S)
    {l₁ l₂ : List S} (h : ∀ a ∈ l₂, a ∈ J) : crossElt p (l₁ ++ l₂) - crossElt p l₁ ∈ J := by
  rw [crossElt, crossElt, crossAux_append]
  have := crossAux_mem p J (0 + l₁.sum) h
  simpa using this

end Work.DSSER
