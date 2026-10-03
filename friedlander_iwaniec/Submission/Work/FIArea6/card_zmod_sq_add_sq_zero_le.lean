import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An upper bound for the number of solutions of `x² + y² = 0` in `(ZMod d)²`

For squarefree `d`, the number of pairs `(x, y)` with `x² + y² = 0` in `ZMod d` is at most
`∏_{p | d} (2p - 1)`.  Indeed by the Chinese remainder theorem `ZMod d ≃ ∏_{p | d} ZMod p`,
the solution set is the product of the solution sets modulo each prime, and modulo a prime `p`
the number of solutions is at most `2p - 1` (there is only `(0,0)` on the line `y = 0`, and for
each of the `p - 1` nonzero values of `y` the equation `x² = -y²` has at most two solutions).
-/

set_option linter.style.haveILetI false

open Finset

namespace Work.FIArea6

/-- In a field (here `ZMod p` for a prime `p`), the equation `x ^ 2 = c` has at most two
solutions. -/
lemma card_le_two_sq_eq (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (Finset.univ.filter (fun x : ZMod p => x ^ 2 = c)).card ≤ 2 := by
  classical
  by_cases hne : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = c)).Nonempty
  · obtain ⟨a, ha⟩ := hne
    rw [Finset.mem_filter] at ha
    have hsub : Finset.univ.filter (fun x : ZMod p => x ^ 2 = c) ⊆
        ({a, -a} : Finset (ZMod p)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hsq : x ^ 2 = a ^ 2 := by rw [hx.2, ha.2]
      rcases eq_or_eq_neg_of_sq_eq_sq x a hsq with h | h
      · simp [h]
      · simp [h]
    calc (Finset.univ.filter (fun x : ZMod p => x ^ 2 = c)).card
        ≤ ({a, -a} : Finset (ZMod p)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          rw [show ({a, -a} : Finset (ZMod p)) = insert a {-a} from rfl]
          exact le_trans (Finset.card_insert_le a {-a}) (by simp)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

/-- Modulo a prime `p`, the equation `x ^ 2 + y ^ 2 = 0` has at most `2 * p - 1` solutions. -/
lemma card_zmod_prime_sq_add_sq_zero_le (p : ℕ) [Fact p.Prime] :
    (Finset.univ.filter (fun r : ZMod p × ZMod p => r.1 ^ 2 + r.2 ^ 2 = 0)).card ≤ 2 * p - 1 := by
  classical
  set sols : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun r : ZMod p × ZMod p => r.1 ^ 2 + r.2 ^ 2 = 0) with hsols
  have hmaps : Set.MapsTo Prod.snd (sols : Set (ZMod p × ZMod p))
      ((Finset.univ : Finset (ZMod p)) : Set (ZMod p)) := by
    intro q _
    exact Finset.mem_univ _
  have hterm : ∀ y ∈ (Finset.univ : Finset (ZMod p)),
      (sols.filter (fun q => Prod.snd q = y)).card ≤ (if y = 0 then 1 else 2) := by
    intro y _
    by_cases hy : y = 0
    · subst hy
      rw [if_pos rfl]
      have hsub : sols.filter (fun q : ZMod p × ZMod p => Prod.snd q = 0) ⊆
          ({(0, 0)} : Finset (ZMod p × ZMod p)) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        simp only [hsols, Finset.mem_filter, Finset.mem_univ, true_and] at hq1
        rw [Finset.mem_singleton]
        have hq2' : q.2 = 0 := hq2
        have hx : q.1 = 0 := by
          rw [hq2'] at hq1
          have h1 : q.1 * q.1 = 0 := by simpa [pow_two] using hq1
          exact mul_self_eq_zero.mp h1
        exact Prod.ext hx hq2'
      calc (sols.filter (fun q : ZMod p × ZMod p => Prod.snd q = 0)).card
          ≤ ({(0, 0)} : Finset (ZMod p × ZMod p)).card := Finset.card_le_card hsub
        _ = 1 := by simp
    · rw [if_neg hy]
      have hsub : sols.filter (fun q : ZMod p × ZMod p => Prod.snd q = y) ⊆
          (Finset.univ.filter (fun x : ZMod p => x ^ 2 = -(y ^ 2))).image (fun x => (x, y)) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        simp only [hsols, Finset.mem_filter, Finset.mem_univ, true_and] at hq1
        rw [Finset.mem_image]
        refine ⟨q.1, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hq2' : q.2 = y := hq2
          have : q.1 ^ 2 + y ^ 2 = 0 := by rw [← hq2']; exact hq1
          exact eq_neg_of_add_eq_zero_left this
        · rw [← hq2]
      calc (sols.filter (fun q : ZMod p × ZMod p => Prod.snd q = y)).card
          ≤ ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = -(y ^ 2))).image
              (fun x => (x, y))).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun x : ZMod p => x ^ 2 = -(y ^ 2))).card :=
            Finset.card_image_le
        _ ≤ 2 := card_le_two_sq_eq p (-(y ^ 2))
  have hsum : ∑ y : ZMod p, (if y = 0 then (1:ℕ) else 2) = 2 * p - 1 := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (ZMod p))
      (fun y => if y = 0 then (1:ℕ) else 2) (Finset.mem_univ 0)]
    rw [if_pos rfl]
    have h2 : ∀ y ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        (if y = 0 then (1:ℕ) else 2) = 2 := by
      intro y hy
      rw [Finset.mem_erase] at hy
      exact if_neg hy.1
    rw [Finset.sum_congr rfl h2, Finset.sum_const]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ, ZMod.card]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [smul_eq_mul]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc (∑ y ∈ (Finset.univ : Finset (ZMod p)), (sols.filter (fun q => Prod.snd q = y)).card)
      ≤ ∑ y ∈ (Finset.univ : Finset (ZMod p)), (if y = 0 then 1 else 2) :=
        Finset.sum_le_sum hterm
    _ = 2 * p - 1 := hsum

/-- For squarefree `d`, the number of pairs `(x, y)` with `x ^ 2 + y ^ 2 = 0` in `ZMod d` is at
most `∏_{p | d} (2 * p - 1)`. -/
theorem card_zmod_sq_add_sq_zero_le (d : ℕ) [NeZero d] (hdsq : Squarefree d) :
    (Finset.univ.filter (fun r : ZMod d × ZMod d => r.1 ^ 2 + r.2 ^ 2 = 0)).card
      ≤ ∏ p ∈ d.primeFactors, (2 * p - 1) := by
  classical
  haveI hfact : ∀ p : d.primeFactors, Fact (Nat.Prime (p : ℕ)) :=
    fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have hprod : ∏ p : d.primeFactors, (p : ℕ) = d := by
    rw [show (∏ p : d.primeFactors, (p : ℕ)) = ∏ p ∈ d.primeFactors, (p : ℕ) from
      Finset.prod_attach d.primeFactors (fun p : ℕ => (p : ℕ))]
    exact Nat.prod_primeFactors_of_squarefree hdsq
  have hcop : Pairwise (Function.onFun Nat.Coprime (fun p : d.primeFactors => (p : ℕ))) := by
    intro p q hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
      (Nat.prime_of_mem_primeFactors q.2)).mpr (fun h => hpq (Subtype.ext h))
  -- Chinese remainder theorem: `ZMod d ≃+* ∏_{p | d} ZMod p`
  let e : ZMod d ≃+* (Π p : d.primeFactors, ZMod (p : ℕ)) :=
    (ZMod.ringEquivCongr hprod).symm.trans
      (ZMod.prodEquivPi (fun p : d.primeFactors => (p : ℕ)) hcop)
  -- the induced injection on solution sets
  let g : {r : ZMod d × ZMod d // r.1 ^ 2 + r.2 ^ 2 = 0} →
      (Π p : d.primeFactors, {q : ZMod (p : ℕ) × ZMod (p : ℕ) // q.1 ^ 2 + q.2 ^ 2 = 0}) :=
    fun r p => ⟨(e r.val.1 p, e r.val.2 p), by
      have h : e (r.val.1 ^ 2 + r.val.2 ^ 2) = 0 := by rw [r.2, map_zero]
      have h2 : e r.val.1 ^ 2 + e r.val.2 ^ 2 = 0 := by
        simpa [map_add, map_pow] using h
      have hp := congr_fun h2 p
      simpa using hp⟩
  have ginj : Function.Injective g := by
    intro r s hrs
    apply Subtype.ext
    have h1 : e r.val.1 = e s.val.1 := by
      funext p
      have hh := congr_arg Subtype.val (congr_fun hrs p)
      exact (Prod.ext_iff.mp hh).1
    have h2 : e r.val.2 = e s.val.2 := by
      funext p
      have hh := congr_arg Subtype.val (congr_fun hrs p)
      exact (Prod.ext_iff.mp hh).2
    exact Prod.ext (e.injective h1) (e.injective h2)
  have hcf : (Finset.univ.filter (fun r : ZMod d × ZMod d => r.1 ^ 2 + r.2 ^ 2 = 0)).card
      = Fintype.card {r : ZMod d × ZMod d // r.1 ^ 2 + r.2 ^ 2 = 0} := by
    rw [Fintype.card_subtype]
  rw [hcf]
  calc Fintype.card {r : ZMod d × ZMod d // r.1 ^ 2 + r.2 ^ 2 = 0}
      ≤ Fintype.card (Π p : d.primeFactors,
          {q : ZMod (p : ℕ) × ZMod (p : ℕ) // q.1 ^ 2 + q.2 ^ 2 = 0}) :=
        Fintype.card_le_of_injective g ginj
    _ = ∏ p : d.primeFactors,
          Fintype.card {q : ZMod (p : ℕ) × ZMod (p : ℕ) // q.1 ^ 2 + q.2 ^ 2 = 0} :=
        Fintype.card_pi
    _ ≤ ∏ p : d.primeFactors, (2 * (p : ℕ) - 1) := by
        apply Finset.prod_le_prod'
        intro p _
        rw [Fintype.card_subtype]
        exact card_zmod_prime_sq_add_sq_zero_le (p : ℕ)
    _ = ∏ p ∈ d.primeFactors, (2 * p - 1) :=
        Finset.prod_attach d.primeFactors (fun p : ℕ => 2 * p - 1)

end Work.FIArea6
