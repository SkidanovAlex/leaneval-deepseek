import Mathlib.Data.ZMod.QuotientRing
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_prime_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- A ring equivalence preserves the number of square-zero elements. -/
private lemma ncard_sq_eq_zero_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    ({x : R | x ^ 2 = 0}.ncard) = ({y : S | y ^ 2 = 0}.ncard) := by
  refine Set.ncard_congr' (Equiv.subtypeEquiv e.toEquiv ?_)
  intro x
  change x ^ 2 = 0 ↔ (e x) ^ 2 = 0
  constructor
  · intro h
    rw [← map_pow, h, map_zero]
  · intro h
    have : e (x ^ 2) = 0 := by rw [map_pow, h]
    exact e.injective (by rw [this, map_zero])

/-- The square-zero elements of a finite product ring are exactly the tuples whose
components are square-zero. -/
private noncomputable def piSqZeroEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    {f : Π i, ZMod (a i) // f ^ 2 = 0} ≃ Π i, {x : ZMod (a i) // x ^ 2 = 0} where
  toFun f := fun i => ⟨f.1 i, by
    have h := congrFun f.2 i
    simpa [Pi.pow_apply] using h⟩
  invFun g := ⟨fun i => (g i).1, by
    funext i
    simp [Pi.pow_apply, (g i).2]⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv g := by
    funext i
    apply Subtype.ext
    rfl

/-- Counting square-zero elements in a finite product of rings: it is the product of
the counts in the factors. -/
private lemma ncard_sq_eq_zero_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] :
    ({f : Π i, ZMod (a i) | f ^ 2 = 0}.ncard) =
      ∏ i, ({x : ZMod (a i) | x ^ 2 = 0}.ncard) := by
  calc
    ({f : Π i, ZMod (a i) | f ^ 2 = 0}.ncard)
        = Fintype.card {f : Π i, ZMod (a i) // f ^ 2 = 0} :=
          (Set.fintypeCard_eq_ncard _).symm
    _ = Fintype.card (Π i, {x : ZMod (a i) // x ^ 2 = 0}) :=
          Fintype.card_congr (piSqZeroEquiv a)
    _ = ∏ i, Fintype.card {x : ZMod (a i) // x ^ 2 = 0} := Fintype.card_pi
    _ = ∏ i, ({x : ZMod (a i) | x ^ 2 = 0}.ncard) := by
          apply Finset.prod_congr rfl
          intro i _
          exact Set.fintypeCard_eq_ncard {x : ZMod (a i) | x ^ 2 = 0}

/-- The number of square-zero elements of `ZMod (p ^ e)` for a prime `p`. -/
private lemma sq_zero_prime_pow (p e : ℕ) (hp : p.Prime) (he : 1 ≤ e) :
    ({α : ZMod (p ^ e) | α ^ 2 = 0}.ncard) = p ^ (e / 2) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [ncard_zmod_eq_range (n := p ^ e) (ψ := fun α : ZMod (p ^ e) => α ^ 2 = 0)]
  have h2 : ((Finset.range (p ^ e)).filter (fun r : ℕ => (r : ZMod (p ^ e)) ^ 2 = 0))
      = ((Finset.range (p ^ e)).filter (fun r : ℕ => p ^ e ∣ r ^ 2)) := by
    apply Finset.filter_congr
    intro r _
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  rw [h2]
  exact card_filter_range_sq_dvd_prime_pow p e hp he

lemma sq_roots_zero_card {d : ℕ} (hd : 0 < d) :
    ({α : ZMod d | α ^ 2 = 0}.ncard) =
      (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  haveI : NeZero d := ⟨hd0⟩
  haveI : ∀ p : d.primeFactors, NeZero ((p : ℕ) ^ (d.factorization p)) :=
    fun p => ⟨pow_ne_zero _ (Nat.mem_primeFactors.mp p.2).1.ne_zero⟩
  calc
    ({α : ZMod d | α ^ 2 = 0}.ncard)
        = ({f : Π p : d.primeFactors, ZMod ((p : ℕ) ^ (d.factorization p)) |
              f ^ 2 = 0}.ncard) :=
          ncard_sq_eq_zero_ringEquiv (ZMod.equivPi d hd0)
    _ = ∏ p : d.primeFactors,
          ({α : ZMod ((p : ℕ) ^ (d.factorization p)) | α ^ 2 = 0}.ncard) :=
          ncard_sq_eq_zero_pi (fun p : d.primeFactors => (p : ℕ) ^ (d.factorization p))
    _ = ∏ p : d.primeFactors, (p : ℕ) ^ (d.factorization p / 2) := by
          apply Finset.prod_congr rfl
          intro p _
          exact sq_zero_prime_pow (p : ℕ) (d.factorization p)
            (Nat.mem_primeFactors.mp p.2).1
            (Nat.Prime.factorization_pos_of_dvd (Nat.mem_primeFactors.mp p.2).1 hd0
              (Nat.mem_primeFactors.mp p.2).2.1)
    _ = (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2)) :=
          Finset.prod_coe_sort (Nat.primeFactors d)
            (fun p : ℕ => p ^ (d.factorization p / 2))

end Commons.NumberTheory.FriedlanderIwaniec