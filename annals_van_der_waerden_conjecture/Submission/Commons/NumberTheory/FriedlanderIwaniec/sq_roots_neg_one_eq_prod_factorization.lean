import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.ZMod.QuotientRing
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mul_of_coprime

namespace Commons.NumberTheory.FriedlanderIwaniec

open Set
open scoped Function

/-- The number of elements of a finite product of finite sets is the product of
the numbers of elements of the factors. -/
private lemma ncard_pi_of_finite {ι : Type*} [Fintype ι] {α : ι → Type*} {s : ∀ i, Set (α i)}
    (h : ∀ i, (s i).Finite) : (Set.pi Set.univ s).ncard = ∏ i, (s i).ncard := by
  have h1 : (∏ i, (s i).encard) = ∏ i, ((s i).ncard : ℕ∞) :=
    Finset.prod_congr rfl (fun i _ => ((h i).cast_ncard_eq).symm)
  rw [Set.ncard_def, Set.encard_pi_eq_prod_encard, h1, ← Nat.cast_prod, ENat.toNat_natCast]

/-- In a product of commutative rings, `f ^ 2 = -1` holds componentwise, so the
solution set of `x ^ 2 = -1` is the product of the solution sets of the
factors. -/
private lemma sq_neg_one_pi_eq {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    ({f : Π i, ZMod (a i) | f ^ 2 = -1} : Set (Π i, ZMod (a i))) =
      Set.pi Set.univ (fun i => {α : ZMod (a i) | α ^ 2 = -1}) := by
  ext f
  constructor
  · intro hf i
    have h := congrFun hf i
    simpa using h
  · intro hf
    funext i
    simpa using hf i

/-- The number of square roots of `-1` in a product of rings `ZMod (a i)` is the
product of the numbers of square roots of `-1` in the factors. -/
private lemma ncard_sq_neg_one_pi {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : ∀ i, a i ≠ 0) :
    ({f : Π i, ZMod (a i) | f ^ 2 = -1}.ncard) =
      ∏ i, ({α : ZMod (a i) | α ^ 2 = -1}.ncard) := by
  rw [sq_neg_one_pi_eq]
  refine ncard_pi_of_finite (fun i => ?_)
  have : NeZero (a i) := ⟨ha i⟩
  exact Set.toFinite _

/-- **Root count factorization.**  By the Chinese remainder theorem
`ZMod d ≃+* ∏_{p | d} ZMod (p ^ v_p(d))`, the solutions of `x ^ 2 = -1` modulo
`d` correspond bijectively to independent choices of a solution modulo each
prime-power divisor, so the total number of roots is the product over the
distinct prime factors `p` of `d` of the number of roots modulo `p ^ v_p(d)`. -/
lemma sq_roots_neg_one_eq_prod_factorization {d : ℕ} (hd : 0 < d) :
    ({α : ZMod d | α ^ 2 = -1}.ncard) =
      (Nat.primeFactors d).prod (fun p => ({α : ZMod (p ^ d.factorization p) | α ^ 2 = -1}.ncard)) := by
  classical
  have hd0 : d ≠ 0 := hd.ne'
  let e : ZMod d ≃+* Π p : d.primeFactors, ZMod ((p : ℕ) ^ d.factorization p) := ZMod.equivPi d hd0
  calc
    ({α : ZMod d | α ^ 2 = -1}.ncard)
        = (e '' ({α : ZMod d | α ^ 2 = -1} : Set (ZMod d))).ncard :=
            (Set.ncard_image_of_injective _ e.injective).symm
    _ = ({f : Π p : d.primeFactors, ZMod ((p : ℕ) ^ d.factorization p) | f ^ 2 = -1}.ncard) := by
            rw [ringEquiv_image_sq_neg_one e]
    _ = ∏ p : d.primeFactors, ({α : ZMod ((p : ℕ) ^ d.factorization p) | α ^ 2 = -1}.ncard) :=
            ncard_sq_neg_one_pi (fun p : d.primeFactors => (p : ℕ) ^ d.factorization p)
              (fun p => pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero)
    _ = (Nat.primeFactors d).prod (fun p => ({α : ZMod (p ^ d.factorization p) | α ^ 2 = -1}.ncard)) :=
            Finset.prod_coe_sort (s := d.primeFactors)
              (f := fun p : ℕ => ({α : ZMod (p ^ d.factorization p) | α ^ 2 = -1}.ncard))

end Commons.NumberTheory.FriedlanderIwaniec