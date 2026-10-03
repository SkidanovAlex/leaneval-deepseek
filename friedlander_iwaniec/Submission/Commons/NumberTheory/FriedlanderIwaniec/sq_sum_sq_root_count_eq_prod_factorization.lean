import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Set

/-- A ring equivalence carries the solution set of `X ^ 2 + c ^ 2 = 0` onto the
solution set of `X ^ 2 + (e c) ^ 2 = 0`. -/
private lemma sq_add_sq_image_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (c : R) :
    e '' ({r : R | r ^ 2 + c ^ 2 = 0} : Set R) = {s : S | s ^ 2 + (e c) ^ 2 = 0} := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    change (e r) ^ 2 + (e c) ^ 2 = 0
    rw [← map_pow e r 2, ← map_pow e c 2, ← map_add, hr, map_zero]
  · intro hs
    change s ^ 2 + (e c) ^ 2 = 0 at hs
    refine ⟨e.symm s, ?_, ?_⟩
    · have h := congrArg (e.symm) hs
      simp only [map_add, map_pow, map_zero, e.symm_apply_apply] at h
      exact h
    · exact e.apply_symm_apply s

/-- In a product of commutative rings, `f ^ 2 + g ^ 2 = 0` holds exactly when
every componentwise equation `f i ^ 2 + g i ^ 2 = 0` holds. -/
private lemma sq_add_sq_pi_eq {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (g : Π i, ZMod (a i)) :
    ({f : Π i, ZMod (a i) | f ^ 2 + g ^ 2 = 0} : Set (Π i, ZMod (a i))) =
      Set.pi Set.univ (fun i => {α : ZMod (a i) | α ^ 2 + g i ^ 2 = 0}) := by
  ext f
  constructor
  · intro hf i
    have h := congrFun hf i
    simpa using h
  · intro hf
    funext i
    simpa using hf i

/-- The number of elements of a finite product of finite sets is the product of
the numbers of elements of the factors. -/
private lemma ncard_pi_of_finite {ι : Type*} [Fintype ι] {α : ι → Type*} {s : ∀ i, Set (α i)}
    (h : ∀ i, (s i).Finite) : (Set.pi Set.univ s).ncard = ∏ i, (s i).ncard := by
  have h1 : (∏ i, (s i).encard) = ∏ i, ((s i).ncard : ℕ∞) :=
    Finset.prod_congr rfl (fun i _ => ((h i).cast_ncard_eq).symm)
  rw [Set.ncard_def, Set.encard_pi_eq_prod_encard, h1, ← Nat.cast_prod, ENat.toNat_natCast]

/-- The number of `f` in a product ring `Π i, ZMod (a i)` with `f ^ 2 + g ^ 2 = 0`
is the product over `i` of the number of solutions in each factor. -/
private lemma ncard_sq_add_sq_pi {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (g : Π i, ZMod (a i)) (ha : ∀ i, a i ≠ 0) :
    ({f : Π i, ZMod (a i) | f ^ 2 + g ^ 2 = 0}.ncard) =
      ∏ i, ({α : ZMod (a i) | α ^ 2 + g i ^ 2 = 0}.ncard) := by
  rw [sq_add_sq_pi_eq]
  refine ncard_pi_of_finite (fun i => ?_)
  have : NeZero (a i) := ⟨ha i⟩
  exact Set.toFinite _

/-- **Root count factorization.**  By the Chinese remainder theorem
`ZMod d ≃+* ∏_{p | d} ZMod (p ^ v_p(d))`, the solutions of `x ^ 2 + b ^ 2 = 0`
modulo `d` correspond bijectively to independent choices of a solution modulo
each prime-power divisor, so the total number of roots is the product over the
distinct prime factors `p` of `d` of the number of roots modulo `p ^ v_p(d)`. -/
lemma sq_sum_sq_root_count_eq_prod_factorization {d b : ℕ} (hd : 0 < d) :
    ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) =
      (Nat.primeFactors d).prod (fun p =>
        ({α : ZMod (p ^ d.factorization p) |
            α ^ 2 + (b : ZMod (p ^ d.factorization p)) ^ 2 = 0}.ncard)) := by
  classical
  have hd0 : d ≠ 0 := hd.ne'
  let e : ZMod d ≃+* Π p : d.primeFactors, ZMod ((p : ℕ) ^ d.factorization p) :=
    ZMod.equivPi d hd0
  let F : ℕ → ℕ := fun p =>
    ({α : ZMod (p ^ d.factorization p) |
      α ^ 2 + (b : ZMod (p ^ d.factorization p)) ^ 2 = 0}.ncard)
  have hb : e (b : ZMod d) =
      (fun p : d.primeFactors => (b : ZMod ((p : ℕ) ^ d.factorization p))) := by
    rw [map_natCast]
    funext p
    rfl
  have hcalc : ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) =
      (Nat.primeFactors d).prod F := by
    calc
      ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard)
          = (e '' ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0} : Set (ZMod d))).ncard :=
              (Set.ncard_image_of_injective _ e.injective).symm
      _ = ({f : Π p : d.primeFactors, ZMod ((p : ℕ) ^ d.factorization p) |
              f ^ 2 + (fun p : d.primeFactors =>
                (b : ZMod ((p : ℕ) ^ d.factorization p))) ^ 2 = 0}.ncard) := by
              rw [sq_add_sq_image_ringEquiv e (b : ZMod d), hb]
      _ = ∏ p : d.primeFactors, F (p : ℕ) :=
              ncard_sq_add_sq_pi (fun p : d.primeFactors => (p : ℕ) ^ d.factorization p)
                (fun p : d.primeFactors => (b : ZMod ((p : ℕ) ^ d.factorization p)))
                (fun p => pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero)
      _ = (Nat.primeFactors d).prod F :=
              Finset.prod_coe_sort (s := d.primeFactors) (f := F)
  exact hcalc

end Commons.NumberTheory.FriedlanderIwaniec