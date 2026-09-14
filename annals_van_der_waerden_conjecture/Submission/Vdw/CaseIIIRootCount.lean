import Mathlib
import Submission.Vdw.CaseIIIStability
import Submission.Vdw.ResidueFiber
import Submission.Vdw.MultiPrime
import Submission.Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero
import Submission.Commons.Data.Set.ncard_eq_natCard

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III, subcase (ii): per-prime constant-coefficient root bounds

In Case III of the proof of Theorem 1 (Bhargava, Annals of Math 2025), after the
double-discriminant machinery has attached to a polynomial `f` (upper coefficients
`u : Fin (n-1) → ℤ`, constant coefficient `c`) the divisor `A = ∏_{p | C, p > H^{δ/2}} p`
of `DD(u)`, one must count, for fixed `u`, the constant coefficients `c ∈ [-H,H]` for
which `Disc(f)` vanishes modulo every prime `p | A`.  For each such prime (with `p ∤ n`)
the value `Disc(f_{u,c}) = P_u(c)` (`P_u := concInnerZ n u ∈ ℤ[t]`, an integer
polynomial of degree `n-1` with leading coefficient `± nⁿ`) vanishes modulo `p` only on
a set of residue classes `c (mod p)` of size at most `n-1` (roots of a degree-`(n-1)`
polynomial over the field `ZMod p`).  This module proves that per-prime bound, plus the
box-transfer lemma needed to turn it into a count of `c ∈ [-H,H]`:

* `concInnerZ_modp_natDegree` — the reduction `P̄_u := P_u (mod p)` still has degree
  `n-1` (the leading coefficient `± nⁿ` is a unit mod `p` because `p ∤ n`);
* `concInnerZ_modp_root_card_le` — `P̄_u` has at most `n-1` roots in `ZMod p`;
* `int_dvd_discr_monicOfUpper_iff_modp_root` — for an integer `c`:
  `p | Disc(monicOfUpper n u c)` iff `c mod p` is a root of `P̄_u`;
* `bddInt_set_fiber_le` — the one-coordinate box-fiber bound
  (generic: `|{z ∈ [-H,H] : z mod m ∈ S}| ≤ |S| · ((2H+1)/m + 1)`);
* **`bddInt_discr_modp_fiber_le`** — the Case-III per-prime constant-coefficient count:
  `|{c ∈ [-H,H] : p | Disc(monicOfUpper n u c)}| ≤ (n-1) · ((2H+1)/p + 1)`.
-/

noncomputable section

namespace Submission.Vdw

/-- The reduction of `P_u := Disc_X(family)` modulo `p` keeps degree `n-1` when
`p ∤ n` (its leading coefficient is `± nⁿ`). -/
lemma concInnerZ_modp_natDegree (p n : ℕ) [Fact (Nat.Prime p)] (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    ((concInnerZ n u).map (Int.castRingHom (ZMod p))).natDegree = n - 1 := by
  classical
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  obtain ⟨hnd, hcoeff⟩ := concInnerZ_natDegree_coeff n hn u
  have hφlc : φ ((concInnerZ n u).leadingCoeff) ≠ 0 := by
    have hφn : φ (n : ℤ) ≠ 0 := by
      intro hz
      apply hpn
      rw [← CharP.cast_eq_zero_iff (ZMod p) p n]
      simpa [φ] using hz
    have hφm1 : φ (-1 : ℤ) ≠ 0 := by
      intro hz
      have : (0 : ZMod p) = 1 := by
        calc
          0 = φ ((-1 : ℤ) * (-1 : ℤ)) := by simpa using congrArg (fun x => x * x) hz.symm
          _ = φ (1 : ℤ) := by simp
          _ = 1 := by simp [φ]
      exact zero_ne_one this
    have hφc0 : φ ((concInnerZ n u).coeff (n - 1)) ≠ 0 := by
      rw [hcoeff]
      have hmul : φ ((-1 : ℤ) ^ (n * (n - 1) / 2) * (n : ℤ) ^ n) =
          (φ (-1 : ℤ)) ^ (n * (n - 1) / 2) * (φ (n : ℤ)) ^ n := by
        rw [map_mul, map_pow, map_pow]
      rw [hmul]
      exact mul_ne_zero (pow_ne_zero (n * (n - 1) / 2) hφm1) (pow_ne_zero n hφn)
    have hlc : (concInnerZ n u).leadingCoeff = (concInnerZ n u).coeff (n - 1) := by
      rw [leadingCoeff, hnd]
    simpa [hlc] using hφc0
  have h := Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero φ hφlc
  simpa [φ, hnd] using h

/-- The reduction `P̄_u` has at most `n-1` roots in `ZMod p`. -/
lemma concInnerZ_modp_root_card_le (p n : ℕ) [Fact (Nat.Prime p)] (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    ({x : ZMod p | ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval x = 0} :
        Set (ZMod p)).ncard ≤ n - 1 := by
  classical
  let P : (ZMod p)[X] := (concInnerZ n u).map (Int.castRingHom (ZMod p))
  have hnd : P.natDegree = n - 1 := by
    simpa [P] using concInnerZ_modp_natDegree p n hn hpn u
  have hP0 : P ≠ 0 := by
    intro hz
    have : P.natDegree = 0 := by simp [hz]
    omega
  let Z : Finset (ZMod p) := Finset.univ.filter (fun x => P.eval x = 0)
  have hZ : Z.val ⊆ P.roots := by
    intro x hx
    rw [Polynomial.mem_roots hP0]
    exact (Finset.mem_filter.mp hx).2
  have hcard : Z.card ≤ n - 1 := by
    exact le_trans (Polynomial.card_le_degree_of_subset_roots hZ) (le_of_eq hnd)
  have hZS : ({x : ZMod p | P.eval x = 0} : Set (ZMod p)) = ↑Z := by
    ext x
    simp [Z]
  calc
    ({x : ZMod p | P.eval x = 0} : Set (ZMod p)).ncard ≤ n - 1 := by
      rw [hZS]
      simp
      exact hcard

/-- For an integer `c`, `p | Disc(monicOfUpper n u c)` iff `c mod p` is a root of
`P̄_u`. -/
lemma int_dvd_discr_monicOfUpper_iff_modp_root (p n : ℕ) [Fact (Nat.Prime p)]
    (hn : 1 ≤ n) (u : Fin (n - 1) → ℤ) (c : ℤ) :
    (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u c) ↔
      ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval (c : ZMod p) = 0 := by
  classical
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hcom : ((concInnerZ n u).map φ).eval (φ c) = φ ((concInnerZ n u).eval c) := by
    calc
      eval (φ c) (map φ (concInnerZ n u)) = eval₂ φ (φ c) (concInnerZ n u) := eval_map φ (φ c)
      _ = φ (eval c (concInnerZ n u)) := eval₂_hom (f := φ) (p := concInnerZ n u) c
  constructor
  · intro hd
    have hφ : φ ((concInnerZ n u).eval c) = 0 := by
      rw [concInnerZ_eval_eq_discr n hn u c]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.discr (monicOfUpper n u c)) p).2 hd
    simpa [φ, hcom] using hφ
  · intro hroot
    have hφ : φ ((concInnerZ n u).eval c) = 0 := by
      simpa [φ, hcom] using hroot
    have hd0 : φ (Polynomial.discr (monicOfUpper n u c)) = 0 := by
      rw [← concInnerZ_eval_eq_discr n hn u c]
      exact hφ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.discr (monicOfUpper n u c)) p).1 hd0

/-- **One-coordinate box fiber bound.**  For a set `S` of residues modulo `m`, at most
`|S| · ((2H+1)/m + 1)` integers of `[-H,H]` reduce into `S`. -/
theorem bddInt_set_fiber_le (H m : ℕ) (hm : 1 ≤ m) (S : Set (ZMod m)) :
    Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) ∈ S} ≤
      S.ncard * ((2 * H + 1) / m + 1) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  let X : Type := {z : BddInt H // ((z : ℤ) : ZMod m) ∈ S}
  let Y : Type := {s : ZMod m // s ∈ S}
  let f : X → Y := fun z => ⟨((z.1 : ℤ) : ZMod m), z.2⟩
  haveI : Fintype X := inferInstance
  haveI : Fintype Y := inferInstance
  have hS : S.ncard = Nat.card Y := by
    change S.ncard = Nat.card {s : ZMod m // s ∈ S}
    exact (ncard_eq_natCard S)
  have hfibN (y : Y) : Nat.card {x : X // f x = y} ≤ (2 * H + 1) / m + 1 := by
    haveI : Fintype {x : X // f x = y} := inferInstance
    let e2 : {x : X // f x = y} ≃ {z : BddInt H // ((z : ℤ) : ZMod m) = y.1} := by
      refine {
        toFun := fun x => ⟨x.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro z
          apply Subtype.ext
          rfl }
      · have hx := congrArg (fun w : Y => w.1) x.2
        simpa [f] using hx
      · rw [z.2]
        exact y.2
      · apply Subtype.ext
        exact z.2
    calc
      Nat.card {x : X // f x = y} =
          Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) = y.1} := Nat.card_congr e2
      _ ≤ (2 * H + 1) / m + 1 := bddInt_congruent_card_le H m hm y.1
  calc
    Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) ∈ S} ≤
        S.ncard * ((2 * H + 1) / m + 1) := by
      calc
        Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) ∈ S} =
            ∑ y : Y, Nat.card {x : X // f x = y} := by
          calc
            Nat.card {z : BddInt H // ((z : ℤ) : ZMod m) ∈ S} =
                Nat.card (Sigma (fun y : Y => {x : X // f x = y})) := by
              simpa [X, Y, f] using (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
            _ = ∑ y : Y, Nat.card {x : X // f x = y} := Nat.card_sigma
        _ ≤ ∑ y : Y, ((2 * H + 1) / m + 1) := by
          apply Finset.sum_le_sum
          intro y hy
          exact hfibN y
        _ = Nat.card Y * ((2 * H + 1) / m + 1) := by
          rw [Finset.sum_const, Finset.card_univ]
          simp [Nat.card_eq_fintype_card]
        _ = S.ncard * ((2 * H + 1) / m + 1) := by rw [← hS]

/-- **Case-III per-prime constant-coefficient count.**  Fix the upper coefficients
`u`.  Among the constant coefficients `c ∈ [-H,H]`, at most `(n-1)·((2H+1)/p + 1)`
satisfy `p | Disc(monicOfUpper n u c)`. -/
theorem bddInt_discr_modp_fiber_le (p H n : ℕ) [Fact (Nat.Prime p)] (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    Nat.card {c : BddInt H // (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} ≤
      (n - 1) * ((2 * H + 1) / p + 1) := by
  classical
  have hp1 : 1 ≤ p := le_of_lt (Fact.out : Nat.Prime p).one_lt
  let S : Set (ZMod p) := {x : ZMod p |
    ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval x = 0}
  have hSn : S.ncard ≤ n - 1 := by
    simpa [S] using concInnerZ_modp_root_card_le p n hn hpn u
  have hfib := bddInt_set_fiber_le H p hp1 S
  have hB : Nat.card {c : BddInt H // ((c : ℤ) : ZMod p) ∈ S} ≤
      (n - 1) * ((2 * H + 1) / p + 1) := by
    exact le_trans hfib (Nat.mul_le_mul_right _ hSn)
  -- relate membership in S to the divisibility condition
  have hrel (c : BddInt H) :
      ((c : ℤ) : ZMod p) ∈ S ↔ (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ)) := by
    change ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval ((c : ℤ) : ZMod p) = 0 ↔
      (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))
    rw [int_dvd_discr_monicOfUpper_iff_modp_root p n (by omega : 1 ≤ n) u (c : ℤ)]
  calc
    Nat.card {c : BddInt H // (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))} =
        Nat.card {c : BddInt H // ((c : ℤ) : ZMod p) ∈ S} := by
      let X : Type := {c : BddInt H // (p : ℤ) ∣ Polynomial.discr (monicOfUpper n u (c : ℤ))}
      let B : Type := {c : BddInt H // ((c : ℤ) : ZMod p) ∈ S}
      have eXB : X ≃ B := by
        refine {
          toFun := fun c => ⟨c.1, (hrel c.1).2 c.2⟩
          invFun := fun c => ⟨c.1, (hrel c.1).1 c.2⟩
          left_inv := by intro c; apply Subtype.ext; rfl
          right_inv := by intro c; apply Subtype.ext; rfl }
      simpa [X, B] using (Nat.card_congr eXB)
    _ ≤ (n - 1) * ((2 * H + 1) / p + 1) := hB
/-- Subtype-cardinality form of `concInnerZ_modp_root_card_le`. -/
lemma concInnerZ_modp_rootCard_subtype_le (p n : ℕ) [Fact (Nat.Prime p)] (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) (u : Fin (n - 1) → ℤ) :
    Nat.card {x : ZMod p // ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval x = 0} ≤
      n - 1 := by
  have h := concInnerZ_modp_root_card_le p n hn hpn u
  change Nat.card {x : ZMod p // x ∈ ({x : ZMod p |
    ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval x = 0} : Set (ZMod p))} ≤ n - 1
  rw [← Commons.Data.Set.ncard_eq_natCard ({x : ZMod p |
    ((concInnerZ n u).map (Int.castRingHom (ZMod p))).eval x = 0} : Set (ZMod p))]
  exact h

/-- If the squarefree `A` has all its (distinct) prime divisors dividing `d`,
then `A | d`. -/
lemma dvd_of_forall_primeFactors_dvd_of_squarefree (A d : ℕ) (hsq : Squarefree A)
    (hd : ∀ p ∈ A.primeFactors, p ∣ d) : A ∣ d := by
  classical
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply pairwise_coprime_prod_dvd_nat (q := fun p : ℕ => p) (s := A.primeFactors) (n := d)
  · intro i hi j hj hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi)
      (Nat.prime_of_mem_primeFactors hj)).2 hij
  · exact hd

/-- For `H < A`, an interval of length `2H+1` contains at most two integers in
any arithmetic progression modulo `A`. -/
lemma div_twoH_add_one_le_two_of_lt (H A : ℕ) (h : H < A) :
    (2 * H + 1) / A + 1 ≤ 2 := by
  have hA0 : 0 < A := by omega
  have hlt : (2 * H + 1) / A < 2 := by
    rw [Nat.div_lt_iff_lt_mul hA0]
    omega
  omega

end Submission.Vdw
