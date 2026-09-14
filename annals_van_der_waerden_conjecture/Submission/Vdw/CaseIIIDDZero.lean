import Mathlib
import Submission.Vdw.CaseIIIRegion
import Submission.Vdw.CaseIIIHeight

open Polynomial
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III: the `DD(u_f) = 0` piece is `O(H^(n-1))`

Case III splits into (a) the double-discriminant-vanishing piece
`DD(u_f) = 0`, (b) subcase (i), and (c) subcase (ii) (whose counting is the
`CaseIIIRegion` / `CaseIIIWrapper` / `CaseIIIField` machinery).  This module
bounds piece (a):

    #{f ∈ Box n H : DD(u_f) = concDDZ n (upperCoeffs n f) = 0}
        ≤ (n-1)·(4n-3)·(2n-1)·(2H+1)^(n-1)          (exact constant)

via `DoubleDisc.ddPoly_zero_box_ncard_le` (the `O(H^(n-2))` zero-set bound
for the fixed nonzero polynomial `DD` on the integer box of the upper
coefficients — this is where the geometric-sieve / Schwartz–Zippel bound of
`Commons.Algebra.MvPolynomial.zeroSet_ncard_le_box` enters) and the
`(u,c)`-parametrisation of the box by upper coefficients `u` and constant
coefficient `c` (`monicOfUpper_eq_self`, at most `2H+1` polynomials per `u`).

The bridge `concDDZ_eq_zero_iff_ddEvalInt` identifies the integer
`DD(u) = 0` with the ℚ-evaluation zero `(ddPoly n).eval (uQ u) = 0` counted
by `ddPoly_zero_box_ncard_le`.
-/

namespace Submission.Vdw

/-- Box polynomials whose double discriminant `DD(u_f)` vanishes: the
`DD(u) = 0` piece of Case III. -/
noncomputable def DDzeroBox (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ Box n H ∧ concDDZ n (upperCoeffs n f) = 0}

/-- The integer `DD(u)` vanishes iff the ℚ-evaluation of the generic
double discriminant `ddPoly` vanishes at the cast vector (the bridge between
`concDDZ` and the `ddPoly_zero_box_ncard_le` count). -/
lemma concDDZ_eq_zero_iff_ddEvalInt (n : ℕ) (hn : 2 ≤ n) (u : Fin (n - 1) → ℤ) :
    concDDZ n u = 0 ↔ ddEvalInt n u = 0 := by
  have hcast : concDDZ n u = 0 ↔ (concDDZ n u : ℚ) = 0 := by
    exact ⟨fun h => by rw [h]; norm_num, fun h => by exact_mod_cast h⟩
  calc
    concDDZ n u = 0 ↔ (concDDZ n u : ℚ) = 0 := hcast
    _ ↔ concDD n (uQ u) = 0 := by rw [concDDZ_cast_eq_concDD n hn u]
    _ ↔ ddEvalInt n u = 0 := by rw [ddEvalInt_eq_concDD n hn u]

/-- **The `DD(u_f) = 0` piece of Case III is `O(H^(n-1))`** — explicit
constant `(n-1)·(4n-3)·(2n-1)`.  Proof: the upper coefficient vectors `u`
with `DD(u) = 0` number `O(H^(n-2))` (`ddPoly_zero_box_ncard_le`, from the
Schwartz–Zippel/zero-set bound for the fixed nonzero polynomial `DD`), and
each `u` admits at most `(2H+1)` constant coefficients `c` (box
parametrisation `f = monicOfUpper n u c`). -/
theorem DDzeroBox_ncard_le (n H : ℕ) (hn : 3 ≤ n) :
    (DDzeroBox n H).ncard ≤ ((n - 1) * ((4 * n - 3) * (2 * n - 1))) * (2 * H + 1) ^ (n - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  let UZ : Set (Fin (n - 1) → ℤ) := {u | (∀ i, |u i| ≤ (H : ℤ)) ∧ concDDZ n u = 0}
  let A : Set (Fin (n - 1) → ℤ) := {u | (∀ i, |u i| ≤ (H : ℤ)) ∧ ddEvalInt n u = 0}
  -- upper box is finite
  have hUBfin : (upperBox n H).Finite := by
    let UBt : Type := {u : Fin (n - 1) → ℤ // u ∈ upperBox n H}
    haveI : Fintype UBt := Fintype.ofEquiv (Fin (n - 1) → BddInt H) (upperBoxEquiv n H).symm
    exact Set.toFinite (upperBox n H)
  have hUZsubUB : UZ ⊆ upperBox n H := by
    intro u hu
    exact hu.1
  have hUZfin : UZ.Finite := hUBfin.subset hUZsubUB
  have hAsubUB : A ⊆ upperBox n H := by
    intro u hu
    exact hu.1
  have hAfin : A.Finite := hUBfin.subset hAsubUB
  -- (1) UZ ⊆ A, so UZ is bounded by the ddPoly zero-set count
  have hUZA : UZ ⊆ A := by
    intro u hu
    exact ⟨hu.1, (concDDZ_eq_zero_iff_ddEvalInt n hn2 u).mp hu.2⟩
  have hUZle : UZ.ncard ≤ (n - 1) * ((4 * n - 3) * (2 * n - 1)) * (2 * H + 1) ^ (n - 2) := by
    exact le_trans (Set.ncard_le_ncard hUZA hAfin) (ddPoly_zero_box_ncard_le n H hn)
  -- (2) box polys with u_f ∈ UZ: ≤ #UZ · (2H+1) via (u, c)-parametrisation
  let UZt : Type := {u : Fin (n - 1) → ℤ // u ∈ UZ}
  haveI : Fintype UZt := hUZfin.fintype
  have hSle : (DDzeroBox n H).ncard ≤ Nat.card (Σ _u : UZt, BddInt H) := by
    let g : {f : ℤ[X] // f ∈ DDzeroBox n H} → Σ _u : UZt, BddInt H := fun f =>
      ⟨⟨upperCoeffs n f.1, ⟨upperCoeffs_bound f.2.1 hn1, f.2.2⟩⟩,
        ⟨f.1.coeff 0, coeff0_bound f.2.1 hn1⟩⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hux : ((g x).1).1 = ((g y).1).1 := congrArg (fun w : Σ _u : UZt, BddInt H => w.1.1) hxy
      have huc : upperCoeffs n x.1 = upperCoeffs n y.1 := by
        change ((g x).1).1 = ((g y).1).1
        exact hux
      have hcBdd : ((g x).2) = ((g y).2) := congrArg (fun w : Σ _u : UZt, BddInt H => w.2) hxy
      have hc0 : x.1.coeff 0 = y.1.coeff 0 := by
        have hc0' := congrArg (fun c : BddInt H => (c : ℤ)) hcBdd
        change ((g x).2 : ℤ) = ((g y).2 : ℤ) at hc0'
        change x.1.coeff 0 = y.1.coeff 0
        exact hc0'
      have hboxx : x.1 ∈ Box n H := x.2.1
      have hboxy : y.1 ∈ Box n H := y.2.1
      have hdegx : x.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hboxx.2.1
      have hdegy : y.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hboxy.2.1
      have hxe : monicOfUpper n (upperCoeffs n x.1) (x.1.coeff 0) = x.1 :=
        monicOfUpper_eq_self n hn1 x.1 hboxx.1 hdegx
      have hye : monicOfUpper n (upperCoeffs n y.1) (y.1.coeff 0) = y.1 :=
        monicOfUpper_eq_self n hn1 y.1 hboxy.1 hdegy
      calc
        x.1 = monicOfUpper n (upperCoeffs n x.1) (x.1.coeff 0) := hxe.symm
        _ = monicOfUpper n (upperCoeffs n y.1) (y.1.coeff 0) := by rw [huc, hc0]
        _ = y.1 := hye
    have hnc : (DDzeroBox n H).ncard = Nat.card {f : ℤ[X] // f ∈ DDzeroBox n H} :=
      (Nat.card_coe_set_eq (DDzeroBox n H)).symm
    rw [hnc]
    exact Nat.card_le_card_of_injective g hinj
  have hSig : Nat.card (Σ _u : UZt, BddInt H) = Fintype.card UZt * (2 * H + 1) := by
    calc
      Nat.card (Σ _u : UZt, BddInt H) = Fintype.card (Σ _u : UZt, BddInt H) := Nat.card_eq_fintype_card
      _ = ∑ _u : UZt, Fintype.card (BddInt H) := Fintype.card_sigma
      _ = Fintype.card UZt * Fintype.card (BddInt H) := by
        rw [Finset.sum_const]
        simp
      _ = Fintype.card UZt * (2 * H + 1) := by
        congr 1
        exact Nat.card_eq_fintype_card.symm.trans (bddInt_card H)
  have hUZcard : Fintype.card UZt = UZ.ncard := by
    calc
      Fintype.card UZt = Nat.card UZt := Nat.card_eq_fintype_card.symm
      _ = UZ.ncard := (ncard_eq_natCard UZ).symm
  calc
    (DDzeroBox n H).ncard ≤ Nat.card (Σ _u : UZt, BddInt H) := hSle
    _ = Fintype.card UZt * (2 * H + 1) := hSig
    _ = UZ.ncard * (2 * H + 1) := by rw [hUZcard]
    _ ≤ ((n - 1) * ((4 * n - 3) * (2 * n - 1))) * (2 * H + 1) ^ (n - 2) * (2 * H + 1) := by
      exact Nat.mul_le_mul_right (2 * H + 1) hUZle
    _ = ((n - 1) * ((4 * n - 3) * (2 * n - 1))) * ((2 * H + 1) ^ (n - 2) * (2 * H + 1)) := by
      rw [Nat.mul_assoc]
    _ = ((n - 1) * ((4 * n - 3) * (2 * n - 1))) * (2 * H + 1) ^ (n - 1) := by
      congr 1
      have hp : (2 * H + 1) ^ (n - 2) * (2 * H + 1) = (2 * H + 1) ^ (n - 1) := by
        rw [← pow_succ]
        congr 1
        omega
      exact hp

/-- **Big-O form:** the `DD(u_f) = 0` box count is `O(H^(n-1))`. -/
theorem DDzeroBox_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((DDzeroBox n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  let C : ℕ := (n - 1) * ((4 * n - 3) * (2 * n - 1))
  have hpoint : ∀ᶠ H : ℕ in atTop, (DDzeroBox n H).ncard ≤ (C * 3 ^ (n - 1)) * H ^ (n - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
    have hb := DDzeroBox_ncard_le n H hn
    calc
      (DDzeroBox n H).ncard ≤ C * (2 * H + 1) ^ (n - 1) := hb
      _ ≤ C * (3 * H) ^ (n - 1) := by
        exact Nat.mul_le_mul_left C (pow_le_pow_left₀ (by omega) (by omega) (n - 1))
      _ = (C * 3 ^ (n - 1)) * H ^ (n - 1) := by rw [mul_pow]; ring
  exact Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) (C * 3 ^ (n - 1))
    (fun H : ℕ => (DDzeroBox n H).ncard) hpoint

end Submission.Vdw
