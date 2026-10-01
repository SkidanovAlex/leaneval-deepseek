import Mathlib
import Submission.Work.LinnikBurgess.singleton_defs
import Submission.Work.LinnikBurgess.DdBits

/-! Definitions for the Burgess route (`BURGESS_ROUTE_LEAD.md`, unit U1). -/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

/-- `e_1, e_2, e_3` of a triple, as integers (`∏ (X + a_l) = X^3 + e₁X² + e₂X + e₃`). -/
def esymm3 (a : Fin 3 → ℕ) : Fin 3 → ℤ :=
  ![(a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ),
    (a 0 : ℤ) * (a 1 : ℤ) + (a 0 : ℤ) * (a 2 : ℤ) + (a 1 : ℤ) * (a 2 : ℤ),
    (a 0 : ℤ) * (a 1 : ℤ) * (a 2 : ℤ)]

/-- The content `gcd_k |e_k(a) - e_k(b)|`. -/
def contAB (a b : Fin 3 → ℕ) : ℕ :=
  Nat.gcd (esymm3 a 0 - esymm3 b 0).natAbs
    (Nat.gcd (esymm3 a 1 - esymm3 b 1).natAbs (esymm3 a 2 - esymm3 b 2).natAbs)

noncomputable def cubicZ (a : Fin 3 → ℕ) : ℤ[X] := ∏ l : Fin 3, (X + C ((a l : ℕ) : ℤ))

/-- The critical (Wronskian) polynomial `N = f_a' f_b - f_a f_b'`. -/
noncomputable def critN (a b : Fin 3 → ℕ) : ℤ[X] :=
  derivative (cubicZ a) * cubicZ b - cubicZ a * derivative (cubicZ b)

def UnitAt (p y : ℕ) (a b : Fin 3 → ℕ) : Prop := ∀ l : Fin 3, ¬ p ∣ y + a l ∧ ¬ p ∣ y + b l

/-- Double-critical level `≥ s` at the prime `p`. -/
def DLp (p s : ℕ) (a b : Fin 3 → ℕ) : Prop :=
  ∃ y : ℕ, UnitAt p y a b ∧ ((p ^ s : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)
    ∧ ((p ^ s : ℕ) : ℤ) ∣ (derivative (critN a b)).eval (y : ℤ)

/-- Double-critical modulo `d` (one witness for all primes of `d`). -/
def DLd (d : ℕ) (a b : Fin 3 → ℕ) : Prop :=
  ∃ y : ℕ, (∀ p ∈ d.primeFactors, UnitAt p y a b) ∧ (d : ℤ) ∣ (critN a b).eval (y : ℤ)
    ∧ (d : ℤ) ∣ (derivative (critN a b)).eval (y : ℤ)

noncomputable def vcap (p K x : ℕ) : ℕ := if x = 0 then K else min (padicValNat p x) K

noncomputable def defect1 (p e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) : ZMod (p ^ e) :=
  (∑ l : Fin 3, (((y + a l : ℕ) : ZMod (p ^ e)))⁻¹)
    - ∑ l : Fin 3, (((y + b l : ℕ) : ZMod (p ^ e)))⁻¹

noncomputable def defect2 (p e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) : ZMod (p ^ e) :=
  (∑ l : Fin 3, ((((y + a l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
    - ∑ l : Fin 3, ((((y + b l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2

def cubeLevel (p e : ℕ) : ℕ := if p = 2 then (e + 3) / 3 else (e + 2) / 3
def capLevel (p e : ℕ) : ℕ := e - 2 * cubeLevel p e

noncomputable def menuW (p e s j : ℕ) : ℝ :=
  let m := cubeLevel p e
  let T := capLevel p e
  if 5 ≤ p then
    (if j = 0 then
        (if s < T then 4 * (p : ℝ) ^ ((s : ℝ) / 2)
         else if s = T then 7 * (p : ℝ) ^ ((T : ℝ) / 2)
         else if s = T + 1 then 60 * (p : ℝ) ^ ((e : ℝ) / 6) else 0)
     else if s = max T j then 7 * ((e : ℝ) + 1) * (p : ℝ) ^ (((m : ℝ) + j) / 2) else 0)
  else if e ≤ 12 then (if s = 0 ∧ j = 0 then 729 else 0)
  else (if j = 0 ∧ s ≤ T then 10 ^ 6 * (p : ℝ) ^ ((s : ℝ) / 2) else 0)
       + (if s = max T j then 10 ^ 6 * (p : ℝ) ^ (((m : ℝ) + j) / 2) else 0)

noncomputable def localFactor (p e : ℕ) (a b : Fin 3 → ℕ) : ℝ :=
  ∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1),
    menuW p e s j * (if DLp p s a b ∧ p ^ j ∣ contAB a b then 1 else 0)

/-- `∏_{l ≠ i} √gcd(m, |v_i - v_l|)`. -/
noncomputable def sqrtGcdW (m : ℕ) (i : Fin 6) (v : Fin 6 → ℕ) : ℝ :=
  ∏ l ∈ Finset.univ.erase i, Real.sqrt ((Nat.gcd m ((v i : ℤ) - (v l : ℤ)).natAbs : ℕ) : ℝ)

def aOf {H : ℕ} (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Fin 3 → ℕ := fun l => (fg.1 l : ℕ) + 1
def bOf {H : ℕ} (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Fin 3 → ℕ := fun l => (fg.2 l : ℕ) + 1

end Work.LinnikBurgess

namespace Work.LinnikBurgess

open Classical

/-- Right-hand side of Lemma A (U2): the two-digit Gauss-sum weight sum over `y < p^m`. -/
noncomputable def gaussTwoRHS (p e m : ℕ) (a b : Fin 3 → ℕ) : ℝ := by
  classical
  exact ∑ y ∈ Finset.range (p ^ m),
    (if UnitAt p y a b
        ∧ p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val) ∣ (defect1 p e a b y).val
     then (p : ℝ) ^ ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℝ) / 2) else 0)

/-- Right-hand side of Lemma A₂ (U3), the 2-adic version. -/
noncomputable def gaussTwoRHS2 (e m : ℕ) (a b : Fin 3 → ℕ) : ℝ := by
  classical
  exact ∑ y ∈ Finset.range (2 ^ m),
    (if UnitAt 2 y a b
        ∧ 2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1) ∣ (defect1 2 e a b y).val
     then (2 : ℝ) ^ ((vcap 2 (e - 2 * m) (defect2 2 e a b y).val : ℝ) / 2) else 0)

/-- The Hensel set of U5 (a filtered initial segment of `ℕ`). -/
noncomputable def henselSet (p : ℕ) (P : Polynomial ℤ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (p ^ M)).filter (fun y : ℕ =>
      ∃ ν : ℕ, ((p ^ ν : ℕ) : ℤ) ∣ (Polynomial.derivative P).eval (y : ℤ)
        ∧ ¬ ((p ^ (ν + 1) : ℕ) : ℤ) ∣ (Polynomial.derivative P).eval (y : ℤ)
        ∧ ((p ^ (max (2 * ν + 1) (M + ν)) : ℕ) : ℤ) ∣ P.eval (y : ℤ))

end Work.LinnikBurgess

namespace Work.LinnikBurgess

open Classical

/-- The indicator weight of Theorem F (U11). -/
noncomputable def frameW {H : ℕ} (d g : ℕ) (fg : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : ℝ := by
  classical
  exact if DLd d (aOf fg) (bOf fg) ∧ g ∣ contAB (aOf fg) (bOf fg) then 1 else 0

end Work.LinnikBurgess
