/-
P1 (theorem_1_3): an explicit infinite family of primitive Descartes
quadruples of type (6,5,−1) residue pattern.

Family (t : ℕ):  a = −(24t+19), b = 24t+21, c = 8(6t+5)², d = c + 4.
Identities (v := 6t+5, |a| = 24t+19 = 4v−1, b = 4v+1):
  a + b = 2,  ab + (a+b)c = 1  ⇒  (with d = a + b + c + 2) the Descartes equation.
  a < 0 < b < c < d; sum = 2c + 6 > 0.
  a ≡ 5, b ≡ 21, c ≡ 8, d ≡ 12 (mod 24): values mod 24 ∈ {0,5,8,12,20,21},
  index parities odd-odd-even-even with odds ≡ 5 (mod 8), evens ≡ 0 (mod 4).
  gcd(a,b) = 1; anchor pairChi a b = −1 (both still to be added, see NOTES).
-/
import ChallengeDeps
import Submission.Apollo.KR
import Submission.Apollo.KsymTool
import Submission.Apollo.CLocal
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
open scoped NumberTheorySymbols
set_option autoImplicit false

open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- the four coordinate families. -/
def famA (t : ℕ) : ℤ := -(24 * (t : ℤ) + 19)
def famB (t : ℕ) : ℤ := 24 * (t : ℤ) + 21
def famC (t : ℕ) : ℤ := 8 * (6 * (t : ℤ) + 5) ^ 2
def famD (t : ℕ) : ℤ := famC t + 4

/-- the family quadruple. -/
def famQuad (t : ℕ) : Fin 4 → ℤ := ![famA t, famB t, famC t, famD t]

lemma famC_pos (t : ℕ) : 0 < famC t := by
  unfold famC
  positivity

lemma famA_lt_zero (t : ℕ) : famA t < 0 := by
  unfold famA
  omega

/-- the negative value's absolute value (as ℤ). -/
lemma famA_natAbs_z (t : ℕ) : ((famA t).natAbs : ℤ) = -(famA t) := by
  have hneg : famA t < 0 := famA_lt_zero t
  rcases Int.natAbs_eq (famA t) with hx | hx
  · exfalso
    omega
  · omega

/-- ordering of the coordinates. -/
lemma fam_lt (t : ℕ) : famA t < famB t ∧ famB t < famC t ∧ famC t < famD t := by
  constructor
  · unfold famA famB
    omega
  · constructor
    · unfold famB famC
      nlinarith [sq_nonneg ((t : ℤ))]
    · change famC t < famC t + 4
      omega

/-- sums of the family coordinates. -/
lemma fam_sum : ∀ (t : ℕ), (∑ i : Fin 4, famQuad t i) = famA t + famB t + famC t + famD t := by
  intro t
  rw [Fin.sum_univ_four]
  simp [famQuad]

/-- Descartes equation for the family. -/
theorem fam_descartes (t : ℕ) :
    (∑ i : Fin 4, famQuad t i) ^ 2 = 2 * ∑ i : Fin 4, (famQuad t i) ^ 2 := by
  simp only [Fin.sum_univ_four]
  simp [famQuad, famA, famB, famC, famD]
  ring_nf

/-- positive coordinate sum. -/
lemma fam_sum_pos (t : ℕ) : 0 < ∑ i : Fin 4, famQuad t i := by
  rw [fam_sum]
  simp [famA, famB, famC, famD]
  nlinarith [sq_nonneg (6 * (t : ℤ) + 5)]

/-- residues modulo 24 of the coordinates. -/
lemma famA_mod24 (t : ℕ) : famA t % 24 = 5 := by
  unfold famA
  omega

lemma famB_mod24 (t : ℕ) : famB t % 24 = 21 := by
  unfold famB
  omega

lemma famC_mod24 (t : ℕ) : famC t % 24 = 8 := by
  unfold famC
  have hq : 8 * (6 * (t : ℤ) + 5) ^ 2 = 24 * (12 * (t : ℤ) ^ 2 + 20 * (t : ℤ) + 8) + 8 := by ring
  rw [hq]
  omega

lemma famD_mod24 (t : ℕ) : famD t % 24 = 12 := by
  unfold famD famC
  have hq : 8 * (6 * (t : ℤ) + 5) ^ 2 + 4 = 24 * (12 * (t : ℤ) ^ 2 + 20 * (t : ℤ) + 8) + 12 := by ring
  rw [hq]
  omega

/-- values lie in the admissible set {0,5,8,12,20,21} mod 24 (type (6,5)). -/
lemma fam_values_admissible (t : ℕ) (i : Fin 4) :
    famQuad t i % 24 = 0 ∨ famQuad t i % 24 = 5 ∨ famQuad t i % 24 = 8 ∨
      famQuad t i % 24 = 12 ∨ famQuad t i % 24 = 20 ∨ famQuad t i % 24 = 21 := by
  fin_cases i <;> simp [famQuad, famA_mod24 t, famB_mod24 t, famC_mod24 t, famD_mod24 t]

/-- odds ≡ 5 mod 8 at indices 0,1; evens ≡ 0 mod 4 at indices 2,3. -/
lemma fam_parity (t : ℕ) :
    (famQuad t 0) % 8 = 5 ∧ (famQuad t 1) % 8 = 5 ∧
      (famQuad t 2) % 4 = 0 ∧ (famQuad t 3) % 4 = 0 := by
  simp [famQuad]
  constructor
  · have hq : famA t = 8 * (-3 * (t : ℤ) - 3) + 5 := by unfold famA; ring
    omega
  · constructor
    · have hq : famB t = 8 * (3 * (t : ℤ) + 2) + 5 := by unfold famB; ring
      omega
    · constructor
      · have hq : famC t = 4 * (2 * (6 * (t : ℤ) + 5) ^ 2) := by unfold famC; ring
        omega
      · have hq : famD t = 4 * (2 * (6 * (t : ℤ) + 5) ^ 2 + 1) := by unfold famD famC; ring
        omega


/-- |famA| as a natural. -/
lemma famA_natAbs (t : ℕ) : (famA t).natAbs = 24 * t + 19 := by
  unfold famA
  have hc : (-(24 * (t : ℤ) + 19)) = -((24 * t + 19 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hc, Int.natAbs_neg, Int.natAbs_natCast]

/-- |famB| as a natural. -/
lemma famB_natAbs (t : ℕ) : (famB t).natAbs = 24 * t + 21 := by
  unfold famB
  have hc : (24 * (t : ℤ) + 21) = ((24 * t + 21 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hc, Int.natAbs_natCast]



/-- gcd of the odd |famA| with 2 is 1. -/
private lemma famA_abs_gcd_two (t : ℕ) : Nat.gcd (24 * t + 19) 2 = 1 := by
  have hodd : Odd (24 * t + 19) := by rw [Nat.odd_iff]; omega
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  rw [Nat.gcd_comm, Nat.gcd_rec]
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  rw [hmod]
  norm_num

/-- gcd of the two odd coordinates. -/
private lemma nat_pair_gcd (t : ℕ) : Nat.gcd (24 * t + 19) (24 * t + 21) = 1 := by
  apply Nat.dvd_antisymm
  · have hg12 : Nat.gcd (24 * t + 19) (24 * t + 21) ∣ Nat.gcd (24 * t + 19) 2 := by
      apply Nat.dvd_gcd (k := Nat.gcd (24 * t + 19) (24 * t + 21))
        (m := 24 * t + 19) (n := 2)
      · exact Nat.gcd_dvd_left (24 * t + 19) (24 * t + 21)
      · have hg2 := Nat.gcd_dvd_right (24 * t + 19) (24 * t + 21)
        have hsub : Nat.gcd (24 * t + 19) (24 * t + 21) ∣ (24 * t + 21) - (24 * t + 19) :=
          Nat.dvd_sub (k := Nat.gcd (24 * t + 19) (24 * t + 21))
            (m := 24 * t + 21) (n := 24 * t + 19) hg2
            (Nat.gcd_dvd_left (24 * t + 19) (24 * t + 21))
        have heq : (24 * t + 21) - (24 * t + 19) = 2 := by omega
        rwa [heq] at hsub
    rwa [famA_abs_gcd_two t] at hg12
  · exact one_dvd _

/-- the odd pair (a,b) is coprime. -/
lemma famAB_gcd_one (t : ℕ) : (famA t).gcd (famB t) = 1 := by
  rw [Int.gcd_eq_natAbs]
  rw [famA_natAbs, famB_natAbs]
  exact nat_pair_gcd t

/-- the odd pair is coprime in the ℤ GCD-monoid (as used by Finset.gcd). -/
lemma famAB_gcdMonoid_one (t : ℕ) : GCDMonoid.gcd (famA t) (famB t) = (1 : ℤ) := by
  change ((famA t).gcd (famB t) : ℤ) = (1 : ℤ)
  rw [famAB_gcd_one]
  norm_num

/-- the base odd pair has χ₂ = −1 (the anchor for the whole family). -/
theorem fam_anchor (t : ℕ) : pairChi (famA t) (famB t) = -1 := by
  have hodd : Odd (24 * t + 19) := by rw [Nat.odd_iff]; omega
  have hn : (24 * (t : ℤ) + 19).natAbs = 24 * t + 19 := by
    have hc : (24 * (t : ℤ) + 19) = ((24 * t + 19 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hc, Int.natAbs_natCast]
  have hg : (famB t).gcd (24 * t + 19) = 1 := by
    rw [Int.gcd_eq_natAbs]
    rw [famB_natAbs, hn]
    rw [Nat.gcd_comm]
    exact nat_pair_gcd t
  have hg2 : (2 : ℤ).gcd (24 * t + 19) = 1 := by
    rw [Int.gcd_eq_natAbs]
    have h2 : (2 : ℤ).natAbs = 2 := by norm_num
    rw [h2]
    rw [Nat.gcd_comm]
    exact famA_abs_gcd_two t
  have hdiv : ((24 * t + 19 : ℕ) : ℤ) ∣ famB t - 2 := by
    refine ⟨1, ?_⟩
    unfold famB
    push_cast
    ring
  have hnum : ksym (famB t) (24 * t + 19) = ksym 2 (24 * t + 19) :=
    ksym_numred (c := famB t) (c' := 2) (m := 24 * t + 19) (Or.inl (Nat.not_even_iff_odd.mpr hodd))
      hg hg2 hdiv
  calc
    pairChi (famA t) (famB t) = ksym (famB t) (24 * t + 19) := by
      unfold pairChi
      rw [famA_natAbs]
    _ = jacobiSym (famB t) (24 * t + 19) := ksym_odd (famB t) hodd
    _ = jacobiSym 2 (24 * t + 19) := by
      rw [← ksym_odd (famB t) hodd, hnum, ksym_odd 2 hodd]
    _ = -1 := by
      have h8 : (24 * t + 19) % 8 = 3 := by omega
      exact Commons.NumberTheory.JacobiSymbol.two_neg_of_mod8_three_five (Or.inl h8)



/-- gcd with 1 in the ℤ GCD-monoid is 1. -/
private lemma gcdMonoid_one_left (a : ℤ) : GCDMonoid.gcd 1 a = (1 : ℤ) := by
  change ((1 : ℤ).gcd a : ℤ) = 1
  rw [Int.gcd_eq_natAbs]
  norm_num

/-- the family quadruple is primitive: the gcd of all four coordinates is 1. -/
lemma fam_univ_gcd_one (t : ℕ) : Finset.univ.gcd (famQuad t) = (1 : ℤ) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp
  rw [huniv]
  simp only [Finset.gcd_insert, Finset.gcd_singleton]
  simp [famQuad]
  have hd : 0 ≤ famD t := by
    unfold famD
    have hc : 0 ≤ famC t := le_of_lt (famC_pos t)
    omega
  rw [Int.normalize_of_nonneg hd]
  rw [← gcd_assoc]
  rw [famAB_gcdMonoid_one]
  exact gcdMonoid_one_left (GCDMonoid.gcd (famC t) (famD t))



/-- the family quadruple is an integral primitive Descartes quadruple. -/
lemma famQuad_mem (t : ℕ) : famQuad t ∈ integralPrimitiveDescartesQuadruple := by
  rw [mem_integralPrimitiveDescartesQuadruple_iff]
  exact ⟨fam_sum_pos t, fam_descartes t, fam_univ_gcd_one t⟩



/-- the base negative value sits at index 0. -/
lemma famQuad_zero (t : ℕ) : famQuad t 0 = famA t := by
  simp [famQuad]

/-- base case of the minimum invariant: every coordinate of the root-form
quadruple is ≥ famA t (with equality at index 0). -/
lemma fam_coords_ge_a (t : ℕ) (j : Fin 4) : famA t ≤ famQuad t j := by
  fin_cases j
  · simp [famQuad]
  · simp [famQuad]
    unfold famA famB
    omega
  · simp [famQuad]
    have hneg : famA t < 0 := famA_lt_zero t
    have hpos : 0 ≤ famC t := le_of_lt (famC_pos t)
    omega
  · simp [famQuad]
    unfold famD
    have hneg : famA t < 0 := famA_lt_zero t
    have hpos : 0 ≤ famC t := le_of_lt (famC_pos t)
    omega

end Apollo
