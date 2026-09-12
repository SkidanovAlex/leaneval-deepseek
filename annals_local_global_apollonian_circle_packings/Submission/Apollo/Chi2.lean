/-
L4 core, STEP 1: χ₂ well-definedness within a single Descartes quadruple.

For a circle occurrence o and two coprime tangent partners p, q that
co-occur with o in one Descartes quadruple, the two χ₂ comparisons agree
(`chi2_inQuad_occ`).  The proof runs inside the quadruple w ∈ apOrbit:
  * the Descartes equation is expanded at the four pairwise-distinct indices
    (`descartes_fourterm`);
  * if the circle's value is odd, Partner.pairChi_partner_consistency_odd
    applies directly;
  * if the circle's value is even, its coprime partners are odd, hence at
    indices 0 or 1 (Parity.coord_odd_iff), hence ≡ 5 mod 8
    (Parity.orbit_odd_coord_eq_five_mod8), giving the mod-8 hypothesis of
    PartnerEven.pairChi_partner_consistency.
This is the first brick of the well-definedness theorem chi2_wellDefined (see
NOTES); the remaining steps (ring transfer around the circle, R2 gaps) are
documented there.
-/
import Submission.Apollo.OrbitFacts
import Submission.Apollo.Partner
import Submission.Apollo.PartnerEven
import Submission.Apollo.MoveStep
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo


/-- the Descartes equation of an orbit quadruple, expanded at four pairwise
distinct indices. -/
theorem descartes_fourterm (w : Fin 4 → ℤ) (hw : w ∈ apOrbit)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (w i + w j + w k + w l) ^ 2 = 2 * ((w i) ^ 2 + (w j) ^ 2 + (w k) ^ 2 + (w l) ^ 2) := by
  have hD := apOrbit_descarates w hw
  have hcard : ({i, j, k, l} : Finset (Fin 4)).card = Fintype.card (Fin 4) := by
    rw [Fintype.card_fin]
    simp [hij, hik, hil, hjk, hjl, hkl]
  have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hs1 : (∑ x ∈ ({i, j, k, l} : Finset (Fin 4)), w x) =
      w i + w j + w k + w l := by
    simp [hij, hik, hil, hjk, hjl, hkl]
    ring
  have hs2 : (∑ x ∈ ({i, j, k, l} : Finset (Fin 4)), (w x) ^ 2) =
      (w i) ^ 2 + (w j) ^ 2 + (w k) ^ 2 + (w l) ^ 2 := by
    simp [hij, hik, hil, hjk, hjl, hkl]
    ring
  rw [← huniv] at hD
  rw [hs1, hs2] at hD
  ring_nf at hD ⊢
  exact hD

/-- χ₂ well-definedness within one Descartes quadruple (STEP 1): a circle and
two coprime tangent partners that co-occur in one quadruple give the same χ₂.
Odd-circle case is direct (no mod-8 condition); even-circle partners are odd,
hence ≡ 5 mod 8. -/
theorem chi2_inQuad (w : Fin 4 → ℤ) (hw : w ∈ apOrbit)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hcopj : (w j).gcd (w i) = 1) (hcopk : (w k).gcd (w i) = 1) :
    pairChi (w i) (w j) = pairChi (w i) (w k) := by
  have hD4 := descartes_fourterm w hw (i := i) (j := j) (k := k) (l := l) hij hik hil hjk hjl hkl
  by_cases hodd : ¬ 2 ∣ w i
  · exact pairChi_partner_consistency_odd (x := w i) (y₁ := w j) (y₂ := w k) (z := w l)
      hD4 hodd hcopj hcopk
  · -- w i is even: the coprime partners are odd, hence at indices 0 or 1,
    -- hence ≡ 5 mod 8:
    have heven : 2 ∣ w i := by
      by_contra h
      exact hodd h
    have hjo : w j % 2 = 1 := odd_mod_of_coprime_even heven hcopj
    have hko : w k % 2 = 1 := odd_mod_of_coprime_even heven hcopk
    have hjodd : ¬ 2 ∣ w j := not_even_of_emod_two hjo
    have hkodd : ¬ 2 ∣ w k := not_even_of_emod_two hko
    have hjin : j = 0 ∨ j = 1 := (coord_odd_iff w hw j).1 hjodd
    have hkin : k = 0 ∨ k = 1 := (coord_odd_iff w hw k).1 hkodd
    have hj5 : w j % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw j hjin
    have hk5 : w k % 8 = 5 := orbit_odd_coord_eq_five_mod8 w hw k hkin
    have h8 : w j % 8 = w k % 8 := by rw [hj5, hk5]
    exact pairChi_partner_consistency (x := w i) (y₁ := w j) (y₂ := w k) (z := w l)
      hD4 hcopj hcopk h8

/-- occurrence-level STEP 1: for a circle occurrence o and two coprime tangent
partners p, q that co-occur with o (and a leftover occurrence r completing the
Descartes quadruple), the two χ₂ comparisons agree. -/
theorem chi2_inQuad_occ (o p q r : Occ) (ho : valid o)
    (htop : tangent o p) (htoq : tangent o q) (htor : tangent o r)
    (hop : o.2 ≠ p.2) (hoq : o.2 ≠ q.2) (hor : o.2 ≠ r.2)
    (hpr : p.2 ≠ r.2) (hqr : q.2 ≠ r.2) (hpq : p.2 ≠ q.2)
    (hcop_p : coprimeValues o p) (hcop_q : coprimeValues o q) :
    pairChi (ovalue o) (ovalue p) = pairChi (ovalue o) (ovalue q) := by
  let w : Fin 4 → ℤ := o.1
  have hw : w ∈ apOrbit := by simpa [w, valid] using ho
  -- o, p, q, r have the same quadruple w:
  have hwp : p.1 = w := by
    rcases htop with ⟨h, _⟩
    simpa [w] using h.symm
  have hwq : q.1 = w := by
    rcases htoq with ⟨h, _⟩
    simpa [w] using h.symm
  have hwr : r.1 = w := by
    rcases htor with ⟨h, _⟩
    simpa [w] using h.symm
  have hcopj : (w (p.2)).gcd (w (o.2)) = 1 := by
    dsimp [coprimeValues] at hcop_p
    rw [Int.gcd_comm]
    simpa [ovalue, hwp] using hcop_p
  have hcopk : (w (q.2)).gcd (w (o.2)) = 1 := by
    dsimp [coprimeValues] at hcop_q
    rw [Int.gcd_comm]
    simpa [ovalue, hwq] using hcop_q
  have hmain := chi2_inQuad w hw
    (i := o.2) (j := p.2) (k := q.2) (l := r.2) hop hoq hor hpq hpr hqr
    hcopj hcopk
  -- translate the coordinate statement back to occurrences:
  simpa [ovalue, hwp, hwq] using hmain


end Apollo
