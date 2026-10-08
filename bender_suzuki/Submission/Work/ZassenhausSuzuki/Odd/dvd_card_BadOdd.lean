import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddFib
import Submission.Work.ZassenhausSuzuki.Odd.OddCore
import Submission.Work.ZassenhausSuzuki.Odd.OddData
import Submission.Work.ZassenhausSuzuki.Odd.coprime_centralizer_BadOdd
import Submission.Work.ZassenhausSuzuki.Odd.twoPoint_isCZ
import Submission.Work.ZassenhausSuzuki.Odd.dvd_card_of_conj_invariant
import Submission.Work.ZassenhausSuzuki.Odd.badOdd_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.dvd_card_BadOdd`

The number of "bad" odd-order elements (`BadOdd`: odd order, `≠ 1`, not strongly real) is
divisible by `(q - 1) q² a` for every order `a` of an `ℱ`-subgroup different from `q - 1`.

The argument is the class-equation argument of Suzuki 1962 §10 as used by the numerical endgame
of `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`: `BadOdd` is invariant under
conjugation, i.e. it is a union of conjugacy classes, and the conjugacy class of a bad element
`y` has cardinality

`|G| / |C_G(y)| = q² (q - 1) (q² + 1) / |C_G(y)|`.

Both `q²` and `q - 1` divide that cardinality:

* `|C_G(y)|` is odd (`odd_centralizer_odd`), so `|C_G(y)|` is coprime to the `2`-power `q²`;
* `|C_G(y)|` is coprime to `|twoPoint H t| = q - 1` (`coprime_centralizer_BadOdd`, applied to
  the `ℱ`-subgroup `twoPoint H t`, which is a member of `ℱ` by `twoPoint_isCZ`).

Moreover `a = |A|` for an `ℱ`-subgroup `A` divides the class size as well, since `a ∣ |G|`
(Lagrange) and `a` is coprime to `|C_G(y)|` (`coprime_centralizer_BadOdd`).  Finally `a` is
coprime to `q (q - 1)` when `a ≠ q - 1` (`coprime_of_mem_Vals`), so the product
`(q - 1) q² a` divides every bad class size, hence their sum, which is `|BadOdd|`.

The reduction from "every bad conjugacy class has cardinality divisible by `N`" to
"`N ∣ |BadOdd|`" is the general class-equation lemma
`Work.ZassenhausSuzuki.Odd.dvd_card_of_conj_invariant` of the sibling module
`Submission.Work.ZassenhausSuzuki.Odd.dvd_card_of_conj_invariant`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## The cardinality of a conjugacy class -/

/-- Orbit–stabiliser for the conjugation action: the cardinality of the conjugacy class of `y`
times the order of the centraliser of `y` is `|G|`. -/
private theorem card_carrier_mul_card_centralizer (y : G) :
    Nat.card ↥(ConjClasses.carrier (ConjClasses.mk y)) *
      Nat.card ↥(Subgroup.centralizer ({y} : Set G)) = Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hOS : Nat.card ↥(MulAction.orbit (ConjAct G) y) *
      Nat.card ↥(MulAction.stabilizer (ConjAct G) y) = Nat.card G := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) y
  have hcar : Nat.card ↥(ConjClasses.carrier (ConjClasses.mk y)) =
      Nat.card ↥(MulAction.orbit (ConjAct G) y) :=
    Nat.card_congr ((ConjAct.orbit_eq_carrier_conjClasses y).symm ▸ Equiv.refl _)
  have hstab : Nat.card ↥(MulAction.stabilizer (ConjAct G) y) =
      Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
    rw [show Nat.card ↥(MulAction.stabilizer (ConjAct G) y) =
        Nat.card ↥(Subgroup.centralizer ({ConjAct.toConjAct y} : Set (ConjAct G))) from
      Nat.card_congr ((ConjAct.stabilizer_eq_centralizer y) ▸ Equiv.refl _)]
    rfl
  rw [hcar, ← hstab]
  exact hOS

/-! ## Coprimality of the relevant integers -/

/-- An order `a` occurring in `ℱ` with `a ≠ q - 1` is coprime to `q² (q - 1)`: it is odd (so
coprime to the `2`-power `q²`) and coprime to `q - 1` (`coprime_of_mem_Vals`). -/
private theorem coprime_Vals_card_G (h : SzOddHyp H Q t) {a : ℕ} (ha : a ∈ Vals G)
    (hane : a ≠ q H - 1) : Nat.Coprime a ((q H) ^ 2 * (q H - 1)) := by
  have h1 : Nat.Coprime a (q H * (q H - 1)) := coprime_of_mem_Vals h ha hane
  have hq : Nat.Coprime a (q H) := h1.coprime_dvd_right (dvd_mul_right (q H) (q H - 1))
  have hq1 : Nat.Coprime a (q H - 1) := h1.coprime_dvd_right (dvd_mul_left (q H - 1) (q H))
  exact (hq.pow_right 2).mul_right hq1

/-- The centraliser of a bad odd element has order coprime to `q² (q - 1)`: it is odd
(`odd_centralizer_odd`, so coprime to the `2`-power `q²`) and coprime to `|twoPoint H t| = q - 1`
(`coprime_centralizer_BadOdd`, since `twoPoint H t ∈ ℱ` by `twoPoint_isCZ`). -/
private theorem coprime_centralizer_BadOdd_card_G (h : SzOddHyp H Q t) {y : G}
    (hy : BadOdd y) :
    Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({y} : Set G)))
      ((q H) ^ 2 * (q H - 1)) := by
  set c : ℕ := Nat.card ↥(Subgroup.centralizer ({y} : Set G)) with hc
  have hodd : Odd c := odd_centralizer_odd h hy.2.1 hy.1
  obtain ⟨l, hl⟩ := (q_structure h).2.2.2.1
  have hq : Nat.Coprime c (q H) := by
    rw [hl]
    exact Nat.Coprime.pow_right l (Nat.coprime_two_right.mpr hodd)
  have hq1 : Nat.Coprime c (q H - 1) := by
    obtain ⟨hDCZ, hDcard, -, -⟩ := twoPoint_isCZ h
    rw [← hDcard]
    exact coprime_centralizer_BadOdd h hy hDCZ
  exact (hq.pow_right 2).mul_right hq1

/-! ## The arithmetic of the class sizes -/

/-- Elementary arithmetic: if `cls * c = q² (q - 1) (q² + 1)` with `c` coprime to `q² (q - 1)`,
`a` coprime to `q² (q - 1)`, `c` coprime to `a`, and `a ∣ q² (q - 1) (q² + 1)`, then
`(q - 1) q² a ∣ cls`. -/
private theorem dvd_classSize {q a cls c : ℕ}
    (hG : cls * c = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hcop1 : Nat.Coprime c (q ^ 2 * (q - 1)))
    (hcop2 : Nat.Coprime a (q ^ 2 * (q - 1)))
    (hcopa : Nat.Coprime c a)
    (hadvd : a ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1)) :
    (q - 1) * q ^ 2 * a ∣ cls := by
  have h1 : q ^ 2 * (q - 1) ∣ cls :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop1.symm (by rw [hG]; exact dvd_mul_right _ _)
  have h2 : a ∣ cls :=
    Nat.Coprime.dvd_of_dvd_mul_right hcopa.symm (by rw [hG]; exact hadvd)
  have h3 : a * (q ^ 2 * (q - 1)) ∣ cls := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop2 h2 h1
  rwa [show a * (q ^ 2 * (q - 1)) = (q - 1) * q ^ 2 * a from by ring] at h3

/-! ## The main theorem -/

theorem dvd_card_BadOdd (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) {a : ℕ}
    (ha : a ∈ Work.ZassenhausSuzuki.Odd.Vals G)
    (hane : a ≠ Work.ZassenhausSuzuki.Odd.q H - 1) :
    (Work.ZassenhausSuzuki.Odd.q H - 1) * (Work.ZassenhausSuzuki.Odd.q H) ^ 2 * a
      ∣ Nat.card {y : G // Work.ZassenhausSuzuki.Odd.BadOdd y} := by
  classical
  obtain ⟨A, hAmem, hAcard⟩ := mem_Vals.mp ha
  have hA : IsCZ A := mem_FinsetCZ.mp hAmem
  -- every bad conjugacy class has cardinality divisible by `(q - 1) q² a`
  refine dvd_card_of_conj_invariant ((q H - 1) * (q H) ^ 2 * a) {y : G | BadOdd y} ?_ ?_
  · intro g y hy
    exact badOdd_conj hy
  · intro y hy
    have hcls : Nat.card ↥(ConjClasses.carrier (ConjClasses.mk y)) *
        Nat.card ↥(Subgroup.centralizer ({y} : Set G))
          = (q H) ^ 2 * (q H - 1) * ((q H) ^ 2 + 1) :=
      (card_carrier_mul_card_centralizer y).trans (card_G_eq h)
    have hcopa : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({y} : Set G))) a := by
      rw [← hAcard]
      exact coprime_centralizer_BadOdd h hy hA
    have hadvd : a ∣ (q H) ^ 2 * (q H - 1) * ((q H) ^ 2 + 1) := by
      rw [← hAcard, ← card_G_eq h]
      exact Subgroup.card_subgroup_dvd_card A
    exact dvd_classSize (q := q H) (a := a) hcls
      (coprime_centralizer_BadOdd_card_G h hy) (coprime_Vals_card_G h ha hane) hcopa hadvd

end Work.ZassenhausSuzuki.Odd
