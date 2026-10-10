import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV5.haRoot
import Submission.Work.MotV5.ordOfPlace_api
import Submission.Work.MotV5.placeVal_valuation
import Submission.Work.MotV5.infPlace_ratPlace
import Submission.Work.MotV5.classification_ratPlace
import Submission.Work.MotV5.affPlace_deriv_bound
import Submission.Work.MotV5.infPlace_deriv_bound
import Submission.Work.MotV5.exists_invariantDeriv
import Submission.Work.MotV5.ker_deriv_fifthpowers
import Submission.Work.MotV5.invDeriv_genX_ne_zero
import Submission.Work.MotV5.aeval_order_pole
import Submission.Work.MotV5.deriv_pole_pos
import Submission.Work.MotV5.integral_everywhere_constant
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The main argument of `Work.MotV5.hurwitz_AS`

Let `E` be an elliptic curve over an algebraically closed field `N` of characteristic `5`, `A` a
polynomial of degree `≥ 2` with `5 ∤ deg A`, and `r ∈ N(E)` an element satisfying the
Artin–Schreier solvability condition `Hyp E A r` at its poles.  The main theorem of this file
(`hurwitz_AS_main`) is that `r` is then constant.

Route.  Let `D` be the invariant derivation of `N(E)`.  Suppose `r` is non-constant.  By
`integral_everywhere_constant` there is a place `S` at which `r` has a pole.
* If `D r ≠ 0` then `D r` is regular at every place: at a pole `Q` of `r` this is
  `deriv_pole_pos` (the Artin–Schreier condition forces `ord_Q (D r) ≥ 2`, by applying `D` to
  `A(r) - (u ^ 5 - u) ∈ O_Q`), and elsewhere it follows because `D` preserves the local rings
  (`deriv_mem_of_mem`).  So `D r = c` is constant, and `0 < ord_Q (D r) = ord_Q c = 0` is absurd.
* If `D r = 0` then `r = ρ ^ 5` (`ker_deriv_fifthpowers`) and the Artin–Schreier condition descends
  to `ρ` with the coefficientwise fifth root of `A` (`hyp_descend`); the pole order at `S` is
  divided by `5`, so the descent terminates, and the first case applies to `ρ`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV5

noncomputable section

variable {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]

/-- The order of a power. -/
theorem ordOfPlace_pow (E : WeierstrassCurve N)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    {g : MotC2.Func E} (hg : g ≠ 0) (k : ℕ) :
    MotV.ordOfPlace E S hS (g ^ k) = k * MotV.ordOfPlace E S hS g := by
  have hone : MotV.ordOfPlace E S hS (1 : MotC2.Func E) = 0 := by
    have := (ordOfPlace_api E S hS).2.2.2.2.2.1 (1 : N) one_ne_zero
    simpa using this
  induction k with
  | zero => simpa using hone
  | succ k ih =>
      rw [pow_succ, (ordOfPlace_api E S hS).1 _ _ (pow_ne_zero _ hg) hg, ih]
      push_cast
      first | refl_ring1 | ring

/-- The invariant derivation preserves the local ring of every rational place. -/
theorem deriv_mem_of_mem (E : WeierstrassCurve N) [E.IsElliptic]
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₃)
    (hDy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) {g : MotC2.Func E}
    (hg : g ∈ S) : D g ∈ S := by
  rcases classification_ratPlace E S hS with h | ⟨a, b, hns, h⟩
  · subst h
    exact (infPlace_deriv_bound E (infPlace_ratPlace E) D hDx hDy).1 g hg
  · subst h
    exact (affPlace_deriv_bound E a b hns D hDx hDy).1 g hg

/-- The invariant derivation lowers the order at a pole by at most one. -/
theorem deriv_bound_general (E : WeierstrassCurve N) [E.IsElliptic]
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₃)
    (hDy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (g : MotC2.Func E)
    (hg : g ∉ S) :
    MotV.ordOfPlace E S hS g - 1 ≤ MotV.ordOfPlace E S hS (D g) := by
  rcases classification_ratPlace E S hS with h | ⟨a, b, hns, h⟩
  · subst h
    rw [show hS = infPlace_ratPlace E from Subsingleton.elim _ _]
    exact (infPlace_deriv_bound E (infPlace_ratPlace E) D hDx hDy).2 g hg
  · subst h
    rw [show hS = (MotC2.AffPlace N E a b hns).1 from Subsingleton.elim _ _]
    exact (affPlace_deriv_bound E a b hns D hDx hDy).2 g hg


/-- **The main case `D r ≠ 0`.**  If the Artin–Schreier condition holds and the invariant
derivation does not kill `r`, then `r` is constant. -/
theorem case_deriv_ne_zero (E : WeierstrassCurve N) [E.IsElliptic] (f : Polynomial N)
    (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree)
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₃)
    (hDy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E)
    (r : MotC2.Func E) (hr : Hyp E f r) (hDr : D r ≠ 0) :
    ∃ c : N, algebraMap N (MotC2.Func E) c = r := by
  by_contra hcon
  have hnot : ¬ (∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S), r ∈ S) :=
    fun hall => hcon (integral_everywhere_constant E r hall)
  push_neg at hnot
  obtain ⟨S, hS, hrS⟩ := hnot
  have hord : MotV.ordOfPlace E S hS r < 0 := by
    rcases lt_or_ge (MotV.ordOfPlace E S hS r) 0 with h | h
    · exact h
    · exact absurd (((ordOfPlace_api E S hS).2.2.1 r).mp h) hrS
  have hchain : ∀ (Q : Subalgebra N (MotC2.Func E)) (hQ : MotC2.IsRatPlace E Q),
      D (Polynomial.aeval r f) = Polynomial.aeval r f.derivative * D r := by
    intro Q hQ
    simpa [smul_eq_mul] using Derivation.map_aeval D f r
  have hpos : 0 < MotV.ordOfPlace E S hS (D r) := by
    obtain ⟨v, hvTriv, hv1, _, _⟩ := placeVal_valuation E S hS
    exact deriv_pole_pos E f hf2 hf5 r hr S hS v hvTriv hv1
      (aeval_order_pole E f hf2 hf5 S hS r hord).1
      (aeval_order_pole E f hf2 hf5 S hS r hord).2 D (hchain S hS)
      (fun g hg => deriv_mem_of_mem E D hDx hDy S hS hg)
      (fun g hg => deriv_bound_general E D hDx hDy S hS g hg) hDr hord
  have hreg : ∀ (Q : Subalgebra N (MotC2.Func E)) (hQ : MotC2.IsRatPlace E Q),
      0 ≤ MotV.ordOfPlace E Q hQ (D r) := by
    intro Q hQ
    by_cases hq : MotV.ordOfPlace E Q hQ r < 0
    · obtain ⟨w, hwTriv, hw1, _, _⟩ := placeVal_valuation E Q hQ
      exact le_of_lt (deriv_pole_pos E f hf2 hf5 r hr Q hQ w hwTriv hw1
        (aeval_order_pole E f hf2 hf5 Q hQ r hq).1
        (aeval_order_pole E f hf2 hf5 Q hQ r hq).2 D (hchain Q hQ)
        (fun g hg => deriv_mem_of_mem E D hDx hDy Q hQ hg)
        (fun g hg => deriv_bound_general E D hDx hDy Q hQ g hg) hDr hq)
    · have hq' : 0 ≤ MotV.ordOfPlace E Q hQ r := not_lt.mp hq
      have hmem : r ∈ Q := ((ordOfPlace_api E Q hQ).2.2.1 r).mp hq'
      have hmem' : D r ∈ Q := deriv_mem_of_mem E D hDx hDy Q hQ hmem
      exact ((ordOfPlace_api E Q hQ).2.2.1 (D r)).mpr hmem'
  obtain ⟨c, hc⟩ := integral_everywhere_constant E (D r)
    (fun Q hQ => ((ordOfPlace_api E Q hQ).2.2.1 (D r)).mp (hreg Q hQ))
  have hc0 : c ≠ 0 := by
    intro h0
    exact hDr (by rw [← hc, h0, map_zero])
  have hz : MotV.ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) = 0 :=
    (ordOfPlace_api E S hS).2.2.2.2.2.1 c hc0
  rw [hc] at hz
  omega

/-- **The induction**: strong induction on the pole order at a fixed place. -/
theorem main_ind (E : WeierstrassCurve N) [E.IsElliptic]
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₃)
    (hDy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E) :
    ∀ (n : ℕ) (A : Polynomial N) (r : MotC2.Func E)
      (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S),
      2 ≤ A.natDegree → ¬ 5 ∣ A.natDegree → Hyp E A r →
      MotV.ordOfPlace E S hS r < 0 →
      (-(MotV.ordOfPlace E S hS r)).toNat ≤ n →
      ∃ c : N, algebraMap N (MotC2.Func E) c = r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A r S hS hA2 hA5 hr hord hbound
    by_cases hD : D r = 0
    · obtain ⟨ρ, hρ⟩ := ker_deriv_fifthpowers E D (by rw [hDx]; exact invDeriv_genX_ne_zero E) r hD
      obtain ⟨A₀, hA₀deg, hA₀val⟩ := exists_rootPoly (R := MotC2.Func E) A ρ
      have hdesc : Hyp E A₀ ρ := hyp_descend E A A₀ r ρ hA₀val hr hρ
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num : 5 ≠ 0)] at hρ
        have hmem : r ∈ S := hρ.symm ▸ Subalgebra.zero_mem S
        exact absurd (((ordOfPlace_api E S hS).2.2.1 r).mpr hmem) (not_le.mpr hord)
      have hpow : MotV.ordOfPlace E S hS r = 5 * MotV.ordOfPlace E S hS ρ := by
        rw [hρ]
        exact ordOfPlace_pow E S hS hρ0 5
      have hρord : MotV.ordOfPlace E S hS ρ < 0 := by nlinarith [hpow, hord]
      have hbnd : (-(MotV.ordOfPlace E S hS ρ)).toNat < n := by
        have h5 : (-(MotV.ordOfPlace E S hS r)).toNat =
            5 * (-(MotV.ordOfPlace E S hS ρ)).toNat := by omega
        have hpos : 0 < (-(MotV.ordOfPlace E S hS ρ)).toNat := by omega
        omega
      have hA₀2 : 2 ≤ A₀.natDegree := by rw [hA₀deg]; exact hA2
      have hA₀5 : ¬ 5 ∣ A₀.natDegree := by rw [hA₀deg]; exact hA5
      obtain ⟨c, hc⟩ := ih ((-(MotV.ordOfPlace E S hS ρ)).toNat) hbnd A₀ ρ S hS hA₀2 hA₀5
        hdesc hρord le_rfl
      exact ⟨c ^ 5, by rw [map_pow, hc, hρ]⟩
    · exact case_deriv_ne_zero E A hA2 hA5 D hDx hDy r hr hD

/-- **`Work.MotV5.hurwitz_AS`, main form.**  An element of `N(E)` satisfying the Artin–Schreier
solvability condition of `hurwitz_AS` is constant. -/
theorem hurwitz_AS_main (E : WeierstrassCurve N) [E.IsElliptic] (f : Polynomial N)
    (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree) (r : MotC2.Func E)
    (hr : Hyp E f r) : ∃ c : N, algebraMap N (MotC2.Func E) c = r := by
  obtain ⟨D, hDx, hDy⟩ := exists_invariantDeriv E
  by_contra hcon
  have hnot : ¬ (∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S), r ∈ S) :=
    fun hall => hcon (integral_everywhere_constant E r hall)
  push_neg at hnot
  obtain ⟨S, hS, hrS⟩ := hnot
  have hord : MotV.ordOfPlace E S hS r < 0 := by
    rcases lt_or_ge (MotV.ordOfPlace E S hS r) 0 with h | h
    · exact h
    · exact absurd (((ordOfPlace_api E S hS).2.2.1 r).mp h) hrS
  exact hcon (main_ind E D hDx hDy (-(MotV.ordOfPlace E S hS r)).toNat f r S hS hf2 hf5 hr
    hord le_rfl)

end

end Work.MotV5
