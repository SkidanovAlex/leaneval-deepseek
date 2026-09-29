import Mathlib
import Submission.Work.DFT.dftDefs
import Submission.Work.DFT.rootSumZ
import Submission.Work.DFT.subDvdMulIf
import Submission.Work.DFT.charExpSplit

/-!
# Orthogonality of the multidimensional DFT character (paper §2.4)

For mixed-radix parameters `ts` (all positive) and flat indices `j a : Fin ts.prod`, the
character sum
`∑ k, exp(2πi · Σᵢ (jᵢ - aᵢ)kᵢ/tᵢ)`
is `ts.prod` when `j = a` and `0` otherwise. This is the orthogonality relation for the
multidimensional DFT `HvdH.dftMulti` used in §2.4 of Harvey–van der Hoeven.

The proof is by induction on `ts`: splitting the sum over `Fin ts.prod` according to the first
digit (`Work.DFT.charSumCons`) turns it into a product of the one-dimensional root-of-unity sum
(`Work.DFT.rootSumZ`) and the same statement for the tail list; the bookkeeping that glues the
two `if`s into `if j = a` is `Work.DFT.subDvdMulIf`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-- Splitting a sum over `Fin (m * n)` into a double sum, using the division/modulo
equivalence `finProdFinEquiv`. -/
theorem sum_fin_mul (m n : ℕ) (f : Fin (m * n) → ℂ) :
    (∑ k : Fin (m * n), f k) = ∑ q : Fin m, ∑ r : Fin n, f (finProdFinEquiv (q, r)) := by
  rw [← Equiv.sum_comp finProdFinEquiv f]
  exact Fintype.sum_prod_type (fun p => f (finProdFinEquiv p))

/-- The character sum over `Fin (t :: ts).prod` factorises into the one-dimensional character
sum over `Fin t` and the character sum for the tail list. -/
theorem charSumCons (t : ℕ) (ts : List ℕ) (hT : 0 < ts.prod) (c₀ : ℤ) (cs : List ℤ) :
    (∑ k : Fin ((t :: ts).prod), charExp (t :: ts) (c₀ :: cs) k) =
      (∑ q : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((c₀ : ℝ) * (q : ℝ)) / (t : ℝ) : ℝ))) *
      (∑ r : Fin ts.prod, charExp ts cs r) := by
  rw [show (t :: ts).prod = t * ts.prod from rfl]
  rw [sum_fin_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have hidx : (↑(finProdFinEquiv (q, r)) : ℕ) = r.val + ts.prod * q.val := rfl
  rw [hidx, charExpSplit t ts hT c₀ cs q r q.isLt r.isLt]

/-- Orthogonality of the multidimensional DFT character, for natural-number indices. -/
theorem charSumSub_gen (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (jj aa : ℕ)
    (hj : jj < ts.prod) (ha : aa < ts.prod) :
    (∑ k : Fin ts.prod, charExp ts (subN (HvdH.digits ts jj) (HvdH.digits ts aa)) k) =
      if jj = aa then (ts.prod : ℂ) else 0 := by
  induction ts generalizing jj aa with
  | nil =>
    have hj0 : jj = 0 := Nat.lt_one_iff.mp hj
    have ha0 : aa = 0 := Nat.lt_one_iff.mp ha
    subst hj0; subst ha0
    rw [List.prod_nil]
    simp [charExp, myPhase]
  | cons t ts ih =>
    have ht : 0 < t := hpos t (List.mem_cons_self ..)
    have hpos' : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem t hx)
    have hT : 0 < ts.prod := List.prod_pos hpos'
    have h1 : jj / ts.prod < t := (Nat.div_lt_iff_lt_mul hT).mpr hj
    have h2 : aa / ts.prod < t := (Nat.div_lt_iff_lt_mul hT).mpr ha
    have hj' : jj % ts.prod < ts.prod := Nat.mod_lt _ hT
    have ha' : aa % ts.prod < ts.prod := Nat.mod_lt _ hT
    have hc : subN (HvdH.digits (t :: ts) jj) (HvdH.digits (t :: ts) aa)
        = ((((jj / ts.prod) % t : ℕ) : ℤ) - (((aa / ts.prod) % t : ℕ) : ℤ)) ::
          subN (HvdH.digits ts (jj % ts.prod)) (HvdH.digits ts (aa % ts.prod)) := rfl
    rw [hc, charSumCons t ts hT, rootSumZ t ht,
      ih hpos' (jj % ts.prod) (aa % ts.prod) hj' ha']
    exact subDvdMulIf t ts.prod jj aa ht hT hj ha

theorem charSumSub (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j a : Fin ts.prod) :
    (∑ k : Fin ts.prod,
        charExp ts (subN (HvdH.digits ts j) (HvdH.digits ts a)) k) =
      if j = a then (ts.prod : ℂ) else 0 := by
  have hgen := charSumSub_gen ts hpos j.val a.val j.isLt a.isLt
  by_cases h : j = a
  · have hv : j.val = a.val := by rw [h]
    rw [ite_eq_left hv] at hgen
    simpa [h] using hgen
  · have hv : ¬ (j.val = a.val) := fun hc => h (Fin.ext hc)
    rw [ite_eq_right hv] at hgen
    simpa [h] using hgen

end Work.DFT
