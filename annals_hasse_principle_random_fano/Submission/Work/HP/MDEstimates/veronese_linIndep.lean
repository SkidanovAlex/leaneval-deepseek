import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.Lat.prim_bezout
import Submission.Work.HP.Lat.detLAux

/-!
# Independence of two Veronese vectors

If `x ≠ ±y` are primitive integer vectors and `d ≥ 2`, then `ν(x) = Work.HP.veronese d n x` and
`ν(y)` are linearly independent over `ℤ`.

Route.  Given `g 0 • ν(x) + g 1 • ν(y) = 0` with `g 0 ≠ 0`, evaluate at the monomials `X_i^d` and
`X_i^{d-1}X_j` (`Work.HP.NA.monDi`, `monDij`): for any `i` with `y i ≠ 0` this gives
`g 0 · x_i^d = -g 1 · y_i^d` and `g 0 · x_i^{d-1} x_j = -g 1 · y_i^{d-1} y_j`, whence
`x_j y_i = x_i y_j` for every `j`, i.e. `x` and `y` are proportional.  Bézout for the primitive
vectors (`Work.HP.Lat.prim_bezout`: `∑ u_j y_j = 1`) turns the proportionality into `y_i ∣ x_i` and
`x_i ∣ y_i`; since `x_i, y_i ≠ 0` this forces `x_i = ± y_i`, and then the proportionality gives
`x = ± y`, contradicting the hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.MDEstimates

open Work.HP

/-- The Veronese image of a nonzero vector is nonzero. -/
lemma veronese_ne_zero {d n : ℕ} {y : Fin (n + 1) → ℤ} (hy : y ≠ 0) :
    veronese d n y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  intro h
  have h1 := congrFun h (NA.monDi d n i)
  rw [NA.veronese_monDi] at h1
  exact (pow_ne_zero d hi) h1

theorem veronese_linIndep (d n : ℕ) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : x ≠ y) (hxy' : x ≠ -y) :
    LinearIndependent ℤ ![veronese d n x, veronese d n y] := by
  have hd0 : d ≠ 0 := by omega
  have hd1 : 1 ≤ d := by omega
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • veronese d n x + g 1 • veronese d n y = 0 := by
    have h := hg
    rw [Fin.sum_univ_two] at h
    simpa using h
  have hcoord : ∀ m : Mon d n, g 0 * veronese d n x m + g 1 * veronese d n y m = 0 := by
    intro m
    have h := congrFun hsum m
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hy0 : y ≠ 0 := isPrim_ne_zero hy
  by_cases hg0 : g 0 = 0
  · -- then `g 1 • ν(y) = 0` and `ν(y) ≠ 0`
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
    have h1 := hcoord (NA.monDi d n i)
    rw [NA.veronese_monDi, NA.veronese_monDi, hg0] at h1
    have h2 : g 1 * y i ^ d = 0 := by simpa using h1
    have hg1 : g 1 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h (pow_ne_zero d hi)
    intro j
    fin_cases j
    · exact hg0
    · exact hg1
  · -- main case: `x` and `y` are proportional, hence `x = ± y`
    exfalso
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := Function.ne_iff.mp hy0
    have hxi : x i ≠ 0 := by
      intro hxi0
      have h1 := hcoord (NA.monDi d n i)
      rw [NA.veronese_monDi, NA.veronese_monDi] at h1
      have h1' : g 1 * y i ^ d = 0 := by
        rw [hxi0, zero_pow hd0, mul_zero, zero_add] at h1
        exact h1
      have hg1 : g 1 = 0 := by
        rcases mul_eq_zero.mp h1' with h | h
        · exact h
        · exact absurd h (pow_ne_zero d hi)
      have h3 : g 0 • veronese d n x = 0 := by
        rw [hg1, zero_smul, add_zero] at hsum
        exact hsum
      have h4 : veronese d n x = 0 := by
        funext m
        have hm := congrFun h3 m
        have hm' : g 0 * veronese d n x m = 0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using hm
        exact (mul_eq_zero.mp hm').resolve_left hg0
      exact veronese_ne_zero hx0 h4
    -- proportionality
    have hprop : ∀ j, x j * y i = x i * y j := by
      intro j
      have e1 := hcoord (NA.monDi d n i)
      have e2 := hcoord (NA.monDij d n hd1 i j)
      rw [NA.veronese_monDi, NA.veronese_monDi] at e1
      rw [NA.veronese_monDij, NA.veronese_monDij] at e2
      have hB : g 0 * x i ^ d = -(g 1 * y i ^ d) := by linarith
      have hC : g 0 * (x i ^ (d - 1) * x j) = -(g 1 * (y i ^ (d - 1) * y j)) := by linarith
      have hpow : y i ^ (d - 1) * y i = y i ^ d := by
        rw [← pow_succ]
        congr 1
        omega
      have hpow' : (y i ^ (d - 1) * y j) * y i = y i ^ d * y j := by
        rw [mul_assoc, mul_comm (y j) (y i), ← mul_assoc, hpow]
      have hkey : g 0 * (x i ^ (d - 1) * x j) * y i = g 0 * x i ^ d * y j := by
        calc g 0 * (x i ^ (d - 1) * x j) * y i
            = (g 0 * (x i ^ (d - 1) * x j)) * y i := by ring
          _ = (-(g 1 * (y i ^ (d - 1) * y j))) * y i := by rw [hC]
          _ = -(g 1 * ((y i ^ (d - 1) * y j) * y i)) := by ring
          _ = -(g 1 * (y i ^ d * y j)) := by rw [hpow']
          _ = (-(g 1 * y i ^ d)) * y j := by ring
          _ = g 0 * x i ^ d * y j := by rw [← hB]
      have hcancel : g 0 * x i ^ (d - 1) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hxi)
      have hpowx : x i ^ (d - 1) * x i = x i ^ d := by
        rw [← pow_succ]
        congr 1
        omega
      have hkey2 : (g 0 * x i ^ (d - 1)) * (x j * y i)
          = (g 0 * x i ^ (d - 1)) * (x i * y j) := by
        have hL : (g 0 * x i ^ (d - 1)) * (x j * y i) = g 0 * (x i ^ (d - 1) * x j) * y i := by
          ring
        have hR : (g 0 * x i ^ (d - 1)) * (x i * y j) = g 0 * x i ^ d * y j := by
          rw [← hpowx]
          ring
        rw [hL, hR, hkey]
      exact mul_left_cancel₀ hcancel hkey2
    -- Bézout in both directions
    obtain ⟨uy, huy⟩ := Lat.prim_bezout y hy
    obtain ⟨ux, hux⟩ := Lat.prim_bezout x hx
    have hdvd1 : y i ∣ x i := by
      refine ⟨∑ j, uy j * x j, ?_⟩
      have key : x i = (∑ j, uy j * x j) * y i := by
        calc x i = x i * (∑ j, uy j * y j) := by rw [huy, mul_one]
          _ = ∑ j, x i * (uy j * y j) := by rw [Finset.mul_sum]
          _ = ∑ j, uy j * (x i * y j) := by
                refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j, uy j * (x j * y i) := by
                refine Finset.sum_congr rfl fun j _ => by rw [hprop j]
          _ = (∑ j, uy j * x j) * y i := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun j _ => by ring
      rw [key, mul_comm]
    have hdvd2 : x i ∣ y i := by
      refine ⟨∑ j, ux j * y j, ?_⟩
      have key : y i = (∑ j, ux j * y j) * x i := by
        calc y i = y i * (∑ j, ux j * x j) := by rw [hux, mul_one]
          _ = ∑ j, y i * (ux j * x j) := by rw [Finset.mul_sum]
          _ = ∑ j, ux j * (y i * x j) := by
                refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j, ux j * (x j * y i) := by
                refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j, ux j * (x i * y j) := by
                refine Finset.sum_congr rfl fun j _ => by rw [hprop j]
          _ = (∑ j, ux j * y j) * x i := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun j _ => by ring
      rw [key, mul_comm]
    obtain ⟨s, hs⟩ := hdvd1
    obtain ⟨t, ht⟩ := hdvd2
    -- `x i = y i * s` and `y i = x i * t` force `s = ± 1`
    have hst : s * t = 1 := by
      have h2 : x i = x i * (t * s) := by
        calc x i = y i * s := hs
          _ = (x i * t) * s := by rw [ht]
          _ = x i * (t * s) := by ring
      have h1 : x i * (t * s - 1) = 0 := by
        rw [mul_sub, mul_one, ← h2]
        ring
      have h3 : t * s - 1 = 0 := (mul_eq_zero.mp h1).resolve_left hxi
      have h4 : t * s = 1 := by omega
      rw [mul_comm] at h4
      exact h4
    have hs1 : s = 1 ∨ s = -1 :=
      (Int.eq_one_or_neg_one_of_mul_eq_one' hst).imp (fun h => h.1) (fun h => h.1)
    rcases hs1 with h1 | h1
    · apply hxy
      funext j
      have hj := hprop j
      have hxii : x i = y i := by rw [hs, h1, mul_one]
      have : x j * y i = y j * y i := by rw [hj, hxii]; ring
      exact mul_right_cancel₀ hi this
    · apply hxy'
      funext j
      have hj := hprop j
      have hxii : x i = -y i := by rw [hs, h1]; ring
      have : x j * y i = (-y j) * y i := by rw [hj, hxii]; ring
      exact mul_right_cancel₀ hi this

end Work.HP.MDEstimates
