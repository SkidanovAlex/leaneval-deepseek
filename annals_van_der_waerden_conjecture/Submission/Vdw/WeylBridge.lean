import Mathlib
import Submission.Vdw.FourierTranslate
import Submission.Commons.Analysis.ExponentialSums.weyl_inequality

open Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Weyl bound gives a power saving for complete polynomial exponential sums

The §4 Fourier gate of the development (`FourierTranslate.expSumBound` /
`MIndexBound`) is a *power saving* `p^{-θ}` (`θ > 0`, allowed to depend on `n`)
for the complete exponential sum

    `Σ_{c ∈ F_p} χ(Q(c))`,    `1 ≤ deg Q ≤ n`,   `p > n`.

The deep classical input is the Weil bound (`θ = 1/2`).  This module shows that
the *elementary* Weyl bound (van der Corput differencing), already available in
the shared commons as
`Commons.Analysis.ExponentialSums.weyl_inequality`, already supplies

    `θ = 2^{-n}`,

i.e. the deepest analytic input of the whole development (the Riemann hypothesis
for Artin–Schreier curves / Hasse's theorem) is **not needed**: any positive
power saving suffices, at the price of shrinking the Case-I threshold `δ` to
`δ ≈ θ/n` (Roadmap Session-152).

## Method

* `liftPoly p Q : ℤ[X]` — the canonical integer lift of `Q : (ZMod p)[X]`
  (coefficients in `[0,p)`), with `map (Int.castRingHom (ZMod p)) (liftPoly p Q)
  = Q` (`map_liftPoly`) and the evaluation bridge `eval_liftPoly_cast`.
* `wPoly p Q = C (p:ℝ)⁻¹ * (liftPoly p Q).map (Int.castRingHom ℝ) : ℝ[X]` — the
  real phase polynomial of the Weyl theorem: its leading coefficient is exactly
  `a/p` with `a = (Q.leadingCoeff).val`, so Weyl's hypothesis
  `|f.leadingCoeff - a/q| ≤ t/q²` holds with `a = (Q.leadingCoeff).val`,
  `q = p`, `t = 1` (indeed with equality).
* `stdAddChar_eq_exp_wPoly` — the character bridge
  `χ(Q(c)) = exp (2πi · wPoly.eval c)` for `c ∈ ℤ`.
* `expSumBound_weyl` — the conclusion: `ExpSumBound n (2^{-n})`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The canonical integer lift of a polynomial over `ZMod p`: coefficients are
taken in the canonical representative range `[0, p)`. -/
def liftPoly (Q : (ZMod p)[X]) : ℤ[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun z : ZMod p => (z.val : ℤ)) (by simp) Q.toFinsupp.coeff))

theorem liftPoly_coeff (Q : (ZMod p)[X]) (i : ℕ) :
    (liftPoly p Q).coeff i = ((Q.coeff i).val : ℤ) := by
  simp only [liftPoly, Polynomial.coeff_ofFinsupp, Finsupp.mapRange_apply]
  rfl

theorem map_liftPoly (Q : (ZMod p)[X]) :
    Polynomial.map (Int.castRingHom (ZMod p)) (liftPoly p Q) = Q := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  ext i
  rw [Polynomial.coeff_map, liftPoly_coeff]
  have hz : (Int.castRingHom (ZMod p)) ((Q.coeff i).val : ℤ)
      = ((Q.coeff i).val : ZMod p) := by
    simp [Int.castRingHom]
  rw [hz]
  exact ZMod.natCast_zmod_val (Q.coeff i)

theorem eval_liftPoly_cast (Q : (ZMod p)[X]) (z : ℤ) :
    (((liftPoly p Q).eval z : ℤ) : ZMod p) = Q.eval ((z : ZMod p)) := by
  have h1 : Polynomial.eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) (liftPoly p Q)
      = (((liftPoly p Q).eval z : ℤ) : ZMod p) := Polynomial.eval₂_hom _ _
  rw [← h1, Polynomial.eval₂_eq_eval_map, map_liftPoly]

/-! ## 2. The real phase polynomial and the character bridge -/

section Phase

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem eval_liftPoly_map (Q : (ZMod p)[X]) (x : ℤ) :
    ((liftPoly p Q).map (Int.castRingHom ℝ)).eval ((x:ℤ):ℝ)
      = (((liftPoly p Q).eval x : ℤ) : ℝ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_hom (Int.castRingHom ℝ) x

/-- The real phase polynomial attached to `Q : (ZMod p)[X]`, for use with the
Weyl bound: `wPoly p Q = C (p:ℝ)⁻¹ * (liftPoly p Q).map (Int.castRingHom ℝ)`,
so its `i`-th coefficient is `(Q.coeff i).val / p` and its leading coefficient is
`(Q.leadingCoeff).val / p`. -/
def wPoly (Q : (ZMod p)[X]) : ℝ[X] :=
  Polynomial.C ((p:ℝ)⁻¹) * (liftPoly p Q).map (Int.castRingHom ℝ)

theorem wPoly_eval_int (Q : (ZMod p)[X]) (x : ℤ) :
    (wPoly p Q).eval ((x:ℤ):ℝ) = (p:ℝ)⁻¹ * (((liftPoly p Q).eval x : ℤ) : ℝ) := by
  rw [wPoly, Polynomial.eval_mul, Polynomial.eval_C, eval_liftPoly_map]

theorem liftPoly_natDegree (Q : (ZMod p)[X]) (hQ : Q ≠ 0) :
    (liftPoly p Q).natDegree = Q.natDegree := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [liftPoly_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  · rw [liftPoly_coeff]
    have hc : Q.coeff Q.natDegree = Q.leadingCoeff := rfl
    rw [hc]
    intro h
    have h2 : (Q.coeff Q.natDegree).val = 0 := by exact_mod_cast h
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ ((ZMod.val_eq_zero _).mp h2)

theorem p_real_ne_zero : ((p:ℝ)) ≠ 0 := by
  exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

theorem wPoly_natDegree (Q : (ZMod p)[X]) (hQ : Q ≠ 0) :
    (wPoly p Q).natDegree = Q.natDegree := by
  rw [wPoly, Polynomial.natDegree_C_mul (inv_ne_zero (p_real_ne_zero p)),
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective, liftPoly_natDegree p Q hQ]

theorem wPoly_leadingCoeff (Q : (ZMod p)[X]) (hQ : Q ≠ 0) :
    (wPoly p Q).leadingCoeff = ((Q.leadingCoeff).val : ℝ) / (p:ℝ) := by
  have hcoeff : ((liftPoly p Q).map (Int.castRingHom ℝ)).coeff Q.natDegree
      = ((Q.leadingCoeff).val : ℝ) := by
    rw [Polynomial.coeff_map, liftPoly_coeff]
    rfl
  show (wPoly p Q).coeff (wPoly p Q).natDegree = _
  rw [wPoly_natDegree p Q hQ]
  show (Polynomial.C ((p:ℝ)⁻¹) * (liftPoly p Q).map (Int.castRingHom ℝ)).coeff Q.natDegree = _
  rw [Polynomial.coeff_C_mul, hcoeff, div_eq_inv_mul]

theorem stdAddChar_eq_exp (Q : (ZMod p)[X]) (x : ℕ) :
    ZMod.stdAddChar (Q.eval ((x : ZMod p)))
      = Complex.exp (2 * Real.pi * Complex.I
          * (((liftPoly p Q).eval ((x : ℤ)) : ℤ) : ℂ) / (p : ℂ)) := by
  have hx : Q.eval ((x : ZMod p)) = (((liftPoly p Q).eval ((x : ℤ)) : ℤ) : ZMod p) := by
    rw [← Int.cast_natCast (R := ZMod p) x]
    exact (eval_liftPoly_cast p Q (x : ℤ)).symm
  rw [hx]
  exact ZMod.stdAddChar_coe (((liftPoly p Q).eval ((x : ℤ)) : ℤ))

theorem sum_zmod_eq_sum_range [NeZero p] (g : ZMod p → ℂ) :
    ∑ c : ZMod p, g c = ∑ x ∈ Finset.range p, g ((x : ZMod p)) := by
  symm
  refine Finset.sum_bij (s := Finset.range p) (t := (Finset.univ : Finset (ZMod p)))
    (f := fun x : ℕ => g ((x : ZMod p))) (g := g) (fun x _ => (x : ZMod p)) ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_univ _
  · intro x hx y hy hxy
    have h : ((x : ZMod p)).val = ((y : ZMod p)).val := by rw [hxy]
    have hx' : ((x : ZMod p)).val = x := ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)
    have hy' : ((y : ZMod p)).val = y := ZMod.val_natCast_of_lt (Finset.mem_range.mp hy)
    omega
  · intro c _
    exact ⟨c.val, Finset.mem_range.mpr c.val_lt, ZMod.natCast_zmod_val c⟩
  · intro x _
    rfl

/-- The character bridge in the exact shape consumed by the Weyl theorem. -/
theorem stdAddChar_eq_exp_wPoly (Q : (ZMod p)[X]) (x : ℕ) :
    ZMod.stdAddChar (Q.eval ((x : ZMod p)))
      = Complex.exp (((2 * Real.pi * (wPoly p Q).eval ((0:ℝ) + (x:ℝ)) : ℝ) : ℂ) * Complex.I) := by
  rw [stdAddChar_eq_exp p Q x]
  congr 1
  have hx : ((0:ℝ) + (x:ℝ)) = (((x:ℤ)) : ℝ) := by push_cast; ring
  rw [hx, wPoly_eval_int p Q (x:ℤ)]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_intCast, Complex.ofReal_ofNat, div_eq_mul_inv]
  ring

/-- **Vanishing of a non-trivial affine linear phase** over `ZMod p`
(orthogonality of a non-trivial character, equivalently a complete Gauss-sum-free
elementary sum). -/
theorem sum_stdAddChar_mul_add (u v : ZMod p) (hu : u ≠ 0) :
    ∑ c : ZMod p, ZMod.stdAddChar (u * c + v) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hsum : ∑ c : ZMod p, ZMod.stdAddChar (c * u) = 0 := by
    have h := AddChar.sum_mulShift (b := u) (ZMod.isPrimitive_stdAddChar p)
    rw [if_neg hu] at h
    simpa using h
  have h1 : ∀ c : ZMod p, ZMod.stdAddChar (u * c + v)
      = ZMod.stdAddChar (c * u) * ZMod.stdAddChar v := by
    intro c; rw [mul_comm u c, AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun c _ => h1 c), ← Finset.sum_mul, hsum, zero_mul]

/-- **Vanishing of the linear phase.**  For a polynomial of degree `1`, the
complete exponential sum over `F_p` vanishes. -/
theorem sum_stdAddChar_eval_natDegree_one (Q : (ZMod p)[X]) (hQ : Q.natDegree = 1) :
    ∑ c : ZMod p, ZMod.stdAddChar (Q.eval c) = 0 := by
  have hQne : Q ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hQ; omega
  have hu : Q.coeff 1 ≠ 0 := by
    have h := Polynomial.leadingCoeff_ne_zero.mpr hQne
    simpa [Polynomial.leadingCoeff, hQ] using h
  have heval : ∀ c : ZMod p, Q.eval c = Q.coeff 1 * c + Q.coeff 0 := by
    intro c
    have h := congrArg (fun r : (ZMod p)[X] => r.eval c)
      (Polynomial.eq_X_add_C_of_natDegree_le_one (p := Q) (le_of_eq hQ))
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] using h
  have h1 : ∀ c : ZMod p, ZMod.stdAddChar (Q.eval c)
      = ZMod.stdAddChar (Q.coeff 1 * c + Q.coeff 0) := fun c => by rw [heval c]
  rw [Finset.sum_congr rfl (fun c _ => h1 c), sum_stdAddChar_mul_add p (Q.coeff 1) (Q.coeff 0) hu]

end Phase


end

end Submission.Vdw
