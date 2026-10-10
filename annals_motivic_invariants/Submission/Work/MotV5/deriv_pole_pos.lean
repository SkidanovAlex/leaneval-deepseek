import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The order of `D r` at a place where `r` has a pole

This file proves `Work.MotV5.deriv_pole_pos`: let `E` be a Weierstrass curve over an algebraically
closed field `N` of characteristic `5`, `S` a rational place of the function field `N(E)`,
`v` a `ℤᵐ⁰`-valued valuation of `N(E)` trivial on `N` whose order function is `ordOfPlace E S hS`,
and `D` an `N`-derivation of `N(E)` which is regular at `S` (`D` maps `S` into `S`) and which
increases the order at `S` by at most one (`ordOfPlace g - 1 ≤ ordOfPlace (D g)` for `g ∉ S`).
If `r` has a pole at `S` (`ordOfPlace r < 0`) and satisfies an Artin–Schreier relation
`f(r) ≡ u⁵ - u` modulo functions without a pole at `S`, for a polynomial `f` of degree `≥ 2` not
divisible by `5`, then `D r` has a *zero* at `S`: `0 < ordOfPlace (D r)`.

The proof is the local form of the ramification argument of
`Work.MotV5.two_le_ordInf_deriv_of_pole`:

* the Artin–Schreier relation `f(r) = (u⁵ - u) + s` with `ordOfPlace s ≥ 0`, together with
  `ordOfPlace (f(r)) = deg f · ordOfPlace r < 0`, forces `u` to have a pole at `S` and gives the
  *ramification equation* `deg f · ordOfPlace r = 5 · ordOfPlace u`; since `5 ∤ deg f` this gives
  `5 ∣ ordOfPlace r`, hence `ordOfPlace r ≤ -5` and `ordOfPlace u ≤ -2`;
* differentiating the relation gives `f'(r) · D r = -D u + D s`, and taking orders produces
  `ordOfPlace r · (deg f/5 - (deg f - 1)) - 1 ≤ ordOfPlace (D r)`, which is positive because
  `ordOfPlace r ≤ -5` and `deg f ≥ 2`.

## Tags

elliptic curve, function field, place, derivation, Artin–Schreier
-/

open Polynomial
open scoped WithZero

set_option autoImplicit false

namespace Work.MotV5

namespace DerivPoleAux

open Work.MotV

variable {N : Type*} [Field N]

/-- An element of the local ring `S` has nonnegative order at `S`. -/
lemma ordOfPlace_nonneg_of_mem (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    {f : Work.MotC2.Func E} (hf : f ∈ S) : 0 ≤ ordOfPlace E S hS f := by
  rw [ordOfPlace]
  simp only [dif_pos hf]
  exact Int.natCast_nonneg _

/-- An element of negative order at `S` does not lie in the local ring `S`. -/
lemma notMem_of_neg (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) {f : Work.MotC2.Func E}
    (h : ordOfPlace E S hS f < 0) : f ∉ S :=
  fun hmem => absurd (ordOfPlace_nonneg_of_mem E S hS hmem) (not_le.mpr h)

/-- The order of `0` is `0`. -/
lemma ordOfPlace_zero (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    ordOfPlace E S hS (0 : Work.MotC2.Func E) = 0 := by
  rw [ordOfPlace]
  simp only [dif_pos (Subalgebra.zero_mem S)]
  rw [show (⟨(0 : Work.MotC2.Func E), Subalgebra.zero_mem S⟩ : ↥S) = 0 from rfl,
    AddValuation.map_zero]
  exact WithTop.untopD_top 0

/-! ## The order function of a valuation

If `v` is a valuation of `N(E)` whose associated order function is `ordOfPlace E S hS`, the
valuation axioms transfer to `ordOfPlace`. -/

/-- `WithZero.exp` commutes with `max`. -/
lemma exp_max_int (a b : ℤ) :
    WithZero.exp (max a b) = max (WithZero.exp a) (WithZero.exp b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (WithZero.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithZero.exp_le_exp.mpr h)]

/-- `v f ≤ 1` exactly when `f` has nonnegative order at `S`. -/
lemma le_one_iff (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g))) (f : Work.MotC2.Func E) :
    v f ≤ 1 ↔ 0 ≤ ordOfPlace E S hS f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Valuation.map_zero, ordOfPlace_zero E S hS]
    simp
  · rw [hv1 f hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    constructor <;> intro h <;> omega

/-- `1 < v f` exactly when `f` has a pole at `S`. -/
lemma one_lt_iff (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g))) (f : Work.MotC2.Func E) :
    1 < v f ↔ ordOfPlace E S hS f < 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Valuation.map_zero, ordOfPlace_zero E S hS]
    simp
  · rw [hv1 f hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    constructor <;> intro h <;> omega

/-- The order at `S` is multiplicative. -/
lemma ord_mul (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g)))
    (f g : Work.MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0) :
    ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g := by
  have key : WithZero.exp (-(ordOfPlace E S hS (f * g)))
      = WithZero.exp (-(ordOfPlace E S hS f + ordOfPlace E S hS g)) := by
    have hL : WithZero.exp (-(ordOfPlace E S hS (f * g))) = v (f * g) :=
      (hv1 (f * g) (mul_ne_zero hf hg)).symm
    have hR : WithZero.exp (-(ordOfPlace E S hS f + ordOfPlace E S hS g)) = v f * v g := by
      rw [show -(ordOfPlace E S hS f + ordOfPlace E S hS g)
            = -(ordOfPlace E S hS f) + -(ordOfPlace E S hS g) by ring,
        WithZero.exp_add, hv1 f hf, hv1 g hg]
    rw [hL, hR, Valuation.map_mul]
  have h := WithZero.exp_inj.mp key
  linarith

/-- The order at `S` is unchanged by negation. -/
lemma ord_neg (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g))) (f : Work.MotC2.Func E) :
    ordOfPlace E S hS (-f) = ordOfPlace E S hS f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  · have key : WithZero.exp (-(ordOfPlace E S hS (-f)))
        = WithZero.exp (-(ordOfPlace E S hS f)) := by
      rw [show WithZero.exp (-(ordOfPlace E S hS (-f))) = v (-f) from
            (hv1 (-f) (neg_ne_zero.mpr hf)).symm,
          Valuation.map_neg]
      exact hv1 f hf
    exact neg_injective (WithZero.exp_inj.mp key)

/-- The order of a fifth power. -/
lemma ord_pow_five (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g))) (f : Work.MotC2.Func E) :
    ordOfPlace E S hS (f ^ 5) = 5 * ordOfPlace E S hS f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_pow (by norm_num : (5 : ℕ) ≠ 0), ordOfPlace_zero E S hS]
    norm_num
  · have hpq : f ^ 4 * f = f ^ 5 := by ring
    have h22 : f ^ 2 * f ^ 2 = f ^ 4 := by ring
    have hsq : f ^ 2 = f * f := by ring
    rw [← hpq, ord_mul E S hS v hv1 _ _ (pow_ne_zero 4 hf) hf, ← h22,
      ord_mul E S hS v hv1 _ _ (pow_ne_zero 2 hf) (pow_ne_zero 2 hf), hsq,
      ord_mul E S hS v hv1 _ _ hf hf]
    first | refl_ring1 | ring

/-- The ultrametric inequality for the order at `S`. -/
lemma ord_add (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g)))
    (f g : Work.MotC2.Func E) (hfg : f + g ≠ 0) :
    min (ordOfPlace E S hS f) (ordOfPlace E S hS g) ≤ ordOfPlace E S hS (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_add, ordOfPlace_zero E S hS]
    exact min_le_right _ _
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero, ordOfPlace_zero E S hS]
    exact min_le_left _ _
  have key : WithZero.exp (-(ordOfPlace E S hS (f + g)))
      ≤ WithZero.exp (-(min (ordOfPlace E S hS f) (ordOfPlace E S hS g))) := by
    calc WithZero.exp (-(ordOfPlace E S hS (f + g)))
        = v (f + g) := (hv1 (f + g) hfg).symm
      _ ≤ max (v f) (v g) := Valuation.map_add v f g
      _ = WithZero.exp (max (-(ordOfPlace E S hS f)) (-(ordOfPlace E S hS g))) := by
            rw [hv1 f hf, hv1 g hg, ← exp_max_int]
      _ = WithZero.exp (-(min (ordOfPlace E S hS f) (ordOfPlace E S hS g))) := by
            rw [max_neg_neg]
  have := WithZero.exp_le_exp.mp key
  linarith

/-- If `f` has strictly smaller order than `g` then the order of `f + g` is the order of `f`. -/
lemma ord_add_eq_of_lt (E : WeierstrassCurve N) (S : Subalgebra N (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)))
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(ordOfPlace E S hS g)))
    (f g : Work.MotC2.Func E) (hf : f ≠ 0)
    (h : ordOfPlace E S hS f < ordOfPlace E S hS g) :
    ordOfPlace E S hS (f + g) = ordOfPlace E S hS f := by
  have hfg : f + g ≠ 0 := by
    intro h0
    have hg : g = -f := eq_neg_of_add_eq_zero_right h0
    rw [hg, ord_neg E S hS v hv1 f] at h
    exact lt_irrefl _ h
  refine le_antisymm ?_ ?_
  · by_contra hc
    rw [not_le] at hc
    have hsum : (f + g) + (-g) = f := by ring
    have h2 := ord_add E S hS v hv1 (f + g) (-g) (by rw [hsum]; exact hf)
    rw [hsum, ord_neg E S hS v hv1 g] at h2
    have : ordOfPlace E S hS f < min (ordOfPlace E S hS (f + g)) (ordOfPlace E S hS g) :=
      lt_min hc h
    linarith
  · exact le_trans (le_of_eq (min_eq_left (le_of_lt h)).symm)
      (ord_add E S hS v hv1 f g hfg)

end DerivPoleAux

open DerivPoleAux
open Work.MotV

theorem deriv_pole_pos {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]
    (E : WeierstrassCurve N) (f : Polynomial N) (hf2 : 2 ≤ f.natDegree) (hf5 : ¬ 5 ∣ f.natDegree)
    (r : Work.MotC2.Func E)
    (hr : ∀ v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn N v → 1 < v r →
      ∃ u, v (Polynomial.aeval r f - (u ^ 5 - u)) ≤ 1)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    (v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ))) (hv : Work.MotV.TrivOn N v)
    (hv1 : ∀ g : Work.MotC2.Func E, g ≠ 0 →
      v g = WithZero.exp (-(Work.MotV.ordOfPlace E S hS g)))
    (ha : Work.MotV.ordOfPlace E S hS (Polynomial.aeval r f) =
      f.natDegree * Work.MotV.ordOfPlace E S hS r)
    (hb : Work.MotV.ordOfPlace E S hS (Polynomial.aeval r f.derivative) =
      (f.natDegree - 1) * Work.MotV.ordOfPlace E S hS r)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hchain : D (Polynomial.aeval r f) = Polynomial.aeval r f.derivative * D r)
    (hD : ∀ g : Work.MotC2.Func E, g ∈ S → D g ∈ S)
    (hD2 : ∀ g : Work.MotC2.Func E, g ∉ S →
      Work.MotV.ordOfPlace E S hS g - 1 ≤ Work.MotV.ordOfPlace E S hS (D g))
    (hDr : D r ≠ 0)
    (hh : Work.MotV.ordOfPlace E S hS r < 0) :
    0 < Work.MotV.ordOfPlace E S hS (D r) := by
  classical
  -- `r` has a pole at the place of `v`, so `hr` applies
  have hrpole : 1 < v r := (one_lt_iff E S hS v hv1 r).mpr hh
  obtain ⟨u, hu⟩ := hr v hv hrpole
  set s : Work.MotC2.Func E := Polynomial.aeval r f - (u ^ 5 - u) with hsdef
  -- the Artin–Schreier residual function has no pole at `S`
  have hs : 0 ≤ ordOfPlace E S hS s := by
    rcases eq_or_ne s 0 with hs0 | hs0
    · rw [hs0, ordOfPlace_zero E S hS]
    · exact (le_one_iff E S hS v hv1 s).mp (by simpa [hsdef] using hu)
  -- basic numerics of the degree of `f`
  have hd2 : (2 : ℤ) ≤ (f.natDegree : ℤ) := by exact_mod_cast hf2
  have hdpos : (0 : ℤ) < (f.natDegree : ℤ) := by linarith
  have hdnot : ¬ (5 : ℤ) ∣ (f.natDegree : ℤ) :=
    fun hc => hf5 (Int.natCast_dvd_natCast.mp hc)
  have hAneg : ordOfPlace E S hS (Polynomial.aeval r f) < 0 := by
    rw [ha]
    exact mul_neg_of_pos_of_neg hdpos hh
  by_cases hu0 : 0 ≤ ordOfPlace E S hS u
  · -- `u` has no pole at `S`, so `f(r) = (u⁵ - u) + s` has no pole: contradiction
    exfalso
    have hc : 0 ≤ ordOfPlace E S hS (u ^ 5 - u) := by
      rcases eq_or_ne (u ^ 5 - u) 0 with h0 | h0
      · rw [h0, ordOfPlace_zero E S hS]
      · have h1 : 0 ≤ ordOfPlace E S hS (u ^ 5) := by
          rw [ord_pow_five E S hS v hv1 u]
          exact mul_nonneg (by norm_num) hu0
        have h2 : 0 ≤ ordOfPlace E S hS (-u) := by
          rw [ord_neg E S hS v hv1 u]
          exact hu0
        have h3 := ord_add E S hS v hv1 (u ^ 5) (-u) (by simpa [sub_eq_add_neg] using h0)
        rw [show u ^ 5 + -u = u ^ 5 - u from by ring] at h3
        exact le_trans (le_min h1 h2) h3
    have hsplit : Polynomial.aeval r f = (u ^ 5 - u) + s := by rw [hsdef]; ring
    rw [hsplit] at hAneg
    rcases eq_or_ne ((u ^ 5 - u) + s) 0 with h0 | h0
    · rw [h0, ordOfPlace_zero E S hS] at hAneg
      exact absurd hAneg (lt_irrefl 0)
    · have h4 : 0 ≤ ordOfPlace E S hS ((u ^ 5 - u) + s) :=
        le_trans (le_min hc hs) (ord_add E S hS v hv1 (u ^ 5 - u) s h0)
      linarith
  · -- `u` has a pole at `S`
    rw [not_le] at hu0
    have hu_ne : u ≠ 0 := by
      intro h
      rw [h, ordOfPlace_zero E S hS] at hu0
      exact lt_irrefl 0 hu0
    -- the ramification equation
    have h5u : ordOfPlace E S hS (u ^ 5) = 5 * ordOfPlace E S hS u :=
      ord_pow_five E S hS v hv1 u
    have hlt : ordOfPlace E S hS (u ^ 5) < ordOfPlace E S hS (-u) := by
      rw [h5u, ord_neg E S hS v hv1 u]
      linarith
    have hadd : u ^ 5 + -u = u ^ 5 - u := by ring
    have hsub_eq : ordOfPlace E S hS (u ^ 5 - u) = 5 * ordOfPlace E S hS u := by
      have h := ord_add_eq_of_lt E S hS v hv1 (u ^ 5) (-u) (pow_ne_zero 5 hu_ne) hlt
      rw [hadd, h5u] at h
      exact h
    have hsub_ne : u ^ 5 - u ≠ 0 := by
      intro h0
      have hsr : s = Polynomial.aeval r f := by rw [hsdef, h0]; ring
      rw [hsr, ha] at hs
      have : (f.natDegree : ℤ) * ordOfPlace E S hS r < 0 := mul_neg_of_pos_of_neg hdpos hh
      linarith
    have hAf : ordOfPlace E S hS (Polynomial.aeval r f) = ordOfPlace E S hS (u ^ 5 - u) := by
      have hsplit : Polynomial.aeval r f = (u ^ 5 - u) + s := by rw [hsdef]; ring
      rw [hsplit]
      exact ord_add_eq_of_lt E S hS v hv1 (u ^ 5 - u) s hsub_ne
        (by rw [hsub_eq]; linarith)
    have hram : (f.natDegree : ℤ) * ordOfPlace E S hS r = 5 * ordOfPlace E S hS u := by
      rw [← ha, hAf, hsub_eq]
    have h5dvd : (5 : ℤ) ∣ ordOfPlace E S hS r := by
      have hdvd : (5 : ℤ) ∣ (f.natDegree : ℤ) * ordOfPlace E S hS r :=
        ⟨ordOfPlace E S hS u, by rw [hram]⟩
      rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp hdvd with h' | h'
      · exact absurd h' hdnot
      · exact h'
    have hn5 : ordOfPlace E S hS r ≤ -5 := by
      obtain ⟨k, hk⟩ := h5dvd
      have hklt : k < 0 := by nlinarith [hk, hh]
      omega
    have hu2 : ordOfPlace E S hS u ≤ -2 := by nlinarith [hram, hn5, hd2]
    -- the derivative of the Artin–Schreier relation
    have hu5D : D (u ^ 5 - u) = -D u := by
      have h1 : u ^ 5 - u
          = Polynomial.aeval u (Polynomial.X ^ 5 - Polynomial.X : Polynomial N) := by
        simp
      rw [h1, Derivation.map_aeval]
      have h2 : Polynomial.derivative (Polynomial.X ^ 5 - Polynomial.X : Polynomial N)
          = Polynomial.C 5 * Polynomial.X ^ 4 - 1 := by
        rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
        norm_num
      rw [h2, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one]
      rw [smul_eq_mul]
      have hCharP : CharP (Work.MotC2.Func E) 5 :=
        charP_of_injective_algebraMap (algebraMap N (Work.MotC2.Func E)).injective 5
      have h5 : (algebraMap N (Work.MotC2.Func E)) (5 : N) = 0 := by
        rw [show (5 : N) = ((5 : ℕ) : N) from by norm_num, map_natCast]
        exact CharP.cast_eq_zero (Work.MotC2.Func E) 5
      rw [h5]
      first | refl_ring1 | ring
    have hDsum : D (Polynomial.aeval r f) = D (u ^ 5 - u) + D s := by
      conv_lhs => rw [show Polynomial.aeval r f = (u ^ 5 - u) + s from by rw [hsdef]; ring]
      exact Derivation.map_add D _ _
    have hrel : Polynomial.aeval r f.derivative * D r = -D u + D s := by
      calc Polynomial.aeval r f.derivative * D r = D (Polynomial.aeval r f) := hchain.symm
        _ = D (u ^ 5 - u) + D s := hDsum
        _ = -D u + D s := by rw [hu5D]
    -- orders of the two constituents
    have hA'ne : Polynomial.aeval r f.derivative ≠ 0 := by
      intro h0
      have hpos : (0 : ℤ) < (f.natDegree : ℤ) - 1 := by
        have : 2 ≤ f.natDegree := hf2
        omega
      rw [h0, ordOfPlace_zero E S hS] at hb
      exact (mul_ne_zero (ne_of_gt hpos) (ne_of_lt hh)) hb.symm
    have hDf : ordOfPlace E S hS (Polynomial.aeval r f.derivative * D r)
        = ((f.natDegree : ℤ) - 1) * ordOfPlace E S hS r
          + ordOfPlace E S hS (D r) := by
      rw [ord_mul E S hS v hv1 _ _ hA'ne hDr, hb]
    have hDu : ordOfPlace E S hS u - 1 ≤ ordOfPlace E S hS (D u) :=
      hD2 u (notMem_of_neg E S hS hu0)
    have hDs : ordOfPlace E S hS u - 1 ≤ ordOfPlace E S hS (D s) := by
      by_cases hsmem : s ∈ S
      · have h1 := ordOfPlace_nonneg_of_mem E S hS (hD s hsmem)
        linarith
      · have h1 := hD2 s hsmem
        linarith
    have hneg : ordOfPlace E S hS (-D u) = ordOfPlace E S hS (D u) := by
      rw [show -D u = -(D u) from rfl]
      exact ord_neg E S hS v hv1 (D u)
    have key : ordOfPlace E S hS u - 1 ≤ ordOfPlace E S hS (-D u + D s) := by
      rcases eq_or_ne (-D u + D s) 0 with h0 | h0
      · rw [h0, ordOfPlace_zero E S hS]
        linarith
      · have hm : min (ordOfPlace E S hS (D u)) (ordOfPlace E S hS (D s))
            ≤ ordOfPlace E S hS (-D u + D s) := by
          have h := ord_add E S hS v hv1 (-D u) (D s) h0
          rwa [hneg] at h
        exact le_trans (le_min hDu hDs) hm
    have hfin : ((f.natDegree : ℤ) - 1) * ordOfPlace E S hS r
          + ordOfPlace E S hS (D r) = ordOfPlace E S hS (-D u + D s) := by
      rw [← hDf, hrel]
    nlinarith [hram, hn5, hd2, hfin, key]

end Work.MotV5
