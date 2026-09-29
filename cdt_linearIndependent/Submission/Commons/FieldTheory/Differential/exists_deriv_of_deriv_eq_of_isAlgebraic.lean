import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# "No new integration" for algebraic elements

Let `L/K` be an extension of characteristic-zero fields carrying compatible derivations.  If
`x ∈ L` is algebraic over `K` and its derivative is the image of an element `a ∈ K`, then `a` is
itself the derivative of an element of `K`.

The proof is the classical one: with `P ∈ K[T]` the minimal polynomial of `x` and `P^{(D)}` the
polynomial obtained by differentiating the coefficients of `P`, the polynomial
`Q := P^{(D)} + a · P'` (with `P'` the formal derivative) has degree `< deg P` and satisfies
`aeval x Q = 0`; by minimality `Q = 0`, and comparing the coefficients of `T ^ (deg P - 1)` gives
`a = - (c)' / (deg P)`, where `c` is the second leading coefficient of `P`.
-/

open Polynomial

namespace Commons.FieldTheory.Differential

/-- The coefficient-wise derivative of a monic polynomial lowers its `natDegree` (weakly): if the
leading coefficient is `1`, its derivative is `0`, and all higher coefficients vanish. -/
lemma natDegree_mapCoeffs_le_of_monic {K : Type*} [Field K] [Differential K] (p : K[X])
    (hp : p.Monic) : (Differential.mapCoeffs p).natDegree ≤ p.natDegree - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Differential.coeff_mapCoeffs]
  have hN' : p.natDegree ≤ N := by omega
  rcases lt_or_eq_of_le hN' with h | h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]
  · rw [← h, hp.coeff_natDegree, Derivation.map_one_eq_zero]

/-- **"No new integration" for algebraic elements.**  Let `L/K` be an extension of
characteristic-zero fields carrying compatible derivations.  If `x ∈ L` is algebraic over `K` and
its derivative is the image of an element `a ∈ K`, then `a` is itself the derivative of an element
of `K`.  (Proof idea: let `P ∈ K[T]` be the minimal polynomial of `x` and let `P^{(D)}` be the
polynomial obtained by differentiating the coefficients of `P`; then
`Q := P^{(D)} + a · P'` (with `P'` the formal derivative) has degree `< deg P`, satisfies
`aeval x Q = 0`, hence vanishes by minimality; comparing the coefficients of `T ^ (deg P - 1)`
gives `a = - (c)' / (deg P)` where `c` is the second leading coefficient of `P`, so `a` is the
derivative of `-c / deg P`.) -/
theorem exists_deriv_of_deriv_eq_of_isAlgebraic {K L : Type*} [Field K] [Field L] [Algebra K L]
    [CharZero K] [Differential K] [Differential L] [DifferentialAlgebra K L] {x : L} {a : K}
    (hx : Differential.deriv x = algebraMap K L a) (h : IsAlgebraic K x) :
    ∃ g : K, Differential.deriv g = a := by
  let p : K[X] := minpoly K x
  have hxint : IsIntegral K x := h.isIntegral
  have hp_monic : p.Monic := minpoly.monic hxint
  have hp_aeval : aeval x p = 0 := minpoly.aeval K x
  have hnpos : 0 < p.natDegree := by
    simpa [p] using minpoly.natDegree_pos (A := K) (B := L) hxint
  -- The auxiliary polynomial `Q := P^{(D)} + a · P'` is a root of `x`.
  have hQaeval : aeval x (Differential.mapCoeffs p + a • derivative p) = 0 := by
    have h1 := Differential.deriv_aeval_eq (A := K) (R := L) x p
    rw [hp_aeval, hx, map_zero] at h1
    calc aeval x (Differential.mapCoeffs p + a • derivative p)
        = aeval x (Differential.mapCoeffs p) + a • aeval x (derivative p) := by
          rw [map_add, map_smul]
      _ = aeval x (Differential.mapCoeffs p) + algebraMap K L a * aeval x (derivative p) := by
          rw [Algebra.smul_def]
      _ = 0 := by rw [mul_comm (algebraMap K L a)]; exact h1.symm
  have hdvd : p ∣ Differential.mapCoeffs p + a • derivative p := by
    simpa [p] using minpoly.dvd K x hQaeval
  -- `Q` has degree strictly smaller than `deg P`.
  have hdeg : (Differential.mapCoeffs p + a • derivative p).natDegree ≤ p.natDegree - 1 := by
    calc (Differential.mapCoeffs p + a • derivative p).natDegree
        ≤ max (Differential.mapCoeffs p).natDegree (a • derivative p).natDegree :=
          natDegree_add_le _ _
      _ ≤ max (p.natDegree - 1) (p.natDegree - 1) :=
          max_le_max (natDegree_mapCoeffs_le_of_monic p hp_monic)
            ((natDegree_smul_le a (derivative p)).trans (natDegree_derivative_le p))
      _ = p.natDegree - 1 := max_self _
  have hQ0 : Differential.mapCoeffs p + a • derivative p = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hdvd (lt_of_le_of_lt hdeg (Nat.sub_one_lt (ne_of_gt hnpos)))
  -- Compare coefficients of `T ^ (deg P - 1)`.
  have hcoeff : Differential.deriv (p.coeff (p.natDegree - 1)) + a * (p.natDegree : K) = 0 := by
    have h0 := congrArg (fun q : K[X] => q.coeff (p.natDegree - 1)) hQ0
    simp only [coeff_zero] at h0
    have h1n : (p.natDegree - 1) + 1 = p.natDegree := by omega
    have hcast : ((p.natDegree - 1 : ℕ) : K) + 1 = (p.natDegree : K) := by
      rw [Nat.cast_sub (R := K) (m := 1) (n := p.natDegree) hnpos, Nat.cast_one,
        sub_add_cancel]
    rw [Polynomial.coeff_add, Differential.coeff_mapCoeffs, Polynomial.coeff_smul,
        Polynomial.coeff_derivative, h1n,
        Polynomial.Monic.coeff_natDegree hp_monic, one_mul, hcast, smul_eq_mul] at h0
    exact h0
  have hn0 : (p.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnpos)
  refine ⟨-(p.coeff (p.natDegree - 1) / (p.natDegree : K)), ?_⟩
  have hderivdiv : Differential.deriv (p.coeff (p.natDegree - 1) / (p.natDegree : K))
      = Differential.deriv (p.coeff (p.natDegree - 1)) / (p.natDegree : K) := by
    have h := Derivation.leibniz_div_const (D := Differential.deriv)
      (p.coeff (p.natDegree - 1)) (p.natDegree : K)
      (Derivation.map_natCast Differential.deriv p.natDegree)
    rw [h, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [map_neg, hderivdiv]
  have h2 : Differential.deriv (p.coeff (p.natDegree - 1)) / (p.natDegree : K) = -a := by
    rw [div_eq_iff hn0]
    rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left hcoeff
  rw [h2, neg_neg]

end Commons.FieldTheory.Differential