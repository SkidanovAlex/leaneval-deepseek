import Mathlib

/-!
# Integer common divisor with integer quotients and no common complex roots

Feeds `lem:squarefree_nocommon` (reduced form, `Submission.NocommonCore`): in
`lem:second_squeeze` and `thm:squarefree` (GON.tex) one must, for a family
`Q : Fin (K+1) → ℤ[Y]` of nonzero integer polynomials, divide out the common
(greatest) divisor `G` so that the quotients `S i := Q i / G` are integer
polynomials with NO common complex root.  This module constructs `G, S`.

## Mathematical proof route

1. Map to ℚ: `Qq i := (Q i).map (algebraMap ℤ ℚ)`.  Over the field ℚ,
   `ℚ[Y]` is a EuclideanDomain, hence a (normalized) GCD monoid.  Let
   `Gq := gcd of the family (Qq i)` (iterate the binary `gcd` right-to-left
   over `Fin (K+1)`, or use any equivalent formulation; prove the two standard
   properties by induction on the iteration):
   (i)  `∀ i, Gq ∣ Qq i` in ℚ[Y]  (write `Qq i = Gq * Tq i`);
   (ii) any common divisor `H` of all the `Qq i` (in ℚ[Y]) divides `Gq`.
   In particular `deg Gq` is the maximal degree of a common divisor.
   Note `Gq ≠ 0` (it divides a nonzero polynomial, or the gcd of nonzero
   elements is nonzero: `gcd_ne_zero_of_left`-type).

2. From (i), over ℚ each quotient `Tq i = Qq i / Gq` lies in `ℚ[Y]`.  Prove:
   `Tq i ∈ ℤ[Y]` for every `i`.  Route: write the monic-normalized `Gq` as
   `Gq = (1/d) * G̃` where `d ≥ 1` is the least positive integer with
   `d * Gq ∈ ℤ[Y]` and `G̃ := d·Gq` is PRIMITIVE (`Polynomial.IsPrimitive` /
   `content`-normalized; ℤ is a `NormalizedGCDMonoid`, `Polynomial.content` is
   available).  [Concretely: take `d` = lcm over `j` of the denominators
   `Rat.den (Gq.coeff j)` of the coefficients; or use
   `Polynomial.IntegralNormalization`/`content`; any explicit construction is
   fine.]  Then `Q i = G̃ * ((Tq i)/d)` with `Q i ∈ ℤ[Y]` and `G̃` primitive
   integer; Gauss's lemma (a primitive integer polynomial that divides an
   integer polynomial over ℚ divides it over ℤ — e.g. via `Polynomial.content`
   and `content_mul`, or the existing Gauss lemma API) gives
   `(Tq i)/d ∈ ℤ[Y]`.

3. Set `G := G̃ ∈ ℤ[Y]` and `S i := (Q i) / G ∈ ℤ[Y]` (the quotient computed
   over ℚ, shown integer in step 2).  Then `Q i = G * (S i)` holds in ℤ[Y],
   `G ≠ 0` (since `Gq ≠ 0`), and `deg G = deg Gq` (`d ≠ 0`).

4. No common complex root: suppose `z : ℂ` is a common root of all `S i`.
   Let `m` be the (monic, irreducible over ℚ) minimal polynomial of `z` over
   ℚ (if `z` is transcendental this cannot happen: `S i ≠ 0` has only
   algebraic roots; formally: if `S i ≠ 0` and `S i (z) = 0` with `z`
   transcendental, impossible since the roots of a nonzero polynomial are
   algebraic — or simpler: take `m :=` the minimal polynomial when `z` is
   algebraic, else derive a contradiction from `S 0 ≠ 0`).  Since
   `S i ∈ ℤ[Y] ⊂ ℚ[Y]` and `S i (z) = 0`, the minimal polynomial `m ∣ S i` in
   `ℚ[Y]` (`Polynomial.aeval`/`Polynomial.isRoot`-based: `X - C z` does not
   live over ℚ, use `minpoly`).  Hence `Q i = G * S i` is divisible over ℚ by
   `G * m`, so `G * m` is a common divisor of all `Q i` over ℚ with degree
   `deg G + deg m > deg G = deg Gq`, contradicting (ii).  Therefore no common
   complex root exists.
   (To get `S i ≠ 0`: `Q i ≠ 0` and `G ≠ 0` and ℤ[Y] is a domain.)

Deliver exactly the theorem below with axioms ⊆ {propext,
Quot.sound, Classical.choice}.  You may add private helper lemmas in this
file.  Do NOT import any other `Submission.*` module (keep this file
self-contained; `import Mathlib` suffices).
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Submission.GcdInt


lemma int_cast_injective_Q : Function.Injective (algebraMap ℤ ℚ) := by
  exact_mod_cast (Int.cast_injective (α := ℚ))

lemma map_int_poly_injective : Function.Injective
    (Polynomial.map (algebraMap ℤ ℚ) : Polynomial ℤ → Polynomial ℚ) := by
  exact Polynomial.map_injective (algebraMap ℤ ℚ) (int_cast_injective_Q)

/-- Clearing denominators: every nonzero rational polynomial is a rational scalar multiple of the
map of a primitive integer polynomial. -/
lemma exists_primitive_int_multiple (H : Polynomial ℚ) (hH : H ≠ 0) :
    ∃ (h : Polynomial ℤ) (r : ℚ), h.IsPrimitive ∧ r ≠ 0 ∧
      C r * h.map (algebraMap ℤ ℚ) = H := by
  classical
  let g : Polynomial ℤ := IsLocalization.integerNormalization (M := nonZeroDivisors ℤ) (S := ℚ) H
  have hg0 : g ≠ 0 := by
    intro hg
    exact hH ((IsFractionRing.integerNormalization_eq_zero_iff (A := ℤ) (K := ℚ)).mp hg)
  obtain ⟨b, hbM, hbspec⟩ :=
    IsLocalization.integerNormalization_spec (M := nonZeroDivisors ℤ) (S := ℚ) H
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast (mem_nonZeroDivisors_iff_ne_zero.mp hbM)
  have hc0 : (g.content : ℚ) ≠ 0 := by
    exact_mod_cast (mt Polynomial.content_eq_zero_iff.mp hg0)
  refine ⟨g.primPart, (g.content : ℚ) / (b : ℚ), g.isPrimitive_primPart, ?_, ?_⟩
  · exact div_ne_zero hc0 hb0
  · have hmapg : g.map (algebraMap ℤ ℚ) = C (g.content : ℚ) * g.primPart.map (algebraMap ℤ ℚ) := by
      calc
        g.map (algebraMap ℤ ℚ) = (C g.content * g.primPart).map (algebraMap ℤ ℚ) := by
          conv_lhs => rw [g.eq_C_content_mul_primPart]
        _ = (C g.content).map (algebraMap ℤ ℚ) * g.primPart.map (algebraMap ℤ ℚ) := by
          rw [Polynomial.map_mul]
        _ = C (g.content : ℚ) * g.primPart.map (algebraMap ℤ ℚ) := by
          simp
    have hEqC : C (b : ℚ) * H = C (g.content : ℚ) * g.primPart.map (algebraMap ℤ ℚ) := by
      calc
        C (b : ℚ) * H = b • H := by
          rw [Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply ℤ ℚ ℚ[X]]
          rw [← Polynomial.C_eq_algebraMap]
          simp
        _ = g.map (algebraMap ℤ ℚ) := hbspec.symm
        _ = C (g.content : ℚ) * g.primPart.map (algebraMap ℤ ℚ) := hmapg
    have hCb : C (b : ℚ) ≠ (0 : Polynomial ℚ) := C_ne_zero.mpr hb0
    apply mul_left_cancel₀ hCb
    calc
      C (b : ℚ) * (C ((g.content : ℚ) / (b : ℚ)) * g.primPart.map (algebraMap ℤ ℚ))
          = C ((b : ℚ) * ((g.content : ℚ) / (b : ℚ))) * g.primPart.map (algebraMap ℤ ℚ) := by
            rw [← mul_assoc, ← (map_mul C (b : ℚ) ((g.content : ℚ) / (b : ℚ)))]
      _ = C (g.content : ℚ) * g.primPart.map (algebraMap ℤ ℚ) := by
            congr 1
            field_simp [hb0]
      _ = C (b : ℚ) * H := hEqC.symm

/-- If `G` is a greatest common divisor over ℤ (any common ℤ-divisor divides `G`), then any
common divisor over ℚ of the mapped family divides the map of `G`. -/
lemma rat_common_divisor_dvd_int_gcd {ι : Type*} (Q : ι → Polynomial ℤ)
    (G : Polynomial ℤ) (j : ι)
    (hQj : Q j ≠ 0)
    (hGmax : ∀ H : Polynomial ℤ, (∀ i, H ∣ Q i) → H ∣ G) :
    ∀ Hq : Polynomial ℚ, (∀ i, Hq ∣ (Q i).map (algebraMap ℤ ℚ)) →
      Hq ∣ G.map (algebraMap ℤ ℚ) := by
  classical
  intro Hq hH
  by_cases hHq : Hq = 0
  · exfalso
    rcases hH j with ⟨c, hc⟩
    have : (Q j).map (algebraMap ℤ ℚ) = 0 := by
      simpa [hHq] using hc
    exact hQj (map_int_poly_injective (by simpa using this))
  · rcases exists_primitive_int_multiple Hq hHq with ⟨h, r, hprim, hr0, hC⟩
    have hmapdiv : ∀ i, h.map (algebraMap ℤ ℚ) ∣ (Q i).map (algebraMap ℤ ℚ) := fun i => by
      rcases hH i with ⟨u, hu⟩
      refine ⟨C r * u, ?_⟩
      rw [hu, ← hC]
      ring
    have hintdiv : ∀ i, h ∣ Q i := fun i => by
      exact hprim.dvd_of_fraction_map_dvd_fraction_map (p := h) (q := Q i) (hmapdiv i)
    have hG : h ∣ G := hGmax h fun i => hintdiv i
    rcases hG with ⟨w, hw⟩
    let P : Polynomial ℚ := h.map (algebraMap ℤ ℚ)
    have hCR : (C r * C (r⁻¹) : Polynomial ℚ) = 1 := by
      rw [← (map_mul C r r⁻¹), mul_inv_cancel₀ hr0, C_1]
    have hcancel : (C r * P) * (C (r⁻¹) * (map (algebraMap ℤ ℚ) w)) = P * map (algebraMap ℤ ℚ) w := by
      calc
        (C r * P) * (C (r⁻¹) * map (algebraMap ℤ ℚ) w)
            = (C r * C (r⁻¹)) * (P * map (algebraMap ℤ ℚ) w) := by ring
        _ = P * map (algebraMap ℤ ℚ) w := by rw [hCR, one_mul]
    refine ⟨C (r⁻¹) * map (algebraMap ℤ ℚ) w, ?_⟩
    calc
      G.map (algebraMap ℤ ℚ) = P * map (algebraMap ℤ ℚ) w := by
        rw [hw, Polynomial.map_mul]
      _ = (C r * P) * (C (r⁻¹) * map (algebraMap ℤ ℚ) w) := hcancel.symm
      _ = Hq * (C (r⁻¹) * map (algebraMap ℤ ℚ) w) := by rw [hC]

/-- if z is a root (in ℂ) of an integer polynomial S, it is a root of its ℚ-map -/
lemma aeval_int_map_aeval (S : Polynomial ℤ) (z : ℂ) :
    Polynomial.aeval z (S.map (algebraMap ℤ ℚ)) = Polynomial.aeval z S := by
  rw [Polynomial.aeval_map_algebraMap ℚ]

theorem gcd_int_quotient {K : ℕ} (Q : Fin (K + 1) → Polynomial ℤ) (hQ : ∀ i, Q i ≠ 0) :
    ∃ (G : Polynomial ℤ) (S : Fin (K + 1) → Polynomial ℤ),
      G ≠ 0 ∧ (∀ i, Q i = G * S i) ∧
        (∀ z : ℂ, ¬ (∀ i, Polynomial.aeval z (S i) = 0)) := by
  classical
  let G : Polynomial ℤ := Finset.univ.gcd Q
  have hGne : G ≠ 0 := by
    rw [Finset.gcd_ne_zero_iff]
    exact ⟨(0 : Fin (K+1)), by simp, hQ 0⟩
  have hGdvd : ∀ i : Fin (K+1), G ∣ Q i := fun i => by
    apply Finset.gcd_dvd
    simp
  have hGmax : ∀ H : Polynomial ℤ, (∀ i : Fin (K+1), H ∣ Q i) → H ∣ G := fun H hH => by
    exact Finset.dvd_gcd (s := (Finset.univ : Finset (Fin (K+1)))) (f := Q)
      (by intro i hi; exact hH i)
  let S : Fin (K+1) → Polynomial ℤ := fun i => Classical.choose (hGdvd i)
  have hS : ∀ i, Q i = G * S i := fun i => Classical.choose_spec (hGdvd i)
  refine ⟨G, S, hGne, hS, ?_⟩
  intro z hz
  have hS0ne : S 0 ≠ 0 := by
    intro h0
    have : Q 0 = 0 := by simpa [h0] using hS 0
    exact hQ 0 this
  have hSmap_ne : (S 0).map (algebraMap ℤ ℚ) ≠ 0 := by
    intro hm
    exact hS0ne (map_int_poly_injective (by simpa using hm))
  have hz0q : Polynomial.aeval z ((S 0).map (algebraMap ℤ ℚ)) = 0 := by
    rw [aeval_int_map_aeval]
    exact hz 0
  have hzalg : IsAlgebraic ℚ z := ⟨(S 0).map (algebraMap ℤ ℚ), hSmap_ne, hz0q⟩
  have hzint : IsIntegral ℚ z := IsAlgebraic.isIntegral hzalg
  let m : Polynomial ℚ := minpoly ℚ z
  have hm_ne : m ≠ 0 := minpoly.ne_zero hzint
  have hGmap_ne : G.map (algebraMap ℤ ℚ) ≠ 0 := by
    intro hg
    exact hGne (map_int_poly_injective (by simpa using hg))
  have hm_dvd : ∀ i : Fin (K+1), m ∣ (S i).map (algebraMap ℤ ℚ) := fun i => by
    refine minpoly.dvd ℚ z ?_
    rw [aeval_int_map_aeval]
    exact hz i
  let Hq : Polynomial ℚ := G.map (algebraMap ℤ ℚ) * m
  have hHqne : Hq ≠ 0 := mul_ne_zero hGmap_ne hm_ne
  have hHqdiv : ∀ i : Fin (K+1), Hq ∣ (Q i).map (algebraMap ℤ ℚ) := fun i => by
    rcases hm_dvd i with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc
      (Q i).map (algebraMap ℤ ℚ) = (G * S i).map (algebraMap ℤ ℚ) := by rw [hS i]
      _ = G.map (algebraMap ℤ ℚ) * (S i).map (algebraMap ℤ ℚ) := by rw [Polynomial.map_mul]
      _ = G.map (algebraMap ℤ ℚ) * (m * v) := by rw [hv]
      _ = (G.map (algebraMap ℤ ℚ) * m) * v := by rw [mul_assoc]
  have hfinal : Hq ∣ G.map (algebraMap ℤ ℚ) :=
    rat_common_divisor_dvd_int_gcd Q G (0 : Fin (K+1)) (hQ 0) hGmax Hq hHqdiv
  rcases hfinal with ⟨c, hc⟩
  have hmul1 : m * c = 1 := by
    apply mul_left_cancel₀ hGmap_ne
    calc
      G.map (algebraMap ℤ ℚ) * (m * c) = (G.map (algebraMap ℤ ℚ) * m) * c := by rw [mul_assoc]
      _ = G.map (algebraMap ℤ ℚ) := hc.symm
      _ = G.map (algebraMap ℤ ℚ) * 1 := by rw [mul_one]
  have hm_unit : IsUnit m := by
    exact isUnit_iff_exists_inv.mpr ⟨c, hmul1⟩
  exact (minpoly.not_isUnit ℚ z) (by simpa [m] using hm_unit)

end Submission.GcdInt
