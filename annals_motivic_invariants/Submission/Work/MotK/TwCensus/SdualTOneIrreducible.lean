import Mathlib
import Submission.Work.MotK.TwCensus.SdualTShape
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sdualT a b 1` is irreducible as soon as its degree-five part is

Target (this file):

```
theorem SdualTOneIrreducible {K : Type} [Field K] (a b : K)
    (hG5 : Irreducible (-a⁵b⁵(x₀⁵+x₁⁵+x₂⁵) + (3a⁴b⁶-a⁹b)x₀²x₁x₂² + (2a⁷b³-a²b⁸)x₀x₁³x₂)) :
    Irreducible (sdualT a b 1)
```

i.e. the *degree-five part* `sdG5 a b` of `sdualT a b 1` is
`-a⁵b⁵(x₀⁵+x₁⁵+x₂⁵) + (3a⁴b⁶-a⁹b)x₀²x₁x₂² + (2a⁷b³-a²b⁸)x₀x₁³x₂` (the def `sdG5` of
`SdualTPrimeGood.lean`, whose body is *literally* the polynomial appearing in `hG5`), and the
hypothesis is exactly `Irreducible (sdG5 a b)`.

## The mathematics

The reduction is the classical "leading form" argument for polynomials over a domain: if
`f = G + L` with `G` homogeneous of degree `d`, `totalDegree L < d` and `G` irreducible, then
`f` is irreducible.

Indeed, if `f = p·q` with `p, q ≠ 0`, then (K a domain) `totalDegree f = totalDegree p +
totalDegree q`, and the degree-`d` homogeneous components multiply:
`homogeneousComponent d (p·q) = homogeneousComponent (totalDegree p) p * homogeneousComponent
(totalDegree q) q` — because in the coefficient sum `(p·q).coeff n = ∑_{a+b=n} p.coeff a * q.coeff b`
with `n.degree = d = totalDegree p + totalDegree q`, the term `p.coeff a * q.coeff b` can only be
nonzero when `a.degree = totalDegree p` and `b.degree = totalDegree q` (otherwise one of the two
degrees exceeds the total degree of its polynomial and the corresponding coefficient vanishes).
Hence `G = top p · top q`, and irreducibility of `G` forces `top p` or `top q` to be a unit; a unit
has total degree `0`, but `top p` is homogeneous of degree `totalDegree p ≠ 0`, so `totalDegree p =
0`, i.e. `p` is a constant, i.e. a unit.

## The degree bookkeeping for `sdualT a b 1`

* `sdualT a b 1 = sdG5 a b + (lower-degree terms)` (from the twelve-term shape `sdualT_explicit`);
* the remainder `sdualT a b 1 - sdG5 a b` is
  `-a⁵b⁵ + (2a³b⁷+a⁸b²)x₀³x₂ + (2a³b⁷+a⁸b²)x₀x₁ - (3a⁶b⁴+ab⁹)x₀²x₁² - (3a⁶b⁴+ab⁹)x₀x₂²
   + (3a⁴b⁶-a⁹b)x₁²x₂ + (2a⁷b³-a²b⁸)x₁x₂³`,
  a sum of seven terms each homogeneous of degree `≤ 4`, so its total degree is `< 5`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MotK.TwCensus

open MvPolynomial

/-! ## §1 The top-degree argument (general, over any domain)

We first record the two elementary facts about `MvPolynomial` that the argument needs.  They are
stated for an arbitrary index type `σ` and an arbitrary field `R`, since they are the reusable
part of this file. -/

/-- **The top-degree parts multiply.**  For `d = totalDegree p + totalDegree q`, the degree-`d`
homogeneous component of `p * q` is the product of the top components of `p` and `q`.

(No hypothesis on `p` and `q` is needed: if `q = 0` both sides vanish.)

Proof by coefficients.  For a multi-index `n` with `n.degree = d`,
`(p*q).coeff n = ∑_{a+b=n} p.coeff a * q.coeff b` (`MvPolynomial.coeff_mul`), and a nonzero term
`p.coeff a * q.coeff b` has `a.degree ≤ totalDegree p`, `b.degree ≤ totalDegree q`; since
`a.degree + b.degree = n.degree = totalDegree p + totalDegree q`, both inequalities are equalities,
which is exactly the coefficient of `(top p * top q).coeff n`. -/
private lemma homogeneousComponent_mul_eq {σ : Type*} [DecidableEq σ] {R : Type*}
    [CommSemiring R] (p q : MvPolynomial σ R) :
    homogeneousComponent (p.totalDegree + q.totalDegree) (p * q) =
      homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  ext n
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  simp only [coeff_homogeneousComponent]
  by_cases hn : Finsupp.degree n = p.totalDegree + q.totalDegree
  · simp only [hn, ↓reduceIte]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : Finsupp.degree x.1 + Finsupp.degree x.2 = p.totalDegree + q.totalDegree := by
      rw [← map_add Finsupp.degree x.1 x.2, hx', hn]
    rcases lt_trichotomy (Finsupp.degree x.1) p.totalDegree with hlt | heq | hgt
    · have hb : q.totalDegree < Finsupp.degree x.2 := by omega
      have hq0 : q.coeff x.2 = 0 := coeff_eq_zero_of_totalDegree_lt hb
      simp [hq0, ne_of_lt hlt]
    · have hb : Finsupp.degree x.2 = q.totalDegree := by omega
      simp [heq, hb]
    · have hp0 : p.coeff x.1 = 0 := coeff_eq_zero_of_totalDegree_lt hgt
      simp [hp0, ne_of_gt hgt]
  · simp only [hn, ↓reduceIte]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hdeg : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree n := by
      rw [← map_add Finsupp.degree x.1 x.2, hx']
    by_cases h1 : Finsupp.degree x.1 = p.totalDegree
    · have h2 : Finsupp.degree x.2 ≠ q.totalDegree := by
        intro h2; apply hn; rw [← hdeg, h1, h2]
      simp [h1, h2]
    · simp [h1]

/-- A nonzero polynomial of total degree `0` is a nonzero constant, hence a unit. -/
private lemma isUnit_of_totalDegree_zero {σ : Type*} {R : Type*} [Field R]
    {r : MvPolynomial σ R} (hr0 : r ≠ 0) (hr : r.totalDegree = 0) : IsUnit r := by
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨r.coeff 0, ?_, (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hr)⟩
  rw [isUnit_iff_ne_zero]
  intro hc0
  exact hr0 (by rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hr, hc0, map_zero])

/-- **An irreducible homogeneous leading form makes the polynomial irreducible.**

If `G` is homogeneous of degree `d` and irreducible, and `totalDegree L < d`, then `G + L`
is irreducible.  (In particular a degree-`0` hypothesis is impossible: a nonzero homogeneous
polynomial of degree `0` is a unit, hence not irreducible, so `d ≠ 0`.) -/
theorem irreducible_of_isHomogeneous_add {σ : Type*} [DecidableEq σ] {R : Type*} [Field R]
    {G L : MvPolynomial σ R} {d : ℕ}
    (hG : G.IsHomogeneous d) (hL : L.totalDegree < d) (hirr : Irreducible G) :
    Irreducible (G + L) := by
  have hG0 : G ≠ 0 := hirr.ne_zero
  have hGd : G.totalDegree = d := hG.totalDegree hG0
  have hlt : L.totalDegree < G.totalDegree := by rw [hGd]; exact hL
  have hfdeg : (G + L).totalDegree = d := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt hlt, hGd]
  have hd0 : d ≠ 0 := by rintro rfl; exact Nat.not_lt_zero _ hL
  have hf0 : G + L ≠ 0 := by
    intro h; rw [h, totalDegree_zero] at hfdeg; exact hd0 hfdeg.symm
  refine ⟨?_, ?_⟩
  · intro hu
    have h : (G + L).totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hfdeg] at h
    exact hd0 h
  · intro p q hpq
    have hp0 : p ≠ 0 := by rintro rfl; rw [zero_mul] at hpq; exact hf0 hpq
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hf0 hpq
    have hdeg : p.totalDegree + q.totalDegree = d := by
      have h := MvPolynomial.totalDegree_mul_of_isDomain hp0 hq0
      rw [← hpq, hfdeg] at h
      exact h.symm
    by_cases hp1 : p.totalDegree = 0
    · exact Or.inl (isUnit_of_totalDegree_zero hp0 hp1)
    by_cases hq1 : q.totalDegree = 0
    · exact Or.inr (isUnit_of_totalDegree_zero hq0 hq1)
    exfalso
    have hcomp : homogeneousComponent d (G + L) = G := by
      rw [map_add, homogeneousComponent_eq_self hG, homogeneousComponent_eq_zero d L hL, add_zero]
    have hkey : homogeneousComponent d (p * q) =
        homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
      rw [← hdeg]; exact homogeneousComponent_mul_eq p q
    have hG' : G = homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
      rw [← hcomp, hpq, hkey]
    rcases hirr.isUnit_or_isUnit hG' with h | h
    · have h1 : (homogeneousComponent p.totalDegree p).totalDegree = p.totalDegree :=
        (homogeneousComponent_isHomogeneous p.totalDegree p).totalDegree h.ne_zero
      have h2 : (homogeneousComponent p.totalDegree p).totalDegree = 0 :=
        (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h).2
      exact hp1 (by rw [← h1, h2])
    · have h1 : (homogeneousComponent q.totalDegree q).totalDegree = q.totalDegree :=
        (homogeneousComponent_isHomogeneous q.totalDegree q).totalDegree h.ne_zero
      have h2 : (homogeneousComponent q.totalDegree q).totalDegree = 0 :=
        (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h).2
      exact hq1 (by rw [← h1, h2])

/-! ## §2 The two inputs about `sdG5`

`sdG5 a b` is the degree-five part of `sdualT a b 1` (definition in `SdualTPrimeGood.lean`); here
we show that it is homogeneous of degree `5` and that the remainder has total degree `< 5`. -/

/-- Numerals in a polynomial ring are homogeneous of degree `0`. -/
private lemma isHomogeneous_natCast {σ : Type*} {R : Type*} [CommSemiring R] (n : ℕ) :
    (n : MvPolynomial σ R).IsHomogeneous 0 := by
  induction n with
  | zero => simpa using (isHomogeneous_zero σ R 0)
  | succ n ih => rw [Nat.cast_succ]; exact ih.add (isHomogeneous_one σ R)

/-- `sdG5 a b` is homogeneous of degree `5` — every monomial is
`-(C a)^5(C b)^5 · xᵢ⁵`, `(3(C a)^4(C b)^6 - (C a)^9(C b)) · x₀²x₁x₂²` or
`(2(C a)^7(C b)^3 - (C a)^2(C b)^8) · x₀x₁³x₂`, of degree `5`, `2+1+2 = 5` and `1+3+1 = 5`. -/
private lemma sdG5_isHomogeneous {K : Type} [Field K] (a b : K) :
    (sdG5 a b).IsHomogeneous 5 := by
  have hCa : (C a : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_C (σ := Fin 3) a
  have hCb : (C b : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_C (σ := Fin 3) b
  have hc1 : (-((C a) ^ 5 * (C b) ^ 5) : MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    (((hCa.pow 5).mul (hCb.pow 5))).neg
  have hm1 : ((X 0) ^ 5 + (X 1) ^ 5 + (X 2) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    ((isHomogeneous_X_pow (R := K) 0 5).add (isHomogeneous_X_pow (R := K) 1 5)).add
      (isHomogeneous_X_pow (R := K) 2 5)
  have hc2 : (3 * (C a) ^ 4 * (C b) ^ 6 - (C a) ^ 9 * (C b) :
      MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    (((isHomogeneous_natCast (σ := Fin 3) (R := K) 3).mul (hCa.pow 4)).mul (hCb.pow 6)).sub
      ((hCa.pow 9).mul hCb)
  have hc3 : (2 * (C a) ^ 7 * (C b) ^ 3 - (C a) ^ 2 * (C b) ^ 8 :
      MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    (((isHomogeneous_natCast (σ := Fin 3) (R := K) 2).mul (hCa.pow 7)).mul (hCb.pow 3)).sub
      ((hCa.pow 2).mul (hCb.pow 8))
  have t1 := hc1.mul hm1
  have t2 := ((hc2.mul (isHomogeneous_X_pow (R := K) 0 2)).mul (isHomogeneous_X (R := K) 1)).mul
      (isHomogeneous_X_pow (R := K) 2 2)
  have t3 := ((hc3.mul (isHomogeneous_X (R := K) 0)).mul (isHomogeneous_X_pow (R := K) 1 3)).mul
      (isHomogeneous_X (R := K) 2)
  rw [sdG5]
  exact (t1.add t2).add t3

/-- `t.totalDegree ≤ 4` from `t` homogeneous of degree `n ≤ 4`. -/
private lemma totalDegree_le_four {K : Type} [CommRing K] {f : MvPolynomial (Fin 3) K} {n : ℕ}
    (h : f.IsHomogeneous n) (hn : n ≤ 4) : f.totalDegree ≤ 4 :=
  h.totalDegree_le.trans hn

/-- If seven polynomials have total degree `≤ 4`, so does their signed sum
`t₁ + t₂ + t₃ - t₄ - t₅ + t₆ + t₇` (the parenthesisation is the left-nested one). -/
private lemma totalDegree_le_of_pieces {K : Type} [CommRing K]
    {t1 t2 t3 t4 t5 t6 t7 : MvPolynomial (Fin 3) K}
    (h1 : t1.totalDegree ≤ 4) (h2 : t2.totalDegree ≤ 4) (h3 : t3.totalDegree ≤ 4)
    (h4 : t4.totalDegree ≤ 4) (h5 : t5.totalDegree ≤ 4) (h6 : t6.totalDegree ≤ 4)
    (h7 : t7.totalDegree ≤ 4) :
    (t1 + t2 + t3 - t4 - t5 + t6 + t7).totalDegree ≤ 4 := by
  have b1 : (t1 + t2).totalDegree ≤ 4 := (totalDegree_add t1 t2).trans (max_le h1 h2)
  have b2 : (t1 + t2 + t3).totalDegree ≤ 4 := (totalDegree_add _ t3).trans (max_le b1 h3)
  have b3 : (t1 + t2 + t3 - t4).totalDegree ≤ 4 := (totalDegree_sub _ t4).trans (max_le b2 h4)
  have b4 : (t1 + t2 + t3 - t4 - t5).totalDegree ≤ 4 :=
    (totalDegree_sub _ t5).trans (max_le b3 h5)
  have b5 : (t1 + t2 + t3 - t4 - t5 + t6).totalDegree ≤ 4 :=
    (totalDegree_add _ t6).trans (max_le b4 h6)
  have b6 : (t1 + t2 + t3 - t4 - t5 + t6 + t7).totalDegree ≤ 4 :=
    (totalDegree_add _ t7).trans (max_le b5 h7)
  exact b6

/-- **The degree bookkeeping.**  Subtracting the degree-five part `sdG5 a b` from `sdualT a b 1`
leaves the seven lower-degree monomials of `sdualT_explicit` (at `h = 1`), each of degree `≤ 4`. -/
private lemma sdualT_one_sub_sdG5_totalDegree {K : Type} [Field K] (a b : K) :
    (Work.MotK.TGen.sdualT a b 1 - sdG5 a b).totalDegree < 5 := by
  have hL : Work.MotK.TGen.sdualT a b 1 - sdG5 a b =
      -((C a) ^ 5 * (C b) ^ 5)
        + (2 * (C a) ^ 3 * (C b) ^ 7 + (C a) ^ 8 * (C b) ^ 2) * (X 0) ^ 3 * X 2
        + (2 * (C a) ^ 3 * (C b) ^ 7 + (C a) ^ 8 * (C b) ^ 2) * X 0 * X 1
        - (3 * (C a) ^ 6 * (C b) ^ 4 + (C a) * (C b) ^ 9) * (X 0) ^ 2 * (X 1) ^ 2
        - (3 * (C a) ^ 6 * (C b) ^ 4 + (C a) * (C b) ^ 9) * X 0 * (X 2) ^ 2
        + (3 * (C a) ^ 4 * (C b) ^ 6 - (C a) ^ 9 * (C b)) * (X 1) ^ 2 * X 2
        + (2 * (C a) ^ 7 * (C b) ^ 3 - (C a) ^ 2 * (C b) ^ 8) * X 1 * (X 2) ^ 3 := by
    rw [sdualT_explicit, sdG5]
    simp only [MvPolynomial.C_1, one_pow, one_mul, mul_one]
    first | refl_ring1 | ring
  have hCa : (C a : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_C (σ := Fin 3) a
  have hCb : (C b : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_C (σ := Fin 3) b
  have h2 : (2 : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_natCast 2
  have h3 : (3 : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_natCast 3
  have hc2 : (2 * (C a) ^ 3 * (C b) ^ 7 + (C a) ^ 8 * (C b) ^ 2 :
      MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    ((h2.mul (hCa.pow 3)).mul (hCb.pow 7)).add ((hCa.pow 8).mul (hCb.pow 2))
  have hc4 : (3 * (C a) ^ 6 * (C b) ^ 4 + (C a) * (C b) ^ 9 :
      MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    ((h3.mul (hCa.pow 6)).mul (hCb.pow 4)).add (hCa.mul (hCb.pow 9))
  have hc6 : (3 * (C a) ^ 4 * (C b) ^ 6 - (C a) ^ 9 * (C b) :
      MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    ((h3.mul (hCa.pow 4)).mul (hCb.pow 6)).sub ((hCa.pow 9).mul hCb)
  have hc7 : (2 * (C a) ^ 7 * (C b) ^ 3 - (C a) ^ 2 * (C b) ^ 8 :
      MvPolynomial (Fin 3) K).IsHomogeneous 0 :=
    ((h2.mul (hCa.pow 7)).mul (hCb.pow 3)).sub ((hCa.pow 2).mul (hCb.pow 8))
  rw [hL]
  refine lt_of_le_of_lt (totalDegree_le_of_pieces ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by norm_num)
  · exact totalDegree_le_four (((hCa.pow 5).mul (hCb.pow 5)).neg) (by norm_num)
  · exact totalDegree_le_four
      ((hc2.mul (isHomogeneous_X_pow (R := K) 0 3)).mul (isHomogeneous_X (R := K) 2)) (by norm_num)
  · exact totalDegree_le_four
      ((hc2.mul (isHomogeneous_X (R := K) 0)).mul (isHomogeneous_X (R := K) 1)) (by norm_num)
  · exact totalDegree_le_four
      ((hc4.mul (isHomogeneous_X_pow (R := K) 0 2)).mul
        (isHomogeneous_X_pow (R := K) 1 2)) (by norm_num)
  · exact totalDegree_le_four
      ((hc4.mul (isHomogeneous_X (R := K) 0)).mul (isHomogeneous_X_pow (R := K) 2 2)) (by norm_num)
  · exact totalDegree_le_four
      ((hc6.mul (isHomogeneous_X_pow (R := K) 1 2)).mul (isHomogeneous_X (R := K) 2)) (by norm_num)
  · exact totalDegree_le_four
      ((hc7.mul (isHomogeneous_X (R := K) 1)).mul (isHomogeneous_X_pow (R := K) 2 3)) (by norm_num)

/-! ## §3 Transfer from `MvPolynomial ℕ K` to `MvPolynomial (Fin 3) K`

There is a formalisation trap in the statement of the target: `hG5` is the irreducibility of

`-a⁵b⁵(x₀⁵+x₁⁵+x₂⁵) + (3a⁴b⁶-a⁹b)x₀²x₁x₂² + (2a⁷b³-a²b⁸)x₀x₁³x₂`

where the *index type* of the polynomial ring is **not pinned down**: the variables are written
`MvPolynomial.X 0`, `MvPolynomial.X 1`, `MvPolynomial.X 2`, and the numerals default to `ℕ`, so the
hypothesis lives in `MvPolynomial ℕ K`, while the conclusion `Irreducible (sdualT a b 1)` lives in
`MvPolynomial (Fin 3) K`.

The bridge is the injective `K`-algebra map

`MvPolynomial.rename (fun i : Fin 3 => (i : ℕ)) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial ℕ K`,

whose image is exactly the "first three variables" subalgebra; it has a left inverse

`natRetract : MvPolynomial ℕ K →ₐ[K] MvPolynomial (Fin 3) K`, `X n ↦ X n` for `n < 3` and `X n ↦ 0`
for `n ≥ 3`.  A ring hom with a left inverse reflects `Irreducible`: if `f = g·h` in `A` with both
factors non-units, then `ι f = ι g · ι h` in `B`, and no `ι g` can be a unit — applying `φ` to an
inverse would exhibit `g = φ (ι g)` as a unit.

(Formally: a unit `u` of `B` with `↑u = ι g` gives `φ ↑u = φ (ι g) = g`, so `g` is a unit as the
image of the unit `u`.) -/

/-- **A ring hom with a left inverse reflects irreducibility.** -/
private lemma irreducible_of_comp_eq_id {A B : Type*} [CommRing A] [CommRing B]
    (ι : A →+* B) (φ : B →+* A) (hφι : ∀ x : A, φ (ι x) = x) {f : A}
    (h : Irreducible (ι f)) : Irreducible f := by
  refine ⟨fun hu => h.not_isUnit (hu.map ι), ?_⟩
  intro g g' hgg'
  have hmul : ι f = ι g * ι g' := by rw [← map_mul, hgg']
  rcases h.isUnit_or_isUnit hmul with h1 | h1
  · left
    rcases h1 with ⟨u, hu⟩
    have hgue : φ (u : B) = g := by rw [hu, hφι g]
    rw [← hgue]
    exact (u.isUnit).map φ
  · right
    rcases h1 with ⟨u, hu⟩
    have hgue : φ (u : B) = g' := by rw [hu, hφι g']
    rw [← hgue]
    exact (u.isUnit).map φ

/-- The composite `Fin 3 → ℕ` (the inclusion of the first three variables). -/
private def fin3ToNat (i : Fin 3) : ℕ := (i : ℕ)

/-- `X n` for `n < 3`, and `0` otherwise: the image of the `n`-th variable under the retraction. -/
private noncomputable def natToFin3 (K : Type) [Field K] (n : ℕ) : MvPolynomial (Fin 3) K :=
  if h : n < 3 then MvPolynomial.X ⟨n, h⟩ else 0

/-- The `K`-algebra retraction `MvPolynomial ℕ K →ₐ[K] MvPolynomial (Fin 3) K` killing all
variables of index `≥ 3`. -/
private noncomputable def natRetract (K : Type) [Field K] :
    MvPolynomial ℕ K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval (natToFin3 K)

/-- The retraction is a left inverse of `MvPolynomial.rename fin3ToNat`. -/
private lemma natRetract_comp_rename (K : Type) [Field K] :
    (natRetract K).comp (MvPolynomial.rename fin3ToNat)
      = AlgHom.id K (MvPolynomial (Fin 3) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.rename_X, natRetract, MvPolynomial.aeval_X,
    natToFin3, fin3ToNat]
  simp only [show (i : ℕ) < 3 from i.isLt, ↓reduceDIte]

/-- **`rename fin3ToNat` sends `sdG5 a b` to the polynomial appearing in `hG5`** (the hypothesis
lives in `MvPolynomial ℕ K`, see the section docstring). -/
private lemma rename_sdG5 {K : Type} [Field K] (a b : K) :
    (MvPolynomial.rename fin3ToNat (sdG5 a b) : MvPolynomial ℕ K)
      = (-((MvPolynomial.C a) ^ 5 * (MvPolynomial.C b) ^ 5) *
            ((MvPolynomial.X 0) ^ 5 + (MvPolynomial.X 1) ^ 5 + (MvPolynomial.X 2) ^ 5)
          + (3 * (MvPolynomial.C a) ^ 4 * (MvPolynomial.C b) ^ 6
                - (MvPolynomial.C a) ^ 9 * (MvPolynomial.C b))
              * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1 * (MvPolynomial.X 2) ^ 2
          + (2 * (MvPolynomial.C a) ^ 7 * (MvPolynomial.C b) ^ 3
                - (MvPolynomial.C a) ^ 2 * (MvPolynomial.C b) ^ 8)
              * MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 3 * MvPolynomial.X 2
        : MvPolynomial ℕ K) := by
  rw [sdG5]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, MvPolynomial.rename_X,
    MvPolynomial.rename_C]
  rw [show fin3ToNat (0 : Fin 3) = 0 from rfl, show fin3ToNat (1 : Fin 3) = 1 from rfl,
    show fin3ToNat (2 : Fin 3) = 2 from rfl]

/-! ## §4 The target -/

/-- **`sdualT a b 1` is irreducible when its degree-five part `sdG5 a b` is.**

`sdualT a b 1 = sdG5 a b + (remainder)` with the remainder of total degree `< 5`, and `sdG5 a b`
is homogeneous of degree `5`; apply `irreducible_of_isHomogeneous_add`.  The hypothesis `hG5` is
stated in `MvPolynomial ℕ K` (the index type of the raw expression is not pinned down, see §3), so
it is first transported to `MvPolynomial (Fin 3) K` along the retraction. -/
theorem SdualTOneIrreducible {K : Type} [Field K] (a b : K)
    (hG5 : Irreducible (-((MvPolynomial.C a) ^ 5 * (MvPolynomial.C b) ^ 5) *
          ((MvPolynomial.X 0) ^ 5 + (MvPolynomial.X 1) ^ 5 + (MvPolynomial.X 2) ^ 5)
        + (3 * (MvPolynomial.C a) ^ 4 * (MvPolynomial.C b) ^ 6 - (MvPolynomial.C a) ^ 9 * (MvPolynomial.C b))
            * (MvPolynomial.X 0) ^ 2 * MvPolynomial.X 1 * (MvPolynomial.X 2) ^ 2
        + (2 * (MvPolynomial.C a) ^ 7 * (MvPolynomial.C b) ^ 3 - (MvPolynomial.C a) ^ 2 * (MvPolynomial.C b) ^ 8)
            * MvPolynomial.X 0 * (MvPolynomial.X 1) ^ 3 * MvPolynomial.X 2)) :
    Irreducible (Work.MotK.TGen.sdualT a b 1) := by
  have hH : Irreducible (MvPolynomial.rename fin3ToNat (sdG5 a b)) := by
    rw [rename_sdG5]
    exact hG5
  have hG5' : Irreducible (sdG5 a b) :=
    irreducible_of_comp_eq_id (MvPolynomial.rename fin3ToNat).toRingHom (natRetract K).toRingHom
      (fun x => by
        have h := DFunLike.congr_fun (natRetract_comp_rename K) x
        simpa using h)
      hH
  have hmain := irreducible_of_isHomogeneous_add (sdG5_isHomogeneous a b)
    (sdualT_one_sub_sdG5_totalDegree a b) hG5'
  have heq : sdG5 a b + (Work.MotK.TGen.sdualT a b 1 - sdG5 a b)
      = Work.MotK.TGen.sdualT a b 1 := by ring
  rwa [heq] at hmain

end Work.MotK.TwCensus
