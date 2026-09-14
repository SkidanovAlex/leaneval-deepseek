import Mathlib
import Submission.Commons.RingTheory.Polynomial.discr_map_of_natDegree
import Submission.Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero
import Submission.Commons.RingTheory.Polynomial.geo_prop_sq

open Polynomial

/-!
# Per-prime discriminant divisibility (Case III of Theorem 1)

The engine behind Bhargava's Case III ("$\Disc(f)$ is a multiple of $C^2$ for mod $C$
reasons $\Rightarrow$ the double discriminant $\mathrm{DD}$ is a multiple of $C$", Annals of
Math 2025, Section 5 / Prop. in the sketch of Case III).  We formalize the per-prime
polynomial-algebra step, entirely at the level of integer polynomials (no number fields):

1. `prime_dvd_discr_of_double_root_modp` -- if the integer polynomial `P` has a double
   root modulo the prime `p` (i.e. `p | P(a₀)` and `p | P'(a₀)` for some integer `a₀`),
   the degree of `P` is at least 2, and `p` does not divide the leading coefficient of `P`,
   then `p` divides the (integer) discriminant of `P`.  (The leading-coefficient
   hypothesis is exactly "the degree does not drop on reduction mod `p`", which keeps the
   discriminant matrix size fixed; the degree hypothesis excludes the linear case, where
   `discr = 1` but the congruence can still hold, e.g. `P = p·X + p`.)

2. `prime_dvd_discr_of_modp_stable` -- the geometric-sieve input: if the value of `P` is
   divisible by `p²` on the whole residue class `a₀ mod p` (`∀ d, p² | P(a₀ + p·d)`),
   then `p | discr(P)`.  Proof: the fleet geometric-sieve proposition `geo_prop_sq`
   (commons) supplies `p | P'(a₀)`; the `d = 0` case supplies `p | P(a₀)`; then (1).

In Case III of the paper, `P` will be `Disc_x(f(x))` regarded as a polynomial in the
constant coefficient `aₙ` (with the upper coefficients fixed), and `discr(P)` is the
double discriminant `DD(u) = Disc_{aₙ}(Disc_x f)` of the upper coefficients `u`.  The
stability hypothesis holds, per prime `p | C`, because for mod-`p` reasons `Disc` is
divisible by `p²` on the whole mod-`p` fibre of `f` (a triple root or a pair of double
roots modulo `p`).  The leading-coefficient hypothesis is `p ∤ n` there, since the
leading coefficient of `P` is `± nⁿ`; in the eventual counting (Case III subcase (ii))
all primes under consideration satisfy `p > H^{δ/2}`, hence `p ∤ n` for all large `H`.
-/

noncomputable section

namespace Submission.Vdw

/-- If an integer polynomial `G` (of degree ≥ 2, with leading coefficient not divisible by
the prime `p`) has a "double root modulo `p`" at `a₀` (both `G(a₀)` and `G'(a₀)`
divisible by `p`), then `p` divides the discriminant of `G`. -/
lemma prime_dvd_discr_of_double_root_modp (p : ℕ) (hp : Nat.Prime p) (G : ℤ[X]) (a₀ : ℤ)
    (hdeg : 2 ≤ G.natDegree) (hlc : ¬ (p : ℤ) ∣ G.leadingCoeff)
    (h1 : (p : ℤ) ∣ G.eval a₀) (h2 : (p : ℤ) ∣ G.derivative.eval a₀) :
    (p : ℤ) ∣ G.discr := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hφ_lc : φ G.leadingCoeff ≠ 0 := by
    intro hz
    apply hlc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd G.leadingCoeff p).1 hz
  have hnd : (map φ G).natDegree = G.natDegree := by
    exact Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero φ hφ_lc
  have hdisc : φ G.discr = (map φ G).discr := by
    exact Commons.RingTheory.Polynomial.discr_map_of_natDegree φ hnd
  -- common root of Ḡ and Ḡ' at φ a₀
  have hφe1 : φ (G.eval a₀) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (G.eval a₀) p).2 h1
  have hroot : (map φ G).IsRoot (φ a₀) := by
    rw [IsRoot]
    calc
      eval (φ a₀) (map φ G) = eval₂ φ (φ a₀) G := eval_map φ (φ a₀)
      _ = φ (eval a₀ G) := eval₂_hom (f := φ) (p := G) a₀
      _ = 0 := hφe1
  have hφe2 : φ (G.derivative.eval a₀) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (G.derivative.eval a₀) p).2 h2
  have hroot' : ((map φ G).derivative).IsRoot (φ a₀) := by
    rw [IsRoot]
    calc
      eval (φ a₀) ((map φ G).derivative) = eval (φ a₀) (map φ G.derivative) := by
          rw [derivative_map]
      _ = eval₂ φ (φ a₀) G.derivative := eval_map φ (φ a₀)
      _ = φ (eval a₀ G.derivative) := eval₂_hom (f := φ) (p := G.derivative) a₀
      _ = 0 := hφe2
  -- not coprime
  have hnotcop : ¬ IsCoprime (map φ G) (map φ G).derivative := by
    intro hcop
    rcases hcop with ⟨u, v, huv⟩
    have hval := congrArg (fun q : (ZMod p)[X] => q.eval (φ a₀)) huv
    have hleft : eval (φ a₀) (u * map φ G + v * (map φ G).derivative) = 0 := by
      rw [eval_add, eval_mul, eval_mul]
      rw [hroot.eq_zero, hroot'.eq_zero]
      ring
    have hright : eval (φ a₀) 1 = (1 : ZMod p) := by simp
    rw [hval] at hleft
    rw [hright] at hleft
    exact zero_ne_one hleft.symm
  -- resultant at default degrees is 0
  have hres0 : (map φ G).resultant (map φ G).derivative = 0 := by
    rw [resultant_eq_zero_iff]
    constructor
    · left
      intro hz
      have : (map φ G).natDegree = 0 := by rw [hz]; simp
      omega
    · exact hnotcop
  -- lift to explicit degree (m, m-1)
  have hres0' : (map φ G).resultant (map φ G).derivative (map φ G).natDegree
      ((map φ G).natDegree - 1) = 0 := by
    let m := (map φ G).natDegree
    let n := ((map φ G).derivative).natDegree
    have hle : n ≤ m - 1 := by
      dsimp [n, m]
      simpa using natDegree_derivative_le (map φ G)
    have hnk : n + (m - 1 - n) = m - 1 := Nat.add_sub_of_le hle
    have hmain := resultant_add_right_deg (f := map φ G) (g := (map φ G).derivative)
      (m := m) (n := n) (k := m - 1 - n) (by dsimp [n]; exact le_rfl)
    have hres : (map φ G).resultant (map φ G).derivative m (m - 1) =
        (map φ G).coeff m ^ (m - 1 - n) * (map φ G).resultant (map φ G).derivative m n := by
      simpa [hnk] using hmain
    have hres'' : (map φ G).resultant (map φ G).derivative m n = 0 := by
      dsimp [n]
      simpa [m] using hres0
    rw [hres, hres'', mul_zero]
  -- relate to discr via resultant_deriv
  have hdegpos : 0 < (map φ G).degree := by
    rw [← natDegree_pos_iff_degree_pos]
    rw [hnd]
    omega
  have hmain2 := resultant_deriv (f := map φ G) hdegpos
  have hsign : (-1 : ZMod p) ^ ((map φ G).natDegree * ((map φ G).natDegree - 1) / 2) ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hmap_lc : (map φ G).leadingCoeff = φ G.leadingCoeff := by
    calc
      (map φ G).leadingCoeff = (map φ G).coeff ((map φ G).natDegree) := rfl
      _ = (map φ G).coeff G.natDegree := by rw [hnd]
      _ = φ (G.coeff G.natDegree) := coeff_map φ G.natDegree
      _ = φ G.leadingCoeff := rfl
  have hlc2 : (map φ G).leadingCoeff ≠ 0 := by
    intro hz
    apply hφ_lc
    rwa [hmap_lc] at hz
  have hmain3 : (map φ G).discr = 0 := by
    rw [hres0'] at hmain2
    exact (mul_eq_zero.mp hmain2.symm).resolve_left (mul_ne_zero hsign hlc2)
  -- conclusion
  have hz : φ G.discr = 0 := by
    rw [hdisc]
    exact hmain3
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd G.discr p).1 (by simpa using hz)

/-- The geometric-sieve input: if the value of the integer polynomial `P` is divisible by
`p²` on the whole residue class `a₀ (mod p)`, then (degree and leading coefficient as in
`prime_dvd_discr_of_double_root_modp`) `p` divides the discriminant of `P`. -/
lemma prime_dvd_discr_of_modp_stable (p : ℕ) (hp : Nat.Prime p) (P : ℤ[X]) (a₀ : ℤ)
    (hdeg : 2 ≤ P.natDegree) (hlc : ¬ (p : ℤ) ∣ P.leadingCoeff)
    (hstab : ∀ d : ℤ, ((p : ℤ) ^ 2) ∣ P.eval (a₀ + (p : ℤ) * d)) :
    (p : ℤ) ∣ P.discr := by
  -- d = 0 supplies p | P(a₀)
  have hp2dvd0 : ((p : ℤ) ^ 2) ∣ P.eval a₀ := by
    simpa using hstab 0
  have h1 : (p : ℤ) ∣ P.eval a₀ := by
    exact dvd_trans (by exact ⟨(p : ℤ), by ring⟩) hp2dvd0
  -- the geometric sieve (fleet) supplies p | P'(a₀)
  have hmodEq : ∀ d : ℤ, Int.ModEq ((p : ℤ) ^ 2) (P.eval (a₀ + (p : ℤ) * d)) 0 := by
    intro d
    exact (Int.modEq_zero_iff_dvd).2 (hstab d)
  have hgeo := Commons.RingTheory.Polynomial.geo_prop_sq (p := p) hp P a₀ hmodEq
  have h2 : (p : ℤ) ∣ P.derivative.eval a₀ := (Int.modEq_zero_iff_dvd).1 hgeo
  exact prime_dvd_discr_of_double_root_modp p hp P a₀ hdeg hlc h1 h2

end Submission.Vdw
