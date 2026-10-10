/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.BwVec4Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.BwVec4Prime` — the cubic `bwVec a b h 4` is prime

`bwVec a b h 4 = ǧ₄` is the fourth component of the inverse link map `χ = π_p ∘ kleinTwR` of the
T-twisted Crauder–Katz link, i.e. the strict transform of the hyperplane `{w₄ = 0}`; it is the
denominator of the affine coordinates of `χ`.  The cubic is put in normal form in
`Submission/Work/MotK/TGen/BwVec4Defs.lean`:

  `bwF a b h = γ - β · X₂`,   `β = C (ab³) + C (a⁴h)·X₀X₁`,  `γ = C (a²b²h)·X₁³ + C (a³bh)·X₀²`,

and `bwTau K (bwF a b h) = bwFpoly a b h = C γ - C β · X` in `K[X₀,X₁][X]`.

Here we prove that this cubic is a **prime** element of `K[X₀,X₁,X₂]` for all `a b h ≠ 0` (no
characteristic restriction).  The argument is the standard one for a polynomial of degree one in
the last variable whose `X₂`-coefficient `β` and constant term `γ` are relatively prime:

* Writing `β = C a · β'` and `γ = C a · γ'` with `β' = C (b³) + C (a³h)·X₀X₁` and
  `γ' = C (ab²h)·X₁³ + C (a²bh)·X₀²` (both `β, γ` are divisible by the unit `C a`), relative
  primeness of `β` and `γ` reduces to that of `β'` and `γ'`.
* `β'` is irreducible: viewed in `K[X₀][X₁]` (through `MvPolynomial.finSuccEquiv`) it is
  `C (a³h·X₀) · X₁ + C (b³)`, a degree-one polynomial whose leading coefficient is nonzero and
  whose constant term `b³` is a unit; `Polynomial.irreducible_C_mul_X_add_C` applies.
* `β' ∤ γ'`: apply the algebra map `X₀ ↦ T, X₁ ↦ T` to `K[T]`; it sends `β'` to `b³ + a³h·T²` and
  `γ'` to `T²·(C (ab²h)·T + C (a²bh))`.  The first has nonzero constant term, so it is coprime to
  `T²`, hence a divisibility `β' ∣ γ'` would force `b³ + a³h·T² ∣ C (ab²h)·T + C (a²bh)`, which is
  impossible for degree reasons (`2 > 1`).
* Consequently `β, γ` are relatively prime, and `Polynomial.irreducible_C_mul_X_add_C` shows that
  `C β · X + C (-γ)` is irreducible; it is prime in the UFD `K[X₀,X₁][X]`, and so is `bwFpoly`
  (which is its negative).  Transporting along the algebra equivalence `bwTau` finishes.

The result is a step in the census of the junk classes of the `T`-twisted link: it says that the
closed subscheme `{ǧ₄ = 0}` in `𝔸³` is reduced and irreducible of codimension one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial Polynomial

noncomputable section

variable {K : Type} [Field K]

/-! ## The factorisation `β = C a · β'`, `γ = C a · γ'` -/

/-- `β' = C (b³) + C (a³h)·X₀X₁`: the primitive factor of `bwBeta a b h`, the cofactor being the
unit `C a`. -/
def bwBeta' (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (b ^ 3) + MvPolynomial.C (a ^ 3 * h) * MvPolynomial.X 0 * MvPolynomial.X 1

/-- `γ' = C (a b²h)·X₁³ + C (a²bh)·X₀²`: the cofactor in `bwGamma a b h = C a · γ'`. -/
def bwGamma' (a b h : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (a * b ^ 2 * h) * MvPolynomial.X 1 ^ 3
    + MvPolynomial.C (a ^ 2 * b * h) * MvPolynomial.X 0 ^ 2

theorem bwBeta_eq (a b h : K) : bwBeta a b h = MvPolynomial.C a * bwBeta' a b h := by
  simp only [bwBeta, bwBeta', map_mul, map_pow]
  first | refl_ring1 | ring

theorem bwGamma_eq (a b h : K) : bwGamma a b h = MvPolynomial.C a * bwGamma' a b h := by
  simp only [bwGamma, bwGamma', map_mul, map_pow]
  first | refl_ring1 | ring

/-! ## `β'` is irreducible -/

/-- The algebra equivalence `MvPolynomial.finSuccEquiv K 1 : K[X₀,X₁] ≃ₐ[K] K[X₀][X₁]` sends the
constants to constants. -/
theorem finSuccEquiv_C (r : K) :
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 2), AlgEquiv.commutes, Polynomial.algebraMap_apply]
  rfl

/-- The image of `β'` in `K[X₀][X₁]`: it is the degree-one polynomial
`C (a³h·X₀) · X₁ + C (b³)`. -/
theorem finSuccEquiv_bwBeta' (a b h : K) :
    MvPolynomial.finSuccEquiv K 1 (bwBeta' a b h)
      = Polynomial.C (MvPolynomial.C (a ^ 3 * h) * MvPolynomial.X 0) * Polynomial.X
        + Polynomial.C (MvPolynomial.C (b ^ 3)) := by
  simp only [bwBeta', map_add, map_mul, map_pow, finSuccEquiv_C, MvPolynomial.finSuccEquiv_X_zero]
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, MvPolynomial.finSuccEquiv_X_succ]
  first | refl_ring1 | ring

/-- `β' = C (b³) + C (a³h)·X₀X₁` is irreducible in `K[X₀,X₁]` (for `a b h ≠ 0`). -/
theorem irreducible_bwBeta' (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Irreducible (bwBeta' a b h) := by
  rw [← MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 1)]
  rw [finSuccEquiv_bwBeta' a b h]
  refine Polynomial.irreducible_C_mul_X_add_C ?_ ?_
  · exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 ha) hh))
      (MvPolynomial.X_ne_zero 0)
  · exact IsUnit.isRelPrime_right
      (IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr (pow_ne_zero 3 hb)))

/-! ## `β'` does not divide `γ'` -/

/-- `β' = C (b³) + C (a³h)·X₀X₁` does not divide `γ' = C (ab²h)·X₁³ + C (a²bh)·X₀²`
(for `a b h ≠ 0`).  Proof: the algebra map `X₀ ↦ T, X₁ ↦ T` (from `K[X₀,X₁]` to `K[T]`) sends
`β'` to `b³ + a³h·T²` and `γ'` to `T²·(C (ab²h)·T + C (a²bh))`; the former has nonzero constant
term so it is relatively prime to `T²`, and a divisibility would therefore force
`b³ + a³h·T² ∣ C (ab²h)·T + C (a²bh)`, which is impossible for degree reasons. -/
theorem not_dvd_bwGamma' (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ¬ bwBeta' a b h ∣ bwGamma' a b h := by
  intro hd
  have h1 := map_dvd (MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : Polynomial K))) hd
  have hψb : (MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : Polynomial K))) (bwBeta' a b h)
      = Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2 := by
    simp only [bwBeta', map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    first | refl_ring1 | ring
  have hψg : (MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : Polynomial K))) (bwGamma' a b h)
      = Polynomial.X ^ 2
        * (Polynomial.C (a * b ^ 2 * h) * Polynomial.X + Polynomial.C (a ^ 2 * b * h)) := by
    simp only [bwGamma', map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    first | refl_ring1 | ring
  rw [hψb, hψg] at h1
  -- `h1 : b³ + a³h·T² ∣ T² · (C (ab²h)·T + C (a²bh))`
  have hXf : ¬ Polynomial.X
      ∣ (Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2 : Polynomial K) := by
    rw [Polynomial.X_dvd_iff]
    have h0 : (Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2
        : Polynomial K).coeff 0 = b ^ 3 := by
      rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow]
      simp
    intro hc
    rw [h0] at hc
    exact pow_ne_zero 3 hb hc
  have hrel : IsRelPrime (Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2
      : Polynomial K) (Polynomial.X ^ 2) := by
    have hxf : IsRelPrime Polynomial.X
        (Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2 : Polynomial K) :=
      (Irreducible.isRelPrime_iff_not_dvd irreducible_X).mpr hXf
    have hX' : IsRelPrime (Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2
        : Polynomial K) Polynomial.X := hxf.symm
    simpa [pow_two] using hX'.mul_right hX'
  have h2 : Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2
      ∣ Polynomial.C (a * b ^ 2 * h) * Polynomial.X + Polynomial.C (a ^ 2 * b * h) :=
    hrel.dvd_of_dvd_mul_left h1
  have hdeg1 : (Polynomial.C (b ^ 3) + Polynomial.C (a ^ 3 * h) * Polynomial.X ^ 2
      : Polynomial K).natDegree = 2 := by
    compute_degree!
  have hdeg2 : (Polynomial.C (a * b ^ 2 * h) * Polynomial.X + Polynomial.C (a ^ 2 * b * h)
      : Polynomial K).natDegree = 1 := by
    compute_degree!
  have hne : (Polynomial.C (a * b ^ 2 * h) * Polynomial.X + Polynomial.C (a ^ 2 * b * h)
      : Polynomial K) ≠ 0 := by
    intro hc
    rw [hc, Polynomial.natDegree_zero] at hdeg2
    exact one_ne_zero hdeg2.symm
  exact absurd (Polynomial.natDegree_le_of_dvd h2 hne) (by omega)

/-! ## `β` and `γ` are relatively prime -/

/-- `β' = C (b³) + C (a³h)·X₀X₁` and `γ' = C (ab²h)·X₁³ + C (a²bh)·X₀²` are relatively prime. -/
theorem isRelPrime_bwBeta'_bwGamma' (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsRelPrime (bwBeta' a b h) (bwGamma' a b h) :=
  (Irreducible.isRelPrime_iff_not_dvd (irreducible_bwBeta' a b h ha hb hh)).mpr
    (not_dvd_bwGamma' a b h ha hb hh)

/-- `β = C (ab³) + C (a⁴h)·X₀X₁` and `γ = C (a²b²h)·X₁³ + C (a³bh)·X₀²` are relatively prime:
this is the coprimality hypothesis of `Polynomial.irreducible_C_mul_X_add_C` for the normal
form `C β · X + C (-γ)` of `bwFpoly`. -/
theorem isRelPrime_bwBeta_bwGamma (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    IsRelPrime (bwBeta a b h) (bwGamma a b h) := by
  have hu : IsUnit (MvPolynomial.C a : MvPolynomial (Fin 2) K) :=
    IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr ha)
  rw [bwBeta_eq a b h, bwGamma_eq a b h]
  exact (isRelPrime_mul_unit_left (x := (MvPolynomial.C a : MvPolynomial (Fin 2) K)) hu).mpr
    (isRelPrime_bwBeta'_bwGamma' a b h ha hb hh)

/-- Relatively prime elements stay relatively prime after negating one of them. -/
theorem isRelPrime_neg_right {R : Type} [Ring R] {x y : R} (h : IsRelPrime x y) :
    IsRelPrime x (-y) := by
  intro d hdx hdy
  exact h hdx (dvd_neg.mp hdy)

/-! ## `bwFpoly` and `bwF` are prime -/

/-- The normal form is the negative of `C β · X + C (-γ)`. -/
theorem bwFpoly_eq_neg (a b h : K) :
    bwFpoly a b h
      = -(Polynomial.C (bwBeta a b h) * Polynomial.X + Polynomial.C (-(bwGamma a b h))) := by
  simp only [bwFpoly, map_neg]
  first | refl_ring1 | ring

/-- `bwFpoly a b h = C γ - C β·X` is prime in `K[X₀,X₁][X]` for `a b h ≠ 0`. -/
theorem prime_bwFpoly (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Prime (bwFpoly a b h) := by
  -- We use the presentation `bwFpoly = C (-β)·X + C γ`, so that
  -- `Polynomial.irreducible_C_mul_X_add_C` applies directly.
  have hrel : IsRelPrime (-(bwBeta a b h)) (bwGamma a b h) := by
    intro d hdx hdy
    exact isRelPrime_bwBeta_bwGamma a b h ha hb hh (dvd_neg.mp hdx) hdy
  have hβ : -(bwBeta a b h) ≠ 0 := neg_ne_zero.mpr (bwBeta_ne_zero a b h ha hb)
  have hpr : Prime (Polynomial.C (-(bwBeta a b h)) * Polynomial.X
      + Polynomial.C (bwGamma a b h)) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (Polynomial.irreducible_C_mul_X_add_C hβ hrel)
  have heq : Polynomial.C (-(bwBeta a b h)) * Polynomial.X + Polynomial.C (bwGamma a b h)
      = bwFpoly a b h := by
    simp only [bwFpoly, map_neg]
    first | refl_ring1 | ring
  rwa [heq] at hpr

end

/-- **The cubic `bwVec a b h 4` is prime.**  For `a b h ≠ 0` in any field `K`, the strict transform
of the hyperplane `{w₄ = 0}` under the inverse link map `χ = π_p ∘ kleinTwR` of the `T`-twisted
Crauder–Katz link is an irreducible (hence reduced) cubic surface. -/
theorem BwVec4Prime {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Prime (Work.MotK.TGen.bwVec a b h 4) := by
  have hp : Prime (bwTau K (bwF a b h)) := by
    rw [bwTau_bwF]
    exact prime_bwFpoly a b h ha hb hh
  have hF : Prime (bwF a b h) := (MulEquiv.prime_iff (bwTau K) (p := bwF a b h)).mp hp
  rwa [bwVec_four_eq a b h]

end Work.MotK.TGen
