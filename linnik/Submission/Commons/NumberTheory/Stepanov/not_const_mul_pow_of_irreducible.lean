import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.Stepanov

/-- If a monic polynomial `f` over a field is such that `X ^ e - C f` is irreducible in
`F[X][X]` (with `2 ≤ e`), then `f` is not a constant multiple of a `p`-th power for any prime `p`
dividing `e`.  Proof: monicity plus `f = C a * h ^ p` forces `a = (h.leadingCoeff)⁻¹ ^ p`, so
`f = g ^ p` with `g = C (h.leadingCoeff)⁻¹ * h`; then `X ^ e - C f = X ^ (p * (e / p)) - (C g) ^ p`;
transport irreducibility to `K = FractionRing F[X]` via Gauss's lemma
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`) and apply
`pow_ne_of_irreducible_X_pow_sub_C` (`Mathlib.FieldTheory.KummerPolynomial`). -/
theorem not_const_mul_pow_of_irreducible {F : Type*} [Field F] (e : ℕ) (he : 2 ≤ e)
    (f : Polynomial F) (hf0 : f ≠ 0) (hfmon : Polynomial.Monic f)
    (hirr : Irreducible (Polynomial.X ^ e - Polynomial.C f)) :
    ∀ (p : ℕ), p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F), f ≠ Polynomial.C a * h ^ p := by
  intro p hp hpe a h hf
  -- `h` is nonzero, otherwise `f = 0`.
  have hne : h ≠ 0 := by
    intro hz
    rw [hz, zero_pow hp.pos.ne', mul_zero] at hf
    exact hf0 hf
  -- Comparing leading coefficients of `f = C a * h ^ p` and using monicity of `f`
  -- gives `a * h.leadingCoeff ^ p = 1`.
  have hlc : a * h.leadingCoeff ^ p = 1 := by
    have h1 := hfmon.leadingCoeff
    rw [hf, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_pow] at h1
    exact h1
  -- Hence `a` is itself a `p`-th power.
  have ha_eq : a = h.leadingCoeff⁻¹ ^ p := by
    rw [eq_inv_of_mul_eq_one_left hlc, ← inv_pow]
  -- So `f = g ^ p` for a monic `g`.
  set g : Polynomial F := Polynomial.C h.leadingCoeff⁻¹ * h with hgdef
  have hg : g ^ p = f := by
    rw [hgdef, mul_pow, ← Polynomial.C_pow, ← ha_eq, hf]
  -- `X ^ e - C f` is monic in `(F[X])[X]`.
  set P : Polynomial (Polynomial F) := Polynomial.X ^ e - Polynomial.C f with hPdef
  have hPmon : P.Monic := by
    rw [hPdef]
    exact Polynomial.monic_X_pow_sub_C f (by omega)
  -- Transport irreducibility to the fraction field `K = FractionRing F[X]` (Gauss's lemma).
  have hKirr : Irreducible (P.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))) :=
    (hPmon.irreducible_iff_irreducible_map_fraction_map).mp hirr
  have hmap : P.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))
      = Polynomial.X ^ e
        - Polynomial.C (algebraMap (Polynomial F) (FractionRing (Polynomial F)) f) := by
    rw [hPdef]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  have hKirr' : Irreducible (Polynomial.X ^ e
      - Polynomial.C (algebraMap (Polynomial F) (FractionRing (Polynomial F)) f)) := by
    rwa [hmap] at hKirr
  -- Kummer's theorem: `f` is not a `p`-th power in `K`; but it is, being the image of `g ^ p = f`.
  have hcontra := pow_ne_of_irreducible_X_pow_sub_C hKirr' hpe hp.ne_one
    (algebraMap (Polynomial F) (FractionRing (Polynomial F)) g)
  exact hcontra (by rw [← map_pow, hg])

end Commons.NumberTheory.Stepanov