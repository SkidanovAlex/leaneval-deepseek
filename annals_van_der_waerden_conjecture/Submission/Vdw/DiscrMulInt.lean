import Mathlib
import Submission.Commons.FieldTheory.Polynomial.discr_mul
import Submission.Commons.RingTheory.Polynomial.discr_map

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Integer discriminant multiplicativity `Disc(f·g) = Disc f · Disc g · Res(f,g)²`

The valuation additivity step of Lemma 24 of Bhargava 2025
(`v_p(Disc(L_h)) = v_p(Disc(L_{h₁})) + v_p(Disc(L_{h₂}))` for a factorization
`h = h₁·h₂` over `ℤ_p` whose factors are coprime modulo `p`, so that
`v_p(Res(h₁,h₂)) = 0`) rests on the integer-level identity

    Disc(f·g) = Disc(f)·Disc(g)·Res(f,g)²        (`int_discr_mul`)

for **monic** `f, g ∈ ℤ[X]`.  It is derived from the field-level identity
`Commons.FieldTheory.Polynomial.discr_mul` (proved over ℚ from the roots of
the factors in a splitting field) by transporting through
`ℤ → ℚ` with the monic-cast lemmas `Polynomial.resultant_map_map` and
`Commons.RingTheory.Polynomial.discr_map`, then pulling the integer equality
back by the injectivity of the cast (`Int.cast_inj`).
-/

namespace Submission.Vdw

noncomputable section

/-- Integer discriminant multiplicativity for monic factors:
`Disc(f·g) = Disc(f)·Disc(g)·Res(f,g)²` over `ℤ`. -/
theorem int_discr_mul {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic) :
    Polynomial.discr (f * g) =
      Polynomial.discr f * Polynomial.discr g * (Polynomial.resultant f g) ^ 2 := by
  classical
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  have hmon_prod : (f * g).Monic := hf.mul hg
  have hdegmap (p : ℤ[X]) (hp : p.Monic) : (Polynomial.map φ p).natDegree = p.natDegree :=
    hp.natDegree_map φ
  have hmapf_deg : (Polynomial.map φ f).natDegree = f.natDegree := hdegmap f hf
  have hmapg_deg : (Polynomial.map φ g).natDegree = g.natDegree := hdegmap g hg
  -- identity over ℚ, on the transported polynomials
  have hQ : ((Polynomial.discr (f * g) : ℤ) : ℚ) =
      ((Polynomial.discr f * Polynomial.discr g * (Polynomial.resultant f g) ^ 2 : ℤ) : ℚ) := by
    calc
      ((Polynomial.discr (f * g) : ℤ) : ℚ)
          = Polynomial.discr (Polynomial.map φ (f * g)) := by
              rw [Commons.RingTheory.Polynomial.discr_map φ hmon_prod]
              rfl
      _ = Polynomial.discr (Polynomial.map φ f * Polynomial.map φ g) := by
              rw [Polynomial.map_mul]
      _ = Polynomial.discr (Polynomial.map φ f) * Polynomial.discr (Polynomial.map φ g) *
            (Polynomial.resultant (Polynomial.map φ f) (Polynomial.map φ g)) ^ 2 := by
              exact Commons.FieldTheory.Polynomial.discr_mul (F := ℚ)
                (Polynomial.map φ f) (Polynomial.map φ g) (hf.map φ) (hg.map φ)
      _ = ((Polynomial.discr f : ℤ) : ℚ) * ((Polynomial.discr g : ℤ) : ℚ) *
            (((Polynomial.resultant f g : ℤ) : ℚ)) ^ 2 := by
              have hdf : Polynomial.discr (Polynomial.map φ f) = ((Polynomial.discr f : ℤ) : ℚ) := by
                rw [Commons.RingTheory.Polynomial.discr_map φ hf]
                rfl
              have hdg : Polynomial.discr (Polynomial.map φ g) = ((Polynomial.discr g : ℤ) : ℚ) := by
                rw [Commons.RingTheory.Polynomial.discr_map φ hg]
                rfl
              have hres : Polynomial.resultant (Polynomial.map φ f) (Polynomial.map φ g) =
                  ((Polynomial.resultant f g : ℤ) : ℚ) := by
                rw [show (Polynomial.map φ f).natDegree = f.natDegree by exact hmapf_deg,
                  show (Polynomial.map φ g).natDegree = g.natDegree by exact hmapg_deg]
                rw [Polynomial.resultant_map_map f g f.natDegree g.natDegree φ]
                rfl
              rw [hdf, hdg, hres]
      _ = ((Polynomial.discr f * Polynomial.discr g * (Polynomial.resultant f g) ^ 2 : ℤ) : ℚ) := by
              norm_num
  exact (Int.cast_inj.mp hQ)


/-- If two monic integer polynomials are coprime modulo the prime `p`, then
`p` does not divide their resultant — the integer shadow of the fact that
distinct Hensel-lift factors have `v_p(Res) = 0` (used in the valuation
additivity step of Lemma 24). -/
theorem not_dvd_resultant_of_coprime_mod {p : ℕ} [Fact p.Prime] {f g : ℤ[X]}
    (hf : f.Monic) (hg : g.Monic)
    (hcop : IsCoprime (Polynomial.map (Int.castRingHom (ZMod p)) f)
      (Polynomial.map (Int.castRingHom (ZMod p)) g)) :
    ¬ (p : ℤ) ∣ Polynomial.resultant f g := by
  classical
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hfdeg : (Polynomial.map φ f).natDegree = f.natDegree := hf.natDegree_map φ
  have hgdeg : (Polynomial.map φ g).natDegree = g.natDegree := hg.natDegree_map φ
  have hres_map : (Polynomial.map φ f).resultant (Polynomial.map φ g) = φ (f.resultant g) := by
    rw [hfdeg, hgdeg]
    exact Polynomial.resultant_map_map f g f.natDegree g.natDegree φ
  have hne : (Polynomial.map φ f).resultant (Polynomial.map φ g) ≠ 0 := by
    exact Polynomial.resultant_ne_zero (Polynomial.map φ f) (Polynomial.map φ g) hcop
  intro hdiv
  -- (p : ℤ) ∣ resultant ⟹ resultant maps to 0 in ZMod p
  obtain ⟨c, hc⟩ := hdiv
  have hφ0 : φ (Polynomial.resultant f g) = 0 := by
    rw [hc]
    simp [φ]
  exact hne (by simpa [hres_map] using hφ0)
end
end Submission.Vdw
