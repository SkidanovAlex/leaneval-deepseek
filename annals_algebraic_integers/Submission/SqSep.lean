import Mathlib

/-!
# Squarefree (ℤ[X]) ⟹ separable complexification

Self-contained Mathlib module. `Squarefree Q` in `ℤ[X]` (Mathlib monoid
notion: no non-unit square divides `Q`) implies that the complexification
`Q.map (algebraMap ℤ ℂ)` is `Separable` (i.e. has no repeated complex root).

This is the standard Gauss-lemma fact: squarefree over `ℤ[X]` ⟹ squarefree
over `ℚ[X]` (map into the fraction field), and over the characteristic-zero
field ℚ squarefree ⟺ Separable (`PerfectField.separable_iff_squarefree` in
`Mathlib/FieldTheory/Perfect.lean`, instance `PerfectField.ofCharZero`);
finally `Separable.map` carries separability to ℂ.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.SqSep

-- the polynomial ring `ℚ[X]` is the localization of `ℤ[X]` at `ℤ \ {0}`,
-- and `ℚ[X]` is a `ℤ[X]`-algebra via coefficient-wise scalar action.
attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- Every nonzero rational polynomial is a scalar multiple of the map of a
primitive integer polynomial.  This is the "clear denominators, then strip the
content" step of Gauss's lemma. -/
lemma rat_poly_decomp {g : Polynomial ℚ} (hg : g ≠ 0) :
    ∃ (a : ℚ) (G : Polynomial ℤ), G.IsPrimitive ∧ a ≠ 0 ∧
      g = C a * (G.map (Int.castRingHom ℚ)) := by
  let H := IsLocalization.integerNormalization (M := nonZeroDivisors ℤ) g
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (M := nonZeroDivisors ℤ) (p := g)
  have hb_ne : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbM
  have hbℚ : (b : ℚ) ≠ 0 := by exact_mod_cast hb_ne
  have hbC : H.map (algebraMap ℤ ℚ) = C (b : ℚ) * g := by
    simpa [Polynomial.map_smul] using hb
  have hH_ne : H ≠ 0 := by
    intro hzero
    apply hg
    have : C (b : ℚ) * g = 0 := by
      rw [← hbC, hzero, Polynomial.map_zero]
    rcases mul_eq_zero.mp this with hc | hg0
    · exact False.elim (hbℚ (C_eq_zero.mp hc))
    · exact hg0
  let a : ℚ := (b : ℚ)⁻¹ * (H.content : ℚ)
  let G : Polynomial ℤ := H.primPart
  have hGprim : G.IsPrimitive := by simpa [G] using isPrimitive_primPart H
  have hEq0 : g = C ((b : ℚ)⁻¹) * (H.map (algebraMap ℤ ℚ)) := by
    calc
      g = C (((b : ℚ)⁻¹) * (b : ℚ)) * g := by rw [inv_mul_cancel₀ hbℚ, C_1, one_mul]
      _ = (C ((b : ℚ)⁻¹) * C (b : ℚ)) * g := by rw [← C_mul]
      _ = C ((b : ℚ)⁻¹) * (C (b : ℚ) * g) := by rw [mul_assoc]
      _ = C ((b : ℚ)⁻¹) * (H.map (algebraMap ℤ ℚ)) := by rw [hbC]
  have hmapH : H.map (algebraMap ℤ ℚ) = C (H.content : ℚ) * (G.map (Int.castRingHom ℚ)) := by
    conv_lhs => rw [eq_C_content_mul_primPart H]
    rw [Polynomial.map_mul, Polynomial.map_C]
    simp [G]
  have hEq : g = C a * (G.map (Int.castRingHom ℚ)) := by
    calc
      g = C ((b : ℚ)⁻¹) * (H.map (algebraMap ℤ ℚ)) := hEq0
      _ = C ((b : ℚ)⁻¹) * (C (H.content : ℚ) * (G.map (Int.castRingHom ℚ))) := by rw [hmapH]
      _ = C a * (G.map (Int.castRingHom ℚ)) := by
        rw [← mul_assoc, ← C_mul]
  refine ⟨a, G, hGprim, ?_, hEq⟩
  · intro ha0
    apply hg
    rw [hEq, ha0, C_0, zero_mul]

/-- Squarefree over `ℤ[X]` is preserved by mapping into `ℚ[X]` (Gauss lemma).
Given a square `g * g` dividing the image of `Q`, decompose `g = C a * G`
with `G` primitive and `a ≠ 0`; the square divisibility lifts back to
`G * G ∣ Q` in `ℤ[X]` (Gauss), where `Squarefree Q` forces `G` to be a unit,
hence `g` is a unit too. -/
lemma squarefree_int_map_rat {Q : Polynomial ℤ} (hQ0 : Q ≠ 0) (hsq : Squarefree Q) :
    Squarefree (Q.map (algebraMap ℤ ℚ)) := by
  rw [Squarefree]
  intro g hgg
  by_cases hg0 : g = 0
  · exfalso
    rcases hgg with ⟨w, hw⟩
    apply hQ0
    apply (Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ))
    simpa [hg0] using hw
  · obtain ⟨a, G, hGprim, ha0, hEq⟩ := rat_poly_decomp hg0
    let m : Polynomial ℚ := G.map (Int.castRingHom ℚ)
    have hGG_map : m * m ∣ Q.map (Int.castRingHom ℚ) := by
      rcases hgg with ⟨h, hh⟩
      refine ⟨C (a * a) * h, ?_⟩
      calc
        Q.map (Int.castRingHom ℚ) = (g * g) * h := by simpa using hh
        _ = (m * m) * (C (a * a) * h) := by
          rw [hEq]
          have hsquare : (C a * m) * (C a * m) = C (a * a) * (m * m) := by
            calc
              (C a * m) * (C a * m) = C a * (m * C a) * m := by ring
              _ = C a * (C a * m) * m := by rw [mul_comm m (C a)]
              _ = (C a * C a) * (m * m) := by ring
              _ = C (a * a) * (m * m) := by rw [← C_mul]
          rw [hsquare]
          ring
    have hprim2 : (G * G).IsPrimitive := hGprim.mul hGprim
    have hGG : (G * G) ∣ Q := by
      rw [Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (G * G) Q hprim2]
      simpa [m, ← Polynomial.map_mul] using hGG_map
    have hGu : IsUnit G := hsq G hGG
    have hmapGu : IsUnit (G.map (Int.castRingHom ℚ)) := by
      simpa using ((hGprim.isUnit_iff_isUnit_map (K := ℚ)).mp hGu)
    have hCa : IsUnit (C a : Polynomial ℚ) := by
      rw [Polynomial.isUnit_C]
      exact isUnit_iff_ne_zero.mpr ha0
    rw [hEq]
    exact hCa.mul hmapGu

/-- MAIN RESULT. -/
theorem squarefree_separable {Q : Polynomial ℤ} (hQ0 : Q ≠ 0) (hsq : Squarefree Q) :
    (Q.map (algebraMap ℤ ℂ)).Separable := by
  have hsqQ : Squarefree (Q.map (algebraMap ℤ ℚ)) := squarefree_int_map_rat hQ0 hsq
  have hsepQ : (Q.map (algebraMap ℤ ℚ)).Separable :=
    (PerfectField.separable_iff_squarefree (K := ℚ)).mpr hsqQ
  have hsepC : ((Q.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).Separable :=
    hsepQ.map (f := algebraMap ℚ ℂ)
  rw [Polynomial.map_map] at hsepC
  convert hsepC using 1
  · ext r
    simp

/-- Variant spelling out degree and nonzeroness for the adjust chain:
`Squarefree Q` + `natDegree = n` ⇒ the complexification is Separable. -/
theorem squarefree_separable_of_degree {n : ℕ} (Q : Polynomial ℤ) (hQ0 : Q ≠ 0)
    (hQn : Q.natDegree = n) (hsq : Squarefree Q) :
    (Q.map (algebraMap ℤ ℂ)).Separable := by
  exact squarefree_separable hQ0 hsq

end Submission.SqSep
