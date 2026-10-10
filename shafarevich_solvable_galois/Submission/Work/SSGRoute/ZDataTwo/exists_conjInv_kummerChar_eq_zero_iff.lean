import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The involution of `Gal(Ω/k)` attached to a real place: the Kummer character vanishes
exactly at the positive elements

Let `k` be a number field, `w` a *real* infinite place of `k` and `Ω` an algebraic closure of `k`.
The purpose of this file is the lemma `exists_conjInv_kummerChar_eq_zero_iff`: there is a
non-trivial involution `c` of `Gal(Ω/k)` — the complex conjugation of `Ω` at `w` — such that for
every `a ∈ kˣ`

`kummerChar a c = 0 ↔ a` is not negative at `w`,

i.e. `a` is positive at the real place `w`.

## Construction

Fix the real embedding `v = w.embedding : k →+* ℝ`, regard `ℂ` as a `k`-algebra through `v`, and
lift it to a ring homomorphism `φ : Ω →+* ℂ` (`NumberField.ComplexEmbedding.lift`).  Since `v` is
real-valued, `φ` and `conj ∘ φ` are two `k`-embeddings of `Ω` into `ℂ`, so they differ by an element
`c` of `Gal(Ω/k)` which is the desired involution: `φ (c x) = conj (φ x)`
(`NumberField.ComplexEmbedding.IsConj`).

## The arithmetic

`kummerChar a c = 0` iff `a` is a norm for `c` (`kummerChar_eq_zero_iff_mem_normSet`), i.e. iff
`a = y * c y` for some `y ≠ 0`.  Because `φ (c y) = conj (φ y)`, this is `φ a = ‖φ y‖² > 0`, so `a`
is positive at `w`; and conversely if `a` is positive at `w` and `m² = a` in `Ω` (which exists as `Ω`
is algebraically closed), then `(φ m)² = v a > 0` is a *positive real* number, so `φ m` is real, so
`c m = m` and `a = m * c m` is a norm.

The second direction is the one that does not need any real-closedness of the fixed field: the
element `m` is *found in `Ω`*, and only then observed to lie in the fixed field of `c`.
-/

namespace Work.SSGRoute.ZDataTwo

open NumberField

/-- A complex number whose square is a positive real number is fixed by complex conjugation. -/
lemma star_eq_self_of_sq_eq_ofReal {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ^ 2 = (r : ℂ)) :
    star z = z := by
  have hs : (((Real.sqrt r : ℝ) : ℂ)) ^ 2 = (r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  have hfac : (z - ((Real.sqrt r : ℝ) : ℂ)) * (z + ((Real.sqrt r : ℝ) : ℂ)) = 0 := by
    have h1 : (z - ((Real.sqrt r : ℝ) : ℂ)) * (z + ((Real.sqrt r : ℝ) : ℂ))
        = z ^ 2 - (((Real.sqrt r : ℝ) : ℂ)) ^ 2 := by ring
    rw [h1, hz, hs, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · have hz' : z = ((Real.sqrt r : ℝ) : ℂ) := sub_eq_zero.mp h
    rw [hz']
    simp
  · have hz' : z = -((Real.sqrt r : ℝ) : ℂ) := by linear_combination h
    rw [hz']
    simp

theorem exists_conjInv_kummerChar_eq_zero_iff {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (w : NumberField.InfinitePlace k) (hw : w.IsReal) :
    ∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ c ≠ 1 ∧
      ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
        ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
  classical
  -- The real embedding of `k` at `w`, and its lift to the algebraic closure `Ω`.
  let v : k →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hw
  let φ : Ω →+* ℂ := NumberField.ComplexEmbedding.lift Ω (Complex.ofRealHom.comp v)
  have hφ : ∀ x : k, φ (algebraMap k Ω x) = (v x : ℂ) := fun x =>
    NumberField.ComplexEmbedding.lift_algebraMap_apply Ω _ x
  have hreal : NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap k Ω)) := by
    have hcomp : φ.comp (algebraMap k Ω) = Complex.ofRealHom.comp v := RingHom.ext hφ
    rw [hcomp, NumberField.ComplexEmbedding.isReal_iff]
    ext x
    exact Complex.conj_ofReal (v x)
  -- The involution of `Gal(Ω/k)` intertwining `φ` with complex conjugation.
  obtain ⟨σ₁, hσ₁⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (K := Ω) (k := k)
    φ (NumberField.ComplexEmbedding.conjugate φ) (by
      rw [NumberField.ComplexEmbedding.conjugate_comp]
      exact hreal.symm)
  let c : Ω ≃ₐ[k] Ω := σ₁.symm
  have hcφ : φ.comp (c : Ω →+* Ω) = NumberField.ComplexEmbedding.conjugate φ := hσ₁
  have hIsConj : NumberField.ComplexEmbedding.IsConj φ c := hcφ.symm
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact NumberField.ComplexEmbedding.isConj_apply_apply hIsConj x
  -- The Kummer character of `a` vanishes iff `a` is positive at `w`.
  have hdict : ∀ a : kˣ, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ a c = 0 ↔
      ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
    intro a
    rw [kummerChar_eq_zero_iff_mem_normSet ζ hζ c hc2 a,
      Work.SSGRoute.TwoTorsion.mem_normSet]
    constructor
    · -- a norm for `c` is positive at `w`
      rintro ⟨y, hy0, hy⟩
      have hcy : φ (c.toRingEquiv y) = star (φ y) :=
        NumberField.ComplexEmbedding.IsConj.eq hIsConj y
      have h1 : (v (a : k) : ℂ) = (Complex.normSq (φ y) : ℂ) := by
        have h2 : φ (algebraMap k Ω (a : k)) = φ y * star (φ y) := by
          rw [hy, map_mul, hcy]
        rw [hφ (a : k)] at h2
        rw [h2]
        exact Complex.mul_conj (φ y)
      have hveq : v (a : k) = Complex.normSq (φ y) := Complex.ofReal_injective h1
      have hy' : φ y ≠ 0 := fun h => hy0 (φ.injective (by rw [h, map_zero]))
      exact (not_isNegAt_iff hw a).mpr (by
        rw [hveq]
        exact Complex.normSq_pos.mpr hy')
    · -- a positive element is a norm for `c`
      intro hneg
      have hpos : 0 < v (a : k) := (not_isNegAt_iff hw a).mp hneg
      obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω (a : k))
        (by norm_num : (0 : ℕ) < 2)
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hm
        exact a.ne_zero ((algebraMap k Ω).injective (by rw [← hm, map_zero]))
      -- `φ m` is a square root of the real number `v a > 0`, hence fixed by conjugation.
      have hsq : (φ m) ^ 2 = (v (a : k) : ℂ) := by
        rw [← map_pow, hm, hφ (a : k)]
      have hz : star (φ m) = φ m := star_eq_self_of_sq_eq_ofReal hpos hsq
      have hcm : φ (c.toRingEquiv m) = φ m :=
        (NumberField.ComplexEmbedding.IsConj.eq hIsConj m).trans hz
      have hfix : c.toRingEquiv m = m := φ.injective hcm
      exact ⟨m, hm0, by rw [hfix, ← hm, pow_two]⟩
  refine ⟨c, hc2, ?_, hdict⟩
  -- `c` is not the identity, because `kummerChar (-1) c ≠ 0`.
  intro hc1
  have h0 : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (-1 : kˣ) c = 0 := by
    rw [hc1]
    exact kummerChar_one ζ hζ (-1)
  exact ((hdict (-1 : kˣ)).mp h0) (isNegAt_neg_one hw)

end Work.SSGRoute.ZDataTwo
