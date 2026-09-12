import Mathlib
import Submission.Conjugates
import Submission.ConjPoly
import Submission.Powers
import Submission.Minpoly
import Submission.Rays
import Submission.PowRev

/-!
# The engine polynomial `G = R₂ · R₄` does not vanish on the cut plane

Fix a number field element `α` with `P := minpoly ℤ α` monic of degree `d`
and conjugate set `S := conjugateValues α` (all nonzero if `α ≠ 0`).  The
engine's polynomial is

    G := (pow2 P).reflect d * (pow4 P).reflect d ∈ ℤ[w]

(its coefficients are those whose formal square root `a` is produced by
`Submission.PowRev.powRev_sqrt_integral`).  We prove here, from the product
factorizations of `pow2 P` and `pow4 P` over `ℂ`:

1. for `w ≠ 0`,  `G(w) = ∏_{z∈S} (1 - z²w) · ∏_{z∈S} (1 - z⁴w)`   (evaluation
   identity of complex numbers), and `G(0) = G.coeff 0 = 1`;
2. hence `G` has no zero on the cut plane `Submission.Rays.cutPlane C` where

        C := (S.image (fun z => (z ^ 2)⁻¹)) ∪ (S.image (fun z => (z ^ 4)⁻¹))

   (every root of `G` is one of the `1/z²`, `1/z⁴`, which lie on the rays
   defining the cut plane).

## Where the evaluation identity comes from

`Polynomial.eval₂_reflect_mul_pow` (`Mathlib/Algebra/Polynomial/Reverse.lean`):
for `f : R[X]` with `f.natDegree ≤ N` and invertible `x`,
`eval₂ i (⅟x) (reflect N f) * x ^ N = eval₂ i x f`; putting `x := w⁻¹` gives,
over `ℂ` with `w ≠ 0`:

    eval₂ φ w (reflect N f) = w ^ N * eval₂ φ (w⁻¹) f .

Over `ℂ`, `(pow2 P).map φ = ∏_{z∈S} (X - C (z²))`
(`Submission.Descent.pow2_complex_prod_sq`), so evaluating at `w⁻¹`:

    eval₂ φ (w⁻¹) (pow2 P) = ∏_{z∈S} (w⁻¹ - z²) = w⁻ᵈ · ∏_{z∈S} (1 - z²w)

(`natDegree (pow2 P) = d` by `Submission.RootCorr.pow2_natDegree`), and the
`w^d` factor from the reflection cancels, leaving `∏(1 - z²w)`; similarly for
`pow4` with `z⁴`.  The constant term: `(pow2 P).reflect d` and
`(pow4 P).reflect d` both have constant term `1`
(`Submission.PowRev.reflect_pow2_coeff_zero`, `reflect_pow4_coeff_zero`), so
`G.coeff 0 = 1`.

You may add helper lemmas.  Do NOT change the statements of the declarations
below.  No sorries may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial Real Topology

namespace Submission.GOnCutPlane

open Submission.Conjugates
open Submission.ConjPoly
open Submission.Powers
open Submission.Minpoly
open Submission.Rays
open Submission.RootCorr
open Submission.Dictionary
open Submission.PowRev

/-- The engine polynomial: `G := (pow2 P).reflect d * (pow4 P).reflect d`,
with `d := P.natDegree`.  (Constant term 1.) -/
def Gpoly (P : ℤ[X]) : ℤ[X] :=
  (pow2 P).reflect P.natDegree * (pow4 P).reflect P.natDegree

set_option linter.style.haveILetI false in
/-- Reflection evaluation in a field: `eval w (f.reflect N) = w^N · eval (w⁻¹) f`
for `natDegree f ≤ N` and `w ≠ 0`. -/
lemma eval_reflect_pow {R : Type*} [Field R] (f : R[X]) (N : ℕ) (hf : f.natDegree ≤ N)
    (w : R) (hw : w ≠ 0) :
    Polynomial.eval w (f.reflect N) = w ^ N * Polynomial.eval (w⁻¹) f := by
  classical
  letI : Invertible w := invertibleOfNonzero hw
  have hdeg : (f.reflect N).natDegree ≤ N := by
    exact le_trans (Polynomial.natDegree_reflect_le (N := N) (p := f))
      (by omega : max N f.natDegree ≤ N)
  have h := Polynomial.eval₂_reflect_mul_pow (i := RingHom.id R) (x := w) N (f.reflect N) hdeg
  -- h : eval₂ id (⅟w) (reflect N (reflect N f)) * w^N = eval₂ id w (f.reflect N)
  have h' : eval₂ (RingHom.id R) (w⁻¹) f * w ^ N = eval₂ (RingHom.id R) w (f.reflect N) := by
    simpa using h
  calc
    Polynomial.eval w (f.reflect N) = eval₂ (RingHom.id R) w (f.reflect N) := by rfl
    _ = eval₂ (RingHom.id R) (w⁻¹) f * w ^ N := by rw [← h']
    _ = w ^ N * Polynomial.eval (w⁻¹) f := by
      rw [← eval₂_id]
      rw [mul_comm]


/-- Over `ℂ`, `pow2 (minpoly ℤ α)` factors into the linear factors of the
conjugate squares: `(pow2 P)̅ = ∏_{z∈S} (X - z²)`. -/
lemma pow2_minpoly_map_prod {K : Type*} [Field K] [NumberField K] (α : K)
    (hα : IsIntegral ℤ α) :
    ((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)) =
      (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2)) := by
  calc
    ((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ))
        = pow2 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) := by
            exact pow2_map (minpoly ℤ α) (algebraMap ℤ ℂ) (minpoly_int_monic α hα)
    _ = pow2 ((conjugateValues α).prod (fun z : ℂ => X - C z)) := by
            rw [minpoly_complex_eq_prod α hα]
    _ = (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2)) := by
            exact pow2_prod_X_sub_C_sq (conjugateValues α) (fun z : ℂ => z)

/-- Over `ℂ`, `pow4 (minpoly ℤ α)` factors into the linear factors of the
conjugate fourth powers: `(pow4 P)̅ = ∏_{z∈S} (X - z⁴)`. -/
lemma pow4_minpoly_map_prod {K : Type*} [Field K] [NumberField K] (α : K)
    (hα : IsIntegral ℤ α) :
    ((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ)) =
      (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4)) := by
  calc
    ((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ))
        = pow4 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) := by
            exact pow4_map (minpoly ℤ α) (algebraMap ℤ ℂ) (minpoly_int_monic α hα)
    _ = pow4 ((conjugateValues α).prod (fun z : ℂ => X - C z)) := by
            rw [minpoly_complex_eq_prod α hα]
    _ = (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4)) := by
            exact pow4_prod (conjugateValues α)

/-- Evaluating the reflected linear-factor product at `w ≠ 0`:
`reflect |T| (∏_z (X - u z))` evaluated at `w` is `∏_z (1 - (u z)·w)`. -/
lemma eval_reflect_prod (T : Finset ℂ) (u : ℂ → ℂ) (w : ℂ) (hw : w ≠ 0) :
    Polynomial.eval w ((T.prod (fun z : ℂ => X - C (u z))).reflect T.card) =
      T.prod (fun z : ℂ => 1 - u z * w) := by
  classical
  have hdeg : (T.prod (fun z : ℂ => X - C (u z))).natDegree ≤ T.card := by
    rw [natDegree_prod_X_sub_C_of T u]
  have hrefl := eval_reflect_pow (T.prod (fun z : ℂ => X - C (u z))) T.card hdeg w hw
  -- hrefl : eval w (...reflect T.card) = w^T.card * eval (w⁻¹) (T.prod ...)
  have hevalm1 : Polynomial.eval (w⁻¹) (T.prod (fun z : ℂ => X - C (u z))) =
      T.prod (fun z : ℂ => w⁻¹ - u z) := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro z hz
    simp
  calc
    Polynomial.eval w ((T.prod (fun z : ℂ => X - C (u z))).reflect T.card)
        = w ^ T.card * Polynomial.eval (w⁻¹) (T.prod (fun z : ℂ => X - C (u z))) := hrefl
    _ = w ^ T.card * T.prod (fun z : ℂ => w⁻¹ - u z) := by rw [hevalm1]
    _ = T.prod (fun z : ℂ => 1 - u z * w) := by
      have hconst : w ^ T.card = T.prod (fun _ : ℂ => w) := by
        rw [Finset.prod_const]
      rw [hconst]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro z hz
      calc
        w * (w⁻¹ - u z) = w * w⁻¹ - w * u z := by ring
        _ = 1 - w * u z := by rw [mul_inv_cancel₀ hw]
        _ = 1 - u z * w := by ring

/-- `Gpoly P` has constant term `1`. -/
lemma coeff_zero_Gpoly (P : ℤ[X]) (hP : P.Monic) : (Gpoly P).coeff 0 = 1 := by
  rw [Gpoly]
  rw [Polynomial.mul_coeff_zero]
  rw [reflect_pow2_coeff_zero P hP, reflect_pow4_coeff_zero P hP]
  norm_num

/-- **Evaluation identity.**  For `P := minpoly ℤ α` of degree `d`, and
`w ≠ 0`:

    (Gpoly P)(w) = (∏ z∈S, 1 - z²·w) · (∏ z∈S, 1 - z⁴·w)

in `ℂ`, where `S := conjugateValues α`. -/
theorem eval₂_Gpoly_eq_prod {K : Type*} [Field K] [NumberField K] (α : K)
    (hα : IsIntegral ℤ α) {w : ℂ} (hw : w ≠ 0) :
    (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) w =
      ((conjugateValues α).prod (fun z : ℂ => 1 - z ^ 2 * w)) *
        ((conjugateValues α).prod (fun z : ℂ => 1 - z ^ 4 * w)) := by
  classical
  -- the reflected square product evaluates to ∏(1 - z²w)
  have hR2 : Polynomial.eval w ((((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
      (minpoly ℤ α).natDegree)) =
      (conjugateValues α).prod (fun z : ℂ => 1 - z ^ 2 * w) := by
    calc
      Polynomial.eval w ((((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
          (minpoly ℤ α).natDegree))
          = Polynomial.eval w ((((conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2))).reflect
              (minpoly ℤ α).natDegree)) := by
              rw [pow2_minpoly_map_prod α hα]
          _ = (conjugateValues α).prod (fun z : ℂ => 1 - z ^ 2 * w) := by
              rw [minpoly_natDegree_eq_card α hα]
              exact eval_reflect_prod (conjugateValues α) (fun z : ℂ => z ^ 2) w hw
  -- and the reflected fourth-power product evaluates to ∏(1 - z⁴w)
  have hR4 : Polynomial.eval w ((((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
      (minpoly ℤ α).natDegree)) =
      (conjugateValues α).prod (fun z : ℂ => 1 - z ^ 4 * w) := by
    calc
      Polynomial.eval w ((((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
          (minpoly ℤ α).natDegree))
          = Polynomial.eval w ((((conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4))).reflect
              (minpoly ℤ α).natDegree)) := by
              rw [pow4_minpoly_map_prod α hα]
          _ = (conjugateValues α).prod (fun z : ℂ => 1 - z ^ 4 * w) := by
              rw [minpoly_natDegree_eq_card α hα]
              exact eval_reflect_prod (conjugateValues α) (fun z : ℂ => z ^ 4) w hw
  calc
    (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) w
        = Polynomial.eval w ((Gpoly (minpoly ℤ α)).map (algebraMap ℤ ℂ)) := by
            rw [Polynomial.eval₂_eq_eval_map]
    _ = Polynomial.eval w ((((pow2 (minpoly ℤ α)).reflect (minpoly ℤ α).natDegree) *
            ((pow4 (minpoly ℤ α)).reflect (minpoly ℤ α).natDegree)).map (algebraMap ℤ ℂ)) := by
            rfl
    _ = Polynomial.eval w ((((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
            (minpoly ℤ α).natDegree) *
            (((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
            (minpoly ℤ α).natDegree)) := by
            rw [Polynomial.map_mul]
            rw [← Polynomial.reflect_map]
            rw [← Polynomial.reflect_map]
    _ = Polynomial.eval w ((((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
            (minpoly ℤ α).natDegree)) *
          Polynomial.eval w ((((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ)).reflect
            (minpoly ℤ α).natDegree)) := by
            rw [Polynomial.eval_mul]
    _ = (conjugateValues α).prod (fun z : ℂ => 1 - z ^ 2 * w) *
          (conjugateValues α).prod (fun z : ℂ => 1 - z ^ 4 * w) := by
            rw [hR2, hR4]

/-- `G(0) = 1`, so `G` does not vanish at `0`. -/
lemma eval₂_Gpoly_zero {K : Type*} [Field K] [NumberField K] (α : K)
    (hα : IsIntegral ℤ α) : (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) 0 = 1 := by
  rw [Polynomial.eval₂_at_zero]
  rw [coeff_zero_Gpoly (minpoly ℤ α) (minpoly_int_monic α hα)]
  norm_num

/-- For a nonzero conjugate `z` of `α`, if `w` is not on the ray of
`(zⁿ)⁻¹` then the factor `1 - zⁿ·w` is nonzero. -/
lemma factor_ne_zero_of_not_mem_ray {K : Type*} [Field K] [NumberField K] (α : K)
    (hα0 : α ≠ 0) {w : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ conjugateValues α)
    (hnotray : w ∉ ray ((z ^ n)⁻¹)) : 1 - z ^ n * w ≠ 0 := by
  intro hf0
  have h1 : 1 = z ^ n * w := sub_eq_zero.mp hf0
  have hEq : z ^ n * w = 1 := h1.symm
  have hz0 : z ≠ 0 := by
    intro hz0
    exact (zero_not_mem_conjugateValues (α := α) hα0) (by simpa [hz0] using hz)
  have hzn0 : z ^ n ≠ 0 := pow_ne_zero n hz0
  have hw : w = (z ^ n)⁻¹ := by
    calc
      w = 1 * w := by rw [one_mul]
      _ = ((z ^ n)⁻¹ * z ^ n) * w := by rw [inv_mul_cancel₀ hzn0]
      _ = (z ^ n)⁻¹ * (z ^ n * w) := by ring
      _ = (z ^ n)⁻¹ * 1 := by rw [hEq]
      _ = (z ^ n)⁻¹ := by rw [mul_one]
  have hwray : w ∈ ray ((z ^ n)⁻¹) := by
    rw [hw]
    exact ⟨1, le_rfl, by simp⟩
  exact hnotray hwray

/-- **`G` is nonvanishing on the cut plane** defined from the roots
`{1/z², 1/z⁴ : z ∈ S}`. -/
theorem Gpoly_ne_zero_on_cutPlane {K : Type*} [Field K] [NumberField K] (α : K)
    (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    let S : Finset ℂ := conjugateValues α
    let C : Finset ℂ := (S.image (fun z : ℂ => (z ^ 2)⁻¹)) ∪
      (S.image (fun z : ℂ => (z ^ 4)⁻¹))
    ∀ w ∈ cutPlane C, (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) w ≠ 0 := by
  classical
  change ∀ w ∈ cutPlane ((conjugateValues α).image (fun z : ℂ => (z ^ 2)⁻¹) ∪
      (conjugateValues α).image (fun z : ℂ => (z ^ 4)⁻¹)),
      (Gpoly (minpoly ℤ α)).eval₂ (algebraMap ℤ ℂ) w ≠ 0
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    have hz := eval₂_Gpoly_zero α hα
    rw [hz]
    norm_num
  · rw [eval₂_Gpoly_eq_prod α hα (w := w) hw0]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro z hz
      refine factor_ne_zero_of_not_mem_ray α hα0 (n := 2) hz ?_
      intro hwray
      exact hw ((z ^ 2)⁻¹) (Finset.mem_union.mpr (Or.inl
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩))) hwray
    · rw [Finset.prod_ne_zero_iff]
      intro z hz
      refine factor_ne_zero_of_not_mem_ray α hα0 (n := 4) hz ?_
      intro hwray
      exact hw ((z ^ 4)⁻¹) (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩))) hwray

end Submission.GOnCutPlane

end
