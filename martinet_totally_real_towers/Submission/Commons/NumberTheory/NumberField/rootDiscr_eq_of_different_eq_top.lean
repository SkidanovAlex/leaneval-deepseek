import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open scoped NumberField
open NumberField

namespace Commons.NumberTheory.NumberField

/-- The absolute value of an integer, coerced to the reals, is its `natAbs`. -/
private lemma int_abs_natAbs (x : ℤ) : |(x : ℝ)| = (x.natAbs : ℝ) := by
  calc
    |(x : ℝ)| = ((|x| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ = ((x.natAbs : ℤ) : ℝ) := by rw [Int.abs_eq_natAbs]
    _ = (x.natAbs : ℝ) := by norm_num

/-- If the relative different of a number-field extension `E ⊆ K` is the unit
ideal, then the absolute discriminant of `K` is the `[K : E]`-th power of the
absolute discriminant of `E`, as natural numbers. -/
private lemma natAbs_discr_pow_of_different_eq_top {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (h : differentIdeal (𝓞 E) (𝓞 K) = ⊤) :
    (NumberField.discr K).natAbs = (NumberField.discr E).natAbs ^ Module.finrank E K := by
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := E) (𝒪 := 𝓞 E) (L := K) (𝒪' := 𝓞 K)]
  simp [h]

/-- Real-valued version: `|discr K| = |discr E| ^ [K : E]` as real numbers. -/
private lemma abs_discr_pow_of_different_eq_top {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (h : differentIdeal (𝓞 E) (𝓞 K) = ⊤) :
    |(NumberField.discr K : ℝ)| =
      |(NumberField.discr E : ℝ)| ^ Module.finrank E K := by
  calc
    |(NumberField.discr K : ℝ)| = ((NumberField.discr K).natAbs : ℝ) := by
      rw [int_abs_natAbs]
    _ = (((NumberField.discr E).natAbs ^ Module.finrank E K : ℕ) : ℝ) := by
      rw [natAbs_discr_pow_of_different_eq_top h]
    _ = ((NumberField.discr E).natAbs : ℝ) ^ Module.finrank E K := by
      rw [Nat.cast_pow]
    _ = |(NumberField.discr E : ℝ)| ^ Module.finrank E K := by
      rw [int_abs_natAbs]

/-- The root discriminant is invariant under unramified tower steps: if the
relative different of the number-field extension `E ⊆ K` is trivial, then
`rootDiscr K = rootDiscr E`.  (Root discriminants
`NumberField.rootDiscr K = |discr K| ^ (1 / [K : ℚ])` are constant along an
everywhere-unramified tower; Martinet's asymptotically-good totally real
towers have this property at every step.)

Proof sketch.  From `abs_discr_pow_of_different_eq_top`:
`|discr K| = |discr E| ^ m` with `m = Module.finrank E K`, and
`Module.finrank ℚ K = m * Module.finrank ℚ E`
(`Module.finrank_mul_finrank`), with `m ≠ 0`, `Module.finrank ℚ E ≠ 0`.
Then by real `rpow` algebra (use `Real.rpow_mul`, `Real.mul_rpow`,
`Real.rpow_inv_natCast_pow`; `|discr E| ≥ 1` so all bases are positive):
`rootDiscr K = (|discr E| ^ m) ^ (1 / (m * [E:ℚ])) = |discr E| ^ (1/[E:ℚ]) =
rootDiscr E`. -/
theorem rootDiscr_eq_of_different_eq_top {E K : Type*} [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K]
    (h : differentIdeal (𝓞 E) (𝓞 K) = ⊤) :
    NumberField.rootDiscr K = NumberField.rootDiscr E := by
  have hfin : Module.finrank ℚ K = Module.finrank ℚ E * Module.finrank E K := by
    exact (Module.finrank_mul_finrank (F := ℚ) (K := E) (A := K)).symm
  have hfinK_real : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ E : ℝ) * (Module.finrank E K : ℝ) := by
    rw [← Nat.cast_mul, hfin]
  have hmne : (Module.finrank E K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := E) (M := K)).ne'
  have hene : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have h_exp : (Module.finrank E K : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ =
      (Module.finrank ℚ E : ℝ)⁻¹ := by
    rw [hfinK_real]
    field_simp [hmne, hene]
  rw [NumberField.rootDiscr_def K, NumberField.rootDiscr_def E]
  simp only [Int.cast_abs]
  rw [abs_discr_pow_of_different_eq_top h]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg _)]
  rw [h_exp]

end Commons.NumberTheory.NumberField