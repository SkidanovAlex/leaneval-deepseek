import Mathlib
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Polynomial.Norm

open Function Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Naive height of integer polynomials and its multiplicative bound

For a monic integer polynomial `f` define `polyHeight f` = the maximum of the
absolute values of its coefficients (a natural number).  This module proves
the key estimate, via the Mahler measure (Mathlib's
`Analysis/Polynomial/MahlerMeasure.lean`):

    polyHeight f * polyHeight g ≤ C · polyHeight (f·g)

for monic `f, g : ℤ[X]`, where `C` depends only on the degrees of `f` and `g`
(the product of the two central binomial coefficients times the degree plus
one).  The chain is:

* `polyHeight f = supNorm (fℂ)` (coefficients of an integer polynomial have
  the same sup-norm over ℤ and over ℂ);
* `supNorm ≤ binom(deg)·M`  (`supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure`);
* `M` is multiplicative  (`mahlerMeasure_mul`);
* `M ≤ √(deg+1)·supNorm`  (`mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`).

This is the analytic heart of the classical count of reducible polynomials
(van der Waerden / Chela); everything else in `Submission.Vdw.Reducible` is
elementary counting.
-/

namespace Submission.Vdw

/-- The standard embedding `ℤ → ℂ`. -/
noncomputable def φ : ℤ →+* ℂ := algebraMap ℤ ℂ

lemma φ_injective : Function.Injective φ := by
  intro a b h
  exact Int.cast_injective h

lemma φ_isometry : Isometry φ := by
  exact AddMonoidHomClass.isometry_of_norm φ (by
    intro z
    change ‖(z : ℂ)‖ = ‖z‖
    rw [Complex.norm_intCast]
    rw [Int.norm_eq_abs])

/-- Naive height of an integer polynomial: the maximum of the absolute values
of its coefficients. -/
noncomputable def polyHeight (f : ℤ[X]) : ℕ :=
  Finset.sup (Polynomial.support f) (fun i : ℕ => (f.coeff i).natAbs)

section PolyHeight

variable {f : ℤ[X]}

/-- A coefficient bound via the height, for coefficients in the support. -/
lemma natAbs_coeff_le_polyHeight_of_mem_support {i : ℕ} (hi : i ∈ f.support) :
    (f.coeff i).natAbs ≤ polyHeight f := by
  unfold polyHeight
  exact Finset.le_sup (f := fun j : ℕ => (f.coeff j).natAbs) hi

/-- Any coefficient is bounded by the height (vanishing coefficients are fine). -/
lemma natAbs_coeff_le_polyHeight (i : ℕ) :
    (f.coeff i).natAbs ≤ polyHeight f := by
  by_cases hi : f.coeff i = 0
  · simp [hi]
  · have hsup : i ∈ (Polynomial.support f) := (Polynomial.mem_support_iff).mpr hi
    exact natAbs_coeff_le_polyHeight_of_mem_support hsup

/-- The height of a monic polynomial is at least `1` (the leading coefficient
is in the support). -/
lemma one_le_polyHeight_of_Monic (hp : f.Monic) : 1 ≤ polyHeight f := by
  have hmem : f.natDegree ∈ (Polynomial.support f) := by
    rw [Polynomial.mem_support_iff]
    rw [Polynomial.coeff_natDegree]
    intro hzero
    have hlc : f.leadingCoeff = 1 := by simpa [Polynomial.Monic.def] using hp
    exact (by norm_num : (1 : ℤ) ≠ 0) (hzero ▸ hlc.symm)
  have hle := natAbs_coeff_le_polyHeight_of_mem_support hmem
  rw [Polynomial.coeff_natDegree] at hle
  have hlc : f.leadingCoeff = 1 := by simpa [Polynomial.Monic.def] using hp
  rwa [hlc] at hle

/-- `polyHeight f ≤ a` iff every coefficient has `natAbs ≤ a`. -/
lemma polyHeight_le_iff (f : ℤ[X]) (a : ℕ) :
    polyHeight f ≤ a ↔ ∀ i : ℕ, (f.coeff i).natAbs ≤ a := by
  constructor
  · intro h i
    exact (natAbs_coeff_le_polyHeight i).trans h
  · intro h
    unfold polyHeight
    rw [Finset.sup_le_iff]
    intro i hi
    exact h i

-- norm of a ℤ element cast into ℂ equals its natAbs
lemma norm_intCast_eq_natAbs (z : ℤ) : ‖(z : ℂ)‖ = (z.natAbs : ℝ) := by
  rw [Complex.norm_intCast]
  rw [← Int.cast_abs]
  congr
  rw [Int.abs_eq_natAbs]

lemma norm_int_eq_natAbs (z : ℤ) : ‖z‖ = (z.natAbs : ℝ) := by
  rw [Int.norm_eq_abs]
  rw [← Int.cast_abs]
  congr
  rw [Int.abs_eq_natAbs]

/-- For monic `f`, the sup-norm of `fℂ` equals the naive height. -/
lemma supNorm_map_eq_polyHeight (f : ℤ[X]) (hf : f.Monic) :
    (f.map φ).supNorm = (polyHeight f : ℝ) := by
  apply le_antisymm
  · -- supNorm ≤ height: the sup-norm is attained at some coefficient index
    obtain ⟨i0, hi0⟩ := (f.map φ).isGreatest_supNorm.1
    calc
      (f.map φ).supNorm = ‖(f.map φ).coeff i0‖ := hi0.symm
      _ = ‖φ (f.coeff i0)‖ := by simp
      _ = (f.coeff i0).natAbs := by
        change ‖(f.coeff i0 : ℂ)‖ = (f.coeff i0).natAbs
        exact norm_intCast_eq_natAbs (f.coeff i0)
      _ ≤ (polyHeight f : ℝ) := by
        exact_mod_cast natAbs_coeff_le_polyHeight i0
  · -- height ≤ supNorm: the maximum of the coefficient sizes is attained
    obtain ⟨i0, _hi0, hsup⟩ := Finset.exists_mem_eq_sup (Polynomial.support f)
      (by
        use f.natDegree
        rw [Polynomial.mem_support_iff]
        rw [Polynomial.coeff_natDegree]
        have hlc : f.leadingCoeff = 1 := by simpa [Polynomial.Monic.def] using hf
        rw [hlc]
        norm_num)
      (fun i : ℕ => (f.coeff i).natAbs)
    calc
      (polyHeight f : ℝ) = ((f.coeff i0).natAbs : ℝ) := by
        have hcast : polyHeight f = (f.coeff i0).natAbs := by
          rw [polyHeight]
          exact hsup
        exact_mod_cast hcast
      _ = ‖φ (f.coeff i0)‖ := by
        change ((f.coeff i0).natAbs : ℝ) = ‖(f.coeff i0 : ℂ)‖
        rw [norm_intCast_eq_natAbs (f.coeff i0)]
      _ = ‖(f.map φ).coeff i0‖ := by simp
      _ ≤ (f.map φ).supNorm := Polynomial.le_supNorm _ _

end PolyHeight

/-- The Mahler measure of the complexification of a product is the product of
the Mahler measures. -/
lemma mahlerMeasure_map_mul (f g : ℤ[X]) :
    ((f * g).map φ).mahlerMeasure = (f.map φ).mahlerMeasure * (g.map φ).mahlerMeasure := by
  rw [Polynomial.map_mul]
  exact Polynomial.mahlerMeasure_mul _ _

lemma sqrt_nat_add_one_le_self (x : ℕ) :
    Real.sqrt (((x : ℕ) : ℝ) + 1) ≤ (((x : ℕ) : ℝ) + 1) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hx1 : (1 : ℝ) ≤ ((x : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : 1 ≤ x + 1)
    nlinarith

/-- **Height-product bound.**  For monic `f, g : ℤ[X]`,
`polyHeight f · polyHeight g ≤ (k+ℓ+1)·B(k)·B(ℓ)·polyHeight (f·g)` with
`k = f.natDegree`, `ℓ = g.natDegree` and `B(m) = m.choose (m / 2)`.  -/
theorem polyHeight_mul_le (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic) :
    polyHeight f * polyHeight g ≤
      (f.natDegree + g.natDegree + 1) *
      (f.natDegree.choose (f.natDegree / 2)) *
      (g.natDegree.choose (g.natDegree / 2)) * polyHeight (f * g) := by
  -- all inequalities below are inequalities of reals; cast back at the end.
  have hf0 : f ≠ 0 := Polynomial.Monic.ne_zero hf
  have hg0 : g ≠ 0 := Polynomial.Monic.ne_zero hg
  have hfg0 : f * g ≠ 0 := mul_ne_zero hf0 hg0
  have hFmon : (f.map φ).Monic := hf.map φ
  have hGmon : (g.map φ).Monic := hg.map φ
  have hfgmon : ((f * g).map φ).Monic := (Polynomial.Monic.mul hf hg).map φ
  have h1f : ((polyHeight f : ℝ) ≤
      (f.natDegree.choose (f.natDegree / 2) : ℝ) * (f.map φ).mahlerMeasure) := by
    calc
      (polyHeight f : ℝ) = (f.map φ).supNorm := (supNorm_map_eq_polyHeight f hf).symm
      _ ≤ (f.natDegree.choose (f.natDegree / 2) : ℝ) * (f.map φ).mahlerMeasure := by
        simpa [Polynomial.natDegree_map_eq_of_injective φ_injective f] using
          (f.map φ).supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
  have h1g : ((polyHeight g : ℝ) ≤
      (g.natDegree.choose (g.natDegree / 2) : ℝ) * (g.map φ).mahlerMeasure) := by
    calc
      (polyHeight g : ℝ) = (g.map φ).supNorm := (supNorm_map_eq_polyHeight g hg).symm
      _ ≤ (g.natDegree.choose (g.natDegree / 2) : ℝ) * (g.map φ).mahlerMeasure := by
        simpa [Polynomial.natDegree_map_eq_of_injective φ_injective g] using
          (g.map φ).supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
  -- M(f·g) ≤ √(k+ℓ+1) · H(f·g) ≤ (k+ℓ+1) · H(f·g)
  have hM : (f.map φ).mahlerMeasure * (g.map φ).mahlerMeasure ≤
      (((f.natDegree + g.natDegree + 1 : ℕ) : ℝ) * (polyHeight (f * g) : ℝ)) := by
    calc
      (f.map φ).mahlerMeasure * (g.map φ).mahlerMeasure =
          ((f * g).map φ).mahlerMeasure := (mahlerMeasure_map_mul f g).symm
      _ ≤ Real.sqrt ((((f * g).map φ).natDegree : ℝ) + 1) * ((f * g).map φ).supNorm := by
        exact ((f * g).map φ).mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
      _ ≤ Real.sqrt (((f.natDegree + g.natDegree : ℕ) : ℝ) + 1) * ((f * g).map φ).supNorm := by
        have hnd : ((f * g).map φ).natDegree = f.natDegree + g.natDegree := by
          rw [Polynomial.natDegree_map_eq_of_injective φ_injective (f * g)]
          exact Polynomial.natDegree_mul hf0 hg0
        rw [hnd]
      _ ≤ (((f.natDegree + g.natDegree : ℕ) : ℝ) + 1) * ((f * g).map φ).supNorm := by
        have hs := sqrt_nat_add_one_le_self (f.natDegree + g.natDegree)
        have hsup0 : (0 : ℝ) ≤ ((f * g).map φ).supNorm := Polynomial.supNorm_nonneg _
        nlinarith
      _ = (((f.natDegree + g.natDegree + 1 : ℕ) : ℝ)) * (polyHeight (f * g) : ℝ) := by
        have hsup : ((f * g).map φ).supNorm = (polyHeight (f * g) : ℝ) :=
          supNorm_map_eq_polyHeight (f * g) (Polynomial.Monic.mul hf hg)
        rw [hsup]
        norm_num
  have hMprod := hM
  -- multiply the two per-factor bounds and conclude
  have hmain : (((polyHeight f * polyHeight g) : ℕ) : ℝ) ≤
      ((((f.natDegree + g.natDegree + 1) * (f.natDegree.choose (f.natDegree / 2)) *
        (g.natDegree.choose (g.natDegree / 2)) * polyHeight (f * g)) : ℕ) : ℝ) := by
    calc
      (((polyHeight f * polyHeight g) : ℕ) : ℝ)
          = (polyHeight f : ℝ) * (polyHeight g : ℝ) := by norm_num
      _ ≤ ((f.natDegree.choose (f.natDegree / 2) : ℝ) * (f.map φ).mahlerMeasure) *
          ((g.natDegree.choose (g.natDegree / 2) : ℝ) * (g.map φ).mahlerMeasure) := by
        exact mul_le_mul h1f h1g (by exact_mod_cast Nat.zero_le _)
          (by exact mul_nonneg (by positivity) (Polynomial.mahlerMeasure_nonneg _))
      _ = ((f.natDegree.choose (f.natDegree / 2) : ℝ) *
          (g.natDegree.choose (g.natDegree / 2) : ℝ)) *
          ((f.map φ).mahlerMeasure * (g.map φ).mahlerMeasure) := by ring
      _ ≤ ((f.natDegree.choose (f.natDegree / 2) : ℝ) *
          (g.natDegree.choose (g.natDegree / 2) : ℝ)) *
          (((f.natDegree + g.natDegree + 1 : ℕ) : ℝ) * (polyHeight (f * g) : ℝ)) := by
        have hb0 : (0 : ℝ) ≤ (f.natDegree.choose (f.natDegree / 2) : ℝ) := by positivity
        have hb0' : (0 : ℝ) ≤ (g.natDegree.choose (g.natDegree / 2) : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hM (mul_nonneg hb0 hb0')
      _ = ((((f.natDegree + g.natDegree + 1) * (f.natDegree.choose (f.natDegree / 2)) *
          (g.natDegree.choose (g.natDegree / 2)) * polyHeight (f * g)) : ℕ) : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
  exact_mod_cast hmain

end Submission.Vdw
