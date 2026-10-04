import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.norm_sq_Lp_eq_integral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bessel's inequality for Fourier coefficients of a continuous function on the cube

Layer A of the STE Fourier toolkit.  For `g : (ι → ℝ) → ℂ` **continuous** (no periodicity and
no integrability hypothesis is needed), the Fourier coefficient family
`k ↦ fourierCoeff g k = ∫_{unitCube} fourierExp (-k) · g` is square summable and its `ℓ²` norm
is bounded by the `L²` norm of `g`:

  `Σ_k ‖fourierCoeff g k‖² ≤ ∫_{unitCube} ‖g‖²`.

This is Bessel's inequality for the family of characters, which is orthonormal in the Hilbert
space `L²(unitCube)`.  The proof therefore goes through the `L²` space of the cube:

* `memLp_of_continuous` : a continuous function is `L²` on the cube (the cube is contained in
  the compact set `[0,1]^ι`, on which `g` is bounded);
* `charLp` : the character `fourierExp k` as an element of `L²(unitCube)`;
* `orthonormal_charLp` : the characters are orthonormal, `⟪charLp i, charLp j⟫ = δ_{ij}`;
* `inner_charLp_toLp` : `⟪charLp k, g⟫ = fourierCoeff g k`;
* `norm_sq_Lp_eq_integral` (sibling file) : `‖u‖² = ∫ ‖u‖²` for `u : L²`;
* Mathlib's `Orthonormal.inner_products_summable` and `Orthonormal.tsum_inner_products_le`
  (Bessel's inequality) then give the result.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped ComplexConjugate

namespace Work.Diff.STE

namespace BesselCont

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma measSet_unitCube : MeasurableSet (unitCube (ι := ι)) := by
  rw [unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

lemma vol_unitCube : (volume : Measure (ι → ℝ)) (unitCube (ι := ι)) = 1 := by
  rw [unitCube, Real.volume_pi_Ioc]
  simp

lemma isFiniteMeasure_restrict_unitCube :
    IsFiniteMeasure (volume.restrict (unitCube (ι := ι))) :=
  isFiniteMeasure_restrict.2 (by rw [vol_unitCube]; exact ENNReal.one_ne_top)

lemma norm_fourierExp_char (k : ι → ℤ) (x : ι → ℝ) : ‖fourierExp k x‖ = 1 := by
  have hmain : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, ((k i : ℤ) : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierExp, hmain, Complex.norm_exp_ofReal_mul_I]

lemma fourierExp_eq_real (k : ι → ℤ) (x : ι → ℝ) :
    fourierExp k x
      = Complex.exp (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ) : ℂ) * Complex.I) := by
  rw [fourierExp]; congr 1; push_cast; ring

lemma star_fourierExp_char (k : ι → ℤ) (x : ι → ℝ) :
    star (fourierExp k x) = fourierExp (-k) x := by
  rw [fourierExp_eq_real k x, fourierExp_eq_real (-k) x]
  have hc : (2 * Real.pi * ∑ i, (((-k) i : ℤ) : ℝ) * x i : ℝ)
      = -(2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * x i : ℝ) := by
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul]
    rw [Finset.sum_neg_distrib]
    ring
  rw [hc]
  have hstar : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := fun z => by simp
  rw [hstar]
  congr 1
  simp

lemma fourierExp_add_char (m n : ι → ℤ) (x : ι → ℝ) :
    fourierExp m x * fourierExp n x = fourierExp (m + n) x := by
  rw [fourierExp, fourierExp, fourierExp, ← Complex.exp_add]
  congr 1
  have h : (∑ i, (((m + n) i : ℤ) : ℂ) * (x i : ℂ))
      = (∑ i, ((m i : ℤ) : ℂ) * (x i : ℂ)) + ∑ i, ((n i : ℤ) : ℂ) * (x i : ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply, Int.cast_add]; ring)
  rw [h]; ring

lemma continuous_fourierExp_char (k : ι → ℤ) : Continuous (fourierExp k) := by
  rw [show fourierExp k = fun x : ι → ℝ =>
      Complex.exp ((2 * (Real.pi : ℝ) : ℂ) * Complex.I * ∑ j, ((k j : ℤ) : ℂ) * (x j : ℂ))
      from rfl]
  exact Complex.continuous_exp.comp (by fun_prop)

lemma memLp_fourierExp_char (k : ι → ℤ) :
    MemLp (fourierExp k) 2 (volume.restrict (unitCube (ι := ι))) := by
  haveI : IsFiniteMeasure (volume.restrict (unitCube (ι := ι))) :=
    isFiniteMeasure_restrict_unitCube
  refine MemLp.of_bound (f := fourierExp k)
    (((continuous_fourierExp_char k).aestronglyMeasurable).mono_measure
      (Measure.restrict_le_self (μ := volume) (s := unitCube))) 1 ?_
  filter_upwards with x
  rw [norm_fourierExp_char]

/-- A continuous function on `ι → ℝ` is square integrable on the unit cube: the cube is
contained in the compact set `[0,1]^ι`, on which a continuous function is bounded. -/
lemma memLp_of_continuous (g : (ι → ℝ) → ℂ) (hg : Continuous g) :
    MemLp g 2 (volume.restrict (unitCube (ι := ι))) := by
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable.restrict]
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC (hg.norm.pow 2).continuousOn).mono_set hsub

/-- The character `fourierExp k` as an element of `L²` of the unit cube. -/
def charLp (k : ι → ℤ) : Lp ℂ 2 (volume.restrict (unitCube (ι := ι))) :=
  (memLp_fourierExp_char k).toLp (fourierExp k)

/-- The characters are orthonormal in `L²(unitCube)`. -/
lemma orthonormal_charLp :
    Orthonormal ℂ (charLp (ι := ι) :
      (ι → ℤ) → Lp ℂ 2 (volume.restrict (unitCube (ι := ι)))) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a : ι → ℝ => inner ℂ (charLp i a) (charLp j a))
      =ᵐ[volume.restrict (unitCube (ι := ι))]
        (fun a : ι → ℝ => fourierExp (-i) a * fourierExp j a) := by
    filter_upwards [(memLp_fourierExp_char i).coeFn_toLp,
      (memLp_fourierExp_char j).coeFn_toLp] with a hi hj
    simp only [charLp]
    rw [hi, hj, RCLike.inner_apply', starRingEnd_apply, star_fourierExp_char i a]
  rw [integral_congr_ae h1]
  have h2 : (fun a : ι → ℝ => fourierExp (-i) a * fourierExp j a)
      = fun a : ι → ℝ => fourierExp (j - i) a := by
    funext a
    rw [fourierExp_add_char]
    congr 1
    simp [sub_eq_add_neg, add_comm]
  rw [h2, integral_fourierExp]
  simp only [sub_eq_zero, eq_comm]

/-- The `L²` inner product of a character with a square integrable function is its Fourier
coefficient. -/
lemma inner_charLp_toLp (g : (ι → ℝ) → ℂ)
    (hg : MemLp g 2 (volume.restrict (unitCube (ι := ι)))) (k : ι → ℤ) :
    inner ℂ (charLp k) (hg.toLp g) = fourierCoeff g k := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a : ι → ℝ => inner ℂ (charLp k a) ((hg.toLp g) a))
      =ᵐ[volume.restrict (unitCube (ι := ι))]
        (fun a : ι → ℝ => fourierExp (-k) a * g a) := by
    filter_upwards [(memLp_fourierExp_char k).coeFn_toLp, hg.coeFn_toLp] with a hk hg'
    simp only [charLp]
    rw [hk, hg', RCLike.inner_apply', starRingEnd_apply, star_fourierExp_char k a]
  rw [integral_congr_ae h1]
  rfl

end BesselCont

open BesselCont in
theorem bessel_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) (hg : Continuous g) :
    Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) ∧
      ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2
        ≤ ∫ x in Work.Diff.STE.unitCube, ‖g x‖ ^ 2 := by
  have hmem := memLp_of_continuous g hg
  have horth := orthonormal_charLp (ι := ι)
  have hinner : ∀ k : ι → ℤ, inner ℂ (charLp k) (hmem.toLp g) = fourierCoeff g k :=
    fun k => inner_charLp_toLp g hmem k
  have hs : Summable (fun k : ι → ℤ => ‖inner ℂ (charLp k) (hmem.toLp g)‖ ^ 2) :=
    horth.inner_products_summable (hmem.toLp g)
  have hb : ∑' k : ι → ℤ, ‖inner ℂ (charLp k) (hmem.toLp g)‖ ^ 2
      ≤ ‖hmem.toLp g‖ ^ 2 :=
    horth.tsum_inner_products_le (hmem.toLp g)
  have hnorm : ‖hmem.toLp g‖ ^ 2 = ∫ x in unitCube, ‖g x‖ ^ 2 := by
    rw [norm_sq_Lp_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
  refine ⟨hs.congr (fun k => by rw [hinner k]), ?_⟩
  calc ∑' k : ι → ℤ, ‖fourierCoeff g k‖ ^ 2
      = ∑' k : ι → ℤ, ‖inner ℂ (charLp k) (hmem.toLp g)‖ ^ 2 :=
        tsum_congr (fun k => by rw [hinner k])
    _ ≤ ‖hmem.toLp g‖ ^ 2 := hb
    _ = ∫ x in unitCube, ‖g x‖ ^ 2 := hnorm

end Work.Diff.STE
