import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseFixB1S.PiAnovaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PiAnova.piVarianceDecomp` — the Pythagorean (variance) decomposition

On the product measure `π = Measure.pi (fun _ : Fin (k+1) => ν)` the coordinate mean

`m x = (ν univ).toReal⁻¹ ∫ z, f (update x j z) ∂ν`

is the conditional expectation of `f` given all the coordinates other than `j`; in particular it is
the orthogonal projection of `f` onto the functions independent of coordinate `j`.  Since a
constant `c` is independent of every coordinate, the Pythagorean theorem for this projection gives

`∫ (f - c)² = ∫ (f - m)² + ∫ (m - c)²`   for every `c : ℝ`.

The two ingredients are

* the **tower/orthogonality identity** `Work.BoseFixB1S.pi_tower_right`:
  `∫ u w = ∫ (E_j u) w` whenever `w` is independent of coordinate `j` — applied with `u = f` and
  `w = m - c` this gives `∫ f (m-c) = ∫ m (m-c)`, hence the cross term `∫ (f-m)(m-c)` vanishes;
* the **`L²` theory of the coordinate mean** `Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le`,
  which shows that `m` — and every function built from `f` and `m` that occurs in the expansion — is
  integrable, so that the binomial expansion `(f-c)² = (f-m)² + (m-c)² + 2(f-m)(m-c)` can be
  integrated term by term.
-/

namespace Work.BoseFixB1S.PiAnova

open MeasureTheory

theorem piVarianceDecomp {α : Type*} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
    [MeasureTheory.SigmaFinite ν] [MeasureTheory.IsFiniteMeasure ν]
    (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {f : (Fin (k + 1) → α) → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hf2 : MeasureTheory.Integrable (fun x => (f x) ^ 2)
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)))
    (c : ℝ) :
    ∫ x, (f x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, (f x - (1 / (ν Set.univ).toReal) * ∫ z, f (Function.update x j z) ∂ν) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
        + ∫ x, ((1 / (ν Set.univ).toReal) * ∫ z, f (Function.update x j z) ∂ν - c) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let m : (Fin (k + 1) → α) → ℝ :=
    fun x => (1 / (ν Set.univ).toReal) * ∫ z, f (Function.update x j z) ∂ν
  change ∫ x, (f x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, (f x - m x) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
        + ∫ x, (m x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
  -- measurability of the coordinate mean
  have hmm : AEStronglyMeasurable m (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    (Work.BoseFixB1S.aestronglyMeasurable_pi_coordMean ν j hfm).const_mul (1 / (ν Set.univ).toReal)
  -- the coordinate mean is in `L²` (with `∫ m² ≤ ∫ f²`)
  have hm2 : Integrable (fun x => (m x) ^ 2) (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    (Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le ν hν j hfm hf2).1
  -- `f` is integrable (finite measure, `f ∈ L²`)
  have hf1 : Integrable f (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (f x) ^ 2 + 1)
      (hf2.add (integrable_const 1)) hfm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (f x), sq_abs (f x), le_abs_self (f x), neg_le_abs (f x)]
  -- `m` is integrable
  have hm1 : Integrable m (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (m x) ^ 2 + 1)
      (hm2.add (integrable_const 1)) hmm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (m x), sq_abs (m x), le_abs_self (m x), neg_le_abs (m x)]
  -- the mixed product `f · m`
  have hfmul : Integrable (fun x => f x * m x) (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (f x) ^ 2 + (m x) ^ 2)
      (hf2.add hm2) (hfm.mul hmm) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, ← sq_abs (f x), ← sq_abs (m x)]
    nlinarith [sq_nonneg (|f x| - |m x|)]
  -- the square `(m - c)²`
  have hmc2 : Integrable (fun x => (m x - c) ^ 2)
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (m x) ^ 2 * 2 + 2 * c ^ 2)
      ((hm2.mul_const 2).add (integrable_const (2 * c ^ 2)))
      ((hmm.sub MeasureTheory.aestronglyMeasurable_const).pow 2) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (m x + c)]
  -- the products occurring in the cross term
  have hfgc : Integrable (fun x => f x * (m x - c))
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (f x) ^ 2 + (m x - c) ^ 2)
      (hf2.add hmc2) (hfm.mul (hmm.sub MeasureTheory.aestronglyMeasurable_const)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, ← sq_abs (f x), ← sq_abs (m x - c)]
    nlinarith [sq_nonneg (|f x| - |m x - c|)]
  have hmmc : Integrable (fun x => m x * (m x - c))
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (m x) ^ 2 + (m x - c) ^ 2)
      (hm2.add hmc2) (hmm.mul (hmm.sub MeasureTheory.aestronglyMeasurable_const)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, ← sq_abs (m x), ← sq_abs (m x - c)]
    nlinarith [sq_nonneg (|m x| - |m x - c|)]
  -- the square `(f - m)²`
  have hmusub2 : Integrable (fun x => (f x - m x) ^ 2)
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => 2 * ((f x) ^ 2 + (m x) ^ 2))
      ((hf2.add hm2).const_mul 2) ((hfm.sub hmm).pow 2) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f x + m x)]
  -- the doubled cross term
  have hprod : Integrable (fun x => 2 * ((f x - m x) * (m x - c)))
      (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    refine Integrable.mono' (g := fun x => (f x - m x) ^ 2 + (m x - c) ^ 2)
      (hmusub2.add hmc2)
      (((hfm.sub hmm).mul (hmm.sub MeasureTheory.aestronglyMeasurable_const)).const_mul 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        ← sq_abs (f x - m x), ← sq_abs (m x - c)]
    nlinarith [sq_nonneg (|f x - m x| - |m x - c|)]
  -- the coordinate mean is independent of coordinate `j`
  have hmin : ∀ x z, m (Function.update x j z) = m x := by
    intro x z
    show (1 / (ν Set.univ).toReal) * ∫ z', f (Function.update (Function.update x j z) j z') ∂ν
       = (1 / (ν Set.univ).toReal) * ∫ z', f (Function.update x j z') ∂ν
    congr 1
    apply integral_congr_ae
    filter_upwards with z'
    rw [Function.update_idem]
  have hw : ∀ x z, (fun x => m x - c) (Function.update x j z) = (fun x => m x - c) x := by
    intro x z
    simp only
    rw [hmin x z]
  -- the tower identity: `∫ f (m-c) = ∫ m (m-c)`
  have hA : ∫ x, f x * (m x - c) ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, m x * (m x - c) ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    Work.BoseFixB1S.pi_tower_right (u := f) (w := fun x => m x - c) ν hν j hw hfgc
  -- the cross term vanishes
  have hc : ∫ x, (f x - m x) * (m x - c) ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) = 0 := by
    have hsplit : (fun x => (f x - m x) * (m x - c))
        = fun x => f x * (m x - c) - m x * (m x - c) := by
      funext x; ring
    rw [hsplit, integral_sub hfgc hmmc, hA, sub_self]
  -- pointwise Pythagorean expansion
  have hpt : ∀ x, (f x - c) ^ 2
      = (f x - m x) ^ 2 + (m x - c) ^ 2 + 2 * ((f x - m x) * (m x - c)) := by
    intro x; ring
  calc ∫ x, (f x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, ((f x - m x) ^ 2 + (m x - c) ^ 2 + 2 * ((f x - m x) * (m x - c)))
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpt x
    _ = ∫ x, ((f x - m x) ^ 2 + (m x - c) ^ 2) ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
        + ∫ x, 2 * ((f x - m x) * (m x - c)) ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) :=
        integral_add (hmusub2.add hmc2) hprod
    _ = (∫ x, (f x - m x) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
          + ∫ x, (m x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)))
        + 2 * ∫ x, (f x - m x) * (m x - c) ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [integral_add hmusub2 hmc2, integral_const_mul]
    _ = ∫ x, (f x - m x) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
        + ∫ x, (m x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [hc]; ring

end Work.BoseFixB1S.PiAnova
