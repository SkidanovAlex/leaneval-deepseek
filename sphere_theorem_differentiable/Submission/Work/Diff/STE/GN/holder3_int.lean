import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hölder's inequality for three functions on the unit cube

We prove the three-function Hölder inequality on the half-open unit cube `unitCube = (0,1]^ι`
(which has measure `1`), by applying the two-function Hölder inequality twice:

* with exponents `p` and `s := p/(p-1)`, to `f` and the product `g * h`;
* with exponents `q/s` and `r/s`, to `g^s` and `h^s` (whose product is `(g h)^s`),

together with the multiplicativity of `Real.rpow` (`(g^s)^(q/s) = g^q`,
`((g h)^s)^(1/s) = (g h)`, and `((∫g^q)^(s/q) (∫h^r)^(s/r))^(1/s) = (∫g^q)^(1/q) (∫h^r)^(1/r)`).

The measure-theoretic side conditions (`MemLp`) are met because the cube is contained in the
compact cube `Icc 0 1` on which the continuous functions are bounded, and the cube has finite
measure.

## Main result

* `Work.Diff.STE.GN.holder3_int`
-/

noncomputable section

namespace Work.Diff.STE.GN

open MeasureTheory

/-- The half-open unit cube has volume `1`. -/
lemma unitCube_volume {ι : Type*} [Fintype ι] :
    volume (Work.Diff.STE.unitCube (ι := ι)) = 1 := by
  rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
  simp

/-- The unit cube has finite measure, so restricting the Lebesgue measure to it is a finite
measure. -/
lemma unitCube_isFiniteMeasure_restrict {ι : Type*} [Fintype ι] :
    IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
  MeasureTheory.isFiniteMeasure_restrict.mpr (by
    rw [unitCube_volume]; exact ENNReal.one_ne_top)

/-- The half-open unit cube is measurable. -/
lemma unitCube_measurableSet {ι : Type*} [Fintype ι] :
    MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := by
  rw [Work.Diff.STE.unitCube]
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc)

set_option linter.style.haveILetI false in
/-- A continuous real function belongs to every `Lᵗ` on the unit cube: the cube has finite measure
and is contained in the compact cube `Icc 0 1`, on which the function is bounded. -/
lemma memLp_continuous_unitCube {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (hF : Continuous F) (t : ℝ) :
    MemLp F (ENNReal.ofReal t) (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  haveI : IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    unitCube_isFiniteMeasure_restrict
  have hsub : Work.Diff.STE.unitCube (ι := ι) ⊆ Set.Icc (0 : ι → ℝ) 1 := by
    intro x hx
    rw [Work.Diff.STE.unitCube] at hx
    exact ⟨fun i => le_of_lt (hx i trivial).1, fun i => (hx i trivial).2⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).exists_bound_of_continuousOn
      hF.continuousOn
  refine MemLp.of_bound hF.stronglyMeasurable.aestronglyMeasurable C ?_
  rw [MeasureTheory.ae_restrict_iff' unitCube_measurableSet]
  exact Filter.Eventually.of_forall (fun x hx => hC x (hsub hx))

/-- **Hölder's inequality for three functions** on the unit cube: for `p, q, r : ℝ` with
`1 ≤ p, q, r` and `1/p + 1/q + 1/r = 1`, and continuous nonnegative `f, g, h`,
`∫ f g h ≤ (∫ f^p)^(1/p) (∫ g^q)^(1/q) (∫ h^r)^(1/r)`.
Derivable from the two-function Hölder inequality (applied to `f` and `g h`, then to `g` and `h`)
together with the multiplicativity of `rpow`. -/
theorem holder3_int {ι : Type*} [Fintype ι] [DecidableEq ι] (p q r : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : 1 / p + 1 / q + 1 / r = 1)
    (f g h : (ι → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * g x * h x
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), f x ^ p) ^ (1 / p)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q) ^ (1 / q)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (1 / r) := by
  -- ## The exponent algebra
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  -- `1 < p`: if `p = 1` then `1/q + 1/r = 0`, impossible since `q, r ≥ 1`.
  have hp1 : 1 < p := by
    rcases lt_or_eq_of_le hp with hc | hc
    · exact hc
    · exfalso
      rw [← hc, one_div_one] at hpqr
      have h1 : 0 < 1 / q := one_div_pos.mpr hq0
      have h2 : 0 < 1 / r := one_div_pos.mpr hr0
      linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hpm1 : p - 1 ≠ 0 := by linarith
  have hspos : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  have hsne : p / (p - 1) ≠ 0 := ne_of_gt hspos
  -- `p` and `s = p/(p-1)` are conjugate
  have hps : p.HolderConjugate (p / (p - 1)) := by
    refine ⟨?_, hp0, hspos⟩
    rw [inv_one, inv_div]
    field_simp
    ring
  have hsub : (1 : ℝ) - 1 / p = (p - 1) / p := by field_simp
  have hinv : 1 / (p / (p - 1)) = (p - 1) / p := by rw [one_div, inv_div]
  -- hence `1/q + 1/r = 1/s`
  have hqr : 1 / q + 1 / r = 1 / (p / (p - 1)) := by
    rw [hinv]; linarith [hpqr, hsub]
  -- and `q/s`, `r/s` are conjugate (since `s(1/q + 1/r) = 1`)
  have hqr' : (q / (p / (p - 1))).HolderConjugate (r / (p / (p - 1))) := by
    refine ⟨?_, div_pos hq0 hspos, div_pos hr0 hspos⟩
    rw [inv_one, inv_div, inv_div]
    have hmul : p / (p - 1) * (1 / q) + p / (p - 1) * (1 / r) = 1 := by
      rw [← mul_add, hqr, mul_one_div, div_self hsne]
    have hs1 : p / (p - 1) / q = p / (p - 1) * (1 / q) := by rw [mul_one_div]
    have hs2 : p / (p - 1) / r = p / (p - 1) * (1 / r) := by rw [mul_one_div]
    rw [hs1, hs2]
    exact hmul
  -- ## Two-function Hölder, first with exponents `(p, s)`
  have hH1 : ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * (g x * h x)
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), f x ^ p) ^ (1 / p)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), (g x * h x) ^ (p / (p - 1))) ^
            (1 / (p / (p - 1))) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι))) hps
      (Filter.Eventually.of_forall hf0)
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hg0 x) (hh0 x)))
      (memLp_continuous_unitCube hf p) (memLp_continuous_unitCube (hg.mul hh) (p / (p - 1)))
  -- ## Two-function Hölder, then with exponents `(q/s, r/s)` on `g^s`, `h^s`
  have hH2 : ∫ x in Work.Diff.STE.unitCube (ι := ι),
        g x ^ (p / (p - 1)) * h x ^ (p / (p - 1))
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (g x ^ (p / (p - 1))) ^ (q / (p / (p - 1)))) ^ (1 / (q / (p / (p - 1))))
        * (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (h x ^ (p / (p - 1))) ^ (r / (p / (p - 1)))) ^ (1 / (r / (p / (p - 1)))) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι))) hqr'
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hg0 x) (p / (p - 1))))
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hh0 x) (p / (p - 1))))
      (memLp_continuous_unitCube (hg.rpow_const (fun x => Or.inr hspos.le)) (q / (p / (p - 1))))
      (memLp_continuous_unitCube (hh.rpow_const (fun x => Or.inr hspos.le)) (r / (p / (p - 1))))
  -- ## Rewriting the second inequality into `∫ (g h)^s ≤ (∫g^q)^(s/q) (∫h^r)^(s/r)`
  have A1 : ∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ (p / (p - 1)) * h x ^ (p / (p - 1))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), (g x * h x) ^ (p / (p - 1)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (Real.mul_rpow (hg0 x) (hh0 x)).symm
  have hs_q : p / (p - 1) * (q / (p / (p - 1))) = q := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ q hsne]
  have hs_r : p / (p - 1) * (r / (p / (p - 1))) = r := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ r hsne]
  have A2 : ∫ x in Work.Diff.STE.unitCube (ι := ι), (g x ^ (p / (p - 1))) ^ (q / (p / (p - 1)))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (g x ^ (p / (p - 1))) ^ (q / (p / (p - 1))) = g x ^ q
    rw [← Real.rpow_mul (hg0 x) (p / (p - 1)) (q / (p / (p - 1))), hs_q]
  have A3 : ∫ x in Work.Diff.STE.unitCube (ι := ι), (h x ^ (p / (p - 1))) ^ (r / (p / (p - 1)))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (h x ^ (p / (p - 1))) ^ (r / (p / (p - 1))) = h x ^ r
    rw [← Real.rpow_mul (hh0 x) (p / (p - 1)) (r / (p / (p - 1))), hs_r]
  have h1s : 1 / (q / (p / (p - 1))) = p / (p - 1) / q := by rw [one_div, inv_div]
  have h2s : 1 / (r / (p / (p - 1))) = p / (p - 1) / r := by rw [one_div, inv_div]
  have hD_le0 := hH2
  rw [A1, A2, A3, h1s, h2s] at hD_le0
  -- ## Take the `1/s`-th power
  have hDgs : 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), (g x * h x) ^ (p / (p - 1)) :=
    integral_nonneg (fun x => Real.rpow_nonneg (mul_nonneg (hg0 x) (hh0 x)) _)
  have hD_le1 : (∫ x in Work.Diff.STE.unitCube (ι := ι), (g x * h x) ^ (p / (p - 1))) ^
        (1 / (p / (p - 1)))
      ≤ ((∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q) ^ (p / (p - 1) / q)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (p / (p - 1) / r)) ^
          (1 / (p / (p - 1))) :=
    Real.rpow_le_rpow hDgs hD_le0 (div_nonneg zero_le_one hspos.le)
  have hAg : 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q :=
    integral_nonneg (fun x => Real.rpow_nonneg (hg0 x) q)
  have hAh : 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r :=
    integral_nonneg (fun x => Real.rpow_nonneg (hh0 x) r)
  have hsq : p / (p - 1) / q * (1 / (p / (p - 1))) = 1 / q := by field_simp
  have hsr : p / (p - 1) / r * (1 / (p / (p - 1))) = 1 / r := by field_simp
  have hD_rhs : ((∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q) ^ (p / (p - 1) / q)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (p / (p - 1) / r)) ^
          (1 / (p / (p - 1)))
      = (∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q) ^ (1 / q)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (1 / r) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hAg _) (Real.rpow_nonneg hAh _),
        ← Real.rpow_mul hAg, ← Real.rpow_mul hAh, hsq, hsr]
  have hD_le := le_trans hD_le1 hD_rhs.le
  -- ## Combine with the first Hölder inequality
  have hLHS : ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * g x * h x
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * (g x * h x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * g x * h x = f x * (g x * h x)
    ring
  have hAf : 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), f x ^ p :=
    integral_nonneg (fun x => Real.rpow_nonneg (hf0 x) p)
  rw [hLHS]
  calc ∫ x in Work.Diff.STE.unitCube (ι := ι), f x * (g x * h x)
      ≤ (∫ x in Work.Diff.STE.unitCube (ι := ι), f x ^ p) ^ (1 / p)
        * ((∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q) ^ (1 / q)
          * (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (1 / r)) :=
        le_trans hH1 (mul_le_mul_of_nonneg_left hD_le (Real.rpow_nonneg hAf _))
    _ = (∫ x in Work.Diff.STE.unitCube (ι := ι), f x ^ p) ^ (1 / p)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), g x ^ q) ^ (1 / q)
        * (∫ x in Work.Diff.STE.unitCube (ι := ι), h x ^ r) ^ (1 / r) := by
        rw [mul_assoc]

end Work.Diff.STE.GN
