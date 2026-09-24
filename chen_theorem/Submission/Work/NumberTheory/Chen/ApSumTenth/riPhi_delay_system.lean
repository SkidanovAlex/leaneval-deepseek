/-
# `ApSumTenth.riPhi_delay_system` — the summed delay system of the delay profiles

The target is the *summed* (i.e. infinite-level) delay system of the Rosser–Iwaniec profile
pair `(riPhi, riPsi)`:

* `s * riPhi s = (3 − s) + ∫_{Ici 2} riPsi`   for `1 ≤ s ≤ 3`,
* `s * riPsi s = ∫_{Ici (s−1)} riPhi`         for `2 ≤ s`,

where `riPhi s = Σ_j profC (2j) s` and `riPsi s = Σ_j profC (2j+1) s`
(`APSwitchUpper.prof`), the delay family of the linear sieve.

## Route

Both identities come from the *finite level* identities

* `evenSum_formula  : evenSum (n+1) s = ((3−s) + Cv n)/s`  for `1 ≤ s ≤ 3`,
* `profC_odd_mul    : s * profC (2i+1) s = profTail (2i) (s−1)`  for `2 ≤ s`,

by passing to the limit `n → ∞`, together with the exchange of the sum over the level with the
integral over the half line.  The exchange is an instance of the series dominated convergence
theorem `hasSum_integral_of_summable_integral_norm`; the two summability inputs are

* `summable_P` (`APSwitchUpper.riPhi_le_env`): `Σ_i ∫_{Ici 2} profC (2i+1) = Ctot < ∞`,
* `riSys_summable_odd`: `Σ_i profC (2i+1) s < ∞` for `s ≥ 2`, which follows from the crude
  majorant `crudeV` of `APSwitchUpper.riPhiSharpCrude` (`level_apart_bpart_crude`).

The geometric input `∫_{Ici a} profC m = ∫_a^{m+3} profC m` (the profile is supported in
`(-∞, m+3]`) reduces the half-line integrals to the interval integrals of `profTail`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_summed_delay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_partial_system
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_le_env

open Finset MeasureTheory Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.ApSumTenth

noncomputable section

attribute [local instance] Classical.propDecidable

open Work.NumberTheory.Chen.APSwitchUpper

/-! ## §1  Integrability of a delay profile and the half-line/interval identity -/

/-- Every delay profile is integrable on every half line `Ici a`: it is supported in
`(-∞, m+3]` and interval integrable. -/
theorem riSys_integrableOn_profC_Ici (m : ℕ) (a : ℝ) :
    IntegrableOn (profC m) (Set.Ici a) volume := by
  rcases le_or_gt a ((m : ℝ) + 3) with ha | ha
  · have hin : IntegrableOn (profC m) (Set.Icc a ((m : ℝ) + 3)) volume := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (profC_intervalIntegrable m a _).1
    have hind : Integrable (Set.indicator (Set.Icc a ((m : ℝ) + 3)) (profC m)) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr hin
    have hind' : IntegrableOn (Set.indicator (Set.Icc a ((m : ℝ) + 3)) (profC m))
        (Set.Ici a) volume := hind.mono_measure Measure.restrict_le_self
    refine hind'.congr_fun ?_ measurableSet_Ici
    intro u hu
    by_cases hux : u ≤ (m : ℝ) + 3
    · rw [Set.indicator_of_mem (show u ∈ Set.Icc a ((m : ℝ) + 3) from ⟨hu, hux⟩)]
    · rw [Set.indicator_of_notMem (fun h => hux h.2),
        profC_support m u (le_of_lt (lt_of_not_ge hux))]
  · have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ici a) volume := integrableOn_zero
    refine h0.congr_fun ?_ measurableSet_Ici
    intro u hu
    exact (profC_support m u (le_trans ha.le hu)).symm

/-- The half-line integral of a delay profile is its interval integral up to the support edge
`m+3`: beyond it the integrand vanishes. -/
theorem riSys_integral_Ici_profC (m : ℕ) (a : ℝ) :
    (∫ u in Set.Ici a, profC m u) = ∫ u in a..((m : ℝ) + 3), profC m u := by
  rcases le_or_gt a ((m : ℝ) + 3) with ha | ha
  · have h1 := riSys_integrableOn_profC_Ici m a
    have h2 := riSys_integrableOn_profC_Ici m ((m : ℝ) + 3)
    have h := intervalIntegral.integral_Ici_sub_Ici' h1 h2
    have hz : (∫ u in Set.Ici ((m : ℝ) + 3), profC m u) = 0 := by
      refine (setIntegral_congr_fun measurableSet_Ici (fun u hu => profC_support m u hu)).trans ?_
      simp
    linarith [h, hz]
  · have hz1 : (∫ u in Set.Ici a, profC m u) = 0 := by
      refine (setIntegral_congr_fun measurableSet_Ici
        (fun u hu => profC_support m u (le_trans ha.le hu))).trans ?_
      simp
    have hz2 : (∫ u in a..((m : ℝ) + 3), profC m u) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℝ)) ?_,
        intervalIntegral.integral_zero]
      intro u hu
      rw [Set.uIcc_of_ge ha.le, Set.mem_Icc] at hu
      exact profC_support m u hu.1
    rw [hz1, hz2]

/-! ## §2  The odd partial sums against the crude majorant -/

/-- `Σ_{i<n} profC (2i+1) s = bpart (2n+1) s`: the odd partial sums are the odd part sums. -/
theorem riSys_sum_range_profC_two_mul_add_one (n : ℕ) (s : ℝ) :
    (∑ i ∈ Finset.range n, profC (2 * i + 1) s) = bpart (2 * n + 1) s := by
  unfold bpart
  have hsub : (Finset.range (2 * n + 1)).filter (fun j => j % 2 = 1)
      = (Finset.range n).image (fun k => 2 * k + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hje⟩
      refine ⟨j / 2, by omega, ?_⟩
      have h := Nat.div_add_mod j 2
      omega
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [hsub, Finset.sum_image]
  intro a _ b _ hab
  have h : 2 * a + 1 = 2 * b + 1 := hab
  omega

/-- `oddSum n s = bpart (2n+3) s`. -/
theorem riSys_oddSum_eq_bpart (n : ℕ) (s : ℝ) : oddSum n s = bpart (2 * n + 3) s := by
  show (∑ i ∈ Finset.range (n + 1), profC (2 * i + 1) s) = bpart (2 * n + 3) s
  have h2 : (2 * (n + 1) + 1 : ℕ) = 2 * n + 3 := by omega
  rw [← h2]
  exact riSys_sum_range_profC_two_mul_add_one (n + 1) s

/-- The odd level sums are dominated by the crude majorant `crudeV = 6 exp (2 − s)`. -/
theorem riSys_oddSum_le_crudeV (n : ℕ) (s : ℝ) (hs : 2 ≤ s) : oddSum n s ≤ crudeV s := by
  rw [riSys_oddSum_eq_bpart]
  exact level_apart_bpart_crude.2 (2 * n + 3) s hs

/-- **Summability of the odd profile series.**  For `s ≥ 2` the series `Σ_i profC (2i+1) s`
converges; the partial sums are bounded by `crudeV s`. -/
theorem riSys_summable_odd (s : ℝ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => profC (2 * i + 1) s) := by
  refine summable_of_sum_range_le (c := crudeV s) (fun i => profC_nonneg (2 * i + 1) s) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simpa using crudeV_nonneg s
  · rw [riSys_sum_range_profC_two_mul_add_one n s]
    exact level_apart_bpart_crude.2 (2 * n + 1) s hs

/-! ## §3  The limit of the even level sums: `s riPhi s = (3 − s) + Ctot` on `[1,3]` -/

/-- On `1 ≤ s ≤ 3` the even levels satisfy `s · evenSum (n+1) s = (3 − s) + Cv n`; passing to
the limit gives `s · riPhi s = (3 − s) + Ctot`, with `Ctot = Σ_i ∫_{Ici 2} profC (2i+1)`. -/
theorem riSys_evenSum_limit (s : ℝ) (h1 : 1 ≤ s) (h3 : s ≤ 3) :
    s * riPhi s = (3 - s) + Ctot := by
  have hEq : ∀ n : ℕ, s * evenSum (n + 1) s = (3 - s) + Cv n := by
    intro n
    rw [evenSum_formula n h1 h3, mul_div_cancel₀ _ (by linarith : s ≠ 0)]
  have hshift : Tendsto (fun n : ℕ => s * evenSum (n + 1) s) atTop (𝓝 ((3 - s) + Ctot)) := by
    simp only [hEq]
    exact tendsto_const_nhds.add tendsto_Cv
  have hleft : Tendsto (fun n : ℕ => s * evenSum (n + 1) s) atTop (𝓝 (s * riPhi s)) :=
    ((tendsto_evenSum s h1).comp (tendsto_add_atTop_nat 1)).const_mul s
  exact tendsto_nhds_unique hleft hshift

/-! ## §4  The two half-line integrals as series of level integrals -/

/-- **`∫_{Ici 2} riPsi = Ctot`.**  The series dominated convergence theorem applied to the
odd profiles over `[2,∞)`; the level integrals are the `P i`. -/
theorem riSys_integral_Ici_two_riPsi :
    (∫ u in Set.Ici (2 : ℝ), riPsi u) = Ctot := by
  have hInt : ∀ i : ℕ, Integrable (fun u : ℝ => profC (2 * i + 1) u)
      (volume.restrict (Set.Ici (2 : ℝ))) :=
    fun i => riSys_integrableOn_profC_Ici (2 * i + 1) 2
  have hP : ∀ i : ℕ, (∫ u in Set.Ici (2 : ℝ), profC (2 * i + 1) u) = P i := by
    intro i
    rw [riSys_integral_Ici_profC, P]
    have hc : (((2 * i + 1 : ℕ) : ℝ) + 3) = ((2 * i + 4 : ℕ) : ℝ) := by push_cast; ring
    rw [hc]
  have hnorm : (fun i : ℕ => ∫ u in Set.Ici (2 : ℝ), ‖profC (2 * i + 1) u‖)
      = fun i : ℕ => ∫ u in Set.Ici (2 : ℝ), profC (2 * i + 1) u := by
    funext i
    refine integral_congr_ae (Eventually.of_forall ?_)
    intro u
    exact Real.norm_of_nonneg (profC_nonneg (2 * i + 1) u)
  have hsumm : Summable (fun i : ℕ => ∫ u in Set.Ici (2 : ℝ), ‖profC (2 * i + 1) u‖) := by
    rw [hnorm]
    rw [show (fun i : ℕ => ∫ u in Set.Ici (2 : ℝ), profC (2 * i + 1) u) = P from funext hP]
    exact summable_P
  have hmain := hasSum_integral_of_summable_integral_norm
    (F := fun i : ℕ => fun u : ℝ => profC (2 * i + 1) u)
    (μ := volume.restrict (Set.Ici (2 : ℝ))) hInt hsumm
  refine HasSum.unique (hmain.congr_fun (fun i => (hP i).symm)) hasSum_P

/-- **`s riPsi s = ∫_{Ici (s−1)} riPhi` for `s ≥ 2`.**  The series dominated convergence
theorem applied to the even profiles over `[s−1,∞)`: by the odd recursion the level integrals
are exactly `s · profC (2i+1) s`, whose sum is `s · riPsi s`. -/
theorem riSys_mul_riPsi_eq_integral (s : ℝ) (hs : 2 ≤ s) :
    s * riPsi s = ∫ u in Set.Ici (s - 1), riPhi u := by
  have hodd : Summable (fun i : ℕ => profC (2 * i + 1) s) := riSys_summable_odd s hs
  have hHasOdd : HasSum (fun i : ℕ => profC (2 * i + 1) s) (riPsi s) := hodd.hasSum
  have hmul : HasSum (fun i : ℕ => s * profC (2 * i + 1) s) (s * riPsi s) :=
    hHasOdd.mul_left s
  have hEq : ∀ i : ℕ, s * profC (2 * i + 1) s = ∫ u in Set.Ici (s - 1), profC (2 * i) u := by
    intro i
    rw [profC_odd_mul i s hs, profTail_eq_integral, riSys_integral_Ici_profC]
  have hHasInt : HasSum (fun i : ℕ => ∫ u in Set.Ici (s - 1), profC (2 * i) u) (s * riPsi s) :=
    hmul.congr_fun (fun i => (hEq i).symm)
  have hInt : ∀ i : ℕ, Integrable (fun u : ℝ => profC (2 * i) u)
      (volume.restrict (Set.Ici (s - 1))) :=
    fun i => riSys_integrableOn_profC_Ici (2 * i) (s - 1)
  have hnorm : (fun i : ℕ => ∫ u in Set.Ici (s - 1), ‖profC (2 * i) u‖)
      = fun i : ℕ => ∫ u in Set.Ici (s - 1), profC (2 * i) u := by
    funext i
    refine integral_congr_ae (Eventually.of_forall ?_)
    intro u
    exact Real.norm_of_nonneg (profC_nonneg (2 * i) u)
  have hsumm : Summable (fun i : ℕ => ∫ u in Set.Ici (s - 1), ‖profC (2 * i) u‖) := by
    rw [hnorm]
    have h2 : (fun i : ℕ => ∫ u in Set.Ici (s - 1), profC (2 * i) u)
        = fun i : ℕ => s * profC (2 * i + 1) s := funext (fun i => (hEq i).symm)
    rw [h2]
    exact hodd.mul_left s
  have hmain := hasSum_integral_of_summable_integral_norm
    (F := fun i : ℕ => fun u : ℝ => profC (2 * i) u)
    (μ := volume.restrict (Set.Ici (s - 1))) hInt hsumm
  exact HasSum.unique hHasInt hmain

/-! ## §5  The target -/

theorem riPhi_delay_system :
    (∀ s : ℝ, 1 ≤ s → s ≤ 3 →
      s * Work.NumberTheory.Chen.APSwitchUpper.riPhi s
        = (3 - s) + ∫ u in Set.Ici (2 : ℝ), Work.NumberTheory.Chen.APSwitchUpper.riPsi u)
    ∧ (∀ s : ℝ, 2 ≤ s →
      s * Work.NumberTheory.Chen.APSwitchUpper.riPsi s
        = ∫ u in Set.Ici (s - 1), Work.NumberTheory.Chen.APSwitchUpper.riPhi u) := by
  constructor
  · intro s h1 h3
    rw [riSys_evenSum_limit s h1 h3, riSys_integral_Ici_two_riPsi]
  · exact riSys_mul_riPsi_eq_integral

end

end Work.NumberTheory.Chen.ApSumTenth
