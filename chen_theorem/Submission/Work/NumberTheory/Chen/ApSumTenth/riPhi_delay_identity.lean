/-
# `ApSumTenth.riPhi_delay_identity` — the summed delay recursion of the Rosser–Iwaniec pair

For the delay family `profC j = f_{j+1}` of the linear sieve (`APSwitchUpper/prof.lean`) the two
summed profiles are

* `riPhi s = Σ_j profC (2j)   = F(s) − 1`   (the upper profile), and
* `riPsi s = Σ_j profC (2j+1) = 1 − f(s)`   (the lower profile).

This file proves the **summed delay identity**

`s·riPhi s = (3 − s)·1_{s ≤ 3} + ∫_{max(s−1,2)}^∞ riPsi`   for `s ≥ 1`,

which is the `s`-truncated (`m = 0`) form of the classical delay system: it is
`DelayIdentity` of `ApSumTenth/cube_surplus_sharp.lean`, the input that turns the delay
calculus into the closed-form Rosser–Iwaniec profile `F`.

## Route

`evenSum_succ_mul` (`APSwitchUpper/riPhiLevelCore.lean`) gives the finite-level identity

`s·evenSum (N+1) s = (3 − s)·1_{s ≤ 3} + ∫_{max(s−1,2)}^{2N+4} oddSum N`,

whose right-hand integral equals `∫_{max(s−1,2)}^∞ oddSum N` because `oddSum N` is supported on
`[2, 2N+4]`; the conversion between the interval integral and the integral over `Set.Ioi` is
`integral_Ioi_eq_interval` below.  Writing the set integral of `oddSum N` as the finite sum
`Σ_{i ≤ N} ∫ profC (2i+1)` (linearity), the left-hand side tends to `s·riPhi s`
(`tendsto_evenSum`) while the right-hand side tends to `(3−s)·1_{s≤3} + ∫ riPsi` by
`hasSum_integral_of_summable_integral_norm`, applied to `F i = profC (2i+1)` and the restricted
measure `volume.restrict (Ioi (max (s−1) 2))`; the required summability of the integrals is
`tail_summable`, and `IntegrableOn` of each `profC j` on a half-line is proved directly from
bounded support (`integrableOn_Ioi_of_intervalIntegrable`).  Uniqueness of limits
(`tendsto_nhds_unique`) closes the identity.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_summed_delay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_le_env

namespace Work.NumberTheory.Chen.ApSumTenth

open MeasureTheory Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A function vanishing on a measurable set is integrable there. -/
private lemma integrableOn_of_forall_eq_zero {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ x ∈ s, f x = 0) : IntegrableOn f s volume :=
  IntegrableOn.congr_fun (integrable_zero ℝ ℝ (volume.restrict s)) (fun x hx => (h x hx).symm) hs

/-- A function that is interval integrable on `M..K` and vanishes beyond the right endpoint `K`
is integrable on `Ioi M`. -/
private lemma integrableOn_Ioi_of_intervalIntegrable {f : ℝ → ℝ} {M K : ℝ}
    (hint : IntervalIntegrable f volume M K) (hzero : ∀ x, K ≤ x → f x = 0) :
    IntegrableOn f (Set.Ioi M) volume := by
  rcases le_total K M with hKM | hKM
  · exact integrableOn_of_forall_eq_zero measurableSet_Ioi
      (fun x hx => hzero x (le_trans hKM (le_of_lt (Set.mem_Ioi.mp hx))))
  · have hunion : Set.Ioc M K ∪ Set.Ioi K = Set.Ioi M := Set.Ioc_union_Ioi_eq_Ioi hKM
    have h1 : IntegrableOn f (Set.Ioc M K) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hKM).mp hint
    have h2 : IntegrableOn f (Set.Ioi K) volume :=
      integrableOn_of_forall_eq_zero measurableSet_Ioi
        (fun x hx => hzero x (le_of_lt (Set.mem_Ioi.mp hx)))
    rw [← hunion]
    exact h1.union h2

/-- Every delay profile is integrable on `Ioi M`. -/
private lemma integrableOn_profC_Ioi (j : ℕ) (M : ℝ) :
    IntegrableOn (Work.NumberTheory.Chen.APSwitchUpper.profC j) (Set.Ioi M) volume :=
  integrableOn_Ioi_of_intervalIntegrable
    (Work.NumberTheory.Chen.APSwitchUpper.profC_intervalIntegrable j M ((j : ℝ) + 3))
    (fun x hx => Work.NumberTheory.Chen.APSwitchUpper.profC_support j x hx)

/-- The odd partial sums are integrable on `Ioi M`. -/
private lemma integrableOn_oddSum_Ioi (N : ℕ) (M : ℝ) :
    IntegrableOn (Work.NumberTheory.Chen.APSwitchUpper.oddSum N) (Set.Ioi M) volume :=
  integrableOn_Ioi_of_intervalIntegrable
    (Work.NumberTheory.Chen.APSwitchUpper.oddSum_intervalIntegrable N M (((2 * N + 4 : ℕ)) : ℝ))
    (fun _ hx => Work.NumberTheory.Chen.APSwitchUpper.oddSum_eq_zero_of_le N hx)

/-- **Integral over `Ioi` versus interval integral** for a function vanishing beyond the
support edge `K`: `∫_{Ioi M} f = ∫_M^K f`, provided `f` is integrable on `Ioi M`. -/
private lemma integral_Ioi_eq_interval {f : ℝ → ℝ} {M K : ℝ}
    (hint : IntegrableOn f (Set.Ioi M) volume) (hzero : ∀ x, K ≤ x → f x = 0) :
    (∫ x in Set.Ioi M, f x) = ∫ x in M..K, f x := by
  rcases le_total M K with hMK | hKM
  · have hK : IntegrableOn f (Set.Ioi K) volume := hint.mono_set (Set.Ioi_subset_Ioi hMK)
    have h := intervalIntegral.integral_interval_add_Ioi hint hK
    have hz : (∫ x in Set.Ioi K, f x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hzero x (le_of_lt (Set.mem_Ioi.mp hx)))
    linarith
  · have hz : (∫ x in Set.Ioi M, f x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero
        (fun x hx => hzero x (le_trans hKM (le_of_lt (Set.mem_Ioi.mp hx))))
    rw [hz, intervalIntegral.integral_of_ge hKM]
    have hz2 : (∫ x in Set.Ioc K M, f x) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero
        (fun x hx => hzero x (le_of_lt (Set.mem_Ioc.mp hx).1))
    rw [hz2, neg_zero]

/-- `riPsi` is the `tsum` of the odd delay profiles, as a function. -/
private lemma riPsi_eq_tsum_fun :
    Work.NumberTheory.Chen.APSwitchUpper.riPsi
      = fun u : ℝ => ∑' j : ℕ, Work.NumberTheory.Chen.APSwitchUpper.profC (2 * j + 1) u := rfl

/-! ## The delay identity -/

theorem riPhi_delay_identity :
    ∀ s : ℝ, 1 ≤ s →
      s * Work.NumberTheory.Chen.APSwitchUpper.riPhi s
        = (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
          + ∫ u in Set.Ici (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.riPsi u := by
  intro s hs
  rw [integral_Ici_eq_integral_Ioi]
  have hM2 : (2 : ℝ) ≤ max (s - 1) 2 := le_max_right _ _
  -- integrability of each odd profile on `Ioi M`
  have hint : ∀ i : ℕ,
      IntegrableOn (Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1))
        (Set.Ioi (max (s - 1) 2)) volume :=
    fun i => integrableOn_profC_Ioi (2 * i + 1) _
  -- the series of tail integrals is summable
  have hcv : ∀ i : ℕ,
      (∫ a in Set.Ioi (max (s - 1) 2),
          ‖Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) a‖)
        = ∫ u in (max (s - 1) 2)..(((2 * i + 4 : ℕ)) : ℝ),
            Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) u := by
    intro i
    have hf : (fun a : ℝ => ‖Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) a‖)
        = fun a : ℝ => Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) a := by
      funext a
      exact Real.norm_of_nonneg (Work.NumberTheory.Chen.APSwitchUpper.profC_nonneg (2 * i + 1) a)
    rw [hf]
    exact integral_Ioi_eq_interval (hint i)
      (fun x hx => Work.NumberTheory.Chen.APSwitchUpper.profC_support (2 * i + 1) x
        (by push_cast at hx ⊢; linarith))
  have hsum : Summable (fun i : ℕ =>
      ∫ a in Set.Ioi (max (s - 1) 2),
        ‖Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) a‖) := by
    rw [show (fun i : ℕ => ∫ a in Set.Ioi (max (s - 1) 2),
          ‖Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) a‖)
        = (fun i : ℕ => ∫ u in (max (s - 1) 2)..(((2 * i + 4 : ℕ)) : ℝ),
            Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) u)
        from funext (fun i => hcv i)]
    exact Work.NumberTheory.Chen.APSwitchUpper.tail_summable hM2
  have hHas := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioi (max (s - 1) 2)))
    (F := fun i u => Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) u) hint hsum
  have hHas' : HasSum (fun i : ℕ => ∫ a in Set.Ioi (max (s - 1) 2),
        Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) a)
      (∫ u in Set.Ioi (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.riPsi u) := by
    simpa only [riPsi_eq_tsum_fun] using hHas
  -- the finite-level identity, in set-integral form
  have hfin : ∀ N : ℕ, s * Work.NumberTheory.Chen.APSwitchUpper.evenSum (N + 1) s
      = (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in Set.Ioi (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.oddSum N u := by
    intro N
    have hconv : (∫ u in (max (s - 1) 2)..(((2 * N + 4 : ℕ)) : ℝ),
          Work.NumberTheory.Chen.APSwitchUpper.oddSum N u)
        = ∫ u in Set.Ioi (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.oddSum N u :=
      (integral_Ioi_eq_interval (integrableOn_oddSum_Ioi N _)
        (fun _ hx => Work.NumberTheory.Chen.APSwitchUpper.oddSum_eq_zero_of_le N hx)).symm
    rw [Work.NumberTheory.Chen.APSwitchUpper.evenSum_succ_mul N hs, hconv]
    by_cases h3 : s ≤ 3 <;> simp [h3]
  -- linearity of the set integral over the odd partial sums
  have hoddint : ∀ N : ℕ, (∫ u in Set.Ioi (max (s - 1) 2),
        Work.NumberTheory.Chen.APSwitchUpper.oddSum N u)
      = ∑ i ∈ Finset.range (N + 1),
          ∫ u in Set.Ioi (max (s - 1) 2),
            Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) u := by
    intro N
    rw [Work.NumberTheory.Chen.APSwitchUpper.oddSum_eq_sum N]
    exact integral_finsetSum (Finset.range (N + 1)) (fun i _ => hint i)
  -- the two limits
  have hleft : Tendsto (fun N : ℕ => s * Work.NumberTheory.Chen.APSwitchUpper.evenSum (N + 1) s)
      atTop (𝓝 (s * Work.NumberTheory.Chen.APSwitchUpper.riPhi s)) :=
    ((Work.NumberTheory.Chen.APSwitchUpper.tendsto_evenSum s hs).comp
      (tendsto_add_atTop_nat 1)).const_mul s
  have hright : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1),
        ∫ u in Set.Ioi (max (s - 1) 2),
          Work.NumberTheory.Chen.APSwitchUpper.profC (2 * i + 1) u)
      atTop (𝓝 (∫ u in Set.Ioi (max (s - 1) 2),
        Work.NumberTheory.Chen.APSwitchUpper.riPsi u)) :=
    (hHas'.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr'
      (Eventually.of_forall (fun N => rfl))
  have hleft' : Tendsto (fun N : ℕ => (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in Set.Ioi (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.oddSum N u)
      atTop (𝓝 (s * Work.NumberTheory.Chen.APSwitchUpper.riPhi s)) :=
    hleft.congr' (Eventually.of_forall (fun N => hfin N))
  have hright' : Tendsto (fun N : ℕ => (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in Set.Ioi (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.oddSum N u)
      atTop (𝓝 ((3 - s) * (if s ≤ 3 then (1 : ℝ) else 0)
        + ∫ u in Set.Ioi (max (s - 1) 2), Work.NumberTheory.Chen.APSwitchUpper.riPsi u)) := by
    have h2 : Tendsto (fun N : ℕ => ∫ u in Set.Ioi (max (s - 1) 2),
          Work.NumberTheory.Chen.APSwitchUpper.oddSum N u)
        atTop (𝓝 (∫ u in Set.Ioi (max (s - 1) 2),
          Work.NumberTheory.Chen.APSwitchUpper.riPsi u)) :=
      hright.congr' (Eventually.of_forall (fun N => (hoddint N).symm))
    exact (tendsto_const_nhds (x := (3 - s) * (if s ≤ 3 then (1 : ℝ) else 0))).add h2
  exact tendsto_nhds_unique hleft' hright'

end

end Work.NumberTheory.Chen.ApSumTenth
