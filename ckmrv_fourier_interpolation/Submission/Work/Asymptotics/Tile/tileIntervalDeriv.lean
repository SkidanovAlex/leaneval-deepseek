/-
# Differentiation under the integral sign on an arbitrary interval

`Submission/Work/Asymptotics/layerLow_seminorm.lean` proves
`Work.Asymptotics.iteratedDeriv_intervalIntegral_of_meas_bound` for the fixed interval `(0,1]`.
The cusp-`±1` tile analysis of `layerLow` needs the same statement on the two sub-intervals
`(0, Im w / 2]` and `[Im w / 2, 1]`, so this file reproduces the proof (verbatim, with `0`,`1`
replaced by `a`,`b`) for a general interval `a..b`.

## Main results

* `Work.Asymptotics.hasDerivAt_intervalIntegral_iteratedDeriv_meas_interval`;
* `Work.Asymptotics.iteratedDeriv_intervalIntegral_of_meas_bound_interval`.
-/
import Mathlib
import Submission.Work.Asymptotics.layerLow_seminorm

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

/-- Differentiation under the integral sign on `a..b` for the family
`r ↦ iteratedDeriv j (fun r' => k r' u) r`, with an integrable `u`-dependent dominator. -/
lemma hasDerivAt_intervalIntegral_iteratedDeriv_meas_interval {k : ℝ → ℝ → ℂ} {j : ℕ}
    {a b : ℝ} (hab : a ≤ b)
    (hk_meas : ∀ j : ℕ, ∀ r : ℝ, Measurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r))
    (hk_smooth : ∀ u, ContDiff ℝ ∞ (fun r : ℝ => k r u))
    (hint : ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc a b) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)),
        ∀ r : ℝ, ‖iteratedDeriv j (fun r' : ℝ => k r' u) r‖ ≤ bd u)
    (hint_succ : ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc a b) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)),
        ∀ r : ℝ, ‖iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r‖ ≤ bd u)
    (r : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ u in a..b, iteratedDeriv j (fun r' : ℝ => k r' u) x)
      (∫ u in a..b, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r) r := by
  obtain ⟨bdj, hbdj_int, hbdj⟩ := hint
  obtain ⟨bd, hbd_int, hbd⟩ := hint_succ
  have hIoc : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  have hbdj_int' : Integrable bdj (volume.restrict (Set.uIoc a b)) := by
    rw [← hIoc] at hbdj_int; exact hbdj_int
  have hbd_int' : Integrable bd (volume.restrict (Set.uIoc a b)) := by
    rw [← hIoc] at hbd_int; exact hbd_int
  have hF_meas : ∀ᶠ x in 𝓝 r,
      AEStronglyMeasurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) x)
        (volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall (fun x => (hk_meas j x).aestronglyMeasurable)
  have hF_int : Integrable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r)
      (volume.restrict (Set.uIoc a b)) := by
    refine hbdj_int'.mono' (hk_meas j r).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine ((ae_restrict_iff' measurableSet_Ioc).mp hbdj).mono ?_
    intro u hu H
    exact hu (hIoc ▸ H) r
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)
      (volume.restrict (Set.uIoc a b)) :=
    (hk_meas (j + 1) r).aestronglyMeasurable
  have h_bound : ∀ᵐ c ∂(volume.restrict (Set.uIoc a b)),
      ∀ x ∈ (Set.univ : Set ℝ), ‖iteratedDeriv (j + 1) (fun r' : ℝ => k r' c) x‖ ≤ bd c := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine ((ae_restrict_iff' measurableSet_Ioc).mp hbd).mono ?_
    intro u hu H
    exact fun x _ => hu (hIoc ▸ H) x
  have h_diff : ∀ᵐ c ∂(volume.restrict (Set.uIoc a b)),
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' c) x)
          (iteratedDeriv (j + 1) (fun r' : ℝ => k r' c) x) x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun c _ x _ => ?_)
    have hd : Differentiable ℝ (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' c) x) :=
      (contDiff_iteratedDeriv_fst_meas (k := k) hk_smooth j c).differentiable (by decide)
    have hd_at : DifferentiableAt ℝ (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' c) x) x :=
      hd.differentiableAt
    have h' : HasDerivAt (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' c) x)
        (deriv (iteratedDeriv j (fun r' : ℝ => k r' c)) x) x := hd_at.hasDerivAt
    exact h'.congr_deriv (congrFun (iteratedDeriv_succ (n := j)
      (f := fun r' : ℝ => k r' c)) x).symm
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.uIoc a b))
    (F := fun x u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) x)
    (F' := fun x u : ℝ => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) x)
    (x₀ := r) (s := Set.univ) (bound := bd)
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound hbd_int' h_diff
  have hconv : ∀ f : ℝ → ℂ,
      (∫ u : ℝ, f u ∂(volume.restrict (Set.uIoc a b))) = ∫ u in a..b, f u := by
    intro f
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hab]
    simp
  have hfun : (fun x : ℝ => ∫ u in a..b, iteratedDeriv j (fun r' : ℝ => k r' u) x)
      = fun x : ℝ => ∫ u : ℝ, iteratedDeriv j (fun r' : ℝ => k r' u) x
          ∂(volume.restrict (Set.uIoc a b)) :=
    funext (fun x => (hconv (fun u => iteratedDeriv j (fun r' : ℝ => k r' u) x)).symm)
  have hval : (∫ u in a..b, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)
      = ∫ u : ℝ, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r
          ∂(volume.restrict (Set.uIoc a b)) :=
    (hconv (fun u => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)).symm
  rw [hfun, hval]
  exact hmain.2

/-- **Iterated differentiation under the integral sign on `a..b`.** -/
theorem iteratedDeriv_intervalIntegral_of_meas_bound_interval (k : ℝ → ℝ → ℂ) (l : ℕ)
    {a b : ℝ} (hab : a ≤ b)
    (hk_meas : ∀ r : ℝ, Measurable (fun u : ℝ => k r u))
    (hk_smooth : ∀ u, ContDiff ℝ ∞ (fun r : ℝ => k r u))
    (hbd : ∀ j ≤ l, ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc a b) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)),
        ∀ r : ℝ, ‖iteratedDeriv j (fun r' : ℝ => k r' u) r‖ ≤ bd u) :
    ∀ j ≤ l, iteratedDeriv j (fun r : ℝ => ∫ u in a..b, k r u)
      = fun r : ℝ => ∫ u in a..b, iteratedDeriv j (fun r' : ℝ => k r' u) r := by
  have hmeas := measurable_iteratedDeriv_fst_meas hk_meas hk_smooth
  have hkey : ∀ j, j ≤ l → iteratedDeriv j (fun r : ℝ => ∫ u in a..b, k r u)
      = fun r : ℝ => ∫ u in a..b, iteratedDeriv j (fun r' : ℝ => k r' u) r := by
    intro j
    induction j with
    | zero =>
      intro _
      funext r
      simp [iteratedDeriv_zero]
    | succ j ih =>
      intro hj
      rw [iteratedDeriv_succ, ih (by omega)]
      funext r
      exact (hasDerivAt_intervalIntegral_iteratedDeriv_meas_interval (j := j) hab hmeas hk_smooth
        (hbd j (by omega)) (hbd (j + 1) hj) r).deriv
  exact hkey

end Work.Asymptotics
