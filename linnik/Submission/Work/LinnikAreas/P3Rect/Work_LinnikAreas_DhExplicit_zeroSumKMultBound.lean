import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Defs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Commons.Analysis.Dyadic.invSq_le_dyadic_layer
import Submission.Work.LinnikAreas.DhExplicit.dyadicBallSumLe
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiUnitWindowCount
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiWindowCount

/-!
# The multiplicity-weighted inverse-square zero sum of `ζ_K = ζ · L(·,χ)`

`Work.LinnikAreas.DhK.kMult χ u = ord_u(Ξ) + ord_u(Λ(·,χ))` is the multiplicity of `u` as a
non-trivial zero of the Dedekind zeta function of the quadratic field attached to `χ`
(`Ξ` = completion of `ζ`, `Λ(·,χ)` = completed `L`-function).  The target estimate

`∑_u kMult χ u / ‖w - u‖² ≤ C (log q + log (2 + ‖w‖) + 2)`   (`Re w ≥ 3/2`)

is obtained from two *centered* zero counts, in Finset form:

* for the `L`-half, the uniform-in-`(N,χ)` count
  `Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5` (a clash-free re-derivation of the
  Bombieri–Vinogradov uniform zero count), whose constant is absolute;
* for the `ζ`-half, the centered ball count `XiBallCountCentered` (sibling module
  `Submission.Work.LinnikAreas.DhExplicit.XiBallCountCentered`).

The two counts are combined by the dyadic decomposition
`1/(1+d²) ≤ ∑_{k ≤ K} [d ≤ 2^k]·4/4^k` (`Commons.Analysis.Dyadic.invSq_le_dyadic_layer`) and the
elementary summation estimate `dyadicBallSumLe`
(sibling module `Submission.Work.LinnikAreas.DhExplicit.dyadicBallSumLe`).

Finally `1/‖w-u‖² ≤ 5/(1+‖w-u‖²)` for every zero `u` (zeros of either factor lie in the closed
critical strip `Re ≤ 1`, while `Re w ≥ 3/2`), and `Summable` + `tsum` bounds follow from the
finite-sum bounds via `summable_of_sum_le` and `Real.tsum_le_of_sum_le`.
-/

open scoped Classical BigOperators

namespace Work.LinnikAreas.DhExplicit

open DirichletCharacter

/-- **Uniform centered ball count of the completed `L`-function**, Finset form: for `ρ ≥ 1` the
total vanishing order of `Λ(·,χ)` over a finite set inside `closedBall a ρ` is at most
`c (ρ+1)(log (‖a‖+ρ+2) + log q + 2)` with an absolute constant `c`.

Immediate from `Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5`: on the ball the (nonnegative)
divisor coefficients of the entire function `completedLFunction χ` equal the vanishing orders, so
the Finset sum is dominated by the divisor `finsum`. -/
theorem completedLBallCountFinset :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) (a : ℂ) (ρ : ℝ), 1 ≤ ρ → ∀ S : Finset ℂ,
      (∀ u ∈ S, ‖a - u‖ ≤ ρ) →
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
        ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (q : ℝ) + 2) := by
  obtain ⟨c, hc, hball⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  refine ⟨c, hc, ?_⟩
  intro q _inst χ hχ hprim a ρ hρ S hS
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛ
  set U : Set ℂ := Metric.closedBall a ρ with hU
  have hAn : AnalyticOnNhd ℂ Λ U :=
    Commons.NumberTheory.Linnik.completedLFunction_analyticOnNhd χ hχ U
  set D : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ U) u : ℤ) : ℝ) with hD
  have hDnn : ∀ u : ℂ, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ U
    · exact Commons.NumberTheory.Linnik.divisor_real_nonneg_of_analyticOnNhd hAn hu
    · have h0 : MeromorphicOn.divisor Λ U u = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        exact fun h => hu h.2
      simp [hD, h0]
  have hDfin : Function.HasFiniteSupport D := by
    have h := Commons.NumberTheory.Linnik.divisor_real_finiteSupport χ hχ a ρ
    simpa only [hD, hU, hΛ] using h
  have hval : ∀ u ∈ U, D u = (analyticOrderNatAt Λ u : ℝ) := by
    intro u hu
    have h := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hAn hu
    simp only [hD, h]
    push_cast
    ring
  have hSU : ∀ u ∈ S, u ∈ U := by
    intro u hu
    rw [hU, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact hS u hu
  have hle_finsum : ∑ u ∈ S, D u ≤ ∑ᶠ u : ℂ, D u := by
    have h1 : ∑ u ∈ S, D u ≤ ∑ u ∈ S ∪ hDfin.toFinset, D u :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun i _ _ => hDnn i)
    have h2 : ∑ u ∈ hDfin.toFinset, D u = ∑ u ∈ S ∪ hDfin.toFinset, D u :=
      Finset.sum_subset Finset.subset_union_right (fun u _ hu => by
        by_contra hne
        exact hu ((hDfin.mem_toFinset).mpr hne))
    calc ∑ u ∈ S, D u ≤ ∑ u ∈ hDfin.toFinset, D u := h1.trans (le_of_eq h2.symm)
      _ = ∑ᶠ u : ℂ, D u :=
          (finsum_eq_sum_of_support_subset D
            (fun u hu => (hDfin.mem_toFinset).mpr hu)).symm
  calc ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ)
      = ∑ u ∈ S, D u :=
        Finset.sum_congr rfl (fun u hu => (hval u (hSU u hu)).symm)
    _ ≤ ∑ᶠ u : ℂ, D u := hle_finsum
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by rw [hD, hΛ, hU]
    _ ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (q : ℝ) + 2) :=
        hball χ hχ hprim a ρ hρ

/-- **Pointwise comparison of the inverse-square kernel with its bounded variant.**  For a
non-trivial zero `u` of `Ξ` or of `Λ(·,χ)` one has `Re u ≤ 1`, and `Re w ≥ 3/2`, so
`‖w - u‖ ≥ 1/2` and `1/‖w-u‖² ≤ 5/(1 + ‖w-u‖²)`. -/
private lemma kMult_div_norm_sq_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re) (u : ℂ) :
    ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2
      ≤ 5 * (((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))) := by
  by_cases h : Work.LinnikAreas.DhK.kMult χ u = 0
  · rw [h]; simp
  · have hkm : Work.LinnikAreas.DhK.kMult χ u
        = analyticOrderNatAt Work.LinnikAreas.DhK.Xi u
          + analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u := rfl
    have hpos : 0 < ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    have hre : u.re ≤ 1 := by
      rcases Nat.eq_zero_or_pos (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u) with h0 | h0
      · have hL : 0 < analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u := by
          omega
        have hz : DirichletCharacter.completedLFunction χ u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero (ne_of_gt hL)
        exact le_of_lt (Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hprim hz).2
      · have hz : Work.LinnikAreas.DhK.Xi u = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero (ne_of_gt h0)
        exact Work.LinnikAreas.DhK.Xi_zero_re_le_one hz
    have hdist : (1 / 2 : ℝ) ≤ ‖w - u‖ := by
      have h1 : |w.re - u.re| ≤ ‖w - u‖ := by
        simpa using Complex.abs_re_le_norm (w - u)
      have h2 : |w.re - u.re| = w.re - u.re := abs_of_nonneg (by linarith)
      linarith
    have h4 : (1 : ℝ) ≤ 4 * ‖w - u‖ ^ 2 := by nlinarith [hdist, sq_nonneg ‖w - u‖]
    have hk : (1 : ℝ) / ‖w - u‖ ^ 2 ≤ 5 * (1 / (1 + ‖w - u‖ ^ 2)) := by
      rw [show (5 : ℝ) * (1 / (1 + ‖w - u‖ ^ 2)) = 5 / (1 + ‖w - u‖ ^ 2) by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h4]
    rw [div_eq_mul_one_div]
    calc ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) * (1 / ‖w - u‖ ^ 2)
        ≤ ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) * (5 * (1 / (1 + ‖w - u‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hk (le_of_lt hpos)
      _ = 5 * (((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) * (1 / (1 + ‖w - u‖ ^ 2))) := by
          ring

/-- **Window count implies centered ball count** for the zeros of `Ξ`: a point of
`closedBall a ρ` has `|Im u - Im a| ≤ ρ`, so a window count at height `Im a` controls the ball. -/
theorem xiBallCount_of_window
    (hwin : ∃ C : ℝ, 0 < C ∧ ∀ (t h : ℝ), 1 ≤ h → ∀ S : Finset ℂ, (∀ u ∈ S, |u.im - t| ≤ h) →
      ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
        ≤ C * (h + 1) * (Real.log (2 + |t| + h) + 2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      ∀ S : Finset ℂ, (∀ u ∈ S, ‖a - u‖ ≤ ρ) →
        ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
          ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + 2) := by
  obtain ⟨C, hCpos, hC⟩ := hwin
  refine ⟨C, hCpos, ?_⟩
  intro a ρ hρ S hS
  have him : ∀ u ∈ S, |u.im - a.im| ≤ ρ := by
    intro u hu
    have h1 : |u.im - a.im| ≤ ‖u - a‖ := by
      simpa using Complex.abs_im_le_norm (u - a)
    have h2 : ‖u - a‖ = ‖a - u‖ := norm_sub_rev u a
    linarith [hS u hu]
  refine (hC a.im ρ hρ S him).trans ?_
  have hlog : Real.log (2 + |a.im| + ρ) ≤ Real.log (‖a‖ + ρ + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have := Complex.abs_im_le_norm a
    linarith
  exact mul_le_mul_of_nonneg_left (by linarith)
    (mul_nonneg (le_of_lt hCpos) (by linarith))

/-- **The main workhorse**: given the centered ball count for the zeros of `Ξ`, the multiplicity
weighted inverse-square zero sum of `ζ_K = ζ · L(·,χ)` is bounded by
`C (log q + log (2 + ‖w‖) + 2)` for `Re w ≥ 3/2`, uniformly in `q`, `χ`, `w`. -/
theorem zeroSumKMultBound_of_XiCount
    (hΞ : ∃ c : ℝ, 0 < c ∧ ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      ∀ S : Finset ℂ, (∀ u ∈ S, ‖a - u‖ ≤ ρ) →
        ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
          ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + 2))
    (harith_in : ∃ C : ℝ, 0 < C ∧ ∀ (x L A : ℝ), 0 ≤ x → 0 ≤ L → 0 ≤ A → ∀ K : ℕ,
      (∑ k ∈ Finset.range (K + 1), (4 / (4 : ℝ) ^ k) * (A * ((2 : ℝ) ^ k + 1) *
          (Real.log (x + (2 : ℝ) ^ k + 2) + L + 2)))
        ≤ C * A * (L + Real.log (2 + x) + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re),
      Summable (fun u : ℂ => ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ, ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2)
          ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) := by
  obtain ⟨cΞ, hcΞpos, hXiCount⟩ := hΞ
  obtain ⟨cL, hcLpos, hLCount⟩ := completedLBallCountFinset
  obtain ⟨Cd, hCdpos, harith⟩ := harith_in
  refine ⟨5 * (Cd * (cΞ + cL)) + 1, by positivity, ?_⟩
  intro q hq _inst χ hχ hprim w hw
  have hApos : 0 < cΞ + cL := by linarith
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hXnn : 0 ≤ ‖w‖ := norm_nonneg w
  set m : ℂ → ℝ := fun u => ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) with hm
  set X : ℝ := Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2 with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    have : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith)
    linarith
  have hkey : ∀ S : Finset ℂ,
      ∑ u ∈ S, ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2
        ≤ (5 * (Cd * (cΞ + cL))) * X := by
    intro S
    -- dyadic decomposition of the bounded kernel
    have hdyad : ∑ u ∈ S, m u * (1 / (1 + ‖w - u‖ ^ 2)) ≤ (Cd * (cΞ + cL)) * X := by
      obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ u ∈ S, ‖w - u‖ ≤ (2 : ℝ) ^ K := by
        rcases S.eq_empty_or_nonempty with h | hne
        · exact ⟨0, by intro u hu; rw [h] at hu; exact absurd hu (Finset.notMem_empty u)⟩
        · obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ u ∈ S, (‖w - u‖ + 1))
            (by norm_num : (1 : ℝ) < 2)
          refine ⟨K, fun u hu => ?_⟩
          have hle : ‖w - u‖ + 1 ≤ ∑ v ∈ S, (‖w - v‖ + 1) :=
            Finset.single_le_sum (f := fun v => ‖w - v‖ + 1) (fun v _ => by positivity) hu
          linarith
      have hstep : ∑ u ∈ S, m u * (1 / (1 + ‖w - u‖ ^ 2))
          ≤ ∑ u ∈ S, m u * (∑ k ∈ Finset.range (K + 1),
              (if ‖w - u‖ ≤ (2 : ℝ) ^ k then 4 / (4 : ℝ) ^ k else 0)) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Commons.Analysis.Dyadic.invSq_le_dyadic_layer ‖w - u‖ (norm_nonneg _) K (hK u hu)
      have hswap : ∑ u ∈ S, m u * (∑ k ∈ Finset.range (K + 1),
              (if ‖w - u‖ ≤ (2 : ℝ) ^ k then 4 / (4 : ℝ) ^ k else 0))
          = ∑ k ∈ Finset.range (K + 1), (4 / (4 : ℝ) ^ k) *
              ∑ u ∈ S, (if ‖w - u‖ ≤ (2 : ℝ) ^ k then m u else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun u _ => ?_)
        by_cases hp : ‖w - u‖ ≤ (2 : ℝ) ^ k
        · rw [if_pos hp, if_pos hp]; ring
        · rw [if_neg hp, if_neg hp]; ring
      have hlayer : ∀ k ∈ Finset.range (K + 1),
          (∑ u ∈ S, (if ‖w - u‖ ≤ (2 : ℝ) ^ k then m u else 0))
            ≤ (cΞ + cL) * ((2 : ℝ) ^ k + 1) *
                (Real.log (‖w‖ + (2 : ℝ) ^ k + 2) + Real.log (q : ℝ) + 2) := by
        intro k _
        have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        set T : Finset ℂ := S.filter (fun u => ‖w - u‖ ≤ (2 : ℝ) ^ k) with hT
        have hmem : ∀ u ∈ T, ‖w - u‖ ≤ (2 : ℝ) ^ k :=
          fun u hu => (Finset.mem_filter.mp hu).2
        have hsum_eq : ∑ u ∈ S, (if ‖w - u‖ ≤ (2 : ℝ) ^ k then m u else 0) = ∑ u ∈ T, m u := by
          rw [hT, Finset.sum_filter]
        have hsplit : ∑ u ∈ T, m u
            = (∑ u ∈ T, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ))
              + (∑ u ∈ T, (analyticOrderNatAt
                  (DirichletCharacter.completedLFunction χ) u : ℝ)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          simp only [hm, Work.LinnikAreas.DhK.kMult]
          push_cast
          ring
        have hΞb := hXiCount w ((2 : ℝ) ^ k) hk1 T (fun u hu => hmem u hu)
        have hLb := hLCount χ hχ hprim w ((2 : ℝ) ^ k) hk1 T (fun u hu => hmem u hu)
        have hLnn : 0 ≤ Real.log (‖w‖ + (2 : ℝ) ^ k + 2) :=
          Real.log_nonneg (by have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
                              linarith [norm_nonneg w])
        rw [hsum_eq, hsplit]
        calc (∑ u ∈ T, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ))
              + (∑ u ∈ T, (analyticOrderNatAt
                  (DirichletCharacter.completedLFunction χ) u : ℝ))
            ≤ cΞ * ((2 : ℝ) ^ k + 1) * (Real.log (‖w‖ + (2 : ℝ) ^ k + 2) + 2)
              + cL * ((2 : ℝ) ^ k + 1)
                  * (Real.log (‖w‖ + (2 : ℝ) ^ k + 2) + Real.log (q : ℝ) + 2) :=
              add_le_add hΞb hLb
          _ = ((2 : ℝ) ^ k + 1) * ((cΞ + cL) * Real.log (‖w‖ + (2 : ℝ) ^ k + 2)
                + cL * Real.log (q : ℝ) + 2 * (cΞ + cL)) := by ring
          _ ≤ ((2 : ℝ) ^ k + 1) * ((cΞ + cL) * Real.log (‖w‖ + (2 : ℝ) ^ k + 2)
                + (cΞ + cL) * Real.log (q : ℝ) + 2 * (cΞ + cL)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              nlinarith [hlogq, hcΞpos]
          _ = (cΞ + cL) * ((2 : ℝ) ^ k + 1)
                * (Real.log (‖w‖ + (2 : ℝ) ^ k + 2) + Real.log (q : ℝ) + 2) := by ring
      calc ∑ u ∈ S, m u * (1 / (1 + ‖w - u‖ ^ 2))
          ≤ ∑ u ∈ S, m u * (∑ k ∈ Finset.range (K + 1),
              (if ‖w - u‖ ≤ (2 : ℝ) ^ k then 4 / (4 : ℝ) ^ k else 0)) := hstep
        _ = ∑ k ∈ Finset.range (K + 1), (4 / (4 : ℝ) ^ k) *
              ∑ u ∈ S, (if ‖w - u‖ ≤ (2 : ℝ) ^ k then m u else 0) := hswap
        _ ≤ ∑ k ∈ Finset.range (K + 1), (4 / (4 : ℝ) ^ k) * ((cΞ + cL) * ((2 : ℝ) ^ k + 1) *
              (Real.log (‖w‖ + (2 : ℝ) ^ k + 2) + Real.log (q : ℝ) + 2)) :=
              Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hlayer k hk) (by positivity))
        _ ≤ Cd * (cΞ + cL) * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) :=
              harith ‖w‖ (Real.log (q : ℝ)) (cΞ + cL) hXnn hlogq (le_of_lt hApos) K
        _ = Cd * (cΞ + cL) * X := by rw [hX]
    have hstep1 : ∑ u ∈ S, m u / ‖w - u‖ ^ 2 ≤ 5 * ∑ u ∈ S, m u * (1 / (1 + ‖w - u‖ ^ 2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun u _ => kMult_div_norm_sq_le q χ hχ hprim w hw u)
    calc ∑ u ∈ S, ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2
        = ∑ u ∈ S, m u / ‖w - u‖ ^ 2 := rfl
      _ ≤ 5 * ∑ u ∈ S, m u * (1 / (1 + ‖w - u‖ ^ 2)) := hstep1
      _ ≤ 5 * ((Cd * (cΞ + cL)) * X) := mul_le_mul_of_nonneg_left hdyad (by norm_num)
      _ ≤ (5 * (Cd * (cΞ + cL))) * X := le_of_eq (by ring)
  have hfin : ∀ S : Finset ℂ,
      ∑ u ∈ S, ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2
        ≤ 5 * (Cd * (cΞ + cL)) * X := hkey
  refine ⟨summable_of_sum_le (fun u => by positivity) hfin, ?_⟩
  have htsum := Real.tsum_le_of_sum_le (f := fun u : ℂ =>
      ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2) (fun u => by positivity) hfin
  refine htsum.trans ?_
  rw [hX]
  have hlogw : 0 ≤ Real.log (2 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
  have hY1 : (1 : ℝ) ≤ Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2 := by linarith
  nlinarith [hY1, hCdpos, hApos]

/-- The centered ball count of the zeros of `Ξ`, assembled from the unit-window count
(`XiUnitWindowCount`), the covering of a window of height `h` by unit windows (`XiWindowCount`) and
the containment of a ball in a window (`xiBallCount_of_window`). -/
theorem xiBallCountCentered_assembled :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      ∀ S : Finset ℂ, (∀ u ∈ S, ‖a - u‖ ≤ ρ) →
        ∑ u ∈ S, (analyticOrderNatAt Work.LinnikAreas.DhK.Xi u : ℝ)
          ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + 2) :=
  xiBallCount_of_window (XiWindowCount XiUnitWindowCount)

theorem zeroSumKMultBound : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (w : ℂ) (hw : (3 / 2 : ℝ) ≤ w.re),
    Summable (fun u : ℂ => ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2) ∧
      (∑' u : ℂ, ((Work.LinnikAreas.DhK.kMult χ u : ℕ) : ℝ) / ‖w - u‖ ^ 2)
        ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2) :=
  zeroSumKMultBound_of_XiCount xiBallCountCentered_assembled dyadicBallSumLe

end Work.LinnikAreas.DhExplicit
