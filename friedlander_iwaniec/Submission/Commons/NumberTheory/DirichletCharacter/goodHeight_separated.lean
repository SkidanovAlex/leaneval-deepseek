import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.Analysis.Intervals.exists_distant_of_finset

open Complex DirichletCharacter
open scoped BigOperators Topology

namespace Commons.NumberTheory.DirichletCharacter

/-- `Λ(·,χ)` never has infinite (analytic) order, because it is entire and does not vanish
identically (`Λ(1,χ) ≠ 0`). -/
private lemma completedL_analyticOrder_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (u : ℂ) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) u ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => hΛdiff.analyticAt z
  have hEq : Set.EqOn (DirichletCharacter.completedLFunction χ) 0 Set.univ :=
    hΛan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ u) htop
  exact (Commons.NumberTheory.Linnik.completedLFunction_one_ne_zero χ hχ) (hEq (Set.mem_univ 1))

/-- The meromorphic order of `Λ(·,χ)` is finite everywhere. -/
private lemma completedL_meromorphicOrderAt_ne_top {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (u : ℂ) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u ≠ ⊤ := by
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  intro h
  rw [(hΛdiff.analyticAt u).meromorphicOrderAt_eq] at h
  rw [ENat.map_eq_top_iff] at h
  exact completedL_analyticOrder_ne_top χ hχ u h

/-- A zero of `Λ(·,χ)` inside a closed ball is in the support of the divisor. -/
private lemma completedL_divisor_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {R : ℝ} {ρ : ℂ}
    (hρU : ρ ∈ Metric.closedBall (0 : ℂ) R)
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R)) ρ
      ≠ 0 := by
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) R) := fun z _ => hΛdiff.analyticAt z
  have hsupp := MeromorphicNFOn.zero_set_eq_divisor_support hΛan.meromorphicNFOn
    (fun u => completedL_meromorphicOrderAt_ne_top χ hχ u.1)
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R ∩
      (DirichletCharacter.completedLFunction χ) ⁻¹' {0} :=
    ⟨hρU, by simpa using hρ⟩
  rw [hsupp] at hmem
  simpa [Function.mem_support] using hmem

/-- The divisor of an analytic function, cast to `ℝ`, is pointwise non-negative. -/
private lemma divisor_cast_nonneg {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (u : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U u : ℤ) : ℝ) := by
  have h := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  exact_mod_cast (h u)

/-- The divisor of an analytic function, cast to `ℝ`, has finite support on a closed ball. -/
private lemma divisor_cast_finiteSupport (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ)) := by
  have hfinZ : (Function.support
      (fun u : ℂ => (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ))).Finite := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor f (Metric.closedBall c R)).finiteSupport (isCompact_closedBall c R))
  refine hfinZ.subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  exact fun hz => hu (by exact_mod_cast hz)

/-- Elementary logarithmic estimate: for `T ≥ 1` and `N ≥ 1`,
`log (T + 6) + log N + 2 ≤ 4 * log (N * (T + 4))`. -/
private lemma window_log_bound {T : ℝ} (hT : 1 ≤ T) {N : ℕ} [NeZero N] :
    Real.log (T + 6) + Real.log (N : ℝ) + 2 ≤ 4 * Real.log ((N : ℝ) * (T + 4)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hT4 : 0 < T + 4 := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h1 : Real.log (T + 6) ≤ Real.log 2 + Real.log (T + 4) := by
    have h2 : T + 6 ≤ 2 * (T + 4) := by linarith
    calc Real.log (T + 6) ≤ Real.log (2 * (T + 4)) := Real.log_le_log (by linarith) h2
      _ = Real.log 2 + Real.log (T + 4) := Real.log_mul (by norm_num) (ne_of_gt hT4)
  have hmul : Real.log ((N : ℝ) * (T + 4)) = Real.log (N : ℝ) + Real.log (T + 4) :=
    Real.log_mul (ne_of_gt hNpos) (ne_of_gt hT4)
  have hL1 : 1 ≤ Real.log ((N : ℝ) * (T + 4)) := by
    have h5 : (5 : ℝ) ≤ (N : ℝ) * (T + 4) := by
      have hT5 : (5 : ℝ) ≤ T + 4 := by linarith
      calc (5 : ℝ) = 1 * 5 := by ring
        _ ≤ (N : ℝ) * (T + 4) := mul_le_mul hN1 hT5 (by norm_num) (by linarith)
    have hexp : Real.exp 1 ≤ (N : ℝ) * (T + 4) := by
      have := Real.exp_one_lt_three
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  calc Real.log (T + 6) + Real.log (N : ℝ) + 2
      ≤ (Real.log 2 + Real.log (T + 4)) + Real.log (N : ℝ) + 2 := by linarith
    _ = Real.log ((N : ℝ) * (T + 4)) + 2 + Real.log 2 := by
          rw [hmul]; ring
    _ ≤ Real.log ((N : ℝ) * (T + 4)) + 3 := by linarith
    _ ≤ 4 * Real.log ((N : ℝ) * (T + 4)) := by linarith

/-- **A "good height" far from all zeros of the completed L-function.**

For a primitive non-trivial Dirichlet character `χ mod N` there is a constant `c > 0` such
that for every `T ≥ 1` one can choose `T' ∈ [T+1, T+2]` whose distance to every zero height
of `Λ(·,χ) = completedLFunction χ` is at least `c / log (N*(T'+3))`.

Proof sketch: the number of zeros with `|Im ρ| ∈ [T, T+2]` is `≪ log (N (T+3))` (local zero
count, `windowZeroCountC`); a pigeonhole/measure argument on `[T+1,T+2]` then produces a
height at distance `≥ 1/(4(M+1))` from all these heights and from their negatives, while all
other zeros are automatically at distance `≥ 1` from `[T+1,T+2]`. -/
theorem goodHeight_separated {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 1 ≤ T → ∃ T' : ℝ, T + 1 ≤ T' ∧ T' ≤ T + 2 ∧
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        c / Real.log (N * (T' + 3)) ≤ |ρ.im - T'|) ∧
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        c / Real.log (N * (T' + 3)) ≤ |ρ.im + T'|) := by
  classical
  obtain ⟨cw, hcwpos, hwzc⟩ :=
    Commons.NumberTheory.DirichletCharacter.windowZeroCountC χ hχ hχprim
  let cf : ℝ := min (1 / 2) (1 / (160 * cw))
  have hcfpos : 0 < cf := by
    dsimp [cf]
    exact lt_min (by norm_num) (by positivity)
  have hcf_half : cf ≤ 1 / 2 := by dsimp [cf]; exact min_le_left _ _
  have hcf_le : cf ≤ 1 / (160 * cw) := by dsimp [cf]; exact min_le_right _ _
  refine ⟨cf, hcfpos, ?_⟩
  intro T hT
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by
    simpa [Λ] using DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : AnalyticOnNhd ℂ Λ Set.univ := fun z _ => hΛdiff.analyticAt z
  -- ===== the local window bound =====
  let F : ℂ → ℝ :=
    fun u => ((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 4)) u : ℤ) : ℝ)
  let w : ℂ → ℝ := fun u => if T ≤ |u.im| ∧ |u.im| ≤ T + 3 then (1 : ℝ) else 0
  let G : ℂ → ℝ := fun u => F u * w u
  have hwin_raw := hwzc T (T + 3) hT (by linarith : T ≤ T + 3)
  have hwinG : (∑ᶠ u : ℂ, G u)
      ≤ cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2) := by
    have hfun : G = (fun u : ℂ =>
        (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 3 + 1))) u : ℤ) : ℝ)
          * (if T ≤ |u.im| ∧ |u.im| ≤ T + 3 then (1 : ℝ) else 0)) := by
      funext u
      simp only [G, F, w]
      rw [show (T : ℝ) + 4 = T + 3 + 1 by ring]
    rw [hfun]
    have e1 : ((T : ℝ) + 3 - T + 2) = 5 := by ring
    have e2 : ((T : ℝ) + 3 + 3) = T + 6 := by ring
    rw [e1, e2] at hwin_raw
    exact hwin_raw
  -- ===== finite support and the counting finset =====
  have hfinF : Function.HasFiniteSupport F := by
    dsimp only [F]
    exact divisor_cast_finiteSupport (DirichletCharacter.completedLFunction χ) 0 (T + 4)
  have hfinG0 : Function.HasFiniteSupport G := by
    dsimp only [G]
    exact Function.HasFiniteSupport.mul_left hfinF w
  have hfinG : (Function.support G).Finite := hfinG0
  let D : Finset ℂ := hfinG.toFinset
  have hDdef : D = hfinG.toFinset := rfl
  have hDsum : (∑ᶠ u : ℂ, G u) = ∑ u ∈ D, G u := by
    refine finsum_eq_sum_of_support_subset G ?_
    intro x hx
    rw [hDdef]
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hx
  have hF_nonneg : ∀ u : ℂ, (0 : ℝ) ≤ F u := by
    intro u
    dsimp only [F, Λ]
    exact divisor_cast_nonneg (fun z _ => hΛdiff.analyticAt z) u
  have hDcard : (D.card : ℝ) ≤ ∑ u ∈ D, G u := by
    have h1 : ∑ u ∈ D, (1 : ℝ) ≤ ∑ u ∈ D, G u := by
      refine Finset.sum_le_sum ?_
      intro u hu
      have hGu_ne : G u ≠ 0 := by
        have hu' : u ∈ hfinG.toFinset := by rwa [hDdef] at hu
        have : u ∈ Function.support G := hfinG.mem_toFinset.mp hu'
        simpa [Function.mem_support] using this
      have hFne : F u ≠ 0 := by
        intro h0
        exact hGu_ne (by simp [G, h0])
      have hF1 : (1 : ℝ) ≤ F u := by
        have hnn : (0 : ℤ) ≤ MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 4)) u := by
          have := hF_nonneg u
          dsimp only [F, Λ] at this
          exact_mod_cast this
        have hne : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 4)) u ≠ 0 := by
          intro h0
          apply hFne
          dsimp only [F]
          rw [h0]; norm_num
        have h1z : (1 : ℤ) ≤ MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 4)) u := by
          omega
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 4)) u : ℤ) : ℝ) := by
                exact_mod_cast h1z
          _ = F u := rfl
      have hw01 : w u = 0 ∨ w u = 1 := by
        by_cases hc : T ≤ |u.im| ∧ |u.im| ≤ T + 3
        · right; dsimp only [w]; rw [if_pos hc]
        · left; dsimp only [w]; rw [if_neg hc]
      rcases hw01 with hw0 | hw1
      · exact absurd (by simp [G, hw0]) hGu_ne
      · dsimp only [G]; rw [hw1, mul_one]; exact hF1
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  -- ===== the set of bad centres =====
  let S : Finset ℝ := D.image (fun u : ℂ => u.im) ∪ D.image (fun u : ℂ => -u.im)
  have hScard : (S.card : ℝ) ≤ 2 * (cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2)) := by
    have hDle : (D.card : ℝ) ≤ cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2) := by
      calc (D.card : ℝ) ≤ ∑ u ∈ D, G u := hDcard
        _ = ∑ᶠ u : ℂ, G u := hDsum.symm
        _ ≤ cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2) := hwinG
    have hcard_nat : S.card ≤ 2 * D.card := by
      have h1 : S.card ≤ (D.image (fun u : ℂ => u.im)).card
          + (D.image (fun u : ℂ => -u.im)).card := Finset.card_union_le _ _
      have h2 : (D.image (fun u : ℂ => u.im)).card ≤ D.card := Finset.card_image_le
      have h3 : (D.image (fun u : ℂ => -u.im)).card ≤ D.card := Finset.card_image_le
      omega
    calc (S.card : ℝ) ≤ ((2 * D.card : ℕ) : ℝ) := by exact_mod_cast hcard_nat
      _ = 2 * (D.card : ℝ) := by push_cast; ring
      _ ≤ 2 * (cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2)) := by linarith
  have hScont : ∀ ρ : ℂ, Λ ρ = 0 → T ≤ |ρ.im| → |ρ.im| ≤ T + 3 →
      ρ.im ∈ S ∧ -ρ.im ∈ S := by
    intro ρ hρ h1 h2
    have hw1 : w ρ = 1 := by dsimp only [w]; rw [if_pos ⟨h1, h2⟩]
    have hρball : ρ ∈ Metric.closedBall (0 : ℂ) (T + 4) := by
      have hstrip := zerosInStrip χ hχ hχprim ρ (by simpa [Λ] using hρ)
      rw [Metric.mem_closedBall, dist_zero_right]
      have hre : |ρ.re| ≤ 1 := by rw [abs_of_pos hstrip.1]; exact le_of_lt hstrip.2
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ ≤ 1 + (T + 3) := by linarith
        _ = T + 4 := by ring
    have hFne : F ρ ≠ 0 := by
      intro h0
      have hd0 : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (T + 4)) ρ : ℤ) = 0 := by
        have := h0
        dsimp only [F] at this
        exact_mod_cast this
      exact (completedL_divisor_ne_zero χ hχ hρball (by simpa [Λ] using hρ)) hd0
    have hGne : G ρ ≠ 0 := by dsimp only [G]; rw [hw1, mul_one]; exact hFne
    have hmem : ρ ∈ D := by
      rw [hDdef, Set.Finite.mem_toFinset]
      simpa [Function.mem_support] using hGne
    refine ⟨?_, ?_⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩))
  -- ===== logarithmic comparability of `N*(T+4)` and `N*(T'+3)` =====
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hLlpos : 0 < Real.log ((N : ℝ) * (T + 4)) := by
    apply Real.log_pos
    have hT4 : (5 : ℝ) ≤ T + 4 := by linarith
    calc (1 : ℝ) < 5 := by norm_num
      _ ≤ (N : ℝ) * (T + 4) := by
          calc (5 : ℝ) = 1 * 5 := by ring
            _ ≤ (N : ℝ) * (T + 4) := mul_le_mul hN1 hT4 (by norm_num) (by linarith)
  -- ===== the combinatorial choice of `T'` =====
  set δ : ℝ := cf / Real.log ((N : ℝ) * (T + 4)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hcfpos hLlpos
  have hcard : 2 * δ * (S.card : ℝ) ≤ (T + 2) - (T + 1) := by
    have hone : (T + 2) - (T + 1) = (1 : ℝ) := by ring
    rw [hone]
    have hlog := window_log_bound (N := N) hT
    have hstep : 2 * δ * (S.card : ℝ)
        ≤ 2 * (cf / Real.log ((N : ℝ) * (T + 4)))
            * (2 * (cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2))) := by
      rw [hδdef]
      apply mul_le_mul_of_nonneg_left hScard
      positivity
    have hdiv : (Real.log (T + 6) + Real.log (N : ℝ) + 2) / Real.log ((N : ℝ) * (T + 4)) ≤ 4 := by
      rw [div_le_iff₀ hLlpos]
      linarith
    have hstep2 : 2 * (cf / Real.log ((N : ℝ) * (T + 4)))
          * (2 * (cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2)))
        = 20 * cf * cw * ((Real.log (T + 6) + Real.log (N : ℝ) + 2)
              / Real.log ((N : ℝ) * (T + 4))) := by
      field_simp
      ring
    have hcfcw : cf * cw ≤ 1 / 160 := by
      have h1 : cf * cw ≤ (1 / (160 * cw)) * cw :=
        mul_le_mul_of_nonneg_right hcf_le (le_of_lt hcwpos)
      have h2 : (1 / (160 * cw)) * cw = 1 / 160 := by
        field_simp
      linarith [h1, h2]
    calc 2 * δ * (S.card : ℝ)
        ≤ 2 * (cf / Real.log ((N : ℝ) * (T + 4)))
            * (2 * (cw * 5 * (Real.log (T + 6) + Real.log (N : ℝ) + 2))) := hstep
      _ = 20 * cf * cw * ((Real.log (T + 6) + Real.log (N : ℝ) + 2)
              / Real.log ((N : ℝ) * (T + 4))) := hstep2
      _ ≤ 20 * cf * cw * 4 := by
            apply mul_le_mul_of_nonneg_left hdiv
            have : (0 : ℝ) ≤ cf * cw := mul_nonneg (le_of_lt hcfpos) (le_of_lt hcwpos)
            linarith
      _ ≤ 20 * (1 / 160) * 4 := by
            have : 0 ≤ cf * cw := mul_nonneg (le_of_lt hcfpos) (le_of_lt hcwpos)
            nlinarith [hcfcw]
      _ = 1 / 2 := by norm_num
      _ ≤ 1 := by norm_num
  obtain ⟨T', hT'lo, hT'hi, hfar⟩ :=
    Commons.Analysis.Intervals.exists_distant_of_finset (S := S) (t := δ) (a := T + 1) (b := T + 2)
      hδpos hcard
  -- ===== conclusion =====
  have hlogcmp : cf / Real.log ((N : ℝ) * (T' + 3)) ≤ δ := by
    have harg : (N : ℝ) * (T + 4) ≤ (N : ℝ) * (T' + 3) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
      linarith
    have hlog : Real.log ((N : ℝ) * (T + 4)) ≤ Real.log ((N : ℝ) * (T' + 3)) :=
      Real.log_le_log (by positivity) harg
    rw [hδdef]
    exact div_le_div_of_nonneg_left (le_of_lt hcfpos) hLlpos hlog
  have hcle1 : cf / Real.log ((N : ℝ) * (T' + 3)) ≤ 1 := by
    have harg : (N : ℝ) * (T + 4) ≤ (N : ℝ) * (T' + 3) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
      linarith
    have hlog : Real.log ((N : ℝ) * (T + 4)) ≤ Real.log ((N : ℝ) * (T' + 3)) :=
      Real.log_le_log (by positivity) harg
    have hlog1 : 1 ≤ Real.log ((N : ℝ) * (T' + 3)) := by
      have h5 : (5 : ℝ) ≤ (N : ℝ) * (T + 4) := by
        have hT5 : (5 : ℝ) ≤ T + 4 := by linarith
        calc (5 : ℝ) = 1 * 5 := by ring
          _ ≤ (N : ℝ) * (T + 4) := mul_le_mul hN1 hT5 (by norm_num) (by linarith)
      have hexp : Real.exp 1 ≤ (N : ℝ) * (T + 4) := by
        have := Real.exp_one_lt_three
        linarith
      have h1' : 1 ≤ Real.log ((N : ℝ) * (T + 4)) := by
        have := Real.log_le_log (Real.exp_pos 1) hexp
        rwa [Real.log_exp] at this
      linarith
    have hlogpos' : 0 < Real.log ((N : ℝ) * (T' + 3)) := lt_of_lt_of_le hLlpos hlog
    rw [div_le_one hlogpos']
    exact le_trans (le_trans hcf_half (by norm_num)) hlog1
  refine ⟨T', hT'lo, hT'hi, ?_, ?_⟩
  · intro ρ hρ
    by_cases hrel : T ≤ |ρ.im| ∧ |ρ.im| ≤ T + 3
    · obtain ⟨hS1, _⟩ := hScont ρ hρ hrel.1 hrel.2
      calc cf / Real.log ((N : ℝ) * (T' + 3)) ≤ δ := hlogcmp
        _ ≤ |T' - ρ.im| := hfar ρ.im hS1
        _ = |ρ.im - T'| := abs_sub_comm _ _
    · have hnot : |ρ.im| < T ∨ T + 3 < |ρ.im| := by
        rcases lt_or_ge |ρ.im| T with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge (fun hc => hrel ⟨h, hc⟩))
      have hdist : 1 ≤ |ρ.im - T'| := by
        rcases hnot with hlt | hgt
        · have him2 : ρ.im < T := (abs_lt.mp hlt).2
          have : ρ.im - T' ≤ -1 := by linarith [him2, hT'lo]
          rw [abs_of_nonpos (by linarith)]
          linarith
        · rcases (lt_abs.mp hgt) with him3 | him4
          · have : 1 ≤ ρ.im - T' := by linarith [him3, hT'hi]
            rw [abs_of_nonneg (by linarith)]
            exact this
          · have : ρ.im - T' ≤ -1 := by linarith [him4, hT'lo]
            rw [abs_of_nonpos (by linarith)]
            linarith
      calc cf / Real.log ((N : ℝ) * (T' + 3)) ≤ 1 := hcle1
        _ ≤ |ρ.im - T'| := hdist
  · intro ρ hρ
    by_cases hrel : T ≤ |ρ.im| ∧ |ρ.im| ≤ T + 3
    · obtain ⟨_, hS2⟩ := hScont ρ hρ hrel.1 hrel.2
      calc cf / Real.log ((N : ℝ) * (T' + 3)) ≤ δ := hlogcmp
        _ ≤ |T' - (-ρ.im)| := hfar (-ρ.im) hS2
        _ = |ρ.im + T'| := by rw [show T' - (-ρ.im) = ρ.im + T' by ring]
    · have hnot : |ρ.im| < T ∨ T + 3 < |ρ.im| := by
        rcases lt_or_ge |ρ.im| T with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge (fun hc => hrel ⟨h, hc⟩))
      have hdist : 1 ≤ |ρ.im + T'| := by
        rcases hnot with hlt | hgt
        · have him1 : -T < ρ.im := (abs_lt.mp hlt).1
          have : 1 ≤ ρ.im + T' := by linarith [him1, hT'lo]
          rw [abs_of_nonneg (by linarith)]
          exact this
        · rcases (lt_abs.mp hgt) with him3 | him4
          · have : 1 ≤ ρ.im + T' := by linarith [him3, hT'lo]
            rw [abs_of_nonneg (by linarith)]
            exact this
          · have : ρ.im + T' ≤ -1 := by linarith [him4, hT'hi]
            rw [abs_of_nonpos (by linarith)]
            linarith
      calc cf / Real.log ((N : ℝ) * (T' + 3)) ≤ 1 := hcle1
        _ ≤ |ρ.im + T'| := hdist

end Commons.NumberTheory.DirichletCharacter
