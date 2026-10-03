import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.NumberTheory.Linnik.partialFraction_conv
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

namespace Work.FIArea5.HeckeZFR.Hadm

open Complex Metric Filter MeromorphicOn
open scoped Topology Real BigOperators

set_option maxHeartbeats 1600000
noncomputable section

/-- Per-term bound for the Hadamard kernel `1/(s-u) - 1/(s₁-u)`. -/
theorem pfKernelBound {s s₁ u : ℂ} (hu0 : 0 < ‖u‖) (hu : 2 * max ‖s‖ ‖s₁‖ ≤ ‖u‖) :
    ‖1 / (s - u) - 1 / (s₁ - u)‖ ≤ 4 * ‖s - s₁‖ / ‖u‖ ^ 2 := by
  have hs_le : ‖s‖ ≤ ‖u‖ / 2 := by
    have h1 : ‖s‖ ≤ max ‖s‖ ‖s₁‖ := le_max_left _ _
    linarith
  have hs₁_le : ‖s₁‖ ≤ ‖u‖ / 2 := by
    have h1 : ‖s₁‖ ≤ max ‖s‖ ‖s₁‖ := le_max_right _ _
    linarith
  have hsu_ge : ‖u‖ / 2 ≤ ‖s - u‖ := by
    have h := abs_norm_sub_norm_le u s
    rw [norm_sub_rev] at h
    have h2 : ‖u‖ - ‖s‖ ≤ ‖s - u‖ := le_trans (le_abs_self _) h
    linarith
  have hs₁u_ge : ‖u‖ / 2 ≤ ‖s₁ - u‖ := by
    have h := abs_norm_sub_norm_le u s₁
    rw [norm_sub_rev] at h
    have h2 : ‖u‖ - ‖s₁‖ ≤ ‖s₁ - u‖ := le_trans (le_abs_self _) h
    linarith
  have hsu_ne : s - u ≠ 0 := by
    intro h
    have : ‖s - u‖ = 0 := by rw [h, norm_zero]
    linarith [hu0]
  have hs₁u_ne : s₁ - u ≠ 0 := by
    intro h
    have : ‖s₁ - u‖ = 0 := by rw [h, norm_zero]
    linarith [hu0]
  have hident : 1 / (s - u) - 1 / (s₁ - u) = (s₁ - s) / ((s - u) * (s₁ - u)) := by
    field_simp
    ring
  calc
    ‖1 / (s - u) - 1 / (s₁ - u)‖ = ‖(s₁ - s) / ((s - u) * (s₁ - u))‖ := by rw [hident]
    _ = ‖s₁ - s‖ / (‖s - u‖ * ‖s₁ - u‖) := by rw [norm_div, norm_mul]
    _ ≤ ‖s₁ - s‖ / ((‖u‖ / 2) * (‖u‖ / 2)) := by
        refine div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) ?_
        exact mul_le_mul hsu_ge hs₁u_ge (by positivity) (by positivity)
    _ = 4 * ‖s - s₁‖ / ‖u‖ ^ 2 := by
        rw [norm_sub_rev s₁ s]
        field_simp
        ring

/-- **Dyadic tail bound for the Hadamard partial sums.** -/
theorem pfHadamardTail (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ)
    (K c M : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (R R' : ℝ) (hR : 2 ≤ R) (hRR' : R ≤ R')
    (hcount : ∀ ρ : ℝ, 2 ≤ ρ →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 ρ)) u : ℝ)) ≤
        c * ρ * (Real.log (ρ + 2) + K))
    (w : ℂ → ℂ) (hw : ∀ u : ℂ, R ≤ ‖u‖ → ‖w u‖ ≤ M / ‖u‖ ^ 2) :
    ‖(∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R')) u : ℤ) : ℂ) * w u)
      - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u)‖
      ≤ 64 * c * M * (Real.log (R + 2) + K + 1) / R := by
  classical
  have hAnAll : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hDiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hAnAll U).meromorphicOn
  have hdivnn : ∀ (ρ : ℝ) (u : ℂ), 0 ≤ MeromorphicOn.divisor Λ (closedBall 0 ρ) u :=
    fun ρ u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAnAll _) u
  let m : ℝ → ℂ → ℤ := fun ρ u => MeromorphicOn.divisor Λ (closedBall 0 ρ) u
  let F : ℝ → ℂ := fun ρ => ∑ᶠ u : ℂ, (((m ρ u : ℤ) : ℂ) * w u)
  have hfin : ∀ ρ : ℝ, (m ρ).support.Finite := fun ρ =>
    (MeromorphicOn.divisor Λ (closedBall 0 ρ)).finiteSupport (isCompact_closedBall (0 : ℂ) ρ)
  let S : Finset ℂ := (hfin R').toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ m R' u ≠ 0 := by
    intro u
    dsimp only [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hRpos : 0 < R := by linarith
  -- rewriting the two partial sums as finite sums over `S`
  have hF' : F R' = ∑ u ∈ S, (((m R' u : ℤ) : ℂ) * w u) := by
    dsimp only [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R' u ≠ 0 := fun hz => hu (by simp [hz])
    exact (hS_mem u).mpr hm
  have hF : F R = ∑ u ∈ S, (((m R u : ℤ) : ℂ) * w u) := by
    dsimp only [F]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hm : m R u ≠ 0 := fun hz => hu (by simp [hz])
    have huB : u ∈ closedBall 0 R :=
      (MeromorphicOn.divisor Λ (closedBall 0 R)).supportWithinDomain hm
    have hle : ‖u‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hEq : m R u = m R' u := by
      dsimp only [m]
      exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer hle (le_trans hle hRR')
    have hm' : m R' u ≠ 0 := by rwa [← hEq]
    exact (hS_mem u).mpr hm'
  have hD : F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ)) : ℂ) * w u) := by
    rw [hF', hF]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro u hu
    simp [Int.cast_sub, sub_mul]
  -- collapsing to the annulus `R < ‖u‖`
  let T : Finset ℂ := S.filter (fun u => R < ‖u‖)
  have hDcoll : F R' - F R = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := by
    have hstep : ∀ u ∈ S, ((((m R' u - m R u : ℤ)) : ℂ) * w u) =
        if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0 := by
      intro u _
      by_cases hbig : R < ‖u‖
      · have hmR0 : m R u = 0 := by
          dsimp only [m]
          exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_zero_of_lt_norm (f := Λ) hbig
        simp [hbig, hmR0]
      · have hle : ‖u‖ ≤ R := le_of_not_gt hbig
        have hEq : m R u = m R' u := by
          dsimp only [m]
          exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer hle (le_trans hle hRR')
        simp [hbig, hEq]
    calc F R' - F R = ∑ u ∈ S, ((((m R' u - m R u : ℤ)) : ℂ) * w u) := hD
      _ = ∑ u ∈ S, (if R < ‖u‖ then (((m R' u : ℤ) : ℂ) * w u) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hstep u hu
      _ = ∑ u ∈ S.filter (fun u => R < ‖u‖), (((m R' u : ℤ) : ℂ) * w u) := by
          rw [Finset.sum_filter]
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℂ) * w u) := rfl
  -- pointwise norm bound
  have hnorm : ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := by
    rw [hDcoll]
    exact norm_sum_le T (fun u => (((m R' u : ℤ) : ℂ) * w u))
  have hterm : ∀ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ = (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    intro u _
    have hm0 : (0 : ℤ) ≤ m R' u := hdivnn R' u
    rw [norm_mul, Complex.norm_int_of_nonneg hm0]
  have hnorm2 : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
    calc ‖F R' - F R‖ ≤ ∑ u ∈ T, ‖(((m R' u : ℤ) : ℂ) * w u)‖ := hnorm
      _ = ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          exact hterm u hu
  have hwu : ∀ u ∈ T, ‖w u‖ ≤ M / ‖u‖ ^ 2 := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    exact hw u (le_of_lt hbig)
  have hbnd : ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / ‖u‖ ^ 2)) := by
    calc ‖F R' - F R‖ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * ‖w u‖) := hnorm2
      _ ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / ‖u‖ ^ 2)) := by
          refine Finset.sum_le_sum ?_
          intro u huT
          exact mul_le_mul_of_nonneg_left (hwu u huT) (by exact_mod_cast hdivnn R' u)
  -- dyadic bookkeeping
  let jl : ℂ → ℕ := fun u =>
    Commons.NumberTheory.Linnik.dyadIdx R ‖u‖ (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_spec : ∀ u : ℂ, ‖u‖ ≤ (2 : ℝ) ^ (jl u + 1) * R := by
    intro u
    dsimp only [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_spec_le R ‖u‖
      (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos)
  have hjl_low : ∀ u : ℂ, R < ‖u‖ → (2 : ℝ) ^ (jl u) * R < ‖u‖ := by
    intro u hu
    dsimp only [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_lower
      (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hu
  obtain ⟨K₀, hK₀⟩ := Commons.NumberTheory.Linnik.exists_dyadic_ge R R' hRpos
  have hjl_le : ∀ u ∈ T, jl u ≤ K₀ := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have huS : u ∈ S := (Finset.mem_filter.mp huT).1
    have hm : m R' u ≠ 0 := (hS_mem u).mp huS
    have huB : u ∈ closedBall 0 R' :=
      (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm
    have huR' : ‖u‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
    have hK' : ‖u‖ ≤ (2 : ℝ) ^ (K₀ + 1) * R := le_trans huR' hK₀
    dsimp only [jl]
    exact Commons.NumberTheory.Linnik.dyadIdx_le_of R ‖u‖
      (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hK'
  -- the dyadic fibres
  let Tj : ℕ → Finset ℂ := fun j => S.filter
    (fun u => (2 : ℝ) ^ j * R < ‖u‖ ∧ ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R)
  let b : ℕ → ℝ := fun j => ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ)
  have hb0 : ∀ j : ℕ, 0 ≤ b j := by
    intro j
    dsimp only [b]
    exact Finset.sum_nonneg (fun u _ => by exact_mod_cast hdivnn R' u)
  have hweight : ∀ j : ℕ, 0 ≤ M / (((4 : ℝ) ^ j) * R ^ 2) := by
    intro j
    exact div_nonneg hM (by positivity)
  -- pointwise replacement of `1/‖u‖²` by the dyadic weight
  have hwM : ∀ u ∈ T, M / ‖u‖ ^ 2 ≤ M / (((4 : ℝ) ^ (jl u)) * R ^ 2) := by
    intro u huT
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hsq := Commons.NumberTheory.Linnik.dyadIdx_sq_le (R := R) (ρ := ‖u‖) hRpos
      (Commons.NumberTheory.Linnik.exists_dyadic_ge R ‖u‖ hRpos) hbig
    exact div_le_div_of_nonneg_left hM (by positivity) hsq
  have hw1 : ∀ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / ‖u‖ ^ 2)) ≤
      (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ (jl u)) * R ^ 2))) := by
    intro u huT
    exact mul_le_mul_of_nonneg_left (hwM u huT) (by exact_mod_cast hdivnn R' u)
  -- the fibre/annulus decomposition
  have hfib_le_Tj : ∀ j : ℕ, T.filter (fun u => jl u = j) ⊆ Tj j := by
    intro j u hu
    have hmem := Finset.mem_filter.mp hu
    have huT : u ∈ T := hmem.1
    have hEq : jl u = j := hmem.2
    have hS' : u ∈ S := (Finset.mem_filter.mp huT).1
    have hbig : R < ‖u‖ := (Finset.mem_filter.mp huT).2
    have hlow : (2 : ℝ) ^ j * R < ‖u‖ := by
      have h := hjl_low u hbig
      rwa [hEq] at h
    have hup : ‖u‖ ≤ (2 : ℝ) ^ (j + 1) * R := by
      have h := hjl_spec u
      rwa [hEq] at h
    exact Finset.mem_filter.mpr ⟨hS', hlow, hup⟩
  have hfib_b : ∀ j : ℕ, (∑ u ∈ T.filter (fun u => jl u = j), ((m R' u : ℤ) : ℝ)) ≤ b j := by
    intro j
    dsimp only [b]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hfib_le_Tj j)
      (fun u _ _ => by exact_mod_cast hdivnn R' u)
  have hpart : (∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ (jl u)) * R ^ 2)))) =
      ∑ j ∈ Finset.range (K₀ + 1),
        ∑ u ∈ T.filter (fun u => jl u = j), (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ j) * R ^ 2))) := by
    have hpf := Commons.NumberTheory.Linnik.Finset.sum_eq_sum_image_filter (s := T) (g := jl)
      (f := fun u => (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ (jl u)) * R ^ 2))))
    have himg : T.image jl ⊆ Finset.range (K₀ + 1) := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨u, huT, hEq⟩
      have hle : j ≤ K₀ := by rw [← hEq]; exact hjl_le u huT
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
    calc (∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ (jl u)) * R ^ 2))))
        = ∑ j ∈ T.image jl, ∑ u ∈ T.filter (fun u => jl u = j),
            (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ j) * R ^ 2))) := by
          rw [hpf]
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro u hu
          have hEq : jl u = j := (Finset.mem_filter.mp hu).2
          simp [hEq]
      _ = ∑ j ∈ Finset.range (K₀ + 1),
            ∑ u ∈ T.filter (fun u => jl u = j), (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ j) * R ^ 2))) := by
          refine Finset.sum_subset himg ?_
          intro j _ hnot
          have hfib_empty : (T.filter (fun u => jl u = j)) = ∅ := by
            ext u
            constructor
            · intro hu
              exact absurd (Finset.mem_image.mpr ⟨u, (Finset.mem_filter.mp hu).1,
                (Finset.mem_filter.mp hu).2⟩) hnot
            · intro hu
              simp at hu
          simp [hfib_empty]
  -- the per-annulus count bound
  have hb_le : ∀ j : ℕ, b j ≤ c * (2 : ℝ) ^ (j + 1) * R *
      (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + K) := by
    intro j
    let ρ : ℝ := (2 : ℝ) ^ (j + 1) * R
    have hρ2 : 2 ≤ ρ := by
      dsimp only [ρ]
      have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by omega : (1 : ℕ) ≤ j + 1)
        simpa using this
      nlinarith
    let Sρ : Finset ℂ := (hfin ρ).toFinset
    have hSρ_mem : ∀ u : ℂ, u ∈ Sρ ↔ m ρ u ≠ 0 := by
      intro u
      dsimp only [Sρ]
      rw [Set.Finite.mem_toFinset]
      rfl
    have hcountρ : (∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ)) ≤
        c * ρ * (Real.log (ρ + 2) + K) := by
      have hc1 := hcount ρ hρ2
      have hc2 : (∑ᶠ u : ℂ, ((m ρ u : ℤ) : ℝ)) = ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Function.mem_support] at hu
        exact (hSρ_mem u).mpr (fun hz => hu (by simp [hz]))
      rwa [hc2] at hc1
    have hEq_val : ∀ u ∈ Tj j, m ρ u = m R' u := by
      intro u huTj
      have hmem := Finset.mem_filter.mp huTj
      have huS : u ∈ S := hmem.1
      have huρ : ‖u‖ ≤ ρ := hmem.2.2
      have hm' : m R' u ≠ 0 := (hS_mem u).mp huS
      have huB : u ∈ closedBall 0 R' :=
        (MeromorphicOn.divisor Λ (closedBall 0 R')).supportWithinDomain hm'
      have huR' : ‖u‖ ≤ R' := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
      dsimp only [m]
      exact Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le hΛmer huρ huR'
    have hsub : Tj j ⊆ Sρ := by
      intro u huTj
      have hmem := Finset.mem_filter.mp huTj
      have huρ : ‖u‖ ≤ ρ := hmem.2.2
      have hm' : m R' u ≠ 0 := (hS_mem u).mp hmem.1
      have hmρ : m ρ u ≠ 0 := by rw [hEq_val u huTj]; exact hm'
      exact (hSρ_mem u).mpr hmρ
    calc b j = ∑ u ∈ Tj j, ((m R' u : ℤ) : ℝ) := rfl
      _ = ∑ u ∈ Tj j, ((m ρ u : ℤ) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro u huTj
          rw [hEq_val u huTj]
      _ ≤ ∑ u ∈ Sρ, ((m ρ u : ℤ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by exact_mod_cast hdivnn ρ u)
      _ ≤ c * ρ * (Real.log (ρ + 2) + K) := hcountρ
      _ = c * (2 : ℝ) ^ (j + 1) * R * (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + K) := by
          dsimp only [ρ]; ring
  -- truncating the dyadic sequence at the level of `R'` and applying the dyadic tail estimate
  let btr : ℕ → ℝ := fun j => if j ≤ K₀ then b j else 0
  have hb0tr : ∀ j : ℕ, 0 ≤ btr j := by
    intro j
    by_cases hj : j ≤ K₀
    · simp only [btr, hj, ↓reduceIte]; exact hb0 j
    · simp only [btr, hj, ↓reduceIte]; exact le_refl 0
  have hb_le_tr : ∀ j : ℕ, btr j ≤ c * (2 : ℝ) ^ (j + 1) * R *
      (Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + K) := by
    intro j
    by_cases hj : j ≤ K₀
    · simp only [btr, hj, ↓reduceIte]; exact hb_le j
    · simp only [btr, hj, ↓reduceIte]
      have hlog : 0 ≤ Real.log ((2 : ℝ) ^ (j + 1) * R + 2) :=
        Real.log_nonneg (by
          have := pow_pos (by norm_num : (0 : ℝ) < 2) (j + 1)
          nlinarith)
      have h1 : 0 ≤ c * (2 : ℝ) ^ (j + 1) * R := by
        have h2 : 0 ≤ (2 : ℝ) ^ (j + 1) := by positivity
        have h3 : 0 ≤ R := by linarith
        positivity
      have h2 : 0 ≤ Real.log ((2 : ℝ) ^ (j + 1) * R + 2) + K := by linarith
      exact mul_nonneg h1 h2
  have htsum_le : (∑' j : ℕ, btr j * (M / ((4 : ℝ) ^ j * R ^ 2))) ≤
      64 * c * M * (Real.log (R + 2) + K + 1) / R :=
    Commons.Analysis.Asymptotics.dyadicAnnulusTail (C := c) (R := R) (M := M) (L := K)
      hc hR hM hK btr hb0tr hb_le_tr
  -- assemble
  have hdybnd : (∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / ‖u‖ ^ 2))) ≤
      64 * c * M * (Real.log (R + 2) + K + 1) / R := by
    calc (∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / ‖u‖ ^ 2)))
        ≤ ∑ u ∈ T, (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ (jl u)) * R ^ 2))) :=
          Finset.sum_le_sum (fun u hu => hw1 u hu)
      _ = ∑ j ∈ Finset.range (K₀ + 1),
            ∑ u ∈ T.filter (fun u => jl u = j), (((m R' u : ℤ) : ℝ) * (M / (((4 : ℝ) ^ j) * R ^ 2))) := hpart
      _ = ∑ j ∈ Finset.range (K₀ + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) *
            (∑ u ∈ T.filter (fun u => jl u = j), ((m R' u : ℤ) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro u _
          ring
      _ ≤ ∑ j ∈ Finset.range (K₀ + 1), (M / (((4 : ℝ) ^ j) * R ^ 2)) * b j := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact mul_le_mul_of_nonneg_left (hfib_b j) (hweight j)
      _ = ∑ j ∈ Finset.range (K₀ + 1), b j * (M / (((4 : ℝ) ^ j) * R ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
      _ = ∑ j ∈ Finset.range (K₀ + 1), btr j * (M / (((4 : ℝ) ^ j) * R ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjle : j ≤ K₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          simp only [btr, hjle, ↓reduceIte]
      _ = ∑' j : ℕ, btr j * (M / ((4 : ℝ) ^ j * R ^ 2)) := by
          refine (tsum_eq_sum ?_).symm
          intro j hj
          have hjle : ¬ (j ≤ K₀) := by
            intro h
            exact hj (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
          simp only [btr, hjle, ↓reduceIte, zero_mul]
      _ ≤ 64 * c * M * (Real.log (R + 2) + K + 1) / R := htsum_le
  exact le_trans hbnd hdybnd

/-- **Convergence of the Hadamard partial sums.**  If the divisor sum of an entire `Λ` is bounded by
`c·R·(log (R+2) + K)`, then for all `s, s₁` the partial sums
`Σ_{|u| ≤ R} ord(u)·(1/(s-u) − 1/(s₁-u))` converge as `R → ∞`. -/
theorem pfConv (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hcount : ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)) ≤
        c * R * (Real.log (R + 2) + K))
    (s s₁ : ℂ) :
    ∃ L : ℂ, Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop (nhds L) := by
  classical
  set w : ℂ → ℂ := fun u => 1 / (s - u) - 1 / (s₁ - u) with hw
  set F : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u) with hF
  set Rthr : ℝ := max 2 (2 * max ‖s‖ ‖s₁‖) with hRthr
  -- the divisor count, normalised to radii `ρ ≥ 2`
  have hcount2 : ∀ ρ : ℝ, 2 ≤ ρ →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 ρ)) u : ℝ)) ≤
        c * ρ * (Real.log (ρ + 2) + K) :=
    fun ρ hρ => hcount ρ (by linarith)
  -- the kernel-bound hypothesis of `pfHadamardTail`
  have hwbd : ∀ T : ℝ, 2 ≤ T → 2 * max ‖s‖ ‖s₁‖ ≤ T → ∀ u : ℂ, T ≤ ‖u‖ →
      ‖w u‖ ≤ (4 * ‖s - s₁‖) / ‖u‖ ^ 2 := by
    intro T hT2 hT u hTu
    have hu0 : 0 < ‖u‖ := by linarith
    simpa [w] using pfKernelBound hu0 (le_trans hT hTu)
  -- the vanishing tail bound
  have hbnd_all : ∀ T T' : ℝ, Rthr ≤ T → T ≤ T' → ‖F T' - F T‖ ≤
      64 * c * (4 * ‖s - s₁‖) * (Real.log (T + 2) + K + 1) / T := by
    intro T T' hT hTT'
    have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hT
    have hTs : 2 * max ‖s‖ ‖s₁‖ ≤ T := le_trans (le_max_right _ _) hT
    have htail := pfHadamardTail Λ hDiff K c (4 * ‖s - s₁‖) hK hc (by positivity) T T' hT2 hTT'
      hcount2 w (hwbd T hT2 hTs)
    simpa [F] using htail
  -- the comparison sequence tends to zero
  have hg : Filter.Tendsto (fun R : ℝ => 64 * c * (4 * ‖s - s₁‖) *
      (Real.log (R + 2) + K + 1) / R) Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun R : ℝ => (Real.log (R + 2) + (K + 1)) / R)
        Filter.atTop (nhds 0) :=
      Commons.NumberTheory.Linnik.log_add_two_add_const_div_self_tendsto_zero (K + 1)
    have hmul : Filter.Tendsto (fun R : ℝ => (64 * c * (4 * ‖s - s₁‖)) *
        ((Real.log (R + 2) + (K + 1)) / R)) Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := 64 * c * (4 * ‖s - s₁‖))).mul hbase
    refine hmul.congr' ?_
    filter_upwards with R
    ring
  -- Cauchy criterion for the partial sums
  have hcauchy : ∀ ε > 0, ∃ R₀ : ℝ, ∀ R R' : ℝ, R₀ ≤ R → R₀ ≤ R' → ‖F R - F R'‖ < ε := by
    intro ε hε
    have hsmall : ∀ᶠ R : ℝ in Filter.atTop,
        64 * c * (4 * ‖s - s₁‖) * (Real.log (R + 2) + K + 1) / R < ε :=
      hg.eventually (Iio_mem_nhds hε)
    rcases Filter.eventually_atTop.mp hsmall with ⟨R₁, hR₁⟩
    refine ⟨max R₁ Rthr, ?_⟩
    intro R R' hR hR'
    have hRthr_R : Rthr ≤ R := le_trans (le_max_right _ _) hR
    have hRthr_R' : Rthr ≤ R' := le_trans (le_max_right _ _) hR'
    have hR₁_R : 64 * c * (4 * ‖s - s₁‖) * (Real.log (R + 2) + K + 1) / R < ε :=
      hR₁ R (le_trans (le_max_left _ _) hR)
    have hR₁_R' : 64 * c * (4 * ‖s - s₁‖) * (Real.log (R' + 2) + K + 1) / R' < ε :=
      hR₁ R' (le_trans (le_max_left _ _) hR')
    by_cases hle : R ≤ R'
    · rw [norm_sub_rev]
      exact lt_of_le_of_lt (hbnd_all R R' hRthr_R hle) hR₁_R
    · have hle' : R' ≤ R := le_of_not_ge hle
      exact lt_of_le_of_lt (hbnd_all R' R hRthr_R' hle') hR₁_R'
  have hFcauchy : Cauchy (Filter.map F Filter.atTop) := by
    rw [cauchy_map_iff]
    constructor
    · exact Filter.atTop_neBot
    · rw [Metric.uniformity_basis_dist.tendsto_right_iff]
      intro ε hε
      rcases hcauchy ε hε with ⟨R₀, hR₀⟩
      rw [Filter.eventually_prod_iff]
      refine ⟨(fun R : ℝ => R₀ ≤ R), ?_, (fun R : ℝ => R₀ ≤ R), ?_, ?_⟩
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · intro R hR R' hR'
        simpa [dist_eq_norm] using hR₀ R R' hR hR'
  rcases (cauchy_map_iff_exists_tendsto (l := Filter.atTop) (f := F)).mp hFcauchy with ⟨L, hL⟩
  exact ⟨L, by simpa [F, w] using hL⟩

end

end Work.FIArea5.HeckeZFR.Hadm
