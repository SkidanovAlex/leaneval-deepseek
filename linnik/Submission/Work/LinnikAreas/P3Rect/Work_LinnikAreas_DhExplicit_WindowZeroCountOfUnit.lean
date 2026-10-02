import Mathlib

namespace Work.LinnikAreas.DhExplicit

/-- Covering of the window `|Im u − t| ≤ h` by unit windows. -/
lemma window_cover_index {x t h : ℝ} (hx : |x - t| ≤ h) :
    (∃ j : ℕ, (j:ℝ) ≤ h/2 + 1 ∧ |x - (t + 2*(j:ℝ))| ≤ 1) ∨
    (∃ j : ℕ, (j:ℝ) ≤ h/2 + 1 ∧ |x - (t - 2*(j:ℝ))| ≤ 1) := by
  have hle : x - t ≤ h := (abs_le.mp hx).2
  have hge : -h ≤ x - t := (abs_le.mp hx).1
  by_cases htx : t ≤ x
  · left
    refine ⟨⌊(x - t + 1)/2⌋₊, ?_, ?_⟩
    · have hm : (0:ℝ) ≤ (x - t + 1)/2 := by linarith
      have h1 : ((⌊(x - t + 1)/2⌋₊ : ℕ) : ℝ) ≤ (x - t + 1)/2 := Nat.floor_le hm
      linarith
    · have hm : (0:ℝ) ≤ (x - t + 1)/2 := by linarith
      have h1 : ((⌊(x - t + 1)/2⌋₊ : ℕ) : ℝ) ≤ (x - t + 1)/2 := Nat.floor_le hm
      have h2 : (x - t + 1)/2 < ((⌊(x - t + 1)/2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [abs_le]; constructor <;> linarith
  · right
    push_neg at htx
    refine ⟨⌊(t - x + 1)/2⌋₊, ?_, ?_⟩
    · have hm : (0:ℝ) ≤ (t - x + 1)/2 := by linarith
      have h1 : ((⌊(t - x + 1)/2⌋₊ : ℕ) : ℝ) ≤ (t - x + 1)/2 := Nat.floor_le hm
      linarith
    · have hm : (0:ℝ) ≤ (t - x + 1)/2 := by linarith
      have h1 : ((⌊(t - x + 1)/2⌋₊ : ℕ) : ℝ) ≤ (t - x + 1)/2 := Nat.floor_le hm
      have h2 : (t - x + 1)/2 < ((⌊(t - x + 1)/2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [abs_le]; constructor <;> linarith

/-- **From unit windows to windows of height `h`.**  If the total vanishing order of a function
`f : ℂ → ℂ` over any finite set in a unit window `|Im u - t| ≤ 1` is at most
`C₀ (log (2 + |t|) + 2)` (hypothesis `hunit`), then it is at most
`C (h+1) (log (2 + |t| + h) + 2)` for every `h ≥ 1` and every finite set in the window
`|Im u - t| ≤ h`.

This is purely real combinatorics: every `x` with `|x - t| ≤ h` lies in one of the unit windows
centred at `t ± 2j` for some `j ≤ h/2 + 1`, and there are at most `h + 2` such centres on each
side.  The statements to copy are `window_cover_index` (floor argument) and
`Work.LinnikAreas.FarRepel.lamWindowZeroCount` in the read-only file
`Submission/Work/LinnikAreas/FarRepel/zeroSumInvSqBound.lean` (that module cannot be imported
because of a name clash, but both lemmas are pure real/combinatorics and can be copied verbatim,
with `completedRiemannZeta`'s unit-window bound replaced by the hypothesis `hunit` for `f`). -/
theorem WindowZeroCountOfUnit (f : ℂ → ℂ) (C0 : ℝ) (hC0 : 0 < C0)
    (hunit : ∀ t : ℝ, ∀ S : Finset ℂ, (∀ u ∈ S, |u.im - t| ≤ 1) →
      ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ) ≤ C0 * (Real.log (2 + |t|) + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t h : ℝ, 1 ≤ h → ∀ S : Finset ℂ,
      (∀ u ∈ S, |u.im - t| ≤ h) →
      ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ)
        ≤ C * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
  refine ⟨50 * C0, by positivity, ?_⟩
  intro t h hh S hS
  set m : ℕ := ⌊h/2 + 1⌋₊ + 1 with hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by
    rw [hm]
    have h1 : (1:ℕ) ≤ ⌊h/2 + 1⌋₊ + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast h1
  have hm_le : (m:ℝ) ≤ h + 2 := by
    rw [hm]
    have h1 : ((⌊h/2 + 1⌋₊ : ℕ) : ℝ) ≤ h/2 + 1 :=
      Nat.floor_le (by linarith : (0:ℝ) ≤ h/2 + 1)
    push_cast
    linarith
  have hcover : ∀ u ∈ S, (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
      + (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0)) ≥ 1 := by
    intro u hu
    have hjm : ∀ j : ℕ, (j:ℝ) ≤ h/2 + 1 → j ∈ Finset.range m := by
      intro j hj
      rw [Finset.mem_range, hm]
      have h2 : j ≤ (⌊h/2 + 1⌋₊ : ℕ) := Nat.le_floor hj
      omega
    rcases window_cover_index (hS u hu) with ⟨j, hj, hw⟩ | ⟨j, hj, hw⟩
    · have h1 : (1:ℝ) ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) := by
        have hmem : j ∈ Finset.range m := hjm j hj
        have hsub : ({j} : Finset ℕ) ⊆ Finset.range m := Finset.singleton_subset_iff.mpr hmem
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => by positivity :
            ∀ i ∈ Finset.range m, i ∉ ({j} : Finset ℕ) →
              0 ≤ (if |u.im - (t + 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0))
        have h3 : ∑ i ∈ ({j} : Finset ℕ),
            (if |u.im - (t + 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0) = 1 := by
          rw [Finset.sum_singleton, if_pos hw]
        linarith
      have h2 : 0 ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      linarith
    · have h2 : (1:ℝ) ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) := by
        have hmem : j ∈ Finset.range m := hjm j hj
        have hsub : ({j} : Finset ℕ) ⊆ Finset.range m := Finset.singleton_subset_iff.mpr hmem
        have h4 := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => by positivity :
            ∀ i ∈ Finset.range m, i ∉ ({j} : Finset ℕ) →
              0 ≤ (if |u.im - (t - 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0))
        have h5 : ∑ i ∈ ({j} : Finset ℕ),
            (if |u.im - (t - 2*(i:ℝ))| ≤ 1 then (1:ℝ) else 0) = 1 := by
          rw [Finset.sum_singleton, if_pos hw]
        linarith
      have h1 : 0 ≤ ∑ j ∈ Finset.range m,
          (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      linarith
  have hdistU : ∀ u : ℂ, ((analyticOrderNatAt f u : ℕ) : ℝ) *
        (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
      = ∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0) := by
    intro u
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    by_cases hp : |u.im - (t + 2*(j:ℝ))| ≤ 1
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have hdistD : ∀ u : ℂ, ((analyticOrderNatAt f u : ℕ) : ℝ) *
        (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
      = ∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0) := by
    intro u
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    by_cases hp : |u.im - (t - 2*(j:ℝ))| ≤ 1
    · rw [if_pos hp, if_pos hp]; ring
    · rw [if_neg hp, if_neg hp]; ring
  have hdist : ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ)
      ≤ ∑ j ∈ Finset.range m,
          (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
            then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
        + ∑ j ∈ Finset.range m,
          (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
            then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0)) := by
    have h1 : ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ)
        ≤ ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ) *
            ((∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
              + (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) := by
      apply Finset.sum_le_sum; intro u hu
      have hc := hcover u hu
      have hnn : (0:ℝ) ≤ ((analyticOrderNatAt f u : ℕ) : ℝ) := by positivity
      nlinarith
    calc ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ)
        ≤ ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ) *
            ((∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
              + (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) := h1
      _ = ∑ u ∈ S, (((analyticOrderNatAt f u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))
            + ((analyticOrderNatAt f u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) := by
          apply Finset.sum_congr rfl; intro u _; ring
      _ = (∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0)))
            + (∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ) *
              (∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1 then (1:ℝ) else 0))) :=
          Finset.sum_add_distrib
      _ = (∑ u ∈ S, ∑ j ∈ Finset.range m, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
            + (∑ u ∈ S, ∑ j ∈ Finset.range m, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0)) := by
          simp only [hdistU, hdistD]
      _ = (∑ j ∈ Finset.range m, ∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
            + (∑ j ∈ Finset.range m, ∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
              then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0)) := by
          congr 1
          · exact Finset.sum_comm
          · exact Finset.sum_comm
  have hwinU : ∀ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
        ≤ C0 * (Real.log (2 + |t + 2*(j:ℝ)|) + 2) := by
    intro j hj
    have hmem : ∀ u ∈ S.filter (fun u => |u.im - (t + 2*(j:ℝ))| ≤ 1),
        |u.im - (t + 2*(j:ℝ))| ≤ 1 := fun u hu => (Finset.mem_filter.mp hu).2
    have hb := hunit (t + 2*(j:ℝ)) (S.filter (fun u => |u.im - (t + 2*(j:ℝ))| ≤ 1)) hmem
    rw [Finset.sum_filter] at hb
    simpa using hb
  have hwinD : ∀ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
        ≤ C0 * (Real.log (2 + |t - 2*(j:ℝ)|) + 2) := by
    intro j hj
    have hmem : ∀ u ∈ S.filter (fun u => |u.im - (t - 2*(j:ℝ))| ≤ 1),
        |u.im - (t - 2*(j:ℝ))| ≤ 1 := fun u hu => (Finset.mem_filter.mp hu).2
    have hb := hunit (t - 2*(j:ℝ)) (S.filter (fun u => |u.im - (t - 2*(j:ℝ))| ≤ 1)) hmem
    rw [Finset.sum_filter] at hb
    simpa using hb
  have hlogterm : ∀ j ∈ Finset.range m,
      Real.log (2 + |t + 2*(j:ℝ)|) + 2 ≤ 2 * (Real.log (2 + |t| + h) + 2)
    ∧ Real.log (2 + |t - 2*(j:ℝ)|) + 2 ≤ 2 * (Real.log (2 + |t| + h) + 2) := by
    intro j hj
    have hjle : (j:ℝ) ≤ h/2 + 1 := by
      have hjm : j < m := Finset.mem_range.mp hj
      rw [hm] at hjm
      have h2 : j ≤ (⌊h/2 + 1⌋₊ : ℕ) := by omega
      exact le_trans (by exact_mod_cast h2 : (j:ℝ) ≤ ((⌊h/2 + 1⌋₊ : ℕ) : ℝ))
        (Nat.floor_le (by linarith : (0:ℝ) ≤ h/2 + 1))
    have h2j : 2*(j:ℝ) ≤ h + 2 := by linarith [hjle, hh]
    have hbase : (0:ℝ) < 2 + |t| + h := by linarith [abs_nonneg t]
    have h6 : 0 ≤ Real.log (2 + |t| + h) := Real.log_nonneg (by linarith [abs_nonneg t])
    have h5 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    constructor
    · have hle : |t + 2*(j:ℝ)| ≤ |t| + h + 2 := by
        calc |t + 2*(j:ℝ)| ≤ |t| + |2*(j:ℝ)| := abs_add_le _ _
          _ = |t| + 2*(j:ℝ) := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ))]; norm_num
          _ ≤ |t| + h + 2 := by linarith
      have h1 : Real.log (2 + |t + 2*(j:ℝ)|) ≤ Real.log (2 + |t| + h + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h3 : (2 + |t| + h + 2) ≤ (2 + |t| + h) * 2 := by
        linarith [abs_nonneg t, hh]
      have h4 : Real.log (2 + |t| + h + 2) ≤ Real.log (2 + |t| + h) + Real.log 2 := by
        have := Real.log_le_log (by positivity) h3
        rwa [Real.log_mul (ne_of_gt hbase) (by norm_num)] at this
      linarith
    · have hle : |t - 2*(j:ℝ)| ≤ |t| + h + 2 := by
        calc |t - 2*(j:ℝ)| ≤ |t| + |2*(j:ℝ)| := by
              have h := abs_sub_le t 0 (2*(j:ℝ))
              simpa using h
          _ = |t| + 2*(j:ℝ) := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ))]; norm_num
          _ ≤ |t| + h + 2 := by linarith
      have h1 : Real.log (2 + |t - 2*(j:ℝ)|) ≤ Real.log (2 + |t| + h + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h3 : (2 + |t| + h + 2) ≤ (2 + |t| + h) * 2 := by
        linarith [abs_nonneg t, hh]
      have h4 : Real.log (2 + |t| + h + 2) ≤ Real.log (2 + |t| + h) + Real.log 2 := by
        have := Real.log_le_log (by positivity) h3
        rwa [Real.log_mul (ne_of_gt hbase) (by norm_num)] at this
      linarith
  have hsumU : ∑ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
      ≤ (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
    calc ∑ j ∈ Finset.range m,
        (∑ u ∈ S, (if |u.im - (t + 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
        ≤ ∑ j ∈ Finset.range m, C0 * (2 * (Real.log (2 + |t| + h) + 2)) := by
          apply Finset.sum_le_sum; intro j hj
          exact le_trans (hwinU j hj)
            (mul_le_mul_of_nonneg_left (hlogterm j hj).1 (le_of_lt hC0))
      _ = (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumD : ∑ j ∈ Finset.range m,
      (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
        then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
      ≤ (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
    calc ∑ j ∈ Finset.range m,
        (∑ u ∈ S, (if |u.im - (t - 2*(j:ℝ))| ≤ 1
          then ((analyticOrderNatAt f u : ℕ) : ℝ) else 0))
        ≤ ∑ j ∈ Finset.range m, C0 * (2 * (Real.log (2 + |t| + h) + 2)) := by
          apply Finset.sum_le_sum; intro j hj
          exact le_trans (hwinD j hj)
            (mul_le_mul_of_nonneg_left (hlogterm j hj).2 (le_of_lt hC0))
      _ = (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h7 : 0 ≤ Real.log (2 + |t| + h) + 2 := by
    have : 0 ≤ Real.log (2 + |t| + h) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  calc ∑ u ∈ S, ((analyticOrderNatAt f u : ℕ) : ℝ)
      ≤ _ := hdist
    _ ≤ (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2)))
          + (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := add_le_add hsumU hsumD
    _ = 2 * (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2))) := by ring
    _ ≤ 50 * C0 * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
        have hstep1 : 2 * (m:ℝ) * (C0 * (2 * (Real.log (2 + |t| + h) + 2)))
            = 4 * C0 * (Real.log (2 + |t| + h) + 2) * (m:ℝ) := by ring
        rw [hstep1]
        have h3 : 4 * C0 * (Real.log (2 + |t| + h) + 2) * (m:ℝ)
            ≤ 4 * C0 * (Real.log (2 + |t| + h) + 2) * (h + 2) := by
          apply mul_le_mul_of_nonneg_left hm_le
          positivity
        have h4 : 4 * C0 * (Real.log (2 + |t| + h) + 2) * (h + 2)
            ≤ 50 * C0 * (h + 1) * (Real.log (2 + |t| + h) + 2) := by
          have h5 : 4 * (h + 2) ≤ 50 * (h + 1) := by linarith
          have h6 := mul_le_mul_of_nonneg_right h5 (mul_nonneg (le_of_lt hC0) h7)
          calc 4 * C0 * (Real.log (2 + |t| + h) + 2) * (h + 2)
              = (4 * (h + 2)) * (C0 * (Real.log (2 + |t| + h) + 2)) := by ring
            _ ≤ (50 * (h + 1)) * (C0 * (Real.log (2 + |t| + h) + 2)) := h6
            _ = 50 * C0 * (h + 1) * (Real.log (2 + |t| + h) + 2) := by ring
        linarith [h3, h4]

end Work.LinnikAreas.DhExplicit
