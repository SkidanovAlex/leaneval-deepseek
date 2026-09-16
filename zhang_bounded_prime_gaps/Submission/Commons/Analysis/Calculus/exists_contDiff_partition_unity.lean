import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

open Function Set Metric Filter
open scoped BigOperators Topology ContDiff

noncomputable section

/-- A standard smooth bump function on `ℝ`, equal to `1` on `[-1/2, 1/2]` and supported in
`[-1, 1]`. -/
def puBump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

@[simp] lemma puBump_rIn : puBump.rIn = (1/2 : ℝ) := rfl
@[simp] lemma puBump_rOut : puBump.rOut = (1 : ℝ) := rfl

/-- The underlying function of `puBump`. -/
def puFun : ℝ → ℝ := puBump

lemma puFun_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) puFun := puBump.contDiff

lemma puFun_nonneg (x : ℝ) : 0 ≤ puFun x := puBump.nonneg

lemma puFun_eq_one {x : ℝ} (hx : |x| ≤ 1/2) : puFun x = 1 := by
  apply puBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  simpa using hx

lemma puFun_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : puFun x = 0 := by
  apply puBump.zero_of_le_dist
  rw [Real.dist_eq]
  simpa using hx

lemma puFun_support_subset : support puFun ⊆ Set.Icc (-1) 1 := by
  have h : support puFun = Metric.ball (0 : ℝ) 1 := by
    change support (puBump : ℝ → ℝ) = Metric.ball (0 : ℝ) 1
    rw [puBump.support_eq]
    simp
  rw [h]
  intro x hx
  rw [Metric.mem_ball, Real.dist_eq] at hx
  simp only [sub_zero] at hx
  rw [abs_lt] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The translate family `x ↦ puFun (x - m)`. -/
def puW (m : ℤ) : ℝ → ℝ := fun x => puFun (x - (m : ℝ))

lemma puW_contDiff (m : ℤ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (puW m) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => x - (m : ℝ)) :=
    contDiff_id.sub contDiff_const
  exact puFun_contDiff.comp h1

lemma puW_nonneg (m : ℤ) (x : ℝ) : 0 ≤ puW m x := puFun_nonneg _

lemma puW_eq_one (m : ℤ) (x : ℝ) (h : |x - (m : ℝ)| ≤ 1/2) : puW m x = 1 :=
  puFun_eq_one h

lemma puW_eq_zero (m : ℤ) (x : ℝ) (h : 1 ≤ |x - (m : ℝ)|) : puW m x = 0 :=
  puFun_eq_zero h

lemma puW_support_subset (m : ℤ) :
    support (puW m) ⊆ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1) := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    simp only [not_le] at h
    exact hx (puW_eq_zero m x (by rw [abs_of_neg (by linarith)]; linarith))
  · by_contra h
    simp only [not_le] at h
    exact hx (puW_eq_zero m x (by rw [abs_of_pos (by linarith)]; linarith))

/-- Every real number is within `1/2` of an integer. -/
lemma exists_int_sub_le_half (x : ℝ) : ∃ m : ℤ, |x - (m : ℝ)| ≤ 1/2 := by
  refine ⟨⌊x + 1/2⌋, ?_⟩
  have h1 : ((⌊x + 1/2⌋ : ℤ) : ℝ) ≤ x + 1/2 := Int.floor_le _
  have h2 : x + 1/2 < ((⌊x + 1/2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- If `m` is outside `Icc (-N) N` (with `N : ℕ`), its real absolute value exceeds `N`. -/
lemma not_mem_Icc_int {N : ℕ} {m : ℤ} (h : m ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    (N : ℝ) < |(m : ℝ)| := by
  rw [Finset.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [not_le] at h
    have h' : (m : ℝ) < -(N : ℝ) := by
      have hcast : (m : ℝ) < ((-(N : ℤ) : ℤ) : ℝ) := by exact_mod_cast h
      simpa using hcast
    rw [abs_of_neg (by linarith)]
    linarith
  · rw [not_le] at h
    have h' : (N : ℝ) < (m : ℝ) := by
      have hcast : (((N : ℤ)) : ℝ) < (m : ℝ) := by exact_mod_cast h
      simpa using hcast
    rw [abs_of_pos (by linarith)]
    linarith

/-- Conversely, `|m| ≤ N` (in `ℝ`) places `m` in `Icc (-N) N`. -/
lemma mem_Icc_int_of_abs_le {N : ℕ} {m : ℤ} (h : |(m : ℝ)| ≤ (N : ℝ)) :
    m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  rw [Finset.mem_Icc]
  rw [abs_le] at h
  constructor
  · exact (Int.cast_le (R := ℝ)).mp (by push_cast; linarith [h.1])
  · exact (Int.cast_le (R := ℝ)).mp (by push_cast; linarith [h.2])

/-- Beyond a threshold, the translated bumps vanish at a fixed point. -/
lemma exists_bound (x : ℝ) : ∃ N : ℕ, ∀ m : ℤ, (N : ℝ) < |(m : ℝ)| → puW m x = 0 := by
  refine ⟨Nat.ceil (|x| + 1), ?_⟩
  intro m hm
  apply puW_eq_zero
  have hN : |x| + 1 ≤ (Nat.ceil (|x| + 1) : ℝ) := Nat.le_ceil _
  have htri : |(m : ℝ)| ≤ |(m : ℝ) - x| + |x| := by
    have h3 := abs_add_le ((m : ℝ) - x) x
    rwa [sub_add_cancel] at h3
  have : 1 < |x - (m : ℝ)| := by
    rw [abs_sub_comm]
    linarith
  linarith

/-- The normalizing sum. -/
def puSum : ℝ → ℝ := fun x => ∑' m : ℤ, puW m x

lemma puSum_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) puSum := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨N, hN⟩ := exists_nat_ge (|x₀| + 2)
  set T : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hT
  have heq : puSum =ᶠ[𝓝 x₀] (fun x => ∑ m ∈ T, puW m x) := by
    filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    change (∑' m : ℤ, puW m x) = ∑ m ∈ T, puW m x
    refine tsum_eq_sum (s := T) ?_
    intro m hm
    apply puW_eq_zero
    have hxle : |x| < (N : ℝ) - 1 := by
      have h2 : |x| ≤ |x₀| + |x - x₀| := by
        have h3 := abs_add_le x₀ (x - x₀)
        rwa [add_sub_cancel] at h3
      have : |x| < |x₀| + 1 := by linarith
      linarith
    have hmgt : (N : ℝ) < |(m : ℝ)| := not_mem_Icc_int hm
    have htri : |(m : ℝ)| ≤ |(m : ℝ) - x| + |x| := by
      have h3 := abs_add_le ((m : ℝ) - x) x
      rwa [sub_add_cancel] at h3
    have : 1 < |x - (m : ℝ)| := by
      rw [abs_sub_comm]
      linarith
    linarith
  exact ContDiffAt.congr_of_eventuallyEq
    ((ContDiff.sum (fun m _ => puW_contDiff m)).contDiffAt) heq

lemma puSum_pos (x : ℝ) : 0 < puSum x := by
  obtain ⟨N, hN⟩ := exists_bound x
  obtain ⟨m₀, hm₀⟩ := exists_int_sub_le_half x
  have hS : puSum x = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), puW m x :=
    tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun m hm => hN m (not_mem_Icc_int hm))
  rw [hS]
  have hmem : m₀ ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    by_contra h
    have := hN m₀ (not_mem_Icc_int h)
    rw [puW_eq_one m₀ x hm₀] at this
    exact one_ne_zero this
  have hle : puW m₀ x ≤ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), puW m x :=
    Finset.single_le_sum (fun i _ => puW_nonneg i x) hmem
  rw [puW_eq_one m₀ x hm₀] at hle
  linarith

/-- The normalized partition functions. -/
def puPsi (m : ℤ) : ℝ → ℝ := fun x => puW m x / puSum x

lemma puPsi_contDiff (m : ℤ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (puPsi m) :=
  (puW_contDiff m).div puSum_contDiff (fun x => ne_of_gt (puSum_pos x))

lemma puPsi_nonneg (m : ℤ) (x : ℝ) : 0 ≤ puPsi m x :=
  div_nonneg (puW_nonneg m x) (le_of_lt (puSum_pos x))

lemma puPsi_support_subset (m : ℤ) :
    support (puPsi m) ⊆ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1) := by
  refine subset_trans ?_ (puW_support_subset m)
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [puPsi, h])

theorem exists_contDiff_partition_unity :
    ∃ ψ : ℤ → ℝ → ℝ, (∀ m, ContDiff ℝ (↑(⊤ : ℕ∞)) (ψ m)) ∧
      (∀ m, Function.support (ψ m) ⊆ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1)) ∧
      (∀ m x, 0 ≤ ψ m x) ∧
      (∀ x, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ψ m x) = 1) := by
  refine ⟨puPsi, puPsi_contDiff, puPsi_support_subset, puPsi_nonneg, ?_⟩
  intro x
  obtain ⟨N, hN⟩ := exists_bound x
  refine ⟨N, fun n hn => ?_⟩
  have hnum : (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), puW m x) = puSum x := by
    have h1 : (∑' m : ℤ, puW m x) = ∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), puW m x := by
      refine tsum_eq_sum (s := Finset.Icc (-(n : ℤ)) (n : ℤ)) ?_
      intro m hm
      apply hN m
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have : (n : ℝ) < |(m : ℝ)| := not_mem_Icc_int hm
      linarith
    rw [← h1]
    rfl
  have hsum : (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), puPsi m x) = 1 := by
    change (∑ m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), puW m x / puSum x) = 1
    rw [← Finset.sum_div, hnum, div_self (ne_of_gt (puSum_pos x))]
  exact hsum

end

end Commons.Analysis.Calculus