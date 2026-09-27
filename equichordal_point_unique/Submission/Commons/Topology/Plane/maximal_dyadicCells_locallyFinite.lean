import Mathlib
import Submission.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex
import Submission.Commons.Topology.Plane.maxCell_mem_of_mem

namespace Commons.Topology.Plane

/-- **Level bound for maximal cells.**  Let `U` be open, `ball x δ ⊆ U` with `δ > 0`.  If a
dyadic cell `dyadicCell m p` is contained in `U` and its parent cell is not contained in `U`,
and if `dyadicCell m p` meets `ball x (δ/2)`, then the level `m` is bounded:
`m - 1 < 2 * √2 / δ`.

The parent contains a point `w ∉ U`; since `ball x δ ⊆ U`, `dist w x ≥ δ`, while the cell meeting
`ball x (δ/2)` gives a point `z` with `dist z x < δ/2`.  Both `z` and `w` lie in the parent cell,
hence `dist z w ≤ √2 · 2 ^ (-(m-1))`, and `δ ≤ dist w z + dist z x < √2·2^(-(m-1)) + δ/2`. -/
lemma level_lt_of_maximal {U : Set ℂ} {x : ℂ} {δ : ℝ} (hδpos : 0 < δ)
    (hδU : Metric.ball x δ ⊆ U) {m : ℕ} {p : ℤ × ℤ}
    (hmax : m = 0 ∨ ¬ dyadicCell (m - 1) (p.1 / 2, p.2 / 2) ⊆ U)
    (hne : (dyadicCell m p ∩ Metric.ball x (δ / 2)).Nonempty) :
    (m : ℝ) - 1 < 2 * Real.sqrt 2 / δ := by
  have hTpos : 0 < 2 * Real.sqrt 2 / δ := by positivity
  rcases eq_or_ne m 0 with hm0 | hmne
  · subst hm0; push_cast; linarith
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
    have hmax' : ¬ dyadicCell (m - 1) (p.1 / 2, p.2 / 2) ⊆ U := hmax.resolve_left hmne
    obtain ⟨z, hz⟩ := hne
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hzcell, hzball⟩ := hz
    rw [Metric.mem_ball] at hzball
    have hzpar : z ∈ dyadicCell (m - 1) (p.1 / 2, p.2 / 2) :=
      dyadicCell_subset_parent' hmpos p hzcell
    obtain ⟨w, hwpar, hwU⟩ := Set.not_subset.mp hmax'
    have hzw : dist z w ≤ Real.sqrt 2 / 2 ^ (m - 1) := dyadicCell_dist_le hzpar hwpar
    have hwx : δ ≤ dist w x := by
      by_contra h
      push_neg at h
      exact hwU (hδU (by rw [Metric.mem_ball]; exact h))
    have hdist : δ ≤ dist w z + dist z x := le_trans hwx (dist_triangle w z x)
    have hkey : δ / 2 < Real.sqrt 2 / 2 ^ (m - 1) := by
      have hcomm : dist w z = dist z w := dist_comm w z
      linarith
    have h2pos : (0:ℝ) < (2:ℝ) ^ (m - 1) := by positivity
    have hmul : (2:ℝ) ^ (m - 1) * δ < 2 * Real.sqrt 2 := by
      have h := (lt_div_iff₀ h2pos).mp hkey
      nlinarith [h]
    have hT : (2:ℝ) ^ (m - 1) < 2 * Real.sqrt 2 / δ := by
      rw [lt_div_iff₀ hδpos]; exact hmul
    have hk : ((m - 1 : ℕ) : ℝ) < (2:ℝ) ^ (m - 1) := by
      have := Nat.lt_two_pow_self (n := m - 1)
      exact_mod_cast this
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hmpos)]; push_cast; ring
    calc (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := hcast.symm
      _ < (2:ℝ) ^ (m - 1) := hk
      _ < 2 * Real.sqrt 2 / δ := hT

/-- **Index bound at a fixed level.**  If `a` is the index of a real dyadic slice of level `m`
containing the point `t`, i.e. `a/2^m ≤ t ≤ (a+1)/2^m`, and `t` is within `r` of `c`, then
`a` is bounded in terms of `c`, `r`, the level bound `M ≥ m` and the bound `B`:
`-B ≤ a ≤ B`. -/
lemma slice_index_abs_le {m M : ℕ} {a : ℤ} {t c r : ℝ} {B : ℤ}
    (hm : m ≤ M) (hr : 0 ≤ r)
    (hB : (|c| + r + 1) * (2:ℝ) ^ M ≤ (B : ℝ))
    (h1 : (a : ℝ) / (2:ℝ) ^ m ≤ t) (h2 : t ≤ ((a : ℝ) + 1) / (2:ℝ) ^ m)
    (ht : |t - c| < r) :
    -B ≤ a ∧ a ≤ B := by
  have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have h2M : (0:ℝ) < (2:ℝ) ^ M := by positivity
  have hpowle : (2:ℝ) ^ m ≤ (2:ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hm
  have ht_ub : t < c + r := by have h := (abs_lt.mp ht).2; linarith
  have ht_lb : c - r < t := by have h := (abs_lt.mp ht).1; linarith
  have hPnn : (0:ℝ) ≤ |c| + r + 1 := by have h := abs_nonneg c; linarith
  -- upper bound for `a`
  have ha_ub : (a : ℝ) < (B : ℝ) := by
    have hle1 : (a : ℝ) ≤ t * (2:ℝ) ^ m := by
      have := (div_le_iff₀ h2m).mp h1
      linarith
    have hc : c + r ≤ |c| + r + 1 := by
      have h := le_abs_self c; linarith
    have htlt : t < |c| + r + 1 := lt_of_lt_of_le ht_ub hc
    have h1' : t * (2:ℝ) ^ m < (|c| + r + 1) * (2:ℝ) ^ m :=
      mul_lt_mul_of_pos_right htlt h2m
    have h2' : (|c| + r + 1) * (2:ℝ) ^ m ≤ (|c| + r + 1) * (2:ℝ) ^ M :=
      mul_le_mul_of_nonneg_left hpowle hPnn
    linarith
  -- lower bound for `a`
  have ha_lb : -(B : ℝ) - 1 < (a : ℝ) := by
    have hge1 : t * (2:ℝ) ^ m ≤ (a : ℝ) + 1 := (le_div_iff₀ h2m).mp h2
    have hlt : (c - r) * (2:ℝ) ^ m < t * (2:ℝ) ^ m :=
      mul_lt_mul_of_pos_right ht_lb h2m
    have hcru : -((|c| + r + 1) * (2:ℝ) ^ M) ≤ (c - r) * (2:ℝ) ^ m := by
      have hstep1 : (|c| + r) * (2:ℝ) ^ M ≤ (|c| + r + 1) * (2:ℝ) ^ M := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt h2M)
        linarith
      have hstep2 : (|c| + r) * (2:ℝ) ^ m ≤ (|c| + r) * (2:ℝ) ^ M :=
        mul_le_mul_of_nonneg_left hpowle (by have h := abs_nonneg c; linarith)
      have hstep3 : -(|c| + r) ≤ c - r := by
        have := neg_abs_le c; linarith
      have hstep4 : -(|c| + r) * (2:ℝ) ^ m ≤ (c - r) * (2:ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hstep3 (le_of_lt h2m)
      linarith
    have hB' : -((|c| + r + 1) * (2:ℝ) ^ M) ≥ -(B : ℝ) := by linarith
    linarith
  refine ⟨?_, ?_⟩
  · have hreal : (((-(B) - 1 : ℤ)) : ℝ) < (a : ℝ) := by
      push_cast
      linarith [ha_lb]
    have hInt : (-(B) - 1 : ℤ) < a := Int.cast_lt.mp hreal
    omega
  · have hInt : a < B := Int.cast_lt.mp ha_ub
    omega

/-- **The family of maximal dyadic cells of an open set is locally finite.**  For `U ⊆ ℂ` open and
`x ∈ U` there is `r > 0` such that only finitely many *maximal* dyadic cells (those `dyadicCell n p`
with `dyadicCell n p ⊆ U` whose parent cell is not contained in `U`, the parent being trivial at
level `0`) meet the ball `ball x r`.

Proof: if `dyadicCell m p ⊆ U` and its parent `dyadicCell (m-1) (p.1/2, p.2/2)` is not contained in
`U`, then the parent contains a point `w` of `Uᶜ`, and `dist z w ≤ √2 · 2 ^ (-(m-1))` for every
`z ∈ dyadicCell m p`.  Hence a maximal cell meeting `ball x (δ/2)`, where `δ > 0` with
`ball x δ ⊆ U`, must satisfy `√2 · 2 ^ (-(m-1)) ≥ δ/2`, so its level `m` is bounded by an explicit
function of `δ`; and at each fixed level `m` the cells meeting a bounded ball have indices in a
bounded box (since `p.1 / 2 ^ m ≤ z.re ≤ (p.1 + 1) / 2 ^ m` for a point `z` of the cell). -/
theorem maximal_dyadicCells_locallyFinite (U : Set ℂ) (hU : IsOpen U) :
    ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧
      {q : ℕ × (ℤ × ℤ) | dyadicCell q.1 q.2 ⊆ U ∧
        (q.1 = 0 ∨ ¬ dyadicCell (q.1 - 1) (q.2.1 / 2, q.2.2 / 2) ⊆ U) ∧
        (dyadicCell q.1 q.2 ∩ Metric.ball x r).Nonempty}.Finite := by
  intro x hx
  obtain ⟨δ, hδpos, hδU⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨δ / 2, by positivity, ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * Real.sqrt 2 / δ)
  let B : ℤ := ⌊(|x.re| + |x.im| + δ / 2 + 1) * (2:ℝ) ^ M⌋ + 1
  let S : Finset (ℕ × (ℤ × ℤ)) :=
    (Finset.range (M + 1)) ×ˢ (Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B)
  refine Set.Finite.subset S.finite_toSet ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨hqcell, hqmax, hqne⟩ := hq
  have hlev : (q.1 : ℝ) - 1 < 2 * Real.sqrt 2 / δ :=
    level_lt_of_maximal hδpos hδU hqmax hqne
  have hm_le : q.1 ≤ M := by
    have hlt : (q.1 : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hlt' : q.1 < M + 1 := by exact_mod_cast hlt
    omega
  have hB_re : (|x.re| + δ / 2 + 1) * (2:ℝ) ^ M ≤ (B : ℝ) := by
    have hle : |x.re| + δ / 2 + 1 ≤ |x.re| + |x.im| + δ / 2 + 1 := by
      have : (0:ℝ) ≤ |x.im| := abs_nonneg _
      linarith
    have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ (2:ℝ) ^ M)
    have hfl : (|x.re| + |x.im| + δ / 2 + 1) * (2:ℝ) ^ M <
        ((⌊(|x.re| + |x.im| + δ / 2 + 1) * (2:ℝ) ^ M⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    simp only [B]; push_cast; linarith
  have hB_im : (|x.im| + δ / 2 + 1) * (2:ℝ) ^ M ≤ (B : ℝ) := by
    have hle : |x.im| + δ / 2 + 1 ≤ |x.re| + |x.im| + δ / 2 + 1 := by
      have : (0:ℝ) ≤ |x.re| := abs_nonneg _
      linarith
    have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ (2:ℝ) ^ M)
    have hfl : (|x.re| + |x.im| + δ / 2 + 1) * (2:ℝ) ^ M <
        ((⌊(|x.re| + |x.im| + δ / 2 + 1) * (2:ℝ) ^ M⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    simp only [B]; push_cast; linarith
  obtain ⟨z, hzmem⟩ := hqne
  rw [Set.mem_inter_iff] at hzmem
  obtain ⟨hzcell, hzball⟩ := hzmem
  rw [Metric.mem_ball] at hzball
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hzcell
  have hre_lt : |z.re - x.re| < δ / 2 := by
    have h := Complex.abs_re_le_norm (z - x)
    rw [Complex.sub_re] at h
    have hd : ‖z - x‖ = dist z x := (dist_eq_norm z x).symm
    rw [hd] at h
    linarith
  have him_lt : |z.im - x.im| < δ / 2 := by
    have h := Complex.abs_im_le_norm (z - x)
    rw [Complex.sub_im] at h
    have hd : ‖z - x‖ = dist z x := (dist_eq_norm z x).symm
    rw [hd] at h
    linarith
  have hre := slice_index_abs_le (r := δ / 2) hm_le (by positivity) hB_re hz1 hz2 hre_lt
  have him := slice_index_abs_le (r := δ / 2) hm_le (by positivity) hB_im hz3 hz4 him_lt
  rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨by omega, ⟨⟨hre.1, hre.2⟩, ⟨him.1, him.2⟩⟩⟩

end Commons.Topology.Plane
