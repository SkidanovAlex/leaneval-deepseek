import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped BigOperators Topology
open Finset Filter

namespace Work.Diff.EXT

/-- **Uniform positive definiteness of a continuous family of quadratic forms.**
If the entries of a matrix-valued function `M' : X → Fin n → Fin n → ℝ` are continuous at `y₀` and
the quadratic form of `M' y₀` is positive definite, then it is *uniformly* positive definite on a
whole neighbourhood of `y₀`: there are `δ > 0` and an open `U ∋ y₀` with
`δ * ∑ i, (v i)^2 ≤ ∑ i, ∑ j, v i * v j * M' y i j` for all `y ∈ U` and all `v : Fin n → ℝ`.
-/
theorem uniform_posDef_of_continuous_v2
    {n : ℕ} {X : Type*} [TopologicalSpace X] (M' : X → Fin n → Fin n → ℝ) {y₀ : X}
    (hcont : ∀ i j, ContinuousAt (fun y => M' y i j) y₀)
    (hpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * M' y₀ i j) :
    ∃ δ > 0, ∃ U : Set X, IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, ∀ v : Fin n → ℝ, δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * M' y i j := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, Set.univ, isOpen_univ, Set.mem_univ y₀, fun y _ v => ?_⟩
    simp
  set S : Set (Fin n → ℝ) := {v | ∑ i, (v i) ^ 2 = 1} with hS
  have hSclosed : IsClosed S := by
    rw [hS]
    exact isClosed_eq (by fun_prop) continuous_const
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have h2 : (v i) ^ 2 ≤ 1 := by
      rw [hS] at hv
      rw [hv] at h1
      exact h1
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hScomp : IsCompact S := (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hSclosed, hSbdd⟩
  have hSne : S.Nonempty := by
    refine ⟨fun _ : Fin n => Real.sqrt (1 / (n : ℝ)), ?_⟩
    rw [hS]
    simp only [Set.mem_setOf_eq]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  set q : (Fin n → ℝ) → ℝ := fun v => ∑ i, ∑ j, v i * v j * M' y₀ i j with hq
  have hqcont : ContinuousOn q S := by
    rw [hq]
    fun_prop
  obtain ⟨v₁, hv₁S, hmin⟩ := hScomp.exists_isMinOn hSne hqcont
  have hv₁ne : v₁ ≠ 0 := by
    intro h
    have h2 : (∑ i, (v₁ i) ^ 2) = 0 := by
      rw [h]
      exact Finset.sum_eq_zero fun i _ => by simp
    have h3 : (∑ i, (v₁ i) ^ 2) = 1 := hv₁S
    rw [h2] at h3
    norm_num at h3
  have hδ₀pos : 0 < q v₁ := hpos v₁ hv₁ne
  set η : ℝ := q v₁ / (2 * (n : ℝ) ^ 2) with hη
  have hηpos : 0 < η := by
    rw [hη]
    positivity
  have hg : ∀ᶠ y in 𝓝 y₀, (∑ i, ∑ j, |M' y i j - M' y₀ i j|) < η := by
    have hlim : Tendsto (fun y : X => ∑ i, ∑ j, |M' y i j - M' y₀ i j|) (𝓝 y₀)
        (𝓝 (∑ _i : Fin n, ∑ _j : Fin n, (0 : ℝ))) := by
      refine tendsto_finsetSum Finset.univ fun i _ =>
        tendsto_finsetSum Finset.univ fun j _ => ?_
      have h1 : Tendsto (fun z : X => M' z i j - M' y₀ i j) (𝓝 y₀) (𝓝 0) := by
        have h2 : Tendsto (fun z : X => M' z i j) (𝓝 y₀) (𝓝 (M' y₀ i j)) := hcont i j
        have h3 : Tendsto (fun _ : X => M' y₀ i j) (𝓝 y₀) (𝓝 (M' y₀ i j)) := tendsto_const_nhds
        have h4 := h2.sub h3
        simpa using h4
      simpa using h1.abs
    simpa using hlim.eventually (isOpen_Iio.mem_nhds (by simpa using hηpos))
  set U : Set X := interior {y : X | (∑ i, ∑ j, |M' y i j - M' y₀ i j|) < η} with hU
  have hUopen : IsOpen U := by rw [hU]; exact isOpen_interior
  have hUmem : y₀ ∈ U := by
    rw [hU]
    exact mem_interior_iff_mem_nhds.mpr hg
  refine ⟨q v₁ / 2, half_pos hδ₀pos, U, hUopen, hUmem, ?_⟩
  intro y hy v
  have hUs : (∑ i, ∑ j, |M' y i j - M' y₀ i j|) < η := by
    have := interior_subset hy
    rwa [Set.mem_ofPred_eq] at this
  have hentry : ∀ i j, |M' y i j - M' y₀ i j| < η := by
    intro i j
    have hy' := hUs
    have h1 : |M' y i j - M' y₀ i j| ≤ ∑ j', |M' y i j' - M' y₀ i j'| :=
      Finset.single_le_sum (f := fun j' => |M' y i j' - M' y₀ i j'|)
        (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ j', |M' y i j' - M' y₀ i j'|) ≤ ∑ i', ∑ j', |M' y i' j' - M' y₀ i' j'| :=
      Finset.single_le_sum (f := fun i' => ∑ j', |M' y i' j' - M' y₀ i' j'|)
        (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hclose : ∀ w ∈ S, |(∑ i, ∑ j, w i * w j * M' y i j)
      - (∑ i, ∑ j, w i * w j * M' y₀ i j)| ≤ q v₁ / 2 := by
    intro w hwS
    have hw1 : ∀ i, |w i| ≤ 1 := by
      intro i
      have h1 : (w i) ^ 2 ≤ ∑ j, (w j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
      rw [hS] at hwS
      rw [hwS] at h1
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have hsplit : (∑ i, ∑ j, w i * w j * M' y i j) - (∑ i, ∑ j, w i * w j * M' y₀ i j)
        = ∑ i, ∑ j, w i * w j * (M' y i j - M' y₀ i j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    calc |∑ i, ∑ j, w i * w j * (M' y i j - M' y₀ i j)|
        ≤ ∑ i, |∑ j, w i * w j * (M' y i j - M' y₀ i j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |w i * w j * (M' y i j - M' y₀ i j)| :=
            Finset.sum_le_sum fun i _ => abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, η := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_mul]
            have h1 : |w i| ≤ 1 := hw1 i
            have h2 : |w j| ≤ 1 := hw1 j
            have h3 : |M' y i j - M' y₀ i j| ≤ η := le_of_lt (hentry i j)
            calc |w i| * |w j| * |M' y i j - M' y₀ i j| ≤ 1 * 1 * η :=
                  mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3 (abs_nonneg _)
                    (by positivity)
              _ = η := by ring
      _ = η * (n : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
      _ = q v₁ / 2 := by
            rw [hη]
            field_simp
  have hSonS : ∀ w ∈ S, q v₁ / 2 ≤ ∑ i, ∑ j, w i * w j * M' y i j := by
    intro w hwS
    have h1 : q v₁ ≤ ∑ i, ∑ j, w i * w j * M' y₀ i j := hmin hwS
    have h2 := hclose w hwS
    have h3 : (∑ i, ∑ j, w i * w j * M' y₀ i j) - q v₁ / 2
        ≤ ∑ i, ∑ j, w i * w j * M' y i j := by
      have := neg_abs_le ((∑ i, ∑ j, w i * w j * M' y i j)
        - (∑ i, ∑ j, w i * w j * M' y₀ i j))
      linarith
    linarith
  by_cases hv : v = 0
  · subst hv
    simp
  · have hsumpos : 0 < ∑ i, (v i) ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        refine hv (funext fun i => ?_)
        by_contra h2
        exact h ⟨i, h2⟩
      exact Finset.sum_pos' (fun j _ => sq_nonneg (v j))
        ⟨i, Finset.mem_univ i, by have := abs_pos.mpr hi; nlinarith [sq_abs (v i)]⟩
    set c : ℝ := Real.sqrt (∑ i, (v i) ^ 2) with hc
    have hcpos : 0 < c := Real.sqrt_pos.mpr hsumpos
    have hc2 : c ^ 2 = ∑ i, (v i) ^ 2 := Real.sq_sqrt hsumpos.le
    set w : Fin n → ℝ := fun i => v i / c with hwdef
    have hwS : w ∈ S := by
      rw [hS]
      simp only [Set.mem_setOf_eq, hwdef]
      have h1 : ∀ i, (v i / c) ^ 2 = (1 / c ^ 2) * (v i) ^ 2 := by
        intro i
        field_simp
      simp only [h1]
      rw [← Finset.mul_sum, hc2]
      field_simp
    have hscale : ∑ i, ∑ j, v i * v j * M' y i j
        = c ^ 2 * ∑ i, ∑ j, w i * w j * M' y i j := by
      simp only [hwdef]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [hscale, hc2]
    calc (q v₁ / 2) * ∑ i, (v i) ^ 2 = (∑ i, (v i) ^ 2) * (q v₁ / 2) := by ring
      _ ≤ (∑ i, (v i) ^ 2) * (∑ i, ∑ j, w i * w j * M' y i j) :=
            mul_le_mul_of_nonneg_left (hSonS w hwS) (by positivity)

end Work.Diff.EXT
