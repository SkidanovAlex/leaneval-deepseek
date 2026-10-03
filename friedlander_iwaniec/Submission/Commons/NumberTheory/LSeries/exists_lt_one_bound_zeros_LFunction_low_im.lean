import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace Commons.NumberTheory.LSeries

open Filter Set Metric
open scoped Topology

/-- A complex-analytic function which does not vanish at some point has only finitely many
zeros inside any compact subset of `ℂ`. -/
theorem finite_zeroSet_of_isCompact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ}
    (hx : f x ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    ({z : ℂ | f z = 0 ∧ z ∈ K}).Finite := by
  rw [← Set.not_infinite]
  intro hInf
  obtain ⟨y, -, hacc⟩ :=
    hInf.exists_accPt_of_subset_isCompact hK fun z hz => hz.2
  rw [accPt_iff_frequently_nhdsNE] at hacc
  have hfreq : ∃ᶠ z in 𝓝[≠] y, f z = 0 := hacc.mono fun z hz => hz.1
  have hf_an : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hzero : Set.EqOn f 0 Set.univ :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero hf_an isPreconnected_univ
      (mem_univ y) hfreq
  exact hx (hzero (mem_univ x))

theorem exists_lt_one_bound_zeros_LFunction_low_im {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ M : ℝ, M < 1 ∧
      ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≤ 2 → ρ.re ≤ M := by
  set f : ℂ → ℂ := DirichletCharacter.LFunction χ with hf
  have hfdiff : Differentiable ℂ f := by
    rw [hf]; exact DirichletCharacter.differentiable_LFunction hχ
  have hf2 : f 2 ≠ 0 := by
    rw [hf]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  -- zeros with `1 / 2 ≤ re` and `|im| ≤ 2` lie in a compact set, hence are finite
  set S : Set ℂ := {ρ : ℂ | f ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ |ρ.im| ≤ 2} with hS
  have hSsub : S ⊆ Metric.closedBall (0 : ℂ) 3 := by
    intro z hz
    rw [hS] at hz
    obtain ⟨hz0, hzre, hzim⟩ := hz
    have hzre1 : z.re ≤ 1 := by
      by_contra h
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
          (le_of_lt (not_le.mp h))) (by rw [hf] at hz0; exact hz0)
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have hre : |z.re| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]; exact hzre1
    linarith
  have hSfin : S.Finite :=
    (finite_zeroSet_of_isCompact hfdiff hf2 (isCompact_closedBall (0 : ℂ) 3)).subset
      (fun z hz => ⟨(hS ▸ hz).1, hSsub hz⟩)
  let T : Finset ℝ := hSfin.toFinset.image (fun z => z.re)
  let M : ℝ := max (1 / 2) (if h : T.Nonempty then T.max' h else 0)
  refine ⟨M, ?_, ?_⟩
  · have hT1 : ∀ x ∈ T, x < 1 := by
      intro x hx
      simp only [T, Finset.mem_image, Set.Finite.mem_toFinset] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [hS] at hz
      obtain ⟨hz0, hzre, hzim⟩ := hz
      rcases lt_or_ge z.re 1 with h | h
      · exact h
      · exact absurd (by rw [hf] at hz0; exact hz0)
          (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h)
    apply max_lt
    · norm_num
    · by_cases h : T.Nonempty
      · simp only [dif_pos h]
        exact hT1 _ (Finset.max'_mem T h)
      · simp [dif_neg h]
  · intro ρ hρ hρim
    by_cases hre : (1 / 2 : ℝ) ≤ ρ.re
    · have hρS : ρ ∈ S := by
        rw [hS]
        exact ⟨hρ, hre, hρim⟩
      have hmem : ρ.re ∈ T := by
        simp only [T, Finset.mem_image, Set.Finite.mem_toFinset]
        exact ⟨ρ, hρS, rfl⟩
      have hTne : T.Nonempty := ⟨ρ.re, hmem⟩
      have hle : ρ.re ≤ T.max' hTne := Finset.le_max' T ρ.re hmem
      have hM : M = max (1 / 2) (T.max' hTne) := by
        simp only [M, dif_pos hTne]
      rw [hM]
      exact le_trans hle (le_max_right _ _)
    · have hle : (1 / 2 : ℝ) ≤ M := by
        simp only [M]
        exact le_max_left _ _
      linarith

end Commons.NumberTheory.LSeries