import Submission.Metric

/-! Endpoint limits of locally linear paths in a complete space. -/

open scoped ENNReal
open Set Filter Topology

namespace Submission
namespace Metric
namespace IsLocLinear

variable {M : Type*} [PseudoEMetricSpace M]

/-- A uniform two-point estimate on the locally linear path near `b⁻`: for every
`ε` there is a member `U` of `𝓝[Iio b] b` (inside `(a,b)`) on which all
`edist (γ s) (γ t) < ε`. -/
private lemma exists_uniform_mem_nhdsWithin_Iio {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) (hab : a < b) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ U ∈ 𝓝[Iio b] b,
      U ⊆ Ioo a b ∧ ∀ ⦃s t : ℝ⦄, s ∈ U → t ∈ U → edist (γ s) (γ t) < ε := by
  intro ε hε
  rcases exists_lt_of_mul_ofReal hε c with ⟨δ, hδpos, hδ⟩
  let δ' : ℝ := min δ ((b - a) / 2)
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'leδ : δ' ≤ δ := min_le_left δ ((b - a) / 2)
  have hδ'ltba : δ' < b - a := by
    have h2 : (b - a) / 2 < b - a := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2)]
      nlinarith [sub_pos.mpr hab]
    exact lt_of_le_of_lt (min_le_right δ ((b - a) / 2)) h2
  let U : Set ℝ := Ioo (b - δ') b
  have hU_sub : U ⊆ Ioo a b := by
    intro x hx
    simp only [U, mem_Ioo] at hx ⊢
    constructor
    · exact lt_trans (by linarith) hx.1
    · exact hx.2
  refine ⟨U, ?_mem, hU_sub, ?_pair⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioo (b - δ') (b + δ'), ?_, ?_⟩
    · exact Ioo_mem_nhds (by linarith) (by linarith)
    · intro x hx
      simp only [mem_inter_iff, mem_Iio, mem_Ioo] at hx ⊢
      constructor
      · exact hx.1.1
      · exact hx.2
  · intro s t hs ht
    have hs' : s ∈ Ioo (b - δ') b := by simpa [U] using hs
    have ht' : t ∈ Ioo (b - δ') b := by simpa [U] using ht
    have h_abs : |t - s| < δ := by
      exact abs_lt.mpr ⟨by linarith [ht'.1, hs'.2, hδ'leδ], by linarith [ht'.2, hs'.1, hδ'leδ]⟩
    have hle := edist_le hγ (hU_sub hs) (hU_sub ht)
    exact lt_of_le_of_lt hle (hδ |t - s| (abs_nonneg (t - s)) h_abs)

/-- A uniform two-point estimate on the locally linear path near `a⁺`: for every
`ε` there is a member `U` of `𝓝[Ioi a] a` (inside `(a,b)`) on which all
`edist (γ s) (γ t) < ε`. -/
private lemma exists_uniform_mem_nhdsWithin_Ioi {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) (hab : a < b) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ U ∈ 𝓝[Ioi a] a,
      U ⊆ Ioo a b ∧ ∀ ⦃s t : ℝ⦄, s ∈ U → t ∈ U → edist (γ s) (γ t) < ε := by
  intro ε hε
  rcases exists_lt_of_mul_ofReal hε c with ⟨δ, hδpos, hδ⟩
  let δ' : ℝ := min δ ((b - a) / 2)
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'leδ : δ' ≤ δ := min_le_left δ ((b - a) / 2)
  have hδ'ltba : δ' < b - a := by
    have h2 : (b - a) / 2 < b - a := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2)]
      nlinarith [sub_pos.mpr hab]
    exact lt_of_le_of_lt (min_le_right δ ((b - a) / 2)) h2
  let U : Set ℝ := Ioo a (a + δ')
  have hU_sub : U ⊆ Ioo a b := by
    intro x hx
    simp only [U, mem_Ioo] at hx ⊢
    constructor
    · exact hx.1
    · exact lt_trans hx.2 (by linarith)
  refine ⟨U, ?_mem, hU_sub, ?_pair⟩
  · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioo (a - δ') (a + δ'), ?_, ?_⟩
    · exact Ioo_mem_nhds (by linarith) (by linarith)
    · intro x hx
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo] at hx ⊢
      constructor
      · exact hx.2
      · exact hx.1.2
  · intro s t hs ht
    have hs' : s ∈ Ioo a (a + δ') := by simpa [U] using hs
    have ht' : t ∈ Ioo a (a + δ') := by simpa [U] using ht
    have h_abs : |t - s| < δ := by
      exact abs_lt.mpr ⟨by linarith [ht'.1, hs'.2, hδ'leδ], by linarith [ht'.2, hs'.1, hδ'leδ]⟩
    have hle := edist_le hγ (hU_sub hs) (hU_sub ht)
    exact lt_of_le_of_lt hle (hδ |t - s| (abs_nonneg (t - s)) h_abs)

variable {M : Type*} [EMetricSpace M] [CompleteSpace M]

/-- In a complete space, a locally linear path on `(a,b)` has a limit at `b⁻`. -/
lemma exists_tendsto_nhdsWithin_Iio {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) (hab : a < b) :
    ∃ p : M, Tendsto γ (𝓝[Iio b] b) (𝓝 p) := by
  let F : Filter ℝ := 𝓝[Iio b] b
  have hF_neBot : NeBot F := by
    dsimp [F]
    exact nhdsLT_neBot_of_exists_lt (α := ℝ) ⟨a, hab⟩
  have hCauchy : Cauchy (F.map γ) := by
    rw [EMetric.cauchy_iff]
    constructor
    · exact neBot_iff.mp ((map_neBot_iff γ).mpr hF_neBot)
    · intro ε hε
      rcases exists_uniform_mem_nhdsWithin_Iio (M := M) hγ hab ε hε with ⟨U, hU, hU_sub, h_pair⟩
      refine ⟨γ '' U, ?_, ?_⟩
      · rw [Filter.mem_map]
        exact mem_of_superset hU (subset_preimage_image γ U)
      · intro x hx y hy
        rcases hx with ⟨s, hs, rfl⟩
        rcases hy with ⟨t, ht, rfl⟩
        exact h_pair hs ht
  rcases CompleteSpace.complete hCauchy with ⟨p, hp⟩
  exact ⟨p, hp⟩

/-- In a complete space, a locally linear path on `(a,b)` has a limit at `a⁺`. -/
lemma exists_tendsto_nhdsWithin_Ioi {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) (hab : a < b) :
    ∃ p : M, Tendsto γ (𝓝[Ioi a] a) (𝓝 p) := by
  let F : Filter ℝ := 𝓝[Ioi a] a
  have hF_neBot : NeBot F := by
    dsimp [F]
    exact nhdsGT_neBot_of_exists_gt (α := ℝ) ⟨b, hab⟩
  have hCauchy : Cauchy (F.map γ) := by
    rw [EMetric.cauchy_iff]
    constructor
    · exact neBot_iff.mp ((map_neBot_iff γ).mpr hF_neBot)
    · intro ε hε
      rcases exists_uniform_mem_nhdsWithin_Ioi (M := M) hγ hab ε hε with ⟨U, hU, hU_sub, h_pair⟩
      refine ⟨γ '' U, ?_, ?_⟩
      · rw [Filter.mem_map]
        exact mem_of_superset hU (subset_preimage_image γ U)
      · intro x hx y hy
        rcases hx with ⟨s, hs, rfl⟩
        rcases hy with ⟨t, ht, rfl⟩
        exact h_pair hs ht
  rcases CompleteSpace.complete hCauchy with ⟨p, hp⟩
  exact ⟨p, hp⟩

end IsLocLinear
end Metric
end Submission
