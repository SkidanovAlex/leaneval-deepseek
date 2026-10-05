import Mathlib
import Submission.Work.RPB.Port.Drive.curve_eq_iff

/-!
# The image of a short arc of a smooth embedded closed curve covers a neighbourhood

Let `γ : Circle → ℝ × ℝ` be a `C^∞` embedding and let `curve γ t = γ (Circle.exp t)`.  For every
`θ₀` and every `δ` with `0 < δ < π` there is `η > 0` such that every point of the curve within
distance `η` of `curve γ θ₀` is of the form `curve γ t` with `|t - θ₀| < δ`.

The proof is the elementary compactness argument: the set
`S = [θ₀ + δ, θ₀ + 2π - δ] ∪ {θ₀ - δ}` parametrises (modulo the period `2π`) exactly the points of
the curve at parameter distance `≥ δ` from `θ₀`; `curve γ '' S` is compact and avoids
`curve γ θ₀`, so a ball around `curve γ θ₀` misses it.
-/

namespace Work.RPB.Port.Drive

open scoped Manifold ContDiff

/-- An integer multiple of `2π` never lies in the closed interval `[δ, 2π - δ]` when
`0 < δ < π`. -/
private lemma two_pi_mul_int_not_mem_Icc {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) (k : ℤ) :
    ¬ (δ ≤ 2 * Real.pi * (k : ℝ) ∧ 2 * Real.pi * (k : ℝ) ≤ 2 * Real.pi - δ) := by
  rintro ⟨h1, h2⟩
  have hk0 : (0 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
  have hk1 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hk0' : 0 < k := by exact_mod_cast hk0
  have hk1' : k < 1 := by exact_mod_cast hk1
  omega

/-- No integer multiple of `2π` equals `-δ` when `0 < δ < π`. -/
private lemma two_pi_mul_int_ne_neg {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) (k : ℤ) :
    2 * Real.pi * (k : ℝ) ≠ -δ := by
  intro hk
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |2 * Real.pi * (k : ℝ)| = δ := by rw [hk, abs_neg, abs_of_pos hδ]
  rw [abs_mul, abs_of_pos h2π] at habs
  have hlt : |(k : ℝ)| < 1 := by nlinarith [habs, hδπ, Real.pi_pos]
  have hlt' : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact hlt
  have hlt'' : (|k| : ℤ) < 1 := by exact_mod_cast hlt'
  have hk0 : k = 0 := by
    have hnn : (0 : ℤ) ≤ |k| := abs_nonneg k
    have hz : (|k| : ℤ) = 0 := by omega
    exact abs_eq_zero.mp hz
  rw [hk0] at hk
  simp at hk
  linarith

theorem curve_arc_cover (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (θ₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    ∃ η > 0, ∀ c : Circle, γ c ∈ Metric.ball (Work.RPB.Port.Drive.curve γ θ₀) η →
      ∃ t : ℝ, |t - θ₀| < δ ∧ γ c = Work.RPB.Port.Drive.curve γ t := by
  have hγ' : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ := hγ
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the parameters at distance `≥ δ` from `θ₀`, reduced into one fundamental period
  set S : Set ℝ := Set.Icc (θ₀ + δ) (θ₀ + 2 * Real.pi - δ) ∪ {θ₀ - δ} with hSdef
  have hSnonempty : S.Nonempty := ⟨θ₀ + δ, Or.inl ⟨le_rfl, by linarith⟩⟩
  have hcont : Continuous (curve γ) :=
    hγ.isEmbedding.continuous.comp Circle.exp.continuous
  have hKc : IsCompact (curve γ '' S) := by
    rw [hSdef]
    exact (isCompact_Icc.union isCompact_singleton).image hcont
  have hKne : (curve γ '' S).Nonempty := hSnonempty.image _
  -- `curve γ θ₀` is not in that compact set
  have hnot : curve γ θ₀ ∉ curve γ '' S := by
    intro hmem
    rw [Set.mem_image] at hmem
    obtain ⟨s, hs, hfs⟩ := hmem
    obtain ⟨k, hk⟩ := (curve_eq_iff γ hγ' s θ₀).1 hfs
    rcases hs with hs | hs
    · rw [Set.mem_Icc] at hs
      exact two_pi_mul_int_not_mem_Icc hδ hδπ k ⟨by linarith [hs.1, hk],
        by linarith [hs.2, hk]⟩
    · rw [Set.mem_singleton_iff] at hs
      exact two_pi_mul_int_ne_neg hδ hδπ k (by linarith [hs, hk])
  refine ⟨Metric.infDist (curve γ θ₀) (curve γ '' S), ?_, ?_⟩
  · exact (hKc.isClosed.notMem_iff_infDist_pos hKne).1 hnot
  · intro c hc
    obtain ⟨s, hs⟩ := Circle.exp_surjective c
    have hcs : γ c = curve γ s := by simp [curve, hs]
    set k : ℤ := -⌊(s - (θ₀ - δ)) / (2 * Real.pi)⌋ with hkdef
    have htk : (k : ℝ) = -(⌊(s - (θ₀ - δ)) / (2 * Real.pi)⌋ : ℝ) := by
      rw [hkdef]; simp
    set t' : ℝ := s + 2 * Real.pi * (k : ℝ) with ht'def
    have hlift : t' ∈ Set.Ico (θ₀ - δ) (θ₀ + 2 * Real.pi - δ) := by
      have h1 := Int.sub_floor_div_mul_nonneg (s - (θ₀ - δ)) h2π
      have h2 := Int.sub_floor_div_mul_lt (s - (θ₀ - δ)) h2π
      rw [Set.mem_Ico, ht'def, htk]
      constructor <;> nlinarith
    have hper : curve γ s = curve γ t' := by
      rw [curve_eq_iff γ hγ' s t']
      refine ⟨-k, ?_⟩
      simp only [ht'def]
      push_cast
      ring
    have hγc : γ c = curve γ t' := hcs.trans hper
    have hbad : curve γ t' ∈ curve γ '' S → False := by
      intro hmem
      have hle := Metric.infDist_le_dist_of_mem (s := curve γ '' S)
        (x := curve γ θ₀) hmem
      rw [dist_comm] at hle
      have hlt := Metric.mem_ball.mp hc
      rw [hγc] at hlt
      linarith
    refine ⟨t', ?_, hγc⟩
    rw [abs_lt]
    constructor
    · rcases eq_or_lt_of_le hlift.1 with heq | hgt
      · exfalso
        apply hbad
        rw [← heq]
        exact ⟨θ₀ - δ, Or.inr rfl, rfl⟩
      · linarith
    · by_contra hcon
      push Not at hcon
      exfalso
      apply hbad
      exact ⟨t', Or.inl ⟨by linarith, hlift.2.le⟩, rfl⟩

end Work.RPB.Port.Drive
