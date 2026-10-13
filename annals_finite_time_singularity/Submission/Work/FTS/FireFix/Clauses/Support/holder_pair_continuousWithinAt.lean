import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses.Support

/-- For `0 < c` and any real constant `C`, the quantity `|C| * δ ^ c` can be made smaller
than any prescribed positive `e` by choosing `δ > 0` small enough. -/
private lemma exists_abs_mul_rpow_lt (C : ℝ) {c : ℝ} (hc : 0 < c) {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ |C| * δ ^ c < e := by
  have hcont : Continuous fun δ : ℝ => |C| * δ ^ c :=
    continuous_const.mul (Real.continuous_rpow_const hc.le)
  have htend : Filter.Tendsto (fun δ : ℝ => |C| * δ ^ c) (nhds 0) (nhds 0) := by
    have h0 : |C| * (0 : ℝ) ^ c = 0 := by
      simp [Real.zero_rpow hc.ne']
    have h := hcont.continuousAt (x := 0)
    rwa [ContinuousAt, h0] at h
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    Metric.eventually_nhds_iff.mp ((Metric.tendsto_nhds.mp htend) e he)
  refine ⟨δ₀ / 2, half_pos hδ₀pos, ?_⟩
  have h2 : (0 : ℝ) ≤ δ₀ / 2 := by linarith
  have hmem : dist (δ₀ / 2) (0 : ℝ) < δ₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]; linarith
  have h := hδ₀ hmem
  rwa [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg h2 c))] at h

theorem holder_pair_continuousWithinAt {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E × ℝ → F} {C N c a S : ℝ} {x₀ : E} {t₀ : ℝ}
    (hc : 0 < c) (ha : 0 < a) (ht₀ : 0 ≤ t₀) (hS : t₀ < S)
    (hx : ∀ x x' t, t ∈ Set.Icc (0 : ℝ) S → dist (f (x, t)) (f (x', t)) ≤ C * ‖x - x'‖ ^ c)
    (ht : ∀ x t t', t ∈ Set.Icc (0 : ℝ) S → t' ∈ Set.Icc (0 : ℝ) S →
        dist (f (x, t)) (f (x, t')) ≤ N * |t - t'| ^ a) :
    ContinuousWithinAt f (Set.univ ×ˢ Set.Ici (0 : ℝ)) (x₀, t₀) := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hCsmall⟩ := exists_abs_mul_rpow_lt C hc (half_pos hε)
  obtain ⟨δ₂, hδ₂pos, hNsmall⟩ := exists_abs_mul_rpow_lt N ha (half_pos hε)
  set δ : ℝ := min ((S - t₀) / 2) (min δ₁ δ₂) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (lt_min hδ₁pos hδ₂pos)
  have hδS : δ ≤ (S - t₀) / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδle₁ : δ ≤ δ₁ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδpos, ?_⟩
  rintro ⟨x, t⟩ hy hdy
  rw [Set.mem_prod] at hy
  obtain ⟨-, ht0⟩ := hy
  -- `0 ≤ t`
  have ht0' : (0 : ℝ) ≤ t := Set.mem_Ici.mp ht0
  have hdx : dist x x₀ ≤ dist ((x, t) : E × ℝ) (x₀, t₀) := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hdt : dist t t₀ ≤ dist ((x, t) : E × ℝ) (x₀, t₀) := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  -- `t` stays below `S`
  have htS : t < S := by
    have h1 : t - t₀ ≤ dist t t₀ := by rw [Real.dist_eq]; exact le_abs_self _
    have h2 : dist t t₀ < δ := lt_of_le_of_lt hdt hdy
    linarith
  have htI : t ∈ Set.Icc (0 : ℝ) S := ⟨ht0', le_of_lt htS⟩
  have ht₀I : t₀ ∈ Set.Icc (0 : ℝ) S := ⟨ht₀, le_of_lt hS⟩
  -- the two Hölder bounds combine
  have key : dist (f (x, t)) (f (x₀, t₀))
      ≤ |C| * (dist x x₀) ^ c + |N| * (dist t t₀) ^ a := by
    calc dist (f (x, t)) (f (x₀, t₀))
        ≤ dist (f (x, t)) (f (x₀, t)) + dist (f (x₀, t)) (f (x₀, t₀)) :=
          dist_triangle _ _ _
      _ ≤ C * ‖x - x₀‖ ^ c + N * |t - t₀| ^ a :=
          add_le_add (hx x x₀ t htI) (ht x₀ t t₀ htI ht₀I)
      _ ≤ |C| * (dist x x₀) ^ c + |N| * (dist t t₀) ^ a := by
          have h1 : C * ‖x - x₀‖ ^ c ≤ |C| * (dist x x₀) ^ c := by
            rw [dist_eq_norm]
            exact mul_le_mul_of_nonneg_right (le_abs_self C)
              (Real.rpow_nonneg (norm_nonneg (x - x₀)) c)
          have h2 : N * |t - t₀| ^ a ≤ |N| * (dist t t₀) ^ a := by
            rw [Real.dist_eq]
            exact mul_le_mul_of_nonneg_right (le_abs_self N)
              (Real.rpow_nonneg (abs_nonneg (t - t₀)) a)
          linarith
  have hxC : |C| * (dist x x₀) ^ c < ε / 2 := by
    have hle : dist x x₀ ≤ δ₁ := le_trans hdx (le_trans (le_of_lt hdy) hδle₁)
    have hdc : (dist x x₀) ^ c ≤ δ₁ ^ c :=
      Real.rpow_le_rpow dist_nonneg hle hc.le
    calc |C| * (dist x x₀) ^ c ≤ |C| * δ₁ ^ c :=
          mul_le_mul_of_nonneg_left hdc (abs_nonneg C)
      _ < ε / 2 := hCsmall
  have htN : |N| * (dist t t₀) ^ a < ε / 2 := by
    have hle : dist t t₀ ≤ δ₂ := le_trans hdt (le_trans (le_of_lt hdy) hδle₂)
    have hda : (dist t t₀) ^ a ≤ δ₂ ^ a :=
      Real.rpow_le_rpow dist_nonneg hle ha.le
    calc |N| * (dist t t₀) ^ a ≤ |N| * δ₂ ^ a :=
          mul_le_mul_of_nonneg_left hda (abs_nonneg N)
      _ < ε / 2 := hNsmall
  calc dist (f (x, t)) (f (x₀, t₀))
      ≤ |C| * (dist x x₀) ^ c + |N| * (dist t t₀) ^ a := key
    _ < ε / 2 + ε / 2 := add_lt_add hxC htN
    _ = ε := by ring

end Work.FTS.FireFix.Clauses.Support
