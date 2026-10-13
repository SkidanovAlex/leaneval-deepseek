import Mathlib.Topology.MetricSpace.Pseudo.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

/-- If `f` is continuous on `[0,T]`, `f 0 < M` and `f τ > M` for some `τ ∈ [0,T]`, then the first
crossing time `sInf {τ ∈ [0,T] | M < f τ}` is strictly positive and at most `T`, the value of `f`
there is exactly `M`, and `f ≤ M` on `[0, sInf …]`. -/
theorem sInf_crossing {f : ℝ → ℝ} {M T : ℝ} (hT : 0 < T) (hf : ContinuousOn f (Set.Icc 0 T))
    (h0 : f 0 < M) (hU : ∃ τ ∈ Set.Icc 0 T, M < f τ) :
    0 < sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} ∧
      sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} ≤ T ∧
      f (sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ}) = M ∧
      ∀ τ ∈ Set.Icc 0 (sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ}), f τ ≤ M := by
  set S : Set ℝ := {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} with hSdef
  have hmemS : ∀ τ, τ ∈ S ↔ τ ∈ Set.Icc 0 T ∧ M < f τ := by
    intro τ; rw [hSdef]; exact Iff.rfl
  have hne : S.Nonempty := by
    obtain ⟨τ, hτ⟩ := hU
    exact ⟨τ, (hmemS τ).mpr hτ⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => ((hmemS x).mp hx).1.1⟩
  have hge0 : 0 ≤ sInf S := le_csInf hne (fun x hx => ((hmemS x).mp hx).1.1)
  have hleT : sInf S ≤ T := by
    obtain ⟨τ, hτ⟩ := hU
    have hτS : τ ∈ S := (hmemS τ).mpr hτ
    exact (csInf_le hbdd hτS).trans hτ.1.2
  have hmem_inf : sInf S ∈ Set.Icc 0 T := ⟨hge0, hleT⟩
  -- The crossing time is strictly positive: continuity at `0` forces `f < M` nearby.
  have hpos : 0 < sInf S := by
    rcases lt_or_eq_of_le hge0 with h | h
    · exact h
    · exfalso
      have hzero : sInf S = 0 := h.symm
      have hcont0 : ContinuousWithinAt f (Set.Icc 0 T) 0 := hf 0 ⟨le_refl 0, hT.le⟩
      obtain ⟨δ, hδpos, hδ⟩ :=
        (Metric.continuousWithinAt_iff.mp hcont0) (M - f 0) (by linarith)
      obtain ⟨s, hsS, hslt⟩ :=
        exists_lt_of_csInf_lt hne (show sInf S < δ by rw [hzero]; exact hδpos)
      have hs0 : 0 ≤ s := ((hmemS s).mp hsS).1.1
      have hsIcc : s ∈ Set.Icc 0 T := ((hmemS s).mp hsS).1
      have hsM : M < f s := ((hmemS s).mp hsS).2
      have hdist : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]
        exact hslt
      have hb := hδ hsIcc hdist
      rw [Real.dist_eq, abs_lt] at hb
      linarith [hb.2, hsM]
  -- `f` at the crossing time is `≥ M`: otherwise a whole neighbourhood lies below `M`,
  -- contradicting the approximating points from `S`.
  have hf_ge : M ≤ f (sInf S) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hf (sInf S) hmem_inf)) (M - f (sInf S)) (by linarith)
    obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hne (by linarith : sInf S < sInf S + δ)
    have hsIcc : s ∈ Set.Icc 0 T := ((hmemS s).mp hsS).1
    have hsM : M < f s := ((hmemS s).mp hsS).2
    have hdist : dist s (sInf S) < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [csInf_le hbdd hsS], by linarith⟩
    have hb := hδ hsIcc hdist
    rw [Real.dist_eq, abs_lt] at hb
    linarith [hb.2, hsM]
  -- `f` at the crossing time is `≤ M`: every point below it has `f ≤ M` (by minimality of the
  -- infimum), so continuity from the left gives the bound.
  have hf_le : f (sInf S) ≤ M := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hf (sInf S) hmem_inf)) (f (sInf S) - M) (by linarith)
    set τ : ℝ := max 0 (sInf S - δ / 3) with hτdef
    have hτ0 : 0 ≤ τ := by rw [hτdef]; exact le_max_left 0 (sInf S - δ / 3)
    have hτlt : τ < sInf S := by
      rw [hτdef]
      rcases le_or_gt 0 (sInf S - δ / 3) with hcase | hcase
      · rw [max_eq_right hcase]; linarith
      · rw [max_eq_left hcase.le]; exact hpos
    have hτT : τ ≤ T := hτlt.le.trans hleT
    have hτIcc : τ ∈ Set.Icc 0 T := ⟨hτ0, hτT⟩
    have hτdist : dist τ (sInf S) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · rcases le_or_gt 0 (sInf S - δ / 3) with hcase | hcase
        · have hτeq : τ = sInf S - δ / 3 := by rw [hτdef]; exact max_eq_right hcase
          rw [hτeq]; linarith
        · have hτeq : τ = 0 := by rw [hτdef]; exact max_eq_left hcase.le
          rw [hτeq]; linarith
      · linarith [hτlt, hδpos]
    have hb := hδ hτIcc hτdist
    rw [Real.dist_eq, abs_lt] at hb
    have hτnot : τ ∉ S := notMem_of_lt_csInf hτlt hbdd
    have hfτ : f τ ≤ M := by
      by_contra hc
      push_neg at hc
      exact hτnot ((hmemS τ).mpr ⟨hτIcc, hc⟩)
    linarith [hb.1, hfτ]
  have hfM : f (sInf S) = M := le_antisymm hf_le hf_ge
  refine ⟨hpos, hleT, hfM, ?_⟩
  intro τ hτ
  rcases lt_or_eq_of_le hτ.2 with h | h
  · have hτT : τ ≤ T := h.le.trans hleT
    by_contra hc
    push_neg at hc
    exact notMem_of_lt_csInf h hbdd ((hmemS τ).mpr ⟨⟨hτ.1, hτT⟩, hc⟩)
  · rw [h]; exact hfM.le

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
