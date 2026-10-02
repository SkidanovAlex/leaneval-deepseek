import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The preimage of a preconnected set under `z ↦ z²` is preconnected

If `S ⊆ ℂ` is preconnected and contains `0`, then `{z : ℂ | z ^ 2 ∈ S}` is preconnected.

An elementary proof: let `T := {z | z² ∈ S}` and suppose `U`, `V` are open with
`T ⊆ U ∪ V`, `T ∩ U ∩ V = ∅`; exchanging `U` and `V` if necessary we may assume `0 ∈ U`
(here `0 ∈ T` because `0² = 0 ∈ S`).  Assume for a contradiction that some `z₀ ∈ T` lies
outside `U`; then `z₀ ∈ V`, and we consider

* `B := T ∩ V`, a relatively clopen piece of `T` containing `z₀` and disjoint from `U`,
* `R := {w : ℂ | ∃ z ∈ B, z ^ 2 = w}`, the image of `B` under squaring.

Then `R ⊆ S \ {0}` and:

* `R` is *open in `S`*: if `w = z²` with `z ∈ B`, then `ball z ρ ⊆ V` for some `ρ > 0`,
  and every `w' ∈ S` with `‖w' - w‖ < ρ²` has a square root `z'` with `‖z' ∓ z‖ < ρ` for
  a suitable sign; that root lies in `ball z ρ ⊆ V` (and `z'² = w' ∈ S`), so `z' ∈ B` and
  `w' ∈ R`.
* If `0 ∉ closure R` then `S \ R` is *open in `S`*: if `w ∈ S \ R` and `w ≠ 0` then both
  square roots `±z` of `w` lie in `T \ B ⊆ U`; any `w' ∈ S` close to `w` has square roots
  close to `±z`, hence both in `U`, so `w' ∉ R` — a square root of `w'` in `B` would be a
  point of `B ∩ U = ∅`.  For `w = 0` this is the very meaning of `0 ∉ closure R`.

Writing `R = S ∩ O` and `S \ R = S ∩ O'` with `O`, `O'` open, preconnectedness of `S`
gives `S ⊆ O` or `S ⊆ O'`.  In the first case `R = S ∋ 0`, contradicting `0 ∉ R`; in the
second `S \ R = S`, so `R = ∅`, contradicting `R ≠ ∅`.  Finally, if `0 ∈ closure R` then
`0 ∈ closure B`, and `B ∩ U = ∅` with `U` a neighbourhood of `0` gives a contradiction.
-/

namespace Work.Bottcher.Contraction2

open Set Metric

/-- The elementary identity `‖z² - w²‖ = ‖z - w‖ * ‖z + w‖`. -/
private lemma norm_sq_sub_sq (z w : ℂ) : ‖z ^ 2 - w ^ 2‖ = ‖z - w‖ * ‖z + w‖ := by
  rw [sq_sub_sq, norm_mul, add_comm, mul_comm]

/-- **Localization of square roots.**  If `z'` is a square root of `w'` and `w'` is within
`ρ²` of `z₀²`, then `z'` lies within `ρ` of `z₀` or within `ρ` of `-z₀`. -/
private lemma localization {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z' w' : ℂ} (hz' : z' ^ 2 = w')
    (h : ‖w' - z₀ ^ 2‖ < ρ ^ 2) : ‖z' - z₀‖ < ρ ∨ ‖z' + z₀‖ < ρ := by
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  have h2 : ρ ^ 2 ≤ ‖z' ^ 2 - z₀ ^ 2‖ := by
    rw [norm_sq_sub_sq, sq]
    exact mul_le_mul hc.1 hc.2 hρ.le (norm_nonneg _)
  rw [hz'] at h2
  linarith

/-- Every complex number has a square root. -/
private lemma exists_sq_eq (w : ℂ) : ∃ z : ℂ, z ^ 2 = w :=
  ⟨Complex.sqrt w, Complex.cpow_nat_inv_pow w (by norm_num : (2 : ℕ) ≠ 0)⟩

/-- **Key step.**  If `S` is preconnected, `U`, `V` are open, `T := {z | z² ∈ S}` is
contained in `U ∪ V`, `T ∩ U ∩ V = ∅`, and `0 ∈ U` (with `0 ∈ S`, so that `0 ∈ T`), then
`T ⊆ U`. -/
private lemma subset_of_isOpen_of_disjoint {S : Set ℂ} (hS : IsPreconnected S) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : {z : ℂ | z ^ 2 ∈ S} ⊆ U ∪ V)
    (hdisj : {z : ℂ | z ^ 2 ∈ S} ∩ (U ∩ V) = ∅) (h0S : (0 : ℂ) ∈ S) (h0U : (0 : ℂ) ∈ U) :
    {z : ℂ | z ^ 2 ∈ S} ⊆ U := by
  by_contra hnot
  obtain ⟨z₀, hz₀T, hz₀U⟩ := Set.not_subset.mp hnot
  set B : Set ℂ := {z : ℂ | z ^ 2 ∈ S ∧ z ∈ V} with hBdef
  have hz₀B : z₀ ∈ B := by
    refine ⟨hz₀T, ?_⟩
    rcases hUV hz₀T with h | h
    · exact absurd h hz₀U
    · exact h
  have hBU : ∀ z, z ∈ B → z ∈ U → False := by
    intro z hzB hzU
    have hmem : z ∈ {z : ℂ | z ^ 2 ∈ S} ∩ (U ∩ V) := ⟨hzB.1, hzU, hzB.2⟩
    rw [hdisj] at hmem
    exact hmem
  set R : Set ℂ := {w : ℂ | ∃ z ∈ B, z ^ 2 = w} with hRdef
  have hRsubS : R ⊆ S := by
    rintro w ⟨z, hzB, hz⟩
    rw [← hz]
    exact hzB.1
  have hRne : R.Nonempty := ⟨z₀ ^ 2, z₀, hz₀B, rfl⟩
  have h0R : (0 : ℂ) ∉ R := by
    rintro ⟨z, hzB, hz⟩
    have hz0 : z = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using hz)
    subst hz0
    exact hBU 0 hzB h0U
  -- `R` is open in `S`
  have hloc₁ : ∀ w : R, ∃ δ : ℝ, 0 < δ ∧ ∀ w' ∈ S, ‖w' - (w : ℂ)‖ < δ → w' ∈ R := by
    intro w
    obtain ⟨z, hzB, hz⟩ : ∃ z ∈ B, z ^ 2 = (w : ℂ) := w.2
    rw [← hz]
    obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzB.2)
    have hzne : z ≠ 0 := by
      rintro rfl
      exact hBU 0 hzB h0U
    have hminpos : 0 < min ρ₀ ‖z‖ := lt_min hρ₀pos (norm_pos_iff.mpr hzne)
    refine ⟨(min ρ₀ ‖z‖ / 2) ^ 2, by positivity, ?_⟩
    intro w' hwS hw'
    obtain ⟨z', hz'⟩ := exists_sq_eq w'
    have hρ' : 0 < min ρ₀ ‖z‖ / 2 := by linarith
    have hle : min ρ₀ ‖z‖ / 2 ≤ ρ₀ := by
      have := min_le_left ρ₀ ‖z‖
      linarith
    rcases localization (z₀ := z) hρ' hz' hw' with h | h
    · refine ⟨z', ⟨by rw [hz']; exact hwS, ?_⟩, hz'⟩
      apply hρ₀
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    · refine ⟨-z', ⟨by rw [neg_sq, hz']; exact hwS, ?_⟩, by rw [neg_sq, hz']⟩
      apply hρ₀
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show -z' - z = -(z' + z) by ring, norm_neg]
      linarith
  -- if `0 ∉ closure R` then `S \ R` is open in `S`
  have hloc₂ : (0 : ℂ) ∉ closure R →
      ∀ w : ↥(S \ R), ∃ δ : ℝ, 0 < δ ∧ ∀ w' ∈ S, ‖w' - (w : ℂ)‖ < δ → w' ∈ S \ R := by
    intro hcl w
    obtain ⟨hwS, hwR⟩ := w.2
    by_cases hw0 : (w : ℂ) = 0
    · rw [hw0]
      have hnot : ¬ ∀ ε > 0, ∃ b ∈ R, dist (0 : ℂ) b < ε := by
        rwa [← Metric.mem_closure_iff]
      simp only [gt_iff_lt, not_forall, not_exists, not_and, not_lt] at hnot
      obtain ⟨ε, hεpos, hε⟩ := hnot
      refine ⟨ε, hεpos, ?_⟩
      intro w' hw'S hw'
      refine ⟨hw'S, ?_⟩
      intro hw'R
      have hb : dist (0 : ℂ) w' < ε := by simpa [dist_eq_norm] using hw'
      exact absurd hb (not_lt.mpr (hε w' hw'R))
    · obtain ⟨z, hz⟩ := exists_sq_eq (w : ℂ)
      have hzT : z ^ 2 ∈ S := by rw [hz]; exact hwS
      have hzU : z ∈ U := by
        rcases hUV hzT with h | h
        · exact h
        · exact absurd ⟨z, ⟨hzT, h⟩, hz⟩ hwR
      have hz'U : -z ∈ U := by
        have hnegT : (-z) ^ 2 ∈ S := by rw [neg_sq, hz]; exact hwS
        rcases hUV hnegT with h | h
        · exact h
        · exact absurd ⟨-z, ⟨hnegT, h⟩, by rw [neg_sq, hz]⟩ hwR
      obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
      obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz'U)
      refine ⟨(min ρ₀ ρ₁ / 2) ^ 2, by positivity, ?_⟩
      intro w' hw'S hw'
      refine ⟨hw'S, ?_⟩
      intro hw'R
      obtain ⟨u, huB, hu⟩ := hw'R
      obtain ⟨z', hz'⟩ := exists_sq_eq w'
      have hρ2 : 0 < min ρ₀ ρ₁ / 2 := by
        have := lt_min hρ₀pos hρ₁pos
        linarith
      have hle₀ : min ρ₀ ρ₁ / 2 ≤ ρ₀ := by
        have := min_le_left ρ₀ ρ₁
        linarith
      have hle₁ : min ρ₀ ρ₁ / 2 ≤ ρ₁ := by
        have := min_le_right ρ₀ ρ₁
        linarith
      have hw'' : ‖w' - z ^ 2‖ < (min ρ₀ ρ₁ / 2) ^ 2 := by rw [hz]; exact hw'
      have key : u = z' ∨ u = -z' := sq_eq_sq_iff_eq_or_eq_neg.mp (hu.trans hz'.symm)
      rcases localization (z₀ := z) hρ2 hz' hw'' with h | h
      · have h1 : z' ∈ U := hρ₀ (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
        have h2 : -z' ∈ U := by
          apply hρ₁
          rw [Metric.mem_ball, dist_eq_norm]
          rw [show -z' - -z = -(z' - z) by ring, norm_neg]
          linarith
        rcases key with hk | hk
        · rw [hk] at huB
          exact hBU z' huB h1
        · rw [hk] at huB
          exact hBU (-z') huB h2
      · have h1 : -z' ∈ U := by
          apply hρ₀
          rw [Metric.mem_ball, dist_eq_norm]
          rw [show -z' - z = -(z' + z) by ring, norm_neg]
          linarith
        have h2 : z' ∈ U := by
          apply hρ₁
          rw [Metric.mem_ball, dist_eq_norm]
          rw [show z' - -z = z' + z by ring]
          linarith
        rcases key with hk | hk
        · rw [hk] at huB
          exact hBU z' huB h2
        · rw [hk] at huB
          exact hBU (-z') huB h1
  rcases em ((0 : ℂ) ∈ closure R) with hclR | hclR
  · have hclB : (0 : ℂ) ∈ closure B := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨w, hwR, hw⟩ := Metric.mem_closure_iff.mp hclR (ε ^ 2) (by positivity)
      obtain ⟨z, hzB, hz⟩ := hwR
      refine ⟨z, hzB, ?_⟩
      have hzw : ‖z‖ ^ 2 = ‖w‖ := by rw [← hz, norm_pow]
      have hε2 : ‖w‖ < ε ^ 2 := by simpa [dist_eq_norm] using hw
      have hlt : ‖z‖ < ε := by nlinarith [norm_nonneg z]
      simpa [dist_eq_norm] using hlt
    obtain ⟨δ, hδpos, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
    obtain ⟨z, hzB, hzδ⟩ := Metric.mem_closure_iff.mp hclB δ hδpos
    exact hBU z hzB (hδU (by simpa [Metric.mem_ball, dist_comm] using hzδ))
  · have hloc₂' := hloc₂ hclR
    choose δ₁ hδ₁ using hloc₁
    choose δ₂ hδ₂ using hloc₂'
    have hRopen : R = S ∩ ⋃ w : R, Metric.ball (w : ℂ) (δ₁ w) := by
      ext x
      constructor
      · intro hx
        refine ⟨hRsubS hx, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨x, hx⟩, by rw [Metric.mem_ball]; simpa using (hδ₁ ⟨x, hx⟩).1⟩
      · rintro ⟨hxS, hx⟩
        rw [Set.mem_iUnion] at hx
        obtain ⟨w, hw⟩ := hx
        rw [Metric.mem_ball] at hw
        exact (hδ₁ w).2 x hxS (by simpa [dist_eq_norm] using hw)
    have hR'open : S \ R = S ∩ ⋃ w : ↥(S \ R), Metric.ball (w : ℂ) (δ₂ w) := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨x, hx⟩, by rw [Metric.mem_ball]; simpa using (hδ₂ ⟨x, hx⟩).1⟩
      · rintro ⟨hxS, hx⟩
        rw [Set.mem_iUnion] at hx
        obtain ⟨w, hw⟩ := hx
        rw [Metric.mem_ball] at hw
        exact (hδ₂ w).2 x hxS (by simpa [dist_eq_norm] using hw)
    have hsub : S ⊆ (⋃ w : R, Metric.ball (w : ℂ) (δ₁ w)) ∪
        (⋃ w : ↥(S \ R), Metric.ball (w : ℂ) (δ₂ w)) := by
      intro x hx
      by_cases hxR : x ∈ R
      · have hxO : x ∈ ⋃ w : R, Metric.ball (w : ℂ) (δ₁ w) := (hRopen ▸ hxR).2
        exact Or.inl hxO
      · have hxSR : x ∈ S \ R := ⟨hx, hxR⟩
        have hxO : x ∈ ⋃ w : ↥(S \ R), Metric.ball (w : ℂ) (δ₂ w) := (hR'open ▸ hxSR).2
        exact Or.inr hxO
    have hdisj' : S ∩ ((⋃ w : R, Metric.ball (w : ℂ) (δ₁ w)) ∩
        (⋃ w : ↥(S \ R), Metric.ball (w : ℂ) (δ₂ w))) = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hxS, hxO, hxO'⟩
      have hxR : x ∈ R := by rw [hRopen]; exact ⟨hxS, hxO⟩
      have hxR' : x ∈ S \ R := by rw [hR'open]; exact ⟨hxS, hxO'⟩
      exact hxR'.2 hxR
    rcases isPreconnected_iff_subset_of_disjoint.mp hS _ _
      (isOpen_iUnion fun w => Metric.isOpen_ball)
      (isOpen_iUnion fun w => Metric.isOpen_ball) hsub hdisj' with hSO | hSO
    · have hmem : (0 : ℂ) ∈ S ∩ ⋃ w : R, Metric.ball (w : ℂ) (δ₁ w) := ⟨h0S, hSO h0S⟩
      rw [← hRopen] at hmem
      exact h0R hmem
    · obtain ⟨w, hwR⟩ := hRne
      have hwS : w ∈ S := hRsubS hwR
      have hmem : w ∈ S \ R := by
        rw [hR'open]
        exact ⟨hwS, hSO hwS⟩
      exact hmem.2 hwR

theorem isPreconnected_preimage_sq {S : Set ℂ} (hS : IsPreconnected S) (h0 : (0 : ℂ) ∈ S) :
    IsPreconnected {z : ℂ | z ^ 2 ∈ S} := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hU hV hUV hdisj
  by_cases h0U : (0 : ℂ) ∈ U
  · exact Or.inl (subset_of_isOpen_of_disjoint hS hU hV hUV hdisj h0 h0U)
  · refine Or.inr (subset_of_isOpen_of_disjoint hS hV hU ?_ ?_ h0 ?_)
    · rwa [Set.union_comm]
    · rw [Set.inter_comm U V] at hdisj
      exact hdisj
    · have h0T : (0 : ℂ) ∈ {z : ℂ | z ^ 2 ∈ S} := by simpa using h0
      rcases hUV h0T with h | h
      · exact absurd h h0U
      · exact h

end Work.Bottcher.Contraction2
