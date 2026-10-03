import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.orbit_region
import Submission.Work.Pert.exhaust_level_bound
import Submission.Work.Pert.Ksub2.Xc_deep_bound

/-!
# `Work.Pert.Ksub2.orbit_region_uniform`

The z-plane orbit region of a compact `K' ⊆ Dφ` for **all** backward steps `m ≥ 1`, with a
thickening that stays inside `D₀`.

`Work.Pert.Ksub2.orbit_region` bounds the first `N` steps (`Z = ⋃_{1 ≤ m ≤ N} φ '' (K' - m)`);
here the level is unbounded, which is possible because the backward walk `w ↦ w - 1` runs to the
left end of the sector, where the Fatou coordinate vanishes:

`Xc_deep_bound` (the deep-strip bound `‖d.φ (w - j)‖ ≤ 4/j` for `j ≥ J₀`, uniform on `K'`) shows
that all but finitely many of the points `d.φ (w - m)` lie in an arbitrarily small disc around
`0 ∈ D₀`.  Taking `Z := Z_fin ∪ closedBall 0 η` with `Z_fin` the (compact) finite part of
`orbit_region`, `Z` is compact, inside `D₀`, and carries a uniform thickening inside `D₀` — the
disc around `0` contributes a fixed thickening `R₁` (the room of `D₀` at `0`), the finite part its
own (`R_fin`), and `cthickening R (s ∪ t) = cthickening R s ∪ cthickening R t` makes the two
combine.
-/

namespace Work.Pert.Ksub2

theorem orbit_region_uniform {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hD0 : IsOpen D₀) (h0D : (0 : ℂ) ∈ D₀) {K' : Set ℂ} (hK'c : IsCompact K')
    (hK' : K' ⊆ d.Dφ) :
    ∃ Z : Set ℂ, IsCompact Z ∧ Z ⊆ D₀ ∧
      (∀ w ∈ K', ∀ m : ℕ, 1 ≤ m → d.φ (w - (m : ℂ)) ∈ Z) ∧
      ∃ R : ℝ, 0 < R ∧ Metric.cthickening R Z ⊆ D₀ := by
  -- ## the tail: uniformly on `K'`, `d.φ (w - j) → 0` at a rate `4/j`
  obtain ⟨J₀, hJ₀⟩ := Xc_deep_bound d hK'c hK'
  -- ## a closed disc around `0` inside `D₀`, with room for a fixed thickening
  obtain ⟨η, hηpos, hηsub⟩ : ∃ η : ℝ, 0 < η ∧ Metric.closedBall (0 : ℂ) η ⊆ D₀ := by
    obtain ⟨e, hepos, hball⟩ := Metric.mem_nhds_iff.mp (hD0.mem_nhds h0D)
    exact ⟨e / 2, half_pos hepos, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  obtain ⟨R₁, hR₁pos, hR₁sub⟩ :=
    (isCompact_closedBall (0 : ℂ) η).exists_cthickening_subset_open hD0 hηsub
  -- ## the finite part, by `orbit_region` at the level `M`
  obtain ⟨ρe, hρepos, hρe⟩ := hK'c.exists_cthickening_subset_open d.Dφ_open hK'
  set M : ℕ := max J₀ ⌈4 / η⌉₊ with hMdef
  have hMt : ⌈4 / η⌉₊ ≤ M := le_max_right _ _
  have hJ₀M : J₀ ≤ M := le_max_left _ _
  obtain ⟨Zfin, hZfin_c, hZfin_sub, hZfin_mem, Rfin, hRfin_pos, -, hRfin_sub⟩ :=
    orbit_region d hD0 hK'c hK' hρepos hρe M
  set Z : Set ℂ := Zfin ∪ Metric.closedBall (0 : ℂ) η with hZdef
  refine ⟨Z, ?_, ?_, ?_, min Rfin R₁, lt_min hRfin_pos hR₁pos, ?_⟩
  · rw [hZdef]
    exact hZfin_c.union (isCompact_closedBall (0 : ℂ) η)
  · rw [hZdef]
    exact Set.union_subset hZfin_sub hηsub
  · intro w hw m hm1
    rw [hZdef, Set.mem_union]
    by_cases hmM : m ≤ M
    · exact Or.inl (hZfin_mem w hw m hm1 hmM)
    · -- beyond the level `M` the point lies in the disc around `0`
      push Not at hmM
      refine Or.inr ?_
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hmJ : J₀ ≤ m := le_trans hJ₀M hmM.le
      have h4 : ‖d.φ (w - (m : ℂ))‖ ≤ 4 / (m : ℝ) := hJ₀ m hmJ w hw
      have hmpos : 0 < (m : ℝ) := by
        have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le M) hmM
        exact_mod_cast hm0
      have hceil : (4 / η) ≤ (m : ℝ) := by
        have h1 : (4 / η) ≤ ((⌈4 / η⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have h2 : ((⌈4 / η⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast le_trans hMt hmM.le
        linarith
      have hηm : 4 ≤ (m : ℝ) * η := (div_le_iff₀ hηpos).mp hceil
      have hle : 4 / (m : ℝ) ≤ η := by
        rw [div_le_iff₀ hmpos]
        nlinarith
      linarith
  · -- the thickenings combine
    rw [hZdef, Metric.cthickening_union]
    exact Set.union_subset
      ((Metric.cthickening_mono (min_le_left _ _) Zfin).trans hRfin_sub)
      ((Metric.cthickening_mono (min_le_right _ _) (Metric.closedBall (0 : ℂ) η)).trans hR₁sub)

end Work.Pert.Ksub2
