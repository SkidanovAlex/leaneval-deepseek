import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

open Set Filter
open scoped Topology

/-- **The intermediate value step.**  A continuous function on `[0,δ]` with `f 0 ≥ 0` and
`f δ < 0` has a zero in `[0,δ]` (no monotonicity needed). -/
lemma exists_root_Icc {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 δ))
    (h0 : 0 ≤ f 0) (hδ' : f δ < 0) : ∃ s ∈ Set.Icc 0 δ, f s = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f δ) (f 0) := ⟨le_of_lt hδ', h0⟩
  have himg : (0 : ℝ) ∈ f '' Set.Icc 0 δ :=
    (intermediate_value_Icc' (a := (0 : ℝ)) (b := δ) (le_of_lt hδ) hf) hmem
  obtain ⟨s, hs, hfs⟩ := (Set.mem_image f (Set.Icc 0 δ) 0).mp himg
  exact ⟨s, hs, hfs⟩

/-- **The parametric root of a strictly decreasing family.** Let `B` be an open set of parameters,
`δ > 0`, and `F : α → ℝ → ℝ` be such that `(u,s) ↦ F u s` is continuous on `B × [0,δ]`, `s ↦ F u s`
is strictly decreasing on `[0,δ]` for `u ∈ B`, with `F u 0 ≥ 0` and `F u δ < 0`.  Then there is a
root `h u ∈ [0,δ]` of `s ↦ F u s` for each `u ∈ B`; `h` is continuous on `B`, the sign of `F u s` is
read off from the position of `s` relative to `h u`, and the root is unique in `[0,δ]`. -/
theorem rootParamContinuous {α : Type*} [TopologicalSpace α] {B : Set α} (hB : IsOpen B)
    {δ : ℝ} (hδ : 0 < δ) {F : α → ℝ → ℝ}
    (hcont : ContinuousOn (fun x : α × ℝ => F x.1 x.2) (B ×ˢ Set.Icc 0 δ))
    (hanti : ∀ u ∈ B, StrictAntiOn (F u) (Set.Icc 0 δ))
    (h0 : ∀ u ∈ B, 0 ≤ F u 0) (hδ' : ∀ u ∈ B, F u δ < 0) :
    ∃ h : α → ℝ, (∀ u ∈ B, h u ∈ Set.Icc 0 δ ∧ F u (h u) = 0) ∧ ContinuousOn h B ∧
      (∀ u ∈ B, ∀ s ∈ Set.Icc 0 δ, (F u s ≤ 0 ↔ h u ≤ s)) ∧
      (∀ u ∈ B, ∀ s ∈ Set.Icc 0 δ, F u s = 0 ↔ s = h u) := by
  classical
  -- the `s`-slice `s ↦ F u s` at a fixed parameter
  have sslice : ∀ (u : α), u ∈ B → ContinuousOn (fun s : ℝ => F u s) (Set.Icc 0 δ) := by
    intro u hu
    have hf : ContinuousOn (fun s : ℝ => (u, s)) (Set.Icc 0 δ) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmap : MapsTo (fun s : ℝ => (u, s)) (Set.Icc 0 δ) (B ×ˢ Set.Icc 0 δ) :=
      fun s hs => ⟨hu, hs⟩
    simpa [Function.comp_def] using hcont.comp hf hmap
  -- the `u`-slice `u ↦ F u c` at a fixed height `c ∈ [0,δ]`
  have uslice : ∀ (c : ℝ), c ∈ Set.Icc 0 δ → ContinuousOn (fun u : α => F u c) B := by
    intro c hc
    have hf : ContinuousOn (fun u : α => (u, c)) B :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hmap : MapsTo (fun u : α => (u, c)) B (B ×ˢ Set.Icc 0 δ) :=
      fun u hu => ⟨hu, hc⟩
    simpa [Function.comp_def] using hcont.comp hf hmap
  -- existence of a root for every parameter
  have exists_root : ∀ u ∈ B, ∃ s : ℝ, s ∈ Set.Icc 0 δ ∧ F u s = 0 := by
    intro u hu
    obtain ⟨s, hs, hfs⟩ := exists_root_Icc hδ (sslice u hu) (h0 u hu) (hδ' u hu)
    exact ⟨s, hs, hfs⟩
  -- the root function
  let h : α → ℝ := fun u => if hu : u ∈ B then Classical.choose (exists_root u hu) else 0
  have h_eq : ∀ u (hu : u ∈ B), h u = Classical.choose (exists_root u hu) := by
    intro u hu
    exact dif_pos hu
  have h_mem : ∀ u (hu : u ∈ B), h u ∈ Set.Icc 0 δ := by
    intro u hu
    rw [h_eq u hu]
    exact (Classical.choose_spec (exists_root u hu)).1
  have h_root : ∀ u (hu : u ∈ B), F u (h u) = 0 := by
    intro u hu
    rw [h_eq u hu]
    exact (Classical.choose_spec (exists_root u hu)).2
  -- the sign of `F u s` is read off from the position of `s` relative to `h u`
  have h_sign : ∀ u (hu : u ∈ B) (s : ℝ), s ∈ Set.Icc 0 δ → (F u s ≤ 0 ↔ h u ≤ s) := by
    intro u hu s hs
    have hh := (hanti u hu).le_iff_ge hs (h_mem u hu)
    rwa [h_root u hu] at hh
  -- and the root is the only zero in `[0,δ]`
  have h_zero : ∀ u (hu : u ∈ B) (s : ℝ), s ∈ Set.Icc 0 δ → (F u s = 0 ↔ s = h u) := by
    intro u hu s hs
    constructor
    · intro hfs
      exact (hanti u hu).injOn hs (h_mem u hu) (by rw [hfs, h_root u hu])
    · intro hsh
      rw [hsh]
      exact h_root u hu
  refine ⟨h, fun u hu => ⟨h_mem u hu, h_root u hu⟩, ?_, h_sign, h_zero⟩
  -- continuity of `h` on `B`, by a squeeze against `F` at the two sides of `h u₀`
  intro u₀ hu₀
  -- on the *open* set `B` continuity within `B` is continuity at the point
  rw [continuousWithinAt_iff_continuousAt (hB.mem_nhds hu₀)]
  change Tendsto h (𝓝 u₀) (𝓝 (h u₀))
  rw [tendsto_order]
  constructor
  · -- `h u` is eventually `> b` when `b < h u₀`
    intro b hb
    by_cases hb0 : b < 0
    · filter_upwards [hB.mem_nhds hu₀] with u hu
      have := (h_mem u hu).1
      linarith
    · rw [not_lt] at hb0
      set c : ℝ := (b + h u₀) / 2 with hc_def
      have hc_mem : c ∈ Set.Icc 0 δ := by
        refine ⟨?_, ?_⟩
        · have h1 := (h_mem u₀ hu₀).1; linarith [hc_def, hb0, h1]
        · have h1 := (h_mem u₀ hu₀).2; linarith [hc_def, h1, hb]
      have hc_lt : c < h u₀ := by linarith [hc_def, hb]
      have hpos : 0 < F u₀ c := by
        rw [← not_le]
        intro hle
        exact absurd ((h_sign u₀ hu₀ c hc_mem).mp hle) (not_le.mpr hc_lt)
      have hev : ∀ᶠ u in 𝓝 u₀, 0 < F u c :=
        ((uslice c hc_mem).continuousAt (hB.mem_nhds hu₀)).preimage_mem_nhds
          (Ioi_mem_nhds hpos)
      filter_upwards [hev, hB.mem_nhds hu₀] with u hfu hu
      have hlt : c < h u := by
        rw [← not_le]
        intro hle
        exact absurd ((h_sign u hu c hc_mem).mpr hle) (not_le.mpr hfu)
      linarith
  · -- `h u` is eventually `< b` when `h u₀ < b`
    intro b hb
    by_cases hbδ : b ≤ δ
    · set c : ℝ := (h u₀ + b) / 2 with hc_def
      have hc_mem : c ∈ Set.Icc 0 δ := by
        refine ⟨?_, ?_⟩
        · have h1 := (h_mem u₀ hu₀).1; linarith [hc_def]
        · have h1 := (h_mem u₀ hu₀).2; linarith [hc_def, h1, hbδ]
      have hc_gt : h u₀ < c := by linarith [hc_def, hb]
      have hneg : F u₀ c < 0 := by
        have h2 : F u₀ c < F u₀ (h u₀) :=
          ((hanti u₀ hu₀).lt_iff_gt hc_mem (h_mem u₀ hu₀)).mpr hc_gt
        rwa [h_root u₀ hu₀] at h2
      have hev : ∀ᶠ u in 𝓝 u₀, F u c < 0 :=
        ((uslice c hc_mem).continuousAt (hB.mem_nhds hu₀)).preimage_mem_nhds
          (Iio_mem_nhds hneg)
      filter_upwards [hev, hB.mem_nhds hu₀] with u hfu hu
      have h1 : h u ≤ c := (h_sign u hu c hc_mem).mp (le_of_lt hfu)
      linarith
    · -- `δ < b`: then `h u ≤ δ < b` everywhere
      rw [not_le] at hbδ
      filter_upwards [hB.mem_nhds hu₀] with u hu
      have := (h_mem u hu).2
      linarith

end Work.PTGeometric.WeakRegion
