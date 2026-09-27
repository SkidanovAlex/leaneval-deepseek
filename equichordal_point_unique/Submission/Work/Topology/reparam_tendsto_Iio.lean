import Mathlib

/-!
# Reparametrising the one-sided limit `t → 1⁻`

The map `s ↦ s/(s+1)` is an order isomorphism `(0,∞) → (0,1)` and tends to `1` as `s → +∞`.
It is used to move between the two parametrisations of a path in `H0`: Rychlik's path-limit
theorem `H0_path_limit` is stated at `s → +∞` on `[0,∞)`, while the radii of the uniformising disc
are naturally parametrised by `r → 1⁻`.
-/

open Filter _root_.Topology

namespace Work.EQ

theorem div_succ_pos {s : ℝ} (hs : 0 < s) : 0 < s / (s + 1) :=
  div_pos hs (by linarith)

theorem div_succ_lt_one {s : ℝ} (hs : -1 < s) : s / (s + 1) < 1 := by
  rw [div_lt_one (by linarith)]; linarith

/-- `P` holds eventually at `1⁻` iff it holds eventually along `s ↦ s/(s+1)` as `s → ∞`. -/
theorem eventually_nhdsWithin_Iio_iff_eventually_atTop_div {P : ℝ → Prop} :
    (∀ᶠ s : ℝ in atTop, P (s / (s + 1))) ↔
      (∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), P r) := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := eventually_atTop.1 h
    refine (nhdsLT_basis (1 : ℝ)).mem_iff.mpr ⟨max S 0 / (max S 0 + 1), ?_, ?_⟩
    · exact div_succ_lt_one (by linarith [le_max_right S 0])
    · intro r hr
      have h1r : 0 < 1 - r := by linarith [hr.2]
      have hrS : S ≤ r / (1 - r) := by
        rw [le_div_iff₀ h1r]
        have hlt : max S 0 / (max S 0 + 1) < r := hr.1
        rw [div_lt_iff₀ (by linarith [le_max_right S 0] : (0:ℝ) < max S 0 + 1)] at hlt
        have h2 : S * (1 - r) ≤ max S 0 * (1 - r) :=
          mul_le_mul_of_nonneg_right (le_max_left S 0) (le_of_lt h1r)
        nlinarith [hlt, h2]
      have hsr : r / (1 - r) / (r / (1 - r) + 1) = r := by
        field_simp
        ring
      rw [← hsr]
      exact hS _ hrS
  · intro h
    obtain ⟨r₀, hr₀, hsub⟩ := (nhdsLT_basis (1 : ℝ)).mem_iff.mp h
    have h1r₀ : 0 < 1 - r₀ := by linarith
    filter_upwards [eventually_gt_atTop (max (r₀ / (1 - r₀)) 1)] with s hs
    have hspos : 0 < s :=
      lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) (le_of_lt hs)
    apply hsub
    refine ⟨?_, div_succ_lt_one (by linarith)⟩
    by_cases h0 : r₀ ≤ 0
    · exact lt_of_le_of_lt h0 (div_succ_pos hspos)
    · have h3 : r₀ / (1 - r₀) < s := lt_of_le_of_lt (le_max_left _ _) hs
      have h4 : r₀ = (1 - r₀) * (r₀ / (1 - r₀)) := by field_simp
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < s + 1), h4]
      nlinarith

/-- Tendsto form of the reparametrisation. -/
theorem tendsto_iff_tendsto_comp_div {Y : Type*} [TopologicalSpace Y] {γ : ℝ → Y} {l : Filter Y} :
    Tendsto (fun s : ℝ => γ (s / (s + 1))) atTop l ↔
      Tendsto γ (nhdsWithin 1 (Set.Iio (1 : ℝ))) l := by
  constructor
  · intro h U hU
    exact (eventually_nhdsWithin_Iio_iff_eventually_atTop_div (P := fun r => γ r ∈ U)).mp
      (h.eventually (eventually_mem_set.mpr hU))
  · intro h U hU
    exact (eventually_nhdsWithin_Iio_iff_eventually_atTop_div (P := fun r => γ r ∈ U)).mpr
      (h.eventually (eventually_mem_set.mpr hU))

/-- Continuity under the reparametrisation. -/
theorem continuousOn_comp_div {Y : Type*} [TopologicalSpace Y] {γ : ℝ → Y}
    (h : ContinuousOn γ (Set.Iio (1 : ℝ))) :
    ContinuousOn (fun s : ℝ => γ (s / (s + 1))) (Set.Ici 0) := by
  have hc : ContinuousOn (fun s : ℝ => s / (s + 1)) (Set.Ici 0) := by
    refine ContinuousOn.div continuousOn_id (continuousOn_id.add continuousOn_const) ?_
    intro s hs
    have hs' : (0:ℝ) ≤ s := hs
    positivity
  refine h.comp hc ?_
  intro s hs
  exact div_succ_lt_one (by linarith [show (0:ℝ) ≤ s from hs])

end Work.EQ
