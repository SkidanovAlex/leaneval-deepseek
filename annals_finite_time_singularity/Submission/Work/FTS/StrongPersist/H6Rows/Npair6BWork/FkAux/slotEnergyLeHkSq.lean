/-
Copyright: work module for the Elgindi finite-time singularity project.

# The single-slot `L²` energy of a leaf weight is bounded by `HkSq`

This file proves `Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq`: the
single-slot energy `∫_z ∫_θ ρ · (D_z^bD_θ^a f)²` of a leaf weight `ρ` of `IP6`
(`Work.FTS.TransportS.IsLeafW α a ρ`) is dominated by the squared `ℋ^m`-norm of `f`.

The content is *purely pointwise*: on the open quadrant every leaf weight `ρ` is dominated
by the square of one of the two block weights of `HkIntegrand` — `(Whz)² = w²σ^{-η}` (for the
`D_z`-only slots) resp. `(Wm)² = w²σ^{-γ}` (for the slots carrying a `θ`-derivative) — and
each block of `HkIntegrand α m` is the square of one of these weights times a slot
(`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).  Hence

  `ρ z θ · (D_z^bD_θ^a f z θ)² ≤ HkIntegrand α m f z θ`

at every point of the open quadrant, and the integral estimate follows by
`integral_mono_of_nonneg` (the two angular endpoints are null for `volume.restrict Iθ`).

The constant is `1`: nothing is lost beyond the passage from the integrand to the integral.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-! ## The two endpoints are null for the angular measure -/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval almost everywhere.  (`Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e.) -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## Nonnegativity of the leaf weights on the closed quadrant -/

/-- Every leaf weight of `IP6` is nonnegative on `Iz × Iθ`. -/
private theorem leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z hz θ hθ
    exact sq_nonneg _
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## The pointwise domination of a leaf weight -/

/-- The *two* leaf weights of a `D_z`-only slot (`a = 0`) — `leafEta` and `leafOne` — are
dominated by the square of the block weight `Whz`.

(`leafGam` is deliberately excluded: at `a = 0` it is not a leaf weight
(`Work.FTS.TransportS.IsLeafW` requires `1 ≤ a` for `leafGam`), and indeed
`w²σ^{-γ} ≤ w²σ^{-η}` is *false* on the open quadrant since `σ^{-γ} ≥ σ^{-η}`.) -/
private theorem leaf_le_Whz_sq {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a = 0) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
  subst ha
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha1, _⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Whz_sq z θ hs]
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
  · exfalso; omega

/-- Every leaf weight is dominated by the square of the block weight `Wm`. -/
private theorem leaf_le_Wm_sq {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · rw [Work.FTS.TransportS.leafEta, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
  · rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Wm_sq α z θ hs]
    exact le_mul_of_one_le_right (sq_nonneg _)
      (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
  · rw [Work.FTS.TransportS.leafGam, Work.FTS.H2.hbi_Wm_sq α z θ hs]

/-- **The pointwise slot domination.**  For a leaf weight `ρ` of the slot `a` and any slot
`(a,b)` of order `≤ N`, the weighted slot of any datum `h` is dominated by the
`ℋ^N`-integrand of `h` on the open quadrant. -/
private theorem leaf_dom_gen {α : ℝ} (hα : 0 < α) {N a b : ℕ} (hab : a + b ≤ N)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {h : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α N h z θ := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    rw [Work.Spaces.mixed_zero_right]
    have hb : b ≤ N := by omega
    calc ρ z θ * (Work.Spaces.DzIter b h z θ) ^ 2
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Whz_sq hρ rfl hθ) (sq_nonneg _)
      _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α N h z θ b hb
  · have h1 : 1 ≤ a := hpos
    calc ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        ≤ (Work.FTS.H2.Wm α z θ) ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (leaf_le_Wm_sq hα hρ hθ) (sq_nonneg _)
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simp only [Work.FTS.H2.Wm]; ring
      _ ≤ Work.Spaces.HkIntegrand α N h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α N h z θ a b h1 hab

/-! ## The requested single-slot energy bound -/

theorem slotEnergyLeHkSq : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ} (m : ℕ),
    0 < α → Work.Spaces.HkMem α m f → ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      a + b ≤ m → Work.FTS.TransportS.IsLeafW α a ρ →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ C * Work.Spaces.HkSq α m f := by
  refine ⟨1, one_pos, ?_⟩
  intro α f m hα hm a b ρ hab hρ
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the angular slice estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hz) ?_
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact mul_nonneg (leaf_nonneg hρ z hz θ ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact leaf_dom_gen hα hab hρ hθ
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α m f z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hm.2 ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact mul_nonneg (leaf_nonneg hρ z hz θ ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
      exact hslice z hz
  rw [Work.Spaces.HkSq, one_mul]
  exact hmain

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
