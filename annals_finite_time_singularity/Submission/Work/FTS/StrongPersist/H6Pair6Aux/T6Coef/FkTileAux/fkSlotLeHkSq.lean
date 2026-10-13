/-
Copyright: work module for the Elgindi finite-time singularity project.

# The single-slot energy of a leaf weight is bounded by `HkSq`

For a leaf weight `ρ` of the slot `a` (`Work.FTS.TransportS.IsLeafW α a ρ`) and any slot
`(a, j)` of order `a + j ≤ n`, the weighted `L²`-energy of a *single* slot,

  `∫_z ∫_θ ρ · (D_z^j D_θ^a f)²`,

is dominated by the squared `ℋⁿ`-norm of `f`, with constant `1`.

The content is purely pointwise.  On the open quadrant every leaf weight `ρ` is dominated by
the square of one of the two block weights of `HkIntegrand`:

* for `a = 0` (only `leafEta`, `leafOne` are available — `IsLeafW α 0 ρ` excludes `leafGam`)
  the block `(Whz)² = w²σ^{-η}` of the `D_z`-slots;
* for `a ≥ 1` the block `(Wm)² = w²σ^{-γ}` of the mixed slots;

and each block of `HkIntegrand α n` is the square of the corresponding block weight times a
slot (`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).  Hence

  `ρ z θ · (D_z^jD_θ^a f z θ)² ≤ HkIntegrand α n f z θ`

on the open quadrant, and the integral estimate follows from `integral_mono_of_nonneg`
(the two angular endpoints are null for `volume.restrict Iθ`, and only `z ∈ Iz` is used,
`z < 0` being irrelevant for the restricted measure).

The same statement with an unspecified constant was proved independently as
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq`; here the constant is
pinned to `1`, which is what the level-six coefficient rows consume.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The two angular endpoints are null for `volume.restrict Iθ` -/

private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## Nonnegativity of the leaf weights on the closed quadrant -/

private lemma leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z _ θ hθ
    rw [Work.FTS.TransportS.leafEta]
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z _ θ _
    rw [Work.FTS.TransportS.leafOne]
    exact sq_nonneg _
  · intro z _ θ hθ
    rw [Work.FTS.TransportS.leafGam]
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## The pointwise domination of a leaf weight by a block weight -/

/-- The two leaf weights of a `D_z`-only slot (`a = 0`) — `leafEta` and `leafOne` — are
dominated by `(Whz)² = w²σ^{-η}`.  (`leafGam` is excluded at `a = 0` by `IsLeafW`, and
rightly so: `w²σ^{-γ} ≤ w²σ^{-η}` is false on the open quadrant since `γ > η`.) -/
private lemma leaf_le_Whz_sq {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
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
  · exact absurd ha1 (by omega)

/-- Every leaf weight is dominated by `(Wm)² = w²σ^{-γ}`, the block weight of the mixed
slots.  This is where `γ ≥ η` (`Work.FTS.H2.rpow_eta_le_gam`) is used. -/
private lemma leaf_le_Wm_sq {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
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
`(a, b)` of order `≤ N`, the weighted slot of any datum `h` is dominated by the
`ℋ^N`-integrand of `h` on the open quadrant. -/
private lemma leaf_dom {α : ℝ} (hα : 0 < α) {N a b : ℕ} (hab : a + b ≤ N)
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
      _ = (Work.Spaces.DzIter b h z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.H2.Whz_eq]
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

/-! ## The single-slot energy bound -/

theorem fkSlotLeHkSq {α : ℝ} (hα : 0 < α) {f : Work.FTS.Galerkin.Fn} {n a j : ℕ}
    (haj : a + j ≤ n) {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    (hmem : Work.Spaces.HkMem α n f) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed j a f z θ) ^ 2) ≤ Work.Spaces.HkSq α n f := by
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the angular slice estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j a f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact mul_nonneg (leaf_nonneg hρ z hz θ ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact leaf_dom hα haj hρ hθ
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
    exact MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      exact mul_nonneg (leaf_nonneg hρ z hz θ ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _))
  · filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
    exact hslice z hz

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
