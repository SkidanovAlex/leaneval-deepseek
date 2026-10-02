import Mathlib
import Submission.Work.PTGeometric.GrRank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Injectivity of `L` on the planes of a continuous family is an open condition

Let `P : M → EndOp n` be a continuous family of orthogonal projections of rank `k`
(`P x ∈ Gr n k`), let `L : ℝⁿ → ℝᵏ` be linear, and suppose `L` is injective on the plane
`im (P x)` (i.e. `P x z = z → L z = 0 → z = 0`).  Then the same holds for every `y` with
`P y` close enough to `P x` in the operator norm.

The proof is a quantitative one: injectivity of `L` on the fixed space of `P x` gives a
continuous left inverse `g` of `L|_im (P x)` (finite-dimensional codomain), hence a uniform
constant `‖g‖` with `‖v‖ ≤ ‖g‖ · ‖L v‖` for `v ∈ im (P x)`.  For `z` in the fixed space of
`P y` with `L z = 0` one then compares `P x z ∈ im (P x)` with `z` through the defect
`(P x - P y) z`, which is small as soon as `‖P y - P x‖` is small.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Work.PTGeometric

open Work.PTGeometric

/-- **`L` stays injective on the planes of a continuous family of projections.**

If `L` is injective on the fixed space of `P x`, then `L` is injective on the fixed space of
every `P y` with `‖P y - P x‖` small enough.  No continuity of `P` is needed for the
conclusion as stated (the neighbourhood is described directly in the operator norm); `hP` is
part of the interface. -/
theorem hinj_nhds_of_hinj {n k : ℕ} {M : Type} [TopologicalSpace M]
    (P : M → Work.PTGeometric.EndOp n)
    (hP : Continuous P) (hproj : ∀ x, P x ∈ Work.PTGeometric.Gr n k)
    (L : Work.PTGeometric.Amb n →L[ℝ] Work.PTGeometric.Amb k) (x : M)
    (hx : ∀ z : Work.PTGeometric.Amb n, P x z = z → L z = 0 → z = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : M, ‖P y - P x‖ < ε →
      ∀ z : Work.PTGeometric.Amb n, P y z = z → L z = 0 → z = 0 := by
  -- The plane of `P x`, as a submodule of `ℝⁿ`.
  set V : Submodule ℝ (Amb n) := LinearMap.range ((P x : EndOp n) : Amb n →ₗ[ℝ] Amb n)
    with hVdef
  -- A vector is fixed by `P x` exactly when it lies in the plane `V`.
  have hVfix : ∀ z : Amb n, z ∈ V ↔ P x z = z := by
    intro z
    rw [hVdef]
    constructor
    · rintro ⟨w, hw⟩
      rw [← hw]
      exact mem_Gr_apply_apply (hproj x) w
    · intro hz
      exact ⟨z, hz⟩
  -- `hx` says that `L` restricted to `V` is injective.
  have hker : ∀ v : V, (L.comp V.subtypeL) v = 0 → v = 0 := by
    intro v hv
    have hLv : L ((v : V) : Amb n) = 0 := hv
    have hfix : P x ((v : V) : Amb n) = ((v : V) : Amb n) := (hVfix _).mp v.2
    exact Subtype.ext (hx _ hfix hLv)
  have hinjLv : Function.Injective (L.comp V.subtypeL) := by
    intro v w hvw
    have h : (L.comp V.subtypeL) (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker (v - w) h)
  -- An injective map with finite-dimensional codomain has a continuous left inverse, giving a
  -- uniform bound `‖v‖ ≤ ‖g‖ ‖L v‖` on the plane.
  obtain ⟨g, hg⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (𝕜 := ℝ) (f := L.comp V.subtypeL) hinjLv
  have hbound : ∀ v ∈ V, ‖v‖ ≤ ‖g‖ * ‖L v‖ := by
    intro v hv
    have h := hg ⟨v, hv⟩
    have hnorm : ‖(⟨v, hv⟩ : V)‖ = ‖v‖ := Submodule.coe_norm ⟨v, hv⟩
    calc ‖v‖ = ‖(⟨v, hv⟩ : V)‖ := hnorm.symm
      _ = ‖g ((L.comp V.subtypeL) ⟨v, hv⟩)‖ := by rw [h]
      _ ≤ ‖g‖ * ‖(L.comp V.subtypeL) ⟨v, hv⟩‖ := g.le_opNorm _
      _ = ‖g‖ * ‖L v‖ := rfl
  refine ⟨1 / (2 * (1 + ‖g‖ * ‖L‖)), by positivity, ?_⟩
  intro y hy z hyz hLz
  have hden : 0 < 1 + ‖g‖ * ‖L‖ := by positivity
  -- The defect of the two projections is small.
  have hδ2 : (1 + ‖g‖ * ‖L‖) * ‖P y - P x‖ < 1 := by
    have h := mul_lt_mul_of_pos_left hy hden
    have hc : (1 + ‖g‖ * ‖L‖) * (1 / (2 * (1 + ‖g‖ * ‖L‖))) = 1 / 2 := by
      field_simp
    rw [hc] at h
    linarith
  -- The three ingredients of the estimate.
  have hPxm : P x z ∈ V := (hVfix _).mpr (mem_Gr_apply_apply (hproj x) z)
  have h1 : ‖P x z‖ ≤ ‖g‖ * ‖L (P x z)‖ := hbound _ hPxm
  have hLsub : L (P x z) = L ((P x - P y) z) := by
    rw [sub_apply, map_sub, hyz, hLz, sub_zero]
  have h2 : ‖L (P x z)‖ ≤ ‖L‖ * (‖P y - P x‖ * ‖z‖) := by
    rw [hLsub]
    calc ‖L ((P x - P y) z)‖ ≤ ‖L‖ * ‖(P x - P y) z‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖P x - P y‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_left ((P x - P y).le_opNorm z) (norm_nonneg L)
      _ = ‖L‖ * (‖P y - P x‖ * ‖z‖) := by rw [norm_sub_rev]
  have hz_eq : z = P x z + (P y - P x) z := by
    have h : (P y - P x) z = z - P x z := by rw [sub_apply, hyz]
    rw [h]; abel
  have h3 : ‖z‖ ≤ ‖P x z‖ + ‖P y - P x‖ * ‖z‖ := by
    have hop : ‖(P y - P x) z‖ ≤ ‖P y - P x‖ * ‖z‖ := (P y - P x).le_opNorm z
    calc ‖z‖ = ‖P x z + (P y - P x) z‖ := congrArg norm hz_eq
      _ ≤ ‖P x z‖ + ‖(P y - P x) z‖ := norm_add_le _ _
      _ ≤ ‖P x z‖ + ‖P y - P x‖ * ‖z‖ := by linarith
  have hA : ‖P x z‖ ≤ ‖g‖ * (‖L‖ * (‖P y - P x‖ * ‖z‖)) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg g))
  have hz1 : ‖z‖ ≤ (1 + ‖g‖ * ‖L‖) * ‖P y - P x‖ * ‖z‖ := by
    calc ‖z‖ ≤ ‖P x z‖ + ‖P y - P x‖ * ‖z‖ := h3
      _ ≤ ‖g‖ * (‖L‖ * (‖P y - P x‖ * ‖z‖)) + ‖P y - P x‖ * ‖z‖ := by linarith
      _ = (1 + ‖g‖ * ‖L‖) * ‖P y - P x‖ * ‖z‖ := by ring
  have hzero : ‖z‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hne)
    have hlt : (1 + ‖g‖ * ‖L‖) * ‖P y - P x‖ * ‖z‖ < ‖z‖ :=
      mul_lt_of_lt_one_left hpos hδ2
    linarith
  exact norm_eq_zero.mp hzero

end Work.PTGeometric
