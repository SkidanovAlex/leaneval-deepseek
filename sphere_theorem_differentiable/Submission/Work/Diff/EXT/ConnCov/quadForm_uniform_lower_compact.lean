import Mathlib
import Submission.Work.Diff.Alg.Pinch.exists_eps_margin_quad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform lower bound for a compact family of positive definite quadratic forms

Let `C` be a compact subset of a topological space `X` and let `A x` be a family of
`n × n` matrices indexed by `x ∈ C`, such that

* every entry `x ↦ A x i j` is continuous at every point of `C`, and
* for every `x ∈ C` the quadratic form `v ↦ ∑ᵢ ∑ⱼ vᵢ vⱼ (A x)ᵢⱼ` is strictly positive on every
  nonzero vector `v`.

Then there is a *uniform* `δ > 0` with `δ * ∑ᵢ vᵢ² ≤ ∑ᵢ ∑ⱼ vᵢ vⱼ (A x)ᵢⱼ` for all `x ∈ C` and
all `v`.

The proof is the standard compactness argument: the quadratic form is continuous on the compact
set `C × {v | ∑ vᵢ² = 1}`, where it is strictly positive, so it attains a strictly positive
minimum there; scaling an arbitrary nonzero `v` to this sphere gives the general bound.
-/

namespace Work.Diff.EXT.ConnCov

open Work.Diff.Alg.Pinch

/-- The component form `∑ᵢ ∑ⱼ vᵢ vⱼ Mᵢⱼ` of a quadratic form is the matrix form
`quad M v = ∑ᵢ ∑ⱼ Mᵢⱼ vᵢ vⱼ`. -/
lemma sum_sum_mul_eq_quad {n : ℕ} (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * M i j) = quad M v := by
  unfold quad
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- `∑ᵢ vᵢ²` is the `normSq` of `v`. -/
lemma sum_sq_eq_normSq {n : ℕ} (v : Fin n → ℝ) : (∑ i, (v i) ^ 2) = normSq v := by
  unfold normSq
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem quadForm_uniform_lower_compact
    {n : ℕ} {X : Type*} [TopologicalSpace X] {A : X → Fin n → Fin n → ℝ} {C : Set X}
    (hC : IsCompact C)
    (hcont : ∀ x ∈ C, ∀ i j, ContinuousAt (fun y => A y i j) x)
    (hpos : ∀ x ∈ C, ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A x i j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, ∀ v : Fin n → ℝ,
      δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * A x i j := by
  classical
  -- The unit sphere of `normSq = ∑ᵢ vᵢ²`.
  set S : Set (Fin n → ℝ) := {v | normSq v = 1} with hSdef
  have memS : ∀ v : Fin n → ℝ, v ∈ S ↔ normSq v = 1 := by
    intro v; rw [hSdef]; exact Iff.rfl
  have hS : IsCompact S := by rw [hSdef]; exact isCompact_normSq_eq_one n
  have hcomp : IsCompact (C ×ˢ S) := hC.prod hS
  -- The quadratic form `(x, v) ↦ quad (A x) v` is continuous on `C ×ˢ S`.
  have hcontOn : ContinuousOn (fun p : X × (Fin n → ℝ) => quad (A p.1) p.2) (C ×ˢ S) := by
    unfold quad
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    have h1 : ContinuousOn (fun p : X × (Fin n → ℝ) => A p.1 i j) (C ×ˢ S) := by
      intro p hp
      exact (hcont p.1 hp.1 i j).comp_continuousWithinAt continuous_fst.continuousWithinAt
    have h2 : ContinuousOn (fun p : X × (Fin n → ℝ) => p.2 i) (C ×ˢ S) :=
      (continuous_apply i).comp_continuousOn continuous_snd.continuousOn
    have h3 : ContinuousOn (fun p : X × (Fin n → ℝ) => p.2 j) (C ×ˢ S) :=
      (continuous_apply j).comp_continuousOn continuous_snd.continuousOn
    exact (h1.mul h2).mul h3
  -- It is strictly positive there.
  have hposOn : ∀ b ∈ C ×ˢ S, (0 : ℝ) < quad (A b.1) b.2 := by
    rintro ⟨x, v⟩ ⟨hx, hvS⟩
    have hmem : normSq v = 1 := (memS v).mp hvS
    have hv0 : v ≠ 0 := fun h => by
      have h0 : normSq v = 0 := by rw [h]; simp [normSq]
      rw [h0] at hmem
      exact zero_ne_one hmem
    rw [← sum_sum_mul_eq_quad]
    exact hpos x hx v hv0
  -- Extreme value theorem on the compact set.
  obtain ⟨δ, hδpos, hδle⟩ := hcomp.exists_forall_le' hcontOn hposOn
  refine ⟨δ, hδpos, fun x hx v => ?_⟩
  rw [sum_sum_mul_eq_quad, sum_sq_eq_normSq]
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [normSq, quad]
  · -- normalise `v` to the unit sphere
    set c : ℝ := Real.sqrt (normSq v) with hc
    have hcpos : 0 < c := Real.sqrt_pos.mpr (normSq_pos hv0)
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hc2 : c ^ 2 = normSq v := Real.sq_sqrt (normSq_nonneg v)
    set w : Fin n → ℝ := c⁻¹ • v with hw
    have hwS : normSq w = 1 := by
      rw [hw, normSq_smul, ← hc2, ← mul_pow, inv_mul_cancel₀ hcne, one_pow]
    have hcw : c • w = v := by
      rw [hw, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    have hvA : quad (A x) v = c ^ 2 * quad (A x) w := by rw [← hcw, quad_smul]
    have hle : δ ≤ quad (A x) w := hδle (x, w) ⟨hx, (memS w).mpr hwS⟩
    calc δ * normSq v = c ^ 2 * δ := by rw [hc2]; ring
      _ ≤ c ^ 2 * quad (A x) w := mul_le_mul_of_nonneg_left hle (sq_nonneg c)
      _ = quad (A x) v := hvA.symm

end Work.Diff.EXT.ConnCov
