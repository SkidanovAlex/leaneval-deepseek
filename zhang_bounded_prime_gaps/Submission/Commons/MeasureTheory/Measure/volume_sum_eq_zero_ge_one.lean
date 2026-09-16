import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace Commons.MeasureTheory.Measure

open _root_.MeasureTheory Filter
open scoped Topology

/-- For a nonempty index set (`1 ≤ k`), the simplex boundary hyperplane `∑ i, t i = c` is
Lebesgue-null in `ℝ^k`.  (Without the hypothesis `1 ≤ k` the statement is false at `k = 0`,
`c = 0`, where `Fin 0 → ℝ` is a single point and the "hyperplane" is the whole space, of
measure `1`.) -/
theorem volume_sum_eq_zero_ge_one {k : ℕ} (hk : 1 ≤ k) (c : ℝ) :
    (volume : _root_.MeasureTheory.Measure (Fin k → ℝ)) {t | ∑ i, t i = c} = 0 := by
  obtain ⟨i0⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  -- The linear functional `t ↦ ∑ i, t i`.
  let L : (Fin k → ℝ) →ₗ[ℝ] ℝ := ∑ i : Fin k, LinearMap.proj i
  have hL : ∀ t : Fin k → ℝ, L t = ∑ i, t i := by
    intro t; simp [L]
  -- A point `t₀` with `∑ i, t₀ i = c`, supported at a single coordinate `i0`.
  let t₀ : Fin k → ℝ := fun i => if i = i0 then c else 0
  have hsum : ∀ x : ℝ, (∑ i : Fin k, (if i = i0 then x else (0 : ℝ))) = x := by
    intro x
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have ht₀ : ∑ i, t₀ i = c := hsum c
  -- The level set is the affine subspace through `t₀` with direction `ker L`.
  set S : AffineSubspace ℝ (Fin k → ℝ) := AffineSubspace.mk' t₀ (LinearMap.ker L) with hSdef
  have hmem : ∀ t : Fin k → ℝ, t ∈ S ↔ ∑ i, t i = c := by
    intro t
    rw [hSdef, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, hL, hL, ht₀,
      sub_eq_zero]
  -- It is a strict affine subspace: the point supported at `i0` with value `c + 1` avoids it.
  have hSne : S ≠ ⊤ := by
    intro htop
    have h1 : (fun i => if i = i0 then c + 1 else (0 : ℝ)) ∈ S := by rw [htop]; trivial
    rw [hmem, hsum (c + 1)] at h1
    linarith
  have hset : {t : Fin k → ℝ | ∑ i, t i = c} = (S : Set (Fin k → ℝ)) := by
    ext t; exact (hmem t).symm
  rw [hset]
  exact _root_.MeasureTheory.Measure.addHaar_affineSubspace volume S hSne

end Commons.MeasureTheory.Measure