import Mathlib

namespace Commons.LinearAlgebra

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField Bundle
open Filter

/-- Two linearly independent pairs spanning the same plane are related by an invertible
change of basis: `u' = a u + b v`, `v' = c u + d v` with `a d - b c ≠ 0`. -/
theorem exists_basis_change_of_span_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    {u v u' v' : V} (hind : LinearIndependent ℝ ![u, v])
    (hind' : LinearIndependent ℝ ![u', v'])
    (hspan : Submodule.span ℝ {u, v} = Submodule.span ℝ {u', v'}) :
    ∃ a b c d : ℝ, u' = a • u + b • v ∧ v' = c • u + d • v ∧ a * d - b * c ≠ 0 := by
  -- Express `u'` and `v'` in terms of the spanning pair `u, v`.
  have h1 : u' ∈ Submodule.span ℝ ({u, v} : Set V) := by
    rw [hspan]; exact Submodule.subset_span (by simp)
  have h2 : v' ∈ Submodule.span ℝ ({u, v} : Set V) := by
    rw [hspan]; exact Submodule.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp h2
  refine ⟨a, b, c, d, hab.symm, hcd.symm, ?_⟩
  -- Suppose the coordinate matrix is singular; then `u'` and `v'` are linearly dependent.
  intro hdet
  have hp := LinearIndependent.pair_iff.mp hind'
  have key1 : d • u' + (-b) • v' = 0 := by
    have hid : d • u' + (-b) • v' = (a * d - b * c) • u := by
      rw [← hab, ← hcd]
      simp only [smul_add, smul_smul]
      module
    rw [hid, hdet, zero_smul]
  have key2 : c • u' + (-a) • v' = 0 := by
    have hid : c • u' + (-a) • v' = (b * c - a * d) • v := by
      rw [← hab, ← hcd]
      simp only [smul_add, smul_smul]
      module
    rw [hid, show b * c - a * d = 0 by linarith [hdet], zero_smul]
  obtain ⟨hd0, hnb0⟩ := hp d (-b) key1
  obtain ⟨hc0, hna0⟩ := hp c (-a) key2
  have hb0 : b = 0 := neg_eq_zero.mp hnb0
  have ha0 : a = 0 := neg_eq_zero.mp hna0
  -- Hence `u' = 0`, contradicting linear independence of `u', v'`.
  have hu'0 : u' = 0 := by rw [hab.symm, ha0, hb0]; simp
  exact one_ne_zero (hp 1 0 (by simp [hu'0])).1

end Commons.LinearAlgebra
