import Mathlib

namespace Work.PL.Generic

/-- "Peeling" step for affine spans: if `x` lies in the affine span of `s ∪ {p}` but not in that of
`s`, then conversely `p` lies in the affine span of `s ∪ {x}`.  (Both spans are affine subspaces of
the vector space `V` regarded as an affine space over itself.) -/
theorem mem_affineSpan_insert_of_mem_of_notMem {V : Type*} [AddCommGroup V] [Module ℝ V]
    {s : Set V} {x p : V} (hx : x ∈ affineSpan ℝ (s ∪ {p})) (hx' : x ∉ affineSpan ℝ s) :
    p ∈ affineSpan ℝ (s ∪ {x}) := by
  rw [Set.union_singleton] at hx ⊢
  by_cases hB : affineSpan ℝ s = ⊥
  · -- Degenerate case: `affineSpan ℝ s` is empty, so `s = ∅` and `x = p` is forced.
    have hs : s = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro a ha
      exact (AffineSubspace.notMem_bot ℝ V a) (by rw [← hB]; exact mem_affineSpan ℝ ha)
    have hxp : x = p := by
      have : x ∈ affineSpan ℝ ({p} : Set V) := by simpa [hs] using hx
      exact (AffineSubspace.mem_affineSpan_singleton ℝ V).mp this
    rw [hxp, hs]
    simp
  · -- Nondegenerate case: pick a base point `b ∈ affineSpan ℝ s`.
    obtain ⟨b, hb⟩ := (AffineSubspace.nonempty_iff_ne_bot (affineSpan ℝ s)).mpr hB
    have hxmem : x ∈ affineSpan ℝ (insert p (affineSpan ℝ s : Set V)) := by
      rw [affineSpan_insert_affineSpan ℝ p s]
      exact hx
    obtain ⟨r, p0, hp0, hxe⟩ := (AffineSubspace.mem_affineSpan_insert_iff hb p x).mp hxmem
    -- `r ≠ 0`, since otherwise `x = p0 ∈ affineSpan ℝ s`.
    have hr : r ≠ 0 := by
      intro hr0
      rw [hr0, zero_smul, zero_vadd] at hxe
      rw [hxe] at hx'
      exact hx' hp0
    -- Invert the relation `x = r • (p -ᵥ b) +ᵥ p0`.
    have hp_eq : p = r⁻¹ • (x -ᵥ p0) +ᵥ b := by
      have hd : x -ᵥ p0 = r • (p -ᵥ b) := by rw [hxe, vadd_vsub]
      have h1 : p -ᵥ b = r⁻¹ • (x -ᵥ p0) := by
        rw [hd, smul_smul, inv_mul_cancel₀ hr, one_smul]
      rw [← h1, vsub_vadd]
    rw [← affineSpan_insert_affineSpan ℝ x s]
    exact (AffineSubspace.mem_affineSpan_insert_iff hp0 x p).mpr ⟨r⁻¹, b, hb, hp_eq⟩

end Work.PL.Generic
