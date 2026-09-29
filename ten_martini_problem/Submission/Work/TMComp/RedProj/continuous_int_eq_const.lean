import Mathlib

namespace Work.TMComp.RedProj

/-- A continuous real-valued function taking only integer values is constant. -/
theorem continuous_int_eq_const (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ x, ∃ k : ℤ, f x = (k : ℝ)) : ∃ c : ℤ, ∀ x, f x = (c : ℝ) := by
  obtain ⟨c, hc⟩ := hz 0
  refine ⟨c, fun x => ?_⟩
  -- The fibre over `c` is clopen.
  have hclopen : IsClopen (f ⁻¹' ({(c : ℝ)} : Set ℝ)) := by
    refine ⟨?_, ?_⟩
    · exact isClosed_singleton.preimage hf
    · have h_eq : f ⁻¹' ({(c : ℝ)} : Set ℝ) =
          {x | (c : ℝ) - 1 < f x} ∩ {x | f x < (c : ℝ) + 1} := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          rw [hx]
          exact ⟨by linarith, by linarith⟩
        · intro hx
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
          obtain ⟨h1, h2⟩ := hx
          obtain ⟨k, hk⟩ := hz x
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          have hkc : k = c := by
            have h1i : (c : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
            have h1z : c < k + 1 := by exact_mod_cast h1i
            have h2i : ((k : ℤ) : ℝ) < ((c + 1 : ℤ) : ℝ) := by push_cast; linarith
            have h2z : k < c + 1 := by exact_mod_cast h2i
            omega
          rw [hk, hkc]
      rw [h_eq]
      exact (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  -- `ℝ` is (pre)connected, so a nonempty clopen subset is everything.
  have hmem : x ∈ f ⁻¹' ({(c : ℝ)} : Set ℝ) := by
    rw [IsClopen.eq_univ hclopen ⟨0, by simpa using hc⟩]
    trivial
  simpa using hmem

end Work.TMComp.RedProj
