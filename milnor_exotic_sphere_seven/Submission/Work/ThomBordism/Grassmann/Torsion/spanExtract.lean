import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Two spanning elements from a spanning set of a space of rank at most two

In a `ℚ`-vector space `V` of (cardinal) rank at most `2`, any spanning set `s` contains two elements
which already span `V`.  This is the algebraic extraction used to produce the two degree-`(k+8)`
classes of the Thom space from the spanning set `{1 ⊗ a}` of the rationalised cohomology (the space
is *a priori* not known to be finite dimensional, so the cardinal rank — not the finrank — is the
right hypothesis: `finrank` is `0` for infinite-dimensional spaces).
-/

namespace Work.ThomBordism.Grassmann.Torsion

/-- **Two elements of a spanning set span**, when the ambient space has rank at most two. -/
theorem exists_pair_span_eq_top_of_rank_le_two {V : Type*} [AddCommGroup V] [Module ℚ V]
    {s : Set V} (hs : Submodule.span ℚ s = ⊤) (hne : s.Nonempty) (h2 : Module.rank ℚ V ≤ 2) :
    ∃ v1 ∈ s, ∃ v2 ∈ s, Submodule.span ℚ ({v1, v2} : Set V) = ⊤ := by
  by_cases hV : Subsingleton V
  · obtain ⟨v, hv⟩ := hne
    refine ⟨v, hv, v, hv, ?_⟩
    rw [show ({v, v} : Set V) = {v} from by simp]
    rw [Submodule.eq_top_iff']
    intro x
    rw [show x = 0 from Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    -- a nonzero element of `s`
    have hex : ∃ v ∈ s, v ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hle : (⊤ : Submodule ℚ V) ≤ ⊥ := by
        rw [← hs]
        exact Submodule.span_le.mpr (fun x hx => by
          rw [hc x hx]
          exact Submodule.zero_mem _)
      have hbot : (⊥ : Submodule ℚ V) = ⊤ := le_antisymm bot_le hle
      exact hV ⟨fun x y => by
        have hx : x ∈ (⊥ : Submodule ℚ V) := hbot ▸ Submodule.mem_top
        have hy : y ∈ (⊥ : Submodule ℚ V) := hbot ▸ Submodule.mem_top
        rw [Submodule.mem_bot] at hx hy
        rw [hx, hy]⟩
    obtain ⟨v1, hv1s, hv1ne⟩ := hex
    by_cases h1 : Submodule.span ℚ ({v1} : Set V) = ⊤
    · refine ⟨v1, hv1s, v1, hv1s, ?_⟩
      rw [show ({v1, v1} : Set V) = {v1} from by simp, h1]
    · obtain ⟨v2, hv2s, hv2⟩ : ∃ v2 ∈ s, v2 ∉ Submodule.span ℚ ({v1} : Set V) := by
        by_contra hc
        push_neg at hc
        exact h1 (top_le_iff.mp (by
          rw [← hs]
          exact Submodule.span_le.mpr hc))
      by_cases h12 : Submodule.span ℚ ({v1, v2} : Set V) = ⊤
      · exact ⟨v1, hv1s, v2, hv2s, h12⟩
      · exfalso
        obtain ⟨v3, hv3s, hv3⟩ : ∃ v3 ∈ s, v3 ∉ Submodule.span ℚ ({v1, v2} : Set V) := by
          by_contra hc
          push_neg at hc
          exact h12 (top_le_iff.mp (by
            rw [← hs]
            exact Submodule.span_le.mpr hc))
        -- the three vectors are linearly independent
        have hmem1 : v1 ∈ Submodule.span ℚ ({v1} : Set V) := Submodule.subset_span (by simp)
        have hmem2 : v2 ∈ Submodule.span ℚ ({v1, v2} : Set V) := Submodule.subset_span (by simp)
        have hmem1' : v1 ∈ Submodule.span ℚ ({v1, v2} : Set V) := Submodule.subset_span (by simp)
        have hli : LinearIndependent ℚ ![v1, v2, v3] := by
          rw [Fintype.linearIndependent_iff]
          intro g hg i
          have hsum : g 0 • v1 + g 1 • v2 + g 2 • v3 = 0 := by
            have := hg
            simpa [Fin.sum_univ_three] using this
          have hg2 : g 2 = 0 := by
            by_contra hne2
            have hv3mem : v3 ∈ Submodule.span ℚ ({v1, v2} : Set V) := by
              have hsplit : g 2 • v3 = -(g 0 • v1 + g 1 • v2) :=
                eq_neg_of_add_eq_zero_right hsum
              have hval : v3 = (g 2)⁻¹ • (-(g 0 • v1 + g 1 • v2)) := by
                rw [← hsplit, inv_smul_smul₀ hne2]
              rw [hval]
              exact Submodule.smul_mem _ _
                (Submodule.neg_mem _ (Submodule.add_mem _
                  (Submodule.smul_mem _ _ hmem1') (Submodule.smul_mem _ _ hmem2)))
            exact hv3 hv3mem
          have hg1 : g 1 = 0 := by
            by_contra hne1
            have hv2mem : v2 ∈ Submodule.span ℚ ({v1} : Set V) := by
              have hsplit : g 1 • v2 = -(g 0 • v1) := by
                have h := hsum
                simp only [hg2, zero_smul, add_zero] at h
                exact eq_neg_of_add_eq_zero_right h
              have hval : v2 = (g 1)⁻¹ • (-(g 0 • v1)) := by
                rw [← hsplit, inv_smul_smul₀ hne1]
              rw [hval]
              exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem1))
            exact hv2 hv2mem
          have hg0 : g 0 = 0 := by
            have : g 0 • v1 = 0 := by
              have h := hsum
              simp only [hg1, hg2, zero_smul, add_zero] at h
              exact h
            rcases smul_eq_zero.mp this with h | h
            · exact h
            · exact absurd h hv1ne
          fin_cases i
          · exact hg0
          · exact hg1
          · exact hg2
        have h3 : (3 : Cardinal) ≤ Module.rank ℚ V := by
          have h := hli.cardinal_lift_le_rank
          simpa using h
        have : (3 : Cardinal) ≤ 2 := le_trans h3 h2
        exact absurd (Nat.cast_le.mp this) (by norm_num)

end Work.ThomBordism.Grassmann.Torsion
