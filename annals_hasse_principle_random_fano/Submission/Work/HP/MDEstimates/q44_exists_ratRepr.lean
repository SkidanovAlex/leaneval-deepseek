import Mathlib
import Submission.Work.HP.Q44Setup

namespace Work.HP.MDEstimates

/-- Every vector `u` of a rank-`3` sublattice `L ⊆ ℤ^5` is a `ℚ`-linear combination of any
`ℤ`-linearly independent triple `v` of elements of `L`. -/
lemma q44_exists_ratRepr {L : Submodule ℤ (Fin 5 → ℤ)} (hL : Work.HP.rk L = 3)
    {v : Fin 3 → (Fin 5 → ℤ)} (hv : LinearIndependent ℤ v) (hvL : ∀ j, v j ∈ L)
    {u : Fin 5 → ℤ} (hu : u ∈ L) :
    ∃ s : Fin 3 → ℚ, ∀ i : Fin 5, (u i : ℚ) = ∑ j : Fin 3, s j * (v j i : ℚ) := by
  classical
  -- Work in `ℚ^5`: it suffices to show that `u` lies in the `ℚ`-span of the coerced family `v`.
  have hmem : (fun i : Fin 5 => (u i : ℚ)) ∈
      Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i : Fin 5 => (v j i : ℚ))) := by
    -- Otherwise adjoining `u` to `v` gives `4` `ℤ`-linearly independent elements of `L`,
    -- contradicting `finrank ℤ L = rk L = 3`.
    by_contra hcon
    have hL' : Module.finrank ℤ L = 3 := hL
    have hw : LinearIndependent ℤ
        ((Fin.cons (⟨u, hu⟩ : L) (fun j => (⟨v j, hvL j⟩ : L))) : Fin 4 → L) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      -- Push the relation in `L` down to `ℤ^5`.
      have hg5 : (∑ i : Fin 4, g i •
          (((Fin.cons (⟨u, hu⟩ : L) (fun j => (⟨v j, hvL j⟩ : L))) : Fin 4 → L)
            i : Fin 5 → ℤ)) = 0 := by
        have := congrArg (fun x : L => (x : Fin 5 → ℤ)) hg
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using this
      rw [Fin.sum_univ_succ] at hg5
      simp only [Fin.cons_zero, Fin.cons_succ] at hg5
      -- `hg5 : g 0 • u + ∑ j, g j.succ • v j = 0`
      by_cases hg0 : g 0 = 0
      · -- The relation only involves `v`, so `hv` kills it.
        have hsum : (∑ j : Fin 3, g j.succ • v j) = 0 := by
          simpa [hg0] using hg5
        intro i
        induction i using Fin.cases with
        | zero => exact hg0
        | succ j =>
            exact (Fintype.linearIndependent_iff.mp hv (fun j => g j.succ) hsum j)
      · -- `g 0 ≠ 0`, so `u` is an explicit rational combination of `v`: contradiction.
        have hg0q : (g 0 : ℚ) ≠ 0 := by exact_mod_cast hg0
        have hcoord : ∀ i' : Fin 5,
            (g 0 : ℚ) * (u i' : ℚ) + ∑ j : Fin 3, (g j.succ : ℚ) * (v j i' : ℚ) = 0 := by
          intro i'
          have h := congrFun hg5 i'
          simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h
          exact_mod_cast h
        have hrepr : ∀ i' : Fin 5,
            (u i' : ℚ) = ∑ j : Fin 3, (-(g j.succ : ℚ) / (g 0 : ℚ)) * (v j i' : ℚ) := by
          intro i'
          have key : (u i' : ℚ) * (g 0 : ℚ)
              = - ∑ j : Fin 3, (g j.succ : ℚ) * (v j i' : ℚ) := by
            linarith [hcoord i']
          have hmul : (u i' : ℚ) * (g 0 : ℚ)
              = ∑ j : Fin 3, (-(g j.succ : ℚ)) * (v j i' : ℚ) := by
            rw [key, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun j _ => by ring)
          have h1 : (u i' : ℚ)
              = (∑ j : Fin 3, (-(g j.succ : ℚ)) * (v j i' : ℚ)) / (g 0 : ℚ) :=
            (eq_div_iff hg0q).mpr hmul
          rw [h1, Finset.sum_div]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        exact absurd (by
          have hone : (fun i : Fin 5 => (u i : ℚ)) =
              ∑ j : Fin 3, (fun j => -(g j.succ : ℚ) / (g 0 : ℚ)) j •
                (fun i : Fin 5 => (v j i : ℚ)) := by
            funext i'
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            exact hrepr i'
          rw [hone]
          exact Submodule.sum_mem _
            (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))) hcon
    have hcard := LinearIndependent.fintype_card_le_finrank hw
    simp only [Fintype.card_fin] at hcard
    omega
  -- Membership in the span yields the rational coefficients.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  refine ⟨c, fun i => ?_⟩
  have h := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

end Work.HP.MDEstimates
