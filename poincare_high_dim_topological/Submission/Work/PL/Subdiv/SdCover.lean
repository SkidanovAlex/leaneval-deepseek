import Submission.Work.PL.Subdiv.SdGlue

/-!
# Every point of a simplex lies in a small simplex of the subdivision (blueprint G3)

`exists_chain_subset_of_mem_simp`: a point of `simp σ` lies in `simp (C.image bary)` for a chain
`C` whose elements are all faces contained in `σ`.  This is the covering statement behind
`PL.Subdivides`: the barycentric subdivision does not change the underlying space.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

variable {N : ℕ}

/-- **Covering lemma.**  A point of the simplex on a face `σ` of `K` lies in the simplex of the
barycenters of a chain of faces contained in `σ`. -/
theorem exists_chain_subset_of_mem_simp {K : Cx N} :
    ∀ (σ : Finset (E N)), σ ∈ K.faces → ∀ x : E N, x ∈ simp σ →
      ∃ C : Finset (Finset (E N)), IsChain K C ∧ (∀ ρ ∈ C, ρ ⊆ σ) ∧ x ∈ simp (C.image bary) := by
  intro σ
  induction σ using Finset.strongInductionOn with
  | _ σ ih =>
    intro hσ x hx
    obtain ⟨α, hα0, hαsum, hαx, -⟩ := exists_sum_smul_of_mem_simp hx
    obtain ⟨v, hvσ, hvmin⟩ := Finset.exists_min_image σ α (K.nonempty_of_mem_faces hσ)
    set τ : Finset (E N) := σ.filter (fun u => α u = α v) with hτ
    have hτσ : τ ⊆ σ := by rw [hτ]; exact Finset.filter_subset _ _
    have hτne : τ.Nonempty := by
      rw [hτ]; exact ⟨v, Finset.mem_filter.mpr ⟨hvσ, rfl⟩⟩
    have hmemτ : ∀ u ∈ σ, u ∈ τ ↔ α u = α v := by
      intro u hu
      rw [hτ, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
    by_cases hτeq : τ = σ
    · -- all coordinates are equal: `x` is the barycenter of `σ`
      have hall : ∀ u ∈ σ, α u = α v := by
        intro u hu
        have h1 : u ∈ τ := by rw [hτeq]; exact hu
        exact (hmemτ u hu).mp h1
      have hval : (σ.card : ℝ) * α v = 1 := by
        rw [← hαsum]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul]
      have hαv : α v = ((σ.card : ℝ))⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hval)
      have hxσ : x = bary σ := by
        rw [← hαx, Finset.sum_congr rfl (fun u hu => by rw [hall u hu]), ← Finset.smul_sum,
          bary_eq_smul_sum, hαv]
      refine ⟨{σ}, ?_, ?_, ?_⟩
      · refine ⟨fun ρ hρ => ?_, fun ρ hρ ρ' hρ' => ?_⟩
        · rw [Finset.mem_singleton.mp hρ]; exact hσ
        · rw [Finset.mem_singleton.mp hρ, Finset.mem_singleton.mp hρ']
          exact Or.inl subset_rfl
      · intro ρ hρ
        rw [Finset.mem_singleton.mp hρ]
      · rw [hxσ, Finset.image_singleton]
        exact subset_convexHull ℝ _ (Finset.mem_singleton_self _)
    · -- some coordinate is strictly larger than the minimum
      have hτssub : τ ⊂ σ := ssubset_iff_subset_ne.mpr ⟨hτσ, hτeq⟩
      obtain ⟨u₀, hu₀σ, hu₀⟩ : ∃ u ∈ σ, α v < α u := by
        obtain ⟨u, hu, hnot⟩ := Finset.exists_of_ssubset hτssub
        refine ⟨u, hu, lt_of_le_of_ne (hvmin u hu) ?_⟩
        intro hcon
        exact hnot ((hmemτ u hu).mpr hcon.symm)
      -- the cone parameter
      set t : ℝ := (σ.card : ℝ) * α v with ht
      have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg (Nat.cast_nonneg _) (hα0 v hvσ)
      have ht1 : t < 1 := by
        have hlt : (↑σ.card : ℝ) * α v < 1 := by
          have h := Finset.sum_lt_sum (fun u hu => hvmin u hu) ⟨u₀, hu₀σ, hu₀⟩
          rw [Finset.sum_const, nsmul_eq_mul, hαsum] at h
          exact h
        rw [ht]
        exact hlt
      have hk : ((σ.card : ℝ)) ≠ 0 := by
        simp only [Nat.cast_ne_zero]
        exact Finset.card_ne_zero.mpr (K.nonempty_of_mem_faces hσ)
      have h1t : (1 : ℝ) - t ≠ 0 := by linarith
      have h1t' : (1 : ℝ) - ↑σ.card * α v ≠ 0 := by rw [← ht]; exact h1t
      set γ : E N → ℝ := fun u => (α u - α v) / (1 - t) with hγ
      have hγ0 : ∀ u ∈ σ, 0 ≤ γ u := by
        intro u hu
        rw [hγ]
        exact div_nonneg (sub_nonneg.mpr (hvmin u hu)) (by linarith)
      have hγτ : ∀ u ∈ τ, γ u = 0 := by
        intro u hu
        have h : α u = α v := (hmemτ u (hτσ hu)).mp hu
        simp only [hγ, h, sub_self, zero_div]
      have hxsplit : x = t • bary σ + (1 - t) • (∑ u ∈ σ, γ u • u) := by
        rw [← hαx, bary_eq_smul_sum, ht]
        simp only [Finset.smul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u hu => ?_
        simp only [hγ, ht]
        rw [smul_smul, smul_smul, ← add_smul]
        congr 1
        field_simp
        ring
      -- the point `y` lies in the simplex on `σ \ τ`
      set y : E N := ∑ u ∈ σ, γ u • u with hy
      have hy_eq : y = ∑ u ∈ σ \ τ, γ u • u := by
        rw [hy]
        exact (Finset.sum_subset Finset.sdiff_subset fun u huσ huτ' => by
          have hu : u ∈ τ := by
            by_contra hu
            exact huτ' (Finset.mem_sdiff.mpr ⟨huσ, hu⟩)
          rw [hγτ u hu, zero_smul]).symm
      have hsumγ : (∑ u ∈ σ \ τ, γ u) = 1 := by
        have hsplit := Finset.sum_sdiff (s₁ := τ) (s₂ := σ) hτσ (f := γ)
        have hτzero : (∑ u ∈ τ, γ u) = 0 := Finset.sum_eq_zero hγτ
        have hσsum : (∑ u ∈ σ, γ u) = 1 := by
          have h1 : (∑ u ∈ σ, γ u) = (∑ u ∈ σ, (α u - α v)) / (1 - t) := by
            rw [hγ, Finset.sum_div]
          have h2 : (∑ u ∈ σ, (α u - α v)) = 1 - t := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hαsum, ht]
          rw [h1, h2, div_self h1t]
        rw [hσsum, hτzero, add_zero] at hsplit
        exact hsplit
      have hy_mem : y ∈ simp (σ \ τ) := by
        rw [hy_eq]
        refine (convex_convexHull ℝ (↑(σ \ τ) : Set (E N))).sum_mem
          (fun u hu => hγ0 u (Finset.mem_sdiff.mp hu).1) hsumγ
          (fun u hu => subset_convexHull ℝ _ (Finset.mem_coe.mpr hu))
      have hfacene : (σ \ τ).Nonempty :=
        Finset.sdiff_nonempty.mpr fun h => hτeq (Finset.Subset.antisymm hτσ h)
      have hface : σ \ τ ∈ K.faces := K.down_closed hσ Finset.sdiff_subset hfacene
      have hssub : σ \ τ ⊂ σ := by
        refine ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun hcon => ?_⟩
        have hsub : τ ⊆ σ \ τ := hcon.symm ▸ hτσ
        obtain ⟨u, hu⟩ := hτne
        exact (Finset.mem_sdiff.mp (hsub hu)).2 hu
      obtain ⟨C', hC', hC'sub, hyC'⟩ := ih (σ \ τ) hssub hface y hy_mem
      refine ⟨insert σ C', ?_, ?_, ?_⟩
      · refine ⟨fun ρ hρ => ?_, fun ρ hρ ρ' hρ' => ?_⟩
        · rcases Finset.mem_insert.mp hρ with rfl | hρ
          · exact hσ
          · exact hC'.1 ρ hρ
        · rcases Finset.mem_insert.mp hρ with h1 | h1
          · rcases Finset.mem_insert.mp hρ' with h2 | h2
            · exact Or.inl (by rw [h1, h2])
            · exact Or.inr (by rw [h1]; exact (hC'sub ρ' h2).trans Finset.sdiff_subset)
          · rcases Finset.mem_insert.mp hρ' with h2 | h2
            · exact Or.inl (by rw [h2]; exact (hC'sub ρ h1).trans Finset.sdiff_subset)
            · exact hC'.2 ρ h1 ρ' h2
      · intro ρ hρ
        rcases Finset.mem_insert.mp hρ with rfl | hρ
        · exact subset_rfl
        · exact (hC'sub ρ hρ).trans Finset.sdiff_subset
      · -- `x` is a convex combination of `bary σ` and `y`
        have hb : bary σ ∈ (↑((insert σ C').image bary) : Set (E N)) :=
          Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨σ, Finset.mem_insert_self σ C', rfl⟩)
        have hyC : y ∈ simp ((insert σ C').image bary) := by
          refine convexHull_mono (Finset.coe_subset.mpr ?_) hyC'
          intro b hb'
          obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb'
          exact Finset.mem_image.mpr ⟨ρ, Finset.mem_insert_of_mem hρ, rfl⟩
        rw [hxsplit, hy]
        exact convex_combo_mem (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ hb) hyC ht0 (le_of_lt ht1)

end

end Work.PL.Subdiv
