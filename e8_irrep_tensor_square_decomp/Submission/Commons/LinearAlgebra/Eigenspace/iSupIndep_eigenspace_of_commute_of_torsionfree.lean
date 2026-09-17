import Mathlib.LinearAlgebra.DFinsupp

namespace Commons.LinearAlgebra.Eigenspace

theorem iSupIndep_eigenspace_of_commute_of_torsionfree {R M ι κ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    (T : ι → Module.End R M) (hcomm : ∀ i j, T i * T j = T j * T i)
    (χ : κ → ι → R) (hsep : Pairwise fun a b => ∃ i, χ a i ≠ χ b i) :
    iSupIndep (fun a : κ => ⨅ i, LinearMap.ker (T i - χ a i • 1)) := by
  classical
  have _hcomm_used := hcomm
  have hV : ∀ (c : κ) (x : M),
      x ∈ (⨅ i, LinearMap.ker (T i - χ c i • 1)) ↔ ∀ i, T i x = χ c i • x := by
    intro c x
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have key : ∀ s : Finset κ, ∀ (v : κ → M) (a : κ → R),
      (∀ c ∈ s, v c ∈ (⨅ i, LinearMap.ker (T i - χ c i • 1))) →
      (∀ c ∈ s, a c ≠ 0) →
      (∑ c ∈ s, a c • v c = 0) → ∀ c ∈ s, v c = 0 := by
    intro s
    refine s.strongInductionOn ?_
    intro s ih v a hmem hne hrel
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb, hvb⟩ := hcon
    by_cases hex : ∃ p ∈ s, p ≠ b
    · obtain ⟨p, hp, hpb⟩ := hex
      obtain ⟨i, hi⟩ : ∃ i, χ p i ≠ χ b i := hsep hpb
      have hrel' : (∑ c ∈ s, (a c * (χ c i - χ b i)) • v c) = 0 := by
        have hterm : ∀ c ∈ s,
            (T i - χ b i • 1) (a c • v c) = (a c * (χ c i - χ b i)) • v c := by
          intro c hc
          have hcv : T i (v c) = χ c i • v c := (hV c (v c)).mp (hmem c hc) i
          have hQv : (T i - χ b i • 1) (v c) = (χ c i - χ b i) • v c := by
            rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hcv, sub_smul]
          rw [map_smul, hQv, smul_smul]
        have h0 : (T i - χ b i • 1) (∑ c ∈ s, a c • v c) = 0 := by rw [hrel, map_zero]
        rw [map_sum] at h0
        rw [Finset.sum_congr rfl hterm] at h0
        exact h0
      let s₁ : Finset κ := s.filter (fun c => χ c i ≠ χ b i)
      let s₂ : Finset κ := s.filter (fun c => ¬ (χ c i ≠ χ b i))
      have hb_not_s₁ : b ∉ s₁ := by
        change b ∉ s.filter (fun c => χ c i ≠ χ b i)
        intro h
        exact (Finset.mem_filter.mp h).2 rfl
      have hp_not_s₂ : p ∉ s₂ := by
        change p ∉ s.filter (fun c => ¬ (χ c i ≠ χ b i))
        intro h
        exact (Finset.mem_filter.mp h).2 hi
      have hs₁_ssub : s₁ ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨b, hb, hb_not_s₁⟩
      have hs₂_ssub : s₂ ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨p, hp, hp_not_s₂⟩
      have hrel1 : (∑ c ∈ s₁, (a c * (χ c i - χ b i)) • v c) = 0 := by
        apply Eq.trans _ hrel'
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro c hc hcnot
        have hci : χ c i = χ b i := by
          by_contra hne'
          exact hcnot (Finset.mem_filter.mpr ⟨hc, hne'⟩)
        rw [hci]; simp
      have hzero₁ : ∀ c ∈ s₁, v c = 0 :=
        ih s₁ hs₁_ssub v (fun c => a c * (χ c i - χ b i))
          (fun c hc => hmem c (Finset.mem_of_mem_filter c hc))
          (fun c hc => by
            have hc' := Finset.mem_filter.mp (show c ∈ s.filter (fun c => χ c i ≠ χ b i) from hc)
            exact mul_ne_zero (hne c hc'.1) (sub_ne_zero.mpr hc'.2))
          hrel1
      have hzero1sum : (∑ c ∈ s₁, a c • v c) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        rw [hzero₁ c hc, smul_zero]
      have hsplit : (∑ c ∈ s₁, a c • v c) + (∑ c ∈ s₂, a c • v c) = ∑ c ∈ s, a c • v c :=
        Finset.sum_filter_add_sum_filter_not s (fun c => χ c i ≠ χ b i) (fun c => a c • v c)
      have hrel2 : (∑ c ∈ s₂, a c • v c) = 0 := by
        rw [hrel] at hsplit
        rw [hzero1sum, zero_add] at hsplit
        exact hsplit
      have hzero₂ : ∀ c ∈ s₂, v c = 0 :=
        ih s₂ hs₂_ssub v a
          (fun c hc => hmem c (Finset.mem_of_mem_filter c hc))
          (fun c hc => hne c (Finset.mem_of_mem_filter c hc))
          hrel2
      have hb_s₂ : b ∈ s₂ := by
        change b ∈ s.filter (fun c => ¬ (χ c i ≠ χ b i))
        exact Finset.mem_filter.mpr ⟨hb, by simp⟩
      exact hvb (hzero₂ b hb_s₂)
    · push Not at hex
      have hs : s = {b} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hb, hex⟩
      have hsingle : a b • v b = 0 := by
        have hh := hrel
        rw [hs, Finset.sum_singleton] at hh
        exact hh
      rcases smul_eq_zero.mp hsingle with h | h
      · exact hne b hb h
      · exact hvb h
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hv0 m hm
  exact key s v (fun _ => 1) hv (fun c _ => one_ne_zero) (by simpa using hv0) m hm

end Commons.LinearAlgebra.Eigenspace
