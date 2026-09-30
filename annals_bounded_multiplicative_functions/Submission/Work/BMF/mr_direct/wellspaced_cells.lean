import Mathlib
import Submission.Work.BMF.mr_direct.integral_le_sum_cellSup
import Submission.Work.BMF.mr_direct.enum_sep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped BigOperators

namespace Work.BMF.mr_direct

noncomputable section

private lemma two_le_sub_of_same_parity {k l : ℤ} (hkl : k < l)
    (hpar : (Even k ∧ Even l) ∨ (Odd k ∧ Odd l)) : (2:ℝ) ≤ (l:ℝ) - (k:ℝ) := by
  have h2 : (2:ℤ) ≤ l - k := by
    have heven : Even (l - k) := by
      rcases hpar with ⟨hk, hl⟩ | ⟨hk, hl⟩
      · exact hl.sub hk
      · exact Odd.sub_odd hl hk
    have hpos : 0 < l - k := by omega
    obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp heven
    omega
  exact_mod_cast h2

private lemma sep_same_parity {k l : ℤ} {pk pl : ℝ}
    (hk : (k:ℝ) ≤ pk ∧ pk < (k:ℝ) + 1) (hl : (l:ℝ) ≤ pl ∧ pl < (l:ℝ) + 1)
    (hkl : k ≠ l) (hpar : (Even k ∧ Even l) ∨ (Odd k ∧ Odd l)) : 1 ≤ |pk - pl| := by
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have h2 : (2:ℝ) ≤ (l:ℝ) - (k:ℝ) := two_le_sub_of_same_parity hlt hpar
    have hplt : pk < pl := by linarith [hk.2, hl.1]
    rw [abs_of_neg (by linarith : pk - pl < 0)]
    linarith
  · have h2 : (2:ℝ) ≤ (k:ℝ) - (l:ℝ) :=
      two_le_sub_of_same_parity hgt (by
        rcases hpar with ⟨hk', hl'⟩ | ⟨hk', hl'⟩
        · exact Or.inl ⟨hl', hk'⟩
        · exact Or.inr ⟨hl', hk'⟩)
    have hplk : pl < pk := by linarith [hl.2, hk.1]
    rw [abs_of_pos (by linarith : 0 < pk - pl)]
    linarith

/-- Cell well-spaced reduction (statement from `_stmt_check_bmf.lean`). -/
lemma wellspaced_cells (f : ℝ → ℝ) (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    {T₀ T : ℝ} (hT : T₀ ≤ T) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Set.Icc T₀ T) :
    ∃ (R₁ R₂ : ℕ) (t₁ : Fin R₁ → ℝ) (t₂ : Fin R₂ → ℝ),
      (∀ i, t₁ i ∈ U) ∧ (∀ i, t₂ i ∈ U) ∧
      (∀ i j, i ≠ j → 1 ≤ |t₁ i - t₁ j|) ∧ (∀ i j, i ≠ j → 1 ≤ |t₂ i - t₂ j|) ∧
      (∫ x in U, f x) ≤ 2 * ((∑ i, f (t₁ i)) + (∑ i, f (t₂ i))) := by
  classical
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := T₀) (b := T)).exists_bound_of_continuousOn hf.continuousOn
  have hMle : ∀ x ∈ Set.Icc T₀ T, f x ≤ M := by
    intro x hx
    have h := hM x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)] at h
    exact h
  set cell : ℤ → Set ℝ := fun k => Set.Ico (k : ℝ) ((k : ℝ) + 1) with hcell
  set E : ℤ → ℝ := fun k => sSup (f '' (U ∩ cell k)) with hE
  set K : Finset ℤ := Finset.Icc (⌊T₀⌋ - 1) (⌊T⌋ + 1) with hK
  set Ssum : ℝ := ∑ k ∈ K, E k with hSsumdef
  have hEeq : ∀ k, E k = sSup (f '' (U ∩ cell k)) := by
    intro k; simp only [hE]
  have hE_nonneg : ∀ k, 0 ≤ E k := by
    intro k
    rw [hEeq k]
    exact Real.sSup_nonneg (by rintro y ⟨x, _, rfl⟩; exact hnn x)
  have hE_zero : ∀ k, ¬ (U ∩ cell k).Nonempty → E k = 0 := by
    intro k hk
    rw [hEeq k]
    have hempty : U ∩ cell k = ∅ := Set.not_nonempty_iff_eq_empty.mp hk
    rw [hempty, Set.image_empty, Real.sSup_empty]
  have hint : (∫ x in U, f x) ≤ Ssum := by
    simp only [hSsumdef, hK, hE, hcell]
    exact integral_le_sum_cellSup f hf hnn hT hU hsub
  by_cases hSsum0 : Ssum = 0
  · refine ⟨0, 0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · have h0 : (∫ x in U, f x) ≤ 0 := by rw [← hSsum0]; exact hint
      simpa using h0
  · have hSsum_nonneg : 0 ≤ Ssum := by
      rw [hSsumdef]; exact Finset.sum_nonneg (fun k _ => hE_nonneg k)
    have hSsumpos : 0 < Ssum := lt_of_le_of_ne hSsum_nonneg (Ne.symm hSsum0)
    set K' : Finset ℤ := K.filter (fun k => (U ∩ cell k).Nonempty) with hK'
    have hK'_mem : ∀ k, k ∈ K' ↔ k ∈ K ∧ (U ∩ cell k).Nonempty := by
      intro k; rw [hK']; exact Finset.mem_filter
    set Ke : Finset ℤ := K'.filter (fun k => Even k) with hKe
    have hKe_mem : ∀ k, k ∈ Ke ↔ k ∈ K' ∧ Even k := by
      intro k; rw [hKe]; exact Finset.mem_filter
    set Ko : Finset ℤ := K'.filter (fun k => ¬ Even k) with hKo
    have hKo_mem : ∀ k, k ∈ Ko ↔ k ∈ K' ∧ ¬ Even k := by
      intro k; rw [hKo]; exact Finset.mem_filter
    set N : ℕ := K'.card with hN
    have hNpos : 0 < N := by
      rw [hN, Finset.card_pos]
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      refine hSsum0 ?_
      rw [hSsumdef]
      refine Finset.sum_eq_zero (fun k hk => ?_)
      apply hE_zero
      intro hne
      have hmem : k ∈ K' := (hK'_mem k).mpr ⟨hk, hne⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty k hmem
    set δ : ℝ := Ssum / (4 * N) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      apply div_pos hSsumpos
      have hNpos' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
      linarith
    have hQ : ∀ k ∈ K', ∃ x ∈ U ∩ cell k, E k - δ < f x := by
      intro k hk
      have hne : (U ∩ cell k).Nonempty := ((hK'_mem k).mp hk).2
      obtain ⟨x0, hx0⟩ := hne
      have hne' : (f '' (U ∩ cell k)).Nonempty := ⟨f x0, x0, hx0, rfl⟩
      have hbdd : BddAbove (f '' (U ∩ cell k)) := by
        refine ⟨M, ?_⟩
        rintro y ⟨x, hx, rfl⟩
        exact hMle x (hsub hx.1)
      have hlt' : E k - δ < sSup (f '' (U ∩ cell k)) := by
        rw [← hEeq k]; linarith [hδpos]
      obtain ⟨y, hy, hylt⟩ := (lt_csSup_iff hbdd hne').mp hlt'
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, hx, hylt⟩
    set p : ℤ → ℝ := (fun k => if hk : k ∈ K' then Classical.choose (hQ k hk) else 0) with hpdef
    have hp_spec : ∀ k (hk : k ∈ K'), p k ∈ U ∩ cell k ∧ E k - δ < f (p k) := by
      intro k hk
      have hpk : p k = Classical.choose (hQ k hk) := by
        simp only [hpdef, dite_eq_left hk]
      rw [hpk]
      exact Classical.choose_spec (hQ k hk)
    have hp_cell : ∀ k (hk : k ∈ K'), p k ∈ cell k := fun k hk => (hp_spec k hk).1.2
    have hp_Ico : ∀ k (hk : k ∈ K'), (k:ℝ) ≤ p k ∧ p k < (k:ℝ) + 1 := by
      intro k hk
      have h := hp_cell k hk
      rw [hcell, Set.mem_Ico] at h
      exact h
    have hmem_even : ∀ k ∈ Ke, p k ∈ U := fun k hk => (hp_spec k ((hKe_mem k).mp hk).1).1.1
    have hmem_odd : ∀ k ∈ Ko, p k ∈ U := fun k hk => (hp_spec k ((hKo_mem k).mp hk).1).1.1
    have hsep_even : ∀ k ∈ Ke, ∀ l ∈ Ke, k ≠ l → 1 ≤ |p k - p l| := by
      intro k hk l hl hkl
      exact sep_same_parity (hp_Ico k ((hKe_mem k).mp hk).1) (hp_Ico l ((hKe_mem l).mp hl).1)
        hkl (Or.inl ⟨((hKe_mem k).mp hk).2, ((hKe_mem l).mp hl).2⟩)
    have hsep_odd : ∀ k ∈ Ko, ∀ l ∈ Ko, k ≠ l → 1 ≤ |p k - p l| := by
      intro k hk l hl hkl
      exact sep_same_parity (hp_Ico k ((hKo_mem k).mp hk).1) (hp_Ico l ((hKo_mem l).mp hl).1)
        hkl (Or.inr ⟨Int.not_even_iff_odd.mp ((hKo_mem k).mp hk).2,
                     Int.not_even_iff_odd.mp ((hKo_mem l).mp hl).2⟩)
    obtain ⟨R₁, t₁, ht₁mem, ht₁sep, ht₁sum⟩ :=
      enum_sep (p := p) (S := Ke) (U := U) (f := f) hsep_even hmem_even
    obtain ⟨R₂, t₂, ht₂mem, ht₂sep, ht₂sum⟩ :=
      enum_sep (p := p) (S := Ko) (U := U) (f := f) hsep_odd hmem_odd
    have hUnion : Ke ∪ Ko = K' := by
      ext k
      rw [Finset.mem_union, hKe_mem k, hKo_mem k]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hk
        rcases Int.even_or_odd k with h | h
        · exact Or.inl ⟨hk, h⟩
        · exact Or.inr ⟨hk, Int.not_even_iff_odd.mpr h⟩
    have hDisj : Disjoint Ke Ko := by
      rw [hKe, hKo, Finset.disjoint_filter]
      intro x hx hev hne
      exact hne hev
    have hsumE : ∑ k ∈ Ke, E k + ∑ k ∈ Ko, E k = Ssum := by
      rw [← Finset.sum_union hDisj, hUnion, hSsumdef]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k hkK hkK' =>
        hE_zero k (fun hne => hkK' ((hK'_mem k).mpr ⟨hkK, hne⟩)))
    have hcard : Ke.card + Ko.card = N := by
      rw [← Finset.card_union_of_disjoint hDisj, hUnion, hN]
    have hA : (∑ k ∈ Ke, E k) - (Ke.card : ℝ) * δ ≤ ∑ k ∈ Ke, f (p k) := by
      have h1 : ∑ k ∈ Ke, (E k - δ) ≤ ∑ k ∈ Ke, f (p k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact le_of_lt (hp_spec k ((hKe_mem k).mp hk).1).2
      rwa [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have hB : (∑ k ∈ Ko, E k) - (Ko.card : ℝ) * δ ≤ ∑ k ∈ Ko, f (p k) := by
      have h1 : ∑ k ∈ Ko, (E k - δ) ≤ ∑ k ∈ Ko, f (p k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact le_of_lt (hp_spec k ((hKo_mem k).mp hk).1).2
      rwa [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have hleft : (∑ k ∈ Ke, E k - (Ke.card : ℝ) * δ) + (∑ k ∈ Ko, E k - (Ko.card : ℝ) * δ)
        = Ssum - Ssum / 4 := by
      have hNnz : (N : ℝ) ≠ 0 := by
        have : (0:ℝ) < N := by exact_mod_cast hNpos
        exact ne_of_gt this
      have hNδ : ((Ke.card : ℝ) + (Ko.card : ℝ)) * δ = Ssum / 4 := by
        rw [← Nat.cast_add, hcard, hδdef]
        field_simp
      linarith [hsumE, hNδ]
    have htot : Ssum - Ssum / 4 ≤ ∑ k ∈ Ke, f (p k) + ∑ k ∈ Ko, f (p k) := by
      linarith [hA, hB, hleft]
    have hmain : Ssum ≤ 2 * (∑ k ∈ Ke, f (p k) + ∑ k ∈ Ko, f (p k)) := by
      nlinarith [htot, hSsum_nonneg]
    exact ⟨R₁, R₂, t₁, t₂, ht₁mem, ht₂mem, ht₁sep, ht₂sep, by
      rw [ht₁sum, ht₂sum]; exact le_trans hint hmain⟩

end

end Work.BMF.mr_direct
