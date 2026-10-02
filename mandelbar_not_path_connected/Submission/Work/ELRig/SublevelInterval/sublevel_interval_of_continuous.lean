import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig.SublevelInterval

theorem sublevel_interval_of_continuous {g : ℝ → ℝ} {ρ x₀ : ℝ}
    (hg : Continuous g) (hx : g x₀ < ρ)
    (hbdd : ∃ R : ℝ, ∀ s : ℝ, R ≤ |s| → ρ ≤ g s)
    (htwo : ∀ a b c : ℝ, g a = ρ → g b = ρ → g c = ρ → a = b ∨ a = c ∨ b = c) :
    ∃ s₁ s₂ : ℝ, s₁ < x₀ ∧ x₀ < s₂ ∧
      (∀ s : ℝ, g s < ρ → s ∈ Set.Icc s₁ s₂) ∧
      (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → g s < ρ) ∧
      g s₁ = ρ ∧ g s₂ = ρ := by
  set S : Set ℝ := {s : ℝ | g s < ρ} with hSdef
  have hSmem : ∀ s : ℝ, s ∈ S ↔ g s < ρ := by
    intro s; rw [hSdef]; simp
  have hSopen : IsOpen S := by
    rw [hSdef]; exact isOpen_Iio.preimage hg
  have hSne : S.Nonempty := ⟨x₀, (hSmem x₀).mpr hx⟩
  obtain ⟨R, hR⟩ := hbdd
  have hSabs : ∀ s ∈ S, |s| < R := by
    intro s hs
    have hs' : g s < ρ := (hSmem s).mp hs
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd (hR s hcon) (not_le.mpr hs')
  have hSbddAbove : BddAbove S := ⟨R, fun s hs => le_of_lt (abs_lt.mp (hSabs s hs)).2⟩
  have hSbddBelow : BddBelow S := ⟨-R, fun s hs => le_of_lt (abs_lt.mp (hSabs s hs)).1⟩
  have hS1notmem : sInf S ∉ S := by
    intro hmem
    obtain ⟨ε, hεpos, hsub⟩ := Metric.isOpen_iff.mp hSopen (sInf S) hmem
    have hmem2 : sInf S - ε/2 ∈ S := hsub (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show sInf S - ε/2 - sInf S = -(ε/2) by ring]
      rw [abs_neg, abs_of_pos (by linarith)]
      linarith)
    have hle := csInf_le hSbddBelow hmem2
    linarith
  have hS2notmem : sSup S ∉ S := by
    intro hmem
    obtain ⟨ε, hεpos, hsub⟩ := Metric.isOpen_iff.mp hSopen (sSup S) hmem
    have hmem2 : sSup S + ε/2 ∈ S := hsub (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show sSup S + ε/2 - sSup S = ε/2 by ring]
      rw [abs_of_pos (by linarith)]
      linarith)
    have hle := le_csSup hSbddAbove hmem2
    linarith
  have hST : S ⊆ {s : ℝ | g s ≤ ρ} := fun s hs => le_of_lt ((hSmem s).mp hs)
  have hgs1 : g (sInf S) = ρ := by
    apply le_antisymm
    · have hcl : sInf S ∈ closure S := csInf_mem_closure hSne hSbddBelow
      have hclosed : IsClosed {s : ℝ | g s ≤ ρ} := isClosed_le hg continuous_const
      have hmem : sInf S ∈ closure {s : ℝ | g s ≤ ρ} := closure_mono hST hcl
      rw [hclosed.closure_eq] at hmem
      exact hmem
    · have : ¬ (g (sInf S) < ρ) := fun h => hS1notmem ((hSmem _).mpr h)
      exact not_lt.mp this
  have hgs2 : g (sSup S) = ρ := by
    apply le_antisymm
    · have hcl : sSup S ∈ closure S := csSup_mem_closure hSne hSbddAbove
      have hclosed : IsClosed {s : ℝ | g s ≤ ρ} := isClosed_le hg continuous_const
      have hmem : sSup S ∈ closure {s : ℝ | g s ≤ ρ} := closure_mono hST hcl
      rw [hclosed.closure_eq] at hmem
      exact hmem
    · have : ¬ (g (sSup S) < ρ) := fun h => hS2notmem ((hSmem _).mpr h)
      exact not_lt.mp this
  have hs1x0 : sInf S < x₀ := by
    have hxS : x₀ ∈ S := (hSmem x₀).mpr hx
    exact lt_of_le_of_ne (csInf_le hSbddBelow hxS) (fun h => hS1notmem (by rw [h]; exact hxS))
  have hx0s2 : x₀ < sSup S := by
    have hxS : x₀ ∈ S := (hSmem x₀).mpr hx
    exact lt_of_le_of_ne (le_csSup hSbddAbove hxS) (fun h => hS2notmem (by rw [← h]; exact hxS))
  have hs12 : sInf S < sSup S := lt_trans hs1x0 hx0s2
  refine ⟨sInf S, sSup S, hs1x0, hx0s2, ?_, ?_, hgs1, hgs2⟩
  · intro s hs
    have hsS : s ∈ S := (hSmem s).mpr hs
    exact ⟨csInf_le hSbddBelow hsS, le_csSup hSbddAbove hsS⟩
  · intro s hs hne1 hne2
    rw [Set.mem_Icc] at hs
    obtain ⟨hs1, hs2⟩ := hs
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hgt | heq
    · have hs1lt : sInf S < s := lt_of_le_of_ne hs1 hne1.symm
      obtain ⟨a, haS, ha_lt⟩ := (csInf_lt_iff hSbddBelow hSne).mp hs1lt
      have haS' : g a < ρ := (hSmem a).mp haS
      have ha_le : a ≤ s := le_of_lt ha_lt
      obtain ⟨p, hp_mem, hp_eq⟩ := (intermediate_value_Ioo (a := a) (b := s) ha_le hg.continuousOn)
        (show ρ ∈ Set.Ioo (g a) (g s) from ⟨haS', hgt⟩)
      rw [Set.mem_Ioo] at hp_mem
      obtain ⟨hap, hps⟩ := hp_mem
      have hs_lt_s2 : s < sSup S := lt_of_le_of_ne hs2 hne2
      have hs1_le_a : sInf S ≤ a := csInf_le hSbddBelow haS
      have hs1_lt_p : sInf S < p := lt_of_le_of_lt hs1_le_a hap
      have hp_lt_s2 : p < sSup S := lt_trans hps hs_lt_s2
      rcases htwo (sInf S) p (sSup S) hgs1 hp_eq hgs2 with h | h | h
      · exact absurd h hs1_lt_p.ne
      · exact absurd h hs12.ne
      · exact absurd h hp_lt_s2.ne
    · have hgs : g s = ρ := heq.symm
      have hs_lt_s2 : s < sSup S := lt_of_le_of_ne hs2 hne2
      have hs1_lt_s : sInf S < s := lt_of_le_of_ne hs1 hne1.symm
      rcases htwo (sInf S) s (sSup S) hgs1 hgs hgs2 with h | h | h
      · exact absurd h hs1_lt_s.ne
      · exact absurd h hs12.ne
      · exact absurd h hs_lt_s2.ne

end Work.ELRig.SublevelInterval
