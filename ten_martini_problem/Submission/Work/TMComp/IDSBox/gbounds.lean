import Mathlib

namespace Work.TMComp.IDSBox

theorem gbounds (g : ℝ → ℝ) (n : ℕ) (hcont : Continuous g) (hmono : Antitone g)
    (htop : Filter.Tendsto g Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto g Filter.atBot (nhds (n : ℝ))) :
    (∀ X : ℝ, g X ∈ Set.Icc (0 : ℝ) (n : ℝ)) ∧
    (∀ m : ℕ, m < n → ∃ E : ℝ, g E = (m : ℝ) + 1/2) := by
  -- Lower bound: g ≥ 0 everywhere, using the limit at +∞ and antitonicity.
  have h0 : ∀ X, 0 ≤ g X := by
    intro X
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    have hmem : Set.Ioo ((0:ℝ) - ε) ((0:ℝ) + ε) ∈ nhds (0:ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp (htop.eventually hmem)
    by_cases hXb : b ≤ X
    · have : (0:ℝ) - ε < g X := (hb X hXb).1
      linarith
    · have hXb' : X ≤ b := le_of_lt (lt_of_not_ge hXb)
      have hgb : g b ≤ g X := hmono hXb'
      have : (0:ℝ) - ε < g b := (hb b le_rfl).1
      linarith
  -- Upper bound: g ≤ n everywhere, using the limit at -∞ and antitonicity.
  have hn : ∀ X, g X ≤ (n:ℝ) := by
    intro X
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    have hmem : Set.Ioo ((n:ℝ) - ε) ((n:ℝ) + ε) ∈ nhds (n:ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp (hbot.eventually hmem)
    by_cases hXb : b ≤ X
    · have : g X ≤ g b := hmono hXb
      have : g b < (n:ℝ) + ε := (hb b le_rfl).2
      linarith
    · have hXb' : X ≤ b := le_of_lt (lt_of_not_ge hXb)
      have : g X < (n:ℝ) + ε := (hb X hXb').2
      linarith
  refine ⟨fun X => ⟨h0 X, hn X⟩, ?_⟩
  -- Intermediate values strictly between 0 and n are attained, by IVT.
  intro m hm
  have hmn : (m:ℝ) + 1 ≤ (n:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hm)
  have hcpos : (0:ℝ) < (m:ℝ) + 1/2 := by
    have : (0:ℝ) ≤ (m:ℝ) := by positivity
    linarith
  have hclt : (m:ℝ) + 1/2 < (n:ℝ) := by linarith
  have hmemA : Set.Iio ((m:ℝ) + 1/2) ∈ nhds (0:ℝ) :=
    IsOpen.mem_nhds isOpen_Iio (by simpa using hcpos)
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (htop.eventually hmemA)
  have hAlt : g A < (m:ℝ) + 1/2 := hA A le_rfl
  have hmemB : Set.Ioi ((m:ℝ) + 1/2) ∈ nhds (n:ℝ) :=
    IsOpen.mem_nhds isOpen_Ioi (by simpa using hclt)
  obtain ⟨B, hB⟩ := Filter.eventually_atBot.mp (hbot.eventually hmemB)
  have hBgt : (m:ℝ) + 1/2 < g B := hB B le_rfl
  have hIVT := IsPreconnected.intermediate_value (isPreconnected_univ) (Set.mem_univ A)
    (Set.mem_univ B) hcont.continuousOn
  obtain ⟨E, -, hE⟩ := hIVT ⟨le_of_lt hAlt, le_of_lt hBgt⟩
  exact ⟨E, hE⟩

end Work.TMComp.IDSBox
