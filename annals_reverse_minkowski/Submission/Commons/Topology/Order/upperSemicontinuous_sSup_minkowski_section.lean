import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Semicontinuity.Basic

namespace Commons.Topology.Order

open Set

/-- Auxiliary general statement: if `K` is compact, `u` is upper semicontinuous on `K`,
`φ` is continuous, and `u ≥ 0` on `K`, then the "fiber supremum"
`z ↦ sSup {t | ∃ x ∈ K, φ x = z ∧ t = u x}` is upper semicontinuous. -/
theorem upperSemicontinuous_sSup_fiber
    {α : Type*} [TopologicalSpace α] [T1Space α]
    {K : Set α} (hK : IsCompact K)
    (u φ : α → ℝ) (hu : UpperSemicontinuousOn u K) (hφ : Continuous φ)
    (hu0 : ∀ x ∈ K, 0 ≤ u x) :
    UpperSemicontinuous fun z : ℝ => sSup {t : ℝ | ∃ x ∈ K, φ x = z ∧ t = u x} := by
  classical
  have hbdd : BddAbove (u '' K) := hu.bddAbove_of_isCompact hK
  have hbddS : ∀ z : ℝ, BddAbove {t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x} := by
    intro z
    apply BddAbove.mono _ hbdd
    rintro t ⟨x, hxK, -, rfl⟩
    exact ⟨x, hxK, rfl⟩
  have hnn : ∀ z : ℝ, 0 ≤ sSup {t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x} := by
    intro z
    rcases Set.eq_empty_or_nonempty {t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x} with h | h
    · rw [h]; simp [Real.sSup_def]
    · obtain ⟨t, ht⟩ := h
      have ht0 : 0 ≤ t := by rcases ht with ⟨x, hxK, -, rfl⟩; exact hu0 x hxK
      exact le_trans ht0 (le_csSup (hbddS z) ht)
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c ≤ 0
  · have hpre : (fun z : ℝ => sSup {t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x}) ⁻¹' Ici c
        = univ := by
      ext z
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact le_trans hc (hnn z)
    rw [hpre]
    exact isClosed_univ
  · push_neg at hc
    have hset : (fun z : ℝ => sSup {t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x}) ⁻¹' Ici c
        = φ '' (K ∩ u ⁻¹' Ici c) := by
      ext z
      rw [mem_preimage, mem_Ici, mem_image]
      constructor
      · intro hz
        have hne : ({t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x}).Nonempty := by
          rcases Set.eq_empty_or_nonempty ({t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x}) with h | h
          · rw [h] at hz; rw [Real.sSup_def] at hz; simp at hz; linarith
          · exact h
        obtain ⟨_, x, hxK, hφx, _⟩ := hne
        have hAne : (K ∩ φ ⁻¹' {z}).Nonempty := ⟨x, hxK, by simpa using hφx⟩
        have hAcomp : IsCompact (K ∩ φ ⁻¹' {z}) :=
          hK.inter_right (isClosed_singleton.preimage hφ)
        obtain ⟨y, hyA, hymax⟩ := (hu.mono inter_subset_left).exists_isMaxOn hAne hAcomp
        have hyK : y ∈ K := hyA.1
        have hyz : φ y = z := by simpa using hyA.2
        have hub : sSup {t : ℝ | ∃ x, x ∈ K ∧ φ x = z ∧ t = u x} ≤ u y := by
          apply csSup_le
          · exact ⟨u y, y, hyK, hyz, rfl⟩
          · rintro t ⟨w, hwK, hwφ, rfl⟩
            exact hymax ⟨hwK, by simpa using hwφ⟩
        exact ⟨y, ⟨hyK, le_trans hz hub⟩, hyz⟩
      · rintro ⟨x, hx, hxz⟩
        rw [← hxz]
        exact le_trans hx.2 (le_csSup (hbddS (φ x)) ⟨x, hx.1, rfl, rfl⟩)
    rw [hset]
    exact (hu.isCompact_inter_preimage_Ici hK c).image hφ |>.isClosed

theorem upperSemicontinuous_sSup_minkowski_section
    (g F G : ℝ → ℝ) (hg : Continuous g) (hgmono : Monotone g) (hg0 : ∀ t : ℝ, 0 ≤ g t)
    {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hFG : UpperSemicontinuousOn (fun p : ℝ × ℝ => F p.1 + G p.2) (K ×ˢ L))
    (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) :
    UpperSemicontinuous (fun z : ℝ => sSup {t : ℝ | ∃ a ∈ K, ∃ b ∈ L,
      lam * a + (1 - lam) * b = z ∧ t = g (F a + G b)}) := by
  have hu : UpperSemicontinuousOn (fun p : ℝ × ℝ => g (F p.1 + G p.2)) (K ×ˢ L) := by
    exact hg.comp_upperSemicontinuousOn hFG hgmono
  have hu0 : ∀ p ∈ K ×ˢ L, 0 ≤ g (F p.1 + G p.2) := fun p _ => hg0 _
  have hmain : UpperSemicontinuous (fun z : ℝ => sSup {t : ℝ | ∃ p ∈ K ×ˢ L,
      lam * p.1 + (1 - lam) * p.2 = z ∧ t = g (F p.1 + G p.2)}) :=
    upperSemicontinuous_sSup_fiber (K := K ×ˢ L) (hK.prod hL)
      (fun p : ℝ × ℝ => g (F p.1 + G p.2)) (fun p : ℝ × ℝ => lam * p.1 + (1 - lam) * p.2)
      hu (by fun_prop) hu0
  have hfun : (fun z : ℝ => sSup {t : ℝ | ∃ a ∈ K, ∃ b ∈ L,
        lam * a + (1 - lam) * b = z ∧ t = g (F a + G b)})
      = (fun z : ℝ => sSup {t : ℝ | ∃ p ∈ K ×ˢ L,
        lam * p.1 + (1 - lam) * p.2 = z ∧ t = g (F p.1 + G p.2)}) := by
    funext z
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_prod]
    constructor
    · rintro ⟨a, ha, b, hb, hab, ht⟩
      exact ⟨(a, b), ⟨ha, hb⟩, hab, ht⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, hpz, ht⟩
      exact ⟨p.1, hp1, p.2, hp2, hpz, ht⟩
  rw [hfun]
  exact hmain

end Commons.Topology.Order