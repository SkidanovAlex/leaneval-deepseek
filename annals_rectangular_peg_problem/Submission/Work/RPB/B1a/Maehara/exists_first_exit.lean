import Mathlib
import Submission.Work.RPB.B1a.Maehara.Defs
import Submission.Work.RPB.B1a.Maehara.interior_RectC

/-!
# The first exit of a path from the Maehara rectangle

Let `p : ℝ → ℂ` be a continuous path with `p 0 ∈ RectC = [-1,1] × [-2,2]` and `p 1 ∉ RectC`.
Then there is a first time `t₀ ∈ [0,1]` at which `p` leaves the rectangle: `p t₀` lies on the
union `BdC` of the four supporting lines of the rectangle, and the whole initial piece
`p '' [0, t₀]` is contained in `RectC`.

The proof takes `t₀` to be the infimum of the times at which `p` has already left `RectC`.  Every
`s ≥ 0` strictly below `t₀` is not such a time, so `p s ∈ RectC`; hence `p t₀ ∈ RectC` since
`RectC` is closed.  On the other hand exit times accumulate at `t₀` from above, so continuity
forces `p t₀ ∉ interior RectC`; a point of the rectangle which is not interior lies on one of the
four supporting lines.
-/

namespace Work.RPB.B1a.Maehara

open Set Metric

/-- A point of `RectC` which is not an interior point of `RectC` lies on one of the four
supporting lines of the rectangle. -/
theorem mem_BdC_of_mem_RectC_notMem_interior {z : ℂ} (hz : z ∈ RectC)
    (hz' : z ∉ interior RectC) : z ∈ BdC := by
  rw [mem_BdC]
  by_contra hcon
  simp only [not_or] at hcon
  apply hz'
  rw [interior_RectC, mem_RectC] at *
  exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hcon.1),
    lt_of_le_of_ne hz.2.1 hcon.2.1,
    lt_of_le_of_ne hz.2.2.1 (Ne.symm hcon.2.2.1),
    lt_of_le_of_ne hz.2.2.2 hcon.2.2.2⟩

theorem exists_first_exit (p : ℝ → ℂ) (hp : Continuous p) (h0 : p 0 ∈ RectC) (h1 : p 1 ∉ RectC) :
    ∃ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 1 ∧ p t₀ ∈ BdC ∧ ∀ s ∈ Set.Icc (0 : ℝ) t₀, p s ∈ RectC := by
  -- The set of times `s ≥ 0` at which `p` has already left the rectangle; its infimum is the
  -- first exit time.
  set A : Set ℝ := {s | 0 ≤ s ∧ p s ∉ RectC} with hA
  have hAne : A.Nonempty := ⟨(1 : ℝ), by rw [hA]; exact ⟨by norm_num, h1⟩⟩
  have hbdd : BddBelow A := ⟨0, fun s hs => by rw [hA] at hs; exact hs.1⟩
  set t₀ : ℝ := sInf A with ht₀
  have ht0_nonneg : 0 ≤ t₀ := by
    rw [ht₀]; exact le_csInf hAne (fun s hs => by rw [hA] at hs; exact hs.1)
  have ht0_le_one : t₀ ≤ 1 := by
    rw [ht₀]; exact csInf_le hbdd (by rw [hA]; exact ⟨by norm_num, h1⟩)
  -- `p` stays inside the rectangle strictly before `t₀` ...
  have hmem : ∀ s, s < t₀ → 0 ≤ s → p s ∈ RectC := by
    intro s hs h0s
    by_contra hns
    have hle : sInf A ≤ s := csInf_le hbdd (by rw [hA]; exact ⟨h0s, hns⟩)
    rw [← ht₀] at hle
    exact absurd hle (not_le.mpr hs)
  -- ... while exit times accumulate at `t₀` from above.
  have hfromabove : ∀ ε > 0, ∃ a ∈ A, a < t₀ + ε := by
    intro ε hε
    by_contra hc
    have hc' : ∀ b ∈ A, t₀ + ε ≤ b := by
      intro b hb
      by_contra hlt
      exact hc ⟨b, hb, not_le.mp hlt⟩
    have hle : t₀ + ε ≤ sInf A := le_csInf hAne hc'
    rw [← ht₀] at hle
    linarith
  -- The first exit time itself is still (in the closure of) the rectangle.
  have ht0_mem : p t₀ ∈ RectC := by
    rcases eq_or_lt_of_le ht0_nonneg with h | h
    · rw [← h]; exact h0
    · have hDclosed : IsClosed ({s : ℝ | 0 ≤ s} ∩ p ⁻¹' RectC) :=
        isClosed_Ici.inter (isClosed_RectC.preimage hp)
      have hsub : Ico (0 : ℝ) t₀ ⊆ ({s : ℝ | 0 ≤ s} ∩ p ⁻¹' RectC) := fun s hs =>
        ⟨hs.1, hmem s hs.2 hs.1⟩
      have hcl : t₀ ∈ closure (Ico (0 : ℝ) t₀) := by
        rw [closure_Ico (a := 0) (b := t₀) (ne_of_lt h)]; exact ⟨le_of_lt h, le_rfl⟩
      have hmemD : t₀ ∈ ({s : ℝ | 0 ≤ s} ∩ p ⁻¹' RectC) := by
        rw [← hDclosed.closure_eq]
        exact closure_mono hsub hcl
      exact hmemD.2
  -- But it is not an interior point of the rectangle: nearby exit times would contradict
  -- continuity.
  have ht0_notint : p t₀ ∉ interior RectC := by
    intro hint
    have hnhds : p ⁻¹' interior RectC ∈ nhds t₀ :=
      hp.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)
    rw [Metric.mem_nhds_iff] at hnhds
    obtain ⟨ε, hεpos, hε⟩ := hnhds
    obtain ⟨a, haA, ha_lt⟩ := hfromabove ε hεpos
    have ha_ge : t₀ ≤ a := by
      have := csInf_le hbdd haA
      rwa [← ht₀] at this
    have hdist : dist a t₀ < ε := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    have hpa : p a ∈ interior RectC := hε (by rw [Metric.mem_ball]; exact hdist)
    rw [hA] at haA
    exact haA.2 (interior_subset hpa)
  exact ⟨t₀, ⟨ht0_nonneg, ht0_le_one⟩,
    mem_BdC_of_mem_RectC_notMem_interior ht0_mem ht0_notint, fun s hs => by
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h]; exact ht0_mem
      · exact hmem s h hs.1⟩

end Work.RPB.B1a.Maehara
