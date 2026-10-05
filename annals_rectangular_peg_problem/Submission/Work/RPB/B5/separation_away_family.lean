import Mathlib
import Submission.Work.RPB.B4.periodic_reduce
import Submission.Work.RPB.B5.pos_min_of_compact

/-!
# B5: uniform separation, uniformly in a family parameter

Let `γ : ℝ → ℝ → ℂ` be a family of curves, jointly continuous, `2π`-periodic in the second
variable, and injective modulo `2π` in the second variable for every `τ ∈ [0,1]`:
`γ τ t = γ τ t'` forces `t' = t + 2π m` for some `m : ℤ`.  Then for every `0 < δ ≤ π` there is
a single `η > 0` with

`η ≤ ‖γ τ (t + s) - γ τ t‖`  for all `τ ∈ [0,1]`, all `t : ℝ` and all `s ∈ [δ, π]`.

This is a compactness statement, uniform in `τ`.  On the compact set
`K = [0,1] × [0,2π] × [δ,π]` the continuous function `(τ,t,s) ↦ ‖γ τ (t+s) - γ τ t‖` is
*strictly positive*: if it vanished, injectivity would give `s = 2π m`, impossible because
`0 < δ ≤ s ≤ π < 2π`.  Hence it has a positive minimum `η` on `K`
(`Work.RPB.B5.pos_min_of_compact`).  An arbitrary `t` is reduced to its representative
`t' ∈ [0,2π]` using the `2π`-periodicity in `t` (`Work.RPB.B4.periodic_reduce`), which does not
change the chord length because it preserves both `γ τ t` and `γ τ (t+s)`.
-/

namespace Work.RPB.B5

theorem separation_away_family (γ : ℝ → ℝ → ℂ)
    (hcont : Continuous (fun z : ℝ × ℝ => γ z.1 z.2))
    (hper : ∀ τ t, γ τ (t + 2 * Real.pi) = γ τ t)
    (hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', γ τ t = γ τ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    ∃ η > 0, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ s ∈ Set.Icc δ Real.pi,
      η ≤ ‖γ τ (t + s) - γ τ t‖ := by
  -- The separation function `(τ,t,s) ↦ ‖γ τ (t+s) - γ τ t‖` is continuous.
  have hcontf : Continuous (fun p : ℝ × ℝ × ℝ => ‖γ p.1 (p.2.1 + p.2.2) - γ p.1 p.2.1‖) := by
    apply Continuous.norm
    apply Continuous.sub
    · have h1 : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1 + p.2.2)) := by fun_prop
      exact hcont.comp h1
    · have h1 : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) := by fun_prop
      exact hcont.comp h1
  -- The fundamental domain is compact.
  have hKc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc δ Real.pi)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKne :
      (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc δ Real.pi)).Nonempty := by
    refine ⟨(0, 0, δ), ?_⟩
    refine ⟨⟨le_refl 0, zero_le_one⟩, ⟨⟨le_refl 0, by positivity⟩, ⟨le_refl δ, hδπ⟩⟩⟩
  -- Strict positivity of the chord length on the fundamental domain, from injectivity mod `2π`.
  have hpos : ∀ p ∈ (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc δ Real.pi)),
      0 < ‖γ p.1 (p.2.1 + p.2.2) - γ p.1 p.2.1‖ := by
    intro p hp
    have hp1 : p.1 ∈ Set.Icc (0:ℝ) 1 := hp.1
    have hp2 : p.2.1 ∈ Set.Icc (0:ℝ) (2 * Real.pi) := hp.2.1
    have hp3 : p.2.2 ∈ Set.Icc δ Real.pi := hp.2.2
    have hp10 := (Set.mem_Icc.mp hp1).1
    have hp11 := (Set.mem_Icc.mp hp1).2
    have hp21 := (Set.mem_Icc.mp hp2).2
    have hp30 := (Set.mem_Icc.mp hp3).1
    have hp31 := (Set.mem_Icc.mp hp3).2
    rw [norm_pos_iff]
    intro hzero
    have hγeq : γ p.1 (p.2.1 + p.2.2) = γ p.1 p.2.1 := sub_eq_zero.mp hzero
    obtain ⟨m, hm⟩ := hinj p.1 ⟨hp10, hp11⟩ p.2.1 (p.2.1 + p.2.2) hγeq.symm
    have hseq : p.2.2 = 2 * Real.pi * (m : ℝ) := by linarith
    have hspos : 0 < p.2.2 := lt_of_lt_of_le hδ hp30
    have hslt : p.2.2 < 2 * Real.pi := lt_of_le_of_lt hp31 (lt_two_mul_self Real.pi_pos)
    have hmpos : (0:ℤ) < m := by
      have : (0:ℝ) < (m:ℝ) := by
        have h : (0:ℝ) < 2 * Real.pi * (m:ℝ) := by rw [← hseq]; exact hspos
        nlinarith [Real.pi_pos]
      exact_mod_cast this
    have hmlt : m < (1:ℤ) := by
      have : (m:ℝ) < 1 := by
        have h : 2 * Real.pi * (m:ℝ) < 2 * Real.pi := by rw [← hseq]; exact hslt
        nlinarith [Real.pi_pos]
      exact_mod_cast this
    omega
  obtain ⟨η, hηpos, hη⟩ := pos_min_of_compact hKc hKne
    (fun p : ℝ × ℝ × ℝ => ‖γ p.1 (p.2.1 + p.2.2) - γ p.1 p.2.1‖) hcontf.continuousOn hpos
  refine ⟨η, hηpos, ?_⟩
  intro τ hτ t s hs
  -- Reduce an arbitrary `t` to a representative `t' ∈ [0, 2π]`.
  obtain ⟨k, t', ht'Ico, ht_eq, ht_fe⟩ := Work.RPB.B4.periodic_reduce (γ τ) (hper τ) t
  rw [Set.mem_Ico] at ht'Ico
  have hmem :
      (τ, t', s) ∈ Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc δ Real.pi) :=
    ⟨hτ, ⟨⟨ht'Ico.1, le_of_lt ht'Ico.2⟩, hs⟩⟩
  have hle := hη (τ, t', s) hmem
  have hp : Function.Periodic (γ τ) (2 * Real.pi) := hper τ
  have hstep : γ τ (t + s) = γ τ (t' + s) := by
    have h1 : t + s = (t' + s) + k • (2 * Real.pi) := by rw [ht_eq]; ring
    rw [h1]
    exact (hp.zsmul k) (t' + s)
  have hval : ‖γ τ (t' + s) - γ τ t'‖ = ‖γ τ (t + s) - γ τ t‖ := by rw [hstep, ht_fe]
  rw [hval] at hle
  exact hle

end Work.RPB.B5
