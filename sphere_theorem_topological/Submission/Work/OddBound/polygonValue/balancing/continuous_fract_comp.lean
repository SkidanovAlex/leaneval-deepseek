import Mathlib

namespace Work.OddBound.polygonValue.balancing

open Set Topology Filter

/-- **Periodisation of a two-variable map that is `1`-periodic in its second variable.**
If `G : X → ℝ → M` is continuous as a map on `X × ℝ` and satisfies `G x 1 = G x 0` for every
`x : X`, then `(x, s) ↦ G x (Int.fract s)` is continuous.

Proof.  The map `Int.fract : ℝ → ℝ` is discontinuous at the integers, so the composition is not
a composition of continuous maps.  The point is that the discontinuity at an integer `n` is
exactly compensated by the hypothesis `G x 1 = G x 0`: on the closed box
`X × [n, n+1]` one has
`G x (Int.fract t) = G x (t - n)`
for **every** `t ∈ [n, n+1]`.  Indeed for `t ∈ [n, n+1)` we have `⌊t⌋ = n`, hence
`Int.fract t = t - n`, while at `t = n + 1` the two sides are `G x 0` and `G x 1`.

Fix `(x₀, t₀)` and let `n = ⌊t₀⌋`, so `t₀ ∈ [n, n+1)`.  The open box
`U := X × (n-1, n+1)` is a neighbourhood of `(x₀, t₀)` and is covered by the two closed boxes
`A := X × [n-1, n]` and `B := X × [n, n+1]`.  On `A` our function agrees with the continuous map
`(x,t) ↦ G x (t - (n-1))`, on `B` with `(x,t) ↦ G x (t - n)`; pasting the two closed pieces
(`ContinuousOn.union_of_isClosed`) yields continuity on `A ∪ B ⊇ U`, hence at `(x₀, t₀)`. -/
theorem continuous_fract_comp {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    {G : X → ℝ → M} (hcont : Continuous (fun p : X × ℝ => G p.1 p.2))
    (hper : ∀ x : X, G x 1 = G x 0) :
    Continuous (fun p : X × ℝ => G p.1 (Int.fract p.2)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, t₀⟩
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (n : ℝ) ≤ t₀ ∧ t₀ < (n : ℝ) + 1 :=
    ⟨⌊t₀⌋, Int.floor_le t₀, Int.lt_floor_add_one t₀⟩
  -- The two affinely shifted continuous maps that agree with our map on the closed boxes.
  have hshiftA : Continuous (fun p : X × ℝ => G p.1 (p.2 - ((n : ℝ) - 1))) :=
    hcont.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const))
  have hshiftB : Continuous (fun p : X × ℝ => G p.1 (p.2 - (n : ℝ))) :=
    hcont.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const))
  have hAcl : IsClosed ((univ : Set X) ×ˢ Icc ((n : ℝ) - 1) (n : ℝ)) :=
    isClosed_univ.prod isClosed_Icc
  have hBcl : IsClosed ((univ : Set X) ×ˢ Icc (n : ℝ) ((n : ℝ) + 1)) :=
    isClosed_univ.prod isClosed_Icc
  -- On `X × [n-1, n]` the map equals `(x,t) ↦ G x (t - (n-1))`.
  have hAeq : EqOn (fun p : X × ℝ => G p.1 (Int.fract p.2))
      (fun p : X × ℝ => G p.1 (p.2 - ((n : ℝ) - 1)))
      ((univ : Set X) ×ˢ Icc ((n : ℝ) - 1) (n : ℝ)) := by
    rintro ⟨x, t⟩ ht
    simp only [mem_prod, mem_univ, true_and, mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    change G x (Int.fract t) = G x (t - ((n : ℝ) - 1))
    rcases lt_or_eq_of_le ht2 with hlt | heq
    · have hfloor : ⌊t⌋ = n - 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      have hfr : Int.fract t = t - ((n : ℝ) - 1) := by
        rw [← Int.self_sub_floor t, hfloor]
        push_cast
        ring
      rw [hfr]
    · subst heq
      rw [Int.fract_intCast, show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring]
      exact (hper x).symm
  -- On `X × [n, n+1]` the map equals `(x,t) ↦ G x (t - n)`.
  have hBeq : EqOn (fun p : X × ℝ => G p.1 (Int.fract p.2))
      (fun p : X × ℝ => G p.1 (p.2 - (n : ℝ)))
      ((univ : Set X) ×ˢ Icc (n : ℝ) ((n : ℝ) + 1)) := by
    rintro ⟨x, t⟩ ht
    simp only [mem_prod, mem_univ, true_and, mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    change G x (Int.fract t) = G x (t - (n : ℝ))
    rcases lt_or_eq_of_le ht2 with hlt | heq
    · have hfloor : ⌊t⌋ = n := by
        rw [Int.floor_eq_iff]
        exact ⟨ht1, hlt⟩
      have hfr : Int.fract t = t - (n : ℝ) := by
        rw [← Int.self_sub_floor t, hfloor]
      rw [hfr]
    · subst heq
      have hf : Int.fract ((n : ℝ) + 1) = 0 := by simp
      rw [hf, add_sub_cancel_left]
      exact (hper x).symm
  -- Paste the two closed pieces.
  have hunion : ContinuousOn (fun p : X × ℝ => G p.1 (Int.fract p.2))
      (((univ : Set X) ×ˢ Icc ((n : ℝ) - 1) (n : ℝ)) ∪
        ((univ : Set X) ×ˢ Icc (n : ℝ) ((n : ℝ) + 1))) :=
    (hshiftA.continuousOn.congr_mono hAeq (subset_univ _)).union_of_isClosed
      (hshiftB.continuousOn.congr_mono hBeq (subset_univ _)) hAcl hBcl
  -- The union contains the open box `X × (n-1, n+1)`, a neighbourhood of `(x₀, t₀)`.
  have hsub : (univ : Set X) ×ˢ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) ⊆
      ((univ : Set X) ×ˢ Icc ((n : ℝ) - 1) (n : ℝ)) ∪
        ((univ : Set X) ×ˢ Icc (n : ℝ) ((n : ℝ) + 1)) := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    simp only [mem_Ioo] at ht
    rcases lt_trichotomy t (n : ℝ) with h | h | h
    · exact Or.inl ⟨trivial, ⟨by linarith, h.le⟩⟩
    · exact Or.inl ⟨trivial, ⟨by linarith, h.le⟩⟩
    · exact Or.inr ⟨trivial, ⟨h.le, by linarith⟩⟩
  have hmem : (univ : Set X) ×ˢ Ioo ((n : ℝ) - 1) ((n : ℝ) + 1) ∈ 𝓝 (x₀, t₀) :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, ⟨by linarith, by linarith⟩⟩
  exact hunion.continuousAt (mem_of_superset hmem hsub)

end Work.OddBound.polygonValue.balancing
