import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.SeparatingElement

universe u

/-- **A transcendence basis of a field extension of transcendence degree `≤ 1` is a single
transcendental element.**  If `h` is transcendental over `k` then a transcendence basis is
nonempty (`IsTranscendenceBasis.nonempty_iff_transcendental`), and if moreover
`Algebra.trdeg k K ≤ 1` then `Cardinal.mk ↥s = Algebra.trdeg k K ≤ 1` by
`IsTranscendenceBasis.cardinalMk_eq_trdeg`; with `Cardinal.mk ↥s = s.card`
(`Cardinal.mk_coe_finset`) this forces `s.card = 1`, hence `s = {t}` for a unique `t`, which is
transcendental over `k` because `s` is algebraically independent
(`algebraicIndependent_singleton_iff`). -/
theorem exists_eq_singleton_of_isTranscendenceBasis_of_trdeg_le_one {k K : Type u} [Field k]
    [Field K] [Algebra k K] (h : K) (hh : Transcendental k h) (htr : Algebra.trdeg k K ≤ 1)
    {s : Finset K} (hs : IsTranscendenceBasis k ((↑) : s → K)) :
    ∃ t : K, s = {t} ∧ Transcendental k t := by
  have hcard : (s.card : Cardinal) ≤ 1 := by
    rw [← Cardinal.mk_coe_finset, hs.cardinalMk_eq_trdeg]
    exact htr
  have hle : s.card ≤ 1 := Nat.cast_le.mp hcard
  have hT : Algebra.Transcendental k K := ⟨⟨h, hh⟩⟩
  have hne : Nonempty ↥s := hs.nonempty_iff_transcendental.mpr hT
  have hpos : 0 < s.card := by
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact Finset.card_pos.mpr ⟨x, hx⟩
  have hcard1 : s.card = 1 := le_antisymm hle (Nat.succ_le_of_lt hpos)
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨t, ht, ?_⟩
  have hmem : t ∈ s := by rw [ht]; exact Finset.mem_singleton_self t
  exact hs.1.transcendental ⟨t, hmem⟩

end Work.CurveBasics.SeparatingElement
