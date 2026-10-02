import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

open Set

/-- **Modulus of continuity of the inverse of a continuous injection on a compact set.**

If `K` is compact, `f` is continuous on `K` and injective on `K`, then the (set-theoretic)
inverse of `f` on `f '' K = range f` is continuous, hence — `K` being compact — uniformly
continuous.  This is the metric form of that uniform continuity: for every `ε > 0` there is
`δ > 0` such that `a, b ∈ K` and `‖f a - f b‖ < δ` force `‖a - b‖ < ε`.

The proof is by compactness: on the compact set of pairs `(a,b) ∈ K × K` with `‖a - b‖ ≥ ε`
the continuous function `(a,b) ↦ ‖f a - f b‖` attains a nonnegative minimum `δ`; if that
minimum were `0`, injectivity of `f` on `K` would force `a = b`, contradicting `‖a - b‖ ≥ ε`. -/
theorem injOn_modulus {K : Set ℂ} {f : ℂ → ℂ} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hinj : Set.InjOn f K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ K, ∀ b ∈ K, ‖f a - f b‖ < δ → ‖a - b‖ < ε := by
  intro ε hε
  set S : Set (ℂ × ℂ) := (K ×ˢ K) ∩ {p | ε ≤ ‖p.1 - p.2‖} with hS
  by_cases hne : S.Nonempty
  · have hcont : ContinuousOn (fun p : ℂ × ℂ => f p.1 - f p.2) (K ×ˢ K) := by
      have h1 : ContinuousOn (fun p : ℂ × ℂ => f p.1) (K ×ˢ K) :=
        hf.comp (continuous_fst.continuousOn) (fun p hp => hp.1)
      have h2 : ContinuousOn (fun p : ℂ × ℂ => f p.2) (K ×ˢ K) :=
        hf.comp (continuous_snd.continuousOn) (fun p hp => hp.2)
      exact h1.sub h2
    have hψcont : ContinuousOn (fun p : ℂ × ℂ => ‖f p.1 - f p.2‖) S :=
      (hcont.norm).mono inter_subset_left
    have hclosed : IsClosed {p : ℂ × ℂ | ε ≤ ‖p.1 - p.2‖} :=
      isClosed_Ici.preimage ((continuous_fst.sub continuous_snd).norm)
    have hScomp : IsCompact S := (hK.prod hK).inter_right hclosed
    obtain ⟨p, hpS, hpmin⟩ := hScomp.exists_isMinOn hne hψcont
    have hp1 : p.1 ∈ K := hpS.1.1
    have hp2 : p.2 ∈ K := hpS.1.2
    have hple : ε ≤ ‖p.1 - p.2‖ := hpS.2
    refine ⟨‖f p.1 - f p.2‖, ?_, ?_⟩
    · rw [norm_pos_iff]
      intro hfeq0
      have hfeq : f p.1 = f p.2 := sub_eq_zero.mp hfeq0
      have hpeq : p.1 = p.2 := hinj hp1 hp2 hfeq
      have hz : ‖p.1 - p.2‖ = 0 := by rw [hpeq, sub_self, norm_zero]
      linarith
    · intro a ha b hb hlt
      by_contra hcon
      have hcon' : ε ≤ ‖a - b‖ := not_lt.mp hcon
      have hmem : (a, b) ∈ S := ⟨⟨ha, hb⟩, hcon'⟩
      have hmin' : ‖f p.1 - f p.2‖ ≤ ‖f a - f b‖ := hpmin hmem
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro a ha b hb hlt
    by_contra hcon
    have hcon' : ε ≤ ‖a - b‖ := not_lt.mp hcon
    exact hne ⟨(a, b), ⟨⟨ha, hb⟩, hcon'⟩⟩

end Work.PARIMPL2.Lavaurs
