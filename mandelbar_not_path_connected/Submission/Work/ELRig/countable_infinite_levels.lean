import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter
open scoped Topology

/-- The set of levels `v` for which `f ⁻¹' {v} ∩ [a,b]` is infinite is countable, for `f`
real-analytic on an open set containing `[a,b]`.

Indeed, if the fibre of `v` inside the compact interval `[a,b]` is infinite, it has an
accumulation point `x ∈ [a,b]`; at that point `f - v` cannot be eventually nonzero (isolated
zeros), hence vanishes in a neighbourhood of `x`, and by the identity principle it vanishes on
all of `[a,b]`, so `v = f a`. Thus the set of such `v` is contained in the singleton `{f a}`. -/
theorem countable_infinite_levels {f : ℝ → ℝ} {W : Set ℝ} (hW : IsOpen W)
    (hf : AnalyticOnNhd ℝ f W) {a b : ℝ} (hab : Set.Icc a b ⊆ W) :
    {v : ℝ | ({t : ℝ | t ∈ Set.Icc a b ∧ f t = v}).Infinite}.Countable := by
  classical
  apply Subsingleton.countable
  intro v hv w hw
  have key : ∀ v : ℝ, ({t : ℝ | t ∈ Set.Icc a b ∧ f t = v}).Infinite → v = f a := by
    intro v hv
    by_cases hab' : a ≤ b
    · obtain ⟨x, hxK, hxacc⟩ :=
        hv.exists_accPt_of_subset_isCompact (K := Set.Icc a b) isCompact_Icc
          (fun t ht => ht.1)
      have hxW : x ∈ W := hab hxK
      have hg_at : AnalyticAt ℝ (fun z : ℝ => f z - v) x :=
        (hf x hxW).sub analyticAt_const
      have hzero : (fun z : ℝ => f z - v) =ᶠ[𝓝 x] 0 := by
        rcases hg_at.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
        · exact h0
        · exfalso
          rw [accPt_iff_frequently_nhdsNE] at hxacc
          have hfreq : ∃ᶠ y in 𝓝[≠] x, (fun z : ℝ => f z - v) y = 0 :=
            hxacc.mono (fun y hy => by simp [hy.2])
          have hboth := hfreq.and_eventually hne
          simp at hboth
      have han : AnalyticOnNhd ℝ (fun z : ℝ => f z - v) (Set.Icc a b) :=
        fun z hz => (hf z (hab hz)).sub analyticAt_const
      have heq0 : Set.EqOn (fun z : ℝ => f z - v) 0 (Set.Icc a b) :=
        han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Icc hxK hzero
      have ha0 : f a - v = 0 := by simpa using heq0 ⟨le_refl a, hab'⟩
      linarith
    · exfalso
      rw [Set.Icc_eq_empty hab'] at hv
      simp at hv
  rw [key v hv, key w hw]

end Work.ELRig
