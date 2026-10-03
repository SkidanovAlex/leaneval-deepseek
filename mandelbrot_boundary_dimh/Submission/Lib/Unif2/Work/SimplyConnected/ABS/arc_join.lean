import Mathlib

/-!
# Reparametrising a concatenated path, and subpath injectivity

Two helper facts about `Path.trans` / `Path.subpath` that are needed to *reason* about concatenations
of injective paths (the transitivity step of the arc theorem
`Topology/Surface/exists_injective_path_in_is_open_connected`), and that Mathlib does not have.

The point of `trans_apply_le_val` / `trans_apply_ge_val` is that the naive use of `Path.trans_apply`
produces a subtype point `⟨2 * (t : ℝ), ?_⟩` whose **proof component is anonymous**; two subtype
points with the same value and different proofs are propositionally but not definitionally equal, so
the parameter cannot be named and the `Icc.convexComb` arithmetic cannot start.  Stating the value of
`(γ.trans γ') t` *existentially*, with the real parameter as a conjunct, avoids the anonymous proofs
entirely: after these two lemmas every argument is arithmetic on `ℝ`.
-/

open Set

namespace Work.Topology.Arc

variable {X : Type*} [TopologicalSpace X]

/-- **Subpaths of an injective path are injective.** -/
theorem injective_subpath {a b : X} {γ : Path a b} (hγ : Function.Injective γ)
    {t₀ t₁ : unitInterval} (h : (t₀ : ℝ) < t₁) : Function.Injective (γ.subpath t₀ t₁) := by
  have hval : ∀ u : unitInterval, (γ.subpath t₀ t₁ u : X) = γ (Icc.convexComb t₀ t₁ u) :=
    fun u => rfl
  intro u v huv
  rw [hval u, hval v] at huv
  have huv' : Icc.convexComb t₀ t₁ u = Icc.convexComb t₀ t₁ v := hγ huv
  have hc : ((Icc.convexComb t₀ t₁ u : unitInterval) : ℝ)
      = ((Icc.convexComb t₀ t₁ v : unitInterval) : ℝ) := congrArg Subtype.val huv'
  simp only [Icc.convexComb, Subtype.coe_mk] at hc
  have h1 : ((u : ℝ) - (v : ℝ)) * ((t₁ : ℝ) - (t₀ : ℝ)) = 0 := by linarith
  have h2 : (0 : ℝ) < (t₁ : ℝ) - (t₀ : ℝ) := by linarith
  have h3 : (u : ℝ) = (v : ℝ) := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · linarith
    · exact absurd h' (ne_of_gt h2)
  exact Subtype.ext h3

/-- **The first half of a concatenation.**  For `t ≤ 1/2`, the value `(γ.trans γ') t` is a value of
`γ`, at the reparametrised time `2 * t` (reported as a real number). -/
theorem trans_apply_le_val {a b c : X} (γ : Path a b) (γ' : Path b c) {t : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 2) :
    ∃ s : unitInterval, (s : ℝ) = 2 * (t : ℝ) ∧ (γ.trans γ') t = γ s := by
  have h2t : (2 : ℝ) * (t : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [t.2.1], by linarith [ht]⟩
  refine ⟨⟨2 * (t : ℝ), h2t⟩, rfl, ?_⟩
  rw [Path.trans_apply, dif_pos ht]

/-- **The second half of a concatenation.**  For `t ≥ 1/2`, the value `(γ.trans γ') t` is a value of
`γ'`, at the reparametrised time `2 * t - 1` (reported as a real number). -/
theorem trans_apply_ge_val {a b c : X} (γ : Path a b) (γ' : Path b c) {t : unitInterval}
    (ht : 1 / 2 < (t : ℝ)) :
    ∃ s : unitInterval, (s : ℝ) = 2 * (t : ℝ) - 1 ∧ (γ.trans γ') t = γ' s := by
  have h2t : (2 : ℝ) * (t : ℝ) - 1 ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht], by linarith [t.2.2]⟩
  refine ⟨⟨2 * (t : ℝ) - 1, h2t⟩, rfl, ?_⟩
  have hnt : ¬ (t : ℝ) ≤ 1 / 2 := by linarith
  rw [Path.trans_apply, dif_neg hnt]

/-- **Transitivity.**  Injective paths `p → q → r` either give `p = r` or an injective path `p → r`.

(The disjunction is unavoidable: there is no injective path from a point to itself.)

`t*` is the **last** time `β` meets the closed image of `α` (`IsCompact.exists_isMaxOn` applied to
`id` on the compact `β ⁻¹' range α`), `s*` the **first** time `α` meets `β t*`
(`IsCompact.exists_isMinOn` on `{s | α s = β t*}`).  Then `α ↾ [0, s*]` and `β ↾ [t*, 1]` meet only
in the common point, so their concatenation is injective; the degenerate cases `s* = 0` resp.
`t* = 1` are a single subpath, and if both hold then `p = r`. -/
theorem eq_or_exists_injective_path_trans {X : Type*} [TopologicalSpace X] [T2Space X]
    {p q r : X} (α : Path p q) (β : Path q r)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    p = r ∨ ∃ γ : Path p r, Function.Injective γ := by
  rcases eq_or_ne p r with hpr | hpr
  · exact Or.inl hpr
  have hαcl : IsClosed (range (α : unitInterval → X)) :=
    (isCompact_range α.continuous).isClosed
  have hToc : IsCompact {t : unitInterval | (β t : X) ∈ range (α : unitInterval → X)} :=
    (hαcl.preimage β.continuous).isCompact
  have hTone : ({t : unitInterval | (β t : X) ∈ range (α : unitInterval → X)}).Nonempty :=
    ⟨0, ⟨1, by rw [α.target, β.source]⟩⟩
  obtain ⟨tstar, htstar, htstarmax⟩ := hToc.exists_isMaxOn hTone continuous_id.continuousOn
  obtain ⟨s₀, hs₀⟩ := htstar
  have hScl : IsClosed {s : unitInterval | (α s : X) = (β tstar : X)} :=
    isClosed_eq α.continuous continuous_const
  have hSne : ({s : unitInterval | (α s : X) = (β tstar : X)}).Nonempty := ⟨s₀, hs₀⟩
  obtain ⟨sstar, hsstar, hsstarmin⟩ :=
    hScl.isCompact.exists_isMinOn hSne continuous_id.continuousOn
  -- `hsstar : α sstar = β tstar`; `htstarmax b hb : b ≤ tstar`; `hsstarmin s h : sstar ≤ s`
  have hcc₂ : ∀ v : unitInterval,
      ((Icc.convexComb tstar (1 : unitInterval) v : unitInterval) : ℝ)
        = (tstar : ℝ) + (v : ℝ) * (1 - (tstar : ℝ)) := by
    intro v; simp only [Icc.convexComb, Subtype.coe_mk, Icc.coe_one]; ring_nf
  rcases eq_or_ne sstar 0 with hs0 | hs0
  · -- `s* = 0`: a single subpath of `β` works
    have ht1ne : tstar ≠ 1 := by
      intro h
      exact hpr (by rw [← α.source, ← hs0, hsstar, h, β.target])
    have hlt : (tstar : ℝ) < 1 := by
      rcases lt_or_eq_of_le tstar.2.2 with h | h
      · exact h
      · exact absurd (Subtype.ext h) ht1ne
    refine Or.inr
      ⟨Path.cast (β.subpath tstar 1) (by rw [← α.source, ← hs0, hsstar]) β.target.symm, ?_⟩
    intro u v huv
    exact (injective_subpath hβ hlt) (by simpa [Path.cast_coe] using huv)
  · rcases eq_or_ne tstar 1 with ht1 | ht1
    · -- `t* = 1`: a single subpath of `α` works
      have hslt : (0 : ℝ) < (sstar : ℝ) := by
        rcases lt_or_eq_of_le sstar.2.1 with h | h
        · exact h
        · exact absurd (Subtype.ext h.symm) hs0
      refine Or.inr
        ⟨Path.cast (α.subpath 0 sstar) α.source.symm (by rw [← β.target, ← ht1]; exact hsstar.symm),
          ?_⟩
      intro u v huv
      exact (injective_subpath hα hslt) (by simpa [Path.cast_coe] using huv)
    · -- main case
      have hslt : (0 : ℝ) < (sstar : ℝ) := by
        rcases lt_or_eq_of_le sstar.2.1 with h | h
        · exact h
        · exact absurd (Subtype.ext h.symm) hs0
      have htltt : (tstar : ℝ) < 1 := by
        rcases lt_or_eq_of_le tstar.2.2 with h | h
        · exact h
        · exact absurd (Subtype.ext h) ht1
      set γ₁ : Path (α 0) (α sstar) := α.subpath 0 sstar with hγ₁
      set γ₂ : Path (α sstar) r := Path.cast (β.subpath tstar 1) hsstar β.target.symm with hγ₂
      have hv₁ : ∀ u : unitInterval, (γ₁ u : X) = α (Icc.convexComb (0 : unitInterval) sstar u) := by
        intro u; rw [hγ₁]; rfl
      have hv₂ : ∀ v : unitInterval, (γ₂ v : X)
          = β (Icc.convexComb tstar (1 : unitInterval) v) := by
        intro v; rw [hγ₂]; simp only [Path.cast_coe]; rfl
      have hinj₁ : Function.Injective γ₁ := by
        intro u v huv
        exact injective_subpath hα hslt (by rw [← hγ₁]; exact huv)
      have hinj₂ : Function.Injective γ₂ := by
        intro u v huv
        rw [hγ₂] at huv
        simp only [Path.cast_coe] at huv
        exact injective_subpath hβ htltt huv
      have hcc₁ : ∀ u : unitInterval,
          ((Icc.convexComb (0 : unitInterval) sstar u : unitInterval) : ℝ)
            = (u : ℝ) * (sstar : ℝ) := by
        intro u; simp only [Icc.convexComb, Subtype.coe_mk, Icc.coe_zero]; ring
      -- in a "mixing" situation the parameter of `β` must be `0`
      have hkey : ∀ {s s' : unitInterval},
          (α (Icc.convexComb (0 : unitInterval) sstar s) : X)
            = β (Icc.convexComb tstar (1 : unitInterval) s') → (s' : ℝ) = 0 := by
        intro s s' heq
        have hbge : (tstar : ℝ) ≤
            ((Icc.convexComb tstar (1 : unitInterval) s' : unitInterval) : ℝ) := by
          rw [hcc₂]; nlinarith [s'.2.1, tstar.2.2]
        rcases lt_or_eq_of_le hbge with hb | hb
        · have hle : ((Icc.convexComb tstar (1 : unitInterval) s' : unitInterval) : ℝ) ≤ (tstar : ℝ) :=
            htstarmax ⟨Icc.convexComb (0 : unitInterval) sstar s, heq⟩
          exact absurd hb (not_lt.mpr hle)
        · have h1 : (tstar : ℝ) + (s' : ℝ) * (1 - (tstar : ℝ)) = (tstar : ℝ) := by
            rw [← hcc₂]; exact hb.symm
          have hpos : (0 : ℝ) < 1 - (tstar : ℝ) := by linarith
          nlinarith [h1, hpos]
      refine Or.inr ⟨Path.cast (γ₁.trans γ₂) α.source.symm rfl, ?_⟩
      intro u v huv
      simp only [Path.cast_coe] at huv
      by_cases hu : (u : ℝ) ≤ 1 / 2 <;> by_cases hv : (v : ℝ) ≤ 1 / 2
      · obtain ⟨s, hsval, hseq⟩ := trans_apply_le_val γ₁ γ₂ hu
        obtain ⟨s', hs'val, hs'eq⟩ := trans_apply_le_val γ₁ γ₂ hv
        have h1 : γ₁ s = γ₁ s' := hseq.symm.trans (huv.trans hs'eq)
        have h2 : (s : ℝ) = (s' : ℝ) := congrArg Subtype.val (hinj₁ h1)
        rw [hsval, hs'val] at h2
        exact Subtype.ext (by linarith)
      · obtain ⟨s, hsval, hseq⟩ := trans_apply_le_val γ₁ γ₂ hu
        obtain ⟨s', hs'val, hs'eq⟩ := trans_apply_ge_val γ₁ γ₂ (not_le.mp hv)
        have h1 : γ₁ s = γ₂ s' := hseq.symm.trans (huv.trans hs'eq)
        rw [hv₁ s, hv₂ s'] at h1
        have h0 : (s' : ℝ) = 0 := hkey h1
        rw [hs'val] at h0
        have hv2 : (v : ℝ) = 1 / 2 := by linarith
        linarith [not_le.mp hv, hv2]
      · obtain ⟨s, hsval, hseq⟩ := trans_apply_ge_val γ₁ γ₂ (not_le.mp hu)
        obtain ⟨s', hs'val, hs'eq⟩ := trans_apply_le_val γ₁ γ₂ hv
        have h1 : γ₂ s = γ₁ s' := hseq.symm.trans (huv.trans hs'eq)
        rw [hv₁ s', hv₂ s] at h1
        have h0 : (s : ℝ) = 0 := hkey h1.symm
        rw [hsval] at h0
        have hu2 : (u : ℝ) = 1 / 2 := by linarith
        linarith [not_le.mp hu, hu2]
      · obtain ⟨s, hsval, hseq⟩ := trans_apply_ge_val γ₁ γ₂ (not_le.mp hu)
        obtain ⟨s', hs'val, hs'eq⟩ := trans_apply_ge_val γ₁ γ₂ (not_le.mp hv)
        have h1 : γ₂ s = γ₂ s' := hseq.symm.trans (huv.trans hs'eq)
        have h2 : (s : ℝ) = (s' : ℝ) := congrArg Subtype.val (hinj₂ h1)
        rw [hsval, hs'val] at h2
        exact Subtype.ext (by linarith)

end Work.Topology.Arc
