import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.FeitSibley.CharQ.scriptS_vanish

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.CharQ

noncomputable section

open Classical

/-- `cfInner` does not depend on the chosen `Fintype` instance (both are the sum over the
universal finset of the same type). -/
theorem cfInner_fintype_indep {α : Type*} (i₁ i₂ : Fintype α) (f g : α → ℂ) :
    @Work.Coherence.cfInner α i₁ f g = @Work.Coherence.cfInner α i₂ f g := by
  have huniv : (@Finset.univ α i₁) = (@Finset.univ α i₂) := by
    apply Finset.ext
    intro x
    simp
  have hcard : (@Fintype.card α i₁ : ℂ) = (@Fintype.card α i₂ : ℂ) := by
    rw [show @Fintype.card α i₁ = @Fintype.card α i₂ from by
      show (@Finset.univ α i₁).card = (@Finset.univ α i₂).card
      rw [huniv]]
  simp only [Work.Coherence.cfInner]
  rw [hcard, Finset.sum_congr huniv (fun x _ => rfl)]

/-- `Q ∖ {1}` is a TI set (Dade 5.10) with normalizer `H`, in the Feit–Sibley set-up.
The only point needing the hypotheses of `FSData` is `normalizer_le`: conjugation by `g` maps
`Q ∖ {1}` into itself, hence (a finite permutation) is bijective, so it normalizes `Q`; then
`g ∈ N_G(Q) = H`. -/
theorem isTISet_Q_diff_one {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    Work.BrauerSuzuki.IsTISet ((h.Q : Set G) \ {1}) h.H := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `1 ∉ Q ∖ {1}`
    simp
  · -- `Q ∖ {1} ⊆ H`
    intro x hx
    exact h.Q_le_H hx.1
  · -- closed under inversion
    intro x hx
    refine ⟨h.Q.inv_mem hx.1, fun hc => hx.2 ?_⟩
    rw [Set.mem_singleton_iff] at hc ⊢
    exact inv_eq_one.mp hc
  · -- `H` normalizes `Q ∖ {1}`
    intro h' hh' x hx
    refine ⟨(Subgroup.mem_set_normalizer_iff.mp (h.Q_normal_in_H hh') x).mp hx.1, ?_⟩
    intro hc
    apply hx.2
    rw [Set.mem_singleton_iff] at hc ⊢
    calc x = h'⁻¹ * (h' * x * h'⁻¹) * h' := by group
      _ = 1 := by rw [hc]; simp
  · -- an element normalizing `Q ∖ {1}` lies in `H = N_G(Q)`
    intro g hg
    -- conjugation by `g` restricts to an injective, hence surjective, self-map of `Q`
    let ψ : ↥h.Q → ↥h.Q := fun x =>
      ⟨g * (x : G) * g⁻¹, by
        by_cases hx1 : (x : G) = 1
        · rw [hx1]; simp
        · exact (hg ⟨x.2, by simpa [Set.mem_singleton_iff] using hx1⟩).1⟩
    have hψval : ∀ x : ↥h.Q, (ψ x : G) = g * (x : G) * g⁻¹ := fun x => rfl
    have hinj : Function.Injective ψ := by
      intro x y hxy
      have h2 : g * (x : G) * g⁻¹ = g * (y : G) * g⁻¹ := by
        rw [← hψval x, ← hψval y, hxy]
      have h2' : (x : G) = (y : G) := by
        calc (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
          _ = g⁻¹ * (g * (y : G) * g⁻¹) * g := by rw [h2]
          _ = (y : G) := by group
      exact Subtype.ext h2'
    have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hinj
    rw [← h.normalizer_Q_eq, Subgroup.mem_set_normalizer_iff]
    intro n
    constructor
    · intro hn
      have hmem := (ψ ⟨n, hn⟩).2
      rwa [hψval ⟨n, hn⟩] at hmem
    · intro hn
      obtain ⟨w, hw⟩ := hsurj ⟨g * n * g⁻¹, hn⟩
      have h2 : (w : G) = n := by
        have h3 : g * (w : G) * g⁻¹ = g * n * g⁻¹ := by
          have h4 : (ψ w : G) = g * n * g⁻¹ := by rw [hw]
          rwa [hψval w] at h4
        calc (w : G) = g⁻¹ * (g * (w : G) * g⁻¹) * g := by group
          _ = g⁻¹ * (g * n * g⁻¹) * g := by rw [h3]
          _ = n := by group
      rw [← h2]
      exact w.2
  · -- distinct conjugates of `Q ∖ {1}` are disjoint (the TI property of `Q`)
    intro g hg x y hx hy hc
    have hmem : y ∈ h.Q ⊓ Submission.Blueprint.conj g h.Q := by
      refine ⟨hy.1, ?_⟩
      show y ∈ Subgroup.map (MulAut.conj g).toMonoidHom h.Q
      exact Subgroup.mem_map.mpr ⟨x, hx.1, by
        show MulAut.conj g x = y
        rw [MulAut.conj_apply]
        exact hc⟩
    rw [h.Q_TI g hg] at hmem
    exact hy.2 (by simpa using hmem)

/-- Every element of `ℤ[𝒮]` is a class function (it is a `ℤ`-combination of irreducible
characters of `H`). -/
theorem zspan_scriptS_isClassFun {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {α : ↥h.H → ℂ}
    (hα : α ∈ Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1)) :
    Work.CharCore.IsClassFun α := by
  obtain ⟨c, hc⟩ := hα
  rw [hc]
  refine Work.CharCore.IsClassFun.sum _ _ (fun x _ => ?_)
  have hxmem : (x : ↥h.H → ℂ) ∈ Submission.Blueprint.excludingKernel h.H h.Q1 := x.2
  unfold Submission.Blueprint.excludingKernel at hxmem
  obtain ⟨hxIrr, -⟩ := Finset.mem_filter.mp hxmem
  exact Work.CharCore.IsClassFun.smul ((c x : ℤ) : ℂ)
    (Work.CharCore.isClassFun_of_mem_Irr hxIrr)

/-- Every element of `ℤ[𝒮]^0` vanishes off `Q ∖ {1}`: on `H ∖ Q` because each member of `𝒮`
does (Peterfalvi Lemma 2a), and at `1` because its degree is `0`. -/
theorem zspan0_scriptS_support {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {α : ↥h.H → ℂ}
    (hα : α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1)) :
    Work.BrauerSuzuki.SupportLeSub α ((h.Q : Set G) \ {1}) := by
  obtain ⟨⟨c, hc⟩, hα1⟩ := (Work.Coherence.mem_zSpan0).mp hα
  intro x hx
  by_cases hxQ : (x : G) ∈ h.Q
  · -- then `(x : G) = 1`, and `α 1 = 0`
    have hx1 : (x : G) = 1 := by
      by_contra hne
      exact hx ⟨hxQ, by simpa [Set.mem_singleton_iff] using hne⟩
    have hxeq : x = 1 := Subtype.ext hx1
    rw [hxeq, hα1]
  · -- off `Q`, every generator of `ℤ[𝒮]` vanishes
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [scriptS_vanish h y.2 hxQ, mul_zero]

theorem isometry_indLin {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    Work.Coherence.IsometryOn (Work.FeitSibley.scriptS h.H h.Q1)
      (Work.FeitSibley.indLin h.H) := by
  refine ⟨fun α hα β hβ => ?_⟩
  rw [Work.FeitSibley.indLin_apply, Work.FeitSibley.indLin_apply]
  -- `cfInner` is independent of the chosen `Fintype` instance, which bridges the instance
  -- fixed inside the imported TI-set isometry with the one of the statement.
  refine (Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet (isTISet_Q_diff_one h)
    (zspan_scriptS_isClassFun h (Work.Coherence.mem_zSpan0.mp hα).1)
    (zspan_scriptS_isClassFun h (Work.Coherence.mem_zSpan0.mp hβ).1)
    (zspan0_scriptS_support h hα) (zspan0_scriptS_support h hβ)).trans ?_
  exact cfInner_fintype_indep _ _ α β

end

end Work.FeitSibley.CharQ
