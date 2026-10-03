import Mathlib
import Submission.Work.HornSC.Tools

namespace Work.HornSC

open Set

/-- **The clopen piece of a disconnected sphere-complement.**
If `X` is open in `ℂ` and the complement of `X` in the one-point compactification `OnePoint ℂ` is
not preconnected, then `Xᶜ` contains a nonempty compact set `S` at positive distance from the rest
of `Xᶜ`.

Route: `(OnePoint.some '' X)ᶜ = some '' Xᶜ ∪ {∞}` is closed (as `some '' X` is open) in the compact
space `OnePoint ℂ`, hence compact.  `¬ IsPreconnected` gives a separation of that set into two
nonempty relatively clopen pieces `A`, `B`; `∞` lies in exactly one of them, say `B`.  Then
`S := some ⁻¹' A ⊆ Xᶜ` is compact, nonempty, avoids `∞`; the gap follows because `A` is closed in
the sphere while `Xᶜ ∖ S` maps into `B`: any sequence in `Xᶜ ∖ S` converging to a point of `S` would
have its image converging inside `A ∩ B = ∅`. -/
theorem exists_compact_gap_of_compl_sphere_not_preconnected {X : Set ℂ} (hX : IsOpen X)
    (h : ¬ IsPreconnected ((OnePoint.some '' X : Set (OnePoint ℂ))ᶜ)) :
    ∃ S : Set ℂ, IsCompact S ∧ S.Nonempty ∧ S ⊆ Xᶜ ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ Xᶜ, s' ∉ S → δ ≤ dist s s' := by
  set K : Set (OnePoint ℂ) := (OnePoint.some '' X)ᶜ with hKdef
  replace h : ¬ IsPreconnected K := by rw [hKdef]; exact h
  have hKcl : IsClosed K := by
    rw [hKdef]
    exact isClosed_compl_iff.mpr (OnePoint.isOpen_image_coe.mpr hX)
  have hpreK : OnePoint.some ⁻¹' K = Xᶜ := by
    rw [hKdef, Set.preimage_compl, Set.preimage_image_eq X (OnePoint.coe_injective (X := ℂ))]
  have hKinf : (OnePoint.infty : OnePoint ℂ) ∈ K := by
    rw [hKdef, OnePoint.compl_image_coe]
    exact Or.inr rfl
  rw [IsPreconnected] at h
  push Not at h
  obtain ⟨u, v, hu, hv, hKuv, hAu, hAv, hdisj⟩ := h
  -- `hdisj : K ∩ (u ∩ v) = ∅`
  have hdisj' : ∀ x : OnePoint ℂ, x ∈ K → x ∈ u → x ∈ v → False := by
    intro x hxK hxu hxv
    have hmem : x ∈ K ∩ (u ∩ v) := ⟨hxK, hxu, hxv⟩
    rw [hdisj] at hmem
    exact hmem
  -- both pieces are closed in the sphere
  have hAcl : IsClosed (K ∩ u) := by
    have heq : K ∩ u = K ∩ vᶜ := by
      ext x
      constructor
      · rintro ⟨hxK, hxu⟩
        exact ⟨hxK, fun hxv => hdisj' x hxK hxu hxv⟩
      · rintro ⟨hxK, hxv⟩
        have hmem := hKuv hxK
        rw [Set.mem_union] at hmem
        rcases hmem with hxu | hxv'
        · exact ⟨hxK, hxu⟩
        · exact absurd hxv' hxv
    rw [heq]
    exact hKcl.inter hv.isClosed_compl
  have hBcl : IsClosed (K ∩ v) := by
    have heq : K ∩ v = K ∩ uᶜ := by
      ext x
      constructor
      · rintro ⟨hxK, hxv⟩
        exact ⟨hxK, fun hxu => hdisj' x hxK hxu hxv⟩
      · rintro ⟨hxK, hxu⟩
        have hmem := hKuv hxK
        rw [Set.mem_union] at hmem
        rcases hmem with hxu' | hxv
        · exact absurd hxu' hxu
        · exact ⟨hxK, hxv⟩
    rw [heq]
    exact hKcl.inter hu.isClosed_compl
  -- the main step: a clopen piece of `K` avoiding `∞` yields the gap
  have key : ∀ (u0 : Set (OnePoint ℂ)), IsOpen u0 → (K ∩ u0).Nonempty →
      OnePoint.infty ∉ K ∩ u0 → IsClosed (K ∩ u0) →
      ∃ S : Set ℂ, IsCompact S ∧ S.Nonempty ∧ S ⊆ Xᶜ ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ Xᶜ, s' ∉ S → δ ≤ dist s s' := by
    intro u0 hu0 hne hinf hcl
    set S : Set ℂ := OnePoint.some ⁻¹' (K ∩ u0) with hSdef
    have hSeq : S = Xᶜ ∩ OnePoint.some ⁻¹' u0 := by
      rw [hSdef]
      ext z
      constructor
      · intro hz
        rw [Set.mem_preimage] at hz
        refine ⟨?_, hz.2⟩
        rw [← hpreK]
        exact hz.1
      · rintro ⟨hzX, hzu⟩
        rw [Set.mem_preimage]
        refine ⟨?_, hzu⟩
        rw [← hpreK] at hzX
        exact hzX
    have hScomp : IsCompact S := by
      rw [hSdef]
      exact ((OnePoint.isClosed_iff_of_notMem hinf).mp hcl).2
    have hSne : S.Nonempty := by
      obtain ⟨a, haK, hau0⟩ := hne
      have ha_ne : a ≠ OnePoint.infty := fun hEq => hinf (hEq ▸ ⟨haK, hau0⟩)
      obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp ha_ne
      exact ⟨z, by rw [hSdef, Set.mem_preimage, hz]; exact ⟨haK, hau0⟩⟩
    refine ⟨S, hScomp, hSne, ?_, ?_⟩
    · intro z hz
      rw [hSeq] at hz
      exact hz.1
    · by_cases hFne : (Xᶜ \ S).Nonempty
      · have hFcl : IsClosed (Xᶜ \ S) := by
          have heq : Xᶜ \ S = Xᶜ ∩ (OnePoint.some ⁻¹' u0)ᶜ := by
            rw [hSeq]
            ext z
            simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
            tauto
          rw [heq]
          exact hX.isClosed_compl.inter
            (by
              simpa only [Set.preimage_compl] using
                (IsClosed.preimage OnePoint.continuous_coe (isClosed_compl_iff.mpr hu0)))
        obtain ⟨r, hr, hgap⟩ :=
          Metric.exists_pos_forall_lt_edist hScomp hFcl Set.disjoint_sdiff_right
        refine ⟨(r : ℝ), NNReal.coe_pos.mpr hr, ?_⟩
        intro s hsS s' hs'X hs'
        have hlt := hgap s hsS s' ⟨hs'X, hs'⟩
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hlt
        exact le_of_lt
          ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).mp hlt)
      · refine ⟨1, one_pos, ?_⟩
        intro s hsS s' hs'X hs'
        exact absurd (⟨s', hs'X, hs'⟩ : (Xᶜ \ S).Nonempty) hFne
  have hmem : OnePoint.infty ∈ u ∨ OnePoint.infty ∈ v :=
    (Set.mem_union OnePoint.infty u v).mp (hKuv hKinf)
  rcases hmem with hinfu | hinfv
  · exact key v hv hAv (fun hc => hdisj' OnePoint.infty hc.1 hinfu hc.2) hBcl
  · exact key u hu hAu (fun hc => hdisj' OnePoint.infty hc.1 hc.2 hinfv) hAcl

end Work.HornSC
