import Mathlib

namespace Work.Drive.Mono

/-- If `X` is compact, `f : α → ℝ` is continuous, the image `f '' X` is order-connected
(an interval), and every nonempty fibre `X ∩ f ⁻¹' {t}` is preconnected, then `X` is
preconnected.

Proof: suppose `X = (X ∩ t) ∪ (X ∩ t')` with `t, t'` closed and `X ∩ t ∩ t' = ∅`.
Then `A := X ∩ t` and `B := X ∩ t'` are nonempty compact (hence `f '' A`, `f '' B` are
closed), disjoint, and cover `X`. Since `f '' X` is preconnected and covered by the two
closed sets `f '' A`, `f '' B`, there is `z` in both; pick `a ∈ A`, `b ∈ B` with
`f a = f b = z`. The fibre over `z` is preconnected and covered by the closed sets
`t, t'`, meeting both, so it meets `t ∩ t'` — a point of `X ∩ t ∩ t'`, contradiction. -/
theorem isPreconnected_of_isCompact_ordConnected_fibers {α : Type*} [TopologicalSpace α]
    {X : Set α} (hX : IsCompact X) {f : α → ℝ} (hf : Continuous f)
    (hT : (f '' X).OrdConnected)
    (hfib : ∀ t ∈ f '' X, IsPreconnected (X ∩ f ⁻¹' {t})) :
    IsPreconnected X := by
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' htt' hXt hXt'
  by_contra hne
  have hSpre : IsPreconnected (f '' X) := hT.isPreconnected
  have hSsub : f '' X ⊆ f '' (X ∩ t) ∪ f '' (X ∩ t') := by
    rintro y ⟨x, hxX, rfl⟩
    rcases htt' hxX with hxt | hxt'
    · exact Or.inl ⟨x, ⟨hxX, hxt⟩, rfl⟩
    · exact Or.inr ⟨x, ⟨hxX, hxt'⟩, rfl⟩
  have hneA : (f '' X ∩ f '' (X ∩ t)).Nonempty := by
    obtain ⟨x, hx⟩ := hXt
    exact ⟨f x, ⟨x, hx.1, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hneB : (f '' X ∩ f '' (X ∩ t')).Nonempty := by
    obtain ⟨x, hx⟩ := hXt'
    exact ⟨f x, ⟨x, hx.1, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hAcl : IsClosed (f '' (X ∩ t)) := ((hX.inter_right ht).image hf).isClosed
  have hBcl : IsClosed (f '' (X ∩ t')) := ((hX.inter_right ht').image hf).isClosed
  obtain ⟨z, hzS, hzA, hzB⟩ :=
    isPreconnected_closed_iff.mp hSpre (f '' (X ∩ t)) (f '' (X ∩ t')) hAcl hBcl hSsub hneA hneB
  obtain ⟨a, ha, hfa⟩ := hzA
  obtain ⟨b, hb, hfb⟩ := hzB
  have hFpre : IsPreconnected (X ∩ f ⁻¹' {z}) := hfib z hzS
  have hFsub : X ∩ f ⁻¹' {z} ⊆ t ∪ t' := fun x hx => htt' hx.1
  have hFa : a ∈ X ∩ f ⁻¹' {z} ∩ t :=
    ⟨⟨ha.1, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hfa⟩, ha.2⟩
  have hFb : b ∈ X ∩ f ⁻¹' {z} ∩ t' :=
    ⟨⟨hb.1, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hfb⟩, hb.2⟩
  obtain ⟨w, hwF, hwtt⟩ :=
    isPreconnected_closed_iff.mp hFpre t t' ht ht' hFsub ⟨a, hFa⟩ ⟨b, hFb⟩
  exact hne ⟨w, hwF.1, hwtt⟩

end Work.Drive.Mono
