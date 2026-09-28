import Mathlib
import Submission.Work.RatHurewicz.AvoidOrigin.Class

/-!
# The chart map of a cell of the cycle model is injective on a face

The map `y ↦ Quotient.mk'' (Sum.inl ⟨i, y⟩)` is injective on the points of the simplex whose
support is a given set `S` with at least three elements: this is a corollary of the description of
the class of a point of a cell (`Work.RatHurewicz.chainTrans`).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.AvoidOrigin

open Work.RatHurewicz

/-- The cardinality of the set of elements of `S` below `u`, computed on the subtype. -/
theorem card_filter_attach {n : ℕ} (S : Finset (Fin (n + 2))) (u : Fin (n + 2)) :
    (S.filter (fun v => v < u)).card
      = (S.attach.filter (fun w : {t // t ∈ S} => (w : Fin (n + 2)) < u)).card := by
  rw [← Finset.card_attach (s := S.filter (fun v => v < u))]
  refine Finset.card_bij
    (fun (w : {v // v ∈ S.filter (fun v => v < u)}) _ =>
      (⟨w.1, (Finset.mem_filter.mp w.2).1⟩ : {t // t ∈ S})) ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach S _, (Finset.mem_filter.mp a.2).2⟩
  · intro a a' _ _ heq
    exact Subtype.ext (congrArg (fun z : {t // t ∈ S} => (z : Fin (n + 2))) heq)
  · intro b hb
    exact ⟨⟨b.1, Finset.mem_filter.mpr ⟨b.2, (Finset.mem_filter.mp hb).2⟩⟩,
      Finset.mem_attach _ _, rfl⟩

/-- **A strictly monotone vertex map with image `S` is the identity.** -/
theorem eq_of_strictMono_image {n : ℕ} {S : Finset (Fin (n + 2))}
    {τ : {t // t ∈ S} → Fin (n + 2)} (h : StrictMono τ) (him : S.attach.image τ = S) :
    ∀ t : {t // t ∈ S}, τ t = t.1 := by
  have hτS : ∀ u : {t // t ∈ S}, τ u ∈ S := fun u => by
    rw [← him]
    exact Finset.mem_image.mpr ⟨u, Finset.mem_attach S u, rfl⟩
  have hcard : ∀ t : {t // t ∈ S},
      (S.filter (fun v => v < τ t)).card = (S.filter (fun v => v < t.1)).card := by
    intro t
    have h1 : (S.attach.filter (fun u : {t // t ∈ S} => (u : Fin (n + 2)) < t.1)).image τ
        = S.filter (fun v => v < τ t) := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨u, ⟨-, hu⟩, rfl⟩
        exact ⟨hτS u, h hu⟩
      · rintro ⟨hwS, hwlt⟩
        obtain ⟨u, -, hu⟩ := Finset.mem_image.mp (by rw [him]; exact hwS)
        exact ⟨u, ⟨Finset.mem_attach S u, by
          by_contra hlt
          exact absurd (hu ▸ h.monotone (le_of_not_gt hlt)) (not_le.mpr hwlt)⟩, hu⟩
    rw [← h1, Finset.card_image_of_injective _ h.injective]
    exact (card_filter_attach S t.1).symm
  intro t
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hlt' : (S.filter (fun v => v < τ t)).card < (S.filter (fun v => v < t.1)).card := by
      refine Finset.card_lt_card ⟨?_, ?_⟩
      · intro x hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
          lt_trans (Finset.mem_filter.mp hx).2 hlt⟩
      · intro hsub
        have hmem : τ t ∈ S.filter (fun v => v < τ t) :=
          hsub (Finset.mem_filter.mpr ⟨hτS t, hlt⟩)
        exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl _)
    exact absurd (hcard t) (ne_of_lt hlt')
  · have hlt' : (S.filter (fun v => v < t.1)).card < (S.filter (fun v => v < τ t)).card := by
      refine Finset.card_lt_card ⟨?_, ?_⟩
      · intro x hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
          lt_trans (Finset.mem_filter.mp hx).2 hlt⟩
      · intro hsub
        have hmem : t.1 ∈ S.filter (fun v => v < t.1) :=
          hsub (Finset.mem_filter.mpr ⟨t.2, hlt⟩)
        exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl _)
    exact absurd (hcard t).symm (ne_of_lt hlt')

/-- **The chart map is injective on the face `S`.** -/
theorem chartInjective {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (hS : 2 < S.card) {y y' : stdSimplex ℝ (Fin (n + 2))}
    (hy : ptSupport y = S) (hy' : ptSupport y' = S)
    (h : (Quotient.mk'' (Sum.inl (⟨i, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))
        : Model D)
      = (Quotient.mk'' (Sum.inl (⟨i, y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))
        : Model D)) : y = y' := by
  have heq : Relation.EqvGen (modelRel D)
      (Sum.inl (⟨i, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))
      (Sum.inl (⟨i, y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))) :=
    Quotient.exact h
  obtain ⟨j, τ, hτ, hCT, hb⟩ := (chainTrans D i S hS y hy _).mp heq
  have hj : (⟨i, y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))
      = ⟨j, transportPt y hy τ hτ⟩ := Sum.inl.inj hb
  have hy'' : y' = transportPt y hy τ hτ := congrArg Sigma.snd hj
  have himage : S.attach.image τ = S := by
    rw [← transportPtSupp y hy τ hτ, ← hy'']
    exact hy'
  have hτid : ∀ t : {t // t ∈ S}, τ t = t.1 :=
    eq_of_strictMono_image (chainTransStrictMono D hCT) himage
  have htransp : transportPt y hy τ hτ
      = transportPt y hy (fun t : {t // t ∈ S} => t.1) (fun a b h => Subtype.ext h) := by
    refine Subtype.ext (funext fun w => ?_)
    change (transportPt y hy τ hτ : Fin (n + 2) → ℝ) w
      = (transportPt y hy (fun t : {t // t ∈ S} => t.1) (fun a b h => Subtype.ext h)
          : Fin (n + 2) → ℝ) w
    simp only [transportPt_apply]
    exact Finset.sum_congr rfl fun t _ => by rw [hτid t]
  rw [hy'', htransp]
  exact (transportPt_id y hy _).symm

end Work.RatHurewicz.AvoidOrigin
