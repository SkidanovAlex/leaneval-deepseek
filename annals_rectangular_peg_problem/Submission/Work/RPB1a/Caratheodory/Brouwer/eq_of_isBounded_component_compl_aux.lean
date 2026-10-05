import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_paths
import Submission.Work.RPB1a.Caratheodory.Brouwer.frontier_component_eq_of_bounded

set_option autoImplicit false

/-!
# The second half of Maehara's argument

`Work.RPB1a.Caratheodory.Brouwer.eq_of_isBounded_component_compl_aux` is the abstract crossing
argument: assuming the "broken line" of `exists_maehara_broken_line` exists, every bounded connected
component of the complement of a Jordan curve is the component of the broken line's midpoint.

`Work.RPB1a.Caratheodory.Brouwer.eq_of_isBounded_component_compl_of_image` is the invariance of the
uniqueness statement under postcomposition with a boundedness-preserving self-homeomorphism of the
plane, which reduces the general case to the normalised one.
-/

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric

/-- The complement of the Maehara rectangle `rect = [-1,1] × [-2,2]` is preconnected: it is the
union of the four open half-planes `x < -1`, `x > 1`, `y < -2`, `y > 2`, glued pairwise. -/
theorem isPreconnected_compl_rect : IsPreconnected (rectᶜ) := by
  have hx1 : IsPreconnected {p : ℝ × ℝ | p.1 < -1} := by
    rw [show {p : ℝ × ℝ | p.1 < -1} = Set.Iio (-1 : ℝ) ×ˢ (Set.univ : Set ℝ) from by
      ext p; simp]
    exact isPreconnected_Iio.prod isPreconnected_univ
  have hx2 : IsPreconnected {p : ℝ × ℝ | 1 < p.1} := by
    rw [show {p : ℝ × ℝ | 1 < p.1} = Set.Ioi (1 : ℝ) ×ˢ (Set.univ : Set ℝ) from by
      ext p; simp]
    exact isPreconnected_Ioi.prod isPreconnected_univ
  have hy1 : IsPreconnected {p : ℝ × ℝ | p.2 < -2} := by
    rw [show {p : ℝ × ℝ | p.2 < -2} = (Set.univ : Set ℝ) ×ˢ Set.Iio (-2 : ℝ) from by
      ext p; simp]
    exact isPreconnected_univ.prod isPreconnected_Iio
  have hy2 : IsPreconnected {p : ℝ × ℝ | 2 < p.2} := by
    rw [show {p : ℝ × ℝ | 2 < p.2} = (Set.univ : Set ℝ) ×ˢ Set.Ioi (2 : ℝ) from by
      ext p; simp]
    exact isPreconnected_univ.prod isPreconnected_Ioi
  have hA : IsPreconnected ({p : ℝ × ℝ | p.1 < -1} ∪ {p : ℝ × ℝ | p.2 < -2}) :=
    IsPreconnected.union' ⟨(-2, -3), ⟨by norm_num, by norm_num⟩⟩ hx1 hy1
  have hB : IsPreconnected ({p : ℝ × ℝ | 1 < p.1} ∪ {p : ℝ × ℝ | 2 < p.2}) :=
    IsPreconnected.union' ⟨(2, 3), ⟨by norm_num, by norm_num⟩⟩ hx2 hy2
  have hAB : IsPreconnected (({p : ℝ × ℝ | p.1 < -1} ∪ {p : ℝ × ℝ | p.2 < -2})
      ∪ ({p : ℝ × ℝ | 1 < p.1} ∪ {p : ℝ × ℝ | 2 < p.2})) :=
    IsPreconnected.union' ⟨(-2, 3), ⟨by norm_num, by norm_num⟩⟩ hA hB
  rwa [show (({p : ℝ × ℝ | p.1 < -1} ∪ {p : ℝ × ℝ | p.2 < -2})
      ∪ ({p : ℝ × ℝ | 1 < p.1} ∪ {p : ℝ × ℝ | 2 < p.2})) = rectᶜ from ?_] at hAB
  ext p
  simp only [mem_rect, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_and_or, not_le]
  tauto

/-- The complement of the Maehara rectangle is unbounded. -/
theorem not_isBounded_compl_rect : ¬ Bornology.IsBounded (rectᶜ : Set (ℝ × ℝ)) := by
  intro hb
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hb
  have hmem : ((max r 1 + 1 : ℝ), (0 : ℝ)) ∈ (rectᶜ : Set (ℝ × ℝ)) := by
    rw [Set.mem_compl_iff, mem_rect]
    intro h
    linarith [h.2.1, le_max_right r 1]
  have hdist : dist ((max r 1 + 1 : ℝ), (0 : ℝ)) (0 : ℝ × ℝ) = max r 1 + 1 := by
    rw [Prod.dist_eq]; simp
    linarith [le_max_right r 1]
  have hlt := hr hmem
  rw [Metric.mem_ball, hdist] at hlt
  linarith [le_max_left r 1]

/-- A bounded connected component of the complement of a curve contained in `rect` is contained in
`rect`. -/
theorem connectedComponentIn_subset_rect {γ : Circle → ℝ × ℝ} (hsub : Set.range γ ⊆ rect)
    {w : ℝ × ℝ} (hw : w ∉ Set.range γ)
    (hb : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) w)) :
    connectedComponentIn ((Set.range γ)ᶜ) w ⊆ rect := by
  by_contra hcon
  obtain ⟨p, hpV, hpr⟩ := Set.not_subset.mp hcon
  have hpE : p ∈ (rectᶜ : Set (ℝ × ℝ)) := hpr
  have hEsub : (rectᶜ : Set (ℝ × ℝ)) ⊆ (Set.range γ)ᶜ := fun z hz hzr => hz (hsub hzr)
  have hsub2 : (rectᶜ : Set (ℝ × ℝ)) ⊆ connectedComponentIn ((Set.range γ)ᶜ) p :=
    isPreconnected_compl_rect.subset_connectedComponentIn hpE hEsub
  have hcomp_eq : connectedComponentIn ((Set.range γ)ᶜ) p =
      connectedComponentIn ((Set.range γ)ᶜ) w := (connectedComponentIn_eq hpV).symm
  exact not_isBounded_compl_rect (hb.subset (hcomp_eq ▸ hsub2))

/-- A homeomorphism carries `connectedComponentIn T t` into `connectedComponentIn (e '' T) (e t)`. -/
theorem image_connectedComponentIn_subset_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {T : Set X} {t : X} (ht : t ∈ T) :
    e '' connectedComponentIn T t ⊆ connectedComponentIn (e '' T) (e t) := by
  refine IsPreconnected.subset_connectedComponentIn ?_ ⟨t, mem_connectedComponentIn ht, rfl⟩ ?_
  · exact IsPreconnected.image (isPreconnected_connectedComponentIn (F := T) (x := t))
      (⇑e) e.continuous.continuousOn
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨z, connectedComponentIn_subset T t hz, rfl⟩

/-- A homeomorphism carries the component of `x` in `S` onto the component of `h x` in `h '' S`. -/
theorem image_connectedComponentIn_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) {S : Set X} {x : X} (hx : x ∈ S) :
    e '' connectedComponentIn S x = connectedComponentIn (e '' S) (e x) := by
  refine Subset.antisymm (image_connectedComponentIn_subset_homeomorph e hx) ?_
  have h := image_connectedComponentIn_subset_homeomorph e.symm
    (T := e '' S) (t := e x) ⟨x, hx, rfl⟩
  have h1 : e.symm '' (e '' S) = S := by
    ext y; constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩; simpa using hw
    · intro hy; exact ⟨e y, ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  rw [h1, e.symm_apply_apply x] at h
  intro y hy
  exact ⟨e.symm y, h ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- **The second half of Maehara's argument.**  Suppose a Jordan curve `γ` lies in `rect` and passes
through `a = (-1,0)` and `b = (1,0)`, and suppose `β` is the broken line of
`exists_maehara_broken_line` with midpoint `x`.  Then every bounded connected component of the
complement of `γ` is the component of `x`. -/
theorem eq_of_isBounded_component_compl_aux
    (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) (hinj : Function.Injective γ)
    (hsub : Set.range γ ⊆ rect)
    (ha : ((-1 : ℝ), (0 : ℝ)) ∈ Set.range γ) (hb : ((1 : ℝ), (0 : ℝ)) ∈ Set.range γ)
    (h₀ : ∃ x : ℝ × ℝ, x ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x))
    {β : ℝ → ℝ × ℝ} {x : ℝ × ℝ}
    (hβc : Continuous β) (hβrect : ∀ t, β t ∈ rect)
    (hβ0 : β (-1) = ((0 : ℝ), (2 : ℝ))) (hβ1 : β 1 = ((0 : ℝ), (-2 : ℝ)))
    (hβa : ((-1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1)
    (hβb : ((1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1)
    (hx : x ∉ Set.range γ)
    (hβcomp : ∀ w ∈ β '' Set.Icc (-1 : ℝ) 1, w ∉ Set.range γ →
        w ∈ connectedComponentIn ((Set.range γ)ᶜ) x ∨
        ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) w)) :
    ∀ y z : ℝ × ℝ, y ∉ Set.range γ → z ∉ Set.range γ →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) y) →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) →
      connectedComponentIn ((Set.range γ)ᶜ) y = connectedComponentIn ((Set.range γ)ᶜ) z := by
  have hmain : ∀ w : ℝ × ℝ, w ∉ Set.range γ →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) w) →
      connectedComponentIn ((Set.range γ)ᶜ) w = connectedComponentIn ((Set.range γ)ᶜ) x := by
    intro w hw hbw
    by_contra hne
    set V : Set (ℝ × ℝ) := connectedComponentIn ((Set.range γ)ᶜ) w with hV
    have hwV : w ∈ V := by rw [hV]; exact mem_connectedComponentIn hw
    have hVK : V ⊆ (Set.range γ)ᶜ := by rw [hV]; exact connectedComponentIn_subset _ _
    have hVrect : V ⊆ rect := by
      rw [hV]; exact connectedComponentIn_subset_rect hsub hw hbw
    have hfront : frontier V = Set.range γ := by
      rw [hV]; exact frontier_component_eq_of_bounded γ hγ hinj h₀ w hw
    have haV : ((-1 : ℝ), (0 : ℝ)) ∈ closure V :=
      frontier_subset_closure (by rw [hfront]; exact ha)
    have hbV : ((1 : ℝ), (0 : ℝ)) ∈ closure V :=
      frontier_subset_closure (by rw [hfront]; exact hb)
    have hVopen : IsOpen V := by
      rw [hV]; exact (isCompact_range hγ).isClosed.isOpen_compl.connectedComponentIn
    have hVpc : IsPathConnected V := by
      have hconn : IsConnected V :=
        ⟨⟨w, hwV⟩, by rw [hV]; exact isPreconnected_connectedComponentIn⟩
      exact (hVopen.isConnected_iff_isPathConnected).mp hconn
    -- `β` does not meet `V`
    have hβV : ∀ z ∈ β '' Set.Icc (-1 : ℝ) 1, z ∉ V := by
      intro z hz hzV
      have hzK : z ∉ Set.range γ := fun h => hVK hzV h
      have hVeq : V = connectedComponentIn ((Set.range γ)ᶜ) z := by
        rw [hV]; exact connectedComponentIn_eq (by rw [← hV]; exact hzV)
      rcases hβcomp z hz hzK with h | h
      · exact hne (hVeq.trans (connectedComponentIn_eq h).symm)
      · exact h (hVeq ▸ hbw)
    -- discs around `a` and `b` disjoint from the broken line
    have hcpt : IsCompact (β '' Set.Icc (-1 : ℝ) 1) := isCompact_Icc.image hβc
    have hclosed : IsClosed (β '' Set.Icc (-1 : ℝ) 1) := hcpt.isClosed
    obtain ⟨εa, hεapos, hεa⟩ : ∃ ε > 0,
        Metric.ball ((-1 : ℝ), (0 : ℝ)) ε ⊆ (β '' Set.Icc (-1 : ℝ) 1)ᶜ := by
      have h := (hclosed.isOpen_compl).mem_nhds hβa
      rwa [Metric.mem_nhds_iff] at h
    obtain ⟨εb, hεbpos, hεb⟩ : ∃ ε > 0,
        Metric.ball ((1 : ℝ), (0 : ℝ)) ε ⊆ (β '' Set.Icc (-1 : ℝ) 1)ᶜ := by
      have h := (hclosed.isOpen_compl).mem_nhds hβb
      rwa [Metric.mem_nhds_iff] at h
    obtain ⟨u, huA, huV⟩ : ∃ u : ℝ × ℝ,
        u ∈ Metric.ball ((-1 : ℝ), (0 : ℝ)) εa ∧ u ∈ V := by
      obtain ⟨u, hu⟩ := mem_closure_iff.mp haV _ Metric.isOpen_ball (mem_ball_self hεapos)
      exact ⟨u, hu.1, hu.2⟩
    obtain ⟨v, hvB, hvV⟩ : ∃ v : ℝ × ℝ,
        v ∈ Metric.ball ((1 : ℝ), (0 : ℝ)) εb ∧ v ∈ V := by
      obtain ⟨v, hv⟩ := mem_closure_iff.mp hbV _ Metric.isOpen_ball (mem_ball_self hεbpos)
      exact ⟨v, hv.1, hv.2⟩
    -- the three pieces
    set S1 : Set (ℝ × ℝ) := rect ∩ Metric.ball ((-1 : ℝ), (0 : ℝ)) εa with hS1
    set S2 : Set (ℝ × ℝ) := rect ∩ V with hS2
    set S3 : Set (ℝ × ℝ) := rect ∩ Metric.ball ((1 : ℝ), (0 : ℝ)) εb with hS3
    have hS2eq : S2 = V := by rw [hS2]; exact Set.inter_eq_right.mpr hVrect
    have hpc1 : IsPathConnected S1 := by
      rw [hS1]
      exact (rect_convex.inter (convex_ball _ _)).isPathConnected
        ⟨(-1, 0), by simp [mem_rect], mem_ball_self hεapos⟩
    have hpc2 : IsPathConnected S2 := by rw [hS2eq]; exact hVpc
    have hpc3 : IsPathConnected S3 := by
      rw [hS3]
      exact (rect_convex.inter (convex_ball _ _)).isPathConnected
        ⟨(1, 0), by simp [mem_rect], mem_ball_self hεbpos⟩
    have hne12 : (S1 ∩ S2).Nonempty :=
      ⟨u, ⟨by rw [hS1]; exact ⟨hVrect huV, huA⟩, by rw [hS2]; exact ⟨hVrect huV, huV⟩⟩⟩
    have hne23 : (S2 ∩ S3).Nonempty :=
      ⟨v, ⟨by rw [hS2]; exact ⟨hVrect hvV, hvV⟩, by rw [hS3]; exact ⟨hVrect hvV, hvB⟩⟩⟩
    have hpath : IsPathConnected (S1 ∪ S2 ∪ S3) :=
      IsPathConnected.union (IsPathConnected.union hpc1 hpc2 hne12) hpc3
        (hne23.mono (by rintro z ⟨hz2, hz3⟩; exact ⟨Or.inr hz2, hz3⟩))
    have hSsub : S1 ∪ S2 ∪ S3 ⊆ rect := by
      intro z hz
      rcases hz with hz | hz
      · rcases hz with hz | hz
        · rw [hS1] at hz; exact hz.1
        · rw [hS2] at hz; exact hz.1
      · rw [hS3] at hz; exact hz.1
    have hjoin : JoinedIn (S1 ∪ S2 ∪ S3) ((-1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) :=
      hpath.joinedIn _ (by left; left; rw [hS1]; exact ⟨by simp [mem_rect], mem_ball_self hεapos⟩)
        _ (by right; rw [hS3]; exact ⟨by simp [mem_rect], mem_ball_self hεbpos⟩)
    obtain ⟨P, hP⟩ := hjoin
    have hPS : Set.range P ⊆ S1 ∪ S2 ∪ S3 := Set.range_subset_iff.mpr hP
    -- the crossing
    obtain ⟨s, hs, t, ht, hst⟩ :=
      crossing_lemma_rect_of_Icc (h := ⇑P.extend) (v := fun t => β (-t))
        P.continuous_extend (hβc.comp continuous_neg)
        (fun t _ => hSsub (hPS (by rw [← Path.extend_range]; exact Set.mem_range_self t)))
        (fun t _ => hβrect (-t))
        (by rw [P.extend_of_le_zero (by norm_num)])
        (by rw [P.extend_of_one_le le_rfl])
        (by simp [hβ1]) (by simp [hβ0])
    have hneg : -t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hzβ : β (-t) ∈ β '' Set.Icc (-1 : ℝ) 1 := ⟨-t, hneg, rfl⟩
    have hzS : P.extend s ∈ S1 ∪ S2 ∪ S3 :=
      hPS (by rw [← Path.extend_range]; exact Set.mem_range_self s)
    rw [hst] at hzS
    rcases hzS with hz | hz
    · rcases hz with hz | hz
      · exact (hεa (by rw [hS1] at hz; exact hz.2)) hzβ
      · exact hβV _ hzβ (by rw [hS2] at hz; exact hz.2)
    · exact (hεb (by rw [hS3] at hz; exact hz.2)) hzβ
  intro y z hy hz hby hbz
  rw [hmain y hy hby, hmain z hz hbz]

/-- Uniqueness of the bounded component is invariant under postcomposition with a
boundedness-preserving self-homeomorphism of the plane. -/
theorem eq_of_isBounded_component_compl_of_image
    (e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (hb : ∀ S : Set (ℝ × ℝ), Bornology.IsBounded S → Bornology.IsBounded (e '' S))
    (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) (hinj : Function.Injective γ)
    (h : (∃ x : ℝ × ℝ, x ∉ Set.range (fun c => e (γ c)) ∧
            Bornology.IsBounded (connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) x)) →
         ∀ y z : ℝ × ℝ, y ∉ Set.range (fun c => e (γ c)) →
           z ∉ Set.range (fun c => e (γ c)) →
           Bornology.IsBounded (connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) y) →
           Bornology.IsBounded (connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) z) →
           connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) y =
             connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) z) :
    (∃ x : ℝ × ℝ, x ∉ Set.range γ ∧
        Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x)) →
    ∀ y z : ℝ × ℝ, y ∉ Set.range γ → z ∉ Set.range γ →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) y) →
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z) →
      connectedComponentIn ((Set.range γ)ᶜ) y = connectedComponentIn ((Set.range γ)ᶜ) z := by
  intro h₀ y z hy hz hby hbz
  have hcomp_eq : ∀ y : ℝ × ℝ, y ∉ Set.range γ →
      connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) (e y) =
        e '' connectedComponentIn ((Set.range γ)ᶜ) y := by
    intro y hy
    have hh := image_connectedComponentIn_homeomorph e (S := (Set.range γ)ᶜ) hy
    rw [Homeomorph.image_compl] at hh
    rw [show Set.range (fun c => e (γ c)) = e '' Set.range γ from Set.range_comp e γ]
    exact hh.symm
  have h0' : ∃ x : ℝ × ℝ, x ∉ Set.range (fun c => e (γ c)) ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) x) := by
    obtain ⟨x0, hx0, hb0⟩ := h₀
    refine ⟨e x0, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      exact hx0 ⟨c, e.injective hc⟩
    · rw [hcomp_eq x0 hx0]
      exact hb _ hb0
  have key := h h0' (e y) (e z) ?_ ?_ ?_ ?_
  · rw [hcomp_eq y hy, hcomp_eq z hz] at key
    exact Set.image_injective.mpr e.injective key
  · rintro ⟨c, hc⟩; exact hy ⟨c, e.injective hc⟩
  · rintro ⟨c, hc⟩; exact hz ⟨c, e.injective hc⟩
  · rw [hcomp_eq y hy]; exact hb _ hby
  · rw [hcomp_eq z hz]; exact hb _ hbz

end Work.RPB1a.Caratheodory.Brouwer
