import Mathlib
import Submission.Work.Whitney.PathTools.exists_hyperplane_slice_isTotallyDisconnected

/-!
# Auxiliary connectedness lemmas for the local room of a one-dimensional compact set

This file collects the elementary "there is room to walk around" lemmas needed to show that a
compact totally disconnected subset of a normed space of dimension `> 1` (and, more generally, a
countable union of such) does not separate.
-/

open Set Metric Topology Filter
open scoped Topology

namespace Work.Whitney.PathTools

variable {E : Type*}

/-- **Annulus.**  In a normed space of dimension `> 1` the region between two concentric spheres
is preconnected. -/
lemma isPreconnected_ball_sdiff_closedBall [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) (a : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsPreconnected (Metric.ball a R \ Metric.closedBall a r) := by
  have hnt : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
    exact ⟨x - y, sub_ne_zero.mpr hxy⟩
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u : E := ‖v‖⁻¹ • v
  have hunorm : ‖u‖ = 1 := by
    rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (ne_of_gt hvnorm)]
  let Ray : Set E := (fun t : ℝ => a + t • u) '' Set.Ioo r R
  have hRay : IsPreconnected Ray :=
    isPreconnected_Ioo.image _ (by fun_prop : ContinuousOn (fun t : ℝ => a + t • u) (Set.Ioo r R))
  have hUn : (⋃ s : Set.Ioo r R, Metric.sphere a s.1 ∪ Ray) = Metric.ball a R \ Metric.closedBall a r := by
    ext z; constructor
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨s, hs⟩ := hz
      rcases hs with hs | hs
      · rw [Metric.mem_sphere] at hs
        refine ⟨Metric.mem_ball.mpr (by rw [hs]; exact s.2.2), ?_⟩
        rw [Metric.mem_closedBall]
        rw [hs]; exact not_le.mpr s.2.1
      · obtain ⟨t, ht, rfl⟩ := hs
        refine ⟨Metric.mem_ball.mpr ?_, ?_⟩
        · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hunorm, mul_one,
            Real.norm_of_nonneg (le_of_lt (lt_trans hr ht.1))]
          exact ht.2
        · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hunorm,
            mul_one, Real.norm_of_nonneg (le_of_lt (lt_trans hr ht.1))]
          exact not_le.mpr ht.1
    · rintro ⟨hzR, hzr⟩
      rw [Set.mem_iUnion]
      refine ⟨⟨dist z a, ?_, ?_⟩, Or.inl (Metric.mem_sphere.mpr rfl)⟩
      · rw [Metric.mem_closedBall] at hzr; exact not_le.mp hzr
      · exact Metric.mem_ball.mp hzR
  rw [← hUn]
  refine isPreconnected_iUnion ?_ ?_
  · refine ⟨a + ((r + R) / 2) • u, ?_⟩
    rw [Set.mem_iInter]
    intro s
    exact Or.inr ⟨(r + R) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  · intro s
    refine (isPreconnected_sphere hrank a s.1).union (a + s.1 • u) ?_ ?_ hRay
    · rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, hunorm, mul_one,
        Real.norm_of_nonneg (le_of_lt (lt_trans hr s.2.1))]
    · exact ⟨s.1, ⟨s.2.1, s.2.2⟩, rfl⟩

/-- **Removal with a room.**  If `T` is preconnected and open, `C` is closed, and `V` is an open
set with `C ⊆ V ⊆ T` whose complement of `C` is preconnected, then `T \ C` is preconnected. -/
lemma isPreconnected_sdiff_of_isClosed_of_room {X : Type*} [TopologicalSpace X] {T C V : Set X}
    (hT : IsPreconnected T) (hTo : IsOpen T) (hC : IsClosed C) (hVo : IsOpen V)
    (hCV : C ⊆ V) (hVT : V ⊆ T) (hVp : IsPreconnected (V \ C)) :
    IsPreconnected (T \ C) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hT ⊢
  intro u v hu hv huv huvdisj
  have hVcov : V \ C ⊆ u ∪ v := fun x hx => huv ⟨hVT hx.1, hx.2⟩
  have hVdisj : (V \ C) ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨⟨hVT hx1.1, hx1.2⟩, hx2⟩
  have h1o : IsOpen (((T \ C) ∩ u) ∪ V) := (hTo.sdiff hC).inter hu |>.union hVo
  have h2o : IsOpen ((T \ C) ∩ v) := (hTo.sdiff hC).inter hv
  have h1o' : IsOpen (((T \ C) ∩ v) ∪ V) := (hTo.sdiff hC).inter hv |>.union hVo
  have h2o' : IsOpen ((T \ C) ∩ u) := (hTo.sdiff hC).inter hu
  have hcov₁ : T ⊆ (((T \ C) ∩ u) ∪ V) ∪ ((T \ C) ∩ v) := by
    intro x hxT
    by_cases hxC : x ∈ C
    · exact Or.inl (Or.inr (hCV hxC))
    · have hx' : x ∈ T \ C := ⟨hxT, hxC⟩
      rcases huv hx' with hxu | hxv
      · exact Or.inl (Or.inl ⟨hx', hxu⟩)
      · exact Or.inr ⟨hx', hxv⟩
  have hcov₂ : T ⊆ (((T \ C) ∩ v) ∪ V) ∪ ((T \ C) ∩ u) := by
    intro x hxT
    by_cases hxC : x ∈ C
    · exact Or.inl (Or.inr (hCV hxC))
    · have hx' : x ∈ T \ C := ⟨hxT, hxC⟩
      rcases huv hx' with hxu | hxv
      · exact Or.inr ⟨hx', hxu⟩
      · exact Or.inl (Or.inl ⟨hx', hxv⟩)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hVp) u v hu hv hVcov hVdisj with hVu | hVv
  · have hdisj₁ : T ∩ ((((T \ C) ∩ u) ∪ V) ∩ ((T \ C) ∩ v)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxT, hx1, hx2⟩
      rcases hx1 with ⟨hx1a, hxu⟩ | hxV
      · exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨hx1a, hxu, hx2.2⟩
      · exact Set.eq_empty_iff_forall_notMem.mp hVdisj x ⟨⟨hxV, hx2.1.2⟩, hVu ⟨hxV, hx2.1.2⟩, hx2.2⟩
    rcases hT _ _ h1o h2o hcov₁ hdisj₁ with h | h
    · left
      intro x hx
      rcases h hx.1 with ⟨hx', hxu⟩ | hxV
      · exact hxu
      · exact hVu ⟨hxV, hx.2⟩
    · right
      intro x hx
      exact (h hx.1).2
  · have hdisj₂ : T ∩ ((((T \ C) ∩ v) ∪ V) ∩ ((T \ C) ∩ u)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxT, hx1, hx2⟩
      rcases hx1 with ⟨hx1a, hxv⟩ | hxV
      · exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨hx1a, hx2.2, hxv⟩
      · exact Set.eq_empty_iff_forall_notMem.mp hVdisj x ⟨⟨hxV, hx2.1.2⟩, hx2.2, hVv ⟨hxV, hx2.1.2⟩⟩
    rcases hT _ _ h1o' h2o' hcov₂ hdisj₂ with h | h
    · right
      intro x hx
      rcases h hx.1 with ⟨hx', hxv⟩ | hxV
      · exact hxv
      · exact hVv ⟨hxV, hx.2⟩
    · left
      intro x hx
      exact (h hx.1).2

/-- A finite family of positive reals has a positive lower bound. -/
lemma exists_pos_lt_all {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ < f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert i₀ s hi₀ ih =>
      have hf' : ∀ i ∈ s, 0 < f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      obtain ⟨δ, hδpos, hδlt⟩ := ih hf'
      refine ⟨min δ (f i₀ / 2), lt_min hδpos (by linarith [hf i₀ (Finset.mem_insert_self i₀ s)]), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hf i (Finset.mem_insert_self i s)])
      · exact lt_of_le_of_lt (min_le_left _ _) (hδlt i hi)

/-- If the closed ball around `a` of radius `ρ` sits in the open ball around `c` of radius `r`,
then `dist a c + ρ < r` (when `ρ > 0` and the space is nontrivial). -/
lemma dist_add_radius_lt_of_closedBall_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {a c : E} {ρ r : ℝ} (hρ : 0 < ρ)
    (h : Metric.closedBall a ρ ⊆ Metric.ball c r) : dist a c + ρ < r := by
  rw [dist_eq_norm]
  rcases eq_or_ne a c with hac | hac
  · subst hac
    obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      exact ⟨‖v‖⁻¹ • v, by
        rw [norm_smul, Real.norm_of_nonneg (by positivity),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    have hmem : a + ρ • u ∈ Metric.closedBall a ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_of_nonneg hρ.le]
    have hlt := Metric.mem_ball.mp (h hmem)
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_of_nonneg hρ.le] at hlt
    simpa using hlt
  · set v : E := a - c with hv
    have hvne : v ≠ 0 := sub_ne_zero.mpr hac
    have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hmem : a + (ρ / ‖v‖) • v ∈ Metric.closedBall a ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_div,
        Real.norm_of_nonneg hρ.le, norm_norm, div_mul_cancel₀ ρ (ne_of_gt hvn)]
    have hlt := Metric.mem_ball.mp (h hmem)
    have hcalc : ‖a + (ρ / ‖v‖) • v - c‖ = ‖v‖ + ρ := by
      have h1 : a + (ρ / ‖v‖) • v - c = (1 + ρ / ‖v‖) • v := by
        rw [hv]; module
      rw [h1, norm_smul, Real.norm_of_nonneg (by positivity), add_mul, one_mul,
        div_mul_cancel₀ ρ (ne_of_gt hvn)]
    rw [dist_eq_norm, hcalc] at hlt
    exact hlt

/-- **Ball with finitely many disjoint closed balls removed.** -/
lemma isPreconnected_ball_sdiff_closedBalls [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) {c : E} {r : ℝ} (hr : 0 < r) {ι : Type*}
    (s : Finset ι) (a : ι → E) (ρ : ι → ℝ) (hρ : ∀ i ∈ s, 0 < ρ i)
    (hsub : ∀ i ∈ s, Metric.closedBall (a i) (ρ i) ⊆ Metric.ball c r)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ρ i + ρ j < dist (a i) (a j)) :
    IsPreconnected (Metric.ball c r \ ⋃ i ∈ s, Metric.closedBall (a i) (ρ i)) := by
  classical
  haveI : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  induction s using Finset.induction_on with
  | empty => simpa using Metric.isPreconnected_ball (x := c) (r := r)
  | insert i₀ s hi₀ ih =>
      have hρ₀ : 0 < ρ i₀ := hρ i₀ (Finset.mem_insert_self i₀ s)
      have hsub₀ : Metric.closedBall (a i₀) (ρ i₀) ⊆ Metric.ball c r :=
        hsub i₀ (Finset.mem_insert_self i₀ s)
      have ihs : IsPreconnected (Metric.ball c r \ ⋃ i ∈ s, Metric.closedBall (a i) (ρ i)) :=
        ih (fun i hi => hρ i (Finset.mem_insert_of_mem hi))
           (fun i hi => hsub i (Finset.mem_insert_of_mem hi))
           (fun i hi j hj hij => hgap i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
      have hslack0 : 0 < r - dist (a i₀) c - ρ i₀ := by
        have := dist_add_radius_lt_of_closedBall_subset_ball hρ₀ hsub₀
        linarith
      have hslack : ∀ i ∈ s, 0 < dist (a i₀) (a i) - ρ i₀ - ρ i := by
        intro i hi
        have h := hgap i₀ (Finset.mem_insert_self i₀ s) i (Finset.mem_insert_of_mem hi)
          (fun h => hi₀ (h.symm ▸ hi))
        linarith
      obtain ⟨δ, hδpos, hδlt⟩ := exists_pos_lt_all s
        (fun i => dist (a i₀) (a i) - ρ i₀ - ρ i) hslack
      set δ' : ℝ := min δ (min ((r - dist (a i₀) c - ρ i₀) / 2) 1) with hδ'def
      have hδ'pos : 0 < δ' := lt_min hδpos (lt_min (by linarith [hslack0]) one_pos)
      have hδ'ball : dist (a i₀) c + ρ i₀ + δ' < r := by
        have h3 : δ' ≤ (r - dist (a i₀) c - ρ i₀) / 2 :=
          le_trans (min_le_right δ _) (min_le_left _ _)
        linarith
      have hδ'gap : ∀ i ∈ s, ρ i₀ + ρ i + δ' < dist (a i₀) (a i) := by
        intro i hi
        have h1 : δ' < dist (a i₀) (a i) - ρ i₀ - ρ i := lt_of_le_of_lt (min_le_left δ _) (hδlt i hi)
        linarith
      -- closedness of the removed part and of the previous removed part
      have hclosed : IsClosed (⋃ i ∈ s, Metric.closedBall (a i) (ρ i)) :=
        s.finite_toSet.isClosed_biUnion (fun i _ => Metric.isClosed_closedBall)
      -- the room
      have hVT : Metric.ball (a i₀) (ρ i₀ + δ') ⊆
          Metric.ball c r \ ⋃ i ∈ s, Metric.closedBall (a i) (ρ i) := by
        intro z hz
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball] at hz ⊢
          calc dist z c ≤ dist z (a i₀) + dist (a i₀) c := dist_triangle _ _ _
            _ < ρ i₀ + δ' + dist (a i₀) c := by linarith
            _ < r := by linarith [hδ'ball]
        · intro hzU
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzU
          obtain ⟨his, hzi⟩ := Set.mem_iUnion.mp hi
          have hdisj := Metric.ball_disjoint_closedBall (x := a i₀) (y := a i)
            (δ := ρ i₀ + δ') (ε := ρ i)
            (le_of_lt (by linarith [hδ'gap i his]))
          exact Set.disjoint_left.mp hdisj hz hzi
      have hrem := isPreconnected_sdiff_of_isClosed_of_room ihs
        (Metric.isOpen_ball.sdiff hclosed) Metric.isClosed_closedBall Metric.isOpen_ball
        (Metric.closedBall_subset_ball (by linarith)) hVT
        (isPreconnected_ball_sdiff_closedBall hrank (a i₀) hρ₀ (by linarith))
      have hset : Metric.ball c r \ ⋃ i ∈ insert i₀ s, Metric.closedBall (a i) (ρ i)
          = (Metric.ball c r \ ⋃ i ∈ s, Metric.closedBall (a i) (ρ i))
              \ Metric.closedBall (a i₀) (ρ i₀) := by
        ext z
        constructor
        · intro hz
          rw [Set.mem_sdiff] at hz ⊢
          obtain ⟨hz1, hz2⟩ := hz
          refine ⟨⟨hz1, ?_⟩, ?_⟩
          · intro h
            obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
            obtain ⟨his, hzi⟩ := Set.mem_iUnion.mp hi
            exact hz2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
              ⟨Finset.mem_insert_of_mem his, hzi⟩⟩)
          · intro h
            exact hz2 (Set.mem_iUnion.mpr ⟨i₀, Set.mem_iUnion.mpr
              ⟨Finset.mem_insert_self i₀ s, h⟩⟩)
        · intro hz
          rw [Set.mem_sdiff] at hz ⊢
          obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
          refine ⟨hz1, ?_⟩
          intro h
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
          obtain ⟨hor, hzi⟩ := Set.mem_iUnion.mp hi
          rcases Finset.mem_insert.mp hor with hi | hi
          · exact hz3 (hi ▸ hzi)
          · exact hz2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hzi⟩⟩)
      rw [hset]
      exact hrem

/-- **A compact countable union of compact totally disconnected sets is totally disconnected.** -/
theorem isTotallyDisconnected_of_isCompact_biUnion {E : Type*} [MetricSpace E]
    {ι : Type*} [Countable ι] {D : ι → Set E} (hDc : ∀ i, IsCompact (D i))
    (hDtd : ∀ i, IsTotallyDisconnected (D i)) (hK : IsCompact (⋃ i, D i)) :
    IsTotallyDisconnected (⋃ i, D i) := by
  intro t ht htp
  refine fun x hx y hy => by_contra fun hxy => ?_
  set C : Set E := closure t with hC
  have hCt : C ⊆ ⋃ i, D i := closure_minimal ht hK.isClosed
  have hCcpt : IsCompact C := hK.of_isClosed_subset isClosed_closure hCt
  have hCpre : IsPreconnected C := htp.closure
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCcpt
  haveI : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hCpre
  haveI : Nontrivial C :=
    ⟨⟨⟨x, subset_closure hx⟩, ⟨y, subset_closure hy⟩, fun h => hxy (congrArg Subtype.val h)⟩⟩
  set f : ι → Set C := fun i => ((↑) : C → E) ⁻¹' (D i) with hf
  have hfcl : ∀ i, IsClosed (f i) := fun i => (hDc i).isClosed.preimage continuous_subtype_val
  have hfcover : (⋃ i, f i) = univ := by
    rw [eq_univ_iff_forall]
    intro z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCt z.2)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hfcl hfcover
  have hUtd : IsTotallyDisconnected (interior (f i)) := by
    intro s hs hsp
    have himg : IsPreconnected (((↑) : C → E) '' s) :=
      hsp.image _ continuous_subtype_val.continuousOn
    have hsub : ((↑) : C → E) '' s ⊆ D i := fun z hz => by
      obtain ⟨w, hw, rfl⟩ := hz
      have h1 : w ∈ f i := interior_subset (hs hw)
      exact h1
    have hsub' : (((↑) : C → E) '' s).Subsingleton := hDtd i _ hsub himg
    exact fun a ha b hb => Subtype.ext (hsub' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  have := no_open_totallyDisconnected_subset isOpen_interior hUtd
  exact hi.ne_empty this

end Work.Whitney.PathTools
