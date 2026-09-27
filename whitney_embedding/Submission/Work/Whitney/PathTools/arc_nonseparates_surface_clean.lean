import Mathlib
import Submission.Work.Whitney.PathTools.LocalRoomAux
import Submission.Work.Whitney.PathTools.arc_accumulation
import Submission.Work.Whitney.PathTools.arc_room_lemma
import Submission.Work.Whitney.PathTools.plane_arc_nonseparation
import Submission.Work.Whitney.PathTools.interior_image_arc_empty
import Submission.Work.Whitney.PathTools.minimal_separator_no_cut_point
import Submission.Work.Whitney.PathTools.arc_interior_empty_surface
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite

/-!
# An arc does not separate a surface

Main target: `Work.Whitney.PathTools.arc_nonseparates_surface_clean`: if `W` is an open path
connected set in a topological `2`-manifold and `γ '' [0,1]` is a compact arc lying in `W`, then
`W \ γ '' [0,1]` is preconnected.

The proof *peels* the arc from its right end down to its left end.  Write
`R s := W \ γ '' [s,1]` for `s ∈ [0,1]`.

* `Peel.janis_singleton_closed` — Janiszewski's theorem in the plane in the form needed below
  (a compact and a closed set meeting in one point do not separate the plane), deduced from the
  proven compact-compact single-point theorem `Grid.janis_singleton_plane`.
* `Peel.planar_slit` — a planar open preconnected set with a *slit with a free end* removed stays
  preconnected (the local engine of the whole argument).
* `Peel.peel_step` — the crux: if `R s` is preconnected and the arc piece `γ '' [s',s]` lies in a
  single chart source, then `R s'` is preconnected.  Proof: the room criterion with room
  `V := e.symm '' Ωp`, where `Ωp` is the component of `e (γ s')` in the chart picture of `R s`;
  the planar slit lemma shows `Ωp \ e '' γ '' (s',s)` is preconnected.  This is why no hypothesis
  on the geometry of the *past* part of the arc is needed.
* `Peel.preconnected_suffix` — a Lebesgue number for the chart cover of the arc makes the step
  size `ε` of `peel_step` uniform; a finite induction starting from `R 1 = W \ {γ 1}` (removing a
  single point, `isPreconnected_diff_singleton`) then gives `IsPreconnected (R t)` for every
  `t ∈ [0,1]`, in particular for `t = 0`.

The file also retains the older "room assembly" `surface_arc_room_of_inputs` (which reduces the
target to four local inputs) and `chartBall_sdiff_arc_isPathConnected`.
-/

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped Topology

noncomputable section

/-- **Room criterion, `IsClosedIn` form.**  If `T` is preconnected, `T \ C` is open, `V` is an
open set with `C ⊆ V ⊆ T` whose complement of `C` inside `V` is preconnected, then `T \ C` is
preconnected.  (Same proof as `isPreconnected_sdiff_of_isClosed_of_room`, which only uses the
openness of `T \ C`.) -/
lemma isPreconnected_sdiff_of_isClosedIn_of_room {X : Type*} [TopologicalSpace X] {T C V : Set X}
    (hT : IsPreconnected T) (hTC : IsOpen (T \ C)) (hVo : IsOpen V)
    (hCV : C ⊆ V) (hVT : V ⊆ T) (hVp : IsPreconnected (V \ C)) :
    IsPreconnected (T \ C) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hT ⊢
  intro u v hu hv huv huvdisj
  have hVcov : V \ C ⊆ u ∪ v := fun x hx => huv ⟨hVT hx.1, hx.2⟩
  have hVdisj : (V \ C) ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨⟨hVT hx1.1, hx1.2⟩, hx2⟩
  have h1o : IsOpen (((T \ C) ∩ u) ∪ V) := hTC.inter hu |>.union hVo
  have h2o : IsOpen ((T \ C) ∩ v) := hTC.inter hv
  have h1o' : IsOpen (((T \ C) ∩ v) ∪ V) := hTC.inter hv |>.union hVo
  have h2o' : IsOpen ((T \ C) ∩ u) := hTC.inter hu
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
      · exact Set.eq_empty_iff_forall_notMem.mp hVdisj x
          ⟨⟨hxV, hx2.1.2⟩, hVu ⟨hxV, hx2.1.2⟩, hx2.2⟩
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
      · exact Set.eq_empty_iff_forall_notMem.mp hVdisj x
          ⟨⟨hxV, hx2.1.2⟩, hx2.2, hVv ⟨hxV, hx2.1.2⟩⟩
    rcases hT _ _ h1o' h2o' hcov₂ hdisj₂ with h | h
    · right
      intro x hx
      rcases h hx.1 with ⟨hx', hxv⟩ | hxV
      · exact hxv
      · exact hVv ⟨hxV, hx.2⟩
    · left
      intro x hx
      exact (h hx.1).2

/-- **A chart ball minus a compact arc inside it is path connected.** -/
theorem chartBall_sdiff_arc_isPathConnected {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {z : EuclideanSpace ℝ (Fin 2)}
    {ρ : ℝ} (hρ : 0 < ρ) (hcl : Metric.closedBall z ρ ⊆ c.target)
    {γ : ℝ → M} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    (hsub : γ '' K ⊆ c.symm '' Metric.ball z ρ) :
    IsPathConnected (c.symm '' Metric.ball z ρ \ γ '' K) := by
  have hballT : Metric.ball z ρ ⊆ c.target := Metric.ball_subset_closedBall.trans hcl
  -- the arc lies in the chart source
  have hsrc : γ '' K ⊆ c.source := by
    rintro m ⟨t, ht, rfl⟩
    obtain ⟨w, hw, hwγ⟩ := hsub ⟨t, ht, rfl⟩
    rw [← hwγ]
    exact c.map_target (hballT hw)
  -- the trace in the chart
  set Ae : Set (EuclideanSpace ℝ (Fin 2)) := (fun t => c (γ t)) '' K with hAedef
  have hcontOn : ContinuousOn (fun t => c (γ t)) K :=
    c.continuousOn.comp hcont (fun t ht => hsrc ⟨t, ht, rfl⟩)
  have hinjOn : Set.InjOn (fun t => c (γ t)) K := by
    intro s hs t ht hst
    exact hinj hs ht (c.injOn (hsrc ⟨s, hs, rfl⟩) (hsrc ⟨t, ht, rfl⟩) hst)
  have hAe_sub : Ae ⊆ Metric.ball z ρ := by
    rintro w ⟨t, ht, rfl⟩
    obtain ⟨w', hw', hw'γ⟩ := hsub ⟨t, ht, rfl⟩
    have : c (γ t) = w' := by rw [← hw'γ]; exact c.right_inv (hballT hw')
    simpa only [this] using hw'
  have hAe_cpt : IsCompact Ae := by
    rw [hAedef]; exact hK.image_of_continuousOn hcontOn
  have hcompl : IsPathConnected (Aeᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hAedef]; exact plane_arc_nonseparation hK hcontOn hinjOn
  have hAe_int : interior Ae = ∅ := by
    rw [hAedef]; exact interior_image_arc_empty hK hcontOn hinjOn
  have hne : (Metric.ball z ρ \ Ae).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : Metric.ball z ρ ⊆ Ae := by
      intro w hw
      by_contra hwAe
      exact Set.eq_empty_iff_forall_notMem.mp hcon w ⟨hw, hwAe⟩
    have h1 : interior (Metric.ball z ρ) ⊆ interior Ae := interior_mono hsub
    rw [Metric.isOpen_ball.interior_eq, hAe_int] at h1
    exact h1 (Metric.mem_ball_self hρ)
  have hplanar : IsPathConnected (Metric.ball z ρ \ Ae) :=
    isPathConnected_iff.mpr ⟨hne, fun X hX Y hY =>
      joinedIn_ball_sdiff_arc_of_subset_ball (p := z) (r := ρ) hρ hK hcontOn hinjOn
        hAe_sub hX hY⟩
  have hEq : c.symm '' (Metric.ball z ρ \ Ae) = c.symm '' Metric.ball z ρ \ γ '' K := by
    ext m
    constructor
    · rintro ⟨w, ⟨hw, hwAe⟩, rfl⟩
      refine ⟨⟨w, hw, rfl⟩, ?_⟩
      rintro ⟨t, ht, htm⟩
      have h1 : c (γ t) = w := by rw [htm, c.right_inv (hballT hw)]
      exact hwAe ⟨t, ht, h1⟩
    · rintro ⟨⟨w, hw, rfl⟩, hmK⟩
      refine ⟨w, ⟨hw, ?_⟩, rfl⟩
      intro hwAe
      obtain ⟨t, ht, htw⟩ := hwAe
      have htw' : c (γ t) = w := htw
      exact hmK ⟨t, ht, by rw [← htw']; exact (c.left_inv (hsrc ⟨t, ht, rfl⟩)).symm⟩
  rw [← hEq]
  exact hplanar.image' (c.continuousOn_symm.mono (fun w hw => hballT hw.1))

theorem surface_arc_room_of_inputs {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPathConnected W)
    {γ : ℝ → M} (hγ : Continuous γ) (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hWγ : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W)
    (hAint : interior (γ '' Set.Icc (0:ℝ) 1) = ∅)
    (hPacL : ∃ (U : Set M) (c : ℝ), IsOpen U ∧ U ⊆ W ∧ γ 0 ∈ U ∧ 0 < c ∧ c ≤ 1 ∧
      U ∩ γ '' Set.Icc (0:ℝ) 1 = γ '' (Set.Ico 0 c) ∧
      IsPreconnected (U \ γ '' Set.Icc (0:ℝ) 1))
    (hPacR : ∃ (U : Set M) (c : ℝ), IsOpen U ∧ U ⊆ W ∧ γ 1 ∈ U ∧ 0 ≤ c ∧ c < 1 ∧
      U ∩ γ '' Set.Icc (0:ℝ) 1 = γ '' (Set.Ioc c 1) ∧
      IsPreconnected (U \ γ '' Set.Icc (0:ℝ) 1) ∧ (0 < c → γ c ∈ frontier U))
    (hPiece : ∀ t ∈ Set.Ioo (0:ℝ) 1, ∃ (U : Set M) (c d : ℝ), IsOpen U ∧ U ⊆ W ∧ γ t ∈ U ∧
      c < t ∧ t < d ∧ Set.Ioo c d ⊆ Set.Icc (0:ℝ) 1 ∧
      U ∩ γ '' Set.Icc (0:ℝ) 1 = γ '' (Set.Ioo c d) ∧
      ∀ z ∈ U \ γ '' Set.Icc (0:ℝ) 1,
        γ '' Set.Ioo c t ⊆ closure (connectedComponentIn (U \ γ '' Set.Icc (0:ℝ) 1) z)) :
    IsPreconnected (W \ γ '' Set.Icc (0:ℝ) 1) := by
  classical
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := 2)
  haveI : LocallyConnectedSpace M := inferInstance
  set A : Set M := γ '' Set.Icc (0:ℝ) 1 with hAdef
  have hAclosed : IsClosed A := (isCompact_Icc.image hγ).isClosed
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huvdisj
  by_cases hune : ((W \ A) ∩ u).Nonempty
  · by_cases hvne : ((W \ A) ∩ v).Nonempty
    · exfalso
      obtain ⟨U₀, c₀, hU₀open, hU₀W, hγ₀U₀, hc₀pos, hc₀le, hU₀A, hU₀pre⟩ := hPacL
      obtain ⟨U₁, c₁, hU₁open, hU₁W, hγ₁U₁, hc₁nn, hc₁lt, hU₁A, hU₁pre, hU₁fr⟩ := hPacR
      have hU₀side : U₀ \ A ⊆ u ∨ U₀ \ A ⊆ v :=
        (isPreconnected_iff_subset_of_disjoint.mp hU₀pre) u v hu hv
          (fun z hz => huv ⟨hU₀W hz.1, hz.2⟩)
          (by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨hz, hzu, hzv⟩
            exact (Set.eq_empty_iff_forall_notMem.mp huvdisj) z
              ⟨⟨hU₀W hz.1, hz.2⟩, hzu, hzv⟩)
      have hU₁side : U₁ \ A ⊆ u ∨ U₁ \ A ⊆ v :=
        (isPreconnected_iff_subset_of_disjoint.mp hU₁pre) u v hu hv
          (fun z hz => huv ⟨hU₁W hz.1, hz.2⟩)
          (by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro z ⟨hz, hzu, hzv⟩
            exact (Set.eq_empty_iff_forall_notMem.mp huvdisj) z
              ⟨⟨hU₁W hz.1, hz.2⟩, hzu, hzv⟩)
      -- main contradiction, assuming `U₀ \ A ⊆ u'`
      have key : ∀ (u' v' : Set M), IsOpen u' → IsOpen v' → W \ A ⊆ u' ∪ v' →
          (W \ A) ∩ (u' ∩ v') = ∅ → ((W \ A) ∩ v').Nonempty → U₀ \ A ⊆ u' →
          (U₁ \ A ⊆ u') ∨ (U₁ \ A ⊆ v') → False := by
        intro u' v' hu' hv' huv' hdisj' hvne' h0 h1side
        have hp0 : γ 0 ∉ closure v' := by
          intro hpcl
          obtain ⟨z, hzU₀, hzv⟩ := (_root_.mem_closure_iff.mp hpcl) U₀ hU₀open hγ₀U₀
          have hsub : U₀ ∩ v' ⊆ A := by
            rintro w ⟨hwU₀, hwv⟩
            by_contra hwA
            exact (Set.eq_empty_iff_forall_notMem.mp hdisj') w
              ⟨⟨hU₀W hwU₀, hwA⟩, h0 ⟨hwU₀, hwA⟩, hwv⟩
          have hInt := interior_maximal hsub (hU₀open.inter hv')
          rw [hAint] at hInt
          exact hInt ⟨hzU₀, hzv⟩
        have hTne : ∃ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ closure v' := by
          obtain ⟨z₁, hz₁⟩ := hvne'
          have hacc := closure_connectedComponentIn_diff_inter_nonempty (X := M) (U := W) (C := A)
            hW hWc.isConnected.isPreconnected (hW.sdiff hAclosed)
            ⟨γ 0, ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩⟩
            (fun z hz => by obtain ⟨t, ht, rfl⟩ := hz; exact hWγ t ht) hz₁.1
          have hZv : connectedComponentIn (W \ A) z₁ ⊆ v' := by
            have hZpre : IsPreconnected (connectedComponentIn (W \ A) z₁) :=
              isPreconnected_connectedComponentIn
            have hZsub : connectedComponentIn (W \ A) z₁ ⊆ W \ A :=
              connectedComponentIn_subset (W \ A) z₁
            rcases (isPreconnected_iff_subset_of_disjoint.mp hZpre) u' v' hu' hv'
              (fun z hz => huv' (hZsub hz)) (by
                rw [Set.eq_empty_iff_forall_notMem]
                rintro z ⟨hz, hzu, hzv⟩
                exact (Set.eq_empty_iff_forall_notMem.mp hdisj') z ⟨hZsub hz, hzu, hzv⟩) with h | h
            · exfalso
              exact (Set.eq_empty_iff_forall_notMem.mp hdisj') z₁
                ⟨hz₁.1, h (mem_connectedComponentIn hz₁.1), hz₁.2⟩
            · exact h
          obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hacc
          obtain ⟨t, ht, htw⟩ := hw.2
          exact ⟨t, ht, htw ▸ closure_mono hZv hw.1⟩
        set T : Set ℝ := {t : ℝ | γ t ∈ closure v'} with hTdef
        have hTclosed : IsClosed T := isClosed_closure.preimage hγ
        have hKne : (T ∩ Set.Icc (0:ℝ) 1).Nonempty := by
          obtain ⟨t, ht, htT⟩ := hTne
          exact ⟨t, htT, ht⟩
        set tstar : ℝ := sInf (T ∩ Set.Icc (0:ℝ) 1) with htstardef
        have hbdd : BddBelow (T ∩ Set.Icc (0:ℝ) 1) := ⟨0, fun x hx => hx.2.1⟩
        have htmem : tstar ∈ T ∩ Set.Icc (0:ℝ) 1 :=
          (hTclosed.inter isClosed_Icc).csInf_mem hKne hbdd
        have htstarT : γ tstar ∈ closure v' := htmem.1
        have htstarIcc : tstar ∈ Set.Icc (0:ℝ) 1 := htmem.2
        have hmin : ∀ t ∈ T ∩ Set.Icc (0:ℝ) 1, tstar ≤ t := fun t ht => csInf_le hbdd ht
        have hpos : 0 < tstar := by
          rcases htstarIcc.1.lt_or_eq with h | h
          · exact h
          · exfalso
            exact hp0 (h ▸ htstarT)
        have hlt : tstar < 1 := by
          rcases h1side with h1 | h1
          · have hq : γ 1 ∉ closure v' := by
              intro hqcl
              obtain ⟨z, hzU₁, hzv⟩ := (_root_.mem_closure_iff.mp hqcl) U₁ hU₁open hγ₁U₁
              have hsub : U₁ ∩ v' ⊆ A := by
                rintro w ⟨hwU₁, hwv⟩
                by_contra hwA
                exact (Set.eq_empty_iff_forall_notMem.mp hdisj') w
                  ⟨⟨hU₁W hwU₁, hwA⟩, h1 ⟨hwU₁, hwA⟩, hwv⟩
              have hInt := interior_maximal hsub (hU₁open.inter hv')
              rw [hAint] at hInt
              exact hInt ⟨hzU₁, hzv⟩
            have hnotT : (1 : ℝ) ∉ T := hq
            rcases htstarIcc.2.lt_or_eq with h | h
            · exact h
            · exact absurd (h ▸ htstarT) hnotT
          · by_cases hc₁ : c₁ = 0
            · exfalso
              have hγ0cl : γ 0 ∈ closure U₁ := by
                rw [_root_.mem_closure_iff]
                intro O hO hγ0O
                have hnhds : γ ⁻¹' O ∈ 𝓝 (0:ℝ) := hγ.continuousAt (hO.mem_nhds hγ0O)
                obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hnhds
                set s : ℝ := min (δ/2) (1/2) with hsdef
                have hspos : 0 < s := lt_min (by linarith) (by norm_num)
                have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
                have hs1 : s ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
                have hsO : γ s ∈ O := hδ (by
                  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hspos]; exact hsδ)
                have hsU₁ : γ s ∈ U₁ := by
                  have hmem : γ s ∈ U₁ ∩ A := by
                    rw [hU₁A]
                    exact ⟨s, ⟨by rw [hc₁]; exact hspos, hs1⟩, rfl⟩
                  exact hmem.1
                exact ⟨γ s, hsO, hsU₁⟩
              obtain ⟨z, hzU₀, hzU₁⟩ := (_root_.mem_closure_iff.mp hγ0cl) U₀ hU₀open hγ₀U₀
              have hne : ((U₀ ∩ U₁) \ A).Nonempty := by
                by_contra h
                rw [Set.not_nonempty_iff_eq_empty] at h
                have hsub : U₀ ∩ U₁ ⊆ A := by
                  intro w hw
                  by_contra hwA
                  exact (Set.eq_empty_iff_forall_notMem.mp h) w ⟨hw, hwA⟩
                have hInt := interior_maximal hsub (hU₀open.inter hU₁open)
                rw [hAint] at hInt
                exact hInt ⟨hzU₀, hzU₁⟩
              obtain ⟨w, hw⟩ := hne
              exact (Set.eq_empty_iff_forall_notMem.mp hdisj') w
                ⟨⟨hU₀W hw.1.1, hw.2⟩, h0 ⟨hw.1.1, hw.2⟩, h1 ⟨hw.1.2, hw.2⟩⟩
            · have hc₁pos : 0 < c₁ := lt_of_le_of_ne hc₁nn (Ne.symm hc₁)
              have hc₁cl : γ c₁ ∈ closure v' := by
                rw [_root_.mem_closure_iff]
                intro O hO hc₁O
                have hcl : γ c₁ ∈ closure U₁ := (hU₁fr hc₁pos).1
                obtain ⟨z, hzO, hzU₁⟩ := (_root_.mem_closure_iff.mp hcl) O hO hc₁O
                have hne : ((O ∩ U₁) \ A).Nonempty := by
                  by_contra h
                  rw [Set.not_nonempty_iff_eq_empty] at h
                  have hsub : O ∩ U₁ ⊆ A := by
                    intro w hw
                    by_contra hwA
                    exact (Set.eq_empty_iff_forall_notMem.mp h) w ⟨hw, hwA⟩
                  have hInt := interior_maximal hsub (hO.inter hU₁open)
                  rw [hAint] at hInt
                  exact hInt ⟨hzO, hzU₁⟩
                obtain ⟨w, hw⟩ := hne
                exact ⟨w, hw.1.1, h1 ⟨hw.1.2, hw.2⟩⟩
              have : tstar ≤ c₁ := hmin c₁ ⟨hc₁cl, ⟨hc₁nn, hc₁lt.le⟩⟩
              linarith
        obtain ⟨Us, cs, ds, hUsopen, hUsW, hγtUs, hcst, htds, hIoo, hUsA, hUscl⟩ :=
          hPiece tstar ⟨hpos, hlt⟩
        by_cases hsub : Us ∩ v' ⊆ A
        · exfalso
          obtain ⟨z, hz⟩ := (_root_.mem_closure_iff.mp htstarT) Us hUsopen hγtUs
          have hInt := interior_maximal hsub (hUsopen.inter hv')
          rw [hAint] at hInt
          exact hInt hz
        · obtain ⟨z, hzin, hzAnot⟩ := Set.not_subset.mp hsub
          obtain ⟨hzUs, hzv'v⟩ := hzin
          have hzUA : z ∈ Us \ A := ⟨hzUs, hzAnot⟩
          have hzWA : z ∈ W \ A := ⟨hUsW hzUs, hzAnot⟩
          have hcomp : connectedComponentIn (Us \ A) z ⊆ v' := by
            have hZpre : IsPreconnected (connectedComponentIn (Us \ A) z) :=
              isPreconnected_connectedComponentIn
            have hZsub : connectedComponentIn (Us \ A) z ⊆ W \ A :=
              fun x hx => ⟨hUsW (connectedComponentIn_subset (Us \ A) z hx).1,
                (connectedComponentIn_subset (Us \ A) z hx).2⟩
            rcases (isPreconnected_iff_subset_of_disjoint.mp hZpre) u' v' hu' hv'
              (fun x hx => huv' (hZsub hx)) (by
                rw [Set.eq_empty_iff_forall_notMem]
                rintro x ⟨hx, hxu, hxv⟩
                exact (Set.eq_empty_iff_forall_notMem.mp hdisj') x ⟨hZsub hx, hxu, hxv⟩) with h | h
            · exfalso
              exact (Set.eq_empty_iff_forall_notMem.mp hdisj') z
                ⟨hzWA, h (mem_connectedComponentIn hzUA), hzv'v⟩
            · exact h
          have hsub2 : γ '' Set.Ioo cs tstar ⊆ closure v' :=
            (hUscl z hzUA).trans (closure_mono hcomp)
          have hne2 : (Set.Ioo cs tstar ∩ Set.Icc (0:ℝ) 1).Nonempty := by
            have h1 : cs ≤ max cs 0 := le_max_left _ _
            have h2 : (0:ℝ) ≤ max cs 0 := le_max_right _ _
            have h3 : max cs 0 < tstar := max_lt hcst hpos
            refine ⟨(max cs 0 + tstar) / 2, ⟨by linarith, by linarith⟩, ?_⟩
            exact ⟨by linarith, by linarith [htstarIcc.2]⟩
          obtain ⟨t, ht⟩ := hne2
          have htT : t ∈ T := hsub2 ⟨t, ht.1, rfl⟩
          have := hmin t ⟨htT, ht.2⟩
          linarith [ht.1.2]
      rcases hU₀side with h0 | h0
      · exact key u v hu hv huv huvdisj hvne h0 hU₁side
      · exact key v u hv hu (by rwa [Set.union_comm] at huv)
          (by simpa [Set.inter_comm] using huvdisj) hune h0 hU₁side.symm
    · left
      intro z hz
      by_contra hzu
      exact hvne ⟨z, hz, (huv hz).resolve_left hzu⟩
  · right
    intro z hz
    by_contra hzv
    exact hune ⟨z, hz, (huv hz).resolve_right hzv⟩


/-!
## Peeling an arc off an open set of a surface

The main theorem of this file, `arc_nonseparates_surface_clean`, is proved by *peeling* the arc
from its right end `γ 1` down to its left end `γ 0`:

* `Peel.janis_singleton_closed` — Janiszewski's theorem in the plane in the form needed below:
  a compact set and a closed set meeting in a single point do not separate the plane;
* `Peel.planar_slit` — a planar open preconnected set with a *slit with a free end* removed stays
  preconnected;
* `Peel.peel_step` — one step: if `W \ γ '' [s,1]` is preconnected and `γ '' [s',s]` is contained
  in a single chart source, then `W \ γ '' [s',1]` is preconnected; the point is that the "room"
  `V` can be taken to be a *component* of the chart picture, which needs no hypothesis on the
  geometry of the past part of the arc;
* `Peel.preconnected_suffix` — the uniform step (a Lebesgue number for the chart cover of the arc)
  plus a finite induction give `IsPreconnected (W \ γ '' [t,1])` for every `t ∈ [0,1]`.
-/

namespace Peel


theorem janis_singleton_closed
    {A B : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsCompact A) (hB : IsClosed B)
    {p : EuclideanSpace ℝ (Fin 2)} (hAB : A ∩ B = {p})
    {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (h₁ : JoinedIn (Aᶜ) x y) (h₂ : JoinedIn (Bᶜ) x y) :
    JoinedIn ((A ∪ B)ᶜ) x y := by
  classical
  have hp : p ∈ A ∩ B := by rw [hAB]; exact Set.mem_singleton p
  obtain ⟨σ₂, hσ₂⟩ := h₂
  obtain ⟨R₁, hR₁⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mp hA.isBounded
  obtain ⟨R₂, hR₂⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mp
      (isCompact_univ.image σ₂.continuous).isBounded
  set R : ℝ := |R₁| + |R₂| + ‖x‖ + ‖y‖ + 1 with hRdef
  have hxR : ‖x‖ < R := by
    rw [hRdef]
    linarith [abs_nonneg R₁, abs_nonneg R₂, norm_nonneg y]
  have hyR : ‖y‖ < R := by
    rw [hRdef]
    linarith [abs_nonneg R₁, abs_nonneg R₂, norm_nonneg x]
  have hAR : A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    intro z hz
    have h1 : ‖z‖ ≤ R₁ := by
      have := hR₁ hz
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    linarith [h1, le_abs_self R₁, abs_nonneg R₂, norm_nonneg x, norm_nonneg y]
  have hσ₂R : ∀ t, σ₂ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    intro t
    have h1 : ‖σ₂ t‖ ≤ R₂ := by
      have := hR₂ ⟨t, Set.mem_univ t, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    linarith [h1, le_abs_self R₂, abs_nonneg R₁, norm_nonneg x, norm_nonneg y]
  have hpR : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R :=
    Metric.ball_subset_closedBall (hAR hp.1)
  set K : Set (EuclideanSpace ℝ (Fin 2)) := A with hK
  set L : Set (EuclideanSpace ℝ (Fin 2)) :=
    (B ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)
      ∪ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) R with hL
  have hKcpt : IsCompact K := by rw [hK]; exact hA
  have hLcpt : IsCompact L := by
    rw [hL]
    exact ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) R).inter_left hB).union
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) R)
  have hKL : K ∩ L = {p} := by
    rw [hK, hL]
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzA, hzL⟩
      rcases hzL with hzB | hzS
      · exact Set.mem_singleton_iff.mp (hAB ▸ ⟨hzA, hzB.1⟩)
      · exfalso
        rw [Metric.mem_sphere, dist_zero_right] at hzS
        have hb := Metric.mem_ball.mp (hAR hzA)
        rw [dist_zero_right] at hb
        linarith
    · rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hp.1, Or.inl ⟨hp.2, hpR⟩⟩
  have hxKL : x ∉ K ∪ L := by
    rw [Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [hK]; exact fun h => hx (Or.inl h)
    · rw [hL, Set.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · exact fun h => hx (Or.inr h.1)
      · exact fun h => absurd h (by
          rw [Metric.mem_sphere, dist_zero_right]; exact ne_of_lt hxR)
  have hyKL : y ∉ K ∪ L := by
    rw [Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [hK]; exact fun h => hy (Or.inl h)
    · rw [hL, Set.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · exact fun h => hy (Or.inr h.1)
      · exact fun h => absurd h (by
          rw [Metric.mem_sphere, dist_zero_right]; exact ne_of_lt hyR)
  have h₁' : JoinedIn (Kᶜ) x y := by rw [hK]; exact h₁
  have h₂' : JoinedIn (Lᶜ) x y := by
    refine ⟨σ₂, fun t => ?_⟩
    rw [Set.mem_compl_iff, hL, Set.mem_union, not_or]
    refine ⟨fun h => hσ₂ t h.1, ?_⟩
    exact fun h => absurd h (by
      rw [Metric.mem_sphere, dist_zero_right]
      exact ne_of_lt (by simpa using Metric.mem_ball.mp (hσ₂R t)))
  obtain ⟨σ, hσ⟩ := Grid.janis_singleton_plane hKcpt hLcpt hKL hxKL hyKL h₁' h₂'
  have hrange_sub : Set.range σ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
      ∪ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ := by
    rintro _ ⟨t, rfl⟩
    by_cases hz : σ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R
    · by_cases hz2 : σ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
      · exact Or.inl hz2
      · exfalso
        have hsphere : σ t ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) R := by
          rw [Metric.mem_sphere, dist_zero_right]
          rw [Metric.mem_closedBall, dist_zero_right] at hz
          rw [Metric.mem_ball, dist_zero_right] at hz2
          exact le_antisymm hz (le_of_not_gt hz2)
        exact hσ t (Or.inr (by rw [hL]; exact Or.inr hsphere))
    · exact Or.inr hz
  have hdisj : Set.range σ ∩ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
      ∩ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, h1, h2⟩
    exact h2 (Metric.ball_subset_closedBall h1)
  have hpre : IsPreconnected (Set.range σ) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image σ σ.continuous.continuousOn
  have hσball : ∀ t, σ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hpre)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)
      ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R))ᶜ
      Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl hrange_sub hdisj with h | h
    · exact fun t => h ⟨t, rfl⟩
    · exfalso
      have hxball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
        rw [Metric.mem_ball, dist_zero_right]; exact hxR
      have hthis : σ 0 ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ :=
        h ⟨0, rfl⟩
      rw [Set.mem_compl_iff, σ.source] at hthis
      exact hthis (Metric.ball_subset_closedBall hxball)
  have hσB : ∀ t, σ t ∉ B := by
    intro t htB
    refine hσ t (Or.inr ?_)
    rw [hL]
    exact Or.inl ⟨htB, Metric.ball_subset_closedBall (hσball t)⟩
  refine ⟨σ, fun t => ?_⟩
  rw [Set.mem_compl_iff, Set.mem_union, not_or]
  exact ⟨fun hA' => hσ t (Or.inl (by rw [hK]; exact hA')), hσB t⟩

/-- **A slit with a free end does not separate.**

Let `Ω ⊆ ℝ²` be open and preconnected, let `h : ℝ → ℝ²` be continuous and injective on `[0,c]`,
suppose `h '' [0,c'] ⊆ Ω` for every `c' < c` and `h c ∉ Ω`.  Then `Ω` with the half-open slit
`h '' [0,c)` removed is preconnected. -/
theorem planar_slit {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    (hΩo : IsOpen Ω) (hΩpre : IsPreconnected Ω)
    {h : ℝ → EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn h (Set.Icc 0 c)) (hinj : Set.InjOn h (Set.Icc 0 c))
    (hsub : ∀ c' < c, h '' Set.Icc 0 c' ⊆ Ω) (hout : h c ∉ Ω) :
    IsPreconnected (Ω \ h '' Set.Ico (0:ℝ) c) := by
  have hIcc : h '' Set.Icc (0:ℝ) c = h '' Set.Ico (0:ℝ) c ∪ {h c} := by
    have h1 : Set.Icc (0:ℝ) c = Set.Ico (0:ℝ) c ∪ {c} := by
      ext t
      simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_or_eq_of_le h2 with h2' | h2'
        · exact Or.inl ⟨h1, h2'⟩
        · exact Or.inr h2'
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, h2.le⟩
        · exact ⟨hc.le, le_rfl⟩
    calc h '' Set.Icc (0:ℝ) c = h '' (Set.Ico (0:ℝ) c ∪ {c}) := by rw [h1]
      _ = h '' Set.Ico (0:ℝ) c ∪ h '' {c} := by rw [Set.image_union]
      _ = h '' Set.Ico (0:ℝ) c ∪ {h c} := by rw [Set.image_singleton]
  have hEq : Ω \ h '' Set.Icc (0:ℝ) c = Ω \ h '' Set.Ico (0:ℝ) c := by
    rw [hIcc]
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h1 => hz' (Or.inl h1)⟩
    · rintro ⟨hz, h1⟩
      exact ⟨hz, fun h => h.elim h1 (fun h2 => hout (h2 ▸ hz))⟩
  rw [← hEq]
  by_cases hne : (Ω \ h '' Set.Icc (0:ℝ) c).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have hpc : IsPathConnected (Ω \ h '' Set.Icc (0:ℝ) c) := by
      have hAeq : h '' Set.Icc (0:ℝ) c ∩ Ωᶜ = {h c} := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro z ⟨hzA, hzB⟩
          obtain ⟨t, ht, rfl⟩ := hzA
          have ht_eq : t = c := by
            rcases lt_or_eq_of_le ht.2 with h' | h'
            · exact absurd (hsub t h' ⟨t, ⟨ht.1, le_refl t⟩, rfl⟩) hzB
            · exact h'
          rw [ht_eq]
          exact Set.mem_singleton_iff.mpr rfl
        · rintro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨⟨c, ⟨hc.le, le_rfl⟩, rfl⟩, hout⟩
      refine ⟨w, hw, fun y hy => ?_⟩
      have hyΩ : y ∈ Ω := hy.1
      have hyA : y ∉ h '' Set.Icc (0:ℝ) c := hy.2
      have hwΩ : w ∈ Ω := hw.1
      have hwA : w ∉ h '' Set.Icc (0:ℝ) c := hw.2
      have h₁ : JoinedIn ((h '' Set.Icc (0:ℝ) c)ᶜ) w y :=
        (plane_arc_nonseparation isCompact_Icc hcont hinj).joinedIn w
          (by simpa using hwA) y (by simpa using hyA)
      have hΩpc : IsPathConnected Ω :=
        hΩo.isConnected_iff_isPathConnected.mp ⟨⟨w, hwΩ⟩, hΩpre⟩
      have h₂ : JoinedIn ((Ωᶜ : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) w y := by
        rw [compl_compl]
        exact hΩpc.joinedIn w hwΩ y hyΩ
      have hmain := janis_singleton_closed
        (isCompact_Icc.image_of_continuousOn hcont) hΩo.isClosed_compl hAeq
        (fun h => h.elim hwA (fun h' => h' hwΩ))
        (fun h => h.elim hyA (fun h' => h' hyΩ)) h₁ h₂
      have hEq2 : ((h '' Set.Icc (0:ℝ) c ∪ Ωᶜ)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))
          = Ω \ h '' Set.Icc (0:ℝ) c := by
        rw [Set.compl_union, compl_compl, Set.sdiff_eq, Set.inter_comm]
      rwa [hEq2] at hmain
    exact hpc.isConnected.2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact isPreconnected_empty

/-- For a partial homeomorphism, `e.symm '' (s ∩ e '' a) = (e.symm '' s) ∩ a`. -/
theorem symm_image_inter_of_subset {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : OpenPartialHomeomorph α β) {s : Set β} (hs : s ⊆ e.target) {a : Set α}
    (ha : a ⊆ e.source) : e.symm '' (s ∩ e '' a) = (e.symm '' s) ∩ a := by
  apply subset_antisymm
  · rintro z ⟨w, ⟨hw, hwe⟩, hwz⟩
    constructor
    · exact ⟨w, hw, hwz⟩
    · obtain ⟨a', ha', haw⟩ := hwe
      rw [← hwz, ← haw, e.left_inv (ha ha')]
      exact ha'
  · rintro z ⟨hz, hza⟩
    obtain ⟨w, hw, hwz⟩ := hz
    exact Exists.intro w (And.intro (And.intro hw
      (Exists.intro z (And.intro hza (by rw [← hwz]; exact e.right_inv (hs hw))))) hwz)

/-- For a partial homeomorphism, `e.symm '' (s \ e '' a) = (e.symm '' s) \ a`. -/
theorem symm_image_sdiff_of_subset {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : OpenPartialHomeomorph α β) {s : Set β} (hs : s ⊆ e.target) {a : Set α}
    (ha : a ⊆ e.source) : e.symm '' (s \ e '' a) = (e.symm '' s) \ a := by
  apply subset_antisymm
  · rintro z ⟨w, ⟨hw, hwe⟩, hwz⟩
    constructor
    · exact ⟨w, hw, hwz⟩
    · intro hza
      refine hwe (Exists.intro z (And.intro hza ?_))
      rw [← hwz]
      exact e.right_inv (hs hw)
  · rintro z ⟨hz, hza⟩
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨w, ⟨hw, ?_⟩, hwz⟩
    rintro ⟨a', ha', haw⟩
    refine hza ?_
    rw [← hwz, ← haw, e.left_inv (ha ha')]
    exact ha'

/-- The set `[0,c)` is preconnected (for `0 < c`). -/
theorem isPreconnected_Ico'' {c : ℝ} (hc : 0 < c) : IsPreconnected (Set.Ico (0:ℝ) c) := by
  have h1 : IsPreconnected (Set.Ioo (0:ℝ) c) := isPreconnected_Ioo
  refine h1.subset_closure ?_ ?_
  · intro x hx; exact ⟨le_of_lt hx.1, hx.2⟩
  · intro x hx
    rw [closure_Ioo (ne_of_lt hc)]
    exact ⟨hx.1, le_of_lt hx.2⟩

/-- **One peeling step.**

If `W \ γ '' [s,1]` is preconnected and the arc piece `γ '' [s',s]` is contained in the source of
a single chart, then `W \ γ '' [s',1]` is preconnected.

Proof: the room criterion (`isPreconnected_sdiff_of_isClosedIn_of_room`) applied to
`T := W \ γ '' [s,1]` and the slit `C := γ '' (s',s)`; the room `V` is the component of `γ s'` in
the chart picture of `T`, and the planar slit lemma shows that `V \ C` is preconnected.  Note that
`γ s' ∈ T` (its free end lies in `T`) while `γ s ∉ T` (the slit ends on the removed arc). -/
theorem peel_step {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {W : Set M} (hW : IsOpen W) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hWγ : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W)
    {s' s : ℝ} (hs'0 : 0 ≤ s') (hs's : s' < s) (hs1 : s ≤ 1)
    (he : ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)),
        γ '' Set.Icc s' s ⊆ e.source)
    (hT : IsPreconnected (W \ γ '' Set.Icc s 1)) :
    IsPreconnected (W \ γ '' Set.Icc s' 1) := by
  classical
  obtain ⟨e, hesub⟩ := he
  have hs'I : s' ∈ Set.Icc (0:ℝ) 1 := ⟨hs'0, le_trans hs's.le hs1⟩
  have hsI : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hs'0 hs's.le, hs1⟩
  have hIcc_split : γ '' Set.Icc s' 1 = γ '' Set.Ico s' s ∪ γ '' Set.Icc s 1 := by
    rw [← Set.image_union, Set.Ico_union_Icc_eq_Icc hs's.le hs1]
  -- the region `T = W \ γ '' [s,1]`
  set T : Set M := W \ γ '' Set.Icc s 1 with hTdef
  have hTopen : IsOpen T := hW.sdiff (isCompact_Icc.image hγ).isClosed
  have hγs'T : γ s' ∈ T := by
    refine ⟨hWγ s' hs'I, ?_⟩
    rintro ⟨u, hu, hue⟩
    have hu1 : u ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans (le_trans hs'0 hs's.le) hu.1, hu.2⟩
    have hus : u = s' := hinj hu1 hs'I hue
    rw [hus] at hu
    exact absurd hu.1 (not_le.mpr hs's)
  have hγs'e : γ s' ∈ e.source := hesub ⟨s', ⟨le_refl s', hs's.le⟩, rfl⟩
  -- the piece to be removed
  have hCsub : γ '' Set.Ico s' s ⊆ T ∩ e.source := by
    rintro z ⟨u, hu, rfl⟩
    have hu1 : u ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hs'0 hu.1, le_trans hu.2.le hs1⟩
    refine ⟨⟨hWγ u hu1, ?_⟩, hesub ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩⟩
    rintro ⟨v, hv, hvu⟩
    have hv1 : v ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hs'0 (le_trans hs's.le hv.1), hv.2⟩
    have huv : v = u := hinj hv1 hu1 hvu
    rw [huv] at hv
    exact absurd hv.1 (not_le.mpr hu.2)
  -- the chart picture
  set Ω : Set (EuclideanSpace ℝ (Fin 2)) := e '' (T ∩ e.source) with hΩdef
  have hΩopen : IsOpen Ω :=
    e.isOpen_image_of_subset_source (hTopen.inter e.open_source) Set.inter_subset_right
  have hγs'Ω : e (γ s') ∈ Ω := ⟨γ s', ⟨hγs'T, hγs'e⟩, rfl⟩
  set Ωp : Set (EuclideanSpace ℝ (Fin 2)) := connectedComponentIn Ω (e (γ s')) with hΩpdef
  have hΩpopen : IsOpen Ωp := hΩopen.connectedComponentIn
  have hΩppre : IsPreconnected Ωp := isPreconnected_connectedComponentIn
  have hΩpsub : Ωp ⊆ Ω := connectedComponentIn_subset Ω (e (γ s'))
  have hΩptgt : Ωp ⊆ e.target := by
    rintro z hz
    obtain ⟨w, hw, rfl⟩ := hΩpsub hz
    exact e.map_source hw.2
  -- the slit lies in the component
  have hCΩpIco : e '' (γ '' Set.Ico s' s) ⊆ Ωp := by
    refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
    · rw [Set.image_image]
      exact (Set.ordConnected_Ico (a := s') (b := s)).isPreconnected.image (fun u => e (γ u))
        (e.continuousOn.comp hγ.continuousOn
          (fun u hu => hesub ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩))
    · exact ⟨γ s', ⟨s', ⟨le_refl s', hs's⟩, rfl⟩, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨w, hCsub hw, rfl⟩
  -- the planar slit lemma
  set hh : ℝ → EuclideanSpace ℝ (Fin 2) := fun u => e (γ (s' + u)) with hhdef
  have hmaps' : ∀ u ∈ Set.Icc (0:ℝ) (s - s'), s' + u ∈ Set.Icc s' s :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hmaps : ∀ u ∈ Set.Icc (0:ℝ) (s - s'), γ (s' + u) ∈ e.source :=
    fun u hu => hesub ⟨s' + u, hmaps' u hu, rfl⟩
  have hhcont : ContinuousOn hh (Set.Icc 0 (s - s')) :=
    e.continuousOn.comp ((hγ.comp (continuous_const.add continuous_id)).continuousOn) hmaps
  have hhinj : Set.InjOn hh (Set.Icc 0 (s - s')) := by
    intro u hu v hv huv
    have huI : s' + u ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2, hs1]⟩
    have hvI : s' + v ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hv.1], by linarith [hv.2, hs1]⟩
    have h1 : γ (s' + u) = γ (s' + v) := e.injOn (hmaps u hu) (hmaps v hv) huv
    have h2 : s' + u = s' + v := hinj huI hvI h1
    linarith
  have hhsub : ∀ c' < s - s', hh '' Set.Icc 0 c' ⊆ Ωp := by
    intro c' hc'
    rintro z ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · rw [← h0]
      simp only [hhdef, add_zero]
      exact mem_connectedComponentIn hγs'Ω
    · refine hCΩpIco ⟨γ (s' + u), ⟨s' + u, ⟨by linarith, by linarith [hu.2, hc']⟩, rfl⟩, ?_⟩
      simp only [hhdef]
  have hγsT : γ s ∉ T := fun h => h.2 ⟨s, ⟨le_refl s, hs1⟩, rfl⟩
  have hhval : hh (s - s') = e (γ s) := by
    have harg : s' + (s - s') = s := by ring
    simp only [hhdef, harg]
  have hhout : hh (s - s') ∉ Ωp := by
    rw [hhval]
    intro hmem
    obtain ⟨w, hw, hwe⟩ := hΩpsub hmem
    have hws : w = γ s := e.injOn hw.2 (hesub ⟨s, ⟨hs's.le, le_refl s⟩, rfl⟩) hwe
    rw [hws] at hw
    exact hγsT hw.1
  have hhimage : hh '' Set.Ico (0:ℝ) (s - s') = e '' (γ '' Set.Ico s' s) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨γ (s' + u), ⟨s' + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u - s', ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      have harg : s' + (u - s') = u := by ring
      simp only [hhdef, harg]
  have hslit : IsPreconnected (Ωp \ e '' (γ '' Set.Ico s' s)) := by
    rw [← hhimage]
    exact planar_slit hΩpopen hΩppre (by linarith) hhcont hhinj hhsub hhout
  -- back to `M`
  set V : Set M := e.symm '' Ωp with hVdef
  have hVopen : IsOpen V := e.isOpen_image_symm_of_subset_target hΩpopen hΩptgt
  have hVsubT : V ⊆ T := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hww'⟩ := hΩpsub hw
    have h1 : e.symm w = w' := by rw [← hww', e.left_inv hw'.2]
    rw [h1]
    exact hw'.1
  have hCV : γ '' Set.Ico s' s ⊆ V := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨e (γ u), hCΩpIco ⟨γ u, ⟨u, hu, rfl⟩, rfl⟩,
      e.left_inv (hCsub ⟨u, hu, rfl⟩).2⟩
  have hVp : IsPreconnected (V \ γ '' Set.Ico s' s) := by
    have hEq : V \ γ '' Set.Ico s' s = e.symm '' (Ωp \ e '' (γ '' Set.Ico s' s)) := by
      rw [hVdef, symm_image_sdiff_of_subset e hΩptgt (fun z hz => (hCsub hz).2)]
    rw [hEq]
    exact hslit.image e.symm (e.continuousOn_symm.mono (fun z hz => hΩptgt hz.1))
  -- the room criterion
  have hTCeq : T \ γ '' Set.Ico s' s = W \ γ '' Set.Icc s' 1 := by
    rw [hTdef, hIcc_split]
    ext z
    constructor
    · rintro ⟨⟨hzW, hzA⟩, hzC⟩
      exact ⟨hzW, fun h => h.elim hzC hzA⟩
    · rintro ⟨hzW, hzA⟩
      exact ⟨⟨hzW, fun h => hzA (Or.inr h)⟩, fun h => hzA (Or.inl h)⟩
  have hTC : IsOpen (T \ γ '' Set.Ico s' s) := by
    rw [hTCeq]
    exact hW.sdiff (isCompact_Icc.image hγ).isClosed
  have hres : IsPreconnected (T \ γ '' Set.Ico s' s) :=
    isPreconnected_sdiff_of_isClosedIn_of_room hT hTC hVopen hCV hVsubT hVp
  rwa [hTCeq] at hres

/-- **Peeling the arc from its right end.**  For every `t ∈ [0,1]`, removing the arc piece
`γ '' [t,1]` from `W` leaves a preconnected set.  A Lebesgue number for the cover of the arc by
chart sources makes the step size of `peel_step` uniform, and then a finite induction starting
from `t = 1` (removing the single point `γ 1`) finishes. -/
theorem preconnected_suffix {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {W : Set M} (hW : IsOpen W)
    (hWc : IsPathConnected W) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hWγ : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    IsPreconnected (W \ γ '' Set.Icc t 1) := by
  classical
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := 2)
  obtain ⟨ε, hεpos, hchart⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      v - u ≤ ε → ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)),
        γ '' Set.Icc u v ⊆ e.source := by
    have hUopen : ∀ i : ℝ, IsOpen {s : ℝ | γ s ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) (γ i)).source} := fun i =>
      (chartAt (EuclideanSpace ℝ (Fin 2)) (γ i)).open_source.preimage hγ
    have hcover : Set.Icc (0:ℝ) 1 ⊆ ⋃ i : ℝ, {s : ℝ | γ s ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) (γ i)).source} :=
      fun s _ => Set.mem_iUnion.mpr ⟨s, mem_chart_source (EuclideanSpace ℝ (Fin 2)) (γ s)⟩
    obtain ⟨V₀, hV₀unif, hV₀⟩ := lebesgue_number_lemma isCompact_Icc hUopen hcover
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.uniformity_basis_dist.mem_iff.mp hV₀unif
    refine ⟨δ / 2, by linarith, ?_⟩
    intro u v hu huv hv1 huvε
    have hvK : v ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hu huv, hv1⟩
    obtain ⟨i, hi⟩ := hV₀ v hvK
    refine ⟨chartAt (EuclideanSpace ℝ (Fin 2)) (γ i), ?_⟩
    have hsub : Set.Icc u v ⊆ {s : ℝ | γ s ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) (γ i)).source} := by
      intro s hs
      have h1 : dist v s < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.1, hs.2, huvε, hδpos]
      exact hi (show s ∈ UniformSpace.ball v V₀ from hδsub h1)
    rintro z ⟨s, hs, rfl⟩
    exact hsub hs
  set S : Set ℝ := {s : ℝ | s ∈ Set.Icc (0:ℝ) 1 ∧ IsPreconnected (W \ γ '' Set.Icc s 1)}
    with hSdef
  have hbase : (1:ℝ) ∈ S := by
    refine ⟨⟨zero_le_one, le_refl 1⟩, ?_⟩
    have hset : γ '' Set.Icc (1:ℝ) 1 = {γ 1} := by rw [Set.Icc_self, Set.image_singleton]
    rw [hset]
    obtain ⟨V, hVo, h1V, hVW, hVp⟩ : ∃ V : Set M, IsOpen V ∧ γ 1 ∈ V ∧ V ⊆ W ∧
        IsPreconnected (V \ {γ 1}) := by
      let c := chartAt (EuclideanSpace ℝ (Fin 2)) (γ 1)
      have hc1 : γ 1 ∈ c.source := mem_chart_source _ (γ 1)
      have hγ1W : γ 1 ∈ W := hWγ 1 ⟨zero_le_one, le_refl 1⟩
      have hUopen : IsOpen (W ∩ c.source) := hW.inter c.open_source
      have hcU : c '' (W ∩ c.source) ⊆ c.target :=
        fun z ⟨w, hw, hwe⟩ => hwe ▸ c.map_source hw.2
      have hc1U : c (γ 1) ∈ c '' (W ∩ c.source) := ⟨γ 1, ⟨hγ1W, hc1⟩, rfl⟩
      obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp
        ((c.isOpen_image_of_subset_source hUopen Set.inter_subset_right).mem_nhds hc1U)
      have hballtgt : Metric.ball (c (γ 1)) ρ ⊆ c.target := fun z hz => hcU (hρsub hz)
      refine ⟨c.symm '' Metric.ball (c (γ 1)) ρ, ?_, ?_, ?_, ?_⟩
      · exact c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtgt
      · exact ⟨c (γ 1), Metric.mem_ball_self hρpos, c.left_inv hc1⟩
      · rintro z ⟨w, hw, rfl⟩
        obtain ⟨x, hx, hxw⟩ := hρsub hw
        have h1 : c.symm w = x := by rw [← hxw, c.left_inv hx.2]
        rw [h1]
        exact hx.1
      · have heq := symm_image_sdiff_of_subset c (s := Metric.ball (c (γ 1)) ρ) hballtgt
          (a := ({γ 1} : Set M))
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hc1)
        rw [Set.image_singleton] at heq
        rw [← heq]
        exact (isPreconnected_ball_diff_singleton (one_lt_rank_euclidean (by norm_num))
          (c (γ 1))).image c.symm (c.continuousOn_symm.mono (fun z hz => hballtgt hz.1))
    exact isPreconnected_diff_singleton hWc.isConnected.isPreconnected hW isClosed_singleton
      hVo h1V hVW hVp
  have hstep : ∀ s ∈ S, Set.Icc (max 0 (s - ε)) s ⊆ S := by
    intro s hs
    obtain ⟨hsI, hsP⟩ := hs
    intro s' hs'
    refine ⟨⟨le_trans (le_max_left (0:ℝ) (s - ε)) hs'.1, le_trans hs'.2 hsI.2⟩, ?_⟩
    rcases eq_or_lt_of_le hs'.2 with h | h
    · rwa [h]
    · exact peel_step hW hγ hinj hWγ (le_trans (le_max_left (0:ℝ) (s - ε)) hs'.1) h hsI.2
        (hchart s' s (le_trans (le_max_left (0:ℝ) (s - ε)) hs'.1) h.le hsI.2
          (by linarith [hs'.1, le_max_right (0:ℝ) (s - ε)])) hsP
  have hind : ∀ k : ℕ, Set.Icc (max 0 (1 - (k:ℝ) * ε)) 1 ⊆ S := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have h0 : max 0 (1 - ((0:ℕ):ℝ) * ε) = 1 := by norm_num
      rw [h0, Set.Icc_self] at hx
      rw [hx]
      exact hbase
    | succ k ih =>
      intro x hx
      have hx0 : 0 ≤ x := le_trans (le_max_left (0:ℝ) (1 - ((k + 1 : ℕ) : ℝ) * ε)) hx.1
      have hxlow : 1 - ((k:ℝ) + 1) * ε ≤ x := by
        have h := le_trans (le_max_right (0:ℝ) (1 - ((k + 1 : ℕ) : ℝ) * ε)) hx.1
        push_cast at h
        linarith
      set u : ℝ := min 1 (x + ε) with hudef
      have hu1 : u ≤ 1 := by rw [hudef]; exact min_le_left _ _
      have hu2 : u ≤ x + ε := by rw [hudef]; exact min_le_right _ _
      have hux : x ≤ u := by rw [hudef]; exact le_min hx.2 (by linarith)
      have hu_ge : 0 ≤ u := by rw [hudef]; exact le_min (by norm_num) (by linarith)
      have hkeps : 0 ≤ (k:ℝ) * ε := mul_nonneg (Nat.cast_nonneg k) hεpos.le
      have huk : 1 - (k:ℝ) * ε ≤ u := by
        rw [hudef]; exact le_min (by linarith) (by linarith)
      have huS : u ∈ Set.Icc (max 0 (1 - (k:ℝ) * ε)) 1 := ⟨max_le hu_ge huk, hu1⟩
      have hxu : x ∈ Set.Icc (max 0 (u - ε)) u := ⟨max_le hx0 (by linarith), hux⟩
      exact hstep u (ih huS) hxu
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hkε : 1 ≤ (k:ℝ) * ε := by
    rw [div_lt_iff₀ hεpos] at hk
    linarith
  exact (hind k ⟨max_le ht.1 (by linarith [ht.1, hkε]), ht.2⟩).2

end Peel

/-- **An arc does not separate a surface.**  If `W` is an open path connected set in a topological
`2`-manifold and a compact arc (the image of an injective continuous map on `[0,1]`) lies in `W`,
then removing the arc from `W` leaves a preconnected set. -/
theorem arc_nonseparates_surface_clean {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {W : Set M} (hW : IsOpen W)
    (hWc : IsPathConnected W) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0 : ℝ) 1))
    (hWγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ W) :
    IsPreconnected (W \ γ '' Set.Icc (0 : ℝ) 1) :=
  Peel.preconnected_suffix hW hWc hγ hinj hWγ ⟨le_refl 0, zero_le_one⟩

/-- **The complement of a compact arc in an open path connected set of a surface is path
connected.**  The preconnectedness is `arc_nonseparates_surface_clean`; openness, local path
connectedness (charted spaces are locally path connected) and nonemptiness (an arc has empty
interior, `arc_interior_empty_surface`) upgrade it to path connectedness. -/
theorem isPathConnected_sdiff_arc_surface_clean {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] {W : Set M} (hW : IsOpen W)
    (hWc : IsPathConnected W) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0 : ℝ) 1))
    (hWγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ W) :
    IsPathConnected (W \ γ '' Set.Icc (0 : ℝ) 1) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := 2)
  have hne : (W \ γ '' Set.Icc (0:ℝ) 1).Nonempty := by
    obtain ⟨w, hw⟩ := hWc.nonempty
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : W ⊆ γ '' Set.Icc (0:ℝ) 1 := by
      intro x hx
      by_contra hxA
      have hx' : x ∈ W \ γ '' Set.Icc (0:ℝ) 1 := ⟨hx, hxA⟩
      rw [hcon] at hx'
      exact hx'
    have h1 : w ∈ interior W := by rw [hW.interior_eq]; exact hw
    have h2 : w ∈ interior (γ '' Set.Icc (0:ℝ) 1) := interior_mono hsub h1
    rw [arc_interior_empty_surface hγ hinj] at h2
    exact h2
  have hopen : IsOpen (W \ γ '' Set.Icc (0:ℝ) 1) :=
    hW.sdiff (isCompact_Icc.image hγ).isClosed
  exact hopen.isConnected_iff_isPathConnected.mp
    ⟨hne, arc_nonseparates_surface_clean hW hWc hγ hinj hWγ⟩

end

end Work.Whitney.PathTools
