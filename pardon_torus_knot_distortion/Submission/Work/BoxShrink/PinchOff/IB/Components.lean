import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.BoxShrink.PinchOff.IB.Pieces

/-!
# The components of the preimage of a union of inessential simple curves

The preimage `Ct` in the parameter plane of a finite union of pairwise disjoint *simple*
*inessential* closed curves of a parametrised torus is a locally finite disjoint union of compact
connected pieces (`Pieces.lean`).  Consequently each connected component of `Ct` is one of the
pieces, and is therefore compact.

The proof that the pieces *are* the components: only finitely many pieces meet a given bounded
set (because the pieces are translates of finitely many compact sets by the discrete lattice);
hence each piece is *open* in `Ct` (a ball around a point of a piece, small enough not to reach the
finitely many other pieces meeting the unit ball, meets `Ct` only in that piece).  Together with
closedness (compactness) this makes the pieces clopen in `Ct`, and a preconnected set covered by
two disjoint open sets lies in one of them.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- A finite set of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_finite {S : Set ℝ} (hS : S.Finite) (hpos : ∀ r ∈ S, 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ S, δ ≤ r := by
  classical
  rcases Set.eq_empty_or_nonempty S with h | hne
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨r₀, hr₀⟩ := hne
    have hne' : hS.toFinset.Nonempty := ⟨r₀, by simpa [Set.Finite.mem_toFinset] using hr₀⟩
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image hS.toFinset (fun x => x) hne'
    refine ⟨a, hpos a (by simpa [Set.Finite.mem_toFinset] using ha), fun r hr => ?_⟩
    exact hmin r (by simpa [Set.Finite.mem_toFinset] using hr)

/-- **Every connected component of the preimage of a union of inessential simple curves of a
parametrised torus is compact.** -/
theorem components_compact {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) :
    ∀ z ∈ Xtilde P (⋃ i, Set.range (γ i).γ),
      IsCompact (connectedComponentIn (Xtilde P (⋃ i, Set.range (γ i).γ)) z) := by
  classical
  set L : ∀ i, Work.CoreTopology.LiftOf P (γ i) := fun i => chosenLift P (γ i) with hLdef
  have hLw : ∀ i, (L i).winding = 0 := fun i => chosenLift_winding (hess i)
  set Ct : Set ℂ := Xtilde P (⋃ i, Set.range (γ i).γ) with hCtdef
  have hCteq : Ct = ⋃ i, ⋃ ν ∈ periodLattice, translate ν (curveSet (L i)) :=
    Xtilde_iUnion_eq L hLw
  have hpiece_sub : ∀ (i : Fin n) (ν : ℂ), ν ∈ periodLattice →
      translate ν (curveSet (L i)) ⊆ Ct := by
    intro i ν hν w hw
    rw [hCteq]
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨ν, Set.mem_iUnion.mpr ⟨hν, hw⟩⟩⟩
  have hpiece_closed : ∀ (i : Fin n) (ν : ℂ), IsClosed (translate ν (curveSet (L i))) :=
    fun i ν => (translate_compact ν (curveSet_compact (L i))).isClosed
  -- Step 1: only finitely many pieces meet a given closed ball.
  have hfinite : ∀ z : ℂ, {q : Fin n × ℂ | q.2 ∈ periodLattice ∧
      ((translate q.2 (curveSet (L q.1))) ∩ Metric.closedBall z 1).Nonempty}.Finite := by
    intro z
    have hsingle : ∀ i : Fin n,
        {ν : ℂ | ν ∈ periodLattice ∧
          ((translate ν (curveSet (L i))) ∩ Metric.closedBall z 1).Nonempty}.Finite := by
      intro i
      obtain ⟨M, hM⟩ := (curveSet_compact (L i)).isBounded.subset_closedBall (0 : ℂ)
      refine Set.Finite.subset (finite_periodLattice_ball (‖z‖ + 1 + M)) ?_
      rintro ν ⟨hν, w, hw1, hw2⟩
      refine ⟨hν, ?_⟩
      rw [mem_translate] at hw1
      obtain ⟨t, htmem, ht⟩ := hw1
      have hMle : ‖liftMap (L i) t‖ ≤ M := by
        have h1 := hM ⟨t, htmem, rfl⟩
        rwa [Metric.mem_closedBall, dist_zero_right] at h1
      have hd : dist w z ≤ 1 := Metric.mem_closedBall.mp hw2
      have hνeq : ν = w - liftMap (L i) t := by rw [ht]; ring
      have h6 : ‖ν‖ = dist w (liftMap (L i) t) := by
        rw [dist_eq_norm, hνeq]
      have h8 : dist w (liftMap (L i) t) ≤ 1 + (‖z‖ + M) := by
        calc dist w (liftMap (L i) t) ≤ dist w z + dist z (liftMap (L i) t) :=
              dist_triangle _ _ _
          _ ≤ 1 + (‖z‖ + M) := by
              have h7 : dist z (liftMap (L i) t) ≤ ‖z‖ + M := by
                rw [dist_eq_norm]
                exact le_trans (norm_sub_le _ _) (by linarith)
              linarith
      have h5 : ‖ν‖ ≤ ‖z‖ + 1 + M := by
        rw [h6]
        linarith
      linarith
    have hcover : {q : Fin n × ℂ | q.2 ∈ periodLattice ∧
        ((translate q.2 (curveSet (L q.1))) ∩ Metric.closedBall z 1).Nonempty} ⊆
        ⋃ i, (fun ν => (i, ν)) '' {ν : ℂ | ν ∈ periodLattice ∧
          ((translate ν (curveSet (L i))) ∩ Metric.closedBall z 1).Nonempty} := by
      rintro ⟨i, ν⟩ ⟨hν, hne⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨ν, ⟨hν, hne⟩, rfl⟩⟩
    exact Set.Finite.subset (Set.finite_iUnion (fun i => (hsingle i).image _)) hcover
  -- Step 2: each piece is open in `Ct`.
  have hopen : ∀ (i : Fin n) (ν : ℂ) (z : ℂ), ν ∈ periodLattice →
      z ∈ translate ν (curveSet (L i)) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ Ct, dist w z < ε → w ∈ translate ν (curveSet (L i)) := by
    intro i ν z hν hz
    set Q : Set (Fin n × ℂ) := {q | q.2 ∈ periodLattice ∧
      ((translate q.2 (curveSet (L q.1))) ∩ Metric.closedBall z 1).Nonempty ∧
      z ∉ translate q.2 (curveSet (L q.1))} with hQdef
    have hQfin : Q.Finite := (hfinite z).subset (fun q hq => ⟨hq.1, hq.2.1⟩)
    have hQpos : ∀ q ∈ Q, ∃ ε : ℝ, 0 < ε ∧
        ∀ y ∈ translate q.2 (curveSet (L q.1)), ε ≤ dist z y := by
      intro q hq
      have hznot : z ∉ translate q.2 (curveSet (L q.1)) := hq.2.2
      have hcl : z ∉ closure (translate q.2 (curveSet (L q.1))) := by
        rw [(hpiece_closed q.1 q.2).closure_eq]
        exact hznot
      have h1 : ¬ (∀ ε > 0, ∃ y ∈ translate q.2 (curveSet (L q.1)), dist z y < ε) := by
        intro h
        exact hcl (Metric.mem_closure_iff.mpr h)
      push_neg at h1
      exact h1
    set S : Set ℝ := (fun q => if hq : q ∈ Q then Classical.choose (hQpos q hq) else 1) '' Q
      with hSdef
    have hSfin : S.Finite := hQfin.image _
    have hSpos : ∀ r ∈ S, 0 < r := by
      rintro r ⟨q, hq, rfl⟩
      simp only [dif_pos hq]
      exact (Classical.choose_spec (hQpos q hq)).1
    obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_of_finite hSfin hSpos
    have hδdist : ∀ q ∈ Q, ∀ y ∈ translate q.2 (curveSet (L q.1)), δ ≤ dist z y := by
      intro q hq y hy
      have h1 : δ ≤ (if hq : q ∈ Q then Classical.choose (hQpos q hq) else 1) :=
        hδle _ ⟨q, hq, rfl⟩
      simp only [dif_pos hq] at h1
      have h2 := (Classical.choose_spec (hQpos q hq)).2 y hy
      linarith
    refine ⟨min 1 δ, lt_min one_pos hδpos, ?_⟩
    intro w hw hdist
    obtain ⟨j, μ, hμ, hwpiece⟩ := exists_piece_of_mem L hLw hw
    by_cases hsame : (j, μ) = (i, ν)
    · have hj : j = i := congrArg Prod.fst hsame
      have hμν : μ = ν := congrArg Prod.snd hsame
      rw [hj, hμν] at hwpiece
      exact hwpiece
    · exfalso
      have hne' : (i, ν) ≠ (j, μ) := fun h => hsame h.symm
      have hznot : z ∉ translate μ (curveSet (L j)) := by
        intro hzpiece
        exact (Set.disjoint_left.mp
          (translate_curveSet_disjoint hsimple hdisj L hLw hν hμ hne') hz) hzpiece
      have hQmem : (j, μ) ∈ Q := by
        refine ⟨hμ, ⟨⟨w, hwpiece, ?_⟩, hznot⟩⟩
        rw [Metric.mem_closedBall]
        linarith [hdist, min_le_left (1 : ℝ) δ]
      have hδle' : δ ≤ dist z w := hδdist (j, μ) hQmem w hwpiece
      have h2 : dist w z < δ := lt_of_lt_of_le hdist (min_le_right (1 : ℝ) δ)
      rw [dist_comm] at h2
      linarith
  -- Step 3: a preconnected subset of `Ct` meeting a piece lies in it.
  have hpre : ∀ (i : Fin n) (ν : ℂ), ν ∈ periodLattice → ∀ C : Set ℂ,
      IsPreconnected C → C ⊆ Ct → (C ∩ translate ν (curveSet (L i))).Nonempty →
      C ⊆ translate ν (curveSet (L i)) := by
    intro i ν hν C hCpre hCsub hne
    have hchoice : ∀ z : ℂ, z ∈ C → ∃ ε : ℝ, 0 < ε ∧
        ((z ∈ translate ν (curveSet (L i)) →
            ∀ w ∈ Ct, dist w z < ε → w ∈ translate ν (curveSet (L i))) ∧
          (z ∉ translate ν (curveSet (L i)) →
            ∀ w ∈ Ct, dist w z < ε → w ∉ translate ν (curveSet (L i)))) := by
      intro z hz
      by_cases hzp : z ∈ translate ν (curveSet (L i))
      · obtain ⟨ε, hε, hb⟩ := hopen i ν z hν hzp
        exact ⟨ε, hε, fun _ => hb, fun h => absurd hzp h⟩
      · have hznot : z ∉ translate ν (curveSet (L i)) := hzp
        have hcl : z ∉ closure (translate ν (curveSet (L i))) := by
          rw [(hpiece_closed i ν).closure_eq]
          exact hznot
        have h1 : ¬ (∀ ε > 0, ∃ y ∈ translate ν (curveSet (L i)), dist z y < ε) := by
          intro h
          exact hcl (Metric.mem_closure_iff.mpr h)
        push_neg at h1
        obtain ⟨ε, hεpos, hεle⟩ := h1
        refine ⟨ε, hεpos, (fun h => absurd h hznot), ?_⟩
        intro _ w hw hdist hwpiece
        have h1' : ε ≤ dist z w := hεle w hwpiece
        rw [dist_comm] at hdist
        exact absurd h1' (not_le.mpr hdist)
    let εf : ℂ → ℝ := fun z => if hz : z ∈ C then Classical.choose (hchoice z hz) else 1
    have hεf_pos : ∀ z ∈ C, 0 < εf z := by
      intro z hz
      have := (Classical.choose_spec (hchoice z hz)).1
      simpa [εf, dif_pos hz] using this
    have hεf_in : ∀ z ∈ C, z ∈ translate ν (curveSet (L i)) → ∀ w ∈ Ct,
        dist w z < εf z → w ∈ translate ν (curveSet (L i)) := by
      intro z hz hzp w hw hdist
      have hε : εf z = Classical.choose (hchoice z hz) := by simp [εf, dif_pos hz]
      have h2 := (Classical.choose_spec (hchoice z hz)).2.1 hzp w hw
      rw [hε] at hdist
      exact h2 hdist
    have hεf_out : ∀ z ∈ C, z ∉ translate ν (curveSet (L i)) → ∀ w ∈ Ct,
        dist w z < εf z → w ∉ translate ν (curveSet (L i)) := by
      intro z hz hzp w hw hdist
      have hε : εf z = Classical.choose (hchoice z hz) := by simp [εf, dif_pos hz]
      have h2 := (Classical.choose_spec (hchoice z hz)).2.2 hzp w hw
      rw [hε] at hdist
      exact h2 hdist
    set U1 : Set ℂ := ⋃ z ∈ (C ∩ translate ν (curveSet (L i))), Metric.ball z (εf z) with hU1def
    set U2 : Set ℂ := ⋃ z ∈ (C \ translate ν (curveSet (L i))), Metric.ball z (εf z) with hU2def
    have hU1o : IsOpen U1 := isOpen_biUnion fun z _ => Metric.isOpen_ball
    have hU2o : IsOpen U2 := isOpen_biUnion fun z _ => Metric.isOpen_ball
    have hcover : C ⊆ U1 ∪ U2 := by
      intro z hz
      by_cases hzp : z ∈ translate ν (curveSet (L i))
      · exact Or.inl (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr
          ⟨⟨hz, hzp⟩, Metric.mem_ball_self (hεf_pos z hz)⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr
          ⟨⟨hz, hzp⟩, Metric.mem_ball_self (hεf_pos z hz)⟩⟩)
    have hdisj : C ∩ (U1 ∩ U2) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxC, hxU1, hxU2⟩
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxU1
      obtain ⟨haCP, hxa⟩ := Set.mem_iUnion.mp ha
      have haC : a ∈ C := haCP.1
      have haP : a ∈ translate ν (curveSet (L i)) := haCP.2
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxU2
      obtain ⟨hbCP, hxb⟩ := Set.mem_iUnion.mp hb
      have hbC : b ∈ C := hbCP.1
      have hbP : b ∉ translate ν (curveSet (L i)) := hbCP.2
      exact hεf_out b hbC hbP x (hCsub hxC) hxb (hεf_in a haC haP x (hCsub hxC) hxa)
    rcases (isPreconnected_iff_subset_of_disjoint.mp hCpre) U1 U2 hU1o hU2o hcover hdisj
      with h | h
    · intro y hy
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (h hy)
      obtain ⟨haCP, hya⟩ := Set.mem_iUnion.mp ha
      exact hεf_in a haCP.1 haCP.2 y (hCsub hy) hya
    · exfalso
      obtain ⟨a, haC, haP⟩ := hne
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (h haC)
      obtain ⟨hbCP, hab⟩ := Set.mem_iUnion.mp hb
      exact hεf_out b hbCP.1 hbCP.2 a (hCsub haC) hab haP
  -- Step 4: conclude.
  intro z hz
  obtain ⟨i, ν, hν, hzmem⟩ := exists_piece_of_mem L hLw hz
  have hcomp_eq : connectedComponentIn Ct z = translate ν (curveSet (L i)) := by
    apply Subset.antisymm
    · exact hpre i ν hν _ isPreconnected_connectedComponentIn (connectedComponentIn_subset Ct z)
        ⟨z, mem_connectedComponentIn hz, hzmem⟩
    · exact (translate_preconnected ν (curveSet_preconnected (L i))).subset_connectedComponentIn
        hzmem (hpiece_sub i ν hν)
  rw [hcomp_eq]
  exact translate_compact ν (curveSet_compact (L i))

end

end Work.BoxShrink.PinchOff
