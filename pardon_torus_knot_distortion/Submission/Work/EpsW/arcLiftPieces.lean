import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Main
import Submission.Work.Smooth.Plane.Slicing

/-!
# The lifts of the arcs of a torus have compact components

The parameter-plane preimage of an injective arc of a parametrised torus is a locally finite
disjoint union of compact arcs (the lifts of the arc), hence each of its connected components is
compact.  This is the companion, for arcs, of
`Work.BoxShrink.PinchOff.components_compact` (whose hypothesis of vanishing winding has no
analogue for an arc, because an injective arc with distinct endpoints cannot wrap).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.BoxShrink.PinchOff

namespace Work.EpsW

noncomputable section

/-- Clamping `ℝ` onto the arc `ArcInterval = [0,1]`. -/
def clampArc (t : ℝ) : Work.Smooth.Plane.ArcInterval :=
  ⟨max 0 (min t 1), le_max_left 0 (min t 1), max_le zero_le_one (min_le_right t 1)⟩

theorem continuous_clampArc : Continuous clampArc :=
  Continuous.subtype_mk (f := fun t : ℝ => max 0 (min t 1))
    (continuous_const.max (continuous_id.min continuous_const)) (fun t => (clampArc t).2)

/-- On the arc, clamping does nothing. -/
theorem clampArc_eq_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampArc t = ⟨t, ht⟩ := by
  apply Subtype.ext
  show max 0 (min t 1) = t
  have hmin : min t 1 = t := le_antisymm (min_le_left t 1) (le_min le_rfl ht.2)
  have hmax : max 0 t = t := le_antisymm (max_le ht.1 le_rfl) (le_max_right 0 t)
  rw [hmin, hmax]

/-- The period vector map is injective. -/
theorem periodPt_injective : Function.Injective (fun p : ℤ × ℤ => periodPt p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h1 : (a : ℝ) * (2 * Real.pi) = (c : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re h
    simpa [periodPt_re] using this
  have h2 : (b : ℝ) * (2 * Real.pi) = (d : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im h
    simpa [periodPt_im] using this
  have ha : a = c := by
    have h : (a : ℝ) = (c : ℝ) := mul_right_cancel₀ hpi h1
    exact_mod_cast h
  have hb : b = d := by
    have h : (b : ℝ) = (d : ℝ) := mul_right_cancel₀ hpi h2
    exact_mod_cast h
  simp [ha, hb]

/-- Two parameter-plane points with the same image on the surface differ by a period vector. -/
theorem sub_mem_periodLattice_of_planePsi_eq {P : Work.CoreTopology.ParamTorus} {u v : ℂ}
    (h : planePsi P u = planePsi P v) : u - v ∈ periodLattice := by
  have h1 : Work.TorusCover.psiMap P.psi (u.re, u.im) =
      Work.TorusCover.psiMap P.psi (v.re, v.im) := h
  obtain ⟨k, l, hkl⟩ := (Work.TorusCover.mem_lattice_iff' _).mp
    ((Work.TorusCover.psiMap_eq_iff_param P).mp h1)
  rw [mem_periodLattice]
  refine ⟨k, l, ?_⟩
  have hk : u.re - v.re = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Prod.fst hkl
    simpa using this
  have hl : u.im - v.im = (l : ℝ) * (2 * Real.pi) := by
    have := congrArg Prod.snd hkl
    simpa using this
  apply Complex.ext
  · simp [Complex.sub_re, periodPt_re, hk]
  · simp [Complex.sub_im, periodPt_im, hl]


/-- **A ball around a point of a piece meets no other piece.**  For a locally finite family of
pairwise disjoint closed sets and a point `y` of a piece `F i₀`, there is a ball around `y` meeting
`⋃ F` only inside `F i₀`. -/
theorem exists_ball_separating_piece {ι : Type*} {F : ι → Set ℂ}
    (hcpt : ∀ i : ι, IsCompact (F i)) (hdisj : ∀ i j : ι, i ≠ j → Disjoint (F i) (F j))
    (hfin : ∀ z : ℂ, {i : ι | (F i ∩ Metric.ball z 1).Nonempty}.Finite)
    {i₀ : ι} {y : ℂ} (hy : y ∈ F i₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ ⋃ i, F i, dist q y < ε → q ∈ F i₀ := by
  classical
  set T : Set ι := {j : ι | (F j ∩ Metric.ball y 1).Nonempty ∧ j ≠ i₀} with hT
  have hTfin : T.Finite := (hfin y).subset (fun j hj => hj.1)
  have hpos : ∀ j ∈ T, ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ F j, ε ≤ dist q y := by
    intro j hj
    have hyj : y ∉ F j := fun h => Set.disjoint_left.mp (hdisj j i₀ hj.2) h hy
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((hcpt j).isClosed.isOpen_compl.mem_nhds hyj)
    refine ⟨ε, hε, fun q hq => ?_⟩
    by_contra hcon
    exact hεsub (Metric.mem_ball.mpr (not_le.mp hcon)) hq
  set S : Set ℝ := (fun j => if h : j ∈ T then Classical.choose (hpos j h) else 1) '' T with hS
  have hSfin : S.Finite := hTfin.image _
  have hSpos : ∀ r ∈ S, 0 < r := by
    rintro r ⟨j, hj, rfl⟩
    simp only [dif_pos hj]
    exact (Classical.choose_spec (hpos j hj)).1
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_of_finite hSfin hSpos
  refine ⟨min 1 δ, lt_min one_pos hδpos, ?_⟩
  intro q hq hdist
  obtain ⟨j, hqj⟩ := Set.mem_iUnion.mp hq
  by_cases hji : j = i₀
  · rwa [hji] at hqj
  · exfalso
    have hq1 : q ∈ Metric.ball y 1 :=
      Metric.mem_ball.mpr (lt_of_lt_of_le hdist (min_le_left (1 : ℝ) δ))
    have hjT : j ∈ T := ⟨⟨q, hqj, hq1⟩, hji⟩
    have h1 : δ ≤ Classical.choose (hpos j hjT) := by
      have h0 := hδle _ ⟨j, hjT, rfl⟩
      simpa only [dif_pos hjT] using h0
    have h2 : Classical.choose (hpos j hjT) ≤ dist q y :=
      (Classical.choose_spec (hpos j hjT)).2 q hqj
    have h3 : dist q y < δ := lt_of_lt_of_le hdist (min_le_right (1 : ℝ) δ)
    linarith

/-- **Every connected component of a locally finite disjoint union of compact preconnected sets is
one of the pieces.** -/
theorem pieces_components_compact {ι : Type*} {F : ι → Set ℂ}
    (hcpt : ∀ i : ι, IsCompact (F i)) (hdisj : ∀ i j : ι, i ≠ j → Disjoint (F i) (F j))
    (hfin : ∀ z : ℂ, {i : ι | (F i ∩ Metric.ball z 1).Nonempty}.Finite)
    (hpre : ∀ i : ι, IsPreconnected (F i)) :
    ∀ z ∈ ⋃ i, F i, IsCompact (connectedComponentIn (⋃ i, F i) z) := by
  intro z hz
  obtain ⟨i₀, hz₀⟩ := Set.mem_iUnion.mp hz
  set U : Set ℂ := ⋃ i, F i with hU
  set S : Set ℂ := ⋃ j ∈ ({j : ι | j ≠ i₀} : Set ι), F j with hSdef
  have hCU : connectedComponentIn U z ⊆ F i₀ ∪ closure S := by
    intro w hw
    have hwU : w ∈ U := connectedComponentIn_subset U z hw
    obtain ⟨j, hwj⟩ := Set.mem_iUnion.mp hwU
    by_cases hji : j = i₀
    · exact Or.inl (hji ▸ hwj)
    · exact Or.inr (subset_closure (Set.mem_iUnion₂.mpr ⟨j, hji, hwj⟩))
  have hCdisj : connectedComponentIn U z ∩ (F i₀ ∩ closure S) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwC, hwF, hwcl⟩
    obtain ⟨ε, hε, hεsub⟩ := exists_ball_separating_piece hcpt hdisj hfin hwF
    obtain ⟨u, huS, huε⟩ := Metric.mem_closure_iff.mp hwcl ε hε
    obtain ⟨j, hj, huj⟩ := Set.mem_iUnion₂.mp huS
    have huU : u ∈ U := Set.mem_iUnion.mpr ⟨j, huj⟩
    have huF : u ∈ F i₀ := hεsub u huU (by rw [dist_comm]; exact huε)
    exact Set.disjoint_left.mp (hdisj i₀ j (Ne.symm hj)) huF huj
  have hsub : connectedComponentIn U z ⊆ F i₀ := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (x := z) (F := U))) (F i₀) (closure S)
      (hcpt i₀).isClosed isClosed_closure hCU hCdisj with h | h
    · exact h
    · exfalso
      have hmem : z ∈ connectedComponentIn U z ∩ (F i₀ ∩ closure S) :=
        ⟨mem_connectedComponentIn hz, hz₀, h (mem_connectedComponentIn hz)⟩
      rw [hCdisj] at hmem
      exact Set.notMem_empty z hmem
  have hsup : F i₀ ⊆ connectedComponentIn U z :=
    (hpre i₀).subset_connectedComponentIn hz₀ (Set.subset_iUnion F i₀)
  have hUdef : connectedComponentIn U z = F i₀ := Subset.antisymm hsub hsup
  rw [hUdef]
  exact hcpt i₀

/-- **A continuous arc of the carrier lifts to the parameter plane.** -/
theorem exists_lift_arc {P : Work.CoreTopology.ParamTorus}
    {a : ContinuousMap Work.Smooth.Plane.ArcInterval R3} (hmem : ∀ x, a x ∈ P.carrier) :
    ∃ c : ℝ → ℂ, Continuous c ∧ ∀ t : ℝ, planePsi P (c t) = a (clampArc t) := by
  have hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi) :=
    Work.TorusCover.isCoveringMap_psiMapToRange_param P
  have hgcont : Continuous fun t : ℝ => a (clampArc t) := a.continuous.comp continuous_clampArc
  have hgmem : ∀ t : ℝ, a (clampArc t) ∈ P.carrier := fun t => hmem (clampArc t)
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ × ℝ, Work.TorusCover.psiMap P.psi p₀ = a (clampArc 0) := hgmem 0
  have hfcont : Continuous fun t : ℝ =>
      (⟨a (clampArc t), hgmem t⟩ : Set.range (Work.TorusCover.psiMap P.psi)) :=
    Continuous.subtype_mk hgcont hgmem
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨fun t : ℝ => ⟨a (clampArc t), hgmem t⟩, hfcont⟩ :
      C(ℝ, Set.range (Work.TorusCover.psiMap P.psi))) 0 p₀ (Subtype.ext hp₀)
  have hF' : ∀ t : ℝ, Work.TorusCover.psiMap P.psi (F t) = a (clampArc t) :=
    fun t => congrArg Subtype.val (congrFun hFlift t)
  refine ⟨fun t => ((F t).1 : ℂ) + ((F t).2 : ℂ) * Complex.I, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (continuous_fst.comp F.continuous)).add
      ((Complex.continuous_ofReal.comp (continuous_snd.comp F.continuous)).mul
        continuous_const)
  · intro t
    have h : planePsi P (((F t).1 : ℂ) + ((F t).2 : ℂ) * Complex.I)
        = Work.TorusCover.psiMap P.psi (F t) := by
      simp [planePsi, Work.TorusCover.psiMap]
    rw [h, hF' t]

/-- **Every connected component of the parameter-plane preimage of a finite disjoint union of
injective arcs of the surface is compact.** -/
theorem components_compact_preimage_arcs_local {P : Work.CoreTopology.ParamTorus} {m : ℕ}
    {a : Fin m → ContinuousMap Work.Smooth.Plane.ArcInterval R3}
    (hinj : ∀ j : Fin m, Function.Injective (a j))
    (hmem : ∀ (j : Fin m) (x : Work.Smooth.Plane.ArcInterval), a j x ∈ P.carrier)
    (hdisj : Pairwise fun j j' : Fin m => Disjoint (Set.range (a j)) (Set.range (a j'))) :
    ∀ z ∈ Xtilde P (⋃ j, Set.range (a j)),
      IsCompact (connectedComponentIn (Xtilde P (⋃ j, Set.range (a j))) z) := by
  classical
  have hlift : ∀ j : Fin m, ∃ c : ℝ → ℂ, Continuous c ∧
      ∀ t : ℝ, planePsi P (c t) = a j (clampArc t) :=
    fun j => exists_lift_arc (P := P) (a := a j) (hmem j)
  choose c hccont hclift using hlift
  let K : Fin m → Set ℂ := fun j => c j '' Set.Icc (0 : ℝ) 1
  have hKcpt : ∀ j, IsCompact (K j) :=
    fun j => isCompact_Icc.image (hccont j)
  have hKpre : ∀ j, IsPreconnected (K j) :=
    fun j => (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).image (c j) (hccont j).continuousOn
  -- the pieces: the period translates of the lifts of the arcs
  have hpiece_cpt : ∀ q : Fin m × (ℤ × ℤ),
      IsCompact (Work.BoxShrink.PinchOff.translate (periodPt q.2.1 q.2.2) (K q.1)) :=
    fun q => translate_compact _ (hKcpt q.1)
  have hpiece_pre : ∀ q : Fin m × (ℤ × ℤ),
      IsPreconnected (Work.BoxShrink.PinchOff.translate (periodPt q.2.1 q.2.2) (K q.1)) :=
    fun q => translate_preconnected _ (hKpre q.1)
  have hpiece_disj : ∀ q q' : Fin m × (ℤ × ℤ), q ≠ q' →
      Disjoint (Work.BoxShrink.PinchOff.translate (periodPt q.2.1 q.2.2) (K q.1))
        (Work.BoxShrink.PinchOff.translate (periodPt q'.2.1 q'.2.2) (K q'.1)) := by
    rintro ⟨j, p⟩ ⟨j', p'⟩ hne
    rw [Set.disjoint_left]
    rintro z hz1 hz2
    rw [Work.BoxShrink.PinchOff.mem_translate] at hz1 hz2
    obtain ⟨s, hs, hcs⟩ := hz1
    obtain ⟨s', hs', hcs'⟩ := hz2
    have hmem_p : periodPt p.1 p.2 ∈ periodLattice := (mem_periodLattice _).mpr ⟨p.1, p.2, rfl⟩
    have hmem_p' : periodPt p'.1 p'.2 ∈ periodLattice := (mem_periodLattice _).mpr ⟨p'.1, p'.2, rfl⟩
    have hz1' : planePsi P z = a j ⟨s, hs⟩ := by
      have h1 : z = c j s + periodPt p.1 p.2 := by rw [hcs]; ring
      rw [h1, planePsi_add_periodLattice P _ _ hmem_p, hclift j s, clampArc_eq_of_mem hs]
    have hz2' : planePsi P z = a j' ⟨s', hs'⟩ := by
      have h1 : z = c j' s' + periodPt p'.1 p'.2 := by rw [hcs']; ring
      rw [h1, planePsi_add_periodLattice P _ _ hmem_p', hclift j' s', clampArc_eq_of_mem hs']
    have hsame : a j ⟨s, hs⟩ = a j' ⟨s', hs'⟩ := hz1'.symm.trans hz2'
    by_cases hjj : j = j'
    · subst hjj
      have hsub := hinj j hsame
      have hsv : s = s' := congrArg Subtype.val hsub
      have hw : periodPt p.1 p.2 = periodPt p'.1 p'.2 := by
        have e1 : z = c j s + periodPt p.1 p.2 := by rw [hcs]; ring
        have e2 : z = c j s' + periodPt p'.1 p'.2 := by rw [hcs']; ring
        have h1 : c j s + periodPt p.1 p.2 = c j s' + periodPt p'.1 p'.2 := by
          rw [← e1, ← e2]
        rw [hsv] at h1
        exact add_left_cancel h1
      have hpp : p = p' := periodPt_injective hw
      exact hne (by rw [hpp])
    · exact Set.disjoint_left.mp (hdisj hjj) ⟨⟨s, hs⟩, rfl⟩ ⟨⟨s', hs'⟩, hsame.symm⟩
  have hpiece_fin : ∀ z : ℂ,
      {q : Fin m × (ℤ × ℤ) |
        (Work.BoxShrink.PinchOff.translate (periodPt q.2.1 q.2.2) (K q.1) ∩ Metric.ball z 1).Nonempty}.Finite := by
    intro z
    have hper : ∀ j : Fin m,
        ({p : ℤ × ℤ |
          (Work.BoxShrink.PinchOff.translate (periodPt p.1 p.2) (K j) ∩ Metric.ball z 1).Nonempty}).Finite := by
      intro j
      obtain ⟨M, hM⟩ := (hKcpt j).isBounded.subset_closedBall (0 : ℂ)
      have hM' : ∀ k ∈ K j, ‖k‖ ≤ M := fun k hk => by
        have h1 := hM hk
        rwa [Metric.mem_closedBall, dist_zero_right] at h1
      have hsub : {p : ℤ × ℤ |
            (Work.BoxShrink.PinchOff.translate (periodPt p.1 p.2) (K j) ∩ Metric.ball z 1).Nonempty}
          ⊆ (fun p : ℤ × ℤ => periodPt p.1 p.2) ⁻¹'
            {w : ℂ | w ∈ periodLattice ∧ ‖w‖ ≤ M + ‖z‖ + 1} := by
        rintro p ⟨y, hy1, hy2⟩
        rw [Work.BoxShrink.PinchOff.mem_translate] at hy1
        have hKy : ‖y - periodPt p.1 p.2‖ ≤ M := hM' _ hy1
        have hzy : dist y z < 1 := Metric.mem_ball.mp hy2
        refine ⟨(mem_periodLattice _).mpr ⟨p.1, p.2, rfl⟩, ?_⟩
        have h1 : ‖periodPt p.1 p.2‖ ≤ ‖y‖ + ‖y - periodPt p.1 p.2‖ := by
          calc ‖periodPt p.1 p.2‖ = ‖y - (y - periodPt p.1 p.2)‖ := by ring_nf
            _ ≤ ‖y‖ + ‖y - periodPt p.1 p.2‖ := norm_sub_le _ _
        have h2 : ‖y‖ ≤ ‖z‖ + 1 := by
          have h3 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
            calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
              _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
          rw [← dist_eq_norm] at h3
          linarith
        linarith
      exact ((finite_periodLattice_ball (M + ‖z‖ + 1)).preimage
        (periodPt_injective.injOn)).subset hsub
    refine Set.Finite.subset (Set.finite_iUnion (fun j : Fin m =>
      (hper j).image (fun p => (j, p)))) ?_
    rintro ⟨j, p⟩ hp
    exact Set.mem_iUnion.mpr ⟨j, ⟨p, hp, rfl⟩⟩
  have hpiece_cover : (⋃ q : Fin m × (ℤ × ℤ),
      Work.BoxShrink.PinchOff.translate (periodPt q.2.1 q.2.2) (K q.1)) = Xtilde P (⋃ j, Set.range (a j)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
      obtain ⟨j, p⟩ := q
      rw [Work.BoxShrink.PinchOff.mem_translate] at hq
      obtain ⟨s, hs, hcs⟩ := hq
      have hmem_p : periodPt p.1 p.2 ∈ periodLattice := (mem_periodLattice _).mpr ⟨p.1, p.2, rfl⟩
      have h2 : planePsi P z = a j ⟨s, hs⟩ := by
        have h1 : z = c j s + periodPt p.1 p.2 := by rw [hcs]; ring
        rw [h1, planePsi_add_periodLattice P _ _ hmem_p, hclift j s, clampArc_eq_of_mem hs]
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨⟨s, hs⟩, h2.symm⟩⟩
    · intro hz
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, hx⟩ := hx
      have hs : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.2
      have hxe : (⟨(x : ℝ), hs⟩ : Work.Smooth.Plane.ArcInterval) = x := Subtype.ext rfl
      have hpl : planePsi P (c j (x : ℝ)) = planePsi P z := by
        rw [hclift j (x : ℝ), clampArc_eq_of_mem hs, hxe, hx]
      obtain ⟨k, l, hkl⟩ := (mem_periodLattice _).mp (sub_mem_periodLattice_of_planePsi_eq hpl.symm)
      refine Set.mem_iUnion.mpr ⟨(j, (k, l)), ?_⟩
      rw [Work.BoxShrink.PinchOff.mem_translate]
      refine ⟨(x : ℝ), hs, ?_⟩
      rw [hkl]
      ring_nf
  rw [← hpiece_cover]
  exact pieces_components_compact hpiece_cpt hpiece_disj hpiece_fin hpiece_pre

end

end Work.EpsW
