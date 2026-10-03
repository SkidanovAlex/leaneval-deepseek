import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.HB.Phi_component_proper
import Submission.Work.HornTopo.horn_topo
import Submission.Work.HornVarphi.horn_varphi
import Submission.Work.HornVarphi.deriv_iterate_ne_zero
import Submission.Work.HornSC.horn_sc
import Submission.Work.PlanarSC.planar_inter_sc
import Submission.Work.BasinSC.basin_sc
import Submission.Work.HornCov.sheet_varphi
import Submission.Work.HornCov.covering_components_homeomorph
import Submission.Work.Horn.biholo_component_of_preimage
import Submission.Work.Horn.image_eq_of_compact_preimage
import Submission.Work.BasinSC.step
import Submission.Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit
import Submission.Work.HornCov.sheet_Phi
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-! Guidance from the project lead (the requester):

LEAD DESIGN (read Submission/Work/Horn/HB/DESIGN.md). Piece HB2: local finiteness of E = Φ∘φ over ball(Φ c, r), r < 1.
Route:
1. Z := connectedComponentIn (B ∩ Φ⁻¹(ball (Φ c) r)) (φ w); note φ w ∈ B because w ∈ BuOf ∪ BlOf ⊆ Btil. By sibling HB1 (Work.Horn.HB.Phi_component_proper, dispatched in parallel; import it), Φ|Z is proper onto the ball. It is surjective because a proper map is closed and a holomorphic non-constant map is open; U is connected.
2. The critical points of Φ in Z are at most {c}. On Z ∩ Y_m, Φ = Ψ∘f^m − m with (Φ|Ωp)' ≠ 0, so Φ'(z) = 0 ⇒ (f^m)'(z) = 0 ⇒ f^j z = c for some j, by uniqueness of c in B (Work.HornVarphi.deriv_iterate_ne_zero may help). Then Φ z = Φ c − j ∈ ball(Φc, r) with r < 1 forces j = 0.
   Hence Z is simply connected by Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit (or Work.BasinSC.simplyConnected_of_proper_holomorphic_no_crit if c ∉ Z). V = ball ≠ univ.
3. Z ∩ critOrbit f₀ c = ∅, since Φ(f^j c) = Φ c + j ∉ ball for j ≥ 1.
4. φ is a covering over B ∖ critOrbit on BuOf ∪ BlOf: Work.HornCov.sheet_varphi with the proved inputs Work.HornTopo.horn_topo, Work.HornVarphi.horn_varphi and the HornSC theorem; grep their exact names. Restricting to the component C of (BuOf ∪ BlOf) ∩ φ⁻¹Z through w gives a covering C → Z, which is bijective by Work.BasinSC.covering_bijective_of_simplyConnected. So φ|C is a homeomorphism onto Z.
5. C equals the E-component in the goal: φ maps the E-component into Z (it is connected and contains φ w), and C ⊆ E⁻¹(ball).
6. C ∩ E⁻¹K = (φ|C)⁻¹(Z ∩ Φ⁻¹K), which is compact.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology

open scoped _root_.Topology

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- **`E` is continuous on a neighbourhood of each of its points of `Ω ⊆ B̃ᵘ ∪ B̃ˡ`**; hence
`Ω ∩ E ⁻¹' V` is open for open `V`. -/
theorem isOpen_inter_preimage_E {d : MandelDim.ParabData f₀ D₀}
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩsub : Ω ⊆ MandelDim.BuOf d B ∪ MandelDim.BlOf d B)
    {V : Set ℂ} (hVo : IsOpen V) : IsOpen (Ω ∩ d.E ⁻¹' V) := by
  obtain ⟨-, -, -, -, -, -, hsubDE⟩ := Work.HornTopo.horn_topo f₀ D₀ B c d hS
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzΩ, hzV⟩
  have hzDE : z ∈ d.DE := hsubDE (hΩsub hzΩ)
  have hφc : ContinuousAt d.φ z :=
    (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hzDE.1)).continuousAt
  have hΦc : ContinuousAt d.Φ (d.φ z) :=
    (d.Φ_holo.differentiableAt
      ((Work.HornCov.isOpen_parabolicBasin f₀ D₀).mem_nhds hzDE.2)).continuousAt
  have hEc : ContinuousAt d.E z := hΦc.comp hφc
  exact Filter.inter_mem (hΩo.mem_nhds hzΩ) (hEc.preimage_mem_nhds (hVo.mem_nhds hzV))

/-- **`Φ` increases by one along the orbit.** -/
theorem Phi_iterate (d : MandelDim.ParabData f₀ D₀) (hS : MandelDim.IsF0Setup f₀ D₀ B c)
    {z : ℂ} (hz : z ∈ B) (n : ℕ) : d.Φ (f₀^[n] z) = d.Φ z + (n : ℂ) := by
  have himm : MandelDim.IsImmediateBasin f₀ D₀ B := hS.2.1
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := himm.2.2.1
  have hBmaps : Set.MapsTo f₀ B B := himm.2.2.2.2.1
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : f₀^[k] z ∈ B := hBmaps.iterate k hz
      rw [Function.iterate_succ_apply', d.Φ_abel _ (hBsub hk), ih]
      push_cast
      ring

/-- **A critical point of `Φ` in the basin is a backward iterate of the critical point `c`.** -/
theorem exists_iterate_eq_crit_of_deriv_Phi_eq_zero (d : MandelDim.ParabData f₀ D₀)
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) {z : ℂ} (hzB : z ∈ B)
    (hz : deriv d.Φ z = 0) : ∃ j : ℕ, f₀^[j] z = c := by
  have himm : MandelDim.IsImmediateBasin f₀ D₀ B := hS.2.1
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := himm.2.2.1
  have hBmaps : Set.MapsTo f₀ B B := himm.2.2.2.2.1
  have hiterz : ∀ j : ℕ, f₀^[j] z ∈ B := fun j => hBmaps.iterate j hzB
  obtain ⟨m, hm⟩ := d.basin_enter z (hBsub hzB) (fun n => d.orbit_avoid z (hBsub hzB) n)
  -- differentiability of the iterates along the orbit
  have hBsubD : B ⊆ D₀ := by
    intro w hw
    obtain ⟨U, hU, hmaps, -⟩ := hBsub hw
    simpa using hmaps 0 (mem_of_mem_nhds hU)
  have hderivB : ∀ w ∈ B, DifferentiableAt ℂ f₀ w := fun w hw =>
    (hS.1.2.2.1).differentiableAt ((hS.1.1).mem_nhds (hBsubD hw))
  have hdit : ∀ j : ℕ, DifferentiableAt ℂ (f₀^[j]) z := by
    intro j
    induction j with
    | zero => simpa using differentiableAt_id
    | succ k ih =>
        rw [show (f₀^[k.succ]) = f₀ ∘ (f₀^[k]) from by
          funext x; rw [Function.iterate_succ_apply']; rfl]
        exact (hderivB (f₀^[k] z) (hiterz k)).comp z ih
  -- `Φ` is a local biholomorphism on the petal
  have hneΦ : deriv d.Φ (f₀^[m] z) ≠ 0 := by
    obtain ⟨ρ, hρ0, hρsub⟩ := Metric.mem_nhds_iff.mp (d.Ωp_open.mem_nhds hm)
    exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρ0
      (Work.HornCov.analyticAt_Phi_of_mem d.Ωp_sub hm) (d.Φ_inj.mono hρsub)
  -- differentiate `Φ ∘ f^m = Φ + m` at `z`
  have hev : (fun u => d.Φ (f₀^[m] u)) =ᶠ[𝓝 z] (fun u => d.Φ u + (m : ℂ)) := by
    filter_upwards [himm.1.mem_nhds hzB] with u hu
    exact Phi_iterate d hS hu m
  have hzero : deriv (f₀^[m]) z = 0 := by
    have h1 : deriv (fun u => d.Φ (f₀^[m] u)) z = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_add_const, hz]
    have h2 : deriv (fun u => d.Φ (f₀^[m] u)) z
        = deriv d.Φ (f₀^[m] z) * deriv (f₀^[m]) z := by
      rw [show (fun u => d.Φ (f₀^[m] u)) = (d.Φ ∘ (f₀^[m])) from rfl]
      exact deriv_comp z (d.Φ_holo.differentiableAt
        ((Work.HornCov.isOpen_parabolicBasin f₀ D₀).mem_nhds (d.Ωp_sub hm))) (hdit m)
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hneΦ
    · exact h
  -- the product formula
  have hprod := Work.HornVarphi.deriv_iterate_eq_prod hBmaps hderivB hzB m
  rw [hprod] at hzero
  obtain ⟨j, hjmem, hj0⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact ⟨j, hS.2.2.2.2 (f₀^[j] z) (hiterz j) hj0⟩

/-- **A connected component of the preimage under a covering map of a simply connected open set is
mapped homeomorphically onto it.** -/
theorem exists_homeomorph_connectedComponentIn_of_isCoveringMapOn {Ω Z : Set ℂ} {φ : ℂ → ℂ}
    (hΩo : IsOpen Ω) (hZo : IsOpen Z) [SimplyConnectedSpace ↥Z]
    [LocallyPathConnectedSpace ↥Z] (hcov : IsCoveringMapOn (fun z : ↥Ω => φ z) Z)
    (hφc : ContinuousOn φ Ω) {w : ℂ} (hw : w ∈ Ω) (hwZ : φ w ∈ Z) :
    ∃ H : ↥(connectedComponentIn (Ω ∩ φ ⁻¹' Z) w) ≃ₜ ↥Z, ∀ z, (H z : ℂ) = φ z := by
  classical
  set C : Set ℂ := connectedComponentIn (Ω ∩ φ ⁻¹' Z) w with hCdef
  have hCsub : C ⊆ Ω ∩ φ ⁻¹' Z := connectedComponentIn_subset _ _
  have hwC : w ∈ C := mem_connectedComponentIn ⟨hw, hwZ⟩
  -- the global section of the covering through `w`
  obtain ⟨F, hF1, hF2⟩ := (hcov.existsUnique_continuousMap_lifts
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Z, ℂ))
      (a₀ := (⟨φ w, hwZ⟩ : ↥Z)) (e₀ := (⟨w, hw⟩ : ↥Ω)) (by rfl) (fun a => a.2)).exists
  have hsec : ∀ a : ↥Z, φ ((F a : ↥Ω) : ℂ) = (a : ℂ) := fun a => congr_fun hF2 a
  have hFsub : ∀ a : ↥Z, ((F a : ↥Ω) : ℂ) ∈ Ω ∩ φ ⁻¹' Z :=
    fun a => ⟨(F a).2, by
      show φ ((F a : ↥Ω) : ℂ) ∈ Z
      rw [hsec a]
      exact a.2⟩
  -- the range of the section lies in the component `C`
  have hcontF : Continuous fun a : ↥Z => ((F a : ↥Ω) : ℂ) :=
    continuous_subtype_val.comp F.continuous
  have hrangeF : Set.range (fun a : ↥Z => ((F a : ↥Ω) : ℂ)) ⊆ C := by
    refine IsPreconnected.subset_connectedComponentIn (isPreconnected_range hcontF) ?_ ?_
    · exact ⟨⟨φ w, hwZ⟩, by show ((F ⟨φ w, hwZ⟩ : ↥Ω) : ℂ) = w; rw [hF1]⟩
    · rintro y ⟨a, rfl⟩; exact hFsub a
  -- the two maps
  let φC : ↥Z → ↥C := fun a => ⟨((F a : ↥Ω) : ℂ), hrangeF ⟨a, rfl⟩⟩
  have hφCcont : Continuous φC := Continuous.subtype_mk hcontF (fun a => hrangeF ⟨a, rfl⟩)
  let p' : ↥C → ↥Z := fun z => ⟨φ (z : ℂ), (hCsub z.2).2⟩
  have hp'cont : Continuous p' :=
    Continuous.subtype_mk (hφc.comp_continuous continuous_subtype_val
      (fun z => (hCsub z.2).1)) (fun z => (hCsub z.2).2)
  have hrp : ∀ a : ↥Z, p' (φC a) = a := fun a => Subtype.ext (hsec a)
  have hclosed : IsClosed (Set.range φC) :=
    Work.HornCov.isClosed_range_of_continuous_section hp'cont hφCcont hrp
  -- openness of the range: it is the preimage of the (open) range of the section under the
  -- inclusion `↥C → ↥Ω`
  have hFopen : IsOpenMap (F : ↥Z → ↥Ω) :=
    Work.HornCov.isOpenMap_of_isLocalHomeomorphOn_comp hcov.isLocalHomeomorphOn
      (fun a => by
        show φ ((F a : ↥Ω) : ℂ) ∈ Z
        rw [hsec a]
        exact a.2) F.continuous hsec
      hZo.isOpenEmbedding_subtypeVal
  have hincl : Continuous fun z : ↥C => (⟨(z : ℂ), (hCsub z.2).1⟩ : ↥Ω) :=
    continuous_id.subtype_map (fun x hx => (hCsub hx).1)
  have hopen : IsOpen (Set.range φC) := by
    have hset : Set.range φC =
        (fun z : ↥C => (⟨(z : ℂ), (hCsub z.2).1⟩ : ↥Ω)) ⁻¹' Set.range (F : ↥Z → ↥Ω) := by
      ext z; constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, Subtype.ext rfl⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext (by simpa using congrArg Subtype.val ha)⟩
    rw [hset]
    exact hFopen.isOpen_range.preimage hincl
  have hclopen : IsClopen (Set.range φC) := ⟨hclosed, hopen⟩
  have hne : (Set.range φC).Nonempty := ⟨φC ⟨φ w, hwZ⟩, ⟨_, rfl⟩⟩
  haveI hpreC : PreconnectedSpace ↥C := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have huniv : Set.range φC = Set.univ := hclopen.eq_univ hne
  have hsurj : Function.Surjective φC := fun z => by
    have h : z ∈ Set.range φC := huniv ▸ Set.mem_univ z
    exact h
  have hinj : Function.Injective φC := by
    intro a b hab
    have h1 : φ ((φC a : ↥C) : ℂ) = φ ((φC b : ↥C) : ℂ) :=
      congrArg (fun z : ↥C => φ (z : ℂ)) hab
    have h2 : φ ((φC a : ↥C) : ℂ) = (a : ℂ) := hsec a
    have h3 : φ ((φC b : ↥C) : ℂ) = (b : ℂ) := hsec b
    rw [h2, h3] at h1
    exact Subtype.ext h1
  have hleft : Function.LeftInverse φC p' := by
    intro z
    obtain ⟨a, rfl⟩ := hsurj z
    rw [hrp a]
  let H : ↥(connectedComponentIn (Ω ∩ φ ⁻¹' Z) w) ≃ₜ ↥Z :=
    { toEquiv := { toFun := p', invFun := φC, left_inv := hleft, right_inv := hrp },
      continuous_toFun := hp'cont, continuous_invFun := hφCcont }
  exact ⟨H, fun z => rfl⟩

/-- **Two components of an open set `Y = Ω ∪ Ω'` (a disjoint union of opens) intersected with `T`
coincide when taken inside `Ω`.** -/
theorem connectedComponentIn_inter_eq_of_clopen {Y Ω Ω' T : Set ℂ} {w : ℂ}
    (hΩo : IsOpen Ω) (hΩ'o : IsOpen Ω') (hdisj : Disjoint Ω Ω') (hY : Y = Ω ∪ Ω')
    (hT : IsOpen (Ω ∩ T)) (hT' : IsOpen (Ω' ∩ T)) (hw : w ∈ Ω ∩ T) :
    connectedComponentIn (Y ∩ T) w = connectedComponentIn (Ω ∩ T) w := by
  have hdisjI : Disjoint (Ω ∩ T) (Ω' ∩ T) :=
    hdisj.mono Set.inter_subset_left Set.inter_subset_left
  have hsub : connectedComponentIn (Y ∩ T) w ⊆ Ω ∩ T := by
    refine Work.HornCov.preconnected_subset_left_of_subset_union hT hT' hdisjI
      isPreconnected_connectedComponentIn ?_ ?_
    · intro z hz
      have hz' : z ∈ Y ∩ T := connectedComponentIn_subset _ _ hz
      rw [hY] at hz'
      rcases hz'.1 with h | h
      · exact Or.inl ⟨h, hz'.2⟩
      · exact Or.inr ⟨h, hz'.2⟩
    · exact ⟨w, mem_connectedComponentIn (by rw [hY]; exact ⟨Or.inl hw.1, hw.2⟩), hw⟩
  have hwY : w ∈ Y ∩ T := by rw [hY]; exact ⟨Or.inl hw.1, hw.2⟩
  refine Set.Subset.antisymm ?_ ?_
  · refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hwY) hsub
  · refine connectedComponentIn_mono w ?_
    intro z hz
    rw [hY]
    exact ⟨Or.inl hz.1, hz.2⟩

/-- **A proper holomorphic map onto a connected open set is surjective** (the version of
`Work.Horn.image_eq_of_compact_preimage` without the hypothesis that the target lie in the domain
of holomorphy). -/
theorem image_eq_of_isCompact_preimage {G : ℂ → ℂ} {D Wn Wn1 : Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hWn : IsOpen Wn) (hWnc : IsConnected Wn)
    (hW1o : IsOpen Wn1) (hW1D : Wn1 ⊆ D) (hW1ne : Wn1.Nonempty)
    (hmaps : G '' Wn1 ⊆ Wn)
    (hprop : ∀ L : Set ℂ, L ⊆ Wn → IsCompact L → IsCompact (Wn1 ∩ G ⁻¹' L)) :
    G '' Wn1 = Wn := by
  have hGcont : ContinuousOn G Wn1 := hG.continuousOn.mono hW1D
  have hGan : AnalyticOnNhd ℂ G Wn1 := (hG.mono hW1D).analyticOnNhd hW1o
  have hopen : IsOpen (G '' Wn1) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    rcases (hGan x hx).eventually_constant_or_nhds_le_map_nhds with hconst | hmap
    · exfalso
      let C : Set ℂ := connectedComponentIn Wn1 x
      have hxC : x ∈ C := mem_connectedComponentIn hx
      have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
      have hCW : C ⊆ Wn1 := connectedComponentIn_subset Wn1 x
      have hCopen : IsOpen C := hW1o.connectedComponentIn
      have hCconst : ∀ z ∈ C, G z = G x :=
        AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hGan.mono hCW)
          (analyticOnNhd_const (v := G x)) hCpre hxC hconst
      have hGxWn : G x ∈ Wn := hmaps ⟨x, hx, rfl⟩
      have hKc : IsCompact (Wn1 ∩ G ⁻¹' {G x}) :=
        hprop {G x} (Set.singleton_subset_iff.mpr hGxWn) isCompact_singleton
      have hCK : C ⊆ Wn1 ∩ G ⁻¹' {G x} := fun z hz =>
        ⟨hCW hz, by simpa using hCconst z hz⟩
      have hCcl : IsClosed C := by
        rw [← closure_subset_iff_isClosed]
        intro z hz
        exact IsPreconnected.subset_connectedComponentIn hCpre.closure (subset_closure hxC)
          ((IsCompact.isClosed hKc).closure_subset_iff.mpr hCK |>.trans inter_subset_left) hz
      have hCne : C ≠ univ := fun h =>
        hKc.ne_univ (Set.eq_univ_of_univ_subset (h ▸ hCK))
      rcases (isPreconnected_univ (α := ℂ)).subset_or_subset hCopen hCcl.isOpen_compl
        disjoint_compl_right (by rintro z -; by_cases h : z ∈ C <;> simp [h]) with h | h
      · exact hCne (Set.eq_univ_of_univ_subset h)
      · exact (h (mem_univ x)) hxC
    · exact hmap (Filter.image_mem_map (hW1o.mem_nhds hx))
  have hclosed : closure (G '' Wn1) ∩ Wn ⊆ G '' Wn1 := by
    rintro y ⟨hycl, hyWn⟩
    obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ Wn := by
      rw [Metric.isOpen_iff] at hWn
      obtain ⟨ε, hε, hεsub⟩ := hWn y hyWn
      exact ⟨ε / 2, half_pos hε, fun z hz =>
        hεsub (closedBall_subset_ball (by linarith) hz)⟩
    have hKc : IsCompact (Wn1 ∩ G ⁻¹' closedBall y r) :=
      hprop _ hrsub (isCompact_closedBall y r)
    have himg : IsCompact (G '' (Wn1 ∩ G ⁻¹' closedBall y r)) :=
      hKc.image_of_continuousOn (hGcont.mono inter_subset_left)
    have hmem : y ∈ G '' (Wn1 ∩ G ⁻¹' closedBall y r) := by
      rw [← himg.isClosed.closure_eq, mem_closure_iff_nhds]
      intro t ht
      have htU : t ∩ ball y r ∈ 𝓝 y := Filter.inter_mem ht (ball_mem_nhds y hr)
      rw [mem_closure_iff_nhds] at hycl
      obtain ⟨z, ⟨hzt, hzb⟩, hzS⟩ := hycl (t ∩ ball y r) htU
      obtain ⟨w, hw1, rfl⟩ := hzS
      exact ⟨G w, hzt, ⟨w, ⟨hw1, ball_subset_closedBall hzb⟩, rfl⟩⟩
    exact Set.image_mono inter_subset_left hmem
  refine Set.Subset.antisymm hmaps ?_
  refine hWnc.isPreconnected.subset_of_closure_inter_subset hopen ?_ hclosed
  obtain ⟨x, hx⟩ := hW1ne
  exact ⟨G x, hmaps ⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩

/-- **The main local finiteness statement for one component `Ω`**, conditional on the sibling
statement HB1 (`Phi_component_proper`). -/
theorem component_proper_core {d : MandelDim.ParabData f₀ D₀}
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩsub : Ω ⊆ MandelDim.BuOf d B ∪ MandelDim.BlOf d B)
    (hsheet : ∀ y ∈ B, y ∉ MandelDim.critOrbit f₀ c → ∃ ρ : ℝ, 0 < ρ ∧
      IsCoveringMapOn (fun z : ↥Ω => d.φ z) (Metric.ball y ρ))
    (hPhiProp : ∀ (U' : Set ℂ), IsOpen U' → IsConnected U' → Bornology.IsBounded U' →
      ∀ z ∈ B, d.Φ z ∈ U' → ∀ L ⊆ U', IsCompact L →
        IsCompact (connectedComponentIn (B ∩ d.Φ ⁻¹' U') z ∩ d.Φ ⁻¹' L))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ} (hwΩ : w ∈ Ω)
    (hwE : d.E w ∈ Metric.ball (d.Φ c) r) :
    ∀ K ⊆ Metric.ball (d.Φ c) r, IsCompact K →
      IsCompact (connectedComponentIn (Ω ∩ d.E ⁻¹' Metric.ball (d.Φ c) r) w ∩ d.E ⁻¹' K) := by
  intro K hKU hKc
  obtain ⟨-, -, -, -, -, -, hsubDE⟩ := Work.HornTopo.horn_topo f₀ D₀ B c d hS
  have himm : MandelDim.IsImmediateBasin f₀ D₀ B := hS.2.1
  have hBopen : IsOpen B := himm.1
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := himm.2.2.1
  have hBmaps : Set.MapsTo f₀ B B := himm.2.2.2.2.1
  set U : Set ℂ := Metric.ball (d.Φ c) r with hUdef
  have hUmem : d.Φ c ∈ U := by rw [hUdef]; exact Metric.mem_ball_self hr0
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨d.Φ c, hUmem⟩
  have hUc : IsConnected U := (convex_ball (d.Φ c) r).isConnected ⟨d.Φ c, hUmem⟩
  have hUsc : SimplyConnectedSpace ↥U := by
    haveI : ContractibleSpace ↥U := by rw [hUdef]; exact Metric.contractibleSpace_ball hr0
    exact SimplyConnectedSpace.ofContractible _
  have hUb : Bornology.IsBounded U := by rw [hUdef]; exact Metric.isBounded_ball
  have hUproper : U ≠ Set.univ := by
    intro hUu
    have hmem : d.Φ c + ((r + 1 : ℝ) : ℂ) ∈ U := by
      rw [hUu]; exact Set.mem_univ _
    rw [hUdef, Metric.mem_ball, dist_eq_norm] at hmem
    have h1 : d.Φ c + ((r + 1 : ℝ) : ℂ) - d.Φ c = ((r + 1 : ℝ) : ℂ) := by ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hmem
    linarith
  -- `φ` maps `Ω` into `B`
  have hΩφB : ∀ z ∈ Ω, d.φ z ∈ B := by
    intro z hz
    rcases hΩsub hz with h | h
    · exact (connectedComponentIn_subset _ _ h).2
    · exact (connectedComponentIn_subset _ _ h).2
  have hwBtil : w ∈ MandelDim.Btil d B := by
    rcases hΩsub hwΩ with h | h
    · exact connectedComponentIn_subset _ _ h
    · exact connectedComponentIn_subset _ _ h
  have hwB : d.φ w ∈ B := hwBtil.2
  have hwU : d.Φ (d.φ w) ∈ U := by rw [hUdef]; exact hwE
  set Z : Set ℂ := connectedComponentIn (B ∩ d.Φ ⁻¹' U) (d.φ w) with hZdef
  have hwZ : d.φ w ∈ Z := mem_connectedComponentIn ⟨hwB, hwU⟩
  have hZsubB : Z ⊆ B := fun z hz => (connectedComponentIn_subset _ _ hz).1
  have hZsubU : Z ⊆ d.Φ ⁻¹' U := fun z hz => (connectedComponentIn_subset _ _ hz).2
  have hZsubBasin : Z ⊆ MandelDim.ParabolicBasin f₀ D₀ := hZsubB.trans hBsub
  have hZopen : IsOpen (B ∩ d.Φ ⁻¹' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzB, hzU⟩
    exact Filter.inter_mem (hBopen.mem_nhds hzB)
      (((d.Φ_holo.differentiableAt ((Work.HornCov.isOpen_parabolicBasin f₀ D₀).mem_nhds
        (hBsub hzB))).continuousAt).preimage_mem_nhds (hUo.mem_nhds hzU))
  have hZo : IsOpen Z := by rw [hZdef]; exact hZopen.connectedComponentIn
  have hZc : IsConnected Z := ⟨⟨d.φ w, hwZ⟩, isPreconnected_connectedComponentIn⟩
  -- `Z` avoids the critical orbit
  have hZcrit : Disjoint Z (MandelDim.critOrbit f₀ c) := by
    rw [Set.disjoint_left]
    rintro z hzZ ⟨n, hn1, rfl⟩
    have hval : d.Φ (f₀^[n] c) = d.Φ c + (n : ℂ) := Phi_iterate d hS hS.2.2.1 n
    have h1 : d.Φ (f₀^[n] c) ∈ U := hZsubU hzZ
    rw [hUdef, Metric.mem_ball, dist_eq_norm] at h1
    rw [hval, add_sub_cancel_left, Complex.norm_natCast] at h1
    have h2 : (n : ℝ) < 1 := lt_of_lt_of_le h1 (le_of_lt hr1)
    have hn0 : n = 0 := Nat.lt_one_iff.mp (by exact_mod_cast h2)
    omega
  -- critical points of `Φ` inside `Z` are exactly `c`
  have hcrit : ∀ z ∈ Z, deriv d.Φ z = 0 → z = c := by
    intro z hzZ hz0
    obtain ⟨j, hj⟩ := exists_iterate_eq_crit_of_deriv_Phi_eq_zero d hS (hZsubB hzZ) hz0
    have hval : d.Φ c = d.Φ z + (j : ℂ) := by
      rw [← hj]; exact Phi_iterate d hS (hZsubB hzZ) j
    have h1 : d.Φ z ∈ U := hZsubU hzZ
    rw [hUdef, Metric.mem_ball, dist_eq_norm] at h1
    have h3 : ‖(j : ℂ)‖ < r := by
      have heq2 : -(d.Φ z - d.Φ c) = (j : ℂ) := by rw [hval]; ring
      calc ‖(j : ℂ)‖ = ‖-(d.Φ z - d.Φ c)‖ := by rw [heq2]
        _ = ‖d.Φ z - d.Φ c‖ := norm_neg _
        _ < r := h1
    rw [Complex.norm_natCast] at h3
    have hj1 : j < 1 := by exact_mod_cast (lt_of_lt_of_le h3 (le_of_lt hr1))
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj1
    rw [hj0] at hj
    simpa using hj
  -- properness of `Φ` on `Z` (sibling HB1)
  have hprop : ∀ L ⊆ U, IsCompact L → IsCompact (Z ∩ d.Φ ⁻¹' L) := by
    intro L hLU hLc
    rw [hZdef]
    exact hPhiProp U hUo hUc hUb (d.φ w) hwB hwU L hLU hLc
  -- surjectivity of `Φ` on `Z`
  have hsurj : U ⊆ d.Φ '' Z := by
    have h := image_eq_of_isCompact_preimage (G := d.Φ)
      (D := MandelDim.ParabolicBasin f₀ D₀) (Wn := U) (Wn1 := Z)
      (Work.HornCov.isOpen_parabolicBasin f₀ D₀) d.Φ_holo hUo hUc hZo hZsubBasin
      ⟨d.φ w, hwZ⟩ (by rintro y ⟨z, hz, rfl⟩; exact hZsubU hz) hprop
    rw [h]
  -- `Z` is simply connected
  have hZsc : SimplyConnectedSpace ↥Z := by
    by_cases hex : ∃ z ∈ Z, deriv d.Φ z = 0
    · obtain ⟨z0, hz0Z, hz0c⟩ := hex
      have hz0eq : z0 = c := hcrit z0 hz0Z hz0c
      have hcZ : c ∈ Z := hz0eq ▸ hz0Z
      have hcc : deriv d.Φ c = 0 := hz0eq ▸ hz0c
      exact Work.BasinSC.StepOneCrit.simplyConnected_of_proper_holomorphic_one_crit
        hUo hUne hUsc hUproper hZo hZc (d.Φ_holo.mono hZsubBasin) (fun z hz => hZsubU hz)
        hsurj hprop hcZ hcc hcrit
    · push_neg at hex
      exact Work.BasinSC.simplyConnected_of_proper_holomorphic_no_crit hUo hUne hUsc hZo hZc
        (d.Φ_holo.mono hZsubBasin) (fun z hz => hZsubU hz) hprop hex
  -- the covering of `φ` over `Z`, and the resulting homeomorphism
  have hcov : IsCoveringMapOn (fun z : ↥Ω => d.φ z) Z := by
    intro y hy
    obtain ⟨ρ, hρ, hρcov⟩ := hsheet y (hZsubB hy)
      (fun hcon => Set.disjoint_left.mp hZcrit hy hcon)
    exact hρcov y (Metric.mem_ball_self hρ)
  have hΩDφ : Ω ⊆ d.Dφ := fun z hz => (hsubDE (hΩsub hz)).1
  have hφΩ : ContinuousOn d.φ Ω := (d.φ_holo.mono hΩDφ).continuousOn
  haveI : LocallyPathConnectedSpace ↥Z := hZo.locallyPathConnectedSpace
  haveI : SimplyConnectedSpace ↥Z := hZsc
  obtain ⟨H, hH⟩ := exists_homeomorph_connectedComponentIn_of_isCoveringMapOn hΩo hZo hcov
    hφΩ hwΩ hwZ
  -- the goal's component is the component of `Ω ∩ φ ⁻¹' Z`
  have hwC : w ∈ connectedComponentIn (Ω ∩ d.E ⁻¹' U) w :=
    mem_connectedComponentIn ⟨hwΩ, hwU⟩
  have hCsubZ : ∀ z ∈ connectedComponentIn (Ω ∩ d.E ⁻¹' U) w, d.φ z ∈ Z := by
    have hpre : IsPreconnected (d.φ '' connectedComponentIn (Ω ∩ d.E ⁻¹' U) w) :=
      isPreconnected_connectedComponentIn.image d.φ
        (hφΩ.mono ((connectedComponentIn_subset _ _).trans Set.inter_subset_left))
    have hsub : d.φ '' connectedComponentIn (Ω ∩ d.E ⁻¹' U) w ⊆ B ∩ d.Φ ⁻¹' U := by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨hΩφB z (connectedComponentIn_subset _ _ hz).1,
        (connectedComponentIn_subset _ _ hz).2⟩
    have hmain := hpre.subset_connectedComponentIn ⟨w, hwC, rfl⟩ hsub
    intro z hz
    exact hmain ⟨z, hz, rfl⟩
  have hCeq : connectedComponentIn (Ω ∩ d.E ⁻¹' U) w
      = connectedComponentIn (Ω ∩ d.φ ⁻¹' Z) w := by
    refine Set.Subset.antisymm ?_ ?_
    · exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn hwC
        (fun z hz => ⟨(connectedComponentIn_subset _ _ hz).1, hCsubZ z hz⟩)
    · exact connectedComponentIn_mono w
        (fun z hz => ⟨hz.1, hZsubU hz.2⟩)
  rw [hCeq]
  -- compactness
  set KS : Set ↥Z := Subtype.val ⁻¹' (Z ∩ d.Φ ⁻¹' K) with hKSdef
  have hKS : IsCompact KS := by
    rw [hKSdef]
    rw [Topology.IsEmbedding.isCompact_iff (f := (Subtype.val : ↥Z → ℂ))
      Topology.IsEmbedding.subtypeVal]
    convert hprop K hKU hKc using 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hz; exact ⟨⟨z, hz.1⟩, hz, rfl⟩
  have hfin : IsCompact (Subtype.val '' (H.symm '' KS)) :=
    (hKS.image H.symm.continuous).image continuous_subtype_val
  have hEq : connectedComponentIn (Ω ∩ d.φ ⁻¹' Z) w ∩ d.E ⁻¹' K
      = Subtype.val '' (H.symm '' KS) := by
    ext z
    constructor
    · rintro ⟨hzC, hzK⟩
      refine ⟨⟨z, hzC⟩, ⟨H ⟨z, hzC⟩, ?_, ?_⟩, rfl⟩
      · show ((H ⟨z, hzC⟩ : ↥Z) : ℂ) ∈ Z ∩ d.Φ ⁻¹' K
        refine ⟨(H ⟨z, hzC⟩).2, ?_⟩
        rw [hH]
        exact hzK
      · exact Homeomorph.symm_apply_apply H ⟨z, hzC⟩
    · rintro ⟨cc, hcc, rfl⟩
      obtain ⟨z', hz'KS, hz'eq⟩ := hcc
      refine ⟨cc.2, ?_⟩
      have hHz : (H cc : ↥Z) = z' := by rw [← hz'eq, Homeomorph.apply_symm_apply]
      have h3 : d.Φ (z' : ℂ) ∈ K := hz'KS.2
      have hEeq : d.E (cc : ℂ) = d.Φ (z' : ℂ) := by
        show d.Φ (d.φ (cc : ℂ)) = d.Φ (z' : ℂ)
        rw [← hH cc, hHz]
      rw [Set.mem_preimage, hEeq]
      exact h3
  rw [hEq]
  exact hfin

theorem E_component_proper_of_hPhi {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀)
    (hS : MandelDim.IsF0Setup f₀ D₀ B c)
    (hPhiProp : ∀ (U' : Set ℂ), IsOpen U' → IsConnected U' → Bornology.IsBounded U' →
      ∀ z ∈ B, d.Φ z ∈ U' → ∀ L ⊆ U', IsCompact L →
        IsCompact (connectedComponentIn (B ∩ d.Φ ⁻¹' U') z ∩ d.Φ ⁻¹' L))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ}
    (hw : w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B) (hwE : d.E w ∈ Metric.ball (d.Φ c) r) :
    ∀ K ⊆ Metric.ball (d.Φ c) r, IsCompact K →
      IsCompact (connectedComponentIn ((MandelDim.BuOf d B ∪ MandelDim.BlOf d B) ∩
        d.E ⁻¹' Metric.ball (d.Φ c) r) w ∩ d.E ⁻¹' K) := by
  intro K hKU hKc
  obtain ⟨hBuo, hBlo, -, -, -, -, -⟩ := Work.HornTopo.horn_topo f₀ D₀ B c d hS
  obtain ⟨-, -, hdisj⟩ := Work.HornSC.horn_sc Work.HornTopo.horn_topo Work.BasinSC.basin_sc
    Work.PlanarSC.planar_inter_sc f₀ D₀ B c d hS
  have hsheet_u : ∀ y ∈ B, y ∉ MandelDim.critOrbit f₀ c → ∃ ρ : ℝ, 0 < ρ ∧
      IsCoveringMapOn (fun z : ↥(MandelDim.BuOf d B) => d.φ z) (Metric.ball y ρ) := by
    intro y hyB hyc
    obtain ⟨ρ, hρ, -, h1, -⟩ := Work.HornCov.sheet_varphi Work.HornTopo.horn_topo
      Work.HornVarphi.horn_varphi (Work.HornSC.horn_sc Work.HornTopo.horn_topo
        Work.BasinSC.basin_sc Work.PlanarSC.planar_inter_sc) f₀ D₀ B c d hS y hyB hyc
    exact ⟨ρ, hρ, h1⟩
  have hsheet_l : ∀ y ∈ B, y ∉ MandelDim.critOrbit f₀ c → ∃ ρ : ℝ, 0 < ρ ∧
      IsCoveringMapOn (fun z : ↥(MandelDim.BlOf d B) => d.φ z) (Metric.ball y ρ) := by
    intro y hyB hyc
    obtain ⟨ρ, hρ, -, -, h2⟩ := Work.HornCov.sheet_varphi Work.HornTopo.horn_topo
      Work.HornVarphi.horn_varphi (Work.HornSC.horn_sc Work.HornTopo.horn_topo
        Work.BasinSC.basin_sc Work.PlanarSC.planar_inter_sc) f₀ D₀ B c d hS y hyB hyc
    exact ⟨ρ, hρ, h2⟩
  have hEBu : IsOpen (MandelDim.BuOf d B ∩ d.E ⁻¹' Metric.ball (d.Φ c) r) :=
    isOpen_inter_preimage_E hS hBuo Set.subset_union_left Metric.isOpen_ball
  have hEBl : IsOpen (MandelDim.BlOf d B ∩ d.E ⁻¹' Metric.ball (d.Φ c) r) :=
    isOpen_inter_preimage_E hS hBlo Set.subset_union_right Metric.isOpen_ball
  rcases hw with hwBu | hwBl
  · have hEq : connectedComponentIn ((MandelDim.BuOf d B ∪ MandelDim.BlOf d B) ∩
          d.E ⁻¹' Metric.ball (d.Φ c) r) w
        = connectedComponentIn (MandelDim.BuOf d B ∩ d.E ⁻¹' Metric.ball (d.Φ c) r) w :=
      connectedComponentIn_inter_eq_of_clopen hBuo hBlo hdisj (Y := MandelDim.BuOf d B ∪
        MandelDim.BlOf d B) rfl hEBu hEBl ⟨hwBu, hwE⟩
    rw [hEq]
    exact component_proper_core hS hBuo Set.subset_union_left hsheet_u hPhiProp hr0 hr1 hwBu
      hwE K hKU hKc
  · have hEq : connectedComponentIn ((MandelDim.BuOf d B ∪ MandelDim.BlOf d B) ∩
          d.E ⁻¹' Metric.ball (d.Φ c) r) w
        = connectedComponentIn (MandelDim.BlOf d B ∩ d.E ⁻¹' Metric.ball (d.Φ c) r) w :=
      connectedComponentIn_inter_eq_of_clopen hBlo hBuo hdisj.symm (Y := MandelDim.BuOf d B ∪
        MandelDim.BlOf d B) (Set.union_comm _ _) hEBl hEBu ⟨hwBl, hwE⟩
    rw [hEq]
    exact component_proper_core hS hBlo Set.subset_union_right hsheet_l hPhiProp hr0 hr1 hwBl
      hwE K hKU hKc

theorem E_component_proper {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ}
    (hw : w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B) (hwE : d.E w ∈ Metric.ball (d.Φ c) r) :
    ∀ K ⊆ Metric.ball (d.Φ c) r, IsCompact K →
      IsCompact (connectedComponentIn ((MandelDim.BuOf d B ∪ MandelDim.BlOf d B) ∩
        d.E ⁻¹' Metric.ball (d.Φ c) r) w ∩ d.E ⁻¹' K) :=
  E_component_proper_of_hPhi d hS
    (fun U' hUo hUc hUb z hzB hzU L hLU hLc =>
      Work.Horn.HB.Phi_component_proper d hS hUo hUc hUb hzB hzU L hLU hLc)
    hr0 hr1 hw hwE

end Work.Horn.HB
