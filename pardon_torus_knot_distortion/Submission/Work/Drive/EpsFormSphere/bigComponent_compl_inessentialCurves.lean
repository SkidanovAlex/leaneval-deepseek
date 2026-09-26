import Mathlib
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.BoxShrink.PinchOff.IB.Main
import Submission.Work.BoxShrink.PinchOff.IB.Separator
import Submission.Work.BoxShrink.PinchOff.IB.Span
import Submission.Work.BoxShrink.PinchOff.IB.Pieces
import Submission.Work.BoxShrink.PinchOff.IB.existsUnique_top_of_partition
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-!
# The big component of the complement of inessential curves of a torus

Let `γ i` (`i : Fin n`) be pairwise disjoint *simple* closed curves of a parametrised torus `P`,
each of them *inessential* (winding vector zero).  This file constructs the "big piece" of the
complement `C = P.carrier \ ⋃ i, range (γ i).γ`: the projection of the *unbounded* connected
component of the lifted complement in the parameter plane `ℂ`.

The three properties proved are

* the big piece `K` is preconnected (it is the image under the projection `planePsi P` of a
  connected component) and lies in the complement `C` of the curves;
* `WindingSpan P K = ⊤`: the lifted component is invariant under the period lattice (the
  uniqueness of the unbounded component of the complement of the lifted curves,
  `Work.BoxShrink.PinchOff.unbounded_component_unique`), hence path connected, and the paths
  joining `z` to `z + periodPt 1 0` and to `z + periodPt 0 1` straighten out into loops of the
  torus of winding `(1, 0)` and `(0, 1)` inside `K`
  (`Work.BoxShrink.PinchOff.exists_closedCurve_of_path`);
* every preconnected piece of the complement disjoint from `K` has vanishing winding span: an
  essential loop of the complement would lift to a curve whose values lie in the complement of the
  lifted curves, and whose image is *unbounded* (the lift advances by a nonzero lattice vector over
  each period); hence its lifted image lies in the unbounded component, i.e. in the preimage of
  `K`.

The existence of the unbounded component uses the peel-off computation
`Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential` (removing the
curves does not change the winding span of the carrier, which is `⊤`) together with
`Work.BoxShrink.PinchOff.IB.exists_unbounded_component_of_windingSpan_eq_top`.
-/

/-- The union of the images of finitely many closed curves of a parametrised torus is closed. -/
theorem isClosed_iUnion_range_closedCurve {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    (γ : Fin n → Work.CoreTopology.ClosedCurve P) :
    IsClosed (⋃ i, Set.range (γ i).γ) := by
  have h : (⋃ i ∈ (Finset.univ : Finset (Fin n)), Set.range (γ i).γ)
      = ⋃ i, Set.range (γ i).γ := by
    ext x
    simp
  rw [← h]
  exact (Work.BoxShrink.PinchOff.isCompact_iUnion_range_closedCurve γ Finset.univ).isClosed

/-- The preimage in the parameter plane of the complement of the curves is the complement of the
preimage of the curves. -/
theorem Xtilde_sdiff_iUnion_range {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    (γ : Fin n → Work.CoreTopology.ClosedCurve P) :
    Work.BoxShrink.PinchOff.Xtilde P (P.carrier \ ⋃ i, Set.range (γ i).γ)
      = (Work.BoxShrink.PinchOff.Xtilde P (⋃ i, Set.range (γ i).γ))ᶜ := by
  ext z
  rw [Work.BoxShrink.PinchOff.mem_Xtilde, Set.mem_sdiff, Set.mem_compl_iff,
    Work.BoxShrink.PinchOff.mem_Xtilde]
  constructor
  · rintro ⟨-, hz⟩
    exact hz
  · intro hz
    exact ⟨Work.BoxShrink.PinchOff.planePsi_mem_carrier P z, hz⟩

open LeanEval.KnotTheory.PardonDistortion in
/-- **The big component of the complement of a finite family of disjoint inessential curves in a
torus.**  If `γ i` are pairwise disjoint simple closed curves of `P`, each inessential in `P`, then
the complement `P.carrier \ ⋃ i, range (γ i)` has a *preconnected* piece `K` carrying the whole of
`H₁(P;ℚ)` (winding span `⊤`), and every preconnected piece of the complement disjoint from `K` has
vanishing winding span. -/
theorem bigComponent_compl_inessentialCurves {P : Work.CoreTopology.ParamTorus}
    {n : ℕ} (γ : Fin n → Work.CoreTopology.ClosedCurve P)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) :
    ∃ K : Set LeanEval.KnotTheory.PardonDistortion.R3, IsPreconnected K ∧
      K ⊆ P.carrier \ ⋃ i, Set.range (γ i).γ ∧
      Work.SurgeryInvariance.WindingSpan P K = ⊤ ∧
      ∀ L : Set LeanEval.KnotTheory.PardonDistortion.R3, IsPreconnected L →
        L ⊆ P.carrier \ ⋃ i, Set.range (γ i).γ →
        Disjoint L K → Work.SurgeryInvariance.WindingSpan P L = ⊥ := by
  classical
  set A : Set R3 := ⋃ i, Set.range (γ i).γ with hA
  set C : Set R3 := P.carrier \ A with hC
  have hcarrierOpen : Work.SurgeryInvariance.IsOpenInCarrier P P.carrier := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier]
    have h : (Subtype.val ⁻¹' P.carrier : Set P.carrier) = Set.univ := by ext x; simp
    rw [h]
    exact isOpen_univ
  have hAclosed : IsClosed A := by rw [hA]; exact isClosed_iUnion_range_closedCurve γ
  have hCsub : C ⊆ P.carrier := by rw [hC]; exact Set.sdiff_subset
  have hopenC : Work.SurgeryInvariance.IsOpenInCarrier P C := by
    rw [hC]
    exact Work.BoxShrink.PinchOff.isOpenInCarrier_sdiff_of_isClosed hcarrierOpen hAclosed
  -- peeling the curves out of the whole carrier shows that the complement spans everything
  have hWSC : Work.SurgeryInvariance.WindingSpan P C = ⊤ := by
    have hpeel := Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
      (P := P) (X := P.carrier) (γ := γ) hcarrierOpen hsimple hess hdisj
      (fun i t => (γ i).mem t)
    have hC' : C = P.carrier \ ⋃ i, Set.range (γ i).γ := by rw [hC, hA]
    rw [hC', ← hpeel]
    exact Work.SurgeryInvariance.WindingSpan.carrier_eq_top P
  -- the lifted complement, and the lifted curves
  set T : Set ℂ := Work.BoxShrink.PinchOff.Xtilde P C with hT
  set Z : Set ℂ := Work.BoxShrink.PinchOff.Xtilde P A with hZ
  have hZeq : Z = Work.BoxShrink.PinchOff.Xtilde P (⋃ i, Set.range (γ i).γ) := by rw [hZ, hA]
  have hTZ : T = Zᶜ := by rw [hT, hZ, hA]; exact Xtilde_sdiff_iUnion_range γ
  have hZclosed : IsClosed Z := by
    rw [hZeq]
    exact hAclosed.preimage (Work.BoxShrink.PinchOff.continuous_planePsi P)
  have hZcomp : ∀ z ∈ Z, IsCompact (connectedComponentIn Z z) := by
    intro z hz
    rw [hZeq] at hz ⊢
    exact Work.BoxShrink.PinchOff.components_compact hsimple hess hdisj z hz
  have hTinv : ∀ z w : ℂ, w ∈ Work.BoxShrink.PinchOff.periodLattice →
      (z + w ∈ T ↔ z ∈ T) :=
    fun z w hw => Work.BoxShrink.PinchOff.Xtilde_add_periodLattice P C z w hw
  have hcomp_eq : ∀ z : ℂ, connectedComponentIn T z = connectedComponentIn Zᶜ z := by
    intro z
    rw [hTZ]
  -- the unbounded component of the lifted complement
  obtain ⟨z₀, hz₀T, hunb⟩ :=
    Work.BoxShrink.PinchOff.IB.exists_unbounded_component_of_windingSpan_eq_top hCsub hopenC hWSC
  set U : Set ℂ := connectedComponentIn T z₀ with hU
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀T
  have hUsubT : U ⊆ T := connectedComponentIn_subset T z₀
  have hUopen : IsOpen U :=
    (Work.BoxShrink.PinchOff.isOpen_Xtilde hCsub hopenC).connectedComponentIn
  have hz₀Z : z₀ ∉ Z := by
    have h1 : z₀ ∈ T := hz₀T
    rw [hTZ] at h1
    exact h1
  -- the unbounded component is invariant under the period lattice
  have hUinv : ∀ w ∈ Work.BoxShrink.PinchOff.periodLattice,
      (fun y : ℂ => y + w) '' U = U := by
    intro w hw
    have hzwT : z₀ + w ∈ T := (hTinv z₀ w hw).mpr hz₀T
    have hcompw : connectedComponentIn T (z₀ + w) = (fun y : ℂ => y + w) '' U :=
      Work.BoxShrink.PinchOff.connectedComponentIn_add hTinv hw hz₀T
    have hzwZ : z₀ + w ∉ Z := by
      have h1 : z₀ + w ∈ T := hzwT
      rw [hTZ] at h1
      exact h1
    have hb1 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Zᶜ z₀, R ≤ ‖y‖ := by
      intro R
      obtain ⟨y, hy, hR⟩ := hunb R
      refine ⟨y, ?_, hR⟩
      rw [← hcomp_eq z₀]
      exact hy
    have hb2 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Zᶜ (z₀ + w), R ≤ ‖y‖ := by
      intro R
      obtain ⟨y, hy, hR⟩ := hunb (R + ‖w‖)
      refine ⟨y + w, ?_, ?_⟩
      · have hmemT : y + w ∈ connectedComponentIn T (z₀ + w) := by
          rw [hcompw]
          exact ⟨y, hy, rfl⟩
        rwa [hcomp_eq (z₀ + w)] at hmemT
      · have h1 : ‖y‖ ≤ ‖y + w‖ + ‖w‖ := by
          calc ‖y‖ = ‖(y + w) - w‖ := by ring_nf
            _ ≤ ‖y + w‖ + ‖w‖ := norm_sub_le _ _
        linarith
    have heq : connectedComponentIn Zᶜ z₀ = connectedComponentIn Zᶜ (z₀ + w) :=
      Work.BoxShrink.PinchOff.unbounded_component_unique hZclosed hZcomp hz₀Z hzwZ hb1 hb2
    have heqT : connectedComponentIn T (z₀ + w) = connectedComponentIn T z₀ := by
      rw [hcomp_eq (z₀ + w), hcomp_eq z₀]
      exact heq.symm
    exact hcompw.symm.trans heqT
  -- the big piece
  set K : Set R3 := Work.BoxShrink.PinchOff.planePsi P '' U with hK
  have hKpre : IsPreconnected K :=
    isPreconnected_connectedComponentIn.image _
      (Work.BoxShrink.PinchOff.continuous_planePsi P).continuousOn
  have hKsub : K ⊆ P.carrier \ ⋃ i, Set.range (γ i).γ := by
    rintro y ⟨z, hz, rfl⟩
    have hzC : Work.BoxShrink.PinchOff.planePsi P z ∈ C := hUsubT hz
    rw [hC, hA] at hzC
    exact hzC
  -- the big piece carries the whole of `H₁`
  have hUpc : ∀ a ∈ U, ∀ b ∈ U, JoinedIn U a b := by
    haveI : LocallyPathConnectedSpace ↥U := hUopen.locallyPathConnectedSpace
    haveI : PreconnectedSpace ↥U :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
    intro a ha b hb
    rw [joinedIn_iff_joined ha hb, ← connectedComponent_eq_iff_joined,
      PreconnectedSpace.connectedComponent_eq_univ, PreconnectedSpace.connectedComponent_eq_univ]
  have hloop : ∀ a b : ℤ, ∃ γ' : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ'.γ t ∈ K) ∧ Work.SurgeryInvariance.windingOf P γ' = (a, b) := by
    intro a b
    have hνmem : Work.BoxShrink.PinchOff.periodPt a b ∈ Work.BoxShrink.PinchOff.periodLattice :=
      ⟨(a, b), rfl⟩
    have hmem : z₀ + Work.BoxShrink.PinchOff.periodPt a b ∈ U := by
      have h := hUinv _ hνmem
      rw [← h]
      exact ⟨z₀, hz₀U, rfl⟩
    obtain ⟨p, hp⟩ := hUpc z₀ hz₀U (z₀ + Work.BoxShrink.PinchOff.periodPt a b) hmem
    set c : ℝ → ℂ := fun t => p.extend (t / (2 * Real.pi)) with hc
    have hc0 : c 0 = z₀ := by
      change p.extend ((0 : ℝ) / (2 * Real.pi)) = z₀
      rw [zero_div]
      exact Path.extend_zero p
    have hc2 : c (2 * Real.pi) = z₀ + Work.BoxShrink.PinchOff.periodPt a b := by
      change p.extend ((2 * Real.pi) / (2 * Real.pi)) = z₀ + Work.BoxShrink.PinchOff.periodPt a b
      rw [show (2 * Real.pi) / (2 * Real.pi) = 1 by field_simp, Path.extend_one]
    have hcmem : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        c t ∈ Work.BoxShrink.PinchOff.Xtilde P K := by
      intro t ht
      have ht1 : t / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg ht.1 (by positivity)
        · rw [div_le_one (by positivity)]; exact ht.2
      change p.extend (t / (2 * Real.pi)) ∈ Work.BoxShrink.PinchOff.Xtilde P K
      rw [Path.extend_apply p ht1]
      exact ⟨p ⟨t / (2 * Real.pi), ht1⟩, hp ⟨t / (2 * Real.pi), ht1⟩, rfl⟩
    exact Work.BoxShrink.PinchOff.exists_closedCurve_of_path c
      (p.extend.continuous.comp (continuous_id.div_const _)) hc0 hc2 hcmem
  have hKtop : Work.SurgeryInvariance.WindingSpan P K = ⊤ := by
    have h1mem : (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) ∈ Work.SurgeryInvariance.WindingSpan P K := by
      obtain ⟨γ', hγ', hw⟩ := hloop 1 0
      refine Submodule.subset_span ⟨γ', hγ', ?_⟩
      rw [hw]
      norm_num
    have h2mem : (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) ∈ Work.SurgeryInvariance.WindingSpan P K := by
      obtain ⟨γ', hγ', hw⟩ := hloop 0 1
      refine Submodule.subset_span ⟨γ', hγ', ?_⟩
      rw [hw]
      norm_num
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = v.1 • (((1 : ℚ), (0 : ℚ)) : ℚ × ℚ) +
        v.2 • (((0 : ℚ), (1 : ℚ)) : ℚ × ℚ) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1mem) (Submodule.smul_mem _ _ h2mem)
  refine ⟨K, hKpre, hKsub, hKtop, ?_⟩
  -- every preconnected piece of the complement disjoint from the big piece is inessential
  intro M _ hMsub hMdisj
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ', hess', hγ'mem⟩
  have hγ'C : ∀ t : ℝ, γ'.γ t ∈ C := by
    intro t
    have h := hMsub (hγ'mem t)
    rw [hC, hA]
    exact h
  have hγ'T : ∀ t : ℝ, γ'.γ t ∈ P.carrier \ ⋃ i, Set.range (γ i).γ := fun t => hMsub (hγ'mem t)
  set LL : Work.CoreTopology.LiftOf P γ' :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ') with hLL
  have hLmemT : ∀ t : ℝ, Work.BoxShrink.PinchOff.liftMap LL t ∈ T := by
    intro t
    have : Work.BoxShrink.PinchOff.planePsi P (Work.BoxShrink.PinchOff.liftMap LL t) ∈ C := by
      rw [Work.BoxShrink.PinchOff.planePsi_liftMap]
      exact hγ'C t
    exact this
  have hVrange : Set.range (Work.BoxShrink.PinchOff.liftMap LL) ⊆ T :=
    fun y ⟨t, ht⟩ => ht ▸ hLmemT t
  have hVpre : IsPreconnected (Set.range (Work.BoxShrink.PinchOff.liftMap LL)) := by
    have h := isPreconnected_univ.image (Work.BoxShrink.PinchOff.liftMap LL)
      (Work.BoxShrink.PinchOff.continuous_liftMap LL).continuousOn
    rwa [Set.image_univ] at h
  have hVsub : Set.range (Work.BoxShrink.PinchOff.liftMap LL) ⊆
      connectedComponentIn T (Work.BoxShrink.PinchOff.liftMap LL 0) :=
    hVpre.subset_connectedComponentIn ⟨0, rfl⟩ hVrange
  -- the lift advances by a nonzero lattice vector over each period, so its image is unbounded
  have hwne : LL.winding ≠ (0, 0) := Work.CoreTopology.IsEssential.winding_ne hess' LL
  have hshift : ∀ t : ℝ, Work.BoxShrink.PinchOff.liftMap LL (t + 2 * Real.pi)
      = Work.BoxShrink.PinchOff.liftMap LL t
        + Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2 := by
    intro t
    have hspec := LL.period_shift_winding t
    have h1 : LL.Θ (t + 2 * Real.pi) = LL.Θ t + (LL.winding).1 * (2 * Real.pi) := hspec.1
    have h2 : LL.Φ (t + 2 * Real.pi) = LL.Φ t + (LL.winding).2 * (2 * Real.pi) := hspec.2
    apply Complex.ext <;>
      simp [Work.BoxShrink.PinchOff.liftMap, h1, h2, Work.BoxShrink.PinchOff.periodPt]
  have hshiftN : ∀ m : ℕ,
      Work.BoxShrink.PinchOff.liftMap LL ((m : ℝ) * (2 * Real.pi))
        = Work.BoxShrink.PinchOff.liftMap LL 0
          + (m : ℂ) * Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hmul : ((m + 1 : ℕ) : ℝ) * (2 * Real.pi)
          = (m : ℝ) * (2 * Real.pi) + 2 * Real.pi := by push_cast; ring
      rw [hmul, hshift, ih]
      push_cast
      ring
  have hunbV : ∀ R : ℝ, ∃ y ∈ connectedComponentIn T
      (Work.BoxShrink.PinchOff.liftMap LL 0), R ≤ ‖y‖ := by
    have hν : Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2 ≠ 0 :=
      Work.BoxShrink.PinchOff.periodPt_ne_zero hwne
    have hνpos : (0 : ℝ) < ‖Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2‖ :=
      norm_pos_iff.mpr hν
    intro R
    obtain ⟨m, hm⟩ := exists_nat_gt ((R + ‖Work.BoxShrink.PinchOff.liftMap LL 0‖) /
      ‖Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2‖)
    refine ⟨Work.BoxShrink.PinchOff.liftMap LL ((m : ℝ) * (2 * Real.pi)),
      hVsub ⟨_, rfl⟩, ?_⟩
    rw [hshiftN m]
    have h1 : ‖(m : ℂ) * Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2‖ ≤
        ‖Work.BoxShrink.PinchOff.liftMap LL 0
          + (m : ℂ) * Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2‖
          + ‖Work.BoxShrink.PinchOff.liftMap LL 0‖ := by
      calc ‖(m : ℂ) * Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2‖
          = ‖(Work.BoxShrink.PinchOff.liftMap LL 0
              + (m : ℂ) * Work.BoxShrink.PinchOff.periodPt LL.winding.1 LL.winding.2)
              - Work.BoxShrink.PinchOff.liftMap LL 0‖ := by ring_nf
        _ ≤ _ + _ := norm_sub_le _ _
    rw [norm_mul, Complex.norm_natCast] at h1
    rw [div_lt_iff₀ hνpos] at hm
    linarith
  -- hence the component of the lift is the unbounded component of the lifted complement
  have hVeqU : connectedComponentIn T (Work.BoxShrink.PinchOff.liftMap LL 0) = U := by
    have hx : Work.BoxShrink.PinchOff.liftMap LL 0 ∉ Z := by
      have h1 : Work.BoxShrink.PinchOff.liftMap LL 0 ∈ T := hLmemT 0
      rw [hTZ] at h1
      exact h1
    have hb1 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Zᶜ
        (Work.BoxShrink.PinchOff.liftMap LL 0), R ≤ ‖y‖ := by
      intro R
      obtain ⟨y, hy, hR⟩ := hunbV R
      exact ⟨y, by rw [hcomp_eq (Work.BoxShrink.PinchOff.liftMap LL 0)] at hy; exact hy, hR⟩
    have hb2 : ∀ R : ℝ, ∃ y ∈ connectedComponentIn Zᶜ z₀, R ≤ ‖y‖ := by
      intro R
      obtain ⟨y, hy, hR⟩ := hunb R
      refine ⟨y, ?_, hR⟩
      rw [← hcomp_eq z₀]
      exact hy
    have heq := Work.BoxShrink.PinchOff.unbounded_component_unique hZclosed hZcomp hx hz₀Z hb1 hb2
    rw [← hcomp_eq (Work.BoxShrink.PinchOff.liftMap LL 0), ← hcomp_eq z₀] at heq
    exact heq
  have hrangeK : Set.range γ'.γ ⊆ K := by
    rintro y ⟨t, rfl⟩
    have hmemU : Work.BoxShrink.PinchOff.liftMap LL t ∈ U := by
      rw [← hVeqU]
      exact hVsub ⟨t, rfl⟩
    exact ⟨Work.BoxShrink.PinchOff.liftMap LL t, hmemU,
      Work.BoxShrink.PinchOff.planePsi_liftMap LL t⟩
  exact (Set.disjoint_left.mp hMdisj) (hγ'mem 0) (hrangeK ⟨0, rfl⟩)

end

end Work.Drive.EpsFormSphere
