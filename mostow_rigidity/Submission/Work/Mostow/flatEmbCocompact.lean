import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspHoroDefs
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.BusemannLipschitz
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.cuspBieberbach
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.cuspHoro.packingCount
import Submission.Work.Mostow.cuspHoro.voronoiDefs
import Submission.Work.Mostow.cuspHoro.voronoiData
import Submission.Work.Mostow.cuspHoro.innerBodySeparated
import Submission.Work.Mostow.cuspHoro.existsTrivialStabilizer
import Submission.Work.Mostow.cuspHoro.horoballDisjointOfSum

/-!
# An embedded horoball forces the cusp stabiliser to act cocompactly on level one

This is the proof of `Work.Mostow.cuspHoro.flatCocompact` (in
`Submission/Work/Mostow/cuspHoro/cuspCocompactLevOne.lean`), reproduced here under the names
`properActionChartEmb` and `flatCocompactEmb` because that file, at the time of writing, cannot be
imported: one of its *transitive* imports -- `cuspHoroballsPairwise`, which is used only by a
different theorem of that file -- does not compile.  Nothing mathematical is changed; only the
import of `geomFiniteCuspCocompact` (used solely by that other theorem) is dropped.

`flatCocompactEmb`: for a lattice `Γ ≤ PO(n,1)` (`n ≥ 2`), a parabolic fixed point `ξ` and a
level `τ` such that the horoball at `ξ` of level `τ` is precisely invariant modulo `Γ`
(`hemb`), the stabiliser `Γ_ξ` acts cocompactly on the level-one horosphere at `ξ`.
-/

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Metric

open scoped ENNReal Pointwise

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **The action of a discrete subgroup of `PO n 1` on the chart is proper**: for a compact set
`K` and a point `u₀`, only finitely many `γ ∈ Γ` have `γ • u₀ ∈ K`. -/
theorem properActionChartEmb (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) (u₀ : E n) (K : Set (E n))
    (hK : IsCompact K) : {γ : Γ | (γ : PO n 1) • u₀ ∈ K}.Finite := by
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  set R : ℝ := Real.arcosh (Real.sqrt (1 + M ^ 2)) + hdist (0 : E n) u₀ with hR
  refine (finite_nearStab (hA := POBasic.ofProp hA) (hI := hI') hdisc R).subset ?_
  intro γ hγ
  have hx : ‖(γ : PO n 1) • u₀‖ ≤ M := hM _ hγ
  have h1 : hdist (0 : E n) ((γ : PO n 1) • u₀) ≤ Real.arcosh (Real.sqrt (1 + M ^ 2)) := by
    have h0 : hdist (0 : E n) ((γ : PO n 1) • u₀) = Real.arcosh (tpart ((γ : PO n 1) • u₀)) := by
      rw [hdist]; simp [tpart]
    rw [h0]
    refine (Real.arcosh_le_arcosh (tpart_pos _) (Real.sqrt_pos.2 (by nlinarith [sq_nonneg M]))).mpr ?_
    rw [tpart]
    exact Real.sqrt_le_sqrt (by nlinarith [hx, norm_nonneg ((γ : PO n 1) • u₀), sq_nonneg (M - ‖(γ : PO n 1) • u₀‖)])
  have h2 : hdist ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n)) = hdist u₀ (0 : E n) :=
    hI'.isom_smul _ _ _
  have htri := hI'.triangle (0 : E n) ((γ : PO n 1) • u₀) ((γ : PO n 1) • (0 : E n))
  rw [h2] at htri
  rw [hI'.symm u₀ 0] at htri
  show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R
  rw [hR]
  linarith


/-- **Flat cocompactness of the cusp stabiliser.** -/
theorem flatCocompactEmb (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (ξ : E n) (hξP : ξ ∈ parFixed Γ)
    (hvan : ∀ (γ : Γ) η, η ∈ parFixed Γ → bd (γ : PO n 1) η = η → bCocy (γ : PO n 1) η = 0)
    (τ : ℝ)
    (hemb : ∀ (γ : Γ), bd (γ : PO n 1) ξ ≠ ξ →
      Disjoint (horoball ξ τ) (horoball (bd (γ : PO n 1) ξ) (τ + bCocy (γ : PO n 1) ξ))) :
    ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = 1 →
      ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K := by
  classical
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  have hξ : ξ ∈ Sph n := hξP.1
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  obtain ⟨Df, hDfm, hDfin⟩ := hΓ.2
  -- the cusp stabiliser and its level preservation
  let G : Subgroup (PO n 1) := stabSub hA' Γ ξ hξ
  let hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u :=
    fun g hg u => stabSub_lev (hA := hA') (hI := hI') (hvan := hvan) (hg := hg) (hξP := hξP) u
  -- the level of the flat action and the flat action itself
  let D : ℝ := Real.exp (τ - 1)
  have hDpos : 0 < D := Real.exp_pos _
  let ρ : G →* (E (CuspB.fdim ξ) ≃ᵢ E (CuspB.fdim ξ)) := CuspB.rhoHom hA' hI ξ hξ D hDpos G hlev
  -- properness of the flat action
  have hpropΓ : ∀ u₀ : E n, lev ξ u₀ = D → ∀ K : Set (E n), IsCompact K →
      {g : G | (g : PO n 1) • u₀ ∈ K}.Finite := by
    intro u₀ _ K hK
    exact (properActionChartEmb n hA hI Γ hdisc u₀ K hK).preimage
      (f := fun g : G => (⟨(g : PO n 1), g.2.1⟩ : Γ))
      (fun a _ b _ hab => Subtype.ext (congrArg (fun z : Γ => (z : PO n 1)) hab))
  have hproper : ∀ K : Set (E (CuspB.fdim ξ)), IsCompact K →
      {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite :=
    CuspB.rhoHom_proper hA' hI ξ hξ D hDpos G hlev hpropΓ
  -- faithfulness of the flat action
  have hinj : ∀ g : G, ρ g = 1 → g = 1 := fun g => CuspB.rhoHom_ker hA' hI ξ hξ D hDpos G hlev g
  -- countability of the cusp stabiliser
  haveI : Countable Γ := (countable_of_isDiscrete (PO n 1) hdisc).to_subtype
  haveI : Countable G := Function.Injective.countable
    (f := fun g : G => (⟨(g : PO n 1), g.2.1⟩ : Γ))
    (fun a b hab => Subtype.ext (congrArg (fun z : Γ => (z : PO n 1)) hab))
  -- a base point with trivial stabiliser
  obtain ⟨x₀, hx₀⟩ := existsTrivialStabilizer (ρ := ρ) hinj
  -- the Dirichlet cell of `x₀` and the separation properties
  obtain ⟨hconv, hcover, hsep⟩ := voronoiData ρ hproper x₀ hx₀
  -- ----------------------------------------------------------------------
  -- Step 1: the injectivity radius of the orbit of `x₀`
  -- ----------------------------------------------------------------------
  have hSfin : {g : G | dist x₀ (ρ g x₀) ≤ 1}.Finite := by
    refine (hproper (Metric.closedBall x₀ 1) (isCompact_closedBall x₀ 1)).subset ?_
    intro g hg
    refine ⟨ρ g x₀, ⟨⟨x₀, Metric.mem_closedBall_self (by norm_num), rfl⟩, ?_⟩⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hg
  obtain ⟨r₀, hr₀pos, hr₀le⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ g : G, g ≠ 1 → r₀ ≤ dist x₀ (ρ g x₀) := by
    by_cases hne : (hSfin.toFinset.filter (fun g => g ≠ 1)).Nonempty
    · set T : Finset ℝ := (hSfin.toFinset.filter (fun g => g ≠ 1)).image
          (fun g => dist x₀ (ρ g x₀)) with hT
      have hTne : T.Nonempty := by rw [hT]; exact Finset.image_nonempty.mpr hne
      have hTmem : ∀ v ∈ T, ∃ g : G, g ≠ 1 ∧ v = dist x₀ (ρ g x₀) ∧
          dist x₀ (ρ g x₀) ≤ 1 := by
        intro v hv
        rw [hT, Finset.mem_image] at hv
        obtain ⟨g, hg, hgv⟩ := hv
        rw [Finset.mem_filter] at hg
        exact ⟨g, hg.2, hgv.symm, (Set.Finite.mem_toFinset hSfin).1 hg.1⟩
      refine ⟨T.min' hTne, ?_, ?_⟩
      · obtain ⟨g, hg1, hgv, -⟩ := hTmem _ (Finset.min'_mem T hTne)
        rw [hgv]
        refine lt_of_le_of_ne dist_nonneg (Ne.symm ?_)
        intro h0
        exact hx₀ g hg1 (dist_eq_zero.mp h0).symm
      · intro g hg1
        by_cases hle : dist x₀ (ρ g x₀) ≤ 1
        · have hmem : dist x₀ (ρ g x₀) ∈ T := by
            rw [hT, Finset.mem_image]
            exact ⟨g, by rw [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hle, hg1⟩, rfl⟩
          exact Finset.min'_le T _ hmem
        · obtain ⟨g', hg'1, hg'v, hg'le⟩ := hTmem _ (Finset.min'_mem T hTne)
          have h1 : T.min' hTne ≤ 1 := by rw [hg'v]; exact hg'le
          exact le_trans h1 (le_of_lt (not_le.mp hle))
    · refine ⟨1, one_pos, ?_⟩
      intro g hg1
      by_contra hlt
      exact hne ⟨g, by
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨le_of_lt (not_le.mp hlt), hg1⟩⟩
  have hr₀half : 0 < r₀ / 2 := by linarith
  have hr₀quarter : 0 < r₀ / 4 := by linarith
  -- ----------------------------------------------------------------------
  -- Step 2: the inner parallel body of the Dirichlet cell is nonempty
  -- ----------------------------------------------------------------------
  have hne_ib : (innerBody (r₀ / 2) (cell ρ x₀)).Nonempty := by
    refine ⟨x₀, fun z hz g => ?_⟩
    by_cases hg1 : g = 1
    · rw [hg1, map_one]
      exact le_refl _
    · have h1 : r₀ ≤ dist x₀ (ρ g x₀) := hr₀le g hg1
      have h2 : dist x₀ (ρ g x₀) ≤ dist z x₀ + dist z (ρ g x₀) := by
        have h := dist_triangle x₀ z (ρ g x₀)
        rwa [dist_comm x₀ z] at h
      have h3 : dist z x₀ < r₀ / 2 := by rw [dist_comm]; exact hz
      linarith
  -- ----------------------------------------------------------------------
  -- Step 3: the flat action is cocompact
  -- ----------------------------------------------------------------------
  set r : ℝ := min (1 / 2) ((1 / 2) * Real.arcosh (1 + (D * (r₀ / 2)) ^ 2 / 2)) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    refine lt_min (by norm_num) ?_
    refine mul_pos (by norm_num) ?_
    refine Real.arcosh_pos ?_
    have hDne : D * (r₀ / 2) ≠ 0 := mul_ne_zero (ne_of_gt hDpos) (by linarith)
    nlinarith [sq_pos_of_ne_zero hDne]
  have hlogD : Real.log D = τ - 1 := by
    rw [show D = Real.exp (τ - 1) from rfl, Real.log_exp]
  have hleτ : Real.log D + r ≤ τ := by
    rw [hlogD]
    have hr1 : r ≤ 1 / 2 := by rw [hrdef]; exact min_le_left _ _
    linarith
  have hsep2 : 2 * r ≤ Real.arcosh (1 + (D * (r₀ / 2)) ^ 2 / 2) := by
    have hr2 : r ≤ (1 / 2) * Real.arcosh (1 + (D * (r₀ / 2)) ^ 2 / 2) := by
      rw [hrdef]; exact min_le_right _ _
    linarith
  have hcoc : ∃ R : ℝ, ∀ x : E (CuspB.fdim ξ), ∃ g : G, dist (ρ g x) x₀ ≤ R := by
    by_contra hcon
    push Not at hcon
    have hunbdd : ¬ Bornology.IsBounded (cell ρ x₀) := by
      intro hbdd
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x₀).1 hbdd
      obtain ⟨x, hx⟩ := hcon R
      obtain ⟨g, hg⟩ := hcover x
      exact absurd (hR hg) (not_le.mpr (hx g))
    -- the packing bound for every `N`
    have hpack : ∀ N : ℕ, (N : ℝ≥0∞) * volH n (hBall (0 : E n) r) ≤ volH n Df := by
      intro N
      obtain ⟨S, hScard, hSsub, hSsep⟩ :=
        innerBodySeparated (cell ρ x₀) hconv (η := r₀ / 2) hr₀half hne_ib hunbdd
          (ε := r₀ / 4) hr₀quarter N
      have hmem : ∀ w ∈ S, w ∈ innerBody (r₀ / 4) (cell ρ x₀) := by
        intro w hw
        have h := hSsub w hw
        rwa [show r₀ / 2 / 2 = r₀ / 4 by ring] at h
      have hpc := packingCount n hA hI Γ ξ hξ hξP hvan hdisc D τ r (r₀ / 2) hDpos hrpos
        hr₀half hemb hleτ hsep2 Df hDfm hDfin (S.image (CuspB.fIso ξ)) ?_
      · rwa [Finset.card_image_of_injective S (CuspB.fIso ξ).injective, hScard] at hpc
      · intro s hs s' hs' g hne
        obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp hs
        obtain ⟨y', hyS', hy'⟩ := Finset.mem_image.mp hs'
        rw [← hy, ← hy']
        by_cases hg1 : g = 1
        · subst hg1
          have hne' : CuspB.fIso ξ y ≠ CuspB.fIso ξ y' := by
            intro h
            exact hne (by rw [← hy, ← hy', h])
          have hyy' : y ≠ y' := fun h => hne' (by rw [h])
          have hs' := hSsep y hyS y' hyS' hyy'
          have hone : cuspFlatHom hA' (HypIsoData.ofProp hI) hξ D hDpos G hlev (1 : G)
              (CuspB.fIso ξ y') = CuspB.fIso ξ y' := by
            rw [map_one]
            rfl
          rw [hone, IsometryEquiv.dist_eq]
          linarith
        · have hsep' := hsep (ε := r₀ / 4) hr₀quarter (g := g) hg1 (hmem y hyS) (hmem y' hyS')
          have hρg : cuspFlatHom hA' (HypIsoData.ofProp hI) hξ D hDpos G hlev g (CuspB.fIso ξ y')
              = CuspB.fIso ξ (ρ g y') := by
            rw [CuspB.rhoHom_apply_eq hA' hI ξ hξ D hDpos G hlev g,
              IsometryEquiv.apply_symm_apply]
            rfl
          have hkey : dist (CuspB.fIso ξ y)
              (cuspFlatHom hA' (HypIsoData.ofProp hI) hξ D hDpos G hlev g (CuspB.fIso ξ y'))
              = dist y (ρ g y') := by
            rw [hρg]
            exact IsometryEquiv.dist_eq (CuspB.fIso ξ) y (ρ g y')
          rw [hkey]
          linarith
    -- the packing bound contradicts finite volume
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, volH n Df < (N₀ : ℝ≥0∞) * volH n (hBall (0 : E n) r) := by
      by_cases hvtop : volH n (hBall (0 : E n) r) = ⊤
      · refine ⟨1, ?_⟩
        rw [hvtop]
        simpa using (lt_top_iff_ne_top.mpr hDfin : volH n Df < ⊤)
      · have hvpos : volH n (hBall (0 : E n) r) ≠ 0 :=
          (volHPosOpen n (isOpen_lt (hdist_continuous_left 0) continuous_const)
            ⟨0, by
              simp only [hBall, Set.mem_ofPred_eq]
              rw [hdist_self]
              exact hrpos⟩).ne'
        obtain ⟨N₀, hN₀⟩ := ENNReal.exists_nat_gt
          (r := volH n Df * (volH n (hBall (0 : E n) r))⁻¹)
          (ENNReal.mul_ne_top hDfin (ENNReal.inv_ne_top.mpr hvpos))
        refine ⟨N₀, ?_⟩
        have hmul := ENNReal.mul_lt_mul_left hvpos hvtop hN₀
        have hL : volH n Df * (volH n (hBall (0 : E n) r))⁻¹ * volH n (hBall (0 : E n) r)
            = volH n Df := by
          rw [mul_assoc, ENNReal.inv_mul_cancel hvpos hvtop, mul_one]
        rwa [hL] at hmul
    exact absurd (hpack N₀) (not_le.mpr hN₀)
  obtain ⟨R, hR⟩ := hcoc
  -- ----------------------------------------------------------------------
  -- Step 4: reduction to the level-one horosphere
  -- ----------------------------------------------------------------------
  set M : ℝ := R + ‖x₀‖ with hMdef
  refine ⟨Metric.closedBall (0 : E n) (M + M ^ 2 / 2), isCompact_closedBall _ _, ?_⟩
  intro u hu
  have hyc0 : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξ u
  let y : xiPerp ξ := ⟨yc ξ u, mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact hyc0)⟩
  obtain ⟨g, hg⟩ := hR ((CuspB.fIso ξ).symm y)
  refine ⟨⟨(g : PO n 1), g.2.1⟩, g.2.2, ?_⟩
  have hbC : bCocy (g : PO n 1) ξ = 0 := hvan ⟨(g : PO n 1), g.2.1⟩ ξ hξP g.2.2
  have hβ : busemann ξ ((g : PO n 1) • (0 : E n)) = 0 := by
    have h1 : busemann ξ ((g : PO n 1) • (0 : E n)) = bCocy (g : PO n 1) ξ := by
      rw [bCocy, g.2.2]
    rw [h1, hbC]
  obtain ⟨A, v, hv, hAperp, hAnorm, hpt⟩ :=
    stabFlatAction n hA hI ξ hξ (g : PO n 1) g.2.2 hβ
  have heq1 : yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) D) = A (yc ξ u) + v :=
    (hpt (yc ξ u) D hyc0 hDpos).2
  have heq2 : yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) 1) = A (yc ξ u) + v :=
    (hpt (yc ξ u) 1 hyc0 one_pos).2
  have hu_hpt : hptOf ξ (yc ξ u) 1 = u := by
    have h := hptOf_yc_lev hξ u
    rwa [hu] at h
  have hyc_eq : yc ξ ((g : PO n 1) • u) = yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) D) := by
    have h2' : yc ξ ((g : PO n 1) • u) = yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) 1) := by
      rw [hu_hpt]
    rw [h2', heq2, heq1]
  have hflat : ((flatFun hξ D (g : PO n 1) y : xiPerp ξ) : E n) = yc ξ ((g : PO n 1) • u) := by
    rw [flatFun_coe]
    show yc ξ ((g : PO n 1) • hptOf ξ (yc ξ u) D) = yc ξ ((g : PO n 1) • u)
    exact hyc_eq.symm
  have hycbound : ‖yc ξ ((g : PO n 1) • u)‖ ≤ M := by
    rw [← hflat, Submodule.norm_coe]
    have h1 : ρ g ((CuspB.fIso ξ).symm y) = (CuspB.fIso ξ).symm (flatFun hξ D (g : PO n 1) y) := by
      rw [CuspB.rhoHom_apply_eq hA' hI ξ hξ D hDpos G hlev g, IsometryEquiv.apply_symm_apply]
    have h2 : ‖ρ g ((CuspB.fIso ξ).symm y)‖ ≤ M := by
      have h3 := dist_triangle (ρ g ((CuspB.fIso ξ).symm y)) x₀ (0 : E (CuspB.fdim ξ))
      rw [dist_zero_right, dist_zero_right] at h3
      rw [hMdef]
      linarith [h3, hg]
    rwa [h1, CuspB.fIso_symm_norm] at h2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hlevg : lev ξ ((g : PO n 1) • u) = 1 := by
    rw [hlev g g.2 u, hu]
  have hptg : hptOf ξ (yc ξ ((g : PO n 1) • u)) 1 = (g : PO n 1) • u := by
    rw [← hlevg]
    exact hptOf_yc_lev hξ ((g : PO n 1) • u)
  have hξn : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  rw [← hptg]
  have hptOf_one : hptOf ξ (yc ξ ((g : PO n 1) • u)) 1
      = (‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2) • ξ + yc ξ ((g : PO n 1) • u) := by
    unfold hptOf
    have : (1 + 1 ^ 2 * ‖yc ξ ((g : PO n 1) • u)‖ ^ 2) / (2 * 1) - 1 / 2
        = ‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2 := by ring
    rw [this, one_smul]
  rw [hptOf_one]
  calc ‖(‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2) • ξ + yc ξ ((g : PO n 1) • u)‖
      ≤ ‖(‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2) • ξ‖ + ‖yc ξ ((g : PO n 1) • u)‖ :=
        norm_add_le _ _
    _ = ‖yc ξ ((g : PO n 1) • u)‖ ^ 2 / 2 + ‖yc ξ ((g : PO n 1) • u)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), hξn, mul_one]
    _ ≤ M + M ^ 2 / 2 := by
        have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hycbound
        nlinarith [hycbound, norm_nonneg (yc ξ ((g : PO n 1) • u)), hM0,
          sq_nonneg (M - ‖yc ξ ((g : PO n 1) • u)‖),
          mul_nonneg (sub_nonneg.mpr hycbound)
            (add_nonneg hM0 (norm_nonneg (yc ξ ((g : PO n 1) • u))))]

end

end Work.Mostow.cuspHoro
