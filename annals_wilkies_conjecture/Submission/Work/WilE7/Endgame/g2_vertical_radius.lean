import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical
import Submission.Work.WilE7.DimAPI.coordProj_fderiv_ker_eventually
import Submission.Work.WilE7.DimAPI.criticalLevelSetLocallyConstAt
import Submission.Work.WilE7.Endgame.g2_vertical_radius_aux

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E

/-! ## The main theorem -/

theorem g2_vertical_radius {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (himm : Work.WilE7.CoreLTSuccPlan.HImm T)
    (hvert : ∀ w ∈ T.X.set, Work.WilE7.MainDesign.projRank T w + 1 = n + (m + 1) - T.j)
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n)
    (z : Fin (0 + (n + (m + 1))) → ℝ) (hz : z ∈ T.X.set)
    (hpers : ∀ᶠ y in nhds z, y ∈ T.X.set →
      (LinearMap.ker (Work.WilE7.MainDesign.jac T y)).map
        ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
          (Work.WilE7.MainDesign.basePrLin n (m + 1))) = ⊤) :
    ∃ O ∈ nhds z, ∃ ε > 0, ∀ y ∈ T.X.set ∩ O, ∀ y' ∈ T.X.set ∩ O,
      (∀ i, Work.WilE7.MainDesign.basePrLin n (m + 1) y' (e i)
        = Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i)) →
      |Work.WilE7.CoreStep.verT y' - Work.WilE7.CoreStep.verT y| < ε →
      Work.WilE7.MainDesign.basePrLin n (m + 1) y' = Work.WilE7.MainDesign.basePrLin n (m + 1) y := by
  classical
  -- ## 0. The persistence neighbourhood of `hpers`, open and containing `z`.
  obtain ⟨Uh, _hUh_mem, hUh_sub⟩ := Filter.eventually_iff_exists_mem.mp hpers
  obtain ⟨U₀, hU₀sub, hU₀open, hzU₀⟩ := mem_nhds_iff.mp ‹Uh ∈ nhds z›
  have hpers_at : ∀ y ∈ U₀, y ∈ T.X.set →
      (LinearMap.ker (Work.WilE7.MainDesign.jac T y)).map
        ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
          (Work.WilE7.MainDesign.basePrLin n (m + 1))) = ⊤ :=
    fun y hy hyX => hUh_sub y (hU₀sub hy) hyX
  -- ## 1. The locality clause of `Good` at `z`.
  have hgood_local : ∀ᶠ y in nhds z, Work.WilE7.DimAPI.eqMap T y = 0 → y ∈ T.X.set := by
    filter_upwards [Work.WilE5.Stratum.good_local hT hz] with y hy hG
    exact hy (Subsingleton.elim _ _) (fun a => congrFun hG a)
  obtain ⟨Ug, hUgsub, hUgopen, hzUg⟩ := mem_nhds_iff.mp hgood_local
  -- ## 2. The kernel equality near every relevant point.
  have hker_ev : ∀ w ∈ T.X.set ∩ U₀, ∀ᶠ y in nhds w, y ∈ T.X.set →
      LinearMap.ker (Work.WilE7.MainDesign.jac T y) ⊓
          (Work.WilE7.MainDesign.basePrLin n (m + 1)).ker
        = LinearMap.ker (Work.WilE7.MainDesign.jac T y) ⊓
          ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
            (Work.WilE7.MainDesign.basePrLin n (m + 1))).ker := by
    intro w hw
    filter_upwards [hU₀open.mem_nhds hw.2] with y hy hyX
    exact g2_ker_basePrLin_eq T hT hvert e y hyX (hpers_at y hy hyX)
  -- ## 3. The base is locally constant along the `(e ∘ π_n)`-fibres.
  have hloc : ∀ w ∈ T.X.set ∩ U₀, ∀ᶠ y in nhds w, Work.WilE7.DimAPI.eqMap T y = 0 →
      (∀ i, Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i)
        = Work.WilE7.MainDesign.basePrLin n (m + 1) w (e i)) →
      Work.WilE7.MainDesign.basePrLin n (m + 1) y
        = Work.WilE7.MainDesign.basePrLin n (m + 1) w :=
    fun w hw => alpha_fiber_local_const T hT e w hw.1 (hpers_at w hw.2 hw.1) (hker_ev w hw)
  -- ## 4. `θ` is a local embedding at `z`.
  have hθstrict : HasStrictFDerivAt (thetaMap T e) (thetaDeriv T e z) z :=
    theta_hasStrictFDerivAt T e z
  have hbij_z : Function.Bijective (thetaDeriv T e z) :=
    thetaDeriv_bijective T hT himm hvert e z hz (hpers_at z hzU₀ hz)
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hbij_z.1
  have hQc : Q.comp (thetaDeriv T e z) = ContinuousLinearMap.id ℝ _ :=
    ContinuousLinearMap.ext fun ξ => hQ ξ
  obtain ⟨W, hWmem, rr, _hrrcont, hrr⟩ :=
    Work.WilE7.CoreStep.localEmbedding_of_injective_strictFDeriv (thetaMap T e)
      (thetaDeriv T e z) z hθstrict Q hQc
  have hinjW : ∀ a ∈ W, ∀ b ∈ W, thetaMap T e a = thetaMap T e b → a = b := by
    intro a ha b hb hab
    rw [← hrr a ha, ← hrr b hb, hab]
  -- ## 5. The source neighbourhood `O` and its `θ`-image, a ball.
  -- `O` is taken *open*, so that it is a neighbourhood of each of its points.
  set O' : Set (Fin (0 + (n + (m + 1))) → ℝ) := interior W ∩ U₀ ∩ Ug with hO'def
  have hO'open : IsOpen O' := by
    rw [hO'def]
    exact (isOpen_interior.inter hU₀open).inter hUgopen
  have hzO' : z ∈ O' := by
    rw [hO'def]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr hWmem, hzU₀⟩, hzUg⟩
  have hO'mem : O' ∈ nhds z := hO'open.mem_nhds hzO'
  have hO'sub : O' ⊆ W := fun a ha => interior_subset (by rw [hO'def] at ha; exact ha.1.1)
  have hθcont : Continuous (thetaMap T e) :=
    continuous_iff_continuousAt.mpr fun w => (theta_analyticAt T e w).continuousAt
  have himg : thetaMap T e '' O' ∈ nhds (thetaMap T e z) := by
    refine Work.WilE7.DimAPI.image_mem_nhds_of_hasStrictFDerivAt_bijective ?_ ?_ O' hO'mem
    · rwa [hθstrict.hasFDerivAt.fderiv]
    · rw [hθstrict.hasFDerivAt.fderiv]
      exact hbij_z
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp himg
  set O : Set (Fin (0 + (n + (m + 1))) → ℝ) :=
    O' ∩ (thetaMap T e) ⁻¹' Metric.ball (thetaMap T e z) ρ with hOdef
  have hOopen : IsOpen O := by
    rw [hOdef]
    exact hO'open.inter (hθcont.isOpen_preimage _ Metric.isOpen_ball)
  have hzO : z ∈ O := by
    rw [hOdef]
    exact ⟨hzO', by rw [Set.mem_preimage]; exact Metric.mem_ball_self hρpos⟩
  have hO : O ∈ nhds z := hOopen.mem_nhds hzO
  have hOball : thetaMap T e '' O = Metric.ball (thetaMap T e z) ρ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro u ⟨w, hw, rfl⟩
      exact hw.2
    · intro u hu
      obtain ⟨w, hwO', hwθ⟩ := hρsub hu
      refine ⟨w, ⟨hwO', ?_⟩, hwθ⟩
      show thetaMap T e w ∈ Metric.ball (thetaMap T e z) ρ
      rw [hwθ]
      exact hu
  have hsubO : O ⊆ O' := by rw [hOdef]; exact Set.inter_subset_left
  have hinjO : ∀ a ∈ O, ∀ b ∈ O, thetaMap T e a = thetaMap T e b → a = b :=
    fun a ha b hb hab => hinjW a (hO'sub (hsubO ha)) b (hO'sub (hsubO hb)) hab
  -- ## 6. The conclusion, with `ε = 1` (no `verT`-closeness is needed).
  refine ⟨O, hO, 1, one_pos, ?_⟩
  intro y hy y' hy' heq _hv
  obtain ⟨hyX, hyO⟩ := hy
  obtain ⟨hy'X, hy'O⟩ := hy'
  have hGy : Work.WilE7.DimAPI.eqMap T y = 0 := Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT hyX
  have hGy' : Work.WilE7.DimAPI.eqMap T y' = 0 :=
    Work.WilE7.DimAPI.eqMap_eq_zero_of_good T hT hy'X
  set c : Fin (n + (m + 1) - T.j - 1) → ℝ :=
    fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) y (e i) with hcdef
  set s : ℝ := Work.WilE7.CoreStep.verT y with hsdef
  set s' : ℝ := Work.WilE7.CoreStep.verT y' with hs'def
  -- the `θ`-values of `y` and `y'`
  have hθy : thetaMap T e y = ((0 : Fin T.j → ℝ), (c, s)) := by
    simp only [thetaMap, hGy, hcdef, hsdef]
  have hθy' : thetaMap T e y' = ((0 : Fin T.j → ℝ), (c, s')) := by
    have hc : (fun i => Work.WilE7.MainDesign.basePrLin n (m + 1) y' (e i)) = c := by
      rw [hcdef]
      exact funext heq
    simp only [thetaMap, hGy', hc, hs'def]
  -- the fibre of `θ` over `(0, c, ·)` is an interval of vertical values
  set I : Set ℝ := {t : ℝ | ((0 : Fin T.j → ℝ), (c, t)) ∈ Metric.ball (thetaMap T e z) ρ}
    with hIdef
  have hsI : s ∈ I := by
    rw [hIdef, Set.mem_setOf_eq, ← hθy]
    exact hyO.2
  have hs'I : s' ∈ I := by
    rw [hIdef, Set.mem_setOf_eq, ← hθy']
    exact hy'O.2
  have hIconv : Convex ℝ I := by
    intro t₁ ht₁ t₂ ht₂ a b ha hb hab
    have hpack : ((0 : Fin T.j → ℝ), (c, a * t₁ + b * t₂))
        = a • ((0 : Fin T.j → ℝ), (c, t₁)) + b • ((0 : Fin T.j → ℝ), (c, t₂)) := by
      have h1 : ∀ i, a * c i + b * c i = c i := by
        intro i
        have h2 : a * c i + b * c i = (a + b) * c i := by ring
        rw [h2, hab, one_mul]
      ext i <;> simp [h1]
    have hmem := (convex_ball (thetaMap T e z) ρ) ht₁ ht₂ ha hb hab
    rw [← hpack] at hmem
    simpa only [hIdef, Set.mem_setOf_eq, smul_eq_mul] using hmem
  haveI : PreconnectedSpace ↥I := Subtype.preconnectedSpace hIconv.isPreconnected
  -- the (unique) point of `O` above a fibre value
  have hw_exists : ∀ t ∈ I, ∃ w ∈ O, thetaMap T e w = ((0 : Fin T.j → ℝ), (c, t)) := by
    intro t ht
    have him : ((0 : Fin T.j → ℝ), (c, t)) ∈ thetaMap T e '' O := by
      rw [hOball]; exact ht
    obtain ⟨w, hw, hθ⟩ := him
    exact ⟨w, hw, hθ⟩
  let wt : ↥I → (Fin (0 + (n + (m + 1))) → ℝ) := fun t => Classical.choose (hw_exists t.1 t.2)
  have hwt_mem : ∀ t : ↥I, wt t ∈ O := fun t => (Classical.choose_spec (hw_exists t.1 t.2)).1
  have hwt_θ : ∀ t : ↥I, thetaMap T e (wt t) = ((0 : Fin T.j → ℝ), (c, t.1)) :=
    fun t => (Classical.choose_spec (hw_exists t.1 t.2)).2
  have hwt_Ug : ∀ t : ↥I, wt t ∈ Ug := fun t => (hsubO (hwt_mem t)).2
  have hwt_U₀ : ∀ t : ↥I, wt t ∈ U₀ := fun t => (hsubO (hwt_mem t)).1.2
  have hwt_X : ∀ t : ↥I, wt t ∈ T.X.set := by
    intro t
    have h3 : Work.WilE7.DimAPI.eqMap T (wt t) = 0 := by
      have h := congrArg Prod.fst (hwt_θ t)
      simpa [thetaMap] using h
    exact hUgsub (hwt_Ug t) h3
  have hwt_uniq : ∀ (t : ↥I) (w : Fin (0 + (n + (m + 1))) → ℝ), w ∈ O →
      thetaMap T e w = ((0 : Fin T.j → ℝ), (c, t.1)) → w = wt t := by
    intro t w hw hwθ
    exact hinjO w hw (wt t) (hwt_mem t) (by rw [hwθ, hwt_θ t])
  -- `π_n` is locally constant along the fibres of `θ` over `(0, c, ·)`
  have hlocconst : IsLocallyConstant
      (fun t : ↥I => Work.WilE7.MainDesign.basePrLin n (m + 1) (wt t)) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr ?_
    intro t
    obtain ⟨N, hNmem, hN⟩ :=
      Filter.eventually_iff_exists_mem.mp (hloc (wt t) ⟨hwt_X t, hwt_U₀ t⟩)
    have hbij : Function.Bijective (thetaDeriv T e (wt t)) :=
      thetaDeriv_bijective T hT himm hvert e (wt t) (hwt_X t)
        (hpers_at (wt t) (hwt_U₀ t) (hwt_X t))
    have hstrict : HasStrictFDerivAt (thetaMap T e) (thetaDeriv T e (wt t)) (wt t) :=
      theta_hasStrictFDerivAt T e (wt t)
    have hNmem' : N ∈ nhds (wt t) := hNmem
    have hO_mem : O ∈ nhds (wt t) := hOopen.mem_nhds (hwt_mem t)
    have hpair : N ∩ O ∈ nhds (wt t) := Filter.inter_mem hNmem' hO_mem
    have hopen : thetaMap T e '' (N ∩ O) ∈ nhds (thetaMap T e (wt t)) := by
      refine Work.WilE7.DimAPI.image_mem_nhds_of_hasStrictFDerivAt_bijective ?_ ?_ (N ∩ O) hpair
      · rwa [hstrict.hasFDerivAt.fderiv]
      · rw [hstrict.hasFDerivAt.fderiv]
        exact hbij
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hopen
    -- transfer the neighbourhood to the subtype
    have hpck_cont : Continuous (fun u : ℝ => ((0 : Fin T.j → ℝ), (c, u))) :=
      Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id)
    have hpre : Subtype.val ⁻¹'
        ((fun u : ℝ => ((0 : Fin T.j → ℝ), (c, u))) ⁻¹'
          Metric.ball (thetaMap T e (wt t)) δ) ∈ nhds t :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds <|
        hpck_cont.continuousAt.preimage_mem_nhds <| by
          rw [← hwt_θ t]
          exact Metric.ball_mem_nhds _ hδpos
    refine Filter.mem_of_superset hpre ?_
    intro t' ht'
    have ht'ball : ((0 : Fin T.j → ℝ), (c, t'.1)) ∈ Metric.ball (thetaMap T e (wt t)) δ := ht'
    have hmem : ((0 : Fin T.j → ℝ), (c, t'.1)) ∈ thetaMap T e '' (N ∩ O) := hδsub ht'ball
    obtain ⟨w'', hw'', hθ''⟩ := hmem
    have hw''eq : w'' = wt t' := hwt_uniq t' w'' hw''.2 hθ''
    have hNapp : Work.WilE7.MainDesign.basePrLin n (m + 1) w''
        = Work.WilE7.MainDesign.basePrLin n (m + 1) (wt t) := by
      refine hN w'' hw''.1 ?_ ?_
      · have h := congrArg Prod.fst hθ''
        simpa [thetaMap] using h
      · intro i
        have h21 : (fun j => Work.WilE7.MainDesign.basePrLin n (m + 1) w'' (e j)) = c := by
          have h := congrArg (fun z => z.2.1) hθ''
          simpa [thetaMap] using h
        have h21w : (fun j => Work.WilE7.MainDesign.basePrLin n (m + 1) (wt t) (e j)) = c := by
          have h := congrArg (fun z => z.2.1) (hwt_θ t)
          simpa [thetaMap] using h
        rw [congrFun h21 i, congrFun h21w i]
    rw [hw''eq] at hNapp
    exact hNapp
  -- ## 7. Assemble.
  have hEq := hlocconst.apply_eq_of_preconnectedSpace ⟨s, hsI⟩ ⟨s', hs'I⟩
  have h1 : wt ⟨s, hsI⟩ = y := (hwt_uniq ⟨s, hsI⟩ y hyO hθy).symm
  have h2 : wt ⟨s', hs'I⟩ = y' := (hwt_uniq ⟨s', hs'I⟩ y' hy'O hθy').symm
  rw [h1, h2] at hEq
  exact hEq.symm

end Work.WilE7.Endgame
