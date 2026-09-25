import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.contDiffOn_glue
import Submission.Work.NN.Final.dilation_expansion
import Submission.Work.NN.Final.eta
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Final.existsFiniteMomentData
import Submission.Work.NN.Final.etaCompMoment
import Submission.Work.NN.Final.holderDerivTendsto

noncomputable section
open Set Filter
open scoped ContDiff Topology
open Metric

namespace Work.NN.Final

/-- **Gluing of `C^m` functions across a hyperplane, localised to an open set `V`.**

This is the localised version of `Work.NN.Final.contDiffOn_glue`: instead of the global slabs
`{-δ < p.2}`, `{-δ < p.2 ∧ p.2 < 0}`, `{0 < p.2}` one uses the intersections of an arbitrary open
set `V` with the same half spaces.  The proof is the proof of `contDiffOn_glue` restricted to a
ball around each boundary point. -/
theorem contDiffOn_glue_open {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} {F : X × ℝ → Y} {V : Set (X × ℝ)} (hV : IsOpen V)
    (hc : ContinuousOn F V)
    (hN : ContDiffOn ℝ m F (V ∩ {p : X × ℝ | p.2 < 0}))
    (hH : ContDiffOn ℝ m F (V ∩ {p : X × ℝ | 0 < p.2}))
    (hlim : ∀ i ≤ m, ∀ p ∈ V, p.2 = 0 →
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) Y,
        Filter.Tendsto (fun q : X × ℝ => iteratedFDeriv ℝ i F q)
          (𝓝[V ∩ {q : X × ℝ | q.2 ≠ 0}] p) (𝓝 L)) :
    ContDiffOn ℝ m F V := by
  classical
  have hsH : IsOpen {z : X × ℝ | (0 : ℝ) < z.2} := isOpen_lt continuous_const continuous_snd
  have hsm : IsOpen {z : X × ℝ | z.2 < (0 : ℝ)} := isOpen_lt continuous_snd continuous_const
  have hVp : IsOpen (V ∩ {z : X × ℝ | (0 : ℝ) < z.2}) := hV.inter hsH
  have hVm : IsOpen (V ∩ {z : X × ℝ | z.2 < (0 : ℝ)}) := hV.inter hsm
  -- the candidate Taylor series
  let P : (X × ℝ) → FormalMultilinearSeries ℝ (X × ℝ) Y := fun y k =>
    match k with
    | 0 => iteratedFDeriv ℝ 0 F y
    | (n+1) => if hy : y ∈ V ∧ y.2 = 0 then
        (if hk : n+1 ≤ m then Classical.choose (hlim (n+1) hk y hy.1 hy.2)
         else iteratedFDeriv ℝ (n+1) F y)
      else iteratedFDeriv ℝ (n+1) F y
  have hP_ne : ∀ (y : X × ℝ) (k : ℕ), y.2 ≠ 0 → P y k = iteratedFDeriv ℝ k F y := by
    intro y k hy
    cases k with
    | zero => rfl
    | succ n => simp only [P]; rw [dite_eq_right]; rintro ⟨-, h2⟩; exact hy h2
  have hP_lim : ∀ (y : X × ℝ) (k : ℕ) (h1 : y ∈ V) (h2 : y.2 = 0) (hk : k ≤ m) (hk0 : 0 < k),
      P y k = Classical.choose (hlim k hk y h1 h2) := by
    intro y k h1 h2 hk hk0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk0)
    simp only [P]; rw [dite_eq_left (show y ∈ V ∧ y.2 = 0 from ⟨h1, h2⟩), dite_eq_left hk]
  have hcurl : ∀ (k : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => X × ℝ) Y),
      L.curryLeft = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X × ℝ) Y) L :=
    fun k L => rfl
  have hkey : ∀ (q : X × ℝ) (r : ℝ), 0 < r → (ball q r ⊆ V) →
      HasFTaylorSeriesUpToOn m F P (ball q r) := by
    intro q r hr hsub
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      change (iteratedFDeriv ℝ 0 F y).curry0 = F y
      simp
    · intro k hk y hy
      have hkm : k < m := by exact_mod_cast hk
      have hk1 : k + 1 ≤ m := hkm
      by_cases hy0 : y.2 = 0
      · -- on the hyperplane
        obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hy)
        set ρ : ℝ := min (ε₁ / 2) 1 with hρdef
        have hρpos : 0 < ρ := lt_min (by linarith) (by norm_num)
        have hρle₁ : ρ < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        -- any point of the closed ball around `y` of radius `ρ` lies in `V`
        have hballV : ∀ z : X × ℝ, dist z y ≤ ρ → z ∈ V := fun z hz =>
          hsub (hε₁' (mem_ball.mpr (lt_of_le_of_lt hz hρle₁)))
        have hyV : y ∈ V := hsub hy
        set Bp : Set (X × ℝ) := ball y ρ ∩ {z : X × ℝ | (0 : ℝ) < z.2} with hBp
        set Bm : Set (X × ℝ) := ball y ρ ∩ {z : X × ℝ | z.2 < (0 : ℝ)} with hBm
        have hBp_open : IsOpen Bp := isOpen_ball.inter hsH
        have hBm_open : IsOpen Bm := isOpen_ball.inter hsm
        have hBp_conv : Convex ℝ Bp := (convex_ball y ρ).inter convex_snd_pos
        have hBm_conv : Convex ℝ Bm := (convex_ball y ρ).inter convex_snd_neg
        have hBp_sub : Bp ⊆ V ∩ {z : X × ℝ | z.2 ≠ 0} := by
          intro z hz
          exact ⟨hballV z (le_of_lt (mem_ball.mp hz.1)), ne_of_gt hz.2⟩
        have hBm_sub : Bm ⊆ V ∩ {z : X × ℝ | z.2 ≠ 0} := by
          intro z hz
          exact ⟨hballV z (le_of_lt (mem_ball.mp hz.1)), ne_of_lt hz.2⟩
        -- all points in the closures of `Bp` and `Bm` lie in `V`
        have hclVp : ∀ z ∈ closure Bp, z ∈ V := by
          intro z hz
          refine hballV z ?_
          have h1 : z ∈ closure (ball y ρ) := closure_mono inter_subset_left hz
          rw [← mem_closedBall, ← closure_ball y (ne_of_gt hρpos)]
          exact h1
        have hclVm : ∀ z ∈ closure Bm, z ∈ V := by
          intro z hz
          refine hballV z ?_
          have h1 : z ∈ closure (ball y ρ) := closure_mono inter_subset_left hz
          rw [← mem_closedBall, ← closure_ball y (ne_of_gt hρpos)]
          exact h1
        have hbp_ge : ∀ z ∈ closure Bp, 0 ≤ z.2 := by
          intro z hz
          rw [hBp] at hz
          have h2 : z ∈ closure {w : X × ℝ | (0 : ℝ) < w.2} :=
            closure_mono inter_subset_right hz
          have hsub'' : {w : X × ℝ | (0 : ℝ) < w.2} ⊆ {w : X × ℝ | (0 : ℝ) ≤ w.2} :=
            fun w hw => Set.mem_ofPred_eq.mpr (le_of_lt (Set.mem_ofPred_eq.mp hw))
          exact (closure_minimal hsub'' (isClosed_le continuous_const continuous_snd)) h2
        have hbm_le : ∀ z ∈ closure Bm, z.2 ≤ 0 := by
          intro z hz
          rw [hBm] at hz
          have h2 : z ∈ closure {w : X × ℝ | w.2 < (0 : ℝ)} :=
            closure_mono inter_subset_right hz
          have hsub'' : {w : X × ℝ | w.2 < (0 : ℝ)} ⊆ {w : X × ℝ | w.2 ≤ (0 : ℝ)} :=
            fun w hw => Set.mem_ofPred_eq.mpr (le_of_lt (Set.mem_ofPred_eq.mp hw))
          exact (closure_minimal hsub'' (isClosed_le continuous_snd continuous_const)) h2
        have hdiffp : DifferentiableOn ℝ (fun z => P z k) Bp := by
          intro z hz
          have hz2 : 0 < z.2 := hz.2
          have hzV : z ∈ V := hballV z (le_of_lt (mem_ball.mp hz.1))
          have hev2 : (fun w => P w k) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsH.mem_nhds hz2) (fun w hw => hP_ne w k (ne_of_gt hw))
          have hcd : ContDiffAt ℝ m F z :=
            (hH z ⟨hzV, hz2⟩).contDiffAt (hVp.mem_nhds ⟨hzV, hz2⟩)
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
            (hcd.iteratedFDeriv_right (m := 1)
              (by exact_mod_cast (by omega : 1 + k ≤ m))).differentiableAt (by norm_num)
          exact (hdiffit.congr_of_eventuallyEq hev2).differentiableWithinAt
        have hdiffm : DifferentiableOn ℝ (fun z => P z k) Bm := by
          intro z hz
          have hz2 : z.2 < 0 := hz.2
          have hzV : z ∈ V := hballV z (le_of_lt (mem_ball.mp hz.1))
          have hev2 : (fun w => P w k) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsm.mem_nhds hz2) (fun w hw => hP_ne w k (ne_of_lt hw))
          have hcd : ContDiffAt ℝ m F z :=
            (hN z ⟨hzV, hz2⟩).contDiffAt (hVm.mem_nhds ⟨hzV, hz2⟩)
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
            (hcd.iteratedFDeriv_right (m := 1)
              (by exact_mod_cast (by omega : 1 + k ≤ m))).differentiableAt (by norm_num)
          exact (hdiffit.congr_of_eventuallyEq hev2).differentiableWithinAt
        have hcontp : ∀ z ∈ closure Bp, ContinuousWithinAt (fun w => P w k) Bp z := by
          intro z hz
          have hzge : 0 ≤ z.2 := hbp_ge z hz
          have hzV : z ∈ V := hclVp z hz
          have hpe : (fun w => P w k) =ᶠ[𝓝[Bp] z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun w hw => hP_ne w k (ne_of_gt hw.2))
          by_cases hz0 : z.2 = 0
          · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ 0 F w) z := by
                have hFc : ContinuousAt F z := hc.continuousAt (hV.mem_nhds hzV)
                have hfun : (fun w => iteratedFDeriv ℝ 0 F w) =
                    (fun w => (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm (F w)) := by
                  funext w; rw [iteratedFDeriv_zero_eq_comp]; rfl
                rw [hfun]
                exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm.continuous.continuousAt.comp
                  hFc
              exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
            · show Tendsto (fun w => P w k) (𝓝[Bp] z) (𝓝 (P z k))
              rw [hP_lim z k hzV hz0 hkm.le hkpos]
              exact ((Classical.choose_spec (hlim k hkm.le z hzV hz0)).mono_left
                (nhdsWithin_mono z hBp_sub)).congr' hpe.symm
          · have hzp : 0 < z.2 := lt_of_le_of_ne hzge (Ne.symm hz0)
            have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) z :=
              (ContinuousOn.continuousOn_iteratedFDeriv hH hVp (by exact_mod_cast hkm.le) z
                ⟨hzV, hzp⟩).continuousAt (hVp.mem_nhds ⟨hzV, hzp⟩)
            show Tendsto (fun w => P w k) (𝓝[Bp] z) (𝓝 (P z k))
            rw [hP_ne z k (ne_of_gt hzp)]
            exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
        have hcontm : ∀ z ∈ closure Bm, ContinuousWithinAt (fun w => P w k) Bm z := by
          intro z hz
          have hzle : z.2 ≤ 0 := hbm_le z hz
          have hzV : z ∈ V := hclVm z hz
          have hpe : (fun w => P w k) =ᶠ[𝓝[Bm] z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun w hw => hP_ne w k (ne_of_lt hw.2))
          by_cases hz0 : z.2 = 0
          · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ 0 F w) z := by
                have hFc : ContinuousAt F z := hc.continuousAt (hV.mem_nhds hzV)
                have hfun : (fun w => iteratedFDeriv ℝ 0 F w) =
                    (fun w => (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm (F w)) := by
                  funext w; rw [iteratedFDeriv_zero_eq_comp]; rfl
                rw [hfun]
                exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm.continuous.continuousAt.comp
                  hFc
              exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
            · show Tendsto (fun w => P w k) (𝓝[Bm] z) (𝓝 (P z k))
              rw [hP_lim z k hzV hz0 hkm.le hkpos]
              exact ((Classical.choose_spec (hlim k hkm.le z hzV hz0)).mono_left
                (nhdsWithin_mono z hBm_sub)).congr' hpe.symm
          · have hzn : z.2 < 0 := lt_of_le_of_ne hzle hz0
            have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) z :=
              (ContinuousOn.continuousOn_iteratedFDeriv hN hVm (by exact_mod_cast hkm.le) z
                ⟨hzV, hzn⟩).continuousAt (hVm.mem_nhds ⟨hzV, hzn⟩)
            show Tendsto (fun w => P w k) (𝓝[Bm] z) (𝓝 (P z k))
            rw [hP_ne z k (ne_of_lt hzn)]
            exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
        have htendp : Tendsto (fun z => fderiv ℝ (fun w => P w k) z) (𝓝[Bp] y)
            (𝓝 ((P y (k+1)).curryLeft)) := by
          have hev : (fun z => fderiv ℝ (fun w => P w k) z) =ᶠ[𝓝[Bp] y]
              (fun z => (iteratedFDeriv ℝ (k+1) F z).curryLeft) := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            have hev2 : (fun w => P w k) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ k F w) :=
              Filter.eventuallyEq_of_mem (hsH.mem_nhds hz.2) (fun w hw => hP_ne w k (ne_of_gt hw))
            rw [Filter.EventuallyEq.fderiv_eq hev2, fderiv_iteratedFDeriv]
            exact (hcurl k (iteratedFDeriv ℝ (k+1) F z)).symm
          refine Tendsto.congr' hev.symm ?_
          have hbase : Tendsto (fun z => iteratedFDeriv ℝ (k+1) F z) (𝓝[Bp] y)
              (𝓝 (P y (k+1))) := by
            rw [hP_lim y (k+1) hyV hy0 hk1 (by omega)]
            exact (Classical.choose_spec (hlim (k+1) hk1 y hyV hy0)).mono_left
              (nhdsWithin_mono y hBp_sub)
          have hfun : (fun z => (iteratedFDeriv ℝ (k+1) F z).curryLeft)
              = (fun z => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X × ℝ) Y)
                  (iteratedFDeriv ℝ (k+1) F z)) := by
            funext z; exact hcurl k _
          have hval : (P y (k+1)).curryLeft
              = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X × ℝ) Y)
                  (P y (k+1)) := hcurl k _
          rw [hfun, hval]
          exact ((continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (k+1) => X × ℝ) Y).continuous.continuousAt.tendsto.comp hbase)
        have htendm : Tendsto (fun z => fderiv ℝ (fun w => P w k) z) (𝓝[Bm] y)
            (𝓝 ((P y (k+1)).curryLeft)) := by
          have hev : (fun z => fderiv ℝ (fun w => P w k) z) =ᶠ[𝓝[Bm] y]
              (fun z => (iteratedFDeriv ℝ (k+1) F z).curryLeft) := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            have hev2 : (fun w => P w k) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ k F w) :=
              Filter.eventuallyEq_of_mem (hsm.mem_nhds hz.2) (fun w hw => hP_ne w k (ne_of_lt hw))
            rw [Filter.EventuallyEq.fderiv_eq hev2, fderiv_iteratedFDeriv]
            exact (hcurl k (iteratedFDeriv ℝ (k+1) F z)).symm
          refine Tendsto.congr' hev.symm ?_
          have hbase : Tendsto (fun z => iteratedFDeriv ℝ (k+1) F z) (𝓝[Bm] y)
              (𝓝 (P y (k+1))) := by
            rw [hP_lim y (k+1) hyV hy0 hk1 (by omega)]
            exact (Classical.choose_spec (hlim (k+1) hk1 y hyV hy0)).mono_left
              (nhdsWithin_mono y hBm_sub)
          have hfun : (fun z => (iteratedFDeriv ℝ (k+1) F z).curryLeft)
              = (fun z => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X × ℝ) Y)
                  (iteratedFDeriv ℝ (k+1) F z)) := by
            funext z; exact hcurl k _
          have hval : (P y (k+1)).curryLeft
              = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X × ℝ) Y)
                  (P y (k+1)) := hcurl k _
          rw [hfun, hval]
          exact ((continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (k+1) => X × ℝ) Y).continuous.continuousAt.tendsto.comp hbase)
        have hA := hasFDerivWithinAt_closure_of_tendsto_fderiv hdiffp hBp_conv hBp_open hcontp htendp
        have hB := hasFDerivWithinAt_closure_of_tendsto_fderiv hdiffm hBm_conv hBm_open hcontm htendm
        have hclos : HasFDerivWithinAt (fun w => P w k) ((P y (k+1)).curryLeft) (ball y ρ) y :=
          (hA.union hB).mono fun z hz => by
            by_cases hz0 : z.2 = 0
            · left; exact mem_closure_ball_inter_pos hz hz0
            · rcases lt_or_gt_of_ne hz0 with hzn | hzp
              · right; exact subset_closure (by rw [hBm]; exact ⟨hz, hzn⟩)
              · left; exact subset_closure (by rw [hBp]; exact ⟨hz, hzp⟩)
        exact ((hclos.hasFDerivAt (isOpen_ball.mem_nhds (mem_ball_self hρpos)))).hasFDerivWithinAt
      · -- off the hyperplane
        rcases lt_or_gt_of_ne hy0 with hneg | hpos
        · have hyV : y ∈ V := hsub hy
          have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsm.mem_nhds hneg) (fun w hw => hP_ne w k (ne_of_lt hw))
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) y := by
            have hcd : ContDiffAt ℝ m F y :=
              (hN y ⟨hyV, hneg⟩).contDiffAt (hVm.mem_nhds ⟨hyV, hneg⟩)
            exact (hcd.iteratedFDeriv_right (m := 1)
              (by exact_mod_cast (by omega : 1 + k ≤ m))).differentiableAt (by norm_num)
          have hdiff : DifferentiableAt ℝ (fun w => P w k) y := hdiffit.congr_of_eventuallyEq hev2
          have hfd : fderiv ℝ (fun w => P w k) y = (P y (k+1)).curryLeft := by
            rw [Filter.EventuallyEq.fderiv_eq hev2, fderiv_iteratedFDeriv]
            rw [hP_ne y (k+1) (ne_of_lt hneg)]
            exact (hcurl k (iteratedFDeriv ℝ (k+1) F y)).symm
          have h1 : HasFDerivWithinAt (fun w => P w k) (fderiv ℝ (fun w => P w k) y)
              (ball q r) y := hdiff.hasFDerivAt.hasFDerivWithinAt
          rwa [hfd] at h1
        · have hyV : y ∈ V := hsub hy
          have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsH.mem_nhds hpos) (fun w hw => hP_ne w k (ne_of_gt hw))
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) y := by
            have hcd : ContDiffAt ℝ m F y :=
              (hH y ⟨hyV, hpos⟩).contDiffAt (hVp.mem_nhds ⟨hyV, hpos⟩)
            exact (hcd.iteratedFDeriv_right (m := 1)
              (by exact_mod_cast (by omega : 1 + k ≤ m))).differentiableAt (by norm_num)
          have hdiff : DifferentiableAt ℝ (fun w => P w k) y := hdiffit.congr_of_eventuallyEq hev2
          have hfd : fderiv ℝ (fun w => P w k) y = (P y (k+1)).curryLeft := by
            rw [Filter.EventuallyEq.fderiv_eq hev2, fderiv_iteratedFDeriv]
            rw [hP_ne y (k+1) (ne_of_gt hpos)]
            exact (hcurl k (iteratedFDeriv ℝ (k+1) F y)).symm
          have h1 : HasFDerivWithinAt (fun w => P w k) (fderiv ℝ (fun w => P w k) y)
              (ball q r) y := hdiff.hasFDerivAt.hasFDerivWithinAt
          rwa [hfd] at h1
    · -- cont field
      intro k hk
      have hkm : k ≤ m := by exact_mod_cast hk
      intro y hy
      by_cases hy0 : y.2 = 0
      · -- on the hyperplane
        set Ω : Set (X × ℝ) := ball q r ∩ {z : X × ℝ | z.2 ≠ 0} with hΩ
        set Hh : Set (X × ℝ) := ball q r ∩ {z : X × ℝ | z.2 = 0} with hHh
        have hΩH : Ω ∪ Hh = ball q r := by
          ext z
          rw [hΩ, hHh]
          simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
          · intro h1
            by_cases h2 : z.2 = 0
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl ⟨h1, h2⟩
        have hyV : y ∈ V := hsub hy
        have hcont_at : ContinuousAt (fun z => P z k) y := by
          refine continuousAt_of_tendsto_nhdsWithin (Ω := Ω) (H := Hh)
            (f := fun z => iteratedFDeriv ℝ k F z) (g := fun z => P z k) ?_ ⟨hy, hy0⟩ ?_ ?_ ?_
          · intro z hz
            rw [hΩ] at hz
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
            exact hP_ne z k hz.2
          · rw [hΩH]; exact isOpen_ball.mem_nhds hy
          · intro z hz
            rw [hHh] at hz
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
            refine closure_mono ?_ (mem_closure_ball_inter_pos hz.1 hz.2)
            intro w hw
            rw [hΩ]
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
            exact ⟨hw.1, ne_of_gt hw.2⟩
          · intro z hz
            rw [hHh] at hz
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
            have hz0 : z.2 = 0 := hz.2
            have hzV : z ∈ V := hsub hz.1
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ 0 F w) z := by
                have hFc : ContinuousAt F z := hc.continuousAt (hV.mem_nhds hzV)
                have hfun : (fun w => iteratedFDeriv ℝ 0 F w) =
                    (fun w => (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm (F w)) := by
                  funext w; rw [iteratedFDeriv_zero_eq_comp]; rfl
                rw [hfun]
                exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm.continuous.continuousAt.comp
                  hFc
              exact hzc.tendsto.mono_left nhdsWithin_le_nhds
            · have hΩsub : Ω ⊆ V ∩ {q : X × ℝ | q.2 ≠ 0} := by
                intro a ha
                rw [hΩ] at ha
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at ha
                exact ⟨hsub ha.1, ha.2⟩
              rw [hP_lim z k hzV hz0 hkm hkpos]
              exact (Classical.choose_spec (hlim k hkm z hzV hz0)).mono_left
                (nhdsWithin_mono z hΩsub)
        exact hcont_at.continuousWithinAt
      · -- off the hyperplane
        rcases lt_or_gt_of_ne hy0 with hneg | hpos
        · have hyV : y ∈ V := hsub hy
          have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsm.mem_nhds hneg) (fun w hw => hP_ne w k (ne_of_lt hw))
          have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) y :=
            (ContinuousOn.continuousOn_iteratedFDeriv hN hVm (by exact_mod_cast hkm) y
              ⟨hyV, hneg⟩).continuousAt (hVm.mem_nhds ⟨hyV, hneg⟩)
          exact (hzc.congr_of_eventuallyEq hev2).continuousWithinAt
        · have hyV : y ∈ V := hsub hy
          have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsH.mem_nhds hpos) (fun w hw => hP_ne w k (ne_of_gt hw))
          have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) y :=
            (ContinuousOn.continuousOn_iteratedFDeriv hH hVp (by exact_mod_cast hkm) y
              ⟨hyV, hpos⟩).continuousAt (hVp.mem_nhds ⟨hyV, hpos⟩)
          exact (hzc.congr_of_eventuallyEq hev2).continuousWithinAt
  -- conclusion
  intro p hp
  by_cases hp0 : p.2 = 0
  · obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hp)
    have hPk := hkey p r hr hrs
    refine contDiffWithinAt_nat.mpr ⟨ball p r, ?_, P, hPk⟩
    exact mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  · rcases lt_or_gt_of_ne hp0 with hneg | hpos
    · exact ((hN p ⟨hp, hneg⟩).contDiffAt (hVm.mem_nhds ⟨hp, hneg⟩)).contDiffWithinAt
    · exact ((hH p ⟨hp, hpos⟩).contDiffAt (hVp.mem_nhds ⟨hp, hpos⟩)).contDiffWithinAt


/-! ## Auxiliary estimate lemmas -/

section Aux

open scoped NNReal ENNReal

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Cross Hölder seminorm of order `α` between two sets: the supremum over pairs `x ∈ Ω`,
`y ∈ Ω'`, `x ≠ y` of `‖D^i f x - D^i f y‖ / ‖x - y‖^α`. -/
noncomputable def gSNc (i : ℕ) (α : ℝ) (f : Y → A) (Ω Ω' : Set Y) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω', ⨆ (_ : x ≠ y),
    ENNReal.ofReal (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)

lemma le_gSNc (i : ℕ) (α : ℝ) {f : Y → A} {Ω Ω' : Set Y} {x y : Y}
    (hx : x ∈ Ω) (hy : y ∈ Ω') (hxy : x ≠ y) :
    ENNReal.ofReal (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)
      ≤ gSNc i α f Ω Ω' :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

lemma gSNc_comm (i : ℕ) (α : ℝ) (f : Y → A) (Ω Ω' : Set Y) :
    gSNc i α f Ω Ω' = gSNc i α f Ω' Ω := by
  have key : ∀ x y : Y,
      ENNReal.ofReal (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)
      = ENNReal.ofReal (‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f x‖ / ‖y - x‖ ^ α) := by
    intro x y
    rw [norm_sub_rev (iteratedFDeriv ℝ i f x) (iteratedFDeriv ℝ i f y), norm_sub_rev x y]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [key x y]
    exact le_gSNc i α hy hx (Ne.symm hxy)
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [key x y]
    exact le_gSNc i α hy hx (Ne.symm hxy)

lemma gDN_union_le (i : ℕ) (f : Y → A) (Ω Ω' : Set Y) :
    Work.NN.Final.gDN i f (Ω ∪ Ω') ≤ Work.NN.Final.gDN i f Ω ⊔ Work.NN.Final.gDN i f Ω' := by
  refine iSup₂_le fun x hx => ?_
  rcases hx with hx | hx
  · exact le_trans (le_gDN i hx) le_sup_left
  · exact le_trans (le_gDN i hx) le_sup_right

lemma gSN_union_le (i : ℕ) (α : ℝ) (f : Y → A) (Ω Ω' : Set Y) :
    Work.NN.Final.gSN i α f (Ω ∪ Ω')
      ≤ Work.NN.Final.gSN i α f Ω ⊔ Work.NN.Final.gSN i α f Ω' ⊔ gSNc i α f Ω Ω' := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact le_trans (le_gSN i α hx hy hxy) (le_sup_left.trans le_sup_left)
  · exact le_trans (le_gSNc i α hx hy hxy) le_sup_right
  · refine le_trans (le_gSNc i α hx hy hxy) ?_
    rw [gSNc_comm i α f Ω' Ω]
    exact le_sup_right
  · exact le_trans (le_gSN i α hx hy hxy) (le_sup_right.trans le_sup_left)

/-- A set is covered by three others if ... -/
lemma gDN_three_le (i : ℕ) (f : Y → A) (Ω Ω₁ Ω₂ Ω₃ : Set Y) (h : Ω ⊆ Ω₁ ∪ Ω₂ ∪ Ω₃) :
    Work.NN.Final.gDN i f Ω ≤ Work.NN.Final.gDN i f Ω₁ ⊔ Work.NN.Final.gDN i f Ω₂ ⊔ Work.NN.Final.gDN i f Ω₃ := by
  calc Work.NN.Final.gDN i f Ω ≤ Work.NN.Final.gDN i f (Ω₁ ∪ Ω₂ ∪ Ω₃) :=
        Work.NN.Final.gDN_mono h i f
    _ ≤ Work.NN.Final.gDN i f (Ω₁ ∪ Ω₂) ⊔ Work.NN.Final.gDN i f Ω₃ := gDN_union_le i f _ _
    _ ≤ (Work.NN.Final.gDN i f Ω₁ ⊔ Work.NN.Final.gDN i f Ω₂) ⊔ Work.NN.Final.gDN i f Ω₃ :=
        sup_le_sup_right (gDN_union_le i f Ω₁ Ω₂) _

end Aux

/-! ## The finite moment data -/

/-- The chosen positive nodes `ε i` of the finite moment problem of order `k`. -/
noncomputable def mEps (k : ℕ) : Fin (k + 1) → ℝ := Classical.choose (existsFiniteMomentData k)

/-- The chosen weights `λ i` of the finite moment problem of order `k`. -/
noncomputable def mLam (k : ℕ) : Fin (k + 1) → ℝ :=
  Classical.choose (Classical.choose_spec (existsFiniteMomentData k))

lemma mEps_pos (k : ℕ) (i : Fin (k + 1)) : 0 < mEps k i :=
  (Classical.choose_spec (Classical.choose_spec (existsFiniteMomentData k))).1 i

lemma mLam_moment (k : ℕ) (j : ℕ) (hj : j ≤ k) :
    ∑ i : Fin (k + 1), mLam k i * (-(mEps k i)) ^ j = 1 :=
  (Classical.choose_spec (Classical.choose_spec (existsFiniteMomentData k))).2 j hj

/-! ## The chain rule for the normal rescaling `eta` -/

section EtaChain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iteratedFDeriv_comp_eta {k i : ℕ} {S : Set (E × ℝ)} (hS : IsOpen S) {g : E × ℝ → ℂ}
    (hg : ContDiffOn ℝ (k : ℕ∞) g S) (hi : i ≤ k) (c : ℝ) {x : E × ℝ}
    (hx : eta (X := E) c x ∈ S) :
    iteratedFDeriv ℝ i (fun z => g (eta (X := E) c z)) x
      = (iteratedFDeriv ℝ i g (eta (X := E) c x)).compContinuousLinearMap
          (fun _ => eta (X := E) c) := by
  have hik : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hi
  have hpre : IsOpen (eta (X := E) c ⁻¹' S) := hS.preimage (eta (X := E) c).continuous
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := eta (X := E) c) (s := S) (f := g) (x := x) (i := i)
    hg hS.uniqueDiffOn hpre.uniqueDiffOn hx hik
  rw [iteratedFDerivWithin_of_isOpen i hpre hx,
      iteratedFDerivWithin_of_isOpen i hS hx] at h
  simpa only [Function.comp_def] using h

lemma norm_iteratedFDeriv_comp_eta_le {k i : ℕ} {S : Set (E × ℝ)} (hS : IsOpen S)
    {g : E × ℝ → ℂ} (hg : ContDiffOn ℝ (k : ℕ∞) g S) (hi : i ≤ k) (c : ℝ) {x : E × ℝ}
    (hx : eta (X := E) c x ∈ S) :
    ‖iteratedFDeriv ℝ i (fun z => g (eta (X := E) c z)) x‖
      ≤ ‖iteratedFDeriv ℝ i g (eta (X := E) c x)‖ * ‖eta (X := E) c‖ ^ i := by
  rw [iteratedFDeriv_comp_eta hS hg hi c hx]
  calc ‖(iteratedFDeriv ℝ i g (eta (X := E) c x)).compContinuousLinearMap
        (fun _ => eta (X := E) c)‖
      ≤ ‖iteratedFDeriv ℝ i g (eta (X := E) c x)‖ * ∏ _ : Fin i, ‖eta (X := E) c‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ i g (eta (X := E) c x)‖ * ‖eta (X := E) c‖ ^ i := by simp

end EtaChain

/-! ## The reflection sum and its derivatives -/

section Reflect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The reflected sum `∑ j, λ j • g (eta (-(ε j)) ·)`. -/
noncomputable def reflSum {n : ℕ} (ε lam : Fin n → ℝ) (g : E × ℝ → ℂ) : E × ℝ → ℂ :=
  fun z => ∑ j : Fin n, (lam j) • g (eta (X := E) (-(ε j)) z)

lemma iteratedFDeriv_reflSum {k i : ℕ} {S : Set (E × ℝ)} (hS : IsOpen S) {g : E × ℝ → ℂ}
    (hg : ContDiffOn ℝ (k : ℕ∞) g S) (hi : i ≤ k) {n : ℕ} (ε lam : Fin n → ℝ)
    {x : E × ℝ} (hx : ∀ j, eta (X := E) (-(ε j)) x ∈ S) :
    iteratedFDeriv ℝ i (reflSum (E := E) ε lam g) x
      = ∑ j : Fin n, (lam j) •
          (iteratedFDeriv ℝ i g (eta (X := E) (-(ε j)) x)).compContinuousLinearMap
            (fun _ => eta (X := E) (-(ε j))) := by
  have hsum := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := i) (u := Finset.univ)
    (f := fun j : Fin n => fun z : E × ℝ => (lam j) • g (eta (X := E) (-(ε j)) z))
    (by
      intro j _
      have hg' : ContDiffAt ℝ (i : ℕ∞) g (eta (X := E) (-(ε j)) x) :=
        (hg.contDiffAt (hS.mem_nhds (hx j))).of_le (by exact_mod_cast hi)
      fun_prop)
  rw [show reflSum (E := E) ε lam g
      = (fun z : E × ℝ => ∑ j : Fin n, (lam j) • g (eta (X := E) (-(ε j)) z)) from rfl,
    hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg' : ContDiffAt ℝ (i : ℕ∞) g (eta (X := E) (-(ε j)) x) :=
    (hg.contDiffAt (hS.mem_nhds (hx j))).of_le (by exact_mod_cast hi)
  have hc : ContDiffAt ℝ (i : ℕ∞) (fun z : E × ℝ => g (eta (X := E) (-(ε j)) z)) x := by
    have h := hg'.comp x ((ContinuousLinearMap.contDiff (eta (X := E) (-(ε j)))).contDiffAt)
    simpa only [Function.comp_def] using h
  rw [show (fun z : E × ℝ => (lam j) • g (eta (X := E) (-(ε j)) z))
      = ((lam j) • (fun z : E × ℝ => g (eta (X := E) (-(ε j)) z))) from by
        funext z; rfl]
  rw [iteratedFDeriv_const_smul_apply (a := (lam j)) hc]
  congr 1
  exact iteratedFDeriv_comp_eta hS hg hi (-(ε j)) (hx j)

/-- Distance estimate for the reflection in the normal variable: for `x` strictly above and `y`
strictly below the hyperplane, `‖x - eta (-c) y‖ ≤ max 1 c * ‖x - y‖`. -/
lemma norm_sub_eta_le {c : ℝ} (hc : 0 ≤ c) {x y : E × ℝ} (hx : 0 < x.2) (hy : y.2 < 0) :
    ‖x - eta (X := E) (-c) y‖ ≤ max 1 c * ‖x - y‖ := by
  have hd : ‖x - y‖ = max ‖x.1 - y.1‖ ‖x.2 - y.2‖ := by
    rw [Prod.norm_mk]; rfl
  have h2 : ‖x.2 - y.2‖ ≤ ‖x - y‖ := by rw [hd]; exact le_max_right _ _
  have hxy2 : ‖x.2 - y.2‖ = x.2 - y.2 := by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h3 : x.2 ≤ ‖x - y‖ := by rw [hxy2] at h2; linarith
  have h4 : -y.2 ≤ ‖x - y‖ := by rw [hxy2] at h2; linarith
  have h5 : |x.2 + c * y.2| ≤ max x.2 (c * (-y.2)) := by
    by_cases hle : 0 ≤ x.2 + c * y.2
    · rw [abs_of_nonneg hle]
      have : c * y.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc (le_of_lt hy)
      exact le_trans (by linarith) (le_max_left _ _)
    · rw [abs_of_neg (not_le.mp hle)]
      have h6 : -(c * y.2) ≤ c * (-y.2) := by ring_nf; exact le_rfl
      exact le_trans (by linarith) (le_max_right _ _)
  have hxy : x - eta (X := E) (-c) y = (x.1 - y.1, x.2 + c * y.2) := by
    ext <;> simp [eta_apply] <;> ring
  rw [hxy, Prod.norm_mk]
  refine max_le ?_ ?_
  · calc ‖x.1 - y.1‖ ≤ ‖x - y‖ := by rw [hd]; exact le_max_left _ _
      _ = 1 * ‖x - y‖ := (one_mul _).symm
      _ ≤ max 1 c * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · refine le_trans h5 (max_le ?_ ?_)
    · calc x.2 ≤ ‖x - y‖ := h3
        _ = 1 * ‖x - y‖ := (one_mul _).symm
        _ ≤ max 1 c * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · calc c * (-y.2) ≤ c * ‖x - y‖ :=
            mul_le_mul_of_nonneg_left (by linarith) hc
        _ ≤ max 1 c * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end Reflect

/-! ## Elementary monotonicity helpers for the extension constants -/

lemma le_max_one_mul_left {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ max 1 a * b * c :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) a) hb) hc

lemma one_mul_le_max_one_mul {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    b * c ≤ max 1 a * b * c := by
  have h1 : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  calc b * c = 1 * (b * c) := (one_mul _).symm
    _ ≤ max 1 a * (b * c) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hb hc)
    _ = max 1 a * b * c := by ring

/-! ## The one-sided extension, per order -/

section Extension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The constant of the one-sided extension estimate at order `k`. -/
noncomputable def extConst (k : ℕ) (α : ℝ) : ℝ :=
  max 1 (∑ i ∈ Finset.range (k + 1),
    (max 1 (∑ j : Fin (k + 1), |mLam k j| * (max 1 (mEps k j)) ^ i)
      + max 1 (∑ j : Fin (k + 1), |mLam k j| * (max 1 (mEps k j)) ^ ((i : ℝ) + α))))

lemma extConst_pos (k : ℕ) (α : ℝ) : 0 < extConst k α :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- **The flat one-sided extension, at a fixed order `k`.**

Given `g` which is `C^k` on the half space `W × (0,∞)` with finite `C^{k,α}` norm there,
there is an extension `G` to the strip `W × (-δ,∞)`, equal to `g` on the half space, with
`holderNorm k α G (W × (-δ,∞)) ≤ ofReal (extConst k α) * holderNorm k α g (W × (0,∞))`. -/
theorem flatExtensionConst {α : ℝ} (hα0 : 0 < α) {δ : ℝ} (hδ : 0 < δ) (k : ℕ)
    (W : Set E) (g : E × ℝ → ℂ) (hW : IsOpen W)
    (hg : ContDiffOn ℝ (k : WithTop ENat) g (Set.prod W {t : ℝ | 0 < t}))
    (hfin : Work.CR.Flat.holderNorm k α g (Set.prod W {t : ℝ | 0 < t}) ≠ ⊤) :
    ∃ G : E × ℝ → ℂ,
      ContDiffOn ℝ (k : WithTop ENat) G (Set.prod W {t : ℝ | -δ < t}) ∧
      (∀ p, p.1 ∈ W → 0 < p.2 → G p = g p) ∧
      Work.CR.Flat.holderNorm k α G (Set.prod W {t : ℝ | -δ < t})
        ≤ ENNReal.ofReal (extConst k α)
          * Work.CR.Flat.holderNorm k α g (Set.prod W {t : ℝ | 0 < t}) := by
  classical
  set S : Set (E × ℝ) := Set.prod W {t : ℝ | 0 < t} with hSdef
  set V : Set (E × ℝ) := Set.prod W {t : ℝ | -δ < t} with hVdef
  have hSopen : IsOpen S := hW.prod isOpen_Ioi
  have hVopen : IsOpen V := hW.prod isOpen_Ioi
  -- the limits of the derivatives of `g` at the boundary
  have hlimEx : ∀ (i : ℕ), i ≤ k → ∀ p : E, p ∈ W →
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ,
        Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i g q) (𝓝[S] (p, 0)) (𝓝 L) :=
    fun i hi p hp => holderDerivTendsto hα0 hW g hfin hi hp
  choose Li hLi using hlimEx
  -- the boundary value of `g`
  have hL0tend : ∀ (p : E) (hp : p ∈ W),
      Filter.Tendsto g (𝓝[S] (p, 0))
        (𝓝 (continuousMultilinearCurryFin0 ℝ (E × ℝ) ℂ (Li 0 (Nat.zero_le k) p hp))) := by
    intro p hp
    have h := hLi 0 (Nat.zero_le k) p hp
    rw [show (fun q : E × ℝ => iteratedFDeriv ℝ 0 g q)
        = (fun q : E × ℝ => (continuousMultilinearCurryFin0 ℝ (E × ℝ) ℂ).symm (g q)) from by
          funext q; rw [iteratedFDeriv_zero_eq_comp]; rfl] at h
    have h2 := ((continuousMultilinearCurryFin0 ℝ (E × ℝ) ℂ).continuous.tendsto
      (Li 0 (Nat.zero_le k) p hp)).comp h
    have h3 : (⇑(continuousMultilinearCurryFin0 ℝ (E × ℝ) ℂ) ∘
        (fun q : E × ℝ => (continuousMultilinearCurryFin0 ℝ (E × ℝ) ℂ).symm (g q))) = g := by
      funext q; simp
    rwa [h3] at h2
  have hL0ex : ∀ p : E, ∃ z : ℂ, p ∈ W → Filter.Tendsto g (𝓝[S] (p, 0)) (𝓝 z) := by
    intro p
    by_cases hp : p ∈ W
    · exact ⟨_, fun _ => hL0tend p hp⟩
    · exact ⟨0, fun h => absurd h hp⟩
  let L0 : E → ℂ := fun p => Classical.choose (hL0ex p)
  have hL0spec : ∀ (p : E) (hp : p ∈ W), Filter.Tendsto g (𝓝[S] (p, 0)) (𝓝 (L0 p)) :=
    fun p hp => Classical.choose_spec (hL0ex p) hp
  let eps : Fin (k + 1) → ℝ := mEps k
  let lam : Fin (k + 1) → ℝ := mLam k
  have heps : ∀ j, 0 < eps j := fun j => mEps_pos k j
  have hlam : ∀ j : ℕ, j ≤ k → ∑ i : Fin (k + 1), lam i * (-(eps i)) ^ j = 1 :=
    fun j hj => mLam_moment k j hj
  -- the extension
  let G : E × ℝ → ℂ := fun p =>
    if 0 < p.2 then g p
    else if p.2 = 0 then L0 p.1
    else ∑ j : Fin (k + 1), (lam j) • g (eta (X := E) (-(eps j)) p)
  have hGupper : ∀ p : E × ℝ, 0 < p.2 → G p = g p := by
    intro p hp; simp only [G]; rw [ite_eq_left hp]
  have hGhyper : ∀ p : E × ℝ, p.2 = 0 → G p = L0 p.1 := by
    intro p hp
    simp only [G]
    rw [ite_eq_right (by rw [hp]; exact not_lt.mpr le_rfl), ite_eq_left hp]
  have hGlower : ∀ p : E × ℝ, p.2 < 0 →
      G p = ∑ j : Fin (k + 1), (lam j) • g (eta (X := E) (-(eps j)) p) := by
    intro p hp
    simp only [G]
    rw [ite_eq_right (not_lt.mpr hp.le), ite_eq_right (ne_of_lt hp)]
  have hGg : ∀ p, p.1 ∈ W → 0 < p.2 → G p = g p := fun p _ hp => hGupper p hp
  -- smoothness on the two halves
  have hVU_sub_S : V ∩ {z : E × ℝ | 0 < z.2} ⊆ S := by
    rintro z ⟨hzV, hz2⟩
    exact ⟨hzV.1, hz2⟩
  have hH : ContDiffOn ℝ (k : ℕ∞) G (V ∩ {z : E × ℝ | 0 < z.2}) :=
    (hg.mono hVU_sub_S).congr fun z hz => hGupper z hz.2
  have hVLmap : ∀ j : Fin (k + 1),
      Set.MapsTo (eta (X := E) (-(eps j))) (V ∩ {z : E × ℝ | z.2 < 0}) S := by
    intro j z hz
    obtain ⟨hzV, hz2⟩ := hz
    simp only [Set.mem_ofPred_eq] at hz2
    refine ⟨?_, ?_⟩
    · simpa using hzV.1
    · rw [eta_apply]
      simp only [Set.mem_ofPred_eq]
      have := heps j
      nlinarith
  have hN : ContDiffOn ℝ (k : ℕ∞) G (V ∩ {z : E × ℝ | z.2 < 0}) := by
    have hfun : ContDiffOn ℝ (k : ℕ∞)
        (fun z : E × ℝ => ∑ j : Fin (k + 1), (lam j) • g (eta (X := E) (-(eps j)) z))
        (V ∩ {z : E × ℝ | z.2 < 0}) := by
      refine ContDiffOn.sum fun j _ => ?_
      refine ContDiffOn.const_smul _ ?_
      have h1 : ContDiffOn ℝ (k : ℕ∞) (fun z : E × ℝ => g (eta (X := E) (-(eps j)) z))
          (V ∩ {z : E × ℝ | z.2 < 0}) := by
        have h2 : ContDiffOn ℝ (k : ℕ∞) (g ∘ (eta (X := E) (-(eps j))))
            ((eta (X := E) (-(eps j))) ⁻¹' S) :=
          hg.comp_continuousLinearMap (eta (X := E) (-(eps j)))
        have hsub : V ∩ {z : E × ℝ | z.2 < 0} ⊆ (eta (X := E) (-(eps j))) ⁻¹' S :=
          hVLmap j
        exact (h2.mono hsub).congr fun z hz => rfl
      exact h1
    exact hfun.congr fun z hz => hGlower z hz.2
  -- ** the two one-sided limits at a boundary point **
  have hVUlim : ∀ p : E × ℝ, p ∈ V → p.2 = 0 →
      Filter.Tendsto G (𝓝[V ∩ {z : E × ℝ | 0 < z.2}] p) (𝓝 (L0 p.1)) := by
    intro p hpV hp0
    have hp_eq : (p.1, (0 : ℝ)) = p := by ext <;> simp [hp0]
    have h1 : Filter.Tendsto g (𝓝[V ∩ {z : E × ℝ | 0 < z.2}] p) (𝓝 (L0 p.1)) := by
      rw [← hp_eq]
      exact (hL0spec p.1 hpV.1).mono_left
        (nhdsWithin_mono _ (fun z hz => ⟨hz.1.1, hz.2⟩))
    exact h1.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
      (fun z hz => (hGupper z hz.2).symm))
  have hVLlim : ∀ p : E × ℝ, p ∈ V → p.2 = 0 →
      Filter.Tendsto G (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] p) (𝓝 (L0 p.1)) := by
    intro p hpV hp0
    have hsum_tend : Filter.Tendsto
        (fun z : E × ℝ => ∑ j : Fin (k + 1), (lam j) • g (eta (X := E) (-(eps j)) z))
        (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] p)
        (𝓝 (∑ j : Fin (k + 1), (lam j) • L0 p.1)) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      have hj : Filter.Tendsto (fun z : E × ℝ => g (eta (X := E) (-(eps j)) z))
          (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] p) (𝓝 (L0 p.1)) := by
        have ht : Filter.Tendsto (eta (X := E) (-(eps j)))
            (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] p) (𝓝[S] (p.1, (0 : ℝ))) := by
          rw [tendsto_nhdsWithin_iff]
          constructor
          · have h0 : Filter.Tendsto (eta (X := E) (-(eps j))) (𝓝 p)
                (𝓝 (eta (X := E) (-(eps j)) p)) :=
              (eta (X := E) (-(eps j))).continuous.continuousAt
            rw [show eta (X := E) (-(eps j)) p = (p.1, (0 : ℝ)) by
                  rw [eta_apply]; simp [hp0]] at h0
            exact h0.mono_left (nhdsWithin_le_nhds (s := V ∩ {z : E × ℝ | z.2 < 0}))
          · filter_upwards [self_mem_nhdsWithin] with z hz
            exact hVLmap j hz
        have h2 := (hL0spec p.1 hpV.1).comp ht
        simpa only [Function.comp_def] using h2
      exact hj.const_smul (lam j)
    have hsumval : (∑ j : Fin (k + 1), (lam j) • L0 p.1) = L0 p.1 := by
      rw [← Finset.sum_smul]
      have h1 : (∑ j : Fin (k + 1), lam j) = 1 := by
        have h3 := hlam 0 (Nat.zero_le k)
        simpa using h3
      rw [h1, one_smul]
    rw [hsumval] at hsum_tend
    exact hsum_tend.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
      (fun z hz => (hGlower z hz.2).symm))
  have hlim_diag : ∀ p : E × ℝ, p ∈ V → p.2 = 0 →
      Filter.Tendsto G (𝓝[V ∩ {z : E × ℝ | z.2 ≠ 0}] p) (𝓝 (L0 p.1)) := by
    intro p hpV hp0
    have hset : V ∩ {z : E × ℝ | z.2 ≠ 0}
        = (V ∩ {z : E × ℝ | 0 < z.2}) ∪ (V ∩ {z : E × ℝ | z.2 < 0}) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_or_gt_of_ne h2 with h | h
        · exact Or.inr ⟨h1, h⟩
        · exact Or.inl ⟨h1, h⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, ne_of_gt h2⟩
        · exact ⟨h1, ne_of_lt h2⟩
    rw [hset, nhdsWithin_union]
    exact tendsto_sup.mpr ⟨hVUlim p hpV hp0, hVLlim p hpV hp0⟩
  -- ** continuity **
  have hcontV0 : ∀ p : E × ℝ, p ∈ V → p.2 = 0 → ContinuousAt G p := by
    intro p hpV hp0
    refine continuousAt_of_tendsto_nhdsWithin (Ω := V ∩ {z : E × ℝ | z.2 ≠ 0})
      (H := V ∩ {z : E × ℝ | z.2 = 0}) (f := G) (g := G) (fun z hz => rfl)
      ⟨hpV, hp0⟩ ?_ ?_ ?_
    · have hcover : (V ∩ {z : E × ℝ | z.2 ≠ 0}) ∪ (V ∩ {z : E × ℝ | z.2 = 0}) = V := by
        ext z
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hz
          by_cases h : z.2 = 0
          · exact Or.inr ⟨hz, h⟩
          · exact Or.inl ⟨hz, h⟩
      rw [hcover]
      exact hVopen.mem_nhds hpV
    · intro z hz
      have hz02 : z.2 = 0 := hz.2
      rw [Metric.mem_closure_iff]
      intro e he
      have hpos : 0 < min e 1 / 2 := by positivity
      refine ⟨(z.1, min e 1 / 2), ?_, ?_⟩
      · refine ⟨⟨hz.1.1, ?_⟩, ?_⟩
        · simp only [Set.mem_ofPred_eq]; linarith
        · simp only [Set.mem_ofPred_eq]; exact hpos.ne'
      · have hdiff : z - (z.1, min e 1 / 2) = (0, -(min e 1 / 2)) := by
          ext <;> simp [hz02]
        rw [dist_eq_norm, hdiff, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _),
          Real.norm_eq_abs, abs_neg, abs_of_pos hpos]
        have h1 : min e 1 ≤ e := min_le_left _ _
        linarith
    · intro z hz
      rw [hGhyper z hz.2]
      exact hlim_diag z hz.1 hz.2
  have hc : ContinuousOn G V := by
    intro p hpV
    by_cases hp2 : p.2 = 0
    · exact (hcontV0 p hpV hp2).continuousWithinAt
    · rcases lt_or_gt_of_ne hp2 with h | h
      · exact ((hN.contDiffAt ((hVopen.inter
          (isOpen_lt continuous_snd continuous_const)).mem_nhds ⟨hpV, h⟩)).continuousAt).continuousWithinAt
      · have hgc : ContDiffAt ℝ (k : ℕ∞) g p :=
          hg.contDiffAt (hSopen.mem_nhds ⟨hpV.1, h⟩)
        have hev : G =ᶠ[𝓝 p] g := by
          filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds h] with z hz
          exact hGupper z hz
        exact ((hgc.continuousAt.congr hev.symm)).continuousWithinAt
  -- ** the jet limits at the boundary **
  have hderivU : ∀ (i : ℕ) (hi : i ≤ k) (q : E) (hq : q ∈ W),
      Filter.Tendsto (fun z : E × ℝ => iteratedFDeriv ℝ i G z)
        (𝓝[V ∩ {z : E × ℝ | 0 < z.2}] (q, (0 : ℝ))) (𝓝 (Li i hi q hq)) := by
    intro i hi q hq
    have h1 : Filter.Tendsto (fun z : E × ℝ => iteratedFDeriv ℝ i g z)
        (𝓝[V ∩ {z : E × ℝ | 0 < z.2}] (q, (0 : ℝ))) (𝓝 (Li i hi q hq)) :=
      (hLi i hi q hq).mono_left (nhdsWithin_mono _ (fun z hz => ⟨hz.1.1, hz.2⟩))
    refine h1.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun z hz => ?_))
    have hev : G =ᶠ[𝓝 z] g := Filter.eventuallyEq_of_mem
      (hSopen.mem_nhds ⟨hz.1.1, hz.2⟩) (fun w hw => hGupper w hw.2)
    exact ((hev.iteratedFDeriv ℝ i).eq_of_nhds).symm
  have hderivL : ∀ (i : ℕ) (hi : i ≤ k) (q : E) (hq : q ∈ W),
      Filter.Tendsto (fun z : E × ℝ => iteratedFDeriv ℝ i G z)
        (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] (q, (0 : ℝ))) (𝓝 (Li i hi q hq)) := by
    intro i hi q hq
    have hfun : Filter.Tendsto
        (fun z : E × ℝ => ∑ j : Fin (k + 1), (lam j) •
            (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) z)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j))))
        (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] (q, (0 : ℝ)))
        (𝓝 (∑ j : Fin (k + 1), (lam j) •
            (Li i hi q hq).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j))))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      have hcomp : Filter.Tendsto (fun z : E × ℝ => eta (X := E) (-(eps j)) z)
          (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] (q, (0 : ℝ))) (𝓝[S] (q, (0 : ℝ))) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have h0 : Filter.Tendsto (eta (X := E) (-(eps j))) (𝓝 (q, (0 : ℝ)))
              (𝓝 (eta (X := E) (-(eps j)) (q, (0 : ℝ)))) :=
            (eta (X := E) (-(eps j))).continuous.continuousAt
          rw [show eta (X := E) (-(eps j)) (q, (0 : ℝ)) = (q, (0 : ℝ)) by
                rw [eta_apply]; simp] at h0
          exact h0.mono_left (nhdsWithin_le_nhds (s := V ∩ {z : E × ℝ | z.2 < 0}))
        · filter_upwards [self_mem_nhdsWithin] with z hz
          exact hVLmap j hz
      have hbase : Filter.Tendsto
          (fun z : E × ℝ => iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) z))
          (𝓝[V ∩ {z : E × ℝ | z.2 < 0}] (q, (0 : ℝ))) (𝓝 (Li i hi q hq)) :=
        (hLi i hi q hq).comp hcomp
      have hcomp' := (ContinuousMultilinearMap.compContinuousLinearMapL
        (f := fun _ : Fin i => eta (X := E) (-(eps j)))).continuous.continuousAt.tendsto.comp hbase
      exact hcomp'.const_smul (lam j)
    have hval : (∑ j : Fin (k + 1), (lam j) •
        (Li i hi q hq).compContinuousLinearMap (fun _ => eta (X := E) (-(eps j))))
        = Li i hi q hq :=
      etaCompMoment (k := k) hlam i hi (Li i hi q hq)
    rw [hval] at hfun
    refine hfun.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun z hz => ?_))
    have hev : G =ᶠ[𝓝 z] reflSum eps lam g := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hz.2] with w hw
      exact hGlower w hw
    exact (((hev.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_reflSum hSopen hg hi eps lam (fun j => hVLmap j hz))).symm
  have hset_split : V ∩ {z : E × ℝ | z.2 ≠ 0}
      = (V ∩ {z : E × ℝ | 0 < z.2}) ∪ (V ∩ {z : E × ℝ | z.2 < 0}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h2 with h | h
      · exact Or.inr ⟨h1, h⟩
      · exact Or.inl ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, ne_of_gt h2⟩
      · exact ⟨h1, ne_of_lt h2⟩
  have hlimJet : ∀ (i : ℕ) (hi : i ≤ k) (q : E) (hq : q ∈ W),
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ,
        Filter.Tendsto (fun z : E × ℝ => iteratedFDeriv ℝ i G z)
          (𝓝[V ∩ {z : E × ℝ | z.2 ≠ 0}] (q, (0 : ℝ))) (𝓝 L) := by
    intro i hi q hq
    exact ⟨Li i hi q hq, by
      rw [hset_split, nhdsWithin_union]
      exact tendsto_sup.mpr ⟨hderivU i hi q hq, hderivL i hi q hq⟩⟩
  have hlim_glue : ∀ (i : ℕ), i ≤ k → ∀ p ∈ V, p.2 = 0 →
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ,
        Filter.Tendsto (fun z : E × ℝ => iteratedFDeriv ℝ i G z)
          (𝓝[V ∩ {z : E × ℝ | z.2 ≠ 0}] p) (𝓝 L) := by
    intro i hi p hpV hp0
    have hp_eq : (p.1, (0 : ℝ)) = p := by ext <;> simp [hp0]
    obtain ⟨L, hL⟩ := hlimJet i hi p.1 hpV.1
    exact ⟨L, by rwa [hp_eq] at hL⟩
  -- ** the gluing lemma **
  have hGdiff : ContDiffOn ℝ (k : ℕ∞) G V :=
    contDiffOn_glue_open hVopen hc hN hH hlim_glue
  -- ** the estimate **
  let R : ℝ := (Work.CR.Flat.holderNorm k α g S).toReal
  have hofR : ENNReal.ofReal R = Work.CR.Flat.holderNorm k α g S :=
    ENNReal.ofReal_toReal hfin
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  let AD : ℕ → ℝ := fun i => ∑ j : Fin (k + 1), |lam j| * (max 1 (eps j)) ^ i
  let AS : ℕ → ℝ := fun i => ∑ j : Fin (k + 1), |lam j| * (max 1 (eps j)) ^ ((i : ℝ) + α)
  have heta_le : ∀ j : Fin (k + 1), ‖eta (X := E) (-(eps j))‖ ≤ max 1 (eps j) := by
    intro j
    refine le_trans (norm_eta_le (-(eps j))) ?_
    rw [abs_neg, abs_of_pos (heps j)]
  have hADnn : ∀ i, 0 ≤ AD i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hASnn : ∀ i, 0 ≤ AS i := fun i =>
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hepsmax : ∀ j, 1 ≤ max 1 (eps j) := fun j => le_max_left _ _
  -- bounds on `g` from the finiteness hypothesis
  have hgnorm : ∀ (i : ℕ), i ≤ k → ∀ x ∈ S, ‖iteratedFDeriv ℝ i g x‖ ≤ R := by
    intro i hi x hx
    have h1 : Work.CR.Flat.iterDerivNorm i g S ≤ Work.CR.Flat.holderNorm k α g S :=
      Work.CR.Flat.iterDerivNorm_le_holderNorm k α g S hi
    have h2 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g S x‖ ≤ ENNReal.ofReal R := by
      rw [hofR]
      exact le_trans (Work.CR.Flat.le_iterDerivNorm i g S hx) h1
    have h3 := (ENNReal.ofReal_le_ofReal_iff hR0).mp h2
    rwa [iteratedFDerivWithin_of_isOpen i hSopen hx] at h3
  have hgdif : ∀ (i : ℕ), i ≤ k → ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ R * ‖x - y‖ ^ α := by
    intro i hi x hx y hy hxy
    have h1 : Work.CR.Flat.holderSeminorm i α g S ≤ Work.CR.Flat.holderNorm k α g S :=
      Work.CR.Flat.holderSeminorm_le_holderNorm k α g S hi
    have h2 : ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i g S x - iteratedFDerivWithin ℝ i g S y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal R := by
      rw [hofR]
      exact le_trans (Work.CR.Flat.le_holderSeminorm i α g S hx hy hxy) h1
    have h3 := (ENNReal.ofReal_le_ofReal_iff hR0).mp h2
    rw [iteratedFDerivWithin_of_isOpen i hSopen hx,
      iteratedFDerivWithin_of_isOpen i hSopen hy] at h3
    have hd : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    exact (div_le_iff₀ hd).mp h3
  -- continuity of the derivatives of `G` on `V`
  have hcontD : ∀ (i : ℕ), i ≤ k → ContinuousOn (iteratedFDeriv ℝ i G) V := fun i hi =>
    ContinuousOn.continuousOn_iteratedFDeriv hGdiff hVopen (by exact_mod_cast hi)
  have hGup_eq : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, 0 < x.2 →
      iteratedFDeriv ℝ i G x = iteratedFDeriv ℝ i g x := by
    intro i hi x hxV hx2
    have hev : G =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem
      (hSopen.mem_nhds ⟨hxV.1, hx2⟩) (fun w hw => hGupper w hw.2)
    exact (hev.iteratedFDeriv ℝ i).eq_of_nhds
  have hGN_formula : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, x.2 < 0 →
      iteratedFDeriv ℝ i G x = ∑ j : Fin (k + 1), (lam j) •
        (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
          (fun _ => eta (X := E) (-(eps j))) := by
    intro i hi x hxV hx2
    have hev : G =ᶠ[𝓝 x] reflSum eps lam g := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hx2] with w hw
      exact hGlower w hw
    rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
    exact iteratedFDeriv_reflSum hSopen hg hi eps lam (fun j => hVLmap j ⟨hxV, hx2⟩)
  -- ** sup-norm bounds **
  have hbd_U : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, 0 < x.2 →
      ‖iteratedFDeriv ℝ i G x‖ ≤ max 1 (AD i) * R := by
    intro i hi x hxV hx2
    rw [hGup_eq i hi x hxV hx2]
    exact le_trans (hgnorm i hi x ⟨hxV.1, hx2⟩)
      (le_mul_of_one_le_left hR0 (le_max_left _ _))
  have hbd_L : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, x.2 < 0 →
      ‖iteratedFDeriv ℝ i G x‖ ≤ max 1 (AD i) * R := by
    intro i hi x hxV hx2
    rw [hGN_formula i hi x hxV hx2]
    have hterm : ∀ j : Fin (k + 1),
        ‖(lam j) • (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j)))‖
        ≤ |lam j| * ((max 1 (eps j)) ^ i * R) := by
      intro j
      have hΦ : ‖iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)‖ ≤ R :=
        hgnorm i hi _ (hVLmap j ⟨hxV, hx2⟩)
      calc ‖(lam j) • (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))‖
          = |lam j| * ‖(iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |lam j| * (R * (max 1 (eps j)) ^ i) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            calc ‖(iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
                  (fun _ => eta (X := E) (-(eps j)))‖
                ≤ ‖iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)‖
                    * ∏ _ : Fin i, ‖eta (X := E) (-(eps j))‖ :=
                  ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
              _ ≤ R * (max 1 (eps j)) ^ i := by
                  have hprod : (∏ _ : Fin i, ‖eta (X := E) (-(eps j))‖)
                      = ‖eta (X := E) (-(eps j))‖ ^ i := by
                    rw [Finset.prod_const, Finset.card_fin]
                  rw [hprod]
                  exact mul_le_mul hΦ (pow_le_pow_left₀ (norm_nonneg _) (heta_le j) i)
                    (pow_nonneg (norm_nonneg _) i) hR0
        _ = |lam j| * ((max 1 (eps j)) ^ i * R) := by ring
    calc ‖∑ j : Fin (k + 1), (lam j) •
          (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j)))‖
        ≤ ∑ j : Fin (k + 1), ‖(lam j) •
            (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin (k + 1), |lam j| * ((max 1 (eps j)) ^ i * R) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = AD i * R := by
          rw [show AD i = ∑ j : Fin (k + 1), (|lam j| * (max 1 (eps j)) ^ i) from rfl,
            Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ max 1 (AD i) * R := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (AD i)) hR0
  have hbd_0 : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, x.2 = 0 →
      ‖iteratedFDeriv ℝ i G x‖ ≤ max 1 (AD i) * R := by
    intro i hi x hxV hx0
    have hcont_at : ContinuousAt (iteratedFDeriv ℝ i G) x :=
      ((hcontD i hi) x hxV).continuousAt (hVopen.mem_nhds hxV)
    have hφ : Filter.Tendsto (fun t : ℝ => (x.1, t)) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have h1 : Filter.Tendsto (fun t : ℝ => (x.1, t)) (𝓝 (0 : ℝ)) (𝓝 ((x.1, (0 : ℝ)))) :=
        (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => x.1) continuous_id).tendsto 0
      rw [show ((x.1, (0 : ℝ))) = x from Prod.ext rfl hx0.symm] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal ‖iteratedFDeriv ℝ i G (x.1, t)‖)
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal ‖iteratedFDeriv ℝ i G x‖)) :=
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp
        (hcont_at.tendsto.comp hφ)
    have hM : 0 ≤ max 1 (AD i) * R := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hR0
    refine (ENNReal.ofReal_le_ofReal_iff hM).mp ?_
    refine le_of_tendsto h1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hzVU : (x.1, t) ∈ V := by
      refine ⟨hxV.1, ?_⟩
      have ht' : (0 : ℝ) < t := ht
      have hd : (-δ : ℝ) < 0 := by linarith [hxV.2, hx0]
      exact lt_trans hd ht'
    rw [hGup_eq i hi _ hzVU ht]
    refine le_trans (ENNReal.ofReal_le_ofReal (hgnorm i hi _ ⟨hxV.1, ht⟩)) ?_
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hR0 (le_max_left _ _))
  have hsd_UU : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, 0 < x.2 → ∀ y ∈ V, 0 < y.2 → x ≠ y →
      ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖ ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
    intro i hi x hxV hx2 y hyV hy2 hxy
    rw [hGup_eq i hi x hxV hx2, hGup_eq i hi y hyV hy2]
    refine le_trans (hgdif i hi x ⟨hxV.1, hx2⟩ y ⟨hyV.1, hy2⟩ hxy) ?_
    exact one_mul_le_max_one_mul hR0 (Real.rpow_nonneg (norm_nonneg _) α)
  have hsd_LL : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, x.2 < 0 → ∀ y ∈ V, y.2 < 0 → x ≠ y →
      ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖ ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
    intro i hi x hxV hx2 y hyV hy2 hxy
    refine le_trans ?_ (le_max_one_mul_left hR0 (Real.rpow_nonneg (norm_nonneg _) α))
    rw [hGN_formula i hi x hxV hx2, hGN_formula i hi y hyV hy2]
    have hdiff : (∑ j : Fin (k + 1), (lam j) •
          (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j))))
        - (∑ j : Fin (k + 1), (lam j) •
          (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j))))
        = ∑ j : Fin (k + 1), (lam j) •
          ((iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))
            - (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (smul_sub _ _ _).symm
    rw [hdiff]
    have hterm : ∀ j : Fin (k + 1),
        ‖(lam j) • ((iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))
            - (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j))))‖
        ≤ |lam j| * ((max 1 (eps j)) ^ ((i : ℝ) + α) * R * ‖x - y‖ ^ α) := by
      intro j
      have hne : eta (X := E) (-(eps j)) x ≠ eta (X := E) (-(eps j)) y := fun h =>
        hxy (eta_injective (-(eps j)) (by have := heps j; linarith) h)
      have h1 := hgdif i hi _ (hVLmap j ⟨hxV, hx2⟩) _ (hVLmap j ⟨hyV, hy2⟩) hne
      have h3 : ‖eta (X := E) (-(eps j)) x - eta (X := E) (-(eps j)) y‖ ^ α
          ≤ (max 1 (eps j) * ‖x - y‖) ^ α := by
        refine Real.rpow_le_rpow (norm_nonneg _) ?_ (le_of_lt hα0)
        calc ‖eta (X := E) (-(eps j)) x - eta (X := E) (-(eps j)) y‖
            = ‖eta (X := E) (-(eps j)) (x - y)‖ := by rw [map_sub]
          _ ≤ ‖eta (X := E) (-(eps j))‖ * ‖x - y‖ := (eta (X := E) (-(eps j))).le_opNorm _
          _ ≤ max 1 (eps j) * ‖x - y‖ :=
              mul_le_mul_of_nonneg_right (heta_le j) (norm_nonneg _)
      have hm1 : ‖iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)‖
          ≤ R * (max 1 (eps j) * ‖x - y‖) ^ α :=
        le_trans h1 (mul_le_mul_of_nonneg_left h3 hR0)
      have hm : ‖iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)‖
              * ‖eta (X := E) (-(eps j))‖ ^ i
          ≤ (R * (max 1 (eps j) * ‖x - y‖) ^ α) * (max 1 (eps j)) ^ i :=
        mul_le_mul hm1 (pow_le_pow_left₀ (norm_nonneg _) (heta_le j) i)
          (pow_nonneg (norm_nonneg _) i) (by positivity)
      calc ‖(lam j) • ((iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j)))
            - (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j))))‖
          = |lam j| * ‖((iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
                (fun _ => eta (X := E) (-(eps j)))
              - (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
                (fun _ => eta (X := E) (-(eps j))))‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |lam j| * (R * (max 1 (eps j)) ^ ((i : ℝ) + α) * ‖x - y‖ ^ α) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            calc ‖((iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)).compContinuousLinearMap
                    (fun _ => eta (X := E) (-(eps j)))
                  - (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
                    (fun _ => eta (X := E) (-(eps j))))‖
                = ‖((iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)
                    - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
                      (fun _ => eta (X := E) (-(eps j)))‖ := by rw [compContinuousLinearMap_sub]
              _ ≤ ‖iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) x)
                    - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)‖
                    * ‖eta (X := E) (-(eps j))‖ ^ i := by
                  have hprod : (∏ _ : Fin i, ‖eta (X := E) (-(eps j))‖)
                      = ‖eta (X := E) (-(eps j))‖ ^ i := by
                    rw [Finset.prod_const, Finset.card_fin]
                  rw [← hprod]
                  exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
              _ ≤ _ := hm
              _ = R * (max 1 (eps j)) ^ ((i : ℝ) + α) * ‖x - y‖ ^ α := by
                  rw [Real.mul_rpow (le_trans zero_le_one (le_max_left 1 (eps j))) (norm_nonneg _),
                    Real.rpow_add (lt_of_lt_of_le zero_lt_one (le_max_left 1 (eps j)))]
                  rw [← Real.rpow_natCast]
                  ring
        _ = |lam j| * ((max 1 (eps j)) ^ ((i : ℝ) + α) * R * ‖x - y‖ ^ α) := by ring
    calc ‖∑ j : Fin (k + 1), (lam j) • _‖ ≤ ∑ j : Fin (k + 1), ‖(lam j) • _‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin (k + 1), |lam j| * ((max 1 (eps j)) ^ ((i : ℝ) + α) * R * ‖x - y‖ ^ α) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = AS i * R * ‖x - y‖ ^ α := by
          rw [show AS i = ∑ j : Fin (k + 1),
              (|lam j| * (max 1 (eps j)) ^ ((i : ℝ) + α)) from rfl,
            Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hsd_UL : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, 0 < x.2 → ∀ y ∈ V, y.2 < 0 →
      ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖ ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
    intro i hi x hxV hx2 y hyV hy2
    refine le_trans ?_ (le_max_one_mul_left hR0 (Real.rpow_nonneg (norm_nonneg _) α))
    rw [hGup_eq i hi x hxV hx2, hGN_formula i hi y hyV hy2]
    have hmom := etaCompMoment (k := k) hlam i hi (iteratedFDeriv ℝ i g x)
    have hdiff0 : (∑ j : Fin (k + 1), (lam j) •
          (iteratedFDeriv ℝ i g x).compContinuousLinearMap (fun _ => eta (X := E) (-(eps j))))
        - (∑ j : Fin (k + 1), (lam j) •
          (iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j))))
        = ∑ j : Fin (k + 1), (lam j) •
          ((iteratedFDeriv ℝ i g x
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [compContinuousLinearMap_sub, smul_sub]
    rw [hmom] at hdiff0
    rw [hdiff0]
    have hterm : ∀ j : Fin (k + 1),
        ‖(lam j) • ((iteratedFDeriv ℝ i g x
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j)))‖
        ≤ |lam j| * ((max 1 (eps j)) ^ ((i : ℝ) + α) * R * ‖x - y‖ ^ α) := by
      intro j
      have hcore : ‖((iteratedFDeriv ℝ i g x
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j)))‖
          ≤ R * (max 1 (eps j)) ^ ((i : ℝ) + α) * ‖x - y‖ ^ α := by
        by_cases hne : x = eta (X := E) (-(eps j)) y
        · rw [hne, sub_self]
          rw [show (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ).compContinuousLinearMap
              (fun _ => eta (X := E) (-(eps j))) = 0 from by ext v; simp]
          rw [norm_zero]
          positivity
        · have h1 := hgdif i hi x ⟨hxV.1, hx2⟩ _ (hVLmap j ⟨hyV, hy2⟩) hne
          have h3 : ‖x - eta (X := E) (-(eps j)) y‖ ^ α
              ≤ (max 1 (eps j) * ‖x - y‖) ^ α :=
            Real.rpow_le_rpow (norm_nonneg _)
              (norm_sub_eta_le (le_of_lt (heps j)) hx2 hy2) (le_of_lt hα0)
          have hm1 : ‖iteratedFDeriv ℝ i g x
                  - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)‖
              ≤ R * (max 1 (eps j) * ‖x - y‖) ^ α :=
            le_trans h1 (mul_le_mul_of_nonneg_left h3 hR0)
          have hm : ‖iteratedFDeriv ℝ i g x
                  - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)‖
                  * ‖eta (X := E) (-(eps j))‖ ^ i
              ≤ (R * (max 1 (eps j) * ‖x - y‖) ^ α) * (max 1 (eps j)) ^ i :=
            mul_le_mul hm1 (pow_le_pow_left₀ (norm_nonneg _) (heta_le j) i)
              (pow_nonneg (norm_nonneg _) i) (by positivity)
          calc ‖((iteratedFDeriv ℝ i g x
                    - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
                    (fun _ => eta (X := E) (-(eps j)))‖
              ≤ ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y)‖
                  * ‖eta (X := E) (-(eps j))‖ ^ i := by
                have hprod : (∏ _ : Fin i, ‖eta (X := E) (-(eps j))‖)
                    = ‖eta (X := E) (-(eps j))‖ ^ i := by
                  rw [Finset.prod_const, Finset.card_fin]
                rw [← hprod]
                exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
            _ ≤ _ := hm
            _ = R * (max 1 (eps j)) ^ ((i : ℝ) + α) * ‖x - y‖ ^ α := by
                rw [Real.mul_rpow (le_trans zero_le_one (le_max_left 1 (eps j))) (norm_nonneg _),
                  Real.rpow_add (lt_of_lt_of_le zero_lt_one (le_max_left 1 (eps j)))]
                rw [← Real.rpow_natCast]
                ring
      calc ‖(lam j) • ((iteratedFDeriv ℝ i g x
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j)))‖
          = |lam j| * ‖((iteratedFDeriv ℝ i g x
              - iteratedFDeriv ℝ i g (eta (X := E) (-(eps j)) y))).compContinuousLinearMap
            (fun _ => eta (X := E) (-(eps j)))‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |lam j| * (R * (max 1 (eps j)) ^ ((i : ℝ) + α) * ‖x - y‖ ^ α) :=
            mul_le_mul_of_nonneg_left hcore (abs_nonneg _)
        _ = |lam j| * ((max 1 (eps j)) ^ ((i : ℝ) + α) * R * ‖x - y‖ ^ α) := by ring
    calc ‖∑ j : Fin (k + 1), (lam j) • _‖ ≤ ∑ j : Fin (k + 1), ‖(lam j) • _‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin (k + 1), |lam j| * ((max 1 (eps j)) ^ ((i : ℝ) + α) * R * ‖x - y‖ ^ α) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = AS i * R * ‖x - y‖ ^ α := by
          rw [show AS i = ∑ j : Fin (k + 1),
              (|lam j| * (max 1 (eps j)) ^ ((i : ℝ) + α)) from rfl,
            Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hsd_all : ∀ (i : ℕ), i ≤ k → ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖ ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
    intro i hi x hxV y hyV hxy
    have hdpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    -- A one-sided Hölder estimate transfers to the hyperplane by a limiting argument.
    have hshift : ∀ (φ ψ : ℝ → E × ℝ),
        Filter.Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 x) →
        Filter.Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 y) →
        (∀ t : ℝ, 0 < t → φ t - ψ t = x - y) →
        (∀ᶠ t in 𝓝[>] (0 : ℝ), φ t ∈ V ∧ ψ t ∈ V) →
        (∀ t : ℝ, 0 < t → φ t ∈ V → ψ t ∈ V →
          ‖iteratedFDeriv ℝ i G (φ t) - iteratedFDeriv ℝ i G (ψ t)‖
            ≤ max 1 (AS i) * R * ‖x - y‖ ^ α) →
        ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖
          ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
      intro φ ψ hφ hψ hsub hmem hbd
      have hcx : ContinuousAt (iteratedFDeriv ℝ i G) x :=
        ((hcontD i hi) x hxV).continuousAt (hVopen.mem_nhds hxV)
      have hcy : ContinuousAt (iteratedFDeriv ℝ i G) y :=
        ((hcontD i hi) y hyV).continuousAt (hVopen.mem_nhds hyV)
      have hnum : Filter.Tendsto
          (fun t : ℝ => ‖iteratedFDeriv ℝ i G (φ t) - iteratedFDeriv ℝ i G (ψ t)‖
            / ‖x - y‖ ^ α)
          (𝓝[>] (0 : ℝ))
          (𝓝 (‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖ / ‖x - y‖ ^ α)) :=
        (((hcx.tendsto.comp hφ).sub (hcy.tendsto.comp hψ)).norm.div_const _)
      have hub : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          ‖iteratedFDeriv ℝ i G (φ t) - iteratedFDeriv ℝ i G (ψ t)‖ / ‖x - y‖ ^ α
            ≤ max 1 (AS i) * R := by
        filter_upwards [self_mem_nhdsWithin, hmem] with t ht hmemt
        exact (div_le_iff₀ hdpos).mpr (hbd t ht hmemt.1 hmemt.2)
      have hlim := le_of_tendsto hnum hub
      exact (div_le_iff₀ hdpos).mp hlim
    -- The two one-sided limiting schemes.
    have hside : ∀ (φ ψ : ℝ → E × ℝ),
        Filter.Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 x) →
        Filter.Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 y) →
        (∀ t : ℝ, 0 < t → φ t - ψ t = x - y) →
        (∀ t : ℝ, 0 < t → 0 < (φ t).2) → (∀ t : ℝ, 0 < t → 0 < (ψ t).2) →
        ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖
          ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
      intro φ ψ hφ hψ hsub h1 h2
      refine hshift φ ψ hφ hψ hsub ?_ ?_
      · exact (hφ.eventually (hVopen.mem_nhds hxV)).and (hψ.eventually (hVopen.mem_nhds hyV))
      · intro t ht hxtV hytV
        have hne : φ t ≠ ψ t := by
          intro h
          have h0 : φ t - ψ t = 0 := by rw [h, sub_self]
          rw [hsub t ht] at h0
          exact (sub_ne_zero.mpr hxy) h0
        have hbd := hsd_UU i hi (φ t) hxtV (h1 t ht) (ψ t) hytV (h2 t ht) hne
        rwa [hsub t ht] at hbd
    have hsideD : ∀ (φ ψ : ℝ → E × ℝ),
        Filter.Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 x) →
        Filter.Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 y) →
        (∀ t : ℝ, 0 < t → φ t - ψ t = x - y) →
        (∀ t : ℝ, 0 < t → (φ t).2 < 0) → (∀ t : ℝ, 0 < t → (ψ t).2 < 0) →
        ‖iteratedFDeriv ℝ i G x - iteratedFDeriv ℝ i G y‖
          ≤ max 1 (AS i) * R * ‖x - y‖ ^ α := by
      intro φ ψ hφ hψ hsub h1 h2
      refine hshift φ ψ hφ hψ hsub ?_ ?_
      · exact (hφ.eventually (hVopen.mem_nhds hxV)).and (hψ.eventually (hVopen.mem_nhds hyV))
      · intro t ht hxtV hytV
        have hne : φ t ≠ ψ t := by
          intro h
          have h0 : φ t - ψ t = 0 := by rw [h, sub_self]
          rw [hsub t ht] at h0
          exact (sub_ne_zero.mpr hxy) h0
        have hbd := hsd_LL i hi (φ t) hxtV (h1 t ht) (ψ t) hytV (h2 t ht) hne
        rwa [hsub t ht] at hbd
    -- The standard test sequences approaching `x` (resp. `y`) from one side.
    have tU : ∀ (v : E × ℝ), v.2 = 0 →
        Filter.Tendsto (fun t : ℝ => (v.1, t)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      intro v hv
      have h1 : Filter.Tendsto (fun t : ℝ => (v.1, t)) (𝓝 (0 : ℝ)) (𝓝 ((v.1, (0 : ℝ)))) :=
        (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => v.1) continuous_id).tendsto 0
      rw [show ((v.1, (0 : ℝ))) = v from Prod.ext rfl hv.symm] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have tD : ∀ (v : E × ℝ), v.2 = 0 →
        Filter.Tendsto (fun t : ℝ => (v.1, -t)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      intro v hv
      have h1 : Filter.Tendsto (fun t : ℝ => (v.1, -t)) (𝓝 (0 : ℝ)) (𝓝 ((v.1, -(0 : ℝ)))) :=
        (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => v.1) continuous_neg).tendsto 0
      rw [show ((v.1, -(0 : ℝ))) = v from Prod.ext rfl (by rw [neg_zero]; exact hv.symm)] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have tUp : ∀ (v : E × ℝ),
        Filter.Tendsto (fun t : ℝ => (v.1, v.2 + t)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      intro v
      have h1 : Filter.Tendsto (fun t : ℝ => (v.1, v.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((v.1, v.2 + 0))) :=
        (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => v.1)
          (continuous_const.add continuous_id)).tendsto 0
      rw [add_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have tDn : ∀ (v : E × ℝ),
        Filter.Tendsto (fun t : ℝ => (v.1, v.2 - t)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      intro v
      have h1 : Filter.Tendsto (fun t : ℝ => (v.1, v.2 - t)) (𝓝 (0 : ℝ)) (𝓝 ((v.1, v.2 - 0))) :=
        (Continuous.prodMk (continuous_const : Continuous fun _ : ℝ => v.1)
          (continuous_const.sub continuous_id)).tendsto 0
      rw [sub_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    rcases lt_trichotomy x.2 0 with hxneg | hxzero | hxpos
    · rcases lt_trichotomy y.2 0 with hyneg | hyzero | hypos
      · exact hsd_LL i hi x hxV hxneg y hyV hyneg hxy
      · refine hsideD (fun t => (x.1, x.2 - t)) (fun t => (y.1, -t))
          (tDn x) (tD y hyzero) ?_ ?_ ?_
        · intro t ht
          ext <;> simp only [Prod.fst_sub, Prod.snd_sub, hyzero] <;> ring
        · intro t ht; linarith
        · intro t ht; linarith
      · have h := hsd_UL i hi y hyV hypos x hxV hxneg
        rw [norm_sub_rev (iteratedFDeriv ℝ i G x) (iteratedFDeriv ℝ i G y), norm_sub_rev x y]
        exact h
    · rcases lt_trichotomy y.2 0 with hyneg | hyzero | hypos
      · refine hsideD (fun t => (x.1, -t)) (fun t => (y.1, y.2 - t))
          (tD x hxzero) (tDn y) ?_ ?_ ?_
        · intro t ht
          ext <;> simp only [Prod.fst_sub, Prod.snd_sub, hxzero] <;> ring
        · intro t ht; linarith
        · intro t ht; linarith
      · refine hside (fun t => (x.1, t)) (fun t => (y.1, t))
          (tU x hxzero) (tU y hyzero) ?_ ?_ ?_
        · intro t ht
          ext <;> simp only [Prod.fst_sub, Prod.snd_sub, hxzero, hyzero] <;> ring
        · intro t ht; exact ht
        · intro t ht; exact ht
      · refine hside (fun t => (x.1, t)) (fun t => (y.1, y.2 + t))
          (tU x hxzero) (tUp y) ?_ ?_ ?_
        · intro t ht
          ext <;> simp only [Prod.fst_sub, Prod.snd_sub, hxzero] <;> ring
        · intro t ht; exact ht
        · intro t ht; linarith
    · rcases lt_trichotomy y.2 0 with hyneg | hyzero | hypos
      · exact hsd_UL i hi x hxV hxpos y hyV hyneg
      · refine hside (fun t => (x.1, x.2 + t)) (fun t => (y.1, t))
          (tUp x) (tU y hyzero) ?_ ?_ ?_
        · intro t ht
          ext <;> simp only [Prod.fst_sub, Prod.snd_sub, hyzero] <;> ring
        · intro t ht; linarith
        · intro t ht; exact ht
      · exact hsd_UU i hi x hxV hxpos y hyV hypos hxy
  -- ** the final estimates **
  have hdn : ∀ (i : ℕ), i ≤ k →
      Work.NN.Final.gDN i G V ≤ ENNReal.ofReal (max 1 (AD i) * R) := by
    intro i hi
    refine iSup₂_le fun x hx => ?_
    rcases lt_trichotomy x.2 0 with h | h | h
    · exact ENNReal.ofReal_le_ofReal (hbd_L i hi x hx h)
    · exact ENNReal.ofReal_le_ofReal (hbd_0 i hi x hx h)
    · exact ENNReal.ofReal_le_ofReal (hbd_U i hi x hx h)
  have hsn : ∀ (i : ℕ), i ≤ k →
      Work.NN.Final.gSN i α G V ≤ ENNReal.ofReal (max 1 (AS i) * R) := by
    intro i hi
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    exact (div_le_iff₀
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)).mpr
      (hsd_all i hi x hx y hy hxy)
  have hsplit : Work.CR.Flat.holderNorm k α G V
      = ∑ i ∈ Finset.range (k + 1),
          (Work.NN.Final.gDN i G V + Work.NN.Final.gSN i α G V) := by
    unfold Work.CR.Flat.holderNorm
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · exact (Work.CR.Flat.Holder.iDN_complex_eq i G V).symm.trans
        (Work.NN.Final.gDN_eq_iDN hVopen i G).symm
    · exact (Work.CR.Flat.Holder.hSN_complex_eq i α G V).symm.trans
        (Work.NN.Final.gSN_eq_hSN hVopen i α G).symm
  refine ⟨G, hGdiff, hGg, ?_⟩
  rw [hsplit, ← hofR]
  have hA : ∀ i, 0 ≤ max 1 (AD i) := fun i => le_trans zero_le_one (le_max_left _ _)
  have hS : ∀ i, 0 ≤ max 1 (AS i) := fun i => le_trans zero_le_one (le_max_left _ _)
  have hT : 0 ≤ ∑ i ∈ Finset.range (k + 1), (max 1 (AD i) + max 1 (AS i)) :=
    Finset.sum_nonneg fun i _ => add_nonneg (hA i) (hS i)
  have hTex : extConst k α
      = max 1 (∑ i ∈ Finset.range (k + 1), (max 1 (AD i) + max 1 (AS i))) := rfl
  calc ∑ i ∈ Finset.range (k + 1), (Work.NN.Final.gDN i G V + Work.NN.Final.gSN i α G V)
      ≤ ∑ i ∈ Finset.range (k + 1),
          (ENNReal.ofReal (max 1 (AD i) * R) + ENNReal.ofReal (max 1 (AS i) * R)) :=
        Finset.sum_le_sum fun i hi' =>
          add_le_add (hdn i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')))
            (hsn i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')))
    _ = ENNReal.ofReal
          ((∑ i ∈ Finset.range (k + 1), (max 1 (AD i) + max 1 (AS i))) * R) := by
        rw [Finset.sum_add_distrib,
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hA i) hR0),
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hS i) hR0),
          ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => mul_nonneg (hA i) hR0)
            (Finset.sum_nonneg fun i _ => mul_nonneg (hS i) hR0),
          ← Finset.sum_add_distrib]
        rw [Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ENNReal.ofReal (extConst k α) * ENNReal.ofReal R := by
        have hE : (0 : ℝ) ≤ max 1
            (∑ i ∈ Finset.range (k + 1), (max 1 (AD i) + max 1 (AS i))) :=
          le_trans hT (le_max_right 1 _)
        rw [hTex, ← ENNReal.ofReal_mul hE]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right 1 _) hR0)

end Extension

/-! ## The one-sided extension theorem -/

theorem flatOneSidedExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (W : Set E) (g : E × ℝ → ℂ),
        IsOpen W →
        ContDiffOn ℝ (k : WithTop ENat) g (W ×ˢ {t : ℝ | 0 < t}) →
        Work.CR.Flat.holderNorm k α g (W ×ˢ {t : ℝ | 0 < t}) ≠ ⊤ →
        ∃ G : E × ℝ → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) G (W ×ˢ {t : ℝ | -δ < t}) ∧
          (∀ p, p.1 ∈ W → 0 < p.2 → G p = g p) ∧
          Work.CR.Flat.holderNorm k α G (W ×ˢ {t : ℝ | -δ < t})
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (W ×ˢ {t : ℝ | 0 < t}) := by
  refine ⟨fun k => extConst k α, fun k => extConst_pos k α, ?_⟩
  intro k W g hW hg hfin
  exact flatExtensionConst hα0 hδ k W g hW hg hfin

end Work.NN.Final



