/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Local helper lemmas for the radial disc extension

This file collects the shared tools used by `Submission/Work/NN/DiscRadial/disc_ext_contDiffOn`:

* `glueOpen_local` — the localised gluing lemma across a hyperplane, copied (unchanged in proof)
  from `Work.NN.Final.contDiffOn_glue_open` in `Submission/Work/NN/Final/flatOneSidedExtension.lean`,
  which cannot be imported because that file currently fails to compile
  (`flatOneSidedExtension.lean:703`).  It is reproduced here verbatim so that this development
  depends only on compiling modules.

* `finite_moment_tensor` — the finite multilinear moment identity which drives the jet matching
  of the radial Seeley extension.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.contDiffOn_glue
import Submission.Work.NN.Final.holderDerivTendsto
import Submission.Work.NN.Final.eta
import Submission.Work.NN.Seeley.seeley_moment_tensor
import Submission.Work.NN.Final.DiscRadialDefs

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
open Metric

namespace Work.NN.DiscRadial

open Work.NN.Final

theorem glueOpen_local {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
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


/-! ## The finite multilinear moment identity -/

/-- **Finite multilinear moment identity.**  If the real weights `lam i` at the positive nodes
`eps i` reproduce the functional `p ↦ p 0` ... more precisely satisfy
`∑ i, lam i * (-(eps i))^j = 1` for `j ≤ k`, then for every continuous multilinear `Φ` of degree
`k` the weighted sum of the precompositions with the reflections `v ↦ (v.1, -(eps i) * v.2)`
is `Φ` itself. -/
theorem finite_moment_tensor {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n k : ℕ} (eps lam : Fin n → ℝ)
    (ha : ∀ j, j ≤ k → ∑ i, lam i * (-(eps i)) ^ j = 1)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) (v : Fin k → X × ℝ) :
    ∑ i, lam i • Φ (fun j => ((v j).1, -(eps i) * (v j).2)) = Φ v := by
  classical
  have hexp : ∀ s : ℝ, Φ (fun j => ((v j).1, s * (v j).2))
      = ∑ t : Finset (Fin k), s ^ t.card • Work.NN.Seeley.seeleyCoef Φ v t :=
    fun s => Work.NN.Seeley.phi_expansion Φ v s
  have hv : Φ v = ∑ t : Finset (Fin k), Work.NN.Seeley.seeleyCoef Φ v t := by
    have h := hexp 1
    rw [show (fun j : Fin k => ((v j).1, (1 : ℝ) * (v j).2)) = v from by funext j; simp] at h
    simpa using h
  calc ∑ i, lam i • Φ (fun j => ((v j).1, -(eps i) * (v j).2))
      = ∑ i, ∑ t : Finset (Fin k), (lam i * (-(eps i)) ^ t.card) •
          Work.NN.Seeley.seeleyCoef Φ v t := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hexp (-(eps i)), Finset.smul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
    _ = ∑ t : Finset (Fin k), (∑ i, lam i * (-(eps i)) ^ t.card) •
          Work.NN.Seeley.seeleyCoef Φ v t := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
    _ = ∑ t : Finset (Fin k), Work.NN.Seeley.seeleyCoef Φ v t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [ha t.card (by simpa using Finset.card_le_univ t), one_smul]
    _ = Φ v := hv.symm

/-- The same identity, in the form used by the jet computation: the weighted sum of the
compositions with the linear maps `eta (-(eps i))` is the identity. -/
theorem finite_moment_tensor_clm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n k : ℕ} (eps lam : Fin n → ℝ)
    (ha : ∀ j, j ≤ k → ∑ i, lam i * (-(eps i)) ^ j = 1)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) ℂ) :
    ∑ i, lam i • Φ.compContinuousLinearMap
        (fun _ => Work.NN.Final.eta (X := X) (-(eps i))) = Φ := by
  ext v
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, Work.NN.Final.eta_apply]
  exact finite_moment_tensor eps lam ha Φ v

end Work.NN.DiscRadial
