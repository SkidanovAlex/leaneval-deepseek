import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.contDiffOn_glue

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace Work.NN.Final

/-- If `f` agrees with `0` near `w`, then all its iterated derivatives at `w` vanish. -/
lemma iteratedFDeriv_eq_zero_of_eventuallyEq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℂ} {w : E} (hf : f =ᶠ[𝓝 w] (fun _ => 0)) (n : ℕ) :
    iteratedFDeriv ℝ n f w = 0 := by
  rw [(hf.iteratedFDeriv ℝ n).self_of_nhds]
  cases n with
  | zero => simp [iteratedFDeriv_zero_eq_comp]
  | succ n => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

theorem extensionByZeroBall {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {c : ℝ} (hc : 1 < c) {U : Set X} (hU : IsOpen U) (hUc : Convex ℝ U) (h : X × ℂ → ℂ)
    (hzero : ∀ p : X × ℂ, ¬ (p.1 ∈ U ∧ ‖p.2‖ < 1) → h p = 0)
    (hC : ContDiffOn ℝ (k : WithTop ENat) h (U ×ˢ Metric.ball (0 : ℂ) 1))
    (hvan : ∀ (i : ℕ), i ≤ k → ∀ p : X × ℂ, p.1 ∈ U → ‖p.2‖ = 1 →
      Filter.Tendsto
        (fun q : X × ℂ =>
          iteratedFDerivWithin ℝ i h (U ×ˢ Metric.ball (0 : ℂ) 1) q)
        (nhdsWithin p (U ×ˢ Metric.ball (0 : ℂ) 1)) (nhds 0)) :
    ContDiffOn ℝ (k : WithTop ENat) h (U ×ˢ Metric.ball (0 : ℂ) c) := by
  classical
  set A : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) 1 with hAdef
  set W : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) c with hWdef
  set Out : Set (X × ℂ) := {w : X × ℂ | (1 : ℝ) < ‖w.2‖} with hOutdef
  have hA_open : IsOpen A := by rw [hAdef]; exact hU.prod isOpen_ball
  have hA_conv : Convex ℝ A := by rw [hAdef]; exact hUc.prod (convex_ball _ _)
  have hW_open : IsOpen W := by rw [hWdef]; exact hU.prod isOpen_ball
  have hOut_open : IsOpen Out := by
    rw [hOutdef]; exact isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hmemA : ∀ z : X × ℂ, z ∈ A ↔ z.1 ∈ U ∧ ‖z.2‖ < 1 := by
    intro z; rw [hAdef, mem_prod]
    exact ⟨fun h => ⟨h.1, by simpa [dist_eq_norm] using h.2⟩,
           fun h => ⟨h.1, by simpa [dist_eq_norm] using h.2⟩⟩
  have hmemW : ∀ z : X × ℂ, z ∈ W ↔ z.1 ∈ U ∧ ‖z.2‖ < c := by
    intro z; rw [hWdef, mem_prod]
    exact ⟨fun h => ⟨h.1, by simpa [dist_eq_norm] using h.2⟩,
           fun h => ⟨h.1, by simpa [dist_eq_norm] using h.2⟩⟩
  have hmemOut : ∀ z : X × ℂ, z ∈ Out ↔ (1 : ℝ) < ‖z.2‖ := by
    intro z; rw [hOutdef]; rfl
  -- The candidate Taylor series `P`: the limits (all `0`) on the sphere, the actual
  -- iterated derivative elsewhere.
  set P : (X × ℂ) → FormalMultilinearSeries ℝ (X × ℂ) ℂ :=
    fun y i => if y.1 ∈ U ∧ ‖y.2‖ = 1 then 0 else iteratedFDeriv ℝ i h y with hPdef
  have hP_ne : ∀ (y : X × ℂ) (i : ℕ), ¬(y.1 ∈ U ∧ ‖y.2‖ = 1) →
      P y i = iteratedFDeriv ℝ i h y := by
    intro y i hy; rw [hPdef]; exact dif_neg hy
  have hP_bd : ∀ (y : X × ℂ) (i : ℕ), (y.1 ∈ U ∧ ‖y.2‖ = 1) → P y i = 0 := by
    intro y i hy; rw [hPdef]; exact dif_pos hy
  have hnotbd_of_A : ∀ w : X × ℂ, w ∈ A → ¬(w.1 ∈ U ∧ ‖w.2‖ = 1) := by
    intro w hw; obtain ⟨_, hlt⟩ := (hmemA w).mp hw; rintro ⟨_, h1⟩; linarith
  have hnotbd_of_Out : ∀ w : X × ℂ, w ∈ Out → ¬(w.1 ∈ U ∧ ‖w.2‖ = 1) := by
    intro w hw; have h1 := (hmemOut w).mp hw; rintro ⟨_, h2⟩; linarith
  have hOut_deriv : ∀ (w : X × ℂ) (n : ℕ), (1 : ℝ) < ‖w.2‖ →
      iteratedFDeriv ℝ n h w = 0 := by
    intro w n hw
    have heq : h =ᶠ[𝓝 w] (fun _ => 0) :=
      Filter.eventuallyEq_of_mem (hOut_open.mem_nhds ((hmemOut w).mpr hw))
        (fun v hv => hzero v (by have := (hmemOut v).mp hv; rintro ⟨_, h1⟩; linarith))
    exact iteratedFDeriv_eq_zero_of_eventuallyEq_zero heq n
  have hsphere_cl : ∀ z : ℂ, ‖z‖ = 1 → z ∈ closure (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right]
    exact le_of_eq hz
  have hcurl : ∀ (i : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin (i+1) => X × ℂ) ℂ),
      L.curryLeft = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i+1) => X × ℂ) ℂ) L :=
    fun i L => rfl
  -- The main local statement: on every closed ball inside `W`, `P` is a Taylor series for `h`.
  have key : ∀ (q : X × ℂ) (r : ℝ), 0 < r → closedBall q r ⊆ W →
      HasFTaylorSeriesUpToOn (k : ℕ∞ω) h P (ball q r) := by
    intro q r hr hsub
    have hU_ball : ∀ z ∈ ball q r, z.1 ∈ U :=
      fun z hz => ((hmemW z).mp (hsub (ball_subset_closedBall hz))).1
    have hU_cl : ∀ z ∈ closedBall q r, z.1 ∈ U := fun z hz => ((hmemW z).mp (hsub hz)).1
    set Bin : Set (X × ℂ) := ball q r ∩ A with hBindef
    set Bout : Set (X × ℂ) := ball q r ∩ Out with hBoutdef
    have hBin_mem : ∀ w : X × ℂ, w ∈ Bin ↔ w ∈ ball q r ∧ w ∈ A :=
      fun w => by rw [hBindef, mem_inter_iff]
    have hBout_mem : ∀ w : X × ℂ, w ∈ Bout ↔ w ∈ ball q r ∧ w ∈ Out :=
      fun w => by rw [hBoutdef, mem_inter_iff]
    have hBin_sub_A : Bin ⊆ A := fun w hw => (hBin_mem w).mp hw |>.2
    have hBin_sub_ball : Bin ⊆ ball q r := fun w hw => (hBin_mem w).mp hw |>.1
    have hBin_of_lt : ∀ w ∈ ball q r, ‖w.2‖ < 1 → w ∈ Bin := by
      intro w hw hlt; rw [hBin_mem]; exact ⟨hw, (hmemA w).mpr ⟨hU_ball w hw, hlt⟩⟩
    have hBout_of_gt : ∀ w ∈ ball q r, (1 : ℝ) < ‖w.2‖ → w ∈ Bout := by
      intro w hw hlt; rw [hBout_mem]; exact ⟨hw, (hmemOut w).mpr hlt⟩
    have hBin_open : IsOpen Bin := by rw [hBindef]; exact isOpen_ball.inter hA_open
    have hBin_conv : Convex ℝ Bin := by rw [hBindef]; exact (convex_ball q r).inter hA_conv
    have hBout_open : IsOpen Bout := by rw [hBoutdef]; exact isOpen_ball.inter hOut_open
    have hclBin_ball : closure Bin ⊆ closedBall q r := by
      rw [← closure_ball q hr.ne']; exact closure_mono hBin_sub_ball
    have hclBin_le : closure Bin ⊆ {z : X × ℂ | ‖z.2‖ ≤ 1} := by
      apply closure_minimal
      · intro z hz; exact le_of_lt ((hmemA z).mp (hBin_sub_A hz)).2
      · exact isClosed_le (continuous_norm.comp continuous_snd) continuous_const
    have hclBout_ball : closure Bout ⊆ closedBall q r := by
      rw [← closure_ball q hr.ne']
      exact closure_mono (fun w hw => (hBout_mem w).mp hw |>.1)
    have hclBout_ge : closure Bout ⊆ {z : X × ℂ | (1 : ℝ) ≤ ‖z.2‖} := by
      apply closure_minimal
      · intro z hz; exact le_of_lt ((hmemOut z).mp ((hBout_mem z).mp hz).2)
      · exact isClosed_le continuous_const (continuous_norm.comp continuous_snd)
    have hcover : ball q r ⊆ closure Bin ∪ closure Bout := by
      intro w hw
      have hwU : w.1 ∈ U := hU_ball w hw
      by_cases hlt : ‖w.2‖ < 1
      · exact Or.inl (subset_closure (hBin_of_lt w hw hlt))
      · rw [not_lt] at hlt
        rcases lt_or_eq_of_le hlt with hgt | heq
        · exact Or.inr (subset_closure (hBout_of_gt w hw hgt))
        · left
          have hwclA : w ∈ closure A := by
            rw [hAdef, closure_prod_eq]
            exact ⟨subset_closure hwU, hsphere_cl w.2 heq.symm⟩
          rw [hBindef]
          exact isOpen_ball.inter_closure ⟨hw, hwclA⟩
    refine ⟨?_, ?_, ?_⟩
    · -- field 1: `P y 0 = h y` on the ball
      intro y hy
      by_cases hbd : y.1 ∈ U ∧ ‖y.2‖ = 1
      · rw [hP_bd y 0 hbd, hzero y (by rintro ⟨_, h1⟩; linarith [hbd.2])]
        simp
      · rw [hP_ne y 0 hbd]
        simp
    · -- field 2: derivative compatibility
      intro m hm y hy
      have hmk : m < k := by exact_mod_cast hm
      have hmk1 : m + 1 ≤ k := by omega
      by_cases hbd : y.1 ∈ U ∧ ‖y.2‖ = 1
      · -- boundary point of the ball
        have htarget : (P y m.succ).curryLeft = 0 := by
          rw [hP_bd y m.succ hbd]
          change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin m.succ => X × ℂ) ℂ) 0 = 0
          exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin m.succ => X × ℂ) ℂ).map_zero
        rw [htarget]
        have hAin : HasFDerivWithinAt (fun w => P w m) (0 : (X × ℂ) →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ)) (closure Bin) y := by
          refine hasFDerivWithinAt_closure_of_tendsto_fderiv ?_ hBin_conv hBin_open ?_ ?_
          · intro z hz
            have hzA : z ∈ A := (hBin_mem z).mp hz |>.2
            have hev : (fun w => P w m) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ m h w) :=
              Filter.eventuallyEq_of_mem (hA_open.mem_nhds hzA)
                (fun w hw => hP_ne w m (hnotbd_of_A w hw))
            have hcd : ContDiffAt ℝ (k : ℕ∞ω) h z := hC.contDiffAt (hA_open.mem_nhds hzA)
            have hcd1 : ContDiffAt ℝ (1 : ℕ∞ω) (iteratedFDeriv ℝ m h) z :=
              hcd.iteratedFDeriv_right (m := 1) (by exact_mod_cast (by omega : 1 + m ≤ k))
            have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ m h) z :=
              hcd1.differentiableAt (by norm_num)
            exact (hdiffit.congr_of_eventuallyEq hev).differentiableWithinAt
          · intro z hz
            have hzU : z.1 ∈ U := hU_cl z (hclBin_ball hz)
            have hzle : ‖z.2‖ ≤ 1 := hclBin_le hz
            rcases lt_or_eq_of_le hzle with hzlt | hz0
            · have hzA : z ∈ A := (hmemA z).mpr ⟨hzU, hzlt⟩
              have hev : (fun w => P w m) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ m h w) :=
                Filter.eventuallyEq_of_mem (hA_open.mem_nhds hzA)
                  (fun w hw => hP_ne w m (hnotbd_of_A w hw))
              have hc : ContinuousAt (fun w => iteratedFDeriv ℝ m h w) z :=
                (ContinuousOn.continuousOn_iteratedFDeriv hC hA_open
                  (by exact_mod_cast (le_of_lt hmk))).continuousAt (hA_open.mem_nhds hzA)
              exact (hc.congr_of_eventuallyEq hev).continuousWithinAt
            · show Tendsto (fun w => P w m) (𝓝[Bin] z) (𝓝 (P z m))
              rw [hP_bd z m ⟨hzU, hz0⟩]
              have h2 : Tendsto (fun w => iteratedFDeriv ℝ m h w) (𝓝[Bin] z) (𝓝 0) := by
                refine Tendsto.congr' ?_ ((hvan m (le_of_lt hmk) z hzU hz0).mono_left
                  (nhdsWithin_mono z hBin_sub_A))
                filter_upwards [self_mem_nhdsWithin] with w hw
                exact iteratedFDerivWithin_of_isOpen m hA_open ((hBin_mem w).mp hw).2
              refine Tendsto.congr' ?_ h2
              filter_upwards [self_mem_nhdsWithin] with w hw
              exact (hP_ne w m (hnotbd_of_A w ((hBin_mem w).mp hw).2)).symm
          · have hev : (fun z => fderiv ℝ (fun w => P w m) z) =ᶠ[𝓝[Bin] y]
                (fun z => (iteratedFDeriv ℝ (m+1) h z).curryLeft) := by
              filter_upwards [self_mem_nhdsWithin] with z hz
              have hzA : z ∈ A := (hBin_mem z).mp hz |>.2
              have hev2 : (fun w => P w m) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ m h w) :=
                Filter.eventuallyEq_of_mem (hA_open.mem_nhds hzA)
                  (fun w hw => hP_ne w m (hnotbd_of_A w hw))
              rw [Filter.EventuallyEq.fderiv_eq hev2, fderiv_iteratedFDeriv]
              simp only [Function.comp_apply]
              exact (hcurl m (iteratedFDeriv ℝ (m+1) h z)).symm
            refine Tendsto.congr' hev.symm ?_
            have h3 : Tendsto (fun z => iteratedFDeriv ℝ (m+1) h z) (𝓝[Bin] y) (𝓝 0) := by
              refine Tendsto.congr' ?_ ((hvan (m+1) hmk1 y hbd.1 hbd.2).mono_left
                (nhdsWithin_mono y hBin_sub_A))
              filter_upwards [self_mem_nhdsWithin] with w hw
              exact iteratedFDerivWithin_of_isOpen (m+1) hA_open ((hBin_mem w).mp hw).2
            have h4 := (continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (m+1) => X × ℂ) ℂ).continuous.continuousAt.tendsto.comp h3
            have h0 : (continuousMultilinearCurryLeftEquiv ℝ
                (fun _ : Fin (m+1) => X × ℂ) ℂ) 0 = 0 :=
              (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => X × ℂ) ℂ).map_zero
            rw [h0] at h4
            change Tendsto ((continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (m+1) => X × ℂ) ℂ) ∘ fun z => iteratedFDeriv ℝ (m+1) h z)
              (𝓝[Bin] y) (𝓝 0)
            exact h4
        have hBout : HasFDerivWithinAt (fun w => P w m) (0 : (X × ℂ) →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ)) (closure Bout) y := by
          refine (hasFDerivWithinAt_const (𝕜 := ℝ) (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ) y (closure Bout)).congr ?_ ?_
          · intro w hw
            have hwU : w.1 ∈ U := hU_cl w (hclBout_ball hw)
            have hwge : (1 : ℝ) ≤ ‖w.2‖ := hclBout_ge hw
            show P w m = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ)
            rcases lt_or_eq_of_le hwge with hgt | heq
            · rw [hP_ne w m (by rintro ⟨_, h1⟩; linarith), hOut_deriv w m hgt]
            · rw [hP_bd w m ⟨hwU, heq.symm⟩]
          · exact hP_bd y m hbd
        exact (hAin.union hBout).mono hcover
      · -- non-boundary point
        have hyU : y.1 ∈ U := hU_ball y hy
        have hyne : ‖y.2‖ ≠ 1 := fun h1 => hbd ⟨hyU, h1⟩
        rcases lt_or_gt_of_ne hyne with hlt | hgt
        · have hyA : y ∈ A := (hmemA y).mpr ⟨hyU, hlt⟩
          have hev2 : (fun w => P w m) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ m h w) :=
            Filter.eventuallyEq_of_mem (hA_open.mem_nhds hyA)
              (fun w hw => hP_ne w m (hnotbd_of_A w hw))
          have hcd : ContDiffAt ℝ (k : ℕ∞ω) h y := hC.contDiffAt (hA_open.mem_nhds hyA)
          have hcd1 : ContDiffAt ℝ (1 : ℕ∞ω) (iteratedFDeriv ℝ m h) y :=
            hcd.iteratedFDeriv_right (m := 1) (by exact_mod_cast (by omega : 1 + m ≤ k))
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ m h) y :=
            hcd1.differentiableAt (by norm_num)
          have hdiff : DifferentiableAt ℝ (fun w => P w m) y :=
            hdiffit.congr_of_eventuallyEq hev2
          have hfd : fderiv ℝ (fun w => P w m) y = (P y m.succ).curryLeft := by
            rw [Filter.EventuallyEq.fderiv_eq hev2, fderiv_iteratedFDeriv]
            rw [hP_ne y m.succ (by rintro ⟨_, h1⟩; linarith)]
            exact (hcurl m (iteratedFDeriv ℝ m.succ h y)).symm
          have h1 : HasFDerivWithinAt (fun w => P w m) (fderiv ℝ (fun w => P w m) y)
              (ball q r) y := hdiff.hasFDerivAt.hasFDerivWithinAt
          rwa [hfd] at h1
        · have hyO : y ∈ Out := (hmemOut y).mpr hgt
          have hev0 : (fun w => P w m) =ᶠ[𝓝 y] (fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ)) := by
            refine Filter.eventuallyEq_of_mem (hOut_open.mem_nhds hyO) ?_
            intro w hw
            show P w m = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ)
            rw [hP_ne w m (hnotbd_of_Out w hw)]
            exact hOut_deriv w m ((hmemOut w).mp hw)
          have hdiff : DifferentiableAt ℝ (fun w => P w m) y :=
            (differentiableAt_const (𝕜 := ℝ) (c := (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ))).congr_of_eventuallyEq hev0
          have hfd : fderiv ℝ (fun w => P w m) y = (P y m.succ).curryLeft := by
            have h0 : fderiv ℝ (fun w => P w m) y = 0 := by
              rw [Filter.EventuallyEq.fderiv_eq hev0]
              simp
            rw [h0, hP_ne y m.succ (by rintro ⟨_, h1⟩; linarith), hOut_deriv y m.succ hgt]
            exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin m.succ => X × ℂ) ℂ).map_zero).symm
          have h1 : HasFDerivWithinAt (fun w => P w m) (fderiv ℝ (fun w => P w m) y)
              (ball q r) y := hdiff.hasFDerivAt.hasFDerivWithinAt
          rwa [hfd] at h1
    · -- field 3: continuity of the coefficients
      intro m hm
      have hmk : m ≤ k := by exact_mod_cast hm
      intro y hy
      by_cases hbd : y.1 ∈ U ∧ ‖y.2‖ = 1
      · -- boundary point
        have hyU : y.1 ∈ U := hU_ball y hy
        have hysph : ‖y.2‖ = 1 := hbd.2
        set H : Set (X × ℂ) := ball q r ∩ {w : X × ℂ | ‖w.2‖ = 1} with hHdef
        have hH_mem : ∀ w : X × ℂ, w ∈ H ↔ w ∈ ball q r ∧ ‖w.2‖ = 1 :=
          fun w => by rw [hHdef, mem_inter_iff, mem_ofPred_eq]
        have hΩH : (Bin ∪ Bout) ∪ H = ball q r := by
          ext w
          constructor
          · rintro ((hw | hw) | hw)
            · exact (hBin_mem w).mp hw |>.1
            · exact (hBout_mem w).mp hw |>.1
            · exact (hH_mem w).mp hw |>.1
          · intro hw
            have hwU : w.1 ∈ U := hU_ball w hw
            by_cases h1 : ‖w.2‖ = 1
            · right; exact (hH_mem w).mpr ⟨hw, h1⟩
            · rcases lt_or_gt_of_ne h1 with hlt | hgt
              · left; left; exact hBin_of_lt w hw hlt
              · left; right; exact hBout_of_gt w hw hgt
        have hcl : ∀ z ∈ H, z ∈ closure (Bin ∪ Bout) := by
          intro z hz
          obtain ⟨hzball, hzsph⟩ := (hH_mem z).mp hz
          have hzclBin : z ∈ closure Bin := by
            have hzclA : z ∈ closure A := by
              rw [hAdef, closure_prod_eq]
              exact ⟨subset_closure (hU_ball z hzball), hsphere_cl z.2 hzsph⟩
            rw [hBindef]
            exact isOpen_ball.inter_closure ⟨hzball, hzclA⟩
          exact closure_mono subset_union_left hzclBin
        have hlim : ∀ z ∈ H, Tendsto (fun w => iteratedFDeriv ℝ m h w) (𝓝[Bin ∪ Bout] z)
            (𝓝 (P z m)) := by
          intro z hz
          obtain ⟨hzball, hzsph⟩ := (hH_mem z).mp hz
          have hzU : z.1 ∈ U := hU_ball z hzball
          rw [hP_bd z m ⟨hzU, hzsph⟩, nhdsWithin_union]
          refine tendsto_sup.mpr ⟨?_, ?_⟩
          · refine Tendsto.congr' ?_ ((hvan m hmk z hzU hzsph).mono_left
              (nhdsWithin_mono z hBin_sub_A))
            filter_upwards [self_mem_nhdsWithin] with w hw
            exact iteratedFDerivWithin_of_isOpen m hA_open ((hBin_mem w).mp hw).2
          · refine Tendsto.congr' ?_ (tendsto_const_nhds :
              Tendsto (fun _ : X × ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => X × ℂ) ℂ)) (𝓝[Bout] z) (𝓝 0))
            filter_upwards [self_mem_nhdsWithin] with w hw
            exact (hOut_deriv w m ((hmemOut w).mp ((hBout_mem w).mp hw).2)).symm
        have hcont : ContinuousAt (fun w => P w m) y :=
          continuousAt_of_tendsto_nhdsWithin
            (Ω := Bin ∪ Bout) (H := H)
            (f := fun w => iteratedFDeriv ℝ m h w) (g := fun w => P w m)
            (fun w hw => by
              rcases hw with hw | hw
              · exact hP_ne w m (hnotbd_of_A w ((hBin_mem w).mp hw).2)
              · exact hP_ne w m (hnotbd_of_Out w ((hBout_mem w).mp hw).2))
            ((hH_mem y).mpr ⟨hy, hysph⟩)
            (by rw [hΩH]; exact isOpen_ball.mem_nhds hy)
            hcl hlim
        exact hcont.continuousWithinAt
      · -- non-boundary point
        have hyU : y.1 ∈ U := hU_ball y hy
        have hyne : ‖y.2‖ ≠ 1 := fun h1 => hbd ⟨hyU, h1⟩
        rcases lt_or_gt_of_ne hyne with hlt | hgt
        · have hyA : y ∈ A := (hmemA y).mpr ⟨hyU, hlt⟩
          have hev : (fun w => P w m) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ m h w) :=
            Filter.eventuallyEq_of_mem (hA_open.mem_nhds hyA)
              (fun w hw => hP_ne w m (hnotbd_of_A w hw))
          have hc : ContinuousAt (fun w => iteratedFDeriv ℝ m h w) y :=
            (ContinuousOn.continuousOn_iteratedFDeriv hC hA_open
              (by exact_mod_cast hmk)).continuousAt (hA_open.mem_nhds hyA)
          exact (hc.congr_of_eventuallyEq hev).continuousWithinAt
        · have hyO : y ∈ Out := (hmemOut y).mpr hgt
          have hev : (fun w => P w m) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ m h w) :=
            Filter.eventuallyEq_of_mem (hOut_open.mem_nhds hyO)
              (fun w hw => hP_ne w m (hnotbd_of_Out w hw))
          have hOut_diff : ContDiffOn ℝ (m : ℕ∞ω) h Out :=
            (contDiffOn_const (c := (0 : ℂ))).congr
              (fun w hw => hzero w (by have := (hmemOut w).mp hw; rintro ⟨_, h1⟩; linarith))
          have hc : ContinuousAt (fun w => iteratedFDeriv ℝ m h w) y :=
            (ContinuousOn.continuousOn_iteratedFDeriv hOut_diff hOut_open le_rfl).continuousAt
              (hOut_open.mem_nhds hyO)
          exact (hc.congr_of_eventuallyEq hev).continuousWithinAt
  -- Assemble: `ContDiffOn` on `W` by the local Taylor-series criterion.
  change ∀ p ∈ W, ContDiffWithinAt ℝ (k : WithTop ENat) h W p
  intro p hp
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hW_open.mem_nhds hp)
  have hr2 : 0 < r / 2 := by linarith
  have hsub : closedBall p (r / 2) ⊆ W :=
    subset_trans (closedBall_subset_ball (by linarith)) hrs
  refine contDiffWithinAt_nat.mpr
    ⟨ball p (r / 2), mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr2)),
      P, key p (r / 2) hr2 hsub⟩

end Work.NN.Final
