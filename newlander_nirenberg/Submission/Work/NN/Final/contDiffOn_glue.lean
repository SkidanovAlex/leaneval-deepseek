import Mathlib
import Submission.Work.NN.Final.continuousAt_of_tendsto_nhdsWithin

noncomputable section
open Set Filter
open scoped ContDiff Topology
open Metric

namespace Work.NN.Final

lemma convex_snd_pos {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Convex ℝ {z : X × ℝ | (0 : ℝ) < z.2} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hx hy ⊢
  nlinarith [mul_pos ha hx, mul_pos hb hy]

lemma convex_snd_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Convex ℝ {z : X × ℝ | z.2 < (0 : ℝ)} := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hx hy ⊢
  nlinarith [mul_neg_of_pos_of_neg ha hx, mul_neg_of_pos_of_neg hb hy]

lemma mem_closure_ball_inter_pos {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {q z : X × ℝ} {r : ℝ} (hz : z ∈ ball q r) (hz0 : z.2 = 0) :
    z ∈ closure (ball q r ∩ {w : X × ℝ | (0 : ℝ) < w.2}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r', hr', hr'sub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hz)
  have h2 : (0 : ℝ) < min ε r' := lt_min hε hr'
  refine ⟨z + (0, min ε r' / 2), ⟨hr'sub ?_, ?_⟩, ?_⟩
  · have h1 : min ε r' ≤ r' := min_le_right _ _
    rw [mem_ball, dist_eq_norm,
      show z + (0, min ε r' / 2) - z = (0, min ε r' / 2) from by simp,
      Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  · rw [Set.mem_ofPred_eq, Prod.snd_add, hz0, zero_add]; positivity
  · have h1 : min ε r' ≤ ε := min_le_left _ _
    rw [dist_comm, dist_eq_norm,
      show z + (0, min ε r' / 2) - z = (0, min ε r' / 2) from by simp,
      Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith

lemma mem_closure_ball_inter_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {q z : X × ℝ} {r : ℝ} (hz : z ∈ ball q r) (hz0 : z.2 = 0) :
    z ∈ closure (ball q r ∩ {w : X × ℝ | w.2 < (0 : ℝ)}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r', hr', hr'sub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hz)
  have h2 : (0 : ℝ) < min ε r' := lt_min hε hr'
  refine ⟨z + (0, - min ε r' / 2), ⟨hr'sub ?_, ?_⟩, ?_⟩
  · have h1 : min ε r' ≤ r' := min_le_right _ _
    rw [mem_ball, dist_eq_norm,
      show z + (0, - min ε r' / 2) - z = (0, - min ε r' / 2) from by simp,
      Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    linarith
  · rw [Set.mem_ofPred_eq, Prod.snd_add]; linarith
  · have h1 : min ε r' ≤ ε := min_le_left _ _
    rw [dist_comm, dist_eq_norm,
      show z + (0, - min ε r' / 2) - z = (0, - min ε r' / 2) from by simp,
      Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    linarith

theorem contDiffOn_glue {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {δ : ℝ} {m : ℕ} {F : X × ℝ → Y}
    (hc : ContinuousOn F {p : X × ℝ | -δ < p.2})
    (hN : ContDiffOn ℝ m F {p : X × ℝ | -δ < p.2 ∧ p.2 < 0})
    (hH : ContDiffOn ℝ m F {p : X × ℝ | 0 < p.2})
    (hlim : ∀ i ≤ m, ∀ p : X × ℝ, -δ < p.2 →
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) Y,
        Filter.Tendsto (fun q : X × ℝ => iteratedFDeriv ℝ i F q)
        (nhdsWithin p {q : X × ℝ | -δ < q.2 ∧ q.2 ≠ 0}) (nhds L)) :
    ContDiffOn ℝ m F {p : X × ℝ | -δ < p.2} := by
  have hsH : IsOpen {z : X × ℝ | (0 : ℝ) < z.2} := isOpen_lt continuous_const continuous_snd
  have hsl : IsOpen {z : X × ℝ | -δ < z.2} := isOpen_lt continuous_const continuous_snd
  have hsN : IsOpen {z : X × ℝ | -δ < z.2 ∧ z.2 < 0} :=
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
  have hsm : IsOpen {z : X × ℝ | z.2 < (0 : ℝ)} := isOpen_lt continuous_snd continuous_const
  by_cases hδ : 0 < δ
  swap
  · push Not at hδ
    refine hH.mono fun z hz => ?_
    simp only [Set.mem_ofPred_eq] at hz ⊢
    linarith
  -- main case
  let P : (X × ℝ) → FormalMultilinearSeries ℝ (X × ℝ) Y := fun y k =>
    match k with
    | 0 => iteratedFDeriv ℝ 0 F y
    | (n+1) => if hy : -δ < y.2 ∧ y.2 = 0 then
        (if hk : n+1 ≤ m then Classical.choose (hlim (n+1) hk y hy.1)
         else iteratedFDeriv ℝ (n+1) F y)
      else iteratedFDeriv ℝ (n+1) F y
  have hP_ne : ∀ (y : X × ℝ) (k : ℕ), y.2 ≠ 0 → P y k = iteratedFDeriv ℝ k F y := by
    intro y k hy
    cases k with
    | zero => rfl
    | succ n => simp only [P]; rw [dite_eq_right]; rintro ⟨-, h2⟩; exact hy h2
  have hP_lim : ∀ (y : X × ℝ) (k : ℕ) (h1 : -δ < y.2) (h2 : y.2 = 0) (hk : k ≤ m) (hk0 : 0 < k),
      P y k = Classical.choose (hlim k hk y h1) := by
    intro y k h1 h2 hk hk0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk0)
    simp only [P]; rw [dite_eq_left ⟨h1, h2⟩, dite_eq_left hk]
  have hcurl : ∀ (k : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => X × ℝ) Y),
      L.curryLeft = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X × ℝ) Y) L :=
    fun k L => rfl
  have hkey : ∀ (q : X × ℝ) (r : ℝ), 0 < r → (∀ z ∈ ball q r, -δ < z.2) →
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
        set ρ : ℝ := min (ε₁ / 2) (δ / 2) with hρdef
        have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
        have hρle₁ : ρ < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hρδ : ρ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
        set Bp : Set (X × ℝ) := ball y ρ ∩ {z : X × ℝ | (0 : ℝ) < z.2} with hBp
        set Bm : Set (X × ℝ) := ball y ρ ∩ {z : X × ℝ | z.2 < (0 : ℝ)} with hBm
        have hBp_open : IsOpen Bp := isOpen_ball.inter hsH
        have hBm_open : IsOpen Bm := isOpen_ball.inter hsm
        have hBp_conv : Convex ℝ Bp := (convex_ball y ρ).inter convex_snd_pos
        have hBm_conv : Convex ℝ Bm := (convex_ball y ρ).inter convex_snd_neg
        have hBp_sub : Bp ⊆ {z : X × ℝ | -δ < z.2 ∧ z.2 ≠ 0} := by
          intro z hz
          have hz2 : 0 < z.2 := hz.2
          exact ⟨by linarith, ne_of_gt hz2⟩
        have hBm_sub : Bm ⊆ {z : X × ℝ | -δ < z.2 ∧ z.2 ≠ 0} := by
          intro z hz
          have hz2 : z.2 < 0 := hz.2
          have hzd : dist z y < ρ := mem_ball.mp hz.1
          have h2 : |z.2 - y.2| ≤ ρ := by
            have h3 : ‖z - y‖ ≤ ρ := by rw [dist_eq_norm] at hzd; exact hzd.le
            calc |z.2 - y.2| = |(z - y).2| := by simp
              _ ≤ ‖z - y‖ := by rw [Prod.norm_mk]; exact le_max_right _ _
              _ ≤ ρ := h3
          have hle := abs_le.mp h2
          exact ⟨by linarith, ne_of_lt hz2⟩
        have hδy : -δ < y.2 := by rw [hy0]; linarith
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
        have hbm_bot : ∀ z ∈ closure Bm, -δ < z.2 := by
          intro z hz
          rw [hBm] at hz
          have h1 : z ∈ closure (ball y ρ) := closure_mono inter_subset_left hz
          have hzd : dist z y ≤ ρ := by
            rw [← mem_closedBall, ← closure_ball y (ne_of_gt hρpos)]
            exact h1
          have h2 : |z.2 - y.2| ≤ ρ := by
            have h3 : ‖z - y‖ ≤ ρ := by rw [dist_eq_norm] at hzd; exact hzd
            calc |z.2 - y.2| = |(z - y).2| := by simp
              _ ≤ ‖z - y‖ := by rw [Prod.norm_mk]; exact le_max_right _ _
              _ ≤ ρ := h3
          have hle := abs_le.mp h2
          linarith
        have hdiffp : DifferentiableOn ℝ (fun z => P z k) Bp := by
          intro z hz
          have hz2 : 0 < z.2 := hz.2
          have hev2 : (fun w => P w k) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsH.mem_nhds hz2) (fun w hw => hP_ne w k (ne_of_gt hw))
          have hcd : ContDiffAt ℝ m F z := hH.contDiffAt (hsH.mem_nhds hz2)
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
            (hcd.iteratedFDeriv_right (m := 1)
              (by exact_mod_cast (by omega : 1 + k ≤ m))).differentiableAt (by norm_num)
          exact (hdiffit.congr_of_eventuallyEq hev2).differentiableWithinAt
        have hdiffm : DifferentiableOn ℝ (fun z => P z k) Bm := by
          intro z hz
          have hz2 : z.2 < 0 := hz.2
          have hzδ : -δ < z.2 := (hBm_sub hz).1
          have hev2 : (fun w => P w k) =ᶠ[𝓝 z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsm.mem_nhds hz2) (fun w hw => hP_ne w k (ne_of_lt hw))
          have hcd : ContDiffAt ℝ m F z := hN.contDiffAt (hsN.mem_nhds ⟨hzδ, hz2⟩)
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
            (hcd.iteratedFDeriv_right (m := 1)
              (by exact_mod_cast (by omega : 1 + k ≤ m))).differentiableAt (by norm_num)
          exact (hdiffit.congr_of_eventuallyEq hev2).differentiableWithinAt
        have hcontp : ∀ z ∈ closure Bp, ContinuousWithinAt (fun w => P w k) Bp z := by
          intro z hz
          have hzge : 0 ≤ z.2 := hbp_ge z hz
          have hδz' : -δ < z.2 := by linarith
          have hpe : (fun w => P w k) =ᶠ[𝓝[Bp] z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun w hw => hP_ne w k (ne_of_gt hw.2))
          by_cases hz0 : z.2 = 0
          · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ 0 F w) z := by
                have hFc : ContinuousAt F z := hc.continuousAt (hsl.mem_nhds hδz')
                have hfun : (fun w => iteratedFDeriv ℝ 0 F w) =
                    (fun w => (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm (F w)) := by
                  funext w; rw [iteratedFDeriv_zero_eq_comp]; rfl
                rw [hfun]
                exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm.continuous.continuousAt.comp
                  hFc
              exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
            · show Tendsto (fun w => P w k) (𝓝[Bp] z) (𝓝 (P z k))
              rw [hP_lim z k hδz' hz0 hkm.le hkpos]
              exact ((Classical.choose_spec (hlim k hkm.le z hδz')).mono_left
                (nhdsWithin_mono z hBp_sub)).congr' hpe.symm
          · have hzp : 0 < z.2 := lt_of_le_of_ne hzge (Ne.symm hz0)
            have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) z :=
              (ContinuousOn.continuousOn_iteratedFDeriv hH hsH (by exact_mod_cast hkm.le) z
                hzp).continuousAt (hsH.mem_nhds hzp)
            show Tendsto (fun w => P w k) (𝓝[Bp] z) (𝓝 (P z k))
            rw [hP_ne z k (ne_of_gt hzp)]
            exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
        have hcontm : ∀ z ∈ closure Bm, ContinuousWithinAt (fun w => P w k) Bm z := by
          intro z hz
          have hzle : z.2 ≤ 0 := hbm_le z hz
          have hδz' : -δ < z.2 := hbm_bot z hz
          have hpe : (fun w => P w k) =ᶠ[𝓝[Bm] z] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun w hw => hP_ne w k (ne_of_lt hw.2))
          by_cases hz0 : z.2 = 0
          · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ 0 F w) z := by
                have hFc : ContinuousAt F z := hc.continuousAt (hsl.mem_nhds hδz')
                have hfun : (fun w => iteratedFDeriv ℝ 0 F w) =
                    (fun w => (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm (F w)) := by
                  funext w; rw [iteratedFDeriv_zero_eq_comp]; rfl
                rw [hfun]
                exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm.continuous.continuousAt.comp
                  hFc
              exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' hpe.symm
            · show Tendsto (fun w => P w k) (𝓝[Bm] z) (𝓝 (P z k))
              rw [hP_lim z k hδz' hz0 hkm.le hkpos]
              exact ((Classical.choose_spec (hlim k hkm.le z hδz')).mono_left
                (nhdsWithin_mono z hBm_sub)).congr' hpe.symm
          · have hzn : z.2 < 0 := lt_of_le_of_ne hzle hz0
            have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) z :=
              (ContinuousOn.continuousOn_iteratedFDeriv hN hsN (by exact_mod_cast hkm.le) z
                ⟨hδz', hzn⟩).continuousAt (hsN.mem_nhds ⟨hδz', hzn⟩)
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
            rw [hP_lim y (k+1) hδy hy0 hk1 (by omega)]
            exact (Classical.choose_spec (hlim (k+1) hk1 y hδy)).mono_left
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
            rw [hP_lim y (k+1) hδy hy0 hk1 (by omega)]
            exact (Classical.choose_spec (hlim (k+1) hk1 y hδy)).mono_left
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
        · have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsm.mem_nhds hneg) (fun w hw => hP_ne w k (ne_of_lt hw))
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) y := by
            have hcd : ContDiffAt ℝ m F y := hN.contDiffAt (hsN.mem_nhds ⟨hsub y hy, hneg⟩)
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
        · have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsH.mem_nhds hpos) (fun w hw => hP_ne w k (ne_of_gt hw))
          have hdiffit : DifferentiableAt ℝ (iteratedFDeriv ℝ k F) y := by
            have hcd : ContDiffAt ℝ m F y := hH.contDiffAt (hsH.mem_nhds hpos)
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
        have hδy : -δ < y.2 := hsub y hy
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
            have hδz : -δ < z.2 := by rw [hz0]; linarith
            rcases Nat.eq_zero_or_pos k with hk0 | hkpos
            · subst hk0
              have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ 0 F w) z := by
                have hFc : ContinuousAt F z := hc.continuousAt (hsl.mem_nhds hδz)
                have hfun : (fun w => iteratedFDeriv ℝ 0 F w) =
                    (fun w => (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm (F w)) := by
                  funext w; rw [iteratedFDeriv_zero_eq_comp]; rfl
                rw [hfun]
                exact (continuousMultilinearCurryFin0 ℝ (X × ℝ) Y).symm.continuous.continuousAt.comp
                  hFc
              exact hzc.tendsto.mono_left nhdsWithin_le_nhds
            · have hΩsub : Ω ⊆ {q : X × ℝ | -δ < q.2 ∧ q.2 ≠ 0} := by
                intro a ha
                rw [hΩ] at ha
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at ha
                exact ⟨hsub a ha.1, ha.2⟩
              rw [hP_lim z k hδz hz0 hkm hkpos]
              exact (Classical.choose_spec (hlim k hkm z hδz)).mono_left
                (nhdsWithin_mono z hΩsub)
        exact hcont_at.continuousWithinAt
      · -- off the hyperplane
        rcases lt_or_gt_of_ne hy0 with hneg | hpos
        · have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsm.mem_nhds hneg) (fun w hw => hP_ne w k (ne_of_lt hw))
          have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) y :=
            (ContinuousOn.continuousOn_iteratedFDeriv hN hsN (by exact_mod_cast hkm) y
              ⟨hsub y hy, hneg⟩).continuousAt (hsN.mem_nhds ⟨hsub y hy, hneg⟩)
          exact (hzc.congr_of_eventuallyEq hev2).continuousWithinAt
        · have hev2 : (fun w => P w k) =ᶠ[𝓝 y] (fun w => iteratedFDeriv ℝ k F w) :=
            Filter.eventuallyEq_of_mem (hsH.mem_nhds hpos) (fun w hw => hP_ne w k (ne_of_gt hw))
          have hzc : ContinuousAt (fun w => iteratedFDeriv ℝ k F w) y :=
            (ContinuousOn.continuousOn_iteratedFDeriv hH hsH (by exact_mod_cast hkm) y
              hpos).continuousAt (hsH.mem_nhds hpos)
          exact (hzc.congr_of_eventuallyEq hev2).continuousWithinAt
  -- conclusion
  intro p hp
  by_cases hp0 : p.2 = 0
  · obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hsl.mem_nhds hp)
    have hPk := hkey p r hr (fun z hz => hrs hz)
    refine contDiffWithinAt_nat.mpr ⟨ball p r, ?_, P, hPk⟩
    exact mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  · rcases lt_or_gt_of_ne hp0 with hneg | hpos
    · exact ((hN p ⟨hp, hneg⟩).contDiffAt (hsN.mem_nhds ⟨hp, hneg⟩)).contDiffWithinAt
    · exact ((hH p hpos).contDiffAt (hsH.mem_nhds hpos)).contDiffWithinAt

end Work.NN.Final
