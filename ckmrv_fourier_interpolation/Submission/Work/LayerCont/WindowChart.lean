import Mathlib
import Submission.Work.LayerCont.LowDouble
import Submission.Work.LayerCont.TruncContinuation
import Submission.Work.LayerCont.TruncDominator

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-- **The cusp dominator on the clean tail `[p,∞)`** (`p > 0`).

The `layerTruncAt` companion of `Work.LayerCont.TruncCuspDominator`: on a compact `K` and with
cleanliness on `[p,∞)` (which for `p` above every pole height is what the web classification
supplies), the cusp-subtracted kernel decays like `C (1+t)^M e^{-π(t-T₀)}`.  The small-`t` half is
`GapBoundKaxisLow` + `Aexp_compact_bound` on the compact window `[p, max Tk p]`, the tail half is
`kernel_axis_bound` (compactness only). -/
theorem TruncCuspDominatorAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {p : ℝ} (hp : 0 < p)
    (hclean : ∀ (w : UpperHalfPlane), w ∈ K → ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → p ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨Ck, Mk, Tk, hCk, hMk, hTk, hkb⟩ := Work.Asymptotics.kernel_axis_bound ℓ d hd hK
  set T : ℝ := max Tk p with hTdef
  have hTpos : 0 < T := lt_max_of_lt_right hp
  have hTk_le : Tk ≤ T := le_max_left _ _
  have hp_le : p ≤ T := le_max_right _ _
  -- the compact window `[p,T]`
  obtain ⟨Cg, hCg, hgb⟩ := GapBoundKaxisLow ℓ d hd hK hp (T := T)
    (fun w hw t ht htI => hclean w hw t ht htI.1)
  obtain ⟨Cae, hCaenn, haeb⟩ := Aexp_compact_bound ℓ d hd hK (T := T)
  refine ⟨max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1, max Mk 0, T,
    by positivity, le_max_right _ _, hTpos.le, fun τ t hτ hpt => ?_⟩
  rcases le_or_gt t T with htT | htT
  · have hKb : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cg :=
      hgb τ t hτ ⟨hpt, htT⟩
    have hAb : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae :=
      haeb τ hτ t (by rw [abs_of_nonneg (by linarith)]; exact htT)
    have hsum : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cg + Cae :=
      le_trans (norm_sub_le _ _) (add_le_add hKb hAb)
    refine le_trans hsum ?_
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have h1' : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.one_le_rpow hw (le_max_right _ _)
    have h2' : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := by
      rw [Real.one_le_exp_iff]; nlinarith [Real.pi_pos]
    have hCC : Cg + Cae ≤ max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1 := by
      linarith [le_max_left (Cg + Cae) (Ck * Real.exp (-(Real.pi * T)))]
    have hone : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T))) := by
      have hA0 : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
      have hB0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := (Real.exp_pos _).le
      nlinarith [h1', h2', hA0, hB0]
    calc Cg + Cae ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * 1 := by
          rw [mul_one]; exact hCC
      _ ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T)))) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T))) := by ring
  · have hb := hkb τ hτ t (le_trans hTk_le (le_of_lt htT))
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have hpM : (1 + t) ^ Mk ≤ (1 + t) ^ max Mk 0 :=
      Real.rpow_le_rpow_of_exponent_le hw (le_max_left _ _)
    have hY : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := (Real.exp_pos _).le
    have hX : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hsplit : Real.exp (-(Real.pi * t))
        = Real.exp (-(Real.pi * T)) * Real.exp (-(Real.pi * (t - T))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hCkC : Ck * Real.exp (-(Real.pi * T)) ≤
        max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1 := by
      linarith [le_max_right (Cg + Cae) (Ck * Real.exp (-(Real.pi * T)))]
    have step2 : Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T))))
        ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpM hCk.le)
        (mul_nonneg (Real.exp_pos _).le hY)
    have step3 : Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T))))
        = (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T)))) := by ring
    have step4 : (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))))
        ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T)))) :=
      mul_le_mul_of_nonneg_right hCkC (mul_nonneg hX hY)
    have step5 : (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))))
        = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))) := by ring
    refine le_trans hb ?_
    calc Ck * (1 + t) ^ Mk * Real.exp (-(Real.pi * t))
        = Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T))
            * Real.exp (-(Real.pi * (t - T)))) := by rw [hsplit]
      _ ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
            * Real.exp (-(Real.pi * (t - T)))) := step2
      _ = (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T)))) := step3
      _ ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T)))) := step4
      _ = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T))) := step5

/-- The indicator form of the retained integral of `layerTruncAt`. -/
lemma layerTruncAt_piece_eq_indicatorIoi (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) {p : ℝ} (hp1 : 1 ≤ p) (r : ℝ) (z : ℂ) :
    (∫ t in Set.Ici p,
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (UpperHalfPlane.ofComplex z) t
          - Work.Asymptotics.Aexp G (UpperHalfPlane.ofComplex z) t)
          * Work.Asymptotics.gaussWeight r t)
      = ∫ t in Set.Ioi (0 : ℝ),
          (Set.Ici p).indicator
            (fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
                (UpperHalfPlane.ofComplex z) t
              - Work.Asymptotics.Aexp G (UpperHalfPlane.ofComplex z) t)
              * Work.Asymptotics.gaussWeight r t) t := by
  have hEmeas : MeasurableSet (Set.Ici p) := measurableSet_Ici
  have hEsub : Set.Ici p ⊆ Set.Ioi (0 : ℝ) :=
    fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (le_trans hp1 hx))
  rw [integral_indicator hEmeas, Measure.restrict_restrict_of_subset hEsub]

/-- **Holomorphy of the extended truncated piece `layerTruncAt`** (the clean tail `[p,∞)`, no
removed interval): the mirror of `Work.LayerCont.TruncHolomorphy` with the dominator from
`Work.LayerCont.TruncCuspDominatorAt` and without the `Aexp`-detour term. -/
theorem mdifferentiableOn_layerTruncAt (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {p : ℝ} (hp1 : 1 ≤ p)
    {t₀ : ℝ} (ht₀ : 0 < t₀) {ε : ℝ} (hε : 0 < ε) (r : ℝ)
    (hclean : ∀ (s : ℝ) (hs : 0 < s), p ≤ s → ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ)
      (Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε) := by
  classical
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hpiece : ∀ x ∈ Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε,
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => ∫ t in Set.Ici p,
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Work.Asymptotics.gaussWeight r t) x := by
    intro x hx
    have hxdist : dist x (Work.Asymptotics.onePlusI t₀ ht₀) < ε := by
      simpa [Metric.mem_ball] using hx
    set ρ : ℝ := (ε - dist x (Work.Asymptotics.onePlusI t₀ ht₀)) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hρlt : dist x (Work.Asymptotics.onePlusI t₀ ht₀) + ρ < ε := by rw [hρdef]; linarith
    set I : Set ℝ := Set.Ici p with hIdef
    have hImeas : MeasurableSet I := measurableSet_Ici
    have hIsub : I ⊆ Set.Ioi (0 : ℝ) :=
      fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (le_trans hp1 hy))
    have hclean' : ∀ (w : UpperHalfPlane), w ∈ Metric.closedBall x ρ → ∀ (s : ℝ) (hs : 0 < s),
        p ≤ s → Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
      intro w hw s hs hps
      refine hclean s hs hps w ?_
      calc dist w (Work.Asymptotics.onePlusI t₀ ht₀)
          ≤ dist w x + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := dist_triangle _ _ _
        _ ≤ ρ + dist x (Work.Asymptotics.onePlusI t₀ ht₀) := by
            linarith [Metric.mem_closedBall.mp hw]
        _ < ε := by linarith
    obtain ⟨C, M, T₀, hCpos, hMnn, hT₀nn, hdb⟩ :=
      TruncCuspDominatorAt ℓ d hd (K := Metric.closedBall x ρ) (isCompact_closedBall x ρ)
        hp0 hclean'
    set Dfun : ℝ → ℝ := fun t => C * Real.exp (Real.pi * T₀)
      * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) with hDfundef
    have hDint : IntegrableOn Dfun (Set.Ici (1 : ℝ)) := by
      have ha : (0 : ℝ) < Real.pi * (1 + r ^ 2) := by positivity
      have h := TailIntegrable hMnn ha
      have h2 : IntegrableOn (fun t : ℝ =>
          (1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) (Set.Ici (1 : ℝ)) := h
      exact h2.const_mul (C * Real.exp (Real.pi * T₀))
    set bound : ℝ → ℝ := I.indicator Dfun with hbounddef
    have hbc : IntegrableOn bound (Set.Ioi (0 : ℝ)) := by
      show Integrable (I.indicator Dfun) (volume.restrict (Set.Ioi (0 : ℝ)))
      rw [integrable_indicator_iff hImeas]
      show Integrable Dfun ((volume.restrict (Set.Ioi (0 : ℝ))).restrict I)
      rw [Measure.restrict_restrict_of_subset hIsub]
      exact hDint.mono_set (fun x hx => le_trans hp1 hx)
    set U : Set ℂ := (UpperHalfPlane.coe : UpperHalfPlane → ℂ) '' (Metric.ball x ρ) with hUdef
    have hUopen : IsOpen U :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
    have hxU : (x : ℂ) ∈ U := ⟨x, Metric.mem_ball_self hρpos, rfl⟩
    have hUim : ∀ z ∈ U, 0 < z.im := by
      rintro z ⟨w, _, rfl⟩
      exact w.im_pos
    have hUb : ∀ z ∈ U, ∃ w : UpperHalfPlane, dist w x ≤ ρ ∧ (w : ℂ) = z := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, le_of_lt (Metric.mem_ball.mp hw), rfl⟩
    set F : ℂ → ℝ → ℂ := fun z t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
        (UpperHalfPlane.ofComplex z) t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) (UpperHalfPlane.ofComplex z) t)
      * Work.Asymptotics.gaussWeight r t with hFdef
    have hbb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, ‖Set.indicator I (fun t' => F z t') t‖ ≤ bound t := by
      filter_upwards with t
      intro z hz
      by_cases htI : t ∈ I
      · obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have ht1 : (1 : ℝ) ≤ t := by
          rw [hIdef] at htI
          exact le_trans hp1 htI
        have hcoe : UpperHalfPlane.ofComplex z = w := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hUim z hz), UpperHalfPlane.coe_mk, hwz]
        have hdb' := hdb w t (Metric.mem_closedBall.mpr hwρ) htI
        have hnormg : ‖Work.Asymptotics.gaussWeight r t‖
            = Real.exp (-(Real.pi * r ^ 2 * t)) := norm_gaussWeight r t
        have hexp : Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
            = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * (1 + r ^ 2) * t)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [Set.indicator_apply, if_pos htI, hbounddef, Set.indicator_apply, if_pos htI, hDfundef]
        simp only [hFdef, hcoe]
        calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
                * Work.Asymptotics.gaussWeight r t‖
            = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
                - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
              * ‖Work.Asymptotics.gaussWeight r t‖ := norm_mul _ _
          _ ≤ (C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
                * ‖Work.Asymptotics.gaussWeight r t‖ :=
              mul_le_mul_of_nonneg_right hdb' (norm_nonneg _)
          _ = C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))
                * Real.exp (-(Real.pi * r ^ 2 * t)) := by rw [hnormg]
          _ = C * Real.exp (Real.pi * T₀)
                * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by
              have hassoc : C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))
                    * Real.exp (-(Real.pi * r ^ 2 * t))
                  = C * (1 + t) ^ M * (Real.exp (-(Real.pi * (t - T₀)))
                    * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
              rw [hassoc, hexp]
              ring
      · rw [Set.indicator_apply, if_neg htI, norm_zero, hbounddef, Set.indicator_apply, if_neg htI]
    have hdiff : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ z ∈ U, DifferentiableAt ℂ (fun z' => Set.indicator I (fun t' => F z' t') t) z := by
      filter_upwards with t
      intro z hz
      have hzim : 0 < z.im := hUim z hz
      have heq : (fun z' : ℂ => Set.indicator I (fun t' => F z' t') t)
          = fun z' : ℂ => if t ∈ I then F z' t else 0 := by
        funext z'
        simp only [Set.indicator_apply]
      rw [heq]
      by_cases htI : t ∈ I
      · simp only [if_pos htI]
        have hpt : p ≤ t := by rw [hIdef] at htI; exact htI
        have ht0 : 0 < t := lt_of_lt_of_le hp0 hpt
        obtain ⟨w, hwρ, hwz⟩ := hUb z hz
        have hJ : Work.Kernels.jInvariantFun (⟨z, hzim⟩ : UpperHalfPlane)
            ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
          have hdist : dist (⟨z, hzim⟩ : UpperHalfPlane) x ≤ ρ := by
            have hzw : (⟨z, hzim⟩ : UpperHalfPlane) = w := UpperHalfPlane.ext hwz.symm
            rw [hzw]; exact hwρ
          exact hclean' ⟨z, hzim⟩ (Metric.mem_closedBall.mpr hdist) t ht0 hpt
        have heq2 : (fun z' : ℂ => F z' t)
            = fun z' : ℂ => (Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z')
                (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
                  (UpperHalfPlane.ofComplex z') t)
              * Work.Asymptotics.gaussWeight r t := by
          funext z'
          simp only [hFdef, Work.Kernels.Kaxis, dif_pos ht0]
        rw [heq2]
        exact ((Work.Asymptotics.differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd
          (τ := (⟨z, hzim⟩ : UpperHalfPlane)) (z := Work.Kernels.imagAxis t ht0) hJ).sub
          (differentiableAt_Aexp_ofComplex ℓ d hd t (⟨z, hzim⟩ : UpperHalfPlane))).mul_const _
      · simp only [if_neg htI]
        exact differentiableAt_const _
    have hmeas : ∀ z ∈ U, AEStronglyMeasurable
        (fun t : ℝ => Set.indicator I (fun t' => F z t') t)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      intro z hz
      have hFmeas : Measurable (fun t : ℝ => F z t) := by
        have h1 : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
            (UpperHalfPlane.ofComplex z) t) :=
          Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd (UpperHalfPlane.ofComplex z)
        have h2 : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
            (UpperHalfPlane.ofComplex z) t) := by
          simp only [Work.Asymptotics.Aexp]
          fun_prop
        have h3 : Measurable (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
          unfold Work.Asymptotics.gaussWeight; fun_prop
        exact ((h1.sub h2).mul h3)
      have h4 : Measurable (I.indicator (fun t : ℝ => F z t)) := hFmeas.indicator hImeas
      simpa only using h4.aestronglyMeasurable
    have hdiffOn : DifferentiableOn ℂ
        (fun z : ℂ => ∫ t in Set.Ioi (0 : ℝ), Set.indicator I (fun t' => F z t') t) U :=
      Work.Asymptotics.differentiableOn_integral_Ioi hUopen bound hbc hbb hdiff hmeas
        (fun z hz => Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn
          hUopen hmeas hdiff z hz)
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    refine (hdiffOn.differentiableAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hxU] with z hz
    simp only [Function.comp_apply, hFdef]
    exact layerTruncAt_piece_eq_indicatorIoi (Work.Asymptotics.Gcusp ℓ d) ℓ d hp1 r z
  intro x hx
  simp only [layerTruncAt]
  exact ((hpiece x hx).const_smul (Work.Asymptotics.sinSqC r)).mdifferentiableWithinAt

/-- **Cleanliness of the retained window ranges for every `τ` of the ball.**

The web gives `τ.re = 1` and `τ.im ∈ {s, s⁻¹}`; the branch `τ.im = s` puts `s` in `I₁` (the height
bound `|τ.im - s₀| < 3 s₀ ε ≤ A₁`), and the branch `τ.im = s⁻¹` puts `s = τ.im⁻¹` in `I₂` — the
latter by the estimate `|τ.im⁻¹ - s₀⁻¹| = |s₀ - τ.im|/(s₀ τ.im) < 3s₀ε/(s₀τ.im) ≤ A₂` (using
`τ.im > (3/4) s₀` from `ε ≤ 1/16` and `4ε ≤ A₂ s₀`). -/
theorem clean_axis_retained_of_web {s₀ A₁ A₂ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hA₁ : 0 < A₁)
    (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) (hεw : ε ≤ rw₀) (h4sε : 4 * s₀ * ε ≤ A₁)
    (h4ε : 4 * ε ≤ A₂ * s₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (s : ℝ) (hs : 0 < s), s ∉ Set.Ioo (s₀ - A₁) (s₀ + A₁) →
      s ∉ Set.Ioo (s₀⁻¹ - A₂) (s₀⁻¹ + A₂) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
  intro s hs hsE₁ hsE₂ τ hτ hjeq
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hd : dist (σ • Work.Kernels.imagAxis s hs) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, him⟩ := hweb σ s hs hd
  rw [hσ] at hre him
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp
    (Work.Asymptotics.abs_re_im_sub_lt hs₀ hε (le_trans hε16 (by norm_num)) hτ).2
  have hA₂pos : 0 < A₂ := by
    rcases le_or_gt A₂ 0 with h | h
    · exfalso
      have h2 : A₂ * s₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hs₀.le
      linarith [h4ε, hε]
    · exact h
  rcases him with him | him
  · -- `τ.im = s`: then `s ∈ I₁`
    refine absurd ?_ hsE₁
    rw [Set.mem_Ioo, ← him]
    exact ⟨by linarith, by linarith⟩
  · -- `τ.im = s⁻¹`: then `s = τ.im⁻¹ ∈ I₂`
    refine absurd ?_ hsE₂
    have hs_eq : s = τ.im⁻¹ := by rw [him, inv_inv]
    have hτim_pos : 0 < τ.im := τ.im_pos
    have hτim_gt : (3 : ℝ) / 4 * s₀ < τ.im := by nlinarith [h2lo, hε16, hs₀]
    have hnum : |s₀ - τ.im| < 3 * s₀ * ε := by
      rw [abs_sub_comm]
      exact abs_lt.mpr ⟨h2lo, h2hi⟩
    have hle1 : 3 * s₀ * ε ≤ 3 * s₀ * (A₂ * s₀ / 4) := by nlinarith [h4ε, hs₀]
    have hle2 : 3 * s₀ * (A₂ * s₀ / 4) < A₂ * s₀ * τ.im := by
      have hmul := mul_lt_mul_of_pos_right hτim_gt (mul_pos hA₂pos hs₀)
      nlinarith [hmul]
    have hkey : |τ.im⁻¹ - s₀⁻¹| < A₂ := by
      have hdiv : τ.im⁻¹ - s₀⁻¹ = (s₀ - τ.im) / (s₀ * τ.im) := by
        rw [inv_sub_inv (ne_of_gt hτim_pos) (ne_of_gt hs₀)]
        ring
      rw [hdiv, abs_div, abs_of_pos (mul_pos hs₀ hτim_pos)]
      rw [div_lt_iff₀ (mul_pos hs₀ hτim_pos)]
      nlinarith [hnum.le, lt_of_le_of_lt hle1 hle2]
    rw [Set.mem_Ioo, hs_eq]
    obtain ⟨h1, h2⟩ := abs_lt.mp hkey
    exact ⟨by linarith, by linarith⟩

/-- **Cleanliness of the tail `[p,∞)` for every `τ` of the ball** (`p` chosen above both `s₀ + A₁`
and `(s₀ - A₁)⁻¹`, the latter legitimate because `A₁ < s₀`): the web's two branches are
`τ.im = s ≥ p > s₀ + A₁ > τ.im` and `τ.im = s⁻¹ ≤ (s₀ - A₁)⁻¹ < p ≤ s`. -/
theorem clean_axis_tail_of_web {s₀ A₁ p ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hA₁s : A₁ < s₀)
    (hε : 0 < ε) (hε16 : ε ≤ 1 / 16) (hεw : ε ≤ rw₀) (h4sε : 4 * s₀ * ε ≤ A₁)
    (hp : max (s₀ + A₁) ((s₀ - A₁)⁻¹) + 1 ≤ p)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
  intro s hs hps τ hτ hjeq
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hd : dist (σ • Work.Kernels.imagAxis s hs) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, him⟩ := hweb σ s hs hd
  rw [hσ] at hre him
  obtain ⟨h2lo, h2hi⟩ := abs_lt.mp
    (Work.Asymptotics.abs_re_im_sub_lt hs₀ hε (le_trans hε16 (by norm_num)) hτ).2
  have hsA₁ : 0 < s₀ - A₁ := by linarith
  have h3sε : 3 * s₀ * ε ≤ A₁ := by linarith
  have hτim_hi : τ.im < s₀ + A₁ := by linarith
  have hτim_lo : s₀ - A₁ < τ.im := by linarith
  have hsp : s₀ + A₁ ≤ p := by
    have h := le_max_left (s₀ + A₁) ((s₀ - A₁)⁻¹)
    linarith
  have hinv : (s₀ - A₁)⁻¹ ≤ p := by
    have h := le_max_right (s₀ + A₁) ((s₀ - A₁)⁻¹)
    linarith
  rcases him with him | him
  · -- `τ.im = s ≥ p > s₀ + A₁ > τ.im`
    exfalso
    linarith
  · -- `τ.im = s⁻¹ ≤ (s₀ - A₁)⁻¹ < p ≤ s`
    exfalso
    have h1 : τ.im = s⁻¹ := him
    have h2 : s ≤ (s₀ - A₁)⁻¹ := by
      by_contra hcon
      push_neg at hcon
      have hlt : s⁻¹ < s₀ - A₁ := (inv_lt_comm₀ hsA₁ hs).mp hcon
      rw [← h1] at hlt
      linarith
    have h3 : (s₀ - A₁)⁻¹ + 1 ≤ p := by
      have h := le_max_right (s₀ + A₁) ((s₀ - A₁)⁻¹)
      linarith
    linarith

/-- **Cleanliness of the whole half-line for `τ.re < 1`**, from the web: `j τ = j (i t)` forces
`τ.re = 1`, contradicting `τ.re < 1`.  (The unrestricted-`t` companion of
`Work.LayerCont.clean_axis_of_web_low`, which needs the same proof but carries a `t ∈ (0,1]`
hypothesis.) -/
theorem clean_axis_of_web_re_lt_one {s₀ ε rw₀ : ℝ} (hs₀ : 0 < s₀) (hεw : ε ≤ rw₀)
    (hweb : ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ) (ht : 0 < t),
      dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ →
      (σ • Work.Kernels.imagAxis t ht).re = 1 ∧
        ((σ • Work.Kernels.imagAxis t ht).im = t ∨
          (σ • Work.Kernels.imagAxis t ht).im = t⁻¹)) :
    ∀ (t : ℝ) (ht : 0 < t), ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → τ.re < 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht τ hτ hτre hjeq
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
  have hd : dist (σ • Work.Kernels.imagAxis t ht) (Work.Asymptotics.onePlusI s₀ hs₀) < rw₀ := by
    rw [hσ]
    exact lt_of_lt_of_le hτ hεw
  obtain ⟨hre, -⟩ := hweb σ t ht hd
  rw [hσ] at hre
  linarith


end Work.LayerCont
