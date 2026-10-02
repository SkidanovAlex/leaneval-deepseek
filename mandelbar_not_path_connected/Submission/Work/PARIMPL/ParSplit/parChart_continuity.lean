import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parChart_algebra
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.PARIMPL.ParSplit.Hp_double_root_count
import Submission.Work.PARIMPL.ParSplit.no_double_root_near
import Submission.Work.PARIMPL.ParSplit.parU0_sq_re_lower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## The complex function whose principal square root is `parU0`

`parU0 S c = Complex.sqrt (parLam S c * (parRho S c)^2 / ‖parRho S c‖^2)`; we call the argument
`chartF S c`.  `parU0` is the *principal* square root, so its continuity is equivalent to `chartF`
avoiding the branch cut `(-∞, 0]`; the phase inequality of `phase_of_split` provides exactly this,
with the quantitative margin `Re (chartF S c) ≥ 17/32` on a small ball (see `parU0_sq_re_lower`,
which is proved from `phase_of_split`). -/

/-- The argument of the principal square root defining `parU0`. -/
noncomputable def chartF (S : SplitData d) (c : ℂ) : ℂ :=
  parLam S c * (parRho S c) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2

/-- `chartF` is the square of the chart constant `parU0`. -/
theorem chartF_eq_parU0_sq (S : SplitData d) (c : ℂ) : chartF S c = (parU0 S c) ^ 2 :=
  (parChart_parU0_sq S c).symm

/-- `parU0` is the principal square root of `chartF`. -/
theorem parU0_eq_sqrt_chartF (S : SplitData d) :
    parU0 S = fun c => Complex.sqrt (chartF S c) := by
  funext c
  show Complex.sqrt (parLam S c * (parRho S c) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2)
      = Complex.sqrt (chartF S c)
  rw [chartF]

/-! ## Continuity of `chartF`, `parU0`, `parS` -/

theorem continuousOn_chartF (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hρ0 : ∀ c ∈ Metric.ball c₀ ρ, parRho S c ≠ 0) :
    ContinuousOn (chartF S) (Metric.ball c₀ ρ) := by
  have hρc : ContinuousOn (parRho S) (Metric.ball c₀ ρ) := continuousOn_parRho S hρ
  have hden : ContinuousOn (fun c => (Complex.ofReal ‖parRho S c‖) ^ 2)
      (Metric.ball c₀ ρ) :=
    (Complex.continuous_ofReal.comp_continuousOn hρc.norm).pow 2
  unfold chartF
  exact ((continuousOn_parLam S hρ).mul (hρc.pow 2)).div hden (fun c hc =>
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hρ0 c hc))))

theorem continuousOn_parU0 (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hρ0 : ∀ c ∈ Metric.ball c₀ ρ, parRho S c ≠ 0)
    (hre : ∀ c ∈ Metric.ball c₀ ρ, 0 < (chartF S c).re) :
    ContinuousOn (parU0 S) (Metric.ball c₀ ρ) := by
  have hcf : ContinuousOn (chartF S) (Metric.ball c₀ ρ) := continuousOn_chartF S hρ hρ0
  rw [parU0_eq_sqrt_chartF]
  intro c hc
  exact ((Complex.continuousAt_sqrt (Or.inl (le_of_lt (hre c hc)))).comp
    (hcf.continuousAt (isOpen_ball.mem_nhds hc))).continuousWithinAt

theorem continuousOn_parS (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hρ0 : ∀ c ∈ Metric.ball c₀ ρ, parRho S c ≠ 0)
    (hre : ∀ c ∈ Metric.ball c₀ ρ, 0 < (chartF S c).re) :
    ContinuousOn (parS S) (Metric.ball c₀ ρ) := by
  unfold parS
  exact (continuousOn_parU0 S hρ hρ0 hre).div (continuousOn_parRho S hρ) hρ0

/-! ## The phase lower bound on the whole ball

Off the collision locus `{E = 0}` the phase inequality gives `Re (chartF) ≥ 17/32`.  On the
collision locus we use that the double-root locus of the fixed point polynomial `Qpoly` has empty
interior (`no_double_root_near`): every point of `{E = 0}` is a limit of parameters with `E ≠ 0`,
and `Re (chartF ·)` is continuous (its argument `chartF` is a composition of continuous functions,
`parRho` being nonvanishing). -/

theorem re_chartF_lower_ball (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hρ0 : ∀ c ∈ Metric.ball c₀ ρ, parRho S c ≠ 0)
    (hHp : ∀ c ∈ Metric.ball c₀ ρ, S.E c = 0 → (Qpoly c).derivative.eval (S.m c) = 0)
    (hgen : ∀ c : ℂ, ∀ ε : ℝ, 0 < ε → ∃ c' ∈ Metric.ball c ε,
      ∀ z : ℂ, ¬ ((Qpoly c').eval z = 0 ∧ (Qpoly c').derivative.eval z = 0))
    (hphase : ∀ c ∈ Metric.ball c₀ ρ, S.E c ≠ 0 → (17 : ℝ)/32 ≤ (chartF S c).re) :
    ∀ c ∈ Metric.ball c₀ ρ, (17 : ℝ)/32 ≤ (chartF S c).re := by
  intro c hc
  by_cases hE : S.E c = 0
  · have hdist : dist c c₀ < ρ := by
      rw [Metric.mem_ball] at hc; simpa [dist_comm] using hc
    have hcfa : ContinuousAt (fun x => (chartF S x).re) c :=
      Complex.continuous_re.continuousAt.comp
        ((continuousOn_chartF S hρ hρ0).continuousAt (isOpen_ball.mem_nhds hc))
    -- a sequence of parameters with `E ≠ 0` tending to `c`
    have hex : ∀ n : ℕ, ∃ c' : ℂ, c' ∈ Metric.ball c (1/(n+1)) ∧ c' ∈ Metric.ball c₀ ρ ∧
        S.E c' ≠ 0 := by
      intro n
      have hε : 0 < min (1/((n:ℝ)+1)) ((ρ - dist c c₀)/2) :=
        lt_min (by positivity) (by linarith)
      obtain ⟨c', hc'1, hc'nd⟩ := hgen c (min (1/((n:ℝ)+1)) ((ρ - dist c c₀)/2)) hε
      have hd : dist c' c < min (1/((n:ℝ)+1)) ((ρ - dist c c₀)/2) := by
        simpa [Metric.mem_ball] using hc'1
      have hc'ρ : c' ∈ Metric.ball c₀ ρ := by
        rw [Metric.mem_ball]
        have h1 : dist c' c < (ρ - dist c c₀)/2 := lt_of_lt_of_le hd (min_le_right _ _)
        calc dist c' c₀ ≤ dist c' c + dist c c₀ := dist_triangle _ _ _
          _ < (ρ - dist c c₀)/2 + dist c c₀ := by linarith
          _ < ρ := by linarith
      have hne : S.E c' ≠ 0 := by
        intro h0
        have hfix : Work.EL.F c' (S.m c') = S.m c' := by
          have h := S.fixed_add c' (Metric.ball_subset_ball hρ hc'ρ)
          rwa [h0, zero_div, add_zero] at h
        have hroot : (Qpoly c').eval (S.m c') = 0 := by rw [Qpoly_eval, hfix, sub_self]
        have hder : (Qpoly c').derivative.eval (S.m c') = 0 := hHp c' hc'ρ h0
        exact hc'nd (S.m c') ⟨hroot, hder⟩
      exact ⟨c', by simpa [Metric.mem_ball] using lt_of_lt_of_le hd (min_le_left _ _),
        hc'ρ, hne⟩
    choose u hu using hex
    have htend : Tendsto u atTop (𝓝 c) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
      have hN0 : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le (by positivity) (le_of_lt hN)
      have hNε : 1 < (N:ℝ) * ε := by
        have h := hN
        rw [div_lt_iff₀ hε] at h
        exact h
      refine ⟨N, fun n hn => ?_⟩
      have h1 : dist (u n) c < 1/((n:ℝ)+1) := by simpa [Metric.mem_ball] using (hu n).1
      have hn' : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have h3 : 1/((n:ℝ)+1) ≤ 1/((N:ℝ)+1) := by
        apply one_div_le_one_div_of_le (by positivity : (0:ℝ) < (N:ℝ)+1)
        linarith
      have h4 : 1/((N:ℝ)+1) < ε := by
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (N:ℝ)+1)]
        nlinarith [hNε, hN0]
      linarith
    have hbnd : ∀ n : ℕ, (17 : ℝ)/32 ≤ (chartF S (u n)).re :=
      fun n => hphase (u n) (hu n).2.1 (hu n).2.2
    have hcont : Tendsto (fun n => (chartF S (u n)).re) atTop (𝓝 ((chartF S c).re)) :=
      (ContinuousAt.tendsto hcfa).comp htend
    exact ge_of_tendsto hcont (Eventually.of_forall hbnd)
  · exact hphase c hc hE

/-! ## Continuity of `parA2` and `parA`

`parA2 S c = σ c · ‖Gc S c‖ · ‖parRho S c‖²`; the product `σ · ‖Gc‖` is `Gc / parLam`
(the denominator-cleared wall identity `parLam · σ · ‖Gc‖ = Gc`), which is continuous and
single-valued even on the collision locus. -/

theorem continuousOn_parA2 (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hlam : ∀ c ∈ Metric.ball c₀ ρ, parLam S c ≠ 0)
    (hwall : ∀ c ∈ Metric.ball c₀ ρ,
      parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c) :
    ContinuousOn (parA2 S) (Metric.ball c₀ ρ) := by
  have hH : ContinuousOn
      (fun c => Gc S c / parLam S c * (Complex.ofReal ‖parRho S c‖) ^ 2)
      (Metric.ball c₀ ρ) := by
    refine ((continuousOn_Gc S hρ).div (continuousOn_parLam S hρ) hlam).mul ?_
    exact (Complex.continuous_ofReal.comp_continuousOn (continuousOn_parRho S hρ).norm).pow 2
  refine (Complex.continuous_re.comp_continuousOn hH).congr ?_
  intro c hc
  show parA2 S c = (Gc S c / parLam S c * (Complex.ofReal ‖parRho S c‖) ^ 2).re
  rw [← Complex.ofReal_re (parA2 S c), parA2_coe S c]
  have h : (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c / parLam S c := by
    rw [eq_div_iff (hlam c hc)]
    linear_combination (hwall c hc)
  rw [h]

theorem continuousOn_parA (S : SplitData d) {ρ : ℝ}
    (h : ContinuousOn (parA2 S) (Metric.ball c₀ ρ)) :
    ContinuousOn (parA S) (Metric.ball c₀ ρ) := by
  unfold parA
  exact continuousOn_realSqrt_comp h

/-! ## Continuity of `parH1`, `parHgerm`, `parKappa` -/

theorem continuousOn_parH1 (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hS : ContinuousOn (parS S) (Metric.ball c₀ ρ)) :
    ContinuousOn (parH1 S) (Metric.ball c₀ ρ) := by
  unfold parH1
  exact (hS.pow 2).mul (continuousOn_psi S 1 hρ)

theorem continuousOn_parHgerm_zero (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hS : ContinuousOn (parS S) (Metric.ball c₀ ρ)) :
    ContinuousOn (fun c => parHgerm S c 0) (Metric.ball c₀ ρ) :=
  (hS.mul (continuousOn_parRho S hρ)).congr (fun c hc => by
    simp [parHgerm, Rfun_zero])

theorem continuousOn_parHgerm (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hS : ContinuousOn (parS S) (Metric.ball c₀ ρ)) :
    ContinuousOn (fun p : ℂ × ℂ => parHgerm S p.1 p.2)
      (Metric.ball c₀ ρ ×ˢ Set.univ) := by
  have hs1 : ContinuousOn (fun p : ℂ × ℂ => parS S p.1) (Metric.ball c₀ ρ ×ˢ Set.univ) :=
    hS.comp continuousOn_fst (fun p hp => hp.1)
  have hR : ContinuousOn (fun p : ℂ × ℂ => Rfun S p.1 (parS S p.1 * p.2))
      (Metric.ball c₀ ρ ×ˢ Set.univ) := by
    have hmap : ContinuousOn (fun p : ℂ × ℂ => (p.1, parS S p.1 * p.2))
        (Metric.ball c₀ ρ ×ˢ Set.univ) :=
      continuousOn_fst.prodMk (hs1.mul continuousOn_snd)
    exact (continuousOn_Rfun S hρ).comp hmap (fun p hp => ⟨hp.1, trivial⟩)
  exact (hs1.mul hR).congr (fun p hp => rfl)

theorem continuousOn_parKappa (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ)
    (hS : ContinuousOn (parS S) (Metric.ball c₀ ρ))
    (hρ0 : ∀ c ∈ Metric.ball c₀ ρ, parRho S c ≠ 0)
    (hre : ∀ c ∈ Metric.ball c₀ ρ, 0 < (chartF S c).re) :
    ContinuousOn (parKappa S) (Metric.ball c₀ ρ) := by
  have hG0 : ContinuousOn (fun c => parHgerm S c 0) (Metric.ball c₀ ρ) :=
    continuousOn_parHgerm_zero S hρ hS
  have hne : ∀ c ∈ Metric.ball c₀ ρ, parHgerm S c 0 ≠ 0 := by
    intro c hc h0
    have hu0 : parU0 S c = 0 := by
      rw [← parHgerm_zero S c (hρ0 c hc)]; exact h0
    have h2 : (parU0 S c) ^ 2 = chartF S c := parChart_parU0_sq S c
    rw [hu0] at h2
    have : (chartF S c).re = 0 := by rw [← h2]; simp
    linarith [hre c hc]
  unfold parKappa
  exact hG0.sub ((continuousOn_parH1 S hρ hS).div hG0 hne)

/-! ## The main auxiliary statement -/

theorem parChart_continuity_aux (S : SplitData d)
    (hgen : ∀ c : ℂ, ∀ ε : ℝ, 0 < ε → ∃ c' ∈ Metric.ball c ε,
      ∀ z : ℂ, ¬ ((Qpoly c').eval z = 0 ∧ (Qpoly c').derivative.eval z = 0))
    (hphase : ∃ ρ > 0, ρ ≤ S.ρ ∧
      ∀ c ∈ Metric.ball c₀ ρ, S.E c ≠ 0 → (17 : ℝ)/32 ≤ (chartF S c).re) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ContinuousOn (parS S) (Metric.ball c₀ ρ') ∧
      ContinuousOn (parA2 S) (Metric.ball c₀ ρ') ∧
      ContinuousOn (parA S) (Metric.ball c₀ ρ') ∧
      ContinuousOn (parH1 S) (Metric.ball c₀ ρ') ∧
      ContinuousOn (parKappa S) (Metric.ball c₀ ρ') ∧
      ContinuousOn (fun c => parHgerm S c 0) (Metric.ball c₀ ρ') ∧
      ContinuousOn (fun p : ℂ × ℂ => parHgerm S p.1 p.2) (Metric.ball c₀ ρ' ×ˢ Set.univ) := by
  obtain ⟨ρH, hH0, hHρ, hH⟩ := Hp_double_root_count S
  obtain ⟨ρφ, hφ0, hφρ, hφ⟩ := hphase
  obtain ⟨ρr, hr0, hrρ, hr⟩ := parRho_ne_zero S
  obtain ⟨ρl, hl0, hlρ, hl⟩ := parLam_ne_zero S
  obtain ⟨ρw, hw0, hwρ, hw⟩ := parLam_sigma_norm_Gc S
  set ρ' : ℝ := min ρφ (min ρH (min ρr (min ρl ρw))) with hρ'def
  have hρ'0 : 0 < ρ' := lt_min hφ0 (lt_min hH0 (lt_min hr0 (lt_min hl0 hw0)))
  have hleφ : ρ' ≤ ρφ := min_le_left _ _
  have hleH : ρ' ≤ ρH := le_trans (min_le_right _ _) (min_le_left _ _)
  have hler : ρ' ≤ ρr :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlel : ρ' ≤ ρl :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hlew : ρ' ≤ ρw :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))
  have hρ'ρ : ρ' ≤ S.ρ := le_trans hleφ hφρ
  have hrho : ∀ c ∈ Metric.ball c₀ ρ', parRho S c ≠ 0 :=
    fun c hc => hr c (Metric.ball_subset_ball hler hc)
  have hlam : ∀ c ∈ Metric.ball c₀ ρ', parLam S c ≠ 0 :=
    fun c hc => hl c (Metric.ball_subset_ball hlel hc)
  have hwall : ∀ c ∈ Metric.ball c₀ ρ',
      parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c :=
    fun c hc => hw c (Metric.ball_subset_ball hlew hc)
  have hHp : ∀ c ∈ Metric.ball c₀ ρ', S.E c = 0 → (Qpoly c).derivative.eval (S.m c) = 0 :=
    fun c hc => hH c (Metric.ball_subset_ball hleH hc)
  have hph : ∀ c ∈ Metric.ball c₀ ρ', S.E c ≠ 0 → (17 : ℝ)/32 ≤ (chartF S c).re :=
    fun c hc => hφ c (Metric.ball_subset_ball hleφ hc)
  have hlow : ∀ c ∈ Metric.ball c₀ ρ', (17 : ℝ)/32 ≤ (chartF S c).re :=
    re_chartF_lower_ball S hρ'ρ hrho hHp hgen hph
  have hre : ∀ c ∈ Metric.ball c₀ ρ', 0 < (chartF S c).re :=
    fun c hc => lt_of_lt_of_le (by norm_num) (hlow c hc)
  have hS : ContinuousOn (parS S) (Metric.ball c₀ ρ') := continuousOn_parS S hρ'ρ hrho hre
  exact ⟨ρ', hρ'0, hρ'ρ, hS, continuousOn_parA2 S hρ'ρ hlam hwall,
    continuousOn_parA S (continuousOn_parA2 S hρ'ρ hlam hwall),
    continuousOn_parH1 S hρ'ρ hS, continuousOn_parKappa S hρ'ρ hS hrho hre,
    continuousOn_parHgerm_zero S hρ'ρ hS, continuousOn_parHgerm S hρ'ρ hS⟩

theorem parChart_continuity {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : Work.PARIMPL.ParSplit.SplitData d) : ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ContinuousOn (Work.PARIMPL.ParSplit.parS S) (Metric.ball c₀ ρ') ∧ ContinuousOn (Work.PARIMPL.ParSplit.parA2 S) (Metric.ball c₀ ρ') ∧ ContinuousOn (Work.PARIMPL.ParSplit.parA S) (Metric.ball c₀ ρ') ∧ ContinuousOn (Work.PARIMPL.ParSplit.parH1 S) (Metric.ball c₀ ρ') ∧ ContinuousOn (Work.PARIMPL.ParSplit.parKappa S) (Metric.ball c₀ ρ') ∧ ContinuousOn (fun c => Work.PARIMPL.ParSplit.parHgerm S c 0) (Metric.ball c₀ ρ') ∧ ContinuousOn (fun p : ℂ × ℂ => Work.PARIMPL.ParSplit.parHgerm S p.1 p.2) (Metric.ball c₀ ρ' ×ˢ Set.univ) := by
  obtain ⟨ρ, hρ0, hρρ, hρ⟩ := parU0_sq_re_lower S
  refine parChart_continuity_aux S (fun c ε hε => no_double_root_near c hε) ⟨ρ, hρ0, hρρ, ?_⟩
  intro c hc hE
  have h := hρ c hc hE
  rwa [← chartF_eq_parU0_sq] at h

end Work.PARIMPL.ParSplit
