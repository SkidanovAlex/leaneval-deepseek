import Mathlib
import Submission.Work.LandLeaves.SnailLemmaMilnor
import Submission.Work.LandLeaves.SnailPathDefs
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.SeedDyn.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The level function at `ρ = 2` -/

/-- The level `snailLevel k 2 t` is always `> 1`. -/
theorem snailLevel_gt_one (k : ℕ) (t : ℝ) : 1 < snailLevel k 2 t := by
  rw [snailLevel, Real.one_lt_exp_iff]
  exact mul_pos (Real.log_pos (by norm_num)) (Real.exp_pos _)

/-- The level function is continuous. -/
theorem continuous_snailLevel (k : ℕ) : Continuous (snailLevel k 2) := by
  unfold snailLevel
  fun_prop

/-- The level function tends to `1` as `t → ∞`. -/
theorem tendsto_snailLevel (k : ℕ) (hk : 0 < k) :
    Tendsto (snailLevel k 2) atTop (𝓝 (1 : ℝ)) := by
  have hμ : 0 < (k : ℝ) * Real.log 4 := by
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact mul_pos hk' (Real.log_pos (by norm_num))
  have h1 : Tendsto (fun t : ℝ => Real.exp (-(((k : ℝ) * Real.log 4) * t)))
      atTop (𝓝 (0 : ℝ)) := by
    have h2 : Tendsto (fun t : ℝ => -(((k : ℝ) * Real.log 4) * t)) atTop atBot :=
      tendsto_neg_atBot_iff.mpr (tendsto_id.const_mul_atTop hμ)
    exact Real.tendsto_exp_atBot.comp h2
  have h4 : Tendsto (fun t : ℝ =>
      Real.log 2 * Real.exp (-(((k : ℝ) * Real.log 4) * t))) atTop (𝓝 (0 : ℝ)) := by
    simpa using h1.const_mul (Real.log 2)
  have h6 : Tendsto (fun t : ℝ =>
      Real.exp (Real.log 2 * Real.exp (-(((k : ℝ) * Real.log 4) * t))))
      atTop (𝓝 (1 : ℝ)) := by
    have h5 := (Real.continuous_exp.tendsto 0).comp h4
    have h5' : Tendsto (fun t : ℝ =>
        Real.exp (Real.log 2 * Real.exp (-(((k : ℝ) * Real.log 4) * t))))
        atTop (𝓝 (Real.exp 0)) := h5
    simpa using h5'
  exact h6

/-- **The exact functional relation of the level function.** -/
theorem snailLevel_succ_pow (k : ℕ) (t : ℝ) :
    snailLevel k 2 t = (snailLevel k 2 (t + 1)) ^ ((4 : ℕ) ^ k) := by
  have hkey : Real.exp (-(((k : ℝ) * Real.log 4) * (t + 1)))
      = Real.exp (-(((k : ℝ) * Real.log 4) * t)) * Real.exp (-(((k : ℝ) * Real.log 4))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hμ : Real.exp (-(((k : ℝ) * Real.log 4))) * (((4 : ℕ) ^ k : ℕ) : ℝ) = 1 := by
    have hn : (((4 : ℕ) ^ k : ℕ) : ℝ) ≠ 0 := by
      have h : ((4 : ℕ) ^ k : ℕ) ≠ 0 := pow_ne_zero k (by norm_num)
      exact_mod_cast h
    have h1 : Real.exp (-(((k : ℝ) * Real.log 4))) = (((4 : ℕ) ^ k : ℕ) : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_nat_mul (Real.log 4) k,
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      push_cast
      ring
    rw [h1]
    exact inv_mul_cancel₀ hn
  rw [eq_comm]
  calc (snailLevel k 2 (t + 1)) ^ ((4 : ℕ) ^ k)
      = Real.exp ((((4 : ℕ) ^ k : ℕ) : ℝ) *
          (Real.log 2 * Real.exp (-(((k : ℝ) * Real.log 4) * (t + 1))))) := by
        rw [snailLevel, ← Real.exp_nat_mul]
    _ = Real.exp (Real.log 2 * Real.exp (-(((k : ℝ) * Real.log 4) * t)) *
          (Real.exp (-(((k : ℝ) * Real.log 4))) * (((4 : ℕ) ^ k : ℕ) : ℝ))) := by
        congr 1
        rw [hkey]
        ring
    _ = Real.exp (Real.log 2 * Real.exp (-(((k : ℝ) * Real.log 4) * t))) := by
        rw [hμ, mul_one]
    _ = snailLevel k 2 t := by rw [snailLevel]

/-- `2 ^ (2 * k) = 4 ^ k`. -/
theorem two_pow_two_mul (k : ℕ) : (2 : ℕ) ^ (2 * k) = (4 : ℕ) ^ k := by
  rw [pow_mul]
  norm_num

/-! ## The action of the second return map on the ray -/

/-- **The action of the holomorphic second return map `(Tsq c)^[k]` on a ray point at a periodic
angle**: the ray at the periodic angle `θ` of period `k` is invariant, and the map acts on the
Böttcher level by `t ↦ t ^ (4 ^ k)`. -/
theorem rayPt_tsqIterate {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) {θ : ℝ} {k : ℕ}
    (hper : Work.Landing.PeriodicAngle θ k) {t : ℝ} (ht : 1 < t) :
    (Work.Landing.Tsq c)^[k] (Work.EL.rayPt hN θ t)
      = Work.EL.rayPt hN θ (t ^ ((4 : ℕ) ^ k)) := by
  have hTk : Work.EL.T^[k] θ = θ := hper
  have hT : Work.EL.T^[2 * k] θ = θ := by
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hTk, hTk]
  have hstep : (Tantibar c)^[2 * k] (Work.EL.rayPt hN θ t)
      = Work.EL.rayPt hN θ (t ^ ((4 : ℕ) ^ k)) := by
    have h := Work.ELRig.rayPt_iterate_antibar hN hB (θ := θ) (t := t) ht (2 * k)
    rw [hT] at h
    rw [h, two_pow_two_mul k]
  have hTsq : Work.Landing.Tsq c = (Tantibar c)^[2] := funext (Work.ELPull.Tsq_eq_iterate c)
  rw [hTsq, ← Function.iterate_mul]
  exact hstep

/-- A `T_c`-iterate of a `snailLevel`-ray point is again a `snailLevel`-ray point: the map
`t ↦ T^[n] θ` only changes the angle, which is fixed modulo `1` by periodicity. -/
theorem rayPt_tsqIterate_snail {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) {θ : ℝ} {k : ℕ}
    (hper : Work.Landing.PeriodicAngle θ k) (t : ℝ) :
    (Work.Landing.Tsq c)^[k] (Work.EL.rayPt hN θ (snailLevel k 2 (t + 1)))
      = Work.EL.rayPt hN θ (snailLevel k 2 t) := by
  rw [rayPt_tsqIterate hN hB hper (snailLevel_gt_one k (t + 1))]
  congr 1
  exact (snailLevel_succ_pow k t).symm

/-! ## Analyticity of the second return map -/

/-- `(Tsq c)^[k]` is analytic at every point. -/
theorem analyticAt_tsq_iterate' (c : ℂ) (k : ℕ) (z : ℂ) :
    AnalyticAt ℂ ((Work.Landing.Tsq c)^[k]) z := by
  have hTsq : ∀ w : ℂ, AnalyticAt ℂ (Work.Landing.Tsq c) w := by
    intro w
    have h1 : AnalyticAt ℂ (fun u : ℂ => u ^ 2 + star c) w :=
      (analyticAt_id.pow 2).add analyticAt_const
    exact (h1.pow 2).add analyticAt_const
  induction k with
  | zero => simpa using analyticAt_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (hTsq _).comp ih

/-! ## The Snail lemma at a periodic ray -/

theorem noNeutralLanding_of_snailMilnor (h : Work.LandLeaves.SnailLemmaMilnor) (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) {θ : ℝ} {k : ℕ} {z : ℂ} (hk : 0 < k)
    (hper : Work.Landing.PeriodicAngle θ k) (hland : Work.Landing.landsAt c θ z)
    (hnorm : ‖Work.Landing.multiplier2 c k z‖ = 1) :
    Work.Landing.multiplier2 c k z = 1 := by
  -- the Böttcher datum and the parametrised landing statement
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    (Work.SeedDyn.isDynBottcherHomeo hc).1
  have hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c) := Work.SeedDyn.dynB hc
  have hLands : Work.EL.LandsN hN θ z := (Work.ELTop.landsN_iff_landsAt hN hφ θ z).mpr hland
  have hzK : z ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hLands
  have hzNotEsc : ¬ Work.ParamRays.Escaping c z := by
    have h1 : z ∉ (Work.ParamRays.filledJulia c)ᶜ := fun hh => hh hzK
    rwa [Work.ParamRays.compl_filledJulia, Work.ParamRays.mem_escapingSet] at h1
  -- the landing point is fixed by the holomorphic second return map
  have hfix : (Tantibar c)^[k] z = z := Work.Landing.landsAt_periodic hland hper
  have hTsqIter : (Work.Landing.Tsq c)^[k] z = z := by
    have hTsq : Work.Landing.Tsq c = (Tantibar c)^[2] := funext (Work.ELPull.Tsq_eq_iterate c)
    rw [hTsq, ← Function.iterate_mul]
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hfix, hfix]
  -- the local inverse germ of the second return map
  have hFan : AnalyticAt ℂ ((Work.Landing.Tsq c)^[k]) z := analyticAt_tsq_iterate' c k z
  have hFne : deriv ((Work.Landing.Tsq c)^[k]) z ≠ 0 := by
    intro h0
    have hh := hnorm
    change ‖deriv ((Work.Landing.Tsq c)^[k]) z‖ = 1 at hh
    rw [h0, norm_zero] at hh
    norm_num at hh
  set g : ℂ → ℂ := hFan.hasStrictDerivAt.localInverse ((Work.Landing.Tsq c)^[k])
    (deriv ((Work.Landing.Tsq c)^[k]) z) z hFne with hgdef
  have hgan : AnalyticAt ℂ g z := by
    have h1 := hFan.analyticAt_localInverse hFne
    rw [hTsqIter] at h1
    simpa only [hgdef] using h1
  have hleft_ev : ∀ᶠ w in 𝓝 z, g ((Work.Landing.Tsq c)^[k] w) = w := by
    have h1 := hFan.hasStrictDerivAt.eventually_left_inverse hFne
    simpa only [hgdef] using h1
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hleft_ev
  have hgz : g z = z := by
    have h1 := hε (show dist z z < ε by simpa using hεpos)
    rwa [hTsqIter] at h1
  have hgderiv : deriv g z = (deriv ((Work.Landing.Tsq c)^[k]) z)⁻¹ := by
    have h1 := hFan.hasStrictDerivAt.to_localInverse hFne
    rw [hTsqIter] at h1
    exact h1.hasDerivAt.deriv
  -- the path along the ray
  set p : ℝ → ℂ := fun t => Work.EL.rayPt hN θ (snailLevel k 2 t) with hpdef
  have hpcont : Continuous p := by
    rw [hpdef]
    exact (Work.Top.continuousOn_rayPt hN θ).comp_continuous (continuous_snailLevel k)
      (fun t => snailLevel_gt_one k t)
  have hpne : ∀ t : ℝ, p t ≠ z := by
    intro t hpt
    have h1 : p t ∉ Work.EL.K c := by
      rw [hpdef]
      exact hN.rayPt_notMem (snailLevel_gt_one k t)
    exact h1 (by rw [hpt]; exact hzK)
  have hpTend : Tendsto p atTop (𝓝 z) := by
    rw [hpdef]
    have hlevel : Tendsto (snailLevel k 2) atTop (𝓝[Set.Ioi (1 : ℝ)] 1) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_snailLevel k hk,
        Filter.Eventually.of_forall (fun t => snailLevel_gt_one k t)⟩
    have h1 := hLands.comp hlevel
    have h1' : Tendsto (fun t : ℝ => Work.EL.rayPt hN θ (snailLevel k 2 t)) atTop (𝓝 z) := h1
    exact h1'
  have hpfunc : ∀ t : ℝ, (Work.Landing.Tsq c)^[k] (p (t + 1)) = p t := by
    intro t
    rw [hpdef]
    exact rayPt_tsqIterate_snail hN hφ hper t
  -- shift the path so that the inverse germ applies at every time
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (hpTend.eventually (Metric.ball_mem_nhds z hεpos))
  set q : ℝ → ℂ := fun t => p (t + T) with hqdef
  have hqcont : ContinuousOn q (Set.Ici 0) := by
    rw [hqdef]
    exact (hpcont.comp (continuous_id.add continuous_const)).continuousOn
  have hqtend : Tendsto q atTop (𝓝 z) := by
    rw [hqdef]
    exact hpTend.comp (Filter.tendsto_atTop_add_const_right _ T tendsto_id)
  have hqeq : ∀ t ∈ Set.Ici (0 : ℝ), g (q t) = q (t + 1) := by
    intro t ht
    have hTt : T ≤ t + T + 1 := by linarith [Set.mem_Ici.mp ht]
    have hball : dist (p (t + T + 1)) z < ε := hT (t + T + 1) hTt
    have h1 : g ((Work.Landing.Tsq c)^[k] (p (t + T + 1))) = p (t + T + 1) := hε hball
    rw [hpfunc (t + T)] at h1
    have harg : t + T + 1 = (t + 1) + T := by ring
    rw [harg] at h1
    simpa only [hqdef] using h1
  -- the Snail lemma
  have hsnail := h g z Set.univ q hgan hgz isOpen_univ (Set.mem_univ z) hqcont
    (fun t _ => ⟨Set.mem_univ _, by rw [hqdef]; exact hpne (t + T)⟩) hqeq hqtend
  rcases hsnail with hlt | heq
  · have hnorm' : ‖deriv ((Work.Landing.Tsq c)^[k]) z‖ = 1 := hnorm
    have hnormg : ‖deriv g z‖ = 1 := by rw [hgderiv, norm_inv, hnorm', inv_one]
    rw [hnormg] at hlt
    exact absurd hlt (lt_irrefl 1)
  · rw [hgderiv, inv_eq_one] at heq
    exact heq

end

end Work.LandLeaves
