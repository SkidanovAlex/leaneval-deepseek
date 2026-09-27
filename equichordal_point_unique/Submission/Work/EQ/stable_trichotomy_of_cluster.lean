import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.la_nnas
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.LaTB.not_flat_of_unNear
import Submission.Work.EQ.tendsto_fan_of_uniform_limit

/-!
# `stable_trichotomy_of_cluster`

The stable half of Rychlik's Theorem 11 (the "cluster" statement): given a sequence `x k` of
heteroclinic chains whose reading parameters `(x k).2.1 = ψ₁ (x k)` converge inside the ball
`B(0,δ)` of the trichotomy, and whose `-N`-th points are `1/4`-unstable-near the axis, the
fan values `fan a h (ε (φ k)) ((x (φ k)).2.1)` of a subsequence converge to a fan value
`fan a h ε₀ (μ₁ · W)` with `μ₁` a characteristic value of modulus `≤ 1`.

The proof is the three-case analysis of Rychlik's Theorem 7 as packaged in `FanTrich`:

* (i)  all fan maps of the subsequence agree with `fan a h ε₀` on `B(0,δ)`: take `μ₁ = 1`
       (`tendsto_fan_of_eventually_eq`);
* (ii) the words are `ε₀ ++ true^{s k} ++ C k` and the fan maps converge uniformly to
       `fan a h ε₀ (charVal a h ε₁ ·)`: take `μ₁ = charVal a h ε₁ ∈ (0,1)`
       (`tendsto_fan_of_uniform_limit`);
* (iii) the fan maps shrink to the axis ("flatness"): the value at the reading parameter is then
       stable-near the coset `-1/2 + 2ℤ` (`FanSep.axis_walk` locates the fan centre), which
       contradicts the `1/4`-unstable-nearness of the `-N`-th point of the chain by the parity
       separation `not_flat_of_unNear`.
-/

namespace Work.EQ

open Filter _root_.Topology Complex Metric

/-- **Case (i) of the trichotomy.**  If every fan map of a sequence of words agrees with one fixed
fan map `fan a h ε₀` on `B(0,δ)`, and the reading parameters converge to `W ∈ B(0,δ)`, then the
fan values converge to `fan a h ε₀ W`. -/
theorem tendsto_fan_of_eventually_eq {a : ℝ} {h : ℂ → ℂ} {δ : ℝ} {ε : ℕ → List Bool}
    {ε₀ : List Bool} {x : ℕ → ChainData} {W : ℂ}
    (heq : ∀ k, Set.EqOn (fan a h (ε k)) (fan a h ε₀) (Metric.ball (0 : ℂ) δ))
    (hz : Tendsto (fun k => (x k).2.1) atTop (nhds W))
    (hzs : ∀ k, ‖(x k).2.1‖ < δ) (hW : ‖W‖ < δ)
    (hcont : ContinuousOn (fan a h ε₀) (Metric.ball (0 : ℂ) δ)) :
    Tendsto (fun k => fan a h (ε k) ((x k).2.1)) atTop (nhds (fan a h ε₀ W)) := by
  have hWmem : W ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hW
  have hmem : ∀ k, (x k).2.1 ∈ Metric.ball (0 : ℂ) δ := fun k => by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hzs k
  have hct : Tendsto (fan a h ε₀) (nhds W) (nhds (fan a h ε₀ W)) :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds hWmem)
  have h1 : Tendsto (fun k => fan a h ε₀ ((x k).2.1)) atTop (nhds (fan a h ε₀ W)) :=
    Filter.Tendsto.comp hct hz
  refine h1.congr' (Eventually.of_forall fun k => ?_)
  exact (heq k (hmem k)).symm

/-- A real characteristic value with positive real part has modulus equal to its real part. -/
theorem norm_charVal_eq_re {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} (him : (charVal a h ε).im = 0)
    (hre0 : 0 < (charVal a h ε).re) : ‖charVal a h ε‖ = (charVal a h ε).re := by
  have h2 : ‖charVal a h ε‖ ^ 2 = (charVal a h ε).re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
    ring
  nlinarith [norm_nonneg (charVal a h ε), hre0, h2]

/-- A characteristic value that is real and lies in `(0,1)` has modulus at most `1`. -/
theorem norm_charVal_le_one {a : ℝ} {h : ℂ → ℂ} {ε : List Bool}
    (him : (charVal a h ε).im = 0) (hre0 : 0 < (charVal a h ε).re)
    (hre1 : (charVal a h ε).re < 1) : ‖charVal a h ε‖ ≤ 1 := by
  rw [norm_charVal_eq_re him hre0]; exact le_of_lt hre1

theorem stable_trichotomy_of_cluster {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∀ {δ : ℝ}, 0 < δ → Work.EQ.FanTrich a h δ →
      (∀ ε : List Bool, ContinuousOn (Work.EQ.fan a h ε) (Metric.ball (0 : ℂ) δ)) →
      ∀ {N : ℕ} {W : ℂ} {x : ℕ → Work.EQ.ChainData} {ε : ℕ → List Bool},
        (∀ k, Work.EQ.IsChain a h (x k)) →
        (∀ k, (x k).1 0 = Work.EQ.fan a h (ε k) (x k).2.1) →
        (∀ k, ‖(x k).2.1‖ < δ) →
        (∀ k, Work.EQ.LaNnas.UnNear a ((x k).1 (-(N : ℤ))) (1 / 4)) →
        Filter.Tendsto (fun k => (x k).2.1) Filter.atTop (nhds W) →
        ‖W‖ < δ →
        ∃ ε₀ μ₁, μ₁ ∈ Work.EQ.charValSet a h ∧ ‖μ₁‖ ≤ 1 ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Filter.Tendsto (fun k => Work.EQ.fan a h (ε (φ k)) ((x (φ k)).2.1)) Filter.atTop
              (nhds (Work.EQ.fan a h ε₀ (μ₁ * W))) := by
  intro δ hδ htrich hcont N W x ε hchain hread hnorm hnear hlim hW
  obtain ⟨φ, hφ, hcase⟩ := htrich ε
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hzφ : Tendsto (fun k => (x (φ k)).2.1) atTop (nhds W) := hlim.comp hφtop
  have hmem : ∀ k, (x (φ k)).2.1 ∈ Metric.ball (0 : ℂ) δ := fun k => by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hnorm (φ k)
  rcases hcase with ⟨ε₀, hagree⟩
    | ⟨ε₀, ε₁, s, C, hs, hword, hCret, hε₁fan, hμim, hμre0, hμre1, hunif⟩
    | ⟨hcount, hflat⟩
  · -- case (i): all the fan maps of the subsequence agree on the ball
    have hlim_i : Tendsto (fun k => fan a h (ε (φ k)) ((x (φ k)).2.1)) atTop
        (nhds (fan a h ε₀ W)) :=
      tendsto_fan_of_eventually_eq (ε := fun k => ε (φ k)) (x := fun k => x (φ k)) (ε₀ := ε₀)
        hagree hzφ (fun k => hnorm (φ k)) hW (hcont ε₀)
    refine ⟨ε₀, 1, Or.inl rfl, by simp, φ, hφ, ?_⟩
    simpa using hlim_i
  · -- case (ii): uniform convergence to `fan a h ε₀ (charVal a h ε₁ ·)`
    have hμlt : ‖charVal a h ε₁‖ < 1 := by
      rw [norm_charVal_eq_re hμim hμre0]; exact hμre1
    refine ⟨ε₀, charVal a h ε₁, Or.inr ⟨ε₁, hε₁fan, rfl⟩,
      norm_charVal_le_one hμim hμre0 hμre1, φ, hφ, ?_⟩
    exact tendsto_fan_of_uniform_limit (ε := fun k => ε (φ k)) (x := fun k => x (φ k))
      (μ := charVal a h ε₁) (ε₀ := ε₀) hunif hzφ (fun k => hnorm (φ k)) hW hμlt (hcont ε₀)
  · -- case (iii): the shrinking (flat) case is impossible
    exfalso
    obtain ⟨η₀, hη₀pos, hnotflat⟩ := LaTB.not_flat_of_unNear ha0 ha1 N
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hflat η₀ hη₀pos)
    obtain ⟨hfl1, hfl2⟩ := hK K le_rfl ((x (φ K)).2.1) (hmem K)
    obtain ⟨Y, hY⟩ := ((FanSep.axis_walk (a := a) ha0 ha1 hh).2 (ε (φ K))).2
    exact hnotflat (hchain (φ K)).1 (hread (φ K)) (hnear (φ K)) hY hfl1 hfl2

end Work.EQ
