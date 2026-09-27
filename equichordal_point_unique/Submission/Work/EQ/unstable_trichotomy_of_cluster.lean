import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.la_nnas
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.H0_invParam_ge

namespace Work.EQ

open Filter

/-- **Unstable trichotomy of a cluster of chains.**  Under Rychlik's trichotomy `FanTrich` at
radius `δ`, a family of chains whose `-N`-th point is `eqMirror` of a fan value with parameter
`w k → W` inside `B(0,δ)`, and whose `0`-th point is `1/4`-near an unstable axis centre, has a
subsequence on which the fan values converge to `fan η₀ (μ₂ W)` with `μ₂` a characteristic
value of modulus `≤ 1`.  Case (iii) of the trichotomy (the flattening of the fan) is incompatible
with the chain through the parity separation `no_near_axis_segment`. -/
theorem unstable_trichotomy_of_cluster {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∀ {δ : ℝ}, 0 < δ → Work.EQ.FanTrich a h δ →
      (∀ ε : List Bool, ContinuousOn (Work.EQ.fan a h ε) (Metric.ball (0 : ℂ) δ)) →
      ∀ {N : ℕ} {W : ℂ} {x : ℕ → Work.EQ.ChainData} {w : ℕ → ℂ} {η : ℕ → List Bool},
        (∀ k, Work.EQ.IsChain a h (x k)) →
        (∀ k, (x k).1 (-(N : ℤ)) = Work.EQ.eqMirror (Work.EQ.fan a h (η k) (w k))) →
        (∀ k, ‖w k‖ < δ) →
        (∀ k, Work.EQ.LaNnas.SnNear a ((x k).1 0) (1 / 4)) →
        Filter.Tendsto w Filter.atTop (nhds W) →
        ‖W‖ < δ →
        ∃ η₀ μ₂, μ₂ ∈ Work.EQ.charValSet a h ∧ ‖μ₂‖ ≤ 1 ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Filter.Tendsto (fun k => Work.EQ.fan a h (η (φ k)) (w (φ k))) Filter.atTop
              (nhds (Work.EQ.fan a h η₀ (μ₂ * W))) := by
  intro δ hδ htri hcont N W x w η hx hxN hw hsn hwt hW
  obtain ⟨φ, hφmono, htri'⟩ := htri η
  have hwφ : Tendsto (fun k => w (φ k)) atTop (nhds W) := hwt.comp hφmono.tendsto_atTop
  have hmem : ∀ k, w (φ k) ∈ Metric.ball (0 : ℂ) δ := fun k => by
    rw [Metric.mem_ball, dist_zero_right]; exact hw (φ k)
  have hWmem : W ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hW
  have hwithin : Tendsto (fun k => w (φ k)) atTop (nhdsWithin W (Metric.ball (0 : ℂ) δ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hwφ
      (Filter.Eventually.of_forall hmem)
  rcases htri' with ⟨ε₀, hε₀⟩ | ⟨ε₀, ε₁, s, C, hst, hword, hC, he₁, him, hpos, hlt, huni⟩ |
    ⟨hvis, hflat⟩
  · -- Case (i): all the words agree with `ε₀` on the disc.
    refine ⟨ε₀, 1, Or.inl rfl, by simp, φ, hφmono, ?_⟩
    have htend : Tendsto (fun k => fan a h ε₀ (w (φ k))) atTop (nhds (fan a h ε₀ W)) :=
      ((hcont ε₀).continuousWithinAt hWmem).tendsto.comp hwithin
    have hpt : ∀ k, fan a h (η (φ k)) (w (φ k)) = fan a h ε₀ (w (φ k)) := by
      intro k
      exact hε₀ _ (hmem k)
    have hres : Tendsto (fun k => fan a h (η (φ k)) (w (φ k))) atTop (nhds (fan a h ε₀ W)) :=
      Filter.Tendsto.congr (fun k => (hpt k).symm) htend
    simpa using hres
  · -- Case (ii): the words split as `ε₀ ++ true^{s k} ++ C k` and the fans converge uniformly.
    have hsq : ‖charVal a h ε₁‖ ^ 2 = (charVal a h ε₁).re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, him]; ring
    have hμle : ‖charVal a h ε₁‖ ≤ 1 := by
      have hlt1 : ‖charVal a h ε₁‖ < 1 := by
        have h3 : ‖charVal a h ε₁‖ ^ 2 < 1 := by rw [hsq]; nlinarith
        nlinarith [norm_nonneg (charVal a h ε₁)]
      linarith
    refine ⟨ε₀, charVal a h ε₁, Or.inr ⟨ε₁, he₁, rfl⟩, hμle, φ, hφmono, ?_⟩
    have hμWmem : charVal a h ε₁ * W ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg W) hμle) hW
    have hfanAt : ContinuousAt (fan a h ε₀) (charVal a h ε₁ * W) :=
      (hcont ε₀).continuousAt (Metric.isOpen_ball.mem_nhds hμWmem)
    have hcw : ContinuousWithinAt (fun u : ℂ => fan a h ε₀ (charVal a h ε₁ * u))
        (Metric.ball (0 : ℂ) δ) W :=
      (hfanAt.comp (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
    exact huni.tendsto_comp hcw hwithin
  · -- Case (iii): the fan flattens to the axis; incompatible with the chain.
    exfalso
    obtain ⟨η', hη'pos, hη'⟩ := LaNnas.no_near_axis_segment (a := a) ha0 ha1 N
    obtain ⟨k, hk⟩ := Filter.Eventually.exists (hflat η' hη'pos)
    have hkw : w (φ k) ∈ Metric.ball (0 : ℂ) δ := hmem k
    obtain ⟨hf1, hf2⟩ := hk (w (φ k)) hkw
    set P : ℂ × ℂ := fan a h (η (φ k)) (w (φ k)) with hPdef
    have hcentre : (fan a h (η (φ k)) 0).1
        = ((stCtr (stAux (η (φ k)).reverse 0) : ℝ) : ℂ) :=
      congrArg Prod.fst (fan_centre_walk ha0 ha1 hh (η (φ k)))
    obtain ⟨Y₀, hY₀⟩ := hsn (φ k)
    set Pfun : ℕ → ℂ × ℂ := fun m => (x (φ k)).1 (-(N : ℤ) + (m : ℤ)) with hPfun
    have hreg : ∀ m < N, RegPair a (Pfun m) (Pfun (m + 1)) := by
      intro m hm
      have hcast : -(N : ℤ) + ((m + 1 : ℕ) : ℤ) = -(N : ℤ) + (m : ℤ) + 1 := by
        push_cast; ring
      change RegPair a ((x (φ k)).1 (-(N : ℤ) + (m : ℤ)))
        ((x (φ k)).1 (-(N : ℤ) + ((m + 1 : ℕ) : ℤ)))
      rw [hcast]
      exact (hx (φ k)).1 (-(N : ℤ) + (m : ℤ))
    refine ((hη' Pfun hreg (-stIdx (stAux (η (φ k)).reverse 0)) Y₀).2
      ⟨⟨?_, ?_⟩, ?_, ?_⟩).elim
    · -- first coordinate of `Pfun 0 = (x (φ k)).1 (-N)` is near the unstable centre
      have hp0 : Pfun 0 = (x (φ k)).1 (-(N : ℤ)) := by simp [Pfun]
      rw [hp0, hxN (φ k)]
      have hmm : (eqMirror P).1 = -(P.1) := rfl
      have hcast : (1 / 2 : ℂ) + 2 * (((-stIdx (stAux (η (φ k)).reverse 0)) : ℤ) : ℂ)
          = -(((stCtr (stAux (η (φ k)).reverse 0) : ℝ)) : ℂ) := by
        rw [stCtr]; push_cast; ring
      rw [hmm, hcast, ← hcentre, hPdef]
      have hneg : -(fan a h (η (φ k)) (w (φ k))).1 - -(fan a h (η (φ k)) 0).1
          = -((fan a h (η (φ k)) (w (φ k))).1 - (fan a h (η (φ k)) 0).1) := by ring
      rw [hneg, norm_neg]
      exact le_of_lt hf1
    · -- second coordinate ratio
      have hp0 : Pfun 0 = (x (φ k)).1 (-(N : ℤ)) := by simp [Pfun]
      rw [hp0, hxN (φ k)]
      have hmm1 : (eqMirror P).1 = -(P.1) := rfl
      have hmm2 : (eqMirror P).2 = P.2 := rfl
      rw [hmm2, hmm1, hPdef]
      have hsub : -(fan a h (η (φ k)) (w (φ k))).1 + ((a / 2 : ℝ) : ℂ)
          = -((fan a h (η (φ k)) (w (φ k))).1 - ((a / 2 : ℝ) : ℂ)) := by ring
      rw [hsub, norm_neg]
      exact le_of_lt hf2
    · -- `Pfun N = (x (φ k)).1 0` is `1/4`-near its stable centre
      have hpN : Pfun N = (x (φ k)).1 0 := by simp [Pfun]
      rw [hpN]
      exact hY₀.1
    · have hpN : Pfun N = (x (φ k)).1 0 := by simp [Pfun]
      rw [hpN]
      have h := hY₀.2
      linarith

end Work.EQ
