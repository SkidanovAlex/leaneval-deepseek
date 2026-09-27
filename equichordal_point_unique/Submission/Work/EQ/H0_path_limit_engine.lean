import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.H0_path_limit_fwd_tail

/-! # The convergence engine for `H0_path_limit`

This module contains the branch-cut-safe propagation of convergence along a continuous path of
chains of the equichordal relation, used by `Work.EQ.H0_path_limit` and its case lemmas.

The *label* ("which of the two local branches of the relation is used at index `n`") is **not**
continuous along a path: the principal square root of the radicand has a branch cut and a path can
cross it (the two labelled values then coincide in the limit and the label flips while the chain
stays continuous).  What *is* continuous is the branch *coefficient*: for `EqRelC a P Q` with
`sig2 a P ≠ 0` there is a unique `μ = stepCoeff a P Q` with `Q + P = μ • (P - O₂)`, it is a
continuous function of `(P,Q)`, and `μ² * sig2 a P = 1`; symmetrically `P + Q = ν • (Q - O₁)` with
`ν = backCoeff a P Q`.

Hence along a *connected* parameter interval a path of `EqRelC`-pairs can only follow one branch
once `sig2` (resp. `sig1`) of the converged coordinate is nonzero, and: *if one chain coordinate
converges and the limit is regular, then the next one converges as well*
(`chain_coord_succ`, `chain_coord_pred`).

Also here: the uniform backward tail (`H0_path_limit_bwd_tail`), the window of a path of chains
(`pathWindow`), and the analyticity of the end map `w ↦ germC a h (λ ^ n₁ * w)`.
-/

namespace Work.EQ

open Filter _root_.Topology Set Metric

set_option maxHeartbeats 800000

noncomputable section

/-! ## The branch coefficients of a step of the equichordal relation -/

/-- `O₂ = (a/2, 0)` as a point of `ℂ²`. -/
private def ptO2 (a : ℝ) : ℂ × ℂ := (((a / 2 : ℝ) : ℂ), 0)

/-- The isotropic-square form of `P` about `O₂`: `(P.1 - a/2)² + P.2²`.  This is the denominator
of the forward branch of the relation at `P`; it vanishes exactly on the isotropic lines through
`O₂`, i.e. exactly where the forward step of `EqRelC` degenerates. -/
def sig2 (a : ℝ) (P : ℂ × ℂ) : ℂ := (P.1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2

/-- The isotropic-square form of `Q` about `O₁ = (-a/2,0)`, the denominator of the backward
branch. -/
def sig1 (a : ℝ) (Q : ℂ × ℂ) : ℂ := (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2

/-- **The branch coefficient of a forward step.**  If `EqRelC a P Q` and `sig2 a P ≠ 0`, then the
vector `Q + P` is a multiple of the vector `P - O₂`; `stepCoeff a P Q` is that multiple.  Unlike
the branch *label*, it is a continuous function of `(P, Q)`. -/
def stepCoeff (a : ℝ) (P Q : ℂ × ℂ) : ℂ :=
  ((Q.1 + P.1) * (P.1 - ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * P.2) / sig2 a P

/-- **The branch coefficient of a backward step**: `P + Q = ν • (Q - O₁)`. -/
def backCoeff (a : ℝ) (P Q : ℂ × ℂ) : ℂ :=
  ((Q.1 + P.1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * Q.2) / sig1 a Q

theorem stepCoeff_spec {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hP : sig2 a P ≠ 0) :
    Q.1 + P.1 = stepCoeff a P Q * (P.1 - ((a / 2 : ℝ) : ℂ)) ∧
    Q.2 + P.2 = stepCoeff a P Q * P.2 := by
  obtain ⟨h1, h2⟩ := h
  have key1 : (Q.1 + P.1) * sig2 a P
      = ((Q.1 + P.1) * (P.1 - ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * P.2)
          * (P.1 - ((a / 2 : ℝ) : ℂ)) := by
    rw [sig2]; linear_combination (norm := ring_nf) P.2 * h2
  have key2 : (Q.2 + P.2) * sig2 a P
      = ((Q.1 + P.1) * (P.1 - ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * P.2) * P.2 := by
    rw [sig2]; linear_combination (norm := ring_nf) (-(P.1 - ((a / 2 : ℝ) : ℂ))) * h2
  have e1 : stepCoeff a P Q * (P.1 - ((a / 2 : ℝ) : ℂ))
      = ((Q.1 + P.1) * (P.1 - ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * P.2)
          * (P.1 - ((a / 2 : ℝ) : ℂ)) / sig2 a P := by
    rw [stepCoeff]; ring
  have e2 : stepCoeff a P Q * P.2
      = ((Q.1 + P.1) * (P.1 - ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * P.2) * P.2 / sig2 a P := by
    rw [stepCoeff]; ring
  constructor
  · rw [e1, eq_div_iff hP]; exact key1
  · rw [e2, eq_div_iff hP]; exact key2

/-- The fundamental relation of the branch coefficient: `μ² sig2(P) = 1`. -/
theorem stepCoeff_sq {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hP : sig2 a P ≠ 0) :
    stepCoeff a P Q ^ 2 * sig2 a P = 1 := by
  obtain ⟨e1, e2⟩ := stepCoeff_spec h hP
  have h1 := h.1
  rw [e1, e2] at h1
  rw [sig2]
  linear_combination (norm := ring_nf) h1

theorem backCoeff_spec {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hQ : sig1 a Q ≠ 0) :
    Q.1 + P.1 = backCoeff a P Q * (Q.1 + ((a / 2 : ℝ) : ℂ)) ∧
    Q.2 + P.2 = backCoeff a P Q * Q.2 := by
  obtain ⟨h1, h2⟩ := h
  have hcr : (Q.1 + P.1) * Q.2 = (Q.2 + P.2) * (Q.1 + ((a / 2 : ℝ) : ℂ)) := by
    linear_combination (norm := ring_nf) (-(h2))
  have key1 : (Q.1 + P.1) * sig1 a Q
      = ((Q.1 + P.1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * Q.2)
          * (Q.1 + ((a / 2 : ℝ) : ℂ)) := by
    rw [sig1]; linear_combination (norm := ring_nf) Q.2 * hcr
  have key2 : (Q.2 + P.2) * sig1 a Q
      = ((Q.1 + P.1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * Q.2) * Q.2 := by
    rw [sig1]; linear_combination (norm := ring_nf) (-(Q.1 + ((a / 2 : ℝ) : ℂ))) * hcr
  have e1 : backCoeff a P Q * (Q.1 + ((a / 2 : ℝ) : ℂ))
      = ((Q.1 + P.1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * Q.2)
          * (Q.1 + ((a / 2 : ℝ) : ℂ)) / sig1 a Q := by
    rw [backCoeff]; ring
  have e2 : backCoeff a P Q * Q.2
      = ((Q.1 + P.1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) + (Q.2 + P.2) * Q.2) * Q.2 / sig1 a Q := by
    rw [backCoeff]; ring
  constructor
  · rw [e1, eq_div_iff hQ]; exact key1
  · rw [e2, eq_div_iff hQ]; exact key2

theorem backCoeff_sq {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hQ : sig1 a Q ≠ 0) :
    backCoeff a P Q ^ 2 * sig1 a Q = 1 := by
  obtain ⟨e1, e2⟩ := backCoeff_spec h hQ
  have h1 := h.1
  rw [e1, e2] at h1
  rw [sig1]
  linear_combination (norm := ring_nf) h1

/-! ## Mirroring and shifting a path of chains -/

/-- The bisector reflection is continuous. -/
private theorem continuous_eqMirror : Continuous (eqMirror : ℂ × ℂ → ℂ × ℂ) := by
  unfold eqMirror
  exact Continuous.prodMk
    ((continuous_fst : Continuous (Prod.fst : ℂ × ℂ → ℂ)).neg)
    (continuous_snd : Continuous (Prod.snd : ℂ × ℂ → ℂ))

/-- The bisector mirror `mirrorChain` is continuous. -/
theorem continuous_mirrorChain : Continuous (mirrorChain : ChainData → ChainData) := by
  unfold mirrorChain
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine continuous_pi (fun n => ?_)
    exact continuous_eqMirror.comp
      ((continuous_apply (-n)).comp (continuous_fst : Continuous (Prod.fst : ChainData → ℤ → ℂ × ℂ)))
  · exact (continuous_snd : Continuous (Prod.snd : ℂ × ℂ → ℂ)).comp
      (continuous_snd : Continuous (Prod.snd : ChainData → ℂ × ℂ))
  · exact (continuous_fst : Continuous (Prod.fst : ℂ × ℂ → ℂ)).comp
      (continuous_snd : Continuous (Prod.snd : ChainData → ℂ × ℂ))

/-- The coordinate projections of a continuous path of chains are continuous. -/
theorem continuousOn_coord {γ : ℝ → ChainData} {S : ℝ} (hcont : ContinuousOn γ (Set.Ici S))
    (n : ℤ) : ContinuousOn (fun s => (γ s).1 n) (Set.Ici S) :=
  ((continuous_apply n).comp continuous_fst).comp_continuousOn hcont

/-- The `ψ₁`-coordinate of a continuous path of chains is continuous. -/
theorem continuousOn_psi1 {γ : ℝ → ChainData} {S : ℝ} (hcont : ContinuousOn γ (Set.Ici S)) :
    ContinuousOn (fun s => (γ s).2.1) (Set.Ici S) :=
  (continuous_fst.comp continuous_snd).comp_continuousOn hcont

/-- The `ψ₂`-coordinate of a continuous path of chains is continuous. -/
theorem continuousOn_psi2 {γ : ℝ → ChainData} {S : ℝ} (hcont : ContinuousOn γ (Set.Ici S)) :
    ContinuousOn (fun s => (γ s).2.2) (Set.Ici S) :=
  (continuous_snd.comp continuous_snd).comp_continuousOn hcont

/-- `eqMirror` is an involution. -/
private theorem eqMirror_invol (Z : ℂ × ℂ) : eqMirror (eqMirror Z) = Z := by
  unfold eqMirror
  simp

/-- The backward tail of a continuous path of chains, obtained from
`Work.EQ.H0_path_limit_fwd_tail` applied to the mirror path. -/
theorem H0_path_limit_bwd_tail {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData} {S : ℝ}
    (hγ : ∀ s, S ≤ s → IsChain a h (γ s)) (hcont : ContinuousOn γ (Set.Ici S))
    {v : ℂ} (hv : v ≠ 0) (h2 : Tendsto (fun s => (γ s).2.2) atTop (𝓝 v)) :
    ∃ m₁ : ℕ, ∀ s, S ≤ s → ∀ n : ℕ, m₁ ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2) := by
  have hγ' : ∀ s, S ≤ s → IsChain a h (mirrorChain (γ s)) :=
    fun s hs => isChain_mirrorChain (hγ s hs)
  have hcont' : ContinuousOn (fun s => mirrorChain (γ s)) (Set.Ici S) :=
    continuous_mirrorChain.comp_continuousOn hcont
  have h2' : Tendsto (fun s => (mirrorChain (γ s)).2.1) atTop (𝓝 v) := by
    simpa [mirrorChain] using h2
  obtain ⟨m₁, hm₁⟩ := H0_path_limit_fwd_tail ha0 ha1 hh hγ' hcont' hv h2'
  refine ⟨m₁, fun s hs n hn => ?_⟩
  have hm := hm₁ s hs n hn
  rw [mirrorChain_psi1] at hm
  have hE : eqMirror ((γ s).1 (-(n : ℤ))) =
      germC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2) := by
    have hh2 := hm
    rwa [mirrorChain_fst] at hh2
  have h2 := congrArg eqMirror hE
  simpa [eqMirror_invol, ugermC] using h2


/-- **The window of a path of chains.**  `pathWindow γ n₁ m₁ s j` is the point of the chain
`γ s` at the index `j - m₁`, so that `j : Fin (n₁ + m₁ + 1)` runs through the indices
`-m₁, …, n₁`. -/
def pathWindow (γ : ℝ → ChainData) (n₁ m₁ : ℕ) (s : ℝ) : Fin (n₁ + m₁ + 1) → ℂ × ℂ :=
  fun j => (γ s).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))

/-- **The end map of the `F3` application is analytic near `u`.**  `germC a h` is analytic on a
ball around `0` (`Work.EQ.germC_facts`), so `w ↦ germC a h (λ^{n₁} w)` is analytic on a
neighbourhood of any `u` with `‖λ^{n₁} u‖` inside that ball. -/
theorem exists_analyticOnNhd_germC_end {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {n₁ : ℕ} {u : ℂ} {ρg : ℝ} (hρg : 0 < ρg)
    (hAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hlt : ‖((eqLam a : ℝ) : ℂ) ^ n₁ * u‖ < ρg) :
    ∃ R : ℝ, 0 < R ∧
      AnalyticOnNhd ℂ (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w))
        (Metric.ball u R) := by
  have hlamne : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; rw [eqLam]; positivity
  set c₀ : ℝ := ‖((eqLam a : ℝ) : ℂ) ^ n₁‖ with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]; exact norm_pos_iff.mpr (pow_ne_zero n₁ hlamne)
  have hc₀u : c₀ * ‖u‖ < ρg := by
    have h := hlt
    rw [norm_mul, ← hc₀] at h
    exact h
  have hu_lt : ‖u‖ < ρg / c₀ := by
    rw [lt_div_iff₀ hc₀pos, mul_comm]
    exact hc₀u
  refine ⟨(ρg / c₀ - ‖u‖) / 2, by linarith, ?_⟩
  intro w hw
  have hw' : ‖w‖ < ‖u‖ + (ρg / c₀ - ‖u‖) / 2 := by
    have h := hw
    rw [Metric.mem_ball, dist_eq_norm] at h
    calc ‖w‖ = ‖(w - u) + u‖ := by ring_nf
      _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le _ _
      _ < (ρg / c₀ - ‖u‖) / 2 + ‖u‖ := by linarith [h]
      _ = ‖u‖ + (ρg / c₀ - ‖u‖) / 2 := by ring
  have hmem : ((eqLam a : ℝ) : ℂ) ^ n₁ * w ∈ Metric.ball (0 : ℂ) ρg := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul]
    have : ‖((eqLam a : ℝ) : ℂ) ^ n₁‖ = c₀ := hc₀
    rw [this]
    calc c₀ * ‖w‖ < c₀ * (‖u‖ + (ρg / c₀ - ‖u‖) / 2) :=
          mul_lt_mul_of_pos_left hw' hc₀pos
      _ = (ρg + c₀ * ‖u‖) / 2 := by field_simp; ring
      _ < ρg := by linarith [hc₀u]
  have hg : AnalyticAt ℂ (germC a h) (((eqLam a : ℝ) : ℂ) ^ n₁ * w) := hAn _ hmem
  have hf : AnalyticAt ℂ (fun v : ℂ => ((eqLam a : ℝ) : ℂ) ^ n₁ * v) w := by fun_prop
  have hc := hg.comp hf
  simpa [Function.comp_def] using hc


/-! ## The convergence engine -/

/-- **The engine, abstract form.**  A continuous path `g : ℝ → ℂ` whose square converges to a
nonzero limit converges: the two candidate square roots of the limit are a positive distance apart,
so continuity of the path between them is impossible. -/
theorem tendsto_of_sq_tendsto_atTop {g : ℝ → ℂ} {L : ℂ} (hL : L ≠ 0) {S : ℝ}
    (hg : ContinuousOn g (Set.Ici S)) (h : Tendsto (fun t => g t ^ 2) atTop (𝓝 L)) :
    ∃ B : ℂ, Tendsto g atTop (𝓝 B) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ 2 = L :=
    ⟨L ^ ((2 : ℂ))⁻¹, Complex.cpow_nat_inv_pow L (n := 2) (by norm_num)⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : L = 0 := by simpa using hc.symm
    exact hL this
  have hcnorm : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc0
  have hcc : dist c (-c) = 2 * ‖c‖ := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_mul, norm_mul]; norm_num
  set δ₁ : ℝ := ‖c‖ / 4 with hδ₁
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁]; positivity
  have hδ₁le : δ₁ ≤ ‖c‖ / 3 := by rw [hδ₁]; linarith
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ ‖c‖ / 3 →
      (∀ᶠ t in atTop, g t ∈ Metric.ball c δ) ∨ (∀ᶠ t in atTop, g t ∈ Metric.ball (-c) δ) := by
    intro δ hδ hδle
    have hsq : ∀ᶠ t in atTop, ‖g t ^ 2 - L‖ < δ ^ 2 := by
      have hb : Metric.ball L (δ ^ 2) ∈ 𝓝 L := Metric.ball_mem_nhds L (by positivity)
      have hthis := h hb
      filter_upwards [hthis] with t ht
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at ht
      exact ht
    obtain ⟨T, hT⟩ := eventually_atTop.1 hsq
    have hdisjδ : Disjoint (Metric.ball c δ) (Metric.ball (-c) δ) := by
      rw [disjoint_left]
      intro z hz1 hz2
      have h1' : dist z c < δ := hz1
      have h2' : dist z (-c) < δ := hz2
      have htri : dist c (-c) ≤ dist c z + dist z (-c) := dist_triangle c z (-c)
      rw [dist_comm c z] at htri
      rw [hcc] at htri
      linarith
    have hsub : g '' Set.Ici (max S T) ⊆ Metric.ball c δ ∪ Metric.ball (-c) δ := by
      rintro z ⟨t, ht, rfl⟩
      have htT : T ≤ t := le_trans (le_max_right S T) ht
      have hgt : ‖g t ^ 2 - L‖ < δ ^ 2 := hT t htT
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨h1', h2'⟩ := hcon
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at h1'
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at h2'
      have h2'' : δ ≤ ‖g t + c‖ := by simpa [add_comm] using h2'
      have hprod : δ * δ ≤ ‖g t - c‖ * ‖g t + c‖ :=
        mul_le_mul h1' h2'' hδ.le (norm_nonneg _)
      have heq : ‖g t - c‖ * ‖g t + c‖ = ‖g t ^ 2 - L‖ := by
        rw [← norm_mul, ← hc]
        congr 1
        ring
      rw [heq] at hprod
      nlinarith [hgt]
    have himg : IsPreconnected (g '' Set.Ici (max S T)) :=
      isPreconnected_Ici.image g (hg.mono (Ici_subset_Ici.mpr (le_max_left S T)))
    rcases himg.subset_or_subset isOpen_ball isOpen_ball hdisjδ hsub with hcase | hcase
    · left
      filter_upwards [eventually_ge_atTop (max S T)] with t ht
      exact hcase ⟨t, ht, rfl⟩
    · right
      filter_upwards [eventually_ge_atTop (max S T)] with t ht
      exact hcase ⟨t, ht, rfl⟩
  have contradiction_step : ∀ {δ δ' : ℝ}, δ ≤ δ₁ → δ' ≤ δ₁ → ∀ z : ℂ,
      z ∈ Metric.ball c δ → z ∈ Metric.ball (-c) δ' → False := by
    intro δ δ' h1 h2 z hz1 hz2
    have h1' : dist z c < δ := hz1
    have h2' : dist z (-c) < δ' := hz2
    have htri : dist c (-c) ≤ dist c z + dist z (-c) := dist_triangle c z (-c)
    rw [dist_comm c z] at htri
    rw [hcc] at htri
    rw [hδ₁] at h1 h2
    linarith
  rcases key δ₁ hδ₁pos hδ₁le with hbase | hbase
  · refine ⟨c, ?_⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ' : 0 < min ε δ₁ := lt_min hε hδ₁pos
    have hle' : min ε δ₁ ≤ ‖c‖ / 3 := le_trans (min_le_right _ _) hδ₁le
    rcases key (min ε δ₁) hδ' hle' with hcase | hcase
    · filter_upwards [hcase] with t ht
      exact lt_of_lt_of_le ht (min_le_left _ _)
    · exfalso
      obtain ⟨t, ht1, ht2⟩ := (hbase.and hcase).exists
      exact contradiction_step le_rfl (min_le_right _ _) (g t) ht1 ht2
  · refine ⟨-c, ?_⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ' : 0 < min ε δ₁ := lt_min hε hδ₁pos
    have hle' : min ε δ₁ ≤ ‖c‖ / 3 := le_trans (min_le_right _ _) hδ₁le
    rcases key (min ε δ₁) hδ' hle' with hcase | hcase
    · exfalso
      obtain ⟨t, ht1, ht2⟩ := (hbase.and hcase).exists
      exact contradiction_step (min_le_right _ _) le_rfl (g t) ht2 ht1
    · filter_upwards [hcase] with t ht
      exact lt_of_lt_of_le ht (min_le_left _ _)

theorem continuous_sig2 (a : ℝ) : Continuous (sig2 a) := by
  unfold sig2; fun_prop

theorem continuous_sig1 (a : ℝ) : Continuous (sig1 a) := by
  unfold sig1; fun_prop

attribute [fun_prop] continuous_sig2 continuous_sig1

theorem continuousOn_stepCoeff_of {a : ℝ} {P Q : ℝ → ℂ × ℂ} {S T : ℝ}
    (hcont : ContinuousOn (fun t => (P t, Q t)) (Set.Ici S))
    (hT : ∀ t, T ≤ t → sig2 a (P t) ≠ 0) (hTS : S ≤ T) :
    ContinuousOn (fun t => stepCoeff a (P t) (Q t)) (Set.Ici T) := by
  have hsub : Set.Ici T ⊆ Set.Ici S := Ici_subset_Ici.mpr hTS
  have hP : ContinuousOn P (Set.Ici T) := continuous_fst.comp_continuousOn (hcont.mono hsub)
  have hQ : ContinuousOn Q (Set.Ici T) := continuous_snd.comp_continuousOn (hcont.mono hsub)
  have hnum : ContinuousOn (fun t => ((Q t).1 + (P t).1) * ((P t).1 - ((a / 2 : ℝ) : ℂ))
      + ((Q t).2 + (P t).2) * (P t).2) (Set.Ici T) := by fun_prop
  have hden : ContinuousOn (fun t => sig2 a (P t)) (Set.Ici T) := by fun_prop
  have hdiv := hnum.div hden (fun t ht => hT t ht)
  refine hdiv.congr ?_
  intro t ht
  simp only [Pi.div_apply, stepCoeff]

theorem continuousOn_backCoeff_of {a : ℝ} {P Q : ℝ → ℂ × ℂ} {S T : ℝ}
    (hcont : ContinuousOn (fun t => (P t, Q t)) (Set.Ici S))
    (hT : ∀ t, T ≤ t → sig1 a (Q t) ≠ 0) (hTS : S ≤ T) :
    ContinuousOn (fun t => backCoeff a (P t) (Q t)) (Set.Ici T) := by
  have hsub : Set.Ici T ⊆ Set.Ici S := Ici_subset_Ici.mpr hTS
  have hP : ContinuousOn P (Set.Ici T) := continuous_fst.comp_continuousOn (hcont.mono hsub)
  have hQ : ContinuousOn Q (Set.Ici T) := continuous_snd.comp_continuousOn (hcont.mono hsub)
  have hnum : ContinuousOn (fun t => ((Q t).1 + (P t).1) * ((Q t).1 + ((a / 2 : ℝ) : ℂ))
      + ((Q t).2 + (P t).2) * (Q t).2) (Set.Ici T) := by fun_prop
  have hden : ContinuousOn (fun t => sig1 a (Q t)) (Set.Ici T) := by fun_prop
  have hdiv := hnum.div hden (fun t ht => hT t ht)
  refine hdiv.congr ?_
  intro t ht
  simp only [Pi.div_apply, backCoeff]

/-- **The engine, concrete form.**  Let `(P t, Q t)` be a path of pairs satisfying the equichordal
relation, and suppose `P t → A` with `sig2 a A ≠ 0`.  Then `Q t` converges.  This is the fact that
a path can only follow one branch of the relation: the two candidate branch values are always a
distance `≥ 2` apart, so a continuous selection is forced. -/
theorem tendsto_of_eqRelC_forward {a : ℝ} {P Q : ℝ → ℂ × ℂ} {A : ℂ × ℂ} {S : ℝ}
    (hrel : ∀ t, S ≤ t → EqRelC a (P t) (Q t))
    (hcont : ContinuousOn (fun t => (P t, Q t)) (Set.Ici S))
    (hP : Tendsto P atTop (𝓝 A)) (hA : sig2 a A ≠ 0) :
    ∃ B : ℂ × ℂ, Tendsto Q atTop (𝓝 B) := by
  have hσ : Tendsto (fun t => sig2 a (P t)) atTop (𝓝 (sig2 a A)) :=
    ((continuous_sig2 a).tendsto A).comp hP
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hσ.eventually_ne hA)
  set T : ℝ := max S T₀ with hT
  have hTS : S ≤ T := le_max_left _ _
  have hcontr : ContinuousOn (fun t => stepCoeff a (P t) (Q t)) (Set.Ici T) :=
    continuousOn_stepCoeff_of hcont (fun t ht => hT₀ t (le_trans (le_max_right S T₀) ht)) hTS
  have hsquare : ∀ t, T ≤ t → stepCoeff a (P t) (Q t) ^ 2 = (sig2 a (P t))⁻¹ := by
    intro t ht
    have h1 := stepCoeff_sq (hrel t (le_trans hTS ht)) (hT₀ t (le_trans (le_max_right S T₀) ht))
    have h2 : sig2 a (P t) * stepCoeff a (P t) (Q t) ^ 2 = 1 := by rw [mul_comm]; exact h1
    exact eq_inv_of_mul_eq_one_right h2
  have hsq_tend : Tendsto (fun t => stepCoeff a (P t) (Q t) ^ 2) atTop (𝓝 ((sig2 a A)⁻¹)) := by
    refine Tendsto.congr' ?_ ((hσ.inv₀ hA))
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hsquare t ht).symm
  have hAinv : (sig2 a A)⁻¹ ≠ 0 := inv_ne_zero hA
  obtain ⟨B', hB'⟩ := tendsto_of_sq_tendsto_atTop hAinv hcontr hsq_tend
  have hP' : Tendsto P atTop (𝓝 A.1 ×ˢ 𝓝 A.2) := by rw [← nhds_prod_eq]; exact hP
  refine ⟨(-A.1 + B' * (A.1 - ((a / 2 : ℝ) : ℂ)), -A.2 + B' * A.2), ?_⟩
  apply Tendsto.prodMk_nhds
  · have h1 : Tendsto (fun t => -(P t).1 + stepCoeff a (P t) (Q t) * ((P t).1 - ((a / 2 : ℝ) : ℂ)))
        atTop (𝓝 (-A.1 + B' * (A.1 - ((a / 2 : ℝ) : ℂ)))) :=
      ((hP'.fst.neg).add (hB'.mul (hP'.fst.sub tendsto_const_nhds)))
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_ge_atTop T] with t ht
    have hspec := (stepCoeff_spec (hrel t (le_trans hTS ht))
      (hT₀ t (le_trans (le_max_right S T₀) ht))).1
    show -(P t).1 + stepCoeff a (P t) (Q t) * ((P t).1 - ((a / 2 : ℝ) : ℂ)) = (Q t).1
    rw [← hspec]; ring
  · have h2 : Tendsto (fun t => -(P t).2 + stepCoeff a (P t) (Q t) * (P t).2)
        atTop (𝓝 (-A.2 + B' * A.2)) :=
      ((hP'.snd.neg).add (hB'.mul hP'.snd))
    refine Tendsto.congr' ?_ h2
    filter_upwards [eventually_ge_atTop T] with t ht
    have hspec := (stepCoeff_spec (hrel t (le_trans hTS ht))
      (hT₀ t (le_trans (le_max_right S T₀) ht))).2
    show -(P t).2 + stepCoeff a (P t) (Q t) * (P t).2 = (Q t).2
    rw [← hspec]; ring

/-- **The engine, backward form.**  If `Q t → A` with `sig1 a A ≠ 0`, then `P t` converges. -/
theorem tendsto_of_eqRelC_backward {a : ℝ} {P Q : ℝ → ℂ × ℂ} {A : ℂ × ℂ} {S : ℝ}
    (hrel : ∀ t, S ≤ t → EqRelC a (P t) (Q t))
    (hcont : ContinuousOn (fun t => (P t, Q t)) (Set.Ici S))
    (hQ : Tendsto Q atTop (𝓝 A)) (hA : sig1 a A ≠ 0) :
    ∃ B : ℂ × ℂ, Tendsto P atTop (𝓝 B) := by
  have hσ : Tendsto (fun t => sig1 a (Q t)) atTop (𝓝 (sig1 a A)) :=
    ((continuous_sig1 a).tendsto A).comp hQ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hσ.eventually_ne hA)
  set T : ℝ := max S T₀ with hT
  have hTS : S ≤ T := le_max_left _ _
  have hcontr : ContinuousOn (fun t => backCoeff a (P t) (Q t)) (Set.Ici T) :=
    continuousOn_backCoeff_of hcont (fun t ht => hT₀ t (le_trans (le_max_right S T₀) ht)) hTS
  have hsquare : ∀ t, T ≤ t → backCoeff a (P t) (Q t) ^ 2 = (sig1 a (Q t))⁻¹ := by
    intro t ht
    have h1 := backCoeff_sq (hrel t (le_trans hTS ht)) (hT₀ t (le_trans (le_max_right S T₀) ht))
    have h2 : sig1 a (Q t) * backCoeff a (P t) (Q t) ^ 2 = 1 := by rw [mul_comm]; exact h1
    exact eq_inv_of_mul_eq_one_right h2
  have hsq_tend : Tendsto (fun t => backCoeff a (P t) (Q t) ^ 2) atTop (𝓝 ((sig1 a A)⁻¹)) := by
    refine Tendsto.congr' ?_ ((hσ.inv₀ hA))
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hsquare t ht).symm
  have hAinv : (sig1 a A)⁻¹ ≠ 0 := inv_ne_zero hA
  obtain ⟨B', hB'⟩ := tendsto_of_sq_tendsto_atTop hAinv hcontr hsq_tend
  have hQ' : Tendsto Q atTop (𝓝 A.1 ×ˢ 𝓝 A.2) := by rw [← nhds_prod_eq]; exact hQ
  refine ⟨(B' * (A.1 + ((a / 2 : ℝ) : ℂ)) - A.1, B' * A.2 - A.2), ?_⟩
  apply Tendsto.prodMk_nhds
  · have h1 : Tendsto (fun t => backCoeff a (P t) (Q t) * ((Q t).1 + ((a / 2 : ℝ) : ℂ)) - (Q t).1)
        atTop (𝓝 (B' * (A.1 + ((a / 2 : ℝ) : ℂ)) - A.1)) :=
      ((hB'.mul (hQ'.fst.add tendsto_const_nhds)).sub hQ'.fst)
    refine Tendsto.congr' ?_ h1
    filter_upwards [eventually_ge_atTop T] with t ht
    have hspec := (backCoeff_spec (hrel t (le_trans hTS ht))
      (hT₀ t (le_trans (le_max_right S T₀) ht))).1
    show backCoeff a (P t) (Q t) * ((Q t).1 + ((a / 2 : ℝ) : ℂ)) - (Q t).1 = (P t).1
    rw [← hspec]; ring
  · have h2 : Tendsto (fun t => backCoeff a (P t) (Q t) * (Q t).2 - (Q t).2)
        atTop (𝓝 (B' * A.2 - A.2)) :=
      ((hB'.mul hQ'.snd).sub hQ'.snd)
    refine Tendsto.congr' ?_ h2
    filter_upwards [eventually_ge_atTop T] with t ht
    have hspec := (backCoeff_spec (hrel t (le_trans hTS ht))
      (hT₀ t (le_trans (le_max_right S T₀) ht))).2
    show backCoeff a (P t) (Q t) * (Q t).2 - (Q t).2 = (P t).2
    rw [← hspec]; ring

/-- **Chain-level corollary (forward).**  If the coordinate at index `M` of a continuous path of
chains converges to a point whose forward radicand is nonzero, then the coordinate at index `M+1`
converges as well. -/
theorem chain_coord_succ {a : ℝ} {h : ℂ → ℂ} {γ : ℝ → ChainData} {S : ℝ}
    (hchain : ∀ s, S ≤ s → IsChain a h (γ s)) (hcont : ContinuousOn γ (Set.Ici S))
    {M : ℤ} {A : ℂ × ℂ} (hM : Tendsto (fun s => (γ s).1 M) atTop (𝓝 A))
    (hA : sig2 a A ≠ 0) :
    ∃ B : ℂ × ℂ, Tendsto (fun s => (γ s).1 (M + 1)) atTop (𝓝 B) := by
  have hcoord : ∀ n : ℤ, ContinuousOn (fun s => (γ s).1 n) (Set.Ici S) := fun n =>
    ((continuous_apply n).comp continuous_fst).comp_continuousOn hcont
  refine tendsto_of_eqRelC_forward (a := a) (P := fun s => (γ s).1 M)
    (Q := fun s => (γ s).1 (M + 1)) (A := A) (S := S) ?_ ?_ hM hA
  · intro s hs
    exact ((hchain s hs).1 M).1
  · exact ContinuousOn.prodMk (hcoord M) (hcoord (M + 1))

/-- **Chain-level corollary (backward).**  If the coordinate at index `M` converges to a point whose
backward radicand is nonzero, then the coordinate at index `M-1` converges as well. -/
theorem chain_coord_pred {a : ℝ} {h : ℂ → ℂ} {γ : ℝ → ChainData} {S : ℝ}
    (hchain : ∀ s, S ≤ s → IsChain a h (γ s)) (hcont : ContinuousOn γ (Set.Ici S))
    {M : ℤ} {A : ℂ × ℂ} (hM : Tendsto (fun s => (γ s).1 M) atTop (𝓝 A))
    (hA : sig1 a A ≠ 0) :
    ∃ B : ℂ × ℂ, Tendsto (fun s => (γ s).1 (M - 1)) atTop (𝓝 B) := by
  have hcoord : ∀ n : ℤ, ContinuousOn (fun s => (γ s).1 n) (Set.Ici S) := fun n =>
    ((continuous_apply n).comp continuous_fst).comp_continuousOn hcont
  refine tendsto_of_eqRelC_backward (a := a) (P := fun s => (γ s).1 (M - 1))
    (Q := fun s => (γ s).1 M) (A := A) (S := S) ?_ ?_ hM hA
  · intro s hs
    have hreg := (hchain s hs).1 (M - 1)
    rw [show M - 1 + 1 = M by ring] at hreg
    exact hreg.1
  · exact ContinuousOn.prodMk (hcoord (M - 1)) (hcoord M)

end

end Work.EQ
