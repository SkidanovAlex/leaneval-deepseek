import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_path_limit_engine
import Submission.Work.EQ.leg_window_eq
import Submission.Work.EQ.H0_path_limit_window
import Submission.Work.EQ.chain_unique_window
import Submission.Work.EQ.chain_unique_window_closeness
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.branchPt_meromorphic

namespace Work.EQ

open Filter _root_.Topology Set Metric

open scoped Topology

set_option maxHeartbeats 1200000

noncomputable section

/-! ## Elementary helpers -/

/-- For `|k| ≤ K` the integer `k` occurs as an index of the window `Fin (K+K+1)`. -/
lemma exists_window_index {K : ℕ} {k : ℤ} (hk : |k| ≤ (K : ℤ)) :
    ∃ j : Fin (K + K + 1), (((j : ℕ) : ℤ) - (K : ℤ)) = k := by
  refine ⟨⟨(k + (K : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 : k ≤ (K : ℤ) := (abs_le.mp hk).2
    have : k + (K : ℤ) < ((K + K + 1 : ℕ) : ℤ) := by omega
    omega
  · have h0 : 0 ≤ k + (K : ℤ) := by
      have h1 : -(K : ℤ) ≤ k := (abs_le.mp hk).1
      omega
    rw [Int.toNat_of_nonneg h0]
    ring

/-- Close to a parameter `x` of the tail the whole window is close to the window at `x`. -/
lemma exists_window_close {γ : ℝ → ChainData} {S : ℝ} (hcont : ContinuousOn γ (Set.Ici S))
    {K : ℕ} {x : ℝ} (hxS : S ≤ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, S ≤ z → |z - x| < δ →
      ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖(γ z).1 k - (γ x).1 k‖ < 1 / 2 := by
  have hperj : ∀ j : Fin (K + K + 1), ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, S ≤ z → |z - x| < δ →
      ‖(γ z).1 (((j : ℕ) : ℤ) - (K : ℤ)) - (γ x).1 (((j : ℕ) : ℤ) - (K : ℤ))‖ < 1 / 2 := by
    intro j
    have hcw : ContinuousWithinAt (fun s : ℝ => (γ s).1 (((j : ℕ) : ℤ) - (K : ℤ)))
        (Set.Ici S) x :=
      (continuousOn_coord hcont (((j : ℕ) : ℤ) - (K : ℤ))).continuousWithinAt hxS
    have hmem : Metric.ball ((γ x).1 (((j : ℕ) : ℤ) - (K : ℤ))) (1 / 2) ∈
        𝓝 ((γ x).1 (((j : ℕ) : ℤ) - (K : ℤ))) := Metric.ball_mem_nhds _ (by norm_num)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp (hcw.preimage_mem_nhdsWithin hmem)
    refine ⟨δ, hδ, fun z hzS hzx => ?_⟩
    have hzball : z ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
      exact hzx
    simpa [Metric.mem_ball, dist_eq_norm] using hδsub ⟨hzball, hzS⟩
  choose δ hδpos hδspec using hperj
  refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hδpos j)
  · intro z hzS hzx k hk
    obtain ⟨j, hj⟩ := exists_window_index (K := K) hk
    have hjle : Finset.univ.inf' Finset.univ_nonempty δ ≤ δ j :=
      Finset.inf'_le _ (Finset.mem_univ j)
    have := hδspec j z hzS (lt_of_lt_of_le hzx hjle)
    simpa [hj] using this

/-- Two visit times in the tail with close windows have equal chains. -/
lemma visit_chain_eq_of_close {a : ℝ} {h : ℂ → ℂ} {γ : ℝ → ChainData} {S T₀ : ℝ} {K : ℕ}
    {u : ℂ} {ρg : ℝ}
    (hinj : Set.InjOn (fun w => (germC a h w).2) (Metric.ball (0 : ℂ) ρg)) (hρg : 0 < ρg)
    (hchain : ∀ s, S ≤ s → IsChain a h (γ s))
    (hfwd : ∀ s, S ≤ s → ∀ n : ℕ, K ≤ n →
      (γ s).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * (γ s).2.1))
    (hbwd : ∀ s, S ≤ s → ∀ n : ℕ, K ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (γ s).2.2))
    (hball : ∀ s, T₀ ≤ s → (eqLam a : ℂ) ^ K * (γ s).2.2 ∈ Metric.ball (0 : ℂ) ρg)
    {x y : ℝ} (hxS : S ≤ x) (hyS : S ≤ y) (hxT : T₀ ≤ x) (hyT : T₀ ≤ y)
    (hxu : (γ x).2.1 = u) (hyu : (γ y).2.1 = u)
    (hwin : ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖(γ x).1 k - (γ y).1 k‖ < 1 / 2) :
    γ x = γ y :=
  chain_unique_window_closeness (N := K) (M := K) (K := K) le_rfl le_rfl hρg hinj
    (γ x) (γ y) (hchain x hxS) (hchain y hyS) (hxu.trans hyu.symm) hwin
    (hball x hxT) (hball y hyT)
    (fun n hn => hfwd x hxS n hn) (fun n hn => hfwd y hyS n hn)
    (fun n hn => hbwd x hxS n hn) (fun n hn => hbwd y hyS n hn)


/-- Frequent-visit case of Rychlik's path-limit step.

Given a path `γ : ℝ → ChainData` continuous on `Set.Ici S` with values in `Work.EQ.H0 a h` there,
along which the chain parameters converge to nonzero limits `u`, `v`, suppose in addition that
`(γ s).2.1 = u` for arbitrarily large `s` (a visit to the fibre of `ψ₁` over its own limit).  Then
`γ` converges in `H0`.

Route which is known to be sound, with the pitfalls written out.

Setup.  `A = {s ≥ S | ψ₁ (γ s) = u}` is closed and unbounded; its complement in `[S,∞)` is a union
of open intervals ("legs").  Fix the uniform tails `n₁`, `m₁` from
`Work.EQ.H0_path_limit_fwd_tail` and `Work.EQ.H0_path_limit_bwd_tail` (both in
`Submission.Work.EQ.H0_path_limit_engine`), put `N = n₁ + m₁`,
`c w = Work.EQ.germC a h (λ ^ n₁ * w)` and let `W s` be the window
`j ↦ (γ s).1 (j - m₁) : Fin (N + 1) → ℂ × ℂ`, a continuous curve of regular backward
`EqRelC`-chains of length `N` ending at `c (ψ₁ (γ s))` with first entry
`ugermC a h (λ ^ m₁ * ψ₂ (γ s))`.

(a) On each connected component of `A` the path is constant: visit points lie in the fibre of `ψ₁`
over `u`, which is discrete because `Work.EQ.H0_structure` gives a neighbourhood of every point of
`H0` on which `ψ₁` is injective on `H0`; a continuous map from a connected set into a discrete set
is constant.

(b) Let `J` be a connected component of the complement of `A` that meets a sufficiently large tail.
On `J` one has `0 < |ψ₁ (γ s) - u| < (rhoFin' a c u R N) ^ (2 ^ N)` (`R` from
`Work.EQ.exists_analyticOnNhd_germC_end`, increasing `n₁` makes `c` analytic), so
`Work.EQ.H0_path_limit_window` applies on `J` and gives one sign sequence `σ_J` and a parameter
`t_J` with `t_J s ^ (2 ^ N) = ψ₁ (γ s) - u` and `W s = branchPt a c u R σ_J (t_J s)` for `s ∈ J`.
As `s` approaches an endpoint of `J` from inside, `t_J s → 0` and `W s` converges (continuity of
the coordinates of `γ`), so some coordinate of `branchPt a c u R σ_J` is bounded along a punctured
sequence tending to `0`; by `Work.EQ.branchPt_meromorphic` each coordinate is meromorphic at `0`,
and a meromorphic function which is bounded along a punctured sequence tending to `0` has a limit
along `𝓝[≠] 0` (this is available as `Work.Topology.meromorphic_tendsto_of_bounded_seq`).  Hence
both endpoints of the leg `J` give the same value of `W`, i.e. consecutive visits have equal
windows.

(c) `Work.EQ.chain_unique_window` (module `Submission.Work.EQ.chain_unique_window`) then forces two
visit chains with equal windows to be equal: they have the same `ψ₁ = u`, their `ψ₂` values tend to
`v` (so they are eventually within its `ε`), the windows agree, and both satisfy the same uniform
tails.  So all sufficiently late visit chains are equal to a single `q ∈ H0`.

(d) Since `|t_J s| ^ (2 ^ N) = |ψ₁ (γ s) - u| → 0` uniformly along the whole tail,
`W s → W q` as `s → ∞` on every leg and `γ s = q` at visits; with the convergent tails this gives
`γ s → q`, and `q ∈ H0`.

Two tempting shortcuts which are WRONG and cost time; do not take them.

(i) "Take a visit time `s₀`, the section `f` of `ψ₁` through `γ s₀` over a disc `D ∋ u`, and the
time `T` from which `ψ₁ (γ s) ∈ D`; then `{s ≥ T | γ s = f (ψ₁ (γ s))}` is clopen in the connected
`Set.Ici T` and nonempty, so it is all of `Set.Ici T`."  The clopen half is fine (closedness uses
continuity of `f` on `D` together with `ψ₁ (γ s) ∈ D` for `s ≥ T`; openness uses local injectivity
of `ψ₁`), but NONEMPTINESS is exactly the content: a later visit time `s ≥ T` gives
`f (ψ₁ (γ s)) = f u = γ s₀`, which need not be `γ s`.  A visit chain different from `γ s₀` may
exist, and then the set is empty.

(ii) "The window `W s` equals one of the `2 ^ N` branch-word candidates, each a continuous function
of `(ψ₁ (γ s), ψ₂ (γ s))`, so the branch word is locally constant and one word works on the whole
tail."  The candidates built from `Work.EQ.invBranch` are NOT continuous in their arguments: the
principal square root has a branch cut, and a path may cross it while the chain stays continuous
(this is why `Submission.Work.EQ.H0_path_limit_engine` uses the continuous branch *coefficient*
`stepCoeff` instead of the labelled branches).  The branch word is genuinely not locally constant. -/
theorem H0_path_limit_visit_case {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {γ : ℝ → Work.EQ.ChainData} {S : ℝ}
    (hγ : ∀ s : ℝ, S ≤ s → γ s ∈ Work.EQ.H0 a h)
    (hcont : ContinuousOn γ (Set.Ici S))
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : Filter.Tendsto (fun s : ℝ => (γ s).2.1) Filter.atTop (nhds u))
    (h2 : Filter.Tendsto (fun s : ℝ => (γ s).2.2) Filter.atTop (nhds v))
    (hfreq : ∃ᶠ s in Filter.atTop, (γ s).2.1 = u) :
    ∃ q ∈ Work.EQ.H0 a h, Filter.Tendsto γ Filter.atTop (nhds q) := by 
  classical
  -- ## 0. chains and the uniform tails
  have hchain : ∀ s : ℝ, S ≤ s → IsChain a h (γ s) := fun s hs => isChain_of_mem_H0 (hγ s hs)
  obtain ⟨n₀, hn₀⟩ := H0_path_limit_fwd_tail ha0 ha1 hh hchain hcont hu h1
  obtain ⟨m₀, hm₀⟩ := H0_path_limit_bwd_tail ha0 ha1 hh hchain hcont hv h2
  obtain ⟨ρg, hρg, hgermAn, -, -, hinj, -⟩ := germC_facts (h := h) ha0 ha1 hh
  have hl0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hl1le : eqLam a ≤ 1 := le_of_lt hl1
  -- ## 1. the window radius `K`
  obtain ⟨K₁, hK₁⟩ : ∃ K : ℕ, ‖((eqLam a : ℝ) : ℂ) ^ K * u‖ < ρg := by
    rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
    · refine ⟨0, ?_⟩
      have huz : u = 0 := norm_eq_zero.mp hzero.symm
      rw [huz, mul_zero, norm_zero]; exact hρg
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hρg hpos) hl1
      refine ⟨k, ?_⟩
      rw [norm_eqLam_pow_mul ha0 ha1 k u]
      calc eqLam a ^ k * ‖u‖ < (ρg / ‖u‖) * ‖u‖ := by gcongr
        _ = ρg := div_mul_cancel₀ ρg (ne_of_gt hpos)
  obtain ⟨K₂, hK₂⟩ : ∃ K : ℕ, eqLam a ^ K * ‖v‖ < ρg / 2 := by
    rcases eq_or_lt_of_le (norm_nonneg v) with hzero | hpos
    · refine ⟨0, ?_⟩
      rw [← hzero, mul_zero]; linarith
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (by linarith : (0:ℝ) < ρg / 2) hpos) hl1
      refine ⟨k, ?_⟩
      calc eqLam a ^ k * ‖v‖ = ‖v‖ * eqLam a ^ k := by ring
        _ < ‖v‖ * (ρg / 2 / ‖v‖) := by gcongr
        _ = ρg / 2 := by field_simp
  set K : ℕ := max (max n₀ m₀) (max K₁ K₂) with hKdef
  have hKn : n₀ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKm : m₀ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK₁K : K₁ ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂K : K₂ ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hKu : ‖((eqLam a : ℝ) : ℂ) ^ K * u‖ < ρg := by
    rw [norm_eqLam_pow_mul ha0 ha1 K u]
    calc eqLam a ^ K * ‖u‖ ≤ eqLam a ^ K₁ * ‖u‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hl0.le hl1le hK₁K) (norm_nonneg u)
      _ = ‖((eqLam a : ℝ) : ℂ) ^ K₁ * u‖ := (norm_eqLam_pow_mul ha0 ha1 K₁ u).symm
      _ < ρg := hK₁
  have hKv : eqLam a ^ K * ‖v‖ < ρg / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hl0.le hl1le hK₂K)
      (norm_nonneg v)) hK₂
  -- ## 2. the analytic end map and the Puiseux radius
  obtain ⟨R, hR, hcAn⟩ := exists_analyticOnNhd_germC_end (h := h) (r := r) ha0 ha1 hh
    (n₁ := K) (u := u) (ρg := ρg) hρg hgermAn hKu
  set ρ : ℝ :=
    rhoFin' a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ K * w)) u R (K + K) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact rhoFin'_pos hR hcAn
  have hρpow : 0 < ρ ^ (2 ^ (K + K)) := pow_pos hρpos _
  -- rewriting the literal Puiseux radius to `ρ`
  have hρconv : ∀ s : ℝ,
      ‖(γ s).2.1 - u‖ < ρ ^ (2 ^ (K + K)) →
      ‖(γ s).2.1 - u‖ < (rhoFin' a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ K * w))
        u R (K + K)) ^ (2 ^ (K + K)) := by
    intro s h
    rw [← hρdef]
    exact h
  -- ## 3. thresholds and a large visit time
  obtain ⟨T₁, hT₁⟩ : ∃ T : ℝ, ∀ s : ℝ, T ≤ s → ‖(γ s).2.1 - u‖ < ρ ^ (2 ^ (K + K)) := by
    obtain ⟨T, hT⟩ := eventually_atTop.1 (h1 (Metric.ball_mem_nhds u (ε := ρ ^ (2 ^ (K + K))) hρpow))
    refine ⟨T, fun s hs => ?_⟩
    have h := hT s hs
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact h
  obtain ⟨T₂, hT₂⟩ : ∃ T : ℝ, ∀ s : ℝ, T ≤ s → ‖(γ s).2.2 - v‖ < ρg / 2 := by
    obtain ⟨T, hT⟩ := eventually_atTop.1 (h2 (Metric.ball_mem_nhds v (ε := ρg / 2) (by linarith)))
    refine ⟨T, fun s hs => ?_⟩
    have h := hT s hs
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact h
  obtain ⟨T₀, hT₀S, hT₀T₁, hT₀T₂, hT₀u⟩ :
      ∃ t : ℝ, S ≤ t ∧ T₁ ≤ t ∧ T₂ ≤ t ∧ (γ t).2.1 = u := by
    obtain ⟨s, hsu, hsm⟩ := (hfreq.and_eventually (eventually_ge_atTop (max S (max T₁ T₂)))).exists
    exact ⟨s, le_trans (le_max_left _ _) hsm,
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsm,
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hsm, hsu⟩
  set q : ChainData := γ T₀ with hqdef
  have hqmem : q ∈ H0 a h := by rw [hqdef]; exact hγ T₀ hT₀S
  have hqpsi1 : q.2.1 = u := by rw [hqdef]; exact hT₀u
  -- uniform tails at threshold `K`, and the ball condition
  have hfwd : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, K ≤ n →
      (γ s).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * (γ s).2.1) :=
    fun s hs n hn => hn₀ s hs n (le_trans hKn hn)
  have hbwd : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, K ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (γ s).2.2) :=
    fun s hs n hn => hm₀ s hs n (le_trans hKm hn)
  have hball : ∀ s : ℝ, T₀ ≤ s → (eqLam a : ℂ) ^ K * (γ s).2.2 ∈ Metric.ball (0 : ℂ) ρg := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right]
    have hbd : ‖(γ s).2.2‖ ≤ ‖v‖ + ρg / 2 := by
      have h := hT₂ s (le_trans hT₀T₂ hs)
      calc ‖(γ s).2.2‖ = ‖(γ s).2.2 - v + v‖ := by ring_nf
        _ ≤ ‖(γ s).2.2 - v‖ + ‖v‖ := norm_add_le _ _
        _ ≤ ρg / 2 + ‖v‖ := by linarith
        _ = ‖v‖ + ρg / 2 := by ring
    calc ‖((eqLam a : ℝ) : ℂ) ^ K * (γ s).2.2‖ = eqLam a ^ K * ‖(γ s).2.2‖ :=
          norm_eqLam_pow_mul ha0 ha1 K _
      _ ≤ eqLam a ^ K * (‖v‖ + ρg / 2) := mul_le_mul_of_nonneg_left hbd (pow_nonneg hl0.le K)
      _ = eqLam a ^ K * ‖v‖ + eqLam a ^ K * (ρg / 2) := by ring
      _ < ρg / 2 + ρg / 2 := by
          refine add_lt_add_of_lt_of_le hKv ?_
          exact mul_le_of_le_one_left (by linarith) (pow_le_one₀ hl0.le hl1le)
      _ = ρg := by ring
  -- ## 4. the visit set `A`
  set A : Set ℝ := {x : ℝ | S ≤ x ∧ (γ x).2.1 = u} with hAdef
  have hAclosed : IsClosed A := by
    rw [hAdef]
    have h := ContinuousOn.preimage_isClosed_of_isClosed (continuousOn_psi1 hcont) isClosed_Ici
      (isClosed_singleton (x := u))
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage,
      Set.mem_singleton_iff]
  have hfreq' : ∀ T : ℝ, ∃ x ∈ A, T ≤ x := by
    intro T
    obtain ⟨s, hsu, hsm⟩ := (hfreq.and_eventually (eventually_ge_atTop (max S T))).exists
    exact ⟨s, ⟨le_trans (le_max_left _ _) hsm, hsu⟩, le_trans (le_max_right _ _) hsm⟩
  -- ## 5. local rigidity of the visit chain, and the chain at visits
  have hloc : ∀ x : ℝ, T₀ ≤ x → (γ x).2.1 = u → ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, T₀ ≤ z → |z - x| < δ → (γ z).2.1 = u → γ z = γ x := by
    intro x hxT hxu
    obtain ⟨δ, hδpos, hδ⟩ := exists_window_close hcont (le_trans hT₀S hxT) (K := K)
    refine ⟨δ, hδpos, fun z hzT hzx hzu => ?_⟩
    exact visit_chain_eq_of_close (S := S) (T₀ := T₀) (K := K)
      hinj hρg hchain hfwd hbwd hball
      (le_trans hT₀S hzT) (le_trans hT₀S hxT) hzT hxT hzu hxu
      (fun k hk => hδ z (le_trans hT₀S hzT) hzx k hk)
  have key : ∀ x : ℝ, T₀ ≤ x → (γ x).2.1 = u → γ x = q := by
    intro x hxT hxu
    by_contra hxne
    set B : Set ℝ := {z : ℝ | T₀ ≤ z ∧ (γ z).2.1 = u ∧ γ z ≠ q} with hBdef
    have hBne : B.Nonempty := ⟨x, hxT, hxu, hxne⟩
    have hBbd : BddBelow B := ⟨T₀, fun z hz => hz.1⟩
    set c : ℝ := sInf B with hcdef
    have hT₀c : T₀ ≤ c := le_csInf hBne (fun z hz => hz.1)
    have hc_approx : ∀ ε : ℝ, 0 < ε → ∃ b ∈ B, b < c + ε := by
      intro ε hε
      have hlt : sInf B < c + ε := by rw [hcdef]; linarith
      exact (csInf_lt_iff hBbd hBne).mp hlt
    have hcA : c ∈ A := by
      have hmem : sInf B ∈ closure B := csInf_mem_closure hBne hBbd
      have hsub : closure B ⊆ A :=
        hAclosed.closure_subset_iff.mpr (fun z hz => ⟨le_trans hT₀S hz.1, hz.2.1⟩)
      exact hsub hmem
    have hgood_below : ∀ z : ℝ, T₀ ≤ z → z < c → (γ z).2.1 = u → γ z = q := by
      intro z hzT hzc hzu
      by_contra hzne
      have hzB : z ∈ B := ⟨hzT, hzu, hzne⟩
      have := csInf_le hBbd hzB
      linarith
    have hc_good : γ c = q := by
      rcases eq_or_lt_of_le hT₀c with hc_eq | hc_gt
      · rw [hqdef, ← hc_eq]
      · set A' : Set ℝ := A ∩ Set.Ico T₀ c with hA'def
        have hT₀A : T₀ ∈ A := ⟨hT₀S, hT₀u⟩
        have hA'ne : A'.Nonempty := ⟨T₀, ⟨hT₀A, le_rfl, hc_gt⟩⟩
        have hA'bd : BddAbove A' := ⟨c, fun z hz => le_of_lt hz.2.2⟩
        set asup : ℝ := sSup A' with hasupdef
        have hT₀asup : T₀ ≤ asup := le_csSup hA'bd ⟨hT₀A, le_rfl, hc_gt⟩
        have hasupc : asup ≤ c := csSup_le hA'ne (fun z hz => le_of_lt hz.2.2)
        have hasupA : asup ∈ A := by
          have hmem : asup ∈ closure A' := csSup_mem_closure hA'ne hA'bd
          exact (hAclosed.closure_subset_iff.mpr (fun z hz => hz.1)) hmem
        have hnoA : ∀ z : ℝ, asup < z → z < c → ¬ (S ≤ z ∧ (γ z).2.1 = u) := by
          intro z haz hzc hz
          have hzA' : z ∈ A' := ⟨hz, le_trans hT₀asup (le_of_lt haz), hzc⟩
          have : z ≤ asup := le_csSup hA'bd hzA'
          linarith
        rcases lt_or_eq_of_le hasupc with halt | haeq
        · have hcl : ∀ s : ℝ, asup < s → s < c →
              ‖(γ s).2.1 - u‖ < (rhoFin' a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ K * w))
                u R (K + K)) ^ (2 ^ (K + K)) := by
            intro s hsx hsy
            exact hρconv s (hT₁ s (le_trans hT₀T₁ (le_trans hT₀asup (le_of_lt hsx))))
          have hwin : ∀ k : ℤ, |k| ≤ (K : ℤ) → ‖(γ asup).1 k - (γ c).1 k‖ < 1 / 2 := by
            intro k hk
            obtain ⟨j, hj⟩ := exists_window_index (K := K) hk
            have hjeq : (γ asup).1 (((j : ℕ) : ℤ) - (K : ℤ)) = (γ c).1 (((j : ℕ) : ℤ) - (K : ℤ)) :=
              leg_window_eq (a := a) ha0 ha1 hh (γ := γ) (S := S) (n₁ := K) (m₁ := K)
                (u := u) hu (R := R) hR hcAn hchain hcont hfwd hbwd halt
                (le_trans hT₀S hT₀asup) (le_trans hT₀S hT₀c) hasupA.2 hcA.2
                (fun s hsx hsy hzu =>
                  hnoA s hsx hsy ⟨le_trans hT₀S (le_trans hT₀asup (le_of_lt hsx)), hzu⟩) hcl j
            rw [← hj]
            have hzero : (γ asup).1 (((j : ℕ) : ℤ) - (K : ℤ)) - (γ c).1 (((j : ℕ) : ℤ) - (K : ℤ)) = 0 := by
              rw [hjeq, sub_self]
            rw [hzero, norm_zero]; norm_num
          have heq : γ asup = γ c := visit_chain_eq_of_close (S := S) (T₀ := T₀) (K := K)
            hinj hρg hchain hfwd hbwd hball
            (le_trans hT₀S hT₀asup) (le_trans hT₀S hT₀c) hT₀asup hT₀c hasupA.2 hcA.2 hwin
          have hasupq : γ asup = q := hgood_below asup hT₀asup halt hasupA.2
          rw [← heq]; exact hasupq
        · have hseq : ∀ n : ℕ, ∃ z ∈ A', c - 1 / ((n : ℝ) + 1) < z := by
            intro n
            have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            have hlt : c - 1 / ((n : ℝ) + 1) < sSup A' := by
              rw [← hasupdef, ← haeq]; linarith
            exact (lt_csSup_iff hA'bd hA'ne).mp hlt
          choose zseq hzA' hzlt using hseq
          have hzup : ∀ n : ℕ, zseq n ≤ c := by
            intro n
            have h1 := le_csSup hA'bd (hzA' n)
            rw [← hasupdef] at h1
            rwa [haeq] at h1
          have hzlim : Tendsto zseq atTop (𝓝 c) := by
            have hlower : Tendsto (fun n : ℕ => c - 1 / ((n : ℝ) + 1)) atTop (𝓝 c) := by
              have h1 : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
              have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
                tendsto_one_div_add_atTop_nhds_zero_nat
              have h := h1.sub h2
              simpa using h
            refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds ?_ ?_
            · intro n; exact le_of_lt (hzlt n)
            · intro n; exact hzup n
          have hγz : ∀ n : ℕ, γ (zseq n) = q :=
            fun n => hgood_below (zseq n) (hzA' n).2.1 (hzA' n).2.2 (hzA' n).1.2
          have hlim : Tendsto (fun n : ℕ => γ (zseq n)) atTop (𝓝 (γ c)) := by
            have hcw : ContinuousWithinAt γ (Set.Ici S) c :=
              hcont.continuousWithinAt (le_trans hT₀S hT₀c)
            refine hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hzlim, ?_⟩)
            exact Filter.Eventually.of_forall (fun n => le_trans hT₀S (hzA' n).2.1)
          have hconst : Tendsto (fun n : ℕ => γ (zseq n)) atTop (𝓝 q) := by
            have hfun : (fun n : ℕ => γ (zseq n)) = fun _ => q := funext hγz
            rw [hfun]; exact tendsto_const_nhds
          rw [tendsto_nhds_unique hlim hconst]
    -- bad visits accumulate at `c` from above, contradicting local constancy
    obtain ⟨δ, hδpos, hδspec⟩ := hloc c hT₀c hcA.2
    obtain ⟨b, hbB, hblt⟩ := hc_approx δ hδpos
    have hcb : c ≤ b := csInf_le hBbd hbB
    have hclose : |b - c| < δ := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact hbB.2.2 ((hδspec b hbB.1 hclose hbB.2.1).trans hc_good)
  -- ## 6. the local section through `q` and the clopen argument
  obtain ⟨ρf, hρf, f, hfSect⟩ := hasSection_of_structure (H0_structure ha0 ha1 hh).2.1 q hqmem
  obtain ⟨Tf, hTf⟩ : ∃ T : ℝ, ∀ s : ℝ, T ≤ s → (γ s).2.1 ∈ Metric.ball q.2.1 ρf := by
    have h1' : Tendsto (fun s : ℝ => (γ s).2.1) atTop (𝓝 q.2.1) := by
      rw [hqpsi1]; exact h1
    obtain ⟨T, hT⟩ := eventually_atTop.1 (h1' (Metric.ball_mem_nhds q.2.1 hρf))
    exact ⟨T, fun s hs => hT s hs⟩
  set σ : ℝ := max T₀ Tf with hσdef
  have hσS : S ≤ σ := le_trans hT₀S (le_max_left _ _)
  have hcontσ : ContinuousOn γ (Set.Ici σ) := hcont.mono (Ici_subset_Ici.mpr hσS)
  set P : Set ↥(Set.Ici σ) := {s | γ (s : ℝ) = f ((γ (s : ℝ)).2.1)} with hPdef
  have hfcomp : ContinuousOn (fun s : ℝ => f ((γ s).2.1)) (Set.Ici σ) := by
    refine hfSect.continuousOn.comp ((continuousOn_psi1 hcont).mono (Ici_subset_Ici.mpr hσS)) ?_
    intro s hs
    exact hTf s (le_trans (le_max_right T₀ Tf) hs)
  have hPclosed : IsClosed P := by
    rw [hPdef]
    exact isClosed_eq hcontσ.domRestrict hfcomp.domRestrict
  have hPopen : IsOpen P := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hs' : γ (s : ℝ) = f ((γ (s : ℝ)).2.1) := hs
    have hxH : γ (s : ℝ) ∈ H0 a h := hγ (s : ℝ) (le_trans hσS s.2)
    obtain ⟨U, hUo, hxU, hUinj⟩ :=
      localInj_of_localHomeomorph (H0_structure ha0 ha1 hh).1 (γ (s : ℝ)) hxH
    have hmem1 : {t : ↥(Set.Ici σ) | γ (t : ℝ) ∈ U} ∈ 𝓝 s :=
      hcontσ.domRestrict.continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)
    have hmem2 : {t : ↥(Set.Ici σ) | f ((γ (t : ℝ)).2.1) ∈ U} ∈ 𝓝 s := by
      have hval : f ((γ (s : ℝ)).2.1) = γ (s : ℝ) := hs'.symm
      refine hfcomp.domRestrict.continuousAt.preimage_mem_nhds (hUo.mem_nhds ?_)
      show f ((γ (s : ℝ)).2.1) ∈ U
      rw [hval]; exact hxU
    refine Filter.mem_of_superset (Filter.inter_mem hmem1 hmem2) ?_
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have htS : S ≤ (t : ℝ) := le_trans hσS t.2
    have hbalt : (γ (t : ℝ)).2.1 ∈ Metric.ball q.2.1 ρf :=
      hTf _ (le_trans (le_max_right T₀ Tf) t.2)
    show γ (t : ℝ) = f ((γ (t : ℝ)).2.1)
    refine hUinj (γ (t : ℝ)) ht1 (hγ _ htS) (f ((γ (t : ℝ)).2.1)) ht2
      ((hfSect.2.2.1 ((γ (t : ℝ)).2.1) hbalt).1) ?_
    rw [(hfSect.2.2.1 ((γ (t : ℝ)).2.1) hbalt).2]
  haveI : PreconnectedSpace ↥(Set.Ici σ) := Subtype.preconnectedSpace (isPreconnected_Ici)
  obtain ⟨sstar, hsstar_ge, hsstar_visit⟩ : ∃ s : ℝ, σ ≤ s ∧ (γ s).2.1 = u := by
    obtain ⟨s, hsu, hsm⟩ := (hfreq.and_eventually (eventually_ge_atTop σ)).exists
    exact ⟨s, hsm, hsu⟩
  have hsstar : γ sstar = q := key sstar (le_trans (le_max_left _ _) hsstar_ge) hsstar_visit
  have hPne : P.Nonempty := by
    refine ⟨⟨sstar, hsstar_ge⟩, ?_⟩
    show γ sstar = f ((γ sstar).2.1)
    rw [hsstar_visit, ← hqpsi1, hfSect.2.1]
    exact hsstar
  have huniv : P = Set.univ := IsClopen.eq_univ ⟨hPclosed, hPopen⟩ hPne
  have hall : ∀ s : ℝ, σ ≤ s → γ s = f ((γ s).2.1) := by
    intro s hs
    have : (⟨s, hs⟩ : ↥(Set.Ici σ)) ∈ P := by rw [huniv]; trivial
    exact this
  -- ## 7. convergence
  have hfinal : Tendsto (fun s : ℝ => f ((γ s).2.1)) atTop (𝓝 q) := by
    have h1' : Tendsto (fun s : ℝ => (γ s).2.1) atTop (𝓝 q.2.1) := by
      rw [hqpsi1]; exact h1
    have h := hfSect.continuousAt.tendsto.comp h1'
    simpa [Function.comp_def, hfSect.2.1] using h
  refine ⟨q, hqmem, ?_⟩
  refine Tendsto.congr' ?_ hfinal
  filter_upwards [eventually_ge_atTop σ] with s hs
  exact (hall s hs).symm


end
end Work.EQ
