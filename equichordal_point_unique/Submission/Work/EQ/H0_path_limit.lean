import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_path_limit_engine
import Submission.Work.EQ.H0_path_limit_fwd_tail
import Submission.Work.EQ.H0_path_limit_window
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.backward_puiseux
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.branchPt_ne
import Submission.Work.EQ.branchPt_germ_stabiliser
import Submission.Work.EQ.branchPt_descend
import Submission.Work.EQ.branchPt_descend_hsep
import Submission.Work.EQ.germC_graph
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germC_small_ball_maps
import Submission.Work.EQ.chain_family_defs
import Submission.Work.EQ.chain_family_of_window
import Submission.Work.EQ.windowChain_isChain
import Submission.Work.EQ.H0_path_limit_germ_curve
import Submission.Work.EQ.chart_image_mem_H0
import Submission.Work.EQ.exists_chart_of_family
import Submission.Work.EQ.puncture_germ_curve
import Submission.Work.EQ.puncture_descend
import Submission.Work.EQ.H0_path_limit_visit_case
import Submission.Work.EQ.H0_path_limit_window_adm
import Submission.Work.EQ.windowChain_continuous
import Submission.Work.EQ.windowChain_meromorphicAt
import Submission.Work.Topology.meromorphic_tendsto_of_bounded_seq

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md, DESIGN_CORE.md and PAPER_PROOFS.md (the lead's full paper proofs for the sketched Rychlik steps; follow them). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit; IsPuncturedChart now carries a scale κ). Proved UNIFORMIZATION library in this workspace (Submission.UnifMain etc.). With UnifMain imported write `open _root_.Topology`.

# H0_path_limit: paths with convergent parameters converge (4–7k; READY with the κ-fixed DefsCore)

**Requires the `DefsCore` patch.** `IsPuncturedChart` now has `ψ₁∘e = u₀ + κζᵏ`.

**Proof.** `PAPER_PROOFS.md` §4.  The route implemented here:

1. The engine (`Submission.Work.EQ.H0_path_limit_engine`): convergence of one chain coordinate,
   together with regularity (`sig2`/`sig1` ≠ 0) of the converged coordinate, forces convergence of
   the neighbouring coordinate; and the uniform forward/backward tails along a path of chains.

2. Case split on whether `ψ₁ ∘ γ` visits its limit `u` frequently (`∃ᶠ s, ψ₁(γ s) = u`).
   * **Frequent visits** (`H0_path_limit_visit_case`): the path is trapped in a single sheet of
     the étale map `ψ₁` (the local injectivity clause of `H0_structure`), hence converges in `H0`.
   * **Eventually no visit** (`H0_path_limit_puncture_case`): the window
     `j ↦ (γ s).1 (j - m₁)` is a regular backward `EqRelC`-chain of length `N = n₁ + m₁` ending at
     `c (ψ₁ (γ s))`, `c w = germC a h (λ^{n₁} w)`, so the backward-Puiseux cover
     (`H0_path_limit_window`) gives a single sign sequence `σ` and a parameter
     `t (s)^{2^N} = ψ₁ (γ s) - u` along the whole tail.  The first window entry lies on the small
     unstable germ curve (`H0_path_limit_germ_curve`), the germ stabiliser of the branch is `μ_d`
     (`branchPt_germ_stabiliser`), primitivity descends it to `β̃` with `d`-th root parametrisation
     (`branchPt_descend`, `branchPt_descend_hsep`), the explicit chain
     `windowChain a h n₁ m₁ u 1 (2^N/d) (psi2 a Yinv β̃) β̃` realises the path
     (`windowChain_isChain`), and `exists_chart_of_family` + `chart_image_mem_H0` produce the
     punctured chart of the second disjunct. -/

namespace Work.EQ

open Filter _root_.Topology Set Metric

noncomputable section

/-- **The window data of the puncture case.**  With the uniform tails fixed and `ψ₁ ∘ γ`
eventually different from its limit `u`, the backward-Puiseux cover of the window holds with one
admissible sign sequence `σ` and a continuous parameter `t`, nonvanishing and inside the branch
disc everywhere, uniformly on a tail. -/
theorem puncture_window_data {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData} {S : ℝ} {n₁ m₁ : ℕ}
    {u : ℂ} (hu : u ≠ 0) {R : ℝ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w))
      (Metric.ball u R))
    (hchain : ∀ s : ℝ, S ≤ s → IsChain a h (γ s))
    (hcont : ContinuousOn γ (Set.Ici S))
    (hfw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, n₁ ≤ n →
      (γ s).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1))
    (hbw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, m₁ ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2))
    (h1 : Tendsto (fun s : ℝ => (γ s).2.1) atTop (𝓝 u))
    (hne : ∀ᶠ s in atTop, (γ s).2.1 ≠ u) :
    ∃ (S' : ℝ) (σ : Fin (n₁ + m₁) → Bool) (t : ℝ → ℂ),
      Adm a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ ∧
      (∀ s : ℝ, 0 < ‖t s‖) ∧
      (∀ s : ℝ, ‖t s‖ < rhoFin' a
        (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R (n₁ + m₁)) ∧
      Tendsto t atTop (𝓝 0) ∧
      (∀ s : ℝ, S' ≤ s →
        t s ^ (2 ^ (n₁ + m₁)) = (γ s).2.1 - u ∧
        ∀ j : Fin (n₁ + m₁ + 1),
          (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) =
            branchPt a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ (t s) j) := by
  classical
  set cc : ℂ → ℂ × ℂ := fun w => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w) with hccdef
  have hcc : AnalyticOnNhd ℂ cc (Metric.ball u R) := by rw [hccdef]; exact hc
  have hρpos : 0 < rhoFin' a cc u R (n₁ + m₁) := rhoFin'_pos hR hcc
  have hev : ∀ᶠ s in atTop,
      ((γ s).2.1 ≠ u ∧ ‖(γ s).2.1 - u‖ < (rhoFin' a cc u R (n₁ + m₁)) ^ (2 ^ (n₁ + m₁))) := by
    refine hne.and ?_
    have hmem : Metric.ball u ((rhoFin' a cc u R (n₁ + m₁)) ^ (2 ^ (n₁ + m₁))) ∈ 𝓝 u :=
      Metric.ball_mem_nhds u (pow_pos hρpos _)
    filter_upwards [h1 hmem] with s hs
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.mp hev
  set I : Set ℝ := Set.Ici (max S S₀) with hIdef
  have hIS : ∀ s ∈ I, S ≤ s := fun s hs => le_trans (le_max_left _ _) hs
  have hI : IsPreconnected I := isPreconnected_Ici
  have hIne : I.Nonempty := ⟨max S S₀, Set.mem_Ici.mpr le_rfl⟩
  have hneI : ∀ s ∈ I, (γ s).2.1 ≠ u :=
    fun s hs => (hS₀ s (le_trans (le_max_right _ _) hs)).1
  have hclI : ∀ s ∈ I, ‖(γ s).2.1 - u‖ < (rhoFin' a cc u R (n₁ + m₁)) ^ (2 ^ (n₁ + m₁)) :=
    fun s hs => (hS₀ s (le_trans (le_max_right _ _) hs)).2
  obtain ⟨σ, hAdm, hwin⟩ :=
    H0_path_limit_window_adm (a := a) ha0 ha1 hh (γ := γ) (S := S) (n₁ := n₁) (m₁ := m₁)
      (u := u) hu (R := R) hR hcc hchain hcont hfw hbw I hIS hI hIne hneI hclI
  obtain ⟨t₀, ht₀a, ht₀b⟩ : ∃ t₀ : ℂ, 0 < ‖t₀‖ ∧ ‖t₀‖ < rhoFin' a cc u R (n₁ + m₁) := by
    obtain ⟨t₁, -, ht₁a, ht₁b, -⟩ := hwin (max S S₀) (Set.mem_Ici.mpr le_rfl)
    exact ⟨t₁, ht₁a, ht₁b⟩
  let t : ℝ → ℂ := fun s => if h : s ∈ I then Classical.choose (hwin s h) else t₀
  have htmem : ∀ s (hs : s ∈ I), t s = Classical.choose (hwin s hs) := by
    intro s hs
    simp only [t, dif_pos hs]
  have htprop : ∀ s (hs : s ∈ I),
      t s ^ (2 ^ (n₁ + m₁)) = (γ s).2.1 - u ∧ 0 < ‖t s‖ ∧
      ‖t s‖ < rhoFin' a cc u R (n₁ + m₁) ∧
      ∀ j : Fin (n₁ + m₁ + 1),
        (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) = branchPt a cc u R σ (t s) j := by
    intro s hs
    rw [htmem s hs]
    exact Classical.choose_spec (hwin s hs)
  refine ⟨max S S₀, σ, t, hAdm, ?_, ?_, ?_, ?_⟩
  · intro s
    by_cases h : s ∈ I
    · exact ((htprop s h)).2.1
    · simp only [t, dif_neg h]
      exact ht₀a
  · intro s
    by_cases h : s ∈ I
    · exact ((htprop s h)).2.2.1
    · simp only [t, dif_neg h]
      exact ht₀b
  · refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (eventually_ge_atTop (max S S₀))
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
      ((h1.sub_const u).norm.eventually (eventually_lt_nhds
        (show ‖u - u‖ < ε ^ (2 ^ (n₁ + m₁)) by
          rw [sub_self, norm_zero]
          positivity)))
    refine ⟨max N₁ N₂, fun s hs => ?_⟩
    have hsI : s ∈ I := hN₁ s (le_trans (le_max_left _ _) hs)
    have hlt : ‖(γ s).2.1 - u‖ < ε ^ (2 ^ (n₁ + m₁)) :=
      hN₂ s (le_trans (le_max_right _ _) hs)
    have heq : ‖t s‖ ^ (2 ^ (n₁ + m₁)) = ‖(γ s).2.1 - u‖ := by
      rw [← norm_pow, (htprop s hsI).1]
    rw [dist_zero_right]
    by_contra hcon
    push_neg at hcon
    have hle : ε ^ (2 ^ (n₁ + m₁)) ≤ ‖t s‖ ^ (2 ^ (n₁ + m₁)) := pow_le_pow_left₀ hε.le hcon _
    rw [heq] at hle
    linarith
  · intro s hs
    have hsI : s ∈ I := hs
    exact ⟨(htprop s hsI).1, fun j => (htprop s hsI).2.2.2 j⟩

/-- **Separation of the window chain family.**  The rotational collisions of the chain family
`windowChain` are exactly those of its window, so the separation of `β` transfers to `E`. -/
theorem windowChain_hsep {a : ℝ} {h : ℂ → ℂ} {n₁ m₁ : ℕ} {u κ : ℂ} {k : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) {Yinv : ℂ → ℂ} {β : ℂ → Fin (n₁ + m₁ + 1) → ℂ × ℂ} {κ' : ℂ}
    (hsepβ : ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
        ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → β (ω * t) ≠ β t) :
    ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ →
        windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β (ω * t) ≠
          windowChain a h n₁ m₁ u κ k (psi2 a Yinv β) β t := by
  intro ω hω hω1
  obtain ⟨δ, hδ0, hδρ, hδ⟩ := hsepβ ω hω hω1
  refine ⟨δ, hδ0, hδρ, fun t ht0 htδ hcontra => ?_⟩
  refine hδ t ht0 htδ (funext fun j => ?_)
  have hj : -((m₁ : ℤ)) ≤ ((j : ℕ) : ℤ) - (m₁ : ℤ) ∧
      ((j : ℕ) : ℤ) - (m₁ : ℤ) ≤ ((n₁ : ℕ) : ℤ) := by
    have := j.isLt
    omega
  have hA := windowChain_fst_of_window (a := a) (h := h) (n₁ := n₁) (m₁ := m₁) (u := u)
    (κ := κ) (k := k) (ψ₂ := psi2 a Yinv β) (β := β) (j := ((j : ℕ) : ℤ) - (m₁ : ℤ)) (ω * t) hj
  have hB := windowChain_fst_of_window (a := a) (h := h) (n₁ := n₁) (m₁ := m₁) (u := u)
    (κ := κ) (k := k) (ψ₂ := psi2 a Yinv β) (β := β) (j := ((j : ℕ) : ℤ) - (m₁ : ℤ)) t hj
  have hw : windowIdx n₁ m₁ (((j : ℕ) : ℤ) - (m₁ : ℤ)) hj = j := windowIdx_sub_m₁ n₁ m₁ j
  have hc := congrArg (fun x : ChainData => x.1 (((j : ℕ) : ℤ) - (m₁ : ℤ))) hcontra
  rw [hA, hB, hw] at hc
  exact hc

/-- **The second coordinate of the stable germ curve contracts near the origin.**  Its derivative
at `0` is `(1 - a) / 2` of modulus at most `1 / 2`, so it is a strict contraction with factor
`3 / 4` on a small ball. -/
theorem germC_snd_contract {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w‖ < δ → ‖(germC a h w).2‖ ≤ (3 / 4) * ‖w‖ := by
  obtain ⟨ρ, hρ, hAn, hgerm0, -, -, hderivY⟩ := germC_facts ha0 ha1 hh
  have hYan : AnalyticAt ℂ (fun u : ℂ => (germC a h u).2) 0 := by
    have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρ
    have hproj : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (germC a h 0) :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
    simpa [Function.comp_def] using hproj.comp (hAn 0 hmem)
  have hY0 : (fun u : ℂ => (germC a h u).2) 0 = 0 := by
    show (germC a h 0).2 = 0
    rw [hgerm0]
  have hc_lt : ‖deriv (fun u : ℂ => (germC a h u).2) 0‖ < (3 / 4 : ℝ) := by
    rw [hderivY]
    have hc0 : (0 : ℝ) ≤ (1 - a) / 2 := by linarith
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hc0]
    linarith
  obtain ⟨δ, hδ, hbd⟩ := analytic_lipschitz_add hYan hY0
    (ε := 3 / 4 - ‖deriv (fun u : ℂ => (germC a h u).2) 0‖) (by linarith)
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hbdd := hbd w hw
  have heq : ‖deriv (fun u : ℂ => (germC a h u).2) 0‖ +
      (3 / 4 - ‖deriv (fun u : ℂ => (germC a h u).2) 0‖) = 3 / 4 := by ring
  rwa [heq] at hbdd

/-- Index arithmetic for the window: the `Fin`-index of the entry at `ℤ`-index `j` sits again at
`ℤ`-index `j` after the shift by `m₁`. -/
theorem windowIdx_val_int {n₁ m₁ : ℕ} {j : ℤ}
    (hj : -((m₁ : ℤ)) ≤ j ∧ j ≤ ((n₁ : ℕ) : ℤ)) :
    (((windowIdx n₁ m₁ j hj : ℕ) : ℤ) - (m₁ : ℤ)) = j := by
  have h1 : 0 ≤ j + (m₁ : ℤ) := by omega
  have h2 : ((windowIdx n₁ m₁ j hj).val : ℤ) = j + (m₁ : ℤ) := by
    rw [windowIdx_val, Int.toNat_of_nonneg h1]
  show (((windowIdx n₁ m₁ j hj).val : ℤ)) - (m₁ : ℤ) = j
  omega

/-- **The puncture case of `H0_path_limit`.** -/
theorem H0_path_limit_puncture_case {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData} {S : ℝ} {n₁ m₁ : ℕ}
    (hγ : ∀ s : ℝ, S ≤ s → γ s ∈ H0 a h)
    (hcont : ContinuousOn γ (Set.Ici S))
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : Tendsto (fun s : ℝ => (γ s).2.1) atTop (𝓝 u))
    (h2 : Tendsto (fun s : ℝ => (γ s).2.2) atTop (𝓝 v))
    (hchain : ∀ s : ℝ, S ≤ s → IsChain a h (γ s))
    (hn₁ : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, n₁ ≤ n →
      (γ s).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1))
    (hm₁ : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, m₁ ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2))
    (hne : ∀ᶠ s in atTop, (γ s).2.1 ≠ u) :
    ∃ (e : ℂ → ChainData) (k : ℕ), IsPuncturedChart a h e u k ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ᶠ s in atTop, γ s ∈ e '' (Metric.ball (0 : ℂ) ρ \ {0}) := by
  classical
  -- ## the germ data
  obtain ⟨ρg, hρg, hAn, hgerm0, hregC, hinjY, hderivY⟩ := germC_facts ha0 ha1 hh
  obtain ⟨ρY0, hρY0pos, hstrict0, hregY0, hinjY0⟩ := germC_small_ball_maps ha0 ha1 hh
  obtain ⟨ρgr, hρgr, φ, Yinv, hφan, hYan0, hY1_0, hY2_0, hY3_0⟩ := germC_graph ha0 ha1 hh
  obtain ⟨δc, hδc, hcontract⟩ := germC_snd_contract ha0 ha1 hh
  have hlamp : 0 < eqLam a := win_eqLam_pos ha0 ha1
  have hlamlt : eqLam a < 1 := win_eqLam_lt_one ha0 ha1
  have hlampC : ((eqLam a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlamp)
  have hnormlam : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := win_norm_eqLamC ha0 ha1
  -- ## the working radius
  set ρY : ℝ := min (min ρY0 ρgr) (min (min ρg (δc / 2)) 1) with hρYdef
  have hρYpos : 0 < ρY := by
    rw [hρYdef]
    exact lt_min (lt_min hρY0pos hρgr) (lt_min (lt_min hρg (by linarith)) (by norm_num))
  have hρYle0 : ρY ≤ ρY0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρYlegr : ρY ≤ ρgr := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρYleg : ρY ≤ ρg := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρYledc : ρY ≤ δc / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρYle1 : ρY ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- ## the germ data restricted to `ρY`
  have hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY) :=
    hYan0.mono (Metric.ball_subset_ball hρYlegr)
  have hY1 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (germC a h (Yinv y)).2 = y :=
    fun y hy => hY1_0 y (Metric.ball_subset_ball hρYlegr hy)
  have hY2 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (germC a h (Yinv y)).1 = φ y :=
    fun y hy => hY2_0 y (Metric.ball_subset_ball hρYlegr hy)
  have hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w :=
    fun w hw => hY3_0 w (Metric.ball_subset_ball hρYlegr hw)
  have hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(germC a h w).2‖ < ρY := by
    intro w hw
    have h1 : ‖(germC a h w).2‖ ≤ (3 / 4) * ‖w‖ := hcontract w (by linarith)
    nlinarith [h1, hw, hρYpos]
  have hYim : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → (germC a h w).2 ∈ Metric.ball (0 : ℂ) ρY := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    refine hstrict w ?_
    have := Metric.mem_ball.mp hw
    rw [dist_zero_right] at this
    exact le_of_lt this
  have hinjYρ : Set.InjOn (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρY) :=
    hinjY.mono (Metric.ball_subset_ball hρYleg)
  -- ## the enlarged tail indices
  have htendu : Tendsto (fun n : ℕ => (eqLam a) ^ n * ‖u‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlamp.le hlamlt).mul_const ‖u‖
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (htendu.eventually (eventually_lt_nhds (show (0 : ℝ) < ρg / 4 by linarith)))
  have htendv : Tendsto (fun n : ℕ => (eqLam a) ^ n * ‖v‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlamp.le hlamlt).mul_const ‖v‖
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp
    (htendv.eventually (eventually_lt_nhds (show (0 : ℝ) < ρY / 8 by linarith)))
  set n₁' : ℕ := max n₁ N₀ with hn₁'def
  set m₁' : ℕ := max m₁ M₀ with hm₁'def
  have hn₁le : n₁ ≤ n₁' := le_max_left _ _
  have hN₀le : N₀ ≤ n₁' := le_max_right _ _
  have hm₁le : m₁ ≤ m₁' := le_max_left _ _
  have hM₀le : M₀ ≤ m₁' := le_max_right _ _
  have hn₁' : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, n₁' ≤ n →
      (γ s).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1) :=
    fun s hs n hn => hn₁ s hs n (le_trans hn₁le hn)
  have hm₁' : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, m₁' ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2) :=
    fun s hs n hn => hm₁ s hs n (le_trans hm₁le hn)
  have hu_small : ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u‖ < ρg / 4 := by
    have h1 : ‖((eqLam a : ℝ) : ℂ) ^ n₁'‖ ≤ (eqLam a) ^ N₀ := by
      rw [norm_pow, hnormlam]
      exact pow_le_pow_of_le_one hlamp.le hlamlt.le hN₀le
    calc ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u‖ = ‖((eqLam a : ℝ) : ℂ) ^ n₁'‖ * ‖u‖ := norm_mul _ _
      _ ≤ (eqLam a) ^ N₀ * ‖u‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg u)
      _ < ρg / 4 := hN₀ N₀ le_rfl
  have hv_small : ‖((eqLam a : ℝ) : ℂ) ^ m₁' * v‖ ≤ ρY / 4 := by
    have h1 : ‖((eqLam a : ℝ) : ℂ) ^ m₁'‖ ≤ (eqLam a) ^ M₀ := by
      rw [norm_pow, hnormlam]
      exact pow_le_pow_of_le_one hlamp.le hlamlt.le hM₀le
    calc ‖((eqLam a : ℝ) : ℂ) ^ m₁' * v‖ = ‖((eqLam a : ℝ) : ℂ) ^ m₁'‖ * ‖v‖ := norm_mul _ _
      _ ≤ (eqLam a) ^ M₀ * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
      _ ≤ ρY / 8 := le_of_lt (hM₀ M₀ le_rfl)
      _ ≤ ρY / 4 := by linarith
  -- ## the end map is analytic near `u`
  set c : ℂ → ℂ × ℂ := fun w => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁' * w) with hcdef
  have hltu : ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u‖ < ρg := by linarith
  obtain ⟨R, hRpos, hcR0⟩ :=
    exists_analyticOnNhd_germC_end (a := a) ha0 ha1 hh (n₁ := n₁') (u := u) (ρg := ρg)
      hρg hAn hltu
  have hcR : AnalyticOnNhd ℂ c (Metric.ball u R) := hcR0
  -- ## the window data
  obtain ⟨S', σ, t, hAdm, ht0, htρ, htend_par, hwin⟩ :=
    puncture_window_data (a := a) ha0 ha1 hh (γ := γ) (S := S) (n₁ := n₁') (m₁ := m₁')
      (u := u) hu (R := R) hRpos hcR hchain hcont hn₁' hm₁' h1 hne
  -- ## the germ-curve constraint on the branch
  set S₂ : ℝ := max S S' with hS₂
  have hbw₂ : ∀ s : ℝ, S₂ ≤ s → ∀ n : ℕ, m₁' ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2) :=
    fun s hs n hn => hm₁' s (le_trans (le_max_left _ _) hs) n hn
  have hwin₂ : ∀ s : ℝ, S₂ ≤ s → ∀ j : Fin (n₁' + m₁' + 1),
      (γ s).1 ((((j : ℕ) : ℤ) - (m₁' : ℤ))) =
        branchPt a c u R σ (t s) j :=
    fun s hs j => (hwin s (le_trans (le_max_right _ _) hs)).2 j
  obtain ⟨ρ', hρ'pos, hρ'le, hcurve⟩ :=
    puncture_germ_curve (a := a) ha0 ha1 hh (γ := γ) (S := S₂) (n₁ := n₁') (m₁ := m₁')
      (u := u) (R := R) hRpos hcR hbw₂ hAdm hρYpos hYan hY1 hY2 hY3 hstrict ht0 htρ htend_par
      hwin₂ hv h2 hv_small
  -- ## the primitive descent
  have hinj_c : ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (fun w : ℂ => (c w).2) (Metric.ball u δ) := by
    have hpre : ((fun z : ℂ => ((eqLam a : ℝ) : ℂ) ^ n₁' * z) ⁻¹' Metric.ball (0 : ℂ) ρg) ∈ 𝓝 u :=
      (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (by
          have hlt : ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u‖ < ρg := lt_trans hu_small (by linarith)
          simpa [Metric.mem_ball, dist_eq_norm] using hlt))
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨δ, hδpos, fun w hw w' hw' heq => ?_⟩
    have h1 : ((eqLam a : ℝ) : ℂ) ^ n₁' * w ∈ Metric.ball (0 : ℂ) ρg := hδsub hw
    have h2 : ((eqLam a : ℝ) : ℂ) ^ n₁' * w' ∈ Metric.ball (0 : ℂ) ρg := hδsub hw'
    have h3 := hinjY h1 h2 (by simpa [hcdef] using heq)
    exact mul_left_cancel₀ (pow_ne_zero _ hlampC) h3
  obtain ⟨d, hd, hdvd, ω, hω, hprim, β, hβan, hβmer, hβdesc, hβreg, hβend, hβsep, hβcurve⟩ :=
    puncture_descend (a := a) ha0 ha1 hh (n₁ := n₁') (m₁ := m₁') (u := u) (R := R) hRpos hcR
      hinj_c hAdm hρ'pos hρ'le hcurve
  -- ##########################################################################
  -- ## The punctured chart: exponent, radius, explicit family and assembly
  -- ##########################################################################
  set k : ℕ := 2 ^ (n₁' + m₁') / d with hkdef
  have hkpos : 0 < k := by
    rw [hkdef]
    exact Nat.div_pos (Nat.le_of_dvd (by positivity) hdvd) hd
  have hdkmul : d * k = 2 ^ (n₁' + m₁') := by
    rw [hkdef]
    exact Nat.mul_div_cancel' hdvd
  have hρFpos : 0 < rhoFin' a c u R (n₁' + m₁') := rhoFin'_pos hRpos hcR
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set ρE : ℝ := min (min ((rhoFin' a c u R (n₁' + m₁')) ^ d) (ρ' ^ d))
      (min (min 1 (‖u‖ / 2)) (ρg / 4)) with hρEdef
  have hρEpos : 0 < ρE := by
    rw [hρEdef]
    exact lt_min (lt_min (pow_pos hρFpos d) (pow_pos hρ'pos d))
      (lt_min (lt_min one_pos (by linarith)) (by linarith))
  have hρEle_rhoF : ρE ≤ (rhoFin' a c u R (n₁' + m₁')) ^ d :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hρEle_rho' : ρE ≤ ρ' ^ d := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρEle_1 : ρE ≤ 1 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρEle_u : ρE ≤ ‖u‖ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρEle_g : ρE ≤ ρg / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- ## the explicit chain family of the descended branch
  set E : ℂ → ChainData := windowChain a h n₁' m₁' u 1 k (psi2 a Yinv β) β with hEdef
  have hgerm_reg : ∀ v : ℂ, v ∈ Metric.ball (0 : ℂ) ρg →
      RegPair a (germC a h v) (germC a h (((eqLam a : ℝ) : ℂ) * v)) :=
    fun v hv => (hregC v hv).1
  have hlamle : ‖((eqLam a : ℝ) : ℂ) ^ n₁'‖ ≤ 1 := by
    rw [norm_pow, hnormlam]
    exact pow_le_one₀ (le_of_lt hlamp) (le_of_lt hlamlt)
  have hsmall : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρE →
      ‖((eqLam a : ℝ) : ℂ) ^ n₁' * (u + 1 * t ^ k)‖ < ρg := by
    intro t ht0 htρ
    have htle1 : ‖t‖ ≤ 1 := le_of_lt (lt_of_lt_of_le htρ hρEle_1)
    have htk : ‖t ^ k‖ ≤ ‖t‖ := by
      rw [norm_pow]
      simpa using pow_le_pow_of_le_one (norm_nonneg t) htle1 (show 1 ≤ k from hkpos)
    have hb : ‖((eqLam a : ℝ) : ℂ) ^ n₁' * (u + 1 * t ^ k)‖ ≤ ρg / 4 + ‖t‖ := by
      calc ‖((eqLam a : ℝ) : ℂ) ^ n₁' * (u + 1 * t ^ k)‖
          = ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u
              + ((eqLam a : ℝ) : ℂ) ^ n₁' * (1 * t ^ k)‖ := by ring_nf
        _ ≤ ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u‖
              + ‖((eqLam a : ℝ) : ℂ) ^ n₁' * (1 * t ^ k)‖ := norm_add_le _ _
        _ = ‖((eqLam a : ℝ) : ℂ) ^ n₁' * u‖
              + ‖((eqLam a : ℝ) : ℂ) ^ n₁'‖ * ‖1 * t ^ k‖ := by simp only [norm_mul]
        _ ≤ ρg / 4 + ‖t‖ := by
            have hthis : ‖((eqLam a : ℝ) : ℂ) ^ n₁'‖ * ‖1 * t ^ k‖ ≤ ‖t‖ := by
              rw [one_mul]
              calc ‖((eqLam a : ℝ) : ℂ) ^ n₁'‖ * ‖t ^ k‖ ≤ 1 * ‖t‖ :=
                    mul_le_mul hlamle htk (norm_nonneg _) (by norm_num)
                _ = ‖t‖ := one_mul _
            linarith [hu_small, hthis]
    linarith [hb, htρ, hρEle_g, hρg]
  have hψne : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρE → u + 1 * t ^ k ≠ 0 := by
    intro t ht0 htρ hzero
    have htle1 : ‖t‖ ≤ 1 := le_of_lt (lt_of_lt_of_le htρ hρEle_1)
    have htk : ‖t ^ k‖ ≤ ‖t‖ := by
      rw [norm_pow]
      simpa using pow_le_pow_of_le_one (norm_nonneg t) htle1 (show 1 ≤ k from hkpos)
    have hu_eq : u = -(1 * t ^ k) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero
    have hle : ‖u‖ ≤ ‖t‖ := by
      rw [hu_eq, norm_neg, one_mul]
      exact htk
    linarith [htρ, hρEle_u]
  have hβanE : ∀ j : Fin (n₁' + m₁' + 1), AnalyticOnNhd ℂ (fun t => β t j)
      (Metric.ball (0 : ℂ) ρE \ {0}) :=
    fun j => (hβan j).mono (fun t ht => ⟨Metric.ball_subset_ball hρEle_rhoF ht.1, ht.2⟩)
  have hβregE : ∀ t ∈ Metric.ball (0 : ℂ) ρE \ {0}, ∀ j : Fin (n₁' + m₁'),
      RegPair a (β t (Fin.castSucc j)) (β t (Fin.succ j)) := by
    intro t ht j
    have htρ : ‖t‖ < ρE := by
      have h := ht.1; rwa [Metric.mem_ball, dist_zero_right] at h
    have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht.2
    exact hβreg t ht0 (lt_of_lt_of_le htρ hρEle_rhoF) j
  have hβendE : ∀ t ∈ Metric.ball (0 : ℂ) ρE \ {0},
      β t (Fin.last (n₁' + m₁')) =
        germC a h (((eqLam a : ℝ) : ℂ) ^ n₁' * (u + 1 * t ^ k)) := by
    intro t ht
    have htρ : ‖t‖ < ρE := by
      have h := ht.1; rwa [Metric.mem_ball, dist_zero_right] at h
    have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht.2
    have h := hβend t ht0 (lt_of_lt_of_le htρ hρEle_rhoF)
    dsimp only at h
    rw [h, one_mul]
  have hβcurveE : ∀ t ∈ Metric.ball (0 : ℂ) ρE \ {0},
      ∃ w : ℂ, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧ ugermC a h w = β t 0 := by
    intro t ht
    have htρ : ‖t‖ < ρE := by
      have h := ht.1; rwa [Metric.mem_ball, dist_zero_right] at h
    have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht.2
    exact hβcurve t ht0 (lt_of_lt_of_le htρ hρEle_rho')
  have hβm : ∀ j : Fin (n₁' + m₁' + 1),
      MeromorphicAt (fun t => (β t j).1) 0 ∧ MeromorphicAt (fun t => (β t j).2) 0 := by
    intro j
    obtain ⟨n, hn⟩ := hβmer j
    constructor
    · refine ⟨n, ?_⟩
      have h1 : AnalyticAt ℂ (fun z : ℂ => ((z - 0) ^ n • β z j).1) 0 :=
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _).comp hn
      have h2 : (fun z : ℂ => ((z - 0) ^ n • β z j).1)
          = fun z : ℂ => (z - 0) ^ n • (β z j).1 := by
        funext z; exact Prod.smul_fst _ _
      rwa [h2] at h1
    · refine ⟨n, ?_⟩
      have h1 : AnalyticAt ℂ (fun z : ℂ => ((z - 0) ^ n • β z j).2) 0 :=
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _).comp hn
      have h2 : (fun z : ℂ => ((z - 0) ^ n • β z j).2)
          = fun z : ℂ => (z - 0) ^ n • (β z j).2 := by
        funext z; exact Prod.smul_snd _ _
      rwa [h2] at h1
  have hEchain_ball : ∀ t ∈ Metric.ball (0 : ℂ) ρE \ {0}, IsChain a h (E t) :=
    windowChain_isChain (a := a) (h := h) (hh := hh) (n₁ := n₁') (m₁ := m₁') (u := u)
      (κ := (1 : ℂ)) (k := k) (ρ := ρE) (ρg := ρg) (ρY := ρY) (Yinv := Yinv) (β := β)
      ha0 ha1 hu one_ne_zero hkpos hρEpos hρg hAn hgerm_reg hsmall hψne
      hρYpos hρYleg hYan hY1 hY2 hY3 hYim hβanE hβregE hβendE hβcurveE
  have hEchain_norm : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρE → IsChain a h (E t) := by
    intro t ht0 htρ
    exact hEchain_ball t ⟨by simpa [Metric.mem_ball, dist_zero_right] using htρ,
      norm_pos_iff.mp ht0⟩
  have hEψ : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρE → (E t).2.1 = u + 1 * t ^ k := by
    intro t _ _
    rw [hEdef]
    exact windowChain_snd_fst t
  have hEcont : ContinuousOn E (Metric.ball (0 : ℂ) ρE \ {0}) := by
    rw [hEdef]
    exact windowChain_continuous (a := a) (h := h) (n₁ := n₁') (m₁ := m₁') (u := u)
      (κ := (1 : ℂ)) (k := k) (ρ := ρE) (ρg := ρg) (ρY := ρY) (Yinv := Yinv) (β := β)
      ha0 ha1 hρEpos hAn hsmall hβanE hYan hY3 hYim hβcurveE hρYleg
  have hEmer : ∀ n : ℤ, MeromorphicAt (fun t => ((E t).1 n).1) 0 ∧
      MeromorphicAt (fun t => ((E t).1 n).2) 0 ∧ MeromorphicAt (fun t => (E t).2.2) 0 := by
    obtain ⟨hψ2mer, hcmer⟩ := windowChain_meromorphicAt (a := a) (h := h) (n₁ := n₁') (m₁ := m₁')
      (u := u) (κ := (1 : ℂ)) (k := k) (ρ := ρE) (ρg := ρg) (ρY := ρY) (Yinv := Yinv) (β := β)
      ha0 ha1 hρEpos hρg hρYpos hρYleg hAn hsmall hβm hβanE hYan hY3 hYim hβcurveE
    intro n
    refine ⟨?_, ?_, ?_⟩
    · rw [hEdef]; exact (hcmer n).1
    · rw [hEdef]; exact (hcmer n).2
    · rw [hEdef]; show MeromorphicAt (fun t => psi2 a Yinv β t) 0; exact hψ2mer
  have hsepβ : ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρE ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → β (ω * t) ≠ β t := by
    intro ω hω hω1
    obtain ⟨δ₀, hδ₀pos, hδ₀le, hδ₀⟩ := hβsep ω hω hω1
    exact ⟨min δ₀ ρE, lt_min hδ₀pos hρEpos, min_le_right _ _, fun t ht0 ht =>
      hδ₀ t ht0 (lt_of_lt_of_le ht (min_le_left _ _))⟩
  have hEsep : ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρE ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → E (ω * t) ≠ E t := by
    rw [hEdef]
    exact windowChain_hsep (n₁ := n₁') (m₁ := m₁') (u := u) (κ := (1 : ℂ)) (k := k)
      (Yinv := Yinv) (β := β) (κ' := (1 : ℂ)) hρEpos hsepβ
  obtain ⟨τ, hτpos, hτρE, κ', hκ', e, hψe, hinj_e, hcont_e, hmer_e, hψ2mer_e, him1, him2⟩ :=
    exists_chart_of_family (u := u) (κ := (1 : ℂ)) (k := k) (ρ := ρE)
      (E := E) hu one_ne_zero hkpos hρEpos hEψ hEcont hEmer hEsep
  have him2' : ∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0},
      ∃ t : ℂ, 0 < ‖t‖ ∧ ‖t‖ < τ ∧ E t = e ζ := by
    intro ζ hζ
    exact him2 ζ (norm_pos_iff.mpr hζ.2)
      (by simpa [Metric.mem_ball, dist_zero_right] using hζ.1)
  have hH0e : ∀ ζ ∈ Metric.ball (0 : ℂ) 1 \ {0}, e ζ ∈ H0 a h :=
    chart_image_mem_H0 (a := a) (h := h) (u := u) (κ := (1 : ℂ)) (k := k) (ρ := ρE) hρEpos
      (E := E) hEchain_norm hEψ hEcont (κ' := κ') hκ' (e := e) (τ := τ) hτpos hτρE hψe him2'
      one_ne_zero hkpos hu
  refine ⟨e, k, ⟨hkpos, hu, κ', hκ', ?_, hinj_e, hcont_e, hψ2mer_e, hmer_e⟩, ?_⟩
  · intro ζ hζ
    exact ⟨hH0e ζ hζ, hψe ζ hζ⟩
  · -- ## the path eventually lies in the chart image
    intro ρ hρ
    have hκ'norm : 0 < ‖κ'‖ := norm_pos_iff.mpr hκ'
    have hlim1 : 0 < ‖κ'‖ * ρ ^ k := mul_pos hκ'norm (pow_pos hρ k)
    have hnormt_tend : Tendsto (fun s : ℝ => ‖t s‖) atTop (𝓝 0) := by
      simpa using htend_par.norm
    have hpow_tend : Tendsto (fun s : ℝ => ‖t s‖ ^ (2 ^ (n₁' + m₁'))) atTop (𝓝 0) := by
      have h := hnormt_tend.pow (2 ^ (n₁' + m₁'))
      simpa [zero_pow (pow_ne_zero (n₁' + m₁') (by norm_num : (2 : ℕ) ≠ 0))] using h
    have hpowd_tend : Tendsto (fun s : ℝ => ‖t s‖ ^ d) atTop (𝓝 0) := by
      have h := hnormt_tend.pow d
      simpa [zero_pow (Nat.ne_of_gt hd)] using h
    have hvs : ∀ᶠ s : ℝ in atTop, ‖((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2‖ < ρY := by
      have h2' : Tendsto (fun s : ℝ => ((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2) atTop
          (𝓝 (((eqLam a : ℝ) : ℂ) ^ m₁' * v)) := h2.const_mul _
      have hlt : ‖((eqLam a : ℝ) : ℂ) ^ m₁' * v‖ < ρY := lt_of_le_of_lt hv_small (by linarith)
      exact h2'.norm.eventually (eventually_lt_nhds hlt)
    filter_upwards [eventually_ge_atTop S₂, hpow_tend.eventually (eventually_lt_nhds hlim1),
      hpowd_tend.eventually (eventually_lt_nhds hτpos), hvs] with s hs₂ hspow hsτ hvw
    have hs_S : S ≤ s := le_trans (le_max_left _ _) hs₂
    have hpos_s : 0 < ‖t s‖ := ht0 s
    have hlt_s : ‖t s‖ < rhoFin' a c u R (n₁' + m₁') := htρ s
    have hβd : β ((t s) ^ d) = branchPt a c u R σ (t s) := hβdesc (t s) hpos_s hlt_s
    have hwin_s : ∀ j : Fin (n₁' + m₁' + 1),
        (γ s).1 (((j : ℕ) : ℤ) - (m₁' : ℤ)) = branchPt a c u R σ (t s) j :=
      fun j => (hwin s (le_trans (le_max_right _ _) hs₂)).2 j
    have hs'_S : S' ≤ s := le_trans (le_max_right _ _) hs₂
    have hγψ1_u : u + 1 * (((t s) ^ d) ^ k) = (γ s).2.1 := by
      have hsub : (γ s).2.1 = (t s) ^ (2 ^ (n₁' + m₁')) + u :=
        sub_eq_iff_eq_add.mp (hwin s hs'_S).1.symm
      rw [hsub, one_mul, ← pow_mul, hdkmul]
      ring
    have hw0mem : ((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2 ∈ Metric.ball (0 : ℂ) ρY := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hvw
    have hβ0 : β ((t s) ^ d) (0 : Fin (n₁' + m₁' + 1)) = (γ s).1 (-(m₁' : ℤ)) := by
      have hb : β ((t s) ^ d) (0 : Fin (n₁' + m₁' + 1))
          = branchPt a c u R σ (t s) (0 : Fin (n₁' + m₁' + 1)) := by rw [hβd]
      rw [hb, ← hwin_s (0 : Fin (n₁' + m₁' + 1))]
      congr 1
      simp
    have hγ0 : (γ s).1 (-(m₁' : ℤ)) =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2) :=
      hm₁' s hs_S m₁' le_rfl
    have hpsi2 : psi2 a Yinv β ((t s) ^ d) = (γ s).2.2 := by
      have hkey : Yinv ((β ((t s) ^ d) (0 : Fin (n₁' + m₁' + 1))).2)
          = ((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2 := by
        rw [hβ0, hγ0]
        have hmirror : (ugermC a h (((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2)).2
            = (germC a h (((eqLam a : ℝ) : ℂ) ^ m₁' * (γ s).2.2)).2 := rfl
        rw [hmirror]
        exact hY3 _ hw0mem
      show Yinv ((β ((t s) ^ d) (0 : Fin (n₁' + m₁' + 1))).2)
          / ((eqLam a : ℝ) : ℂ) ^ m₁' = (γ s).2.2
      rw [hkey, mul_div_cancel_left₀ _ (pow_ne_zero _ hlampC)]
    have hfun : (γ s).1 = (E ((t s) ^ d)).1 := by
      funext j
      rw [hEdef]
      by_cases hj : -((m₁' : ℤ)) ≤ j ∧ j ≤ ((n₁' : ℕ) : ℤ)
      · have hb : β ((t s) ^ d) (windowIdx n₁' m₁' j hj)
            = branchPt a c u R σ (t s) (windowIdx n₁' m₁' j hj) := by rw [hβd]
        rw [windowChain_fst_of_window (ψ₂ := psi2 a Yinv β) (β := β) (t := (t s) ^ d) hj, hb,
          ← hwin_s (windowIdx n₁' m₁' j hj)]
        exact congrArg (fun i => (γ s).1 i) (windowIdx_val_int hj).symm
      · by_cases hj2 : ((n₁' : ℕ) : ℤ) < j
        · have hj0 : 0 ≤ j := by omega
          have hnat : (((j.toNat : ℕ)) : ℤ) = j := Int.toNat_of_nonneg hj0
          have hnle : n₁' ≤ j.toNat := by omega
          have hγj : (γ s).1 j = germC a h (((eqLam a : ℝ) : ℂ) ^ j * (γ s).2.1) := by
            have h := hn₁' s hs_S j.toNat hnle
            rw [hnat] at h
            rw [← zpow_natCast, hnat] at h
            exact h
          rw [windowChain_fst_of_fwd (ψ₂ := psi2 a Yinv β) (β := β) (t := (t s) ^ d) hj2, hγj]
          congr 1
          rw [hγψ1_u]
        · have hj3 : j < -((m₁' : ℤ)) := by omega
          have hj0 : 0 ≤ -j := by omega
          have hnat : ((((-j).toNat : ℕ)) : ℤ) = -j := Int.toNat_of_nonneg hj0
          have hnle : m₁' ≤ (-j).toNat := by omega
          have hγj : (γ s).1 j =
              ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * (γ s).2.2) := by
            have h := hm₁' s hs_S (-j).toNat hnle
            have hcast : -((((-j).toNat : ℕ)) : ℤ) = j := by omega
            rw [hcast] at h
            rw [← zpow_natCast, hnat] at h
            exact h
          rw [windowChain_fst_of_bwd (ψ₂ := psi2 a Yinv β) (β := β) (t := (t s) ^ d) hj3, hγj]
          rw [hpsi2]
    have hγE : γ s = E ((t s) ^ d) := by
      refine Prod.ext hfun (Prod.ext ?_ ?_)
      · rw [hEdef]
        show (γ s).2.1 = u + 1 * (((t s) ^ d) ^ k)
        exact hγψ1_u.symm
      · rw [hEdef]
        show (γ s).2.2 = psi2 a Yinv β ((t s) ^ d)
        exact hpsi2.symm
    have ht0' : 0 < ‖(t s) ^ d‖ := by rw [norm_pow]; exact pow_pos hpos_s d
    have htτ : ‖(t s) ^ d‖ < τ := by rw [norm_pow]; exact hsτ
    obtain ⟨ζ, hζ0, hζ1, hζe⟩ := him1 ((t s) ^ d) ht0' htτ
    refine ⟨ζ, ⟨?_, norm_pos_iff.mp hζ0⟩, hζe.trans hγE.symm⟩
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hcon
    push_neg at hcon
    have hkey : κ' * ζ ^ k = ((t s) ^ d) ^ k := by
      have hA : (e ζ).2.1 = u + κ' * ζ ^ k :=
        hψe ζ ⟨by simpa [Metric.mem_ball, dist_zero_right] using hζ1, norm_pos_iff.mp hζ0⟩
      have hB : (e ζ).2.1 = u + 1 * (((t s) ^ d) ^ k) := by
        rw [hζe]; show (E ((t s) ^ d)).2.1 = u + 1 * (((t s) ^ d) ^ k)
        exact windowChain_snd_fst _
      have hmid : u + κ' * ζ ^ k = u + 1 * (((t s) ^ d) ^ k) := by rw [← hA, hB]
      rw [one_mul] at hmid
      exact add_left_cancel hmid
    have hnorm : ‖κ'‖ * ‖ζ‖ ^ k = ‖t s‖ ^ (d * k) := by
      calc ‖κ'‖ * ‖ζ‖ ^ k = ‖κ' * ζ ^ k‖ := by rw [norm_mul, norm_pow]
        _ = ‖((t s) ^ d) ^ k‖ := by rw [hkey]
        _ = ‖(t s) ^ (d * k)‖ := by rw [pow_mul]
        _ = ‖t s‖ ^ (d * k) := norm_pow _ _
    have h1 : ‖κ'‖ * ρ ^ k ≤ ‖t s‖ ^ (d * k) := by
      rw [← hnorm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hρ) hcon k) (norm_nonneg κ')
    rw [hdkmul] at h1
    linarith [hspow]

/-- **Paths with convergent parameters converge (Rychlik Thm 11, the step "Z has one point ⇒
γ has a limit").** A path in `H0` along which `ψ₁` and `ψ₂` converge in `ℂ*` converges in
`H0` or runs into a puncture. -/
theorem H0_path_limit {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData} (hγ : ∀ s, 0 ≤ s → γ s ∈ H0 a h)
    (hcont : ContinuousOn γ (Set.Ici 0)) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : Tendsto (fun s => (γ s).2.1) atTop (𝓝 u))
    (h2 : Tendsto (fun s => (γ s).2.2) atTop (𝓝 v)) :
    (∃ q ∈ H0 a h, Tendsto γ atTop (𝓝 q)) ∨
      ∃ (e : ℂ → ChainData) (k : ℕ), IsPuncturedChart a h e u k ∧
        ∀ ρ : ℝ, 0 < ρ → ∀ᶠ s in atTop, γ s ∈ e '' (Metric.ball (0 : ℂ) ρ \ {0}) := by
  have hchain : ∀ s : ℝ, 0 ≤ s → IsChain a h (γ s) := fun s hs => isChain_of_mem_H0 (hγ s hs)
  obtain ⟨n₁, hn₁⟩ := H0_path_limit_fwd_tail ha0 ha1 hh hchain hcont hu h1
  obtain ⟨m₁, hm₁⟩ := H0_path_limit_bwd_tail ha0 ha1 hh hchain hcont hv h2
  by_cases hfreq : ∃ᶠ s in atTop, (γ s).2.1 = u
  · exact Or.inl (H0_path_limit_visit_case ha0 ha1 hh hγ hcont hu hv h1 h2 hfreq)
  · exact Or.inr (H0_path_limit_puncture_case ha0 ha1 hh hγ hcont hu hv h1 h2 hchain hn₁ hm₁
      (not_frequently.mp hfreq))

end

end Work.EQ
