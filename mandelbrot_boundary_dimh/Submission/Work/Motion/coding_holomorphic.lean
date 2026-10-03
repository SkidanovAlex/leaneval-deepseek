import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.Coding

namespace Work.Motion

open Metric Set Filter
open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open scoped Topology

/-!
# Holomorphy of the coding map in the parameter

For a `PertData` family of inverse branches, the coding map `c ↦ D.coding c ω` is the
locally uniform limit of the holomorphic maps `c ↦ pComp (D.τc c) ω k p`.  The convergence
is in fact uniform on the whole parameter disc `ball c₀ D.ρ`, with the geometric bound
`2 s θ^{k-1}` coming from the contraction estimate `PertData.pComp_dist_le'`.  Weierstrass'
theorem (`TendstoLocallyUniformlyOn.differentiableOn`) then gives holomorphy.
-/

namespace PertData

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
variable (D : PertData c₀ N τ n p r K)
include D

lemma r₁_pos : 0 < D.r₁ := by linarith [D.r_pos, D.hr₁]

/-- Each finite composition `c ↦ pComp (D.τc c) ω k p` is holomorphic in the parameter on the
parameter disc. -/
lemma differentiableOn_pComp (ω : ℕ → Fin N) (k : ℕ) :
    DifferentiableOn ℂ (fun c => pComp (D.τc c) ω k p) (ball c₀ D.ρ) := by
  induction k generalizing ω with
  | zero =>
    exact differentiableOn_const (𝕜 := ℂ) (s := ball c₀ D.ρ) p
  | succ k ih =>
    have hmem : ∀ c ∈ ball c₀ D.ρ,
        pComp (D.τc c) (fun j => ω (j + 1)) k p ∈ ball p D.r₁ := by
      intro c hc
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [pComp_zero]; exact mem_ball_self D.r₁_pos
      · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
        exact D.closedBall_s_subset' (D.pComp_mem c hc (fun j => ω (j + 1)) l p (D.half_mem p))
    refine ((D.hol (ω 0)).comp
      (differentiableOn_id.prodMk (ih (fun j => ω (j + 1))))
      (fun c hc => ⟨hc, hmem c hc⟩)).congr (fun c hc => ?_)
    simp only [pComp_succ, Function.comp_apply, id_eq]

/-- The coding point is the uniform limit of its finite approximations, with the geometric
bound `2 s θ^{k-1}` on the whole parameter disc. -/
lemma dist_coding_pComp (ω : ℕ → Fin N) {c : ℂ} (hc : c ∈ ball c₀ D.ρ) {k : ℕ} (hk : 1 ≤ k) :
    dist (D.coding c ω) (pComp (D.τc c) ω k p) ≤ 2 * D.s * D.θ ^ (k - 1) := by
  have hlim : Tendsto (fun m => dist (pComp (D.τc c) ω m p) (pComp (D.τc c) ω k p)) atTop
      (𝓝 (dist (D.coding c ω) (pComp (D.τc c) ω k p))) :=
    (D.coding_tendsto c hc ω).dist tendsto_const_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop k] with m hm
  rw [dist_eq_norm]
  exact D.pComp_dist_le' c hc ω hm hk

/-- The finite approximations converge uniformly on the parameter disc. -/
lemma tendstoUniformlyOn_coding (ω : ℕ → Fin N) :
    TendstoUniformlyOn (fun k (c : ℂ) => pComp (D.τc c) ω k p) (fun c => D.coding c ω)
      atTop (ball c₀ D.ρ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC : 0 ≤ 2 * D.s := by linarith [D.hs0]
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · filter_upwards [eventually_ge_atTop 1] with k hk c hc
    have h1 := D.dist_coding_pComp ω hc hk
    have h2 : 2 * D.s * D.θ ^ (k - 1) = 0 := by rw [← hC0, zero_mul]
    rw [h2] at h1
    linarith
  · obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (show (0:ℝ) < ε / (2 * D.s) by positivity) D.hθ1
    filter_upwards [eventually_ge_atTop (n + 1)] with k hk c hc
    have h1 := D.dist_coding_pComp ω hc (by omega : 1 ≤ k)
    have h2 : D.θ ^ (k - 1) ≤ D.θ ^ n :=
      pow_le_pow_of_le_one D.hθ0 (le_of_lt D.hθ1) (by omega)
    have h3 : 2 * D.s * D.θ ^ (k - 1) ≤ 2 * D.s * D.θ ^ n :=
      mul_le_mul_of_nonneg_left h2 hC
    have h4 : 2 * D.s * D.θ ^ n < 2 * D.s * (ε / (2 * D.s)) :=
      mul_lt_mul_of_pos_left hn hCpos
    have h5 : 2 * D.s * (ε / (2 * D.s)) = ε := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ (ne_of_gt hCpos)
    linarith

end

end PertData

/-- **Holomorphy of the coding map in the parameter.** -/
theorem coding_holomorphic {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (D : PertData c₀ N τ n p r K) (ω : ℕ → Fin N) :
    DifferentiableOn ℂ (fun c => D.coding c ω) (ball c₀ D.ρ) := by
  exact (D.tendstoUniformlyOn_coding ω).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun k => D.differentiableOn_pComp ω k) Metric.isOpen_ball

end Work.Motion
