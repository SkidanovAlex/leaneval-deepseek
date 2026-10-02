import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.ParamRays.exists_pow_two_pow_eq_one
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open Filter
open scoped Real Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)

/-- Uniqueness of the critical Böttcher coordinate on a `T_c`-invariant preconnected piece of
the critical domain: any continuous nonvanishing solution `ψ` of the Böttcher equation
`ψ (T_c z) = conj (ψ z)²` there which is asymptotic to the identity at infinity coincides with
any critical Böttcher coordinate `φ`. -/
theorem eqOn_of_isCritBottcher_sub {c : ℂ} {φ ψ : ℂ → ℂ} {U : Set ℂ}
    (hφ : Work.ParamRays.IsCritBottcher c φ) (hU : IsPreconnected U)
    (hUc : U ⊆ Work.ParamRays.critDomain c)
    (hTU : ∀ z ∈ U, LeanEval.ComplexAnalysis.Tantibar c z ∈ U)
    (hψc : ContinuousOn ψ U) (hψ0 : ∀ z ∈ U, ψ z ≠ 0)
    (hψeq : ∀ z ∈ U, ψ (LeanEval.ComplexAnalysis.Tantibar c z) = star (ψ z) ^ 2)
    (hψas : ∀ ε > 0, ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖ψ z - z‖ ≤ ε * ‖z‖) :
    ∀ z ∈ U, φ z = ψ z := by
  -- ## The ratio `φ / ψ` tends to `1` at infinity
  have hratio : Tendsto (fun w : ℂ => φ w / ψ w) (cocompact ℂ) (nhds 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := min (ε / 8) (1 / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδle : δ ≤ 1 / 2 := min_le_right _ _
    have hδle' : δ ≤ ε / 8 := min_le_left _ _
    have hφe : ∀ᶠ w : ℂ in cocompact ℂ, ‖φ w - w‖ ≤ δ * ‖w‖ := hφ.2.2 δ hδpos
    have hψe : ∀ᶠ w : ℂ in cocompact ℂ, ‖ψ w - w‖ ≤ δ * ‖w‖ := hψas δ hδpos
    have h1e : ∀ᶠ w : ℂ in cocompact ℂ, 1 ≤ ‖w‖ := by
      have hmem : {w : ℂ | 1 ≤ ‖w‖} ∈ cocompact ℂ := by
        rw [Filter.mem_cocompact]
        refine ⟨Metric.closedBall 0 1, isCompact_closedBall _ _, ?_⟩
        intro w hw
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
        exact le_of_lt hw
      exact hmem
    filter_upwards [hφe, hψe, h1e] with w hφw hψw h1w
    have hw1 : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le zero_lt_one h1w
    have hψlb : (1 - δ) * ‖w‖ ≤ ‖ψ w‖ := by
      have h5 : ‖w‖ ≤ ‖ψ w‖ + ‖w - ψ w‖ := by
        calc ‖w‖ = ‖ψ w + (w - ψ w)‖ := by rw [show ψ w + (w - ψ w) = w by ring]
          _ ≤ ‖ψ w‖ + ‖w - ψ w‖ := norm_add_le _ _
      rw [norm_sub_rev w (ψ w)] at h5
      nlinarith
    have hψpos : 0 < ‖ψ w‖ := by
      have h3 : (1 / 2) * ‖w‖ ≤ (1 - δ) * ‖w‖ := by nlinarith
      have h4 : (0 : ℝ) < (1 / 2) * ‖w‖ := by positivity
      linarith
    have hψwne : ψ w ≠ 0 := norm_pos_iff.mp hψpos
    rw [dist_eq_norm, div_sub_one hψwne, norm_div, div_lt_iff₀ hψpos]
    have hnum : ‖φ w - ψ w‖ ≤ 2 * δ * ‖w‖ := by
      have h5 : ‖φ w - ψ w‖ ≤ ‖φ w - w‖ + ‖w - ψ w‖ := by
        calc ‖φ w - ψ w‖ = ‖(φ w - w) + (w - ψ w)‖ := by
              rw [show (φ w - w) + (w - ψ w) = φ w - ψ w by ring]
          _ ≤ ‖φ w - w‖ + ‖w - ψ w‖ := norm_add_le _ _
      rw [norm_sub_rev w (ψ w)] at h5
      linarith
    calc ‖φ w - ψ w‖ ≤ 2 * δ * ‖w‖ := hnum
      _ < ε * ((1 - δ) * ‖w‖) := by
            have h6 : 2 * δ < ε * (1 - δ) := by nlinarith
            nlinarith
      _ ≤ ε * ‖ψ w‖ := mul_le_mul_of_nonneg_left hψlb hε.le
  -- ## The orbit of a point of `U` escapes to infinity
  have hcocOf : ∀ z ∈ U, Tendsto (fun k : ℕ => Work.ParamRays.orbit c z k) atTop (cocompact ℂ) := by
    intro z hz
    have hesc : Work.ParamRays.Escaping c z :=
      Work.ParamRays.critDomain_subset_escapingSet c (hUc hz)
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop 0 ?_
    show Tendsto (fun n : ℕ => dist (Work.ParamRays.orbit c z n) 0) atTop atTop
    rw [show (fun n : ℕ => dist (Work.ParamRays.orbit c z n) 0)
        = fun n : ℕ => ‖Work.ParamRays.orbit c z n‖ from by
      funext n; rw [dist_zero_right]]
    exact hesc
  -- ## The forward orbit of a point of `U` stays in `U`
  have hUiterOf : ∀ z ∈ U, ∀ k : ℕ, Work.ParamRays.orbit c z k ∈ U := by
    intro z hz k
    induction k with
    | zero => rw [Work.ParamRays.orbit_zero]; exact hz
    | succ k ih => rw [Work.ParamRays.orbit_succ]; exact hTU _ ih
  -- ## Every value of the ratio is a root of unity of `2`-power order
  have key : ∀ z ∈ U, ∃ N : ℕ, (φ z / ψ z) ^ (2 ^ N) = 1 := by
    intro z hz
    set ρ : ℕ → ℂ := fun k => φ (Work.ParamRays.orbit c z k) / ψ (Work.ParamRays.orbit c z k)
      with hρdef
    have hstep : ∀ k, ρ (k + 1) = conj (ρ k) ^ 2 := by
      intro k
      have hk : Work.ParamRays.orbit c z k ∈ U := hUiterOf z hz k
      have h1 := hφ.2.1 (Work.ParamRays.orbit c z k) (hUc hk)
      have h2 : ψ (Tantibar c (Work.ParamRays.orbit c z k))
          = conj (ψ (Work.ParamRays.orbit c z k)) ^ 2 := by
        rw [hψeq (Work.ParamRays.orbit c z k) hk, Complex.star_def]
      simp only [hρdef]
      rw [Work.ParamRays.orbit_succ, h1, h2, map_div₀, div_pow]
    have hconjstep : ∀ k, conj (ρ (k + 1)) = (ρ k) ^ 2 := by
      intro k
      rw [hstep k, map_pow, Complex.conj_conj]
    have hpow_or : ∀ k, (ρ 0) ^ (2 ^ k) = ρ k ∨ (ρ 0) ^ (2 ^ k) = conj (ρ k) := by
      intro k
      induction k with
      | zero => exact Or.inl (by simp)
      | succ k ih =>
        have hp : (ρ 0) ^ (2 ^ (k + 1)) = ((ρ 0) ^ (2 ^ k)) ^ 2 := by
          rw [pow_succ (2 : ℕ) k, pow_mul]
        rw [hp]
        rcases ih with h | h
        · rw [h]; right; rw [hconjstep k]
        · rw [h]; left; rw [hstep k]
    have hρlim : Tendsto ρ atTop (nhds 1) := by
      rw [hρdef]
      exact hratio.comp (hcocOf z hz)
    have hpowlim : Tendsto (fun k : ℕ => (ρ 0) ^ (2 ^ k)) atTop (nhds 1) := by
      have h1 := hρlim
      have h2 : Tendsto (fun k => conj (ρ k)) atTop (nhds 1) := by
        have hcc : Tendsto (fun x : ℂ => conj x) (nhds 1) (nhds 1) := by
          simpa using (Complex.continuous_conj.tendsto (1 : ℂ))
        exact hcc.comp h1
      rw [Metric.tendsto_nhds] at h1 h2 ⊢
      intro ε hε
      filter_upwards [h1 ε hε, h2 ε hε] with k hk1 hk2
      rcases hpow_or k with h | h <;> rw [h]
      · exact hk1
      · exact hk2
    obtain ⟨N, hN⟩ := Work.ParamRays.exists_pow_two_pow_eq_one hpowlim
    exact ⟨N, by simpa only [hρdef, Work.ParamRays.orbit_zero] using hN⟩
  -- ## The image of `U` under the ratio is a subsingleton, so the ratio is constant
  have hcont : ContinuousOn (fun w : ℂ => φ w / ψ w) U :=
    (hφ.1.mono hUc).div hψc hψ0
  have hpre : IsPreconnected ((fun w : ℂ => φ w / ψ w) '' U) := hU.image _ hcont
  have hsub : (fun w : ℂ => φ w / ψ w) '' U ⊆ {ζ : ℂ | ∃ n : ℕ, ζ ^ (2 ^ n) = 1} := by
    rintro ζ ⟨w, hw, rfl⟩
    exact key w hw
  have hsingle : ((fun w : ℂ => φ w / ψ w) '' U).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre hsub
  intro z hz
  have hconst : ∀ k : ℕ,
      φ (Work.ParamRays.orbit c z k) / ψ (Work.ParamRays.orbit c z k) = φ z / ψ z := by
    intro k
    exact hsingle ⟨_, hUiterOf z hz k, rfl⟩ ⟨_, hz, rfl⟩
  have hlim : Tendsto (fun k : ℕ =>
      φ (Work.ParamRays.orbit c z k) / ψ (Work.ParamRays.orbit c z k)) atTop (nhds 1) :=
    hratio.comp (hcocOf z hz)
  have hlim' : Tendsto (fun _ : ℕ => φ z / ψ z) atTop (nhds 1) := by
    have hfun : (fun k : ℕ => φ (Work.ParamRays.orbit c z k) / ψ (Work.ParamRays.orbit c z k))
        = fun _ : ℕ => φ z / ψ z := funext fun k => hconst k
    rw [hfun] at hlim
    exact hlim
  have hz1 : φ z / ψ z = 1 := tendsto_nhds_unique tendsto_const_nhds hlim'
  exact (div_eq_one_iff_eq (hψ0 z hz)).mp hz1

end Work.NAKANE2.Surgery
