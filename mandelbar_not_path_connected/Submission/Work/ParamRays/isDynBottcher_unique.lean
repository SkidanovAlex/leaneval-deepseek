import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Green
import Submission.Work.ParamRays.Bottcher
import Submission.Work.ParamRays.exists_pow_two_pow_eq_one
import Submission.Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The escape radius adapted to the parameter -/

/-- The escape radius `‖c‖ + 2` adapted to the parameter `c`: above it the orbit grows. -/
noncomputable def escR (c : ℂ) : ℝ := ‖c‖ + 3

theorem escR_pos (c : ℂ) : 0 < escR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  simp only [escR]; linarith

theorem lt_max_escR (c : ℂ) : max 2 ‖c‖ < escR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [escR]
  exact max_lt (by linarith) (by linarith)

theorem one_le_escR (c : ℂ) : 1 ≤ escR c := by
  have h : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  simp only [escR]; linarith

theorem escR_le_sq_sub (c : ℂ) : escR c ≤ escR c ^ 2 - ‖c‖ := by
  have key : escR c ^ 2 - ‖c‖ - escR c = ‖c‖ ^ 2 + 4 * ‖c‖ + 6 := by
    rw [escR]; ring
  have hnn : (0 : ℝ) ≤ ‖c‖ ^ 2 + 4 * ‖c‖ + 6 := by positivity
  linarith

theorem lt_norm_Tantibar_of_lt_escR {c w : ℂ} (h : escR c < ‖w‖) :
    escR c < ‖Tantibar c w‖ := by
  have h1 : escR c ≤ escR c ^ 2 - ‖c‖ := escR_le_sq_sub c
  have h2 : escR c ^ 2 - ‖c‖ < ‖w‖ ^ 2 - ‖c‖ := by
    have h3 : escR c ^ 2 < ‖w‖ ^ 2 := by
      have hp : 0 < escR c := escR_pos c
      nlinarith
    linarith
  have h4 := norm_sq_sub_le_norm_Tantibar c w
  linarith

theorem escSet_subset_succ (c : ℂ) (n : ℕ) :
    {z : ℂ | escR c < ‖orbit c z n‖} ⊆ {z : ℂ | escR c < ‖orbit c z (n + 1)‖} := by
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [orbit_succ]
  exact lt_norm_Tantibar_of_lt_escR hz

theorem Escaping.of_shift {c z : ℂ} {n : ℕ} (h : Escaping c (orbit c z n)) : Escaping c z := by
  simp only [Escaping] at h ⊢
  refine (Filter.tendsto_add_atTop_iff_nat (f := fun m => ‖orbit c z m‖) n).mp ?_
  have h2 : (fun m : ℕ => ‖orbit c z (m + n)‖) =
      fun m : ℕ => ‖orbit c (orbit c z n) m‖ := by
    funext m
    rw [Nat.add_comm m n, orbit_add]
  rw [h2]
  exact h

/-! ## The escaping set is preconnected -/

theorem differentiable_orbit_two_mul (c : ℂ) (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => orbit c z (2 * n)) := by
  have hT2 : Differentiable ℂ (fun y : ℂ => Tantibar c (Tantibar c y)) := by
    have he : (fun y : ℂ => Tantibar c (Tantibar c y)) = fun y : ℂ => (y ^ 2 + conj c) ^ 2 + c := by
      funext y
      simp only [Tantibar, map_add, map_pow, Complex.conj_conj]
    rw [he]
    fun_prop
  induction n with
  | zero => simpa using differentiable_id
  | succ n ih =>
    have h : (fun z : ℂ => orbit c z (2 * (n + 1))) =
        (fun y : ℂ => Tantibar c (Tantibar c y)) ∘ (fun z : ℂ => orbit c z (2 * n)) := by
      funext z
      simp only [Function.comp_apply]
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, orbit_succ, orbit_succ]
    rw [h]
    exact hT2.comp ih

theorem tendsto_norm_orbit_two_mul (c : ℂ) (n : ℕ) :
    Tendsto (fun z : ℂ => ‖orbit c z (2 * n)‖) (cocompact ℂ) atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  have hmem : {z : ℂ | b ≤ ‖orbit c z (2 * n)‖} ∈ cocompact ℂ := by
    rw [Filter.mem_cocompact]
    refine ⟨Metric.closedBall 0 (max b (max 2 ‖c‖)), isCompact_closedBall _ _, ?_⟩
    intro z hz
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    have hzc : max 2 ‖c‖ < ‖z‖ := lt_of_le_of_lt (le_max_right b (max 2 ‖c‖)) hz
    have hb : b < ‖z‖ := lt_of_le_of_lt (le_max_left b (max 2 ‖c‖)) hz
    have hge := norm_orbit_ge_add c z hzc (2 * n)
    have hnn : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) * (‖z‖ * (‖z‖ - 2)) := by
      have h2 : (0 : ℝ) ≤ ‖z‖ - 2 := by
        have := hzc; have := le_max_left (2 : ℝ) ‖c‖; linarith
      positivity
    have hle : ‖z‖ ≤ ‖orbit c z (2 * n)‖ := by linarith
    exact le_of_lt (lt_of_lt_of_le hb hle)
  exact hmem

/-- A convenient point of every approximating escape set. -/
noncomputable def e0 (c : ℂ) : ℂ := ((escR c + 1 : ℝ) : ℂ)

theorem norm_e0 (c : ℂ) : ‖e0 c‖ = escR c + 1 := by
  rw [e0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have := escR_pos c; linarith

theorem e0_mem (c : ℂ) : e0 c ∈ escapingSet c := by
  rw [mem_escapingSet]
  refine escaping_of_lt_norm c _ ?_
  rw [norm_e0]
  exact lt_of_lt_of_le (lt_max_escR c) (by linarith)

theorem escaping_iff_exists_escR (c z : ℂ) :
    Escaping c z ↔ ∃ n : ℕ, escR c < ‖orbit c z (2 * n)‖ := by
  constructor
  · intro hz
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Escaping.eventually_gt hz (escR c))
    exact ⟨N, hN (2 * N) (by omega)⟩
  · rintro ⟨n, hn⟩
    exact Escaping.of_shift (escaping_of_lt_norm c (orbit c z (2 * n))
      (lt_of_le_of_lt (le_of_lt (lt_max_escR c)) hn))

theorem isPreconnected_escapingSet (c : ℂ) : IsPreconnected (escapingSet c) := by
  have hEq : escapingSet c = ⋃ n : ℕ, {z : ℂ | escR c < ‖orbit c z (2 * n)‖} := by
    ext z
    rw [mem_escapingSet, escaping_iff_exists_escR]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  rw [hEq]
  refine isPreconnected_iUnion ?_ ?_
  · refine ⟨e0 c, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro n
    have hzc : max 2 ‖c‖ < ‖e0 c‖ := by
      rw [norm_e0]; exact lt_of_lt_of_le (lt_max_escR c) (by linarith)
    have hge := norm_orbit_ge_add c (e0 c) hzc (2 * n)
    rw [norm_e0] at hge
    have h2 : (0 : ℝ) ≤ escR c + 1 - 2 := by have := one_le_escR c; linarith
    have hnn : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) * ((escR c + 1) * (escR c + 1 - 2)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith [escR_pos c]) h2)
    linarith
  · intro n
    exact Work.ParamRays.isPreconnected_lt_norm_of_differentiable
      (differentiable_orbit_two_mul c n) (tendsto_norm_orbit_two_mul c n) (escR_pos c).le

/-! ## The ratio `φ / ψ` -/

theorem IsDynBottcher.ne_zero {c : ℂ} {ψ : ℂ → ℂ} (hψ : IsDynBottcher c ψ) {z : ℂ}
    (hz : Escaping c z) : ψ z ≠ 0 := by
  intro hz0
  have hzero : ∀ n : ℕ, ψ (orbit c z n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hz0
    | succ n ih =>
      rw [orbit_succ, hψ.2.1 (orbit c z n) (hz.iterate n), ih]
      simp
  have hcoc : Tendsto (fun n : ℕ => orbit c z n) atTop (cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by
      show Tendsto (fun n : ℕ => dist (orbit c z n) 0) atTop atTop
      rw [show (fun n : ℕ => dist (orbit c z n) 0) = fun n : ℕ => ‖orbit c z n‖ from by
        funext n; rw [dist_zero_right]]
      exact hz)
  have h2 : ∀ᶠ w : ℂ in cocompact ℂ, ‖ψ w - w‖ ≤ (1 / 2) * ‖w‖ := hψ.2.2 (1 / 2) (by norm_num)
  have h3 : ∀ᶠ n : ℕ in atTop, ‖ψ (orbit c z n) - orbit c z n‖ ≤ (1 / 2) * ‖orbit c z n‖ :=
    hcoc.eventually h2
  have h4 : ∀ᶠ n : ℕ in atTop, 0 < ‖orbit c z n‖ := Escaping.eventually_gt hz 0
  obtain ⟨n, hn1, hn2⟩ := (h3.and h4).exists
  have hineq : ‖orbit c z n‖ ≤ ‖ψ (orbit c z n)‖ + (1 / 2) * ‖orbit c z n‖ := by
    have hsum : ψ (orbit c z n) + (orbit c z n - ψ (orbit c z n)) = orbit c z n := by ring
    calc ‖orbit c z n‖ = ‖ψ (orbit c z n) + (orbit c z n - ψ (orbit c z n))‖ := by rw [hsum]
      _ ≤ ‖ψ (orbit c z n)‖ + ‖orbit c z n - ψ (orbit c z n)‖ := norm_add_le _ _
      _ = ‖ψ (orbit c z n)‖ + ‖ψ (orbit c z n) - orbit c z n‖ := by rw [norm_sub_rev]
      _ ≤ ‖ψ (orbit c z n)‖ + (1 / 2) * ‖orbit c z n‖ := by linarith
  have hpos : 0 < ‖ψ (orbit c z n)‖ := by linarith
  rw [hzero n] at hpos
  simp at hpos

theorem uq_T {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsDynBottcher c φ) (hψ : IsDynBottcher c ψ)
    {z : ℂ} (hz : Escaping c z) :
    φ (Tantibar c z) / ψ (Tantibar c z) = conj (φ z / ψ z) ^ 2 := by
  rw [hφ.2.1 z hz, hψ.2.1 z hz, map_div₀, div_pow]

theorem conj_uq_orbit_succ {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsDynBottcher c φ) (hψ : IsDynBottcher c ψ)
    {z : ℂ} (hz : Escaping c z) (k : ℕ) :
    conj (φ (orbit c z (k + 1)) / ψ (orbit c z (k + 1))) =
      (φ (orbit c z k) / ψ (orbit c z k)) ^ 2 := by
  have h1 : φ (orbit c z (k + 1)) / ψ (orbit c z (k + 1)) =
      conj (φ (orbit c z k) / ψ (orbit c z k)) ^ 2 := by
    rw [orbit_succ]
    exact uq_T hφ hψ (hz.iterate k)
  rw [h1, map_pow, Complex.conj_conj]

theorem uq_pow_two_or {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsDynBottcher c φ) (hψ : IsDynBottcher c ψ)
    {z : ℂ} (hz : Escaping c z) :
    ∀ k : ℕ, (φ z / ψ z) ^ (2 ^ k) = φ (orbit c z k) / ψ (orbit c z k) ∨
      (φ z / ψ z) ^ (2 ^ k) = conj (φ (orbit c z k) / ψ (orbit c z k)) := by
  intro k
  induction k with
  | zero => exact Or.inl (by simp)
  | succ k ih =>
    have hp : (φ z / ψ z) ^ (2 ^ (k + 1)) = ((φ z / ψ z) ^ (2 ^ k)) ^ 2 := by
      rw [pow_succ (2 : ℕ) k, pow_mul]
    rw [hp]
    rcases ih with h | h
    · rw [h]
      right
      rw [conj_uq_orbit_succ hφ hψ hz k]
    · rw [h]
      left
      have h2 : φ (orbit c z (k + 1)) / ψ (orbit c z (k + 1)) =
          conj (φ (orbit c z k) / ψ (orbit c z k)) ^ 2 := by
        rw [orbit_succ]
        exact uq_T hφ hψ (hz.iterate k)
      rw [h2]

theorem tendsto_uq_cocompact {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsDynBottcher c φ)
    (hψ : IsDynBottcher c ψ) :
    Tendsto (fun w : ℂ => φ w / ψ w) (cocompact ℂ) (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (ε / 8) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ 1 / 2 := min_le_right _ _
  have hδle' : δ ≤ ε / 8 := min_le_left _ _
  have hφe : ∀ᶠ w : ℂ in cocompact ℂ, ‖φ w - w‖ ≤ δ * ‖w‖ := hφ.2.2 δ hδpos
  have hψe : ∀ᶠ w : ℂ in cocompact ℂ, ‖ψ w - w‖ ≤ δ * ‖w‖ := hψ.2.2 δ hδpos
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

theorem tendsto_uq_pow_two {c : ℂ} {φ ψ : ℂ → ℂ} (hφ : IsDynBottcher c φ)
    (hψ : IsDynBottcher c ψ) {z : ℂ} (hz : Escaping c z) :
    Tendsto (fun k : ℕ => (φ z / ψ z) ^ (2 ^ k)) atTop (nhds 1) := by
  have hcoc : Tendsto (fun k : ℕ => orbit c z k) atTop (cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by
      show Tendsto (fun n : ℕ => dist (orbit c z n) 0) atTop atTop
      rw [show (fun n : ℕ => dist (orbit c z n) 0) = fun n : ℕ => ‖orbit c z n‖ from by
        funext n; rw [dist_zero_right]]
      exact hz)
  have h1 : Tendsto (fun k : ℕ => φ (orbit c z k) / ψ (orbit c z k)) atTop (nhds 1) :=
    (tendsto_uq_cocompact hφ hψ).comp hcoc
  have h2 : Tendsto (fun k : ℕ => conj (φ (orbit c z k) / ψ (orbit c z k))) atTop (nhds 1) := by
    have hcc : Tendsto (fun x : ℂ => conj x) (nhds 1) (nhds 1) := by
      simpa using (Complex.continuous_conj.tendsto (1 : ℂ))
    exact hcc.comp h1
  rw [Metric.tendsto_nhds] at h1 h2 ⊢
  intro ε hε
  filter_upwards [h1 ε hε, h2 ε hε] with k hk1 hk2
  rcases uq_pow_two_or hφ hψ hz k with h | h <;> rw [h]
  · exact hk1
  · exact hk2

/-! ## Uniqueness -/

/-- Two Böttcher coordinates of the same antipolynomial agree on the escaping set.

Proof route (reviewer's repair): `u := φ / ψ` is continuous on the escaping set,
`u (T_c z) = conj (u z) ^ 2`, and `u w → 1` as `w → ∞`.  Since `E` is connected and the relation
forces `u (T_c z) = u z ^ (-2)` in `S¹`, a continuous lift of the argument (available on a simply
connected component; use `u ≠ -1` near infinity to build the lift locally and propagate along
orbits) satisfies `θ (T_c z) + 2 θ z = 2 π k` with `k` a locally constant integer, hence `k = 0`
after letting `z → ∞`; then `θ (T_c^n z) = (-2)^n θ z` is bounded while `T_c^n z → ∞`, so
`θ z = 0`.  Note `u z ^ (4 ^ n) → 1` alone is insufficient, since `u z = -1` satisfies it. -/
theorem isDynBottcher_unique {c : ℂ} {φ ψ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hψ : Work.ParamRays.IsDynBottcher c ψ)
    {z : ℂ} (hz : Work.ParamRays.Escaping c z) : φ z = ψ z := by
  have hψne : ∀ w : ℂ, Escaping c w → ψ w ≠ 0 := fun w hw => hψ.ne_zero hw
  have hcont : ContinuousOn (fun w : ℂ => φ w / ψ w) (escapingSet c) :=
    hφ.1.div hψ.1 (fun w hw => hψne w hw)
  have hpre : IsPreconnected ((fun w : ℂ => φ w / ψ w) '' escapingSet c) :=
    (isPreconnected_escapingSet c).image _ hcont
  have hsub : (fun w : ℂ => φ w / ψ w) '' escapingSet c ⊆ {ζ : ℂ | ∃ n, ζ ^ (2 ^ n) = 1} := by
    rintro ζ ⟨w, hw, rfl⟩
    exact Work.ParamRays.exists_pow_two_pow_eq_one (tendsto_uq_pow_two hφ hψ hw)
  have hsingle : (((fun w : ℂ => φ w / ψ w) '' escapingSet c)).Subsingleton :=
    Work.ParamRays.isPreconnected_subsingleton_of_pow_two_pow_eq_one hpre hsub
  set c₀ : ℂ := φ (e0 c) / ψ (e0 c) with hc₀def
  have hval : ∀ w : ℂ, Escaping c w → φ w / ψ w = c₀ := by
    intro w hw
    exact (hsingle ⟨w, hw, rfl⟩ ⟨e0 c, e0_mem c, rfl⟩).trans hc₀def.symm
  have hc₀ : c₀ = 1 := by
    by_contra hne
    have hpos : 0 < ‖c₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hev : {w : ℂ | ‖φ w / ψ w - 1‖ < ‖c₀ - 1‖} ∈ cocompact ℂ := by
      have ht : {w : ℂ | dist (φ w / ψ w) 1 < ‖c₀ - 1‖} ∈ cocompact ℂ :=
        (Metric.tendsto_nhds.mp (tendsto_uq_cocompact hφ hψ)) _ hpos
      rwa [show {w : ℂ | dist (φ w / ψ w) 1 < ‖c₀ - 1‖} =
          {w : ℂ | ‖φ w / ψ w - 1‖ < ‖c₀ - 1‖} from by
        ext w; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, dist_eq_norm]] at ht
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK, hKs⟩ := hev
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    set M : ℝ := max R 0 with hMdef
    set w₀ : ℂ := ((max M (escR c + 2) + 1 : ℝ) : ℂ) with hw₀def
    have hw₀norm : ‖w₀‖ = max M (escR c + 2) + 1 := by
      rw [hw₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      have h1 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
      have h2 : 0 < escR c := escR_pos c
      have h3 : M ≤ max M (escR c + 2) := le_max_left _ _
      have h4 : escR c ≤ max M (escR c + 2) :=
        le_trans (by linarith) (le_max_right M (escR c + 2))
      linarith
    have hw₀K : w₀ ∉ K := by
      intro hmem
      have h1 := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right, hw₀norm] at h1
      have h2 : M ≤ max M (escR c + 2) := le_max_left _ _
      have h3 : R ≤ M := le_max_left _ _
      linarith
    have hw₀esc : Escaping c w₀ := by
      refine escaping_of_lt_norm c w₀ ?_
      rw [hw₀norm]
      have h4 : escR c ≤ max M (escR c + 2) :=
        le_trans (le_add_of_nonneg_right (by norm_num)) (le_max_right M (escR c + 2))
      exact lt_of_lt_of_le (lt_max_escR c) (by linarith)
    have hdist := hKs hw₀K
    simp only [Set.mem_setOf_eq] at hdist
    rw [hval w₀ hw₀esc] at hdist
    exact lt_irrefl _ hdist
  have hz1 : φ z / ψ z = 1 := by rw [hval z hz, hc₀]
  exact (div_eq_one_iff_eq (hψne z hz)).mp hz1

end Work.ParamRays
