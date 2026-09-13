/-
# Equicontinuity of the family of solutions of the small-perturbation equation

This is the compactness input of Savin's Proposition 4.1.

The sequence `v k` solves `Fop (cofOp (N k)) (e k) (D²·) = 0` on `ball 0 1`, with `e k → 0` and
`N k` in the ellipticity class, and `‖v k‖ ≤ 1`.  The *value scaling* `Ψ k := e k • v k` turns it
into the unperturbed equation `s2 (N k + D²Ψ k) = 1` with `‖Ψ k‖ ≤ e k`, so the (UNIFORM-in-the-base)
Hölder estimate `holder_estimate_scaled_uniform` applies: for every centre `x₀ ∈ B_{1/2}` and every
level `s` one has

  `osc_{B_{(1/2)^{s+2}}(x₀)} (Ψ k) ≤ (1-δ)^s osc_{B_{1/2}(x₀)}(Ψ k) ≤ 2(1-δ)^s e k`

as soon as `2 e k ≤ c₁ (1/2)^{2s+2}`.  Dividing by `e k` gives the graded equicontinuity

  `∀ j, ∃ K j, ∃ h > 0, ∀ k ≥ K j, osc_{B_h}(v k) ≤ 1/(j+1)`

which is exactly the `hthr` hypothesis of `Commons.Topology.Metric.arzelaAscoli_threshold`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Stability
import Submission.Savin.HolderScale
import Submission.Savin.PropagationAbove
import Submission.Commons.Topology.Metric.arzelaAscoli_threshold

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The trace of an operator is bounded by `4` times a quadratic-form upper bound. -/
theorem trOp_le_of_quadform_le {T : ℝ⁴ →L[ℝ] ℝ⁴} {c' : ℝ}
    (h : ∀ v : ℝ⁴, ⟪T v, v⟫ ≤ c' * ‖v‖ ^ 2) : trOp T ≤ 4 * c' := by
  rw [trOp_eq_sum]
  have h1 : ∀ i : Fin 4, ⟪T (stdB4 i), stdB4 i⟫ ≤ c' := by
    intro i
    have h2 := h (stdB4 i)
    rw [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h2
    exact h2
  calc ∑ i : Fin 4, ⟪T (stdB4 i), stdB4 i⟫ ≤ ∑ _i : Fin 4, c' := Finset.sum_le_sum fun i _ => h1 i
    _ = 4 * c' := by simp

/-- **Graded equicontinuity** of the family `v k` (see the file header). -/
theorem equicontinuous_threshold
    {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {v : ℕ → ℝ⁴ → ℝ} {c c' p M : ℝ}
    (hc : 0 < c) (hc'pos : 0 < c') (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p)
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (hcq : ∀ k u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (N k) u, u⟫)
    (hcq' : ∀ k u, ⟪cofOp (N k) u, u⟫ ≤ c' * ‖u‖ ^ 2)
    (he0 : ∀ k, 0 < e k) (hetend : Tendsto e atTop (𝓝 0))
    (hv : ∀ k, ContDiffOn ℝ 2 (v k) (ball 0 2))
    (heq : ∀ k, ∀ x ∈ ball 0 2, s2 (N k + e k • hessOp (v k) x) = 1)
    (hpos : ∀ k, ∀ x ∈ ball 0 2, 0 < trOp (N k + e k • hessOp (v k) x))
    (hbdd : ∀ k, ∀ x ∈ ball 0 2, |v k x| ≤ 1) :
    ∀ j : ℕ, ∃ Kj : ℕ, ∃ h : ℝ, 0 < h ∧ ∀ k ≥ Kj, ∀ x ∈ closedBall 0 1,
      ∀ y ∈ closedBall 0 1, dist x y ≤ h → |v k x - v k y| ≤ 1 / (j + 1) := by
  have hYnn : 0 ≤ 8 * c' / c := by positivity
  obtain ⟨c₁, δ, hc₁, hδ, hδ1, H⟩ :=
    holder_estimate_scaled_uniform (Y := 8 * c' / c) hc hc'pos hYnn hp hM1 hM hpbig
  have hδnn : 0 ≤ 1 - δ := by linarith
  intro j
  -- the level `s` at which the geometric decay beats `1/(j+1)`
  have hlim : Tendsto (fun n : ℕ => (1 - δ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hδnn (by linarith : 1 - δ < 1)
  obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 * (1 - δ) ^ s ≤ 1 / (j + 1) := by
    have h2 : Tendsto (fun n : ℕ => 2 * (1 - δ) ^ n) atTop (𝓝 0) := by
      have h := hlim.const_mul 2
      simpa using h
    have h : ∀ᶠ n in atTop, 2 * (1 - δ) ^ n < 1 / (j + 1) :=
      h2.eventually_lt_const (by positivity : (0 : ℝ) < 1 / (j + 1))
    obtain ⟨s, hs⟩ := h.exists
    exact ⟨s, le_of_lt hs⟩
  -- the threshold on `e k`
  have hev : ∀ᶠ k in atTop, 2 * e k
      ≤ c₁ * 1 ^ 2 * (1 / 2 : ℝ) ^ (2 * s) := by
    have h0 : Tendsto (fun k : ℕ => 2 * e k) atTop (𝓝 0) := by
      have h := hetend.const_mul 2
      simpa using h
    exact (h0.eventually_lt_const
      (by positivity : (0 : ℝ) < c₁ * 1 ^ 2 * (1 / 2 : ℝ) ^ (2 * s))).mono
      fun k hk => le_of_lt hk
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K, (1 / 2 : ℝ) ^ (s + 1), by positivity, ?_⟩
  intro k hk x hx y hy hxy
  have hxnorm : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
  have hsub : ball x 1 ⊆ ball 0 2 := by
    intro z hz
    rw [mem_ball] at hz ⊢
    rw [dist_eq_norm] at hz
    rw [dist_zero_right]
    calc ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
          have h4 : (z - x) + x = z := by abel
          calc ‖z‖ = ‖(z - x) + x‖ := by rw [h4]
            _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < 2 := by linarith
  set Ψ : ℝ⁴ → ℝ := fun z => e k * v k z with hΨdef
  have hΨsub : ball x 1 ⊆ ball 0 2 := hsub
  have hΨ2 : ContDiffOn ℝ 2 Ψ (ball x 1) := by
    have h1 : ContDiffOn ℝ 2 (v k) (ball x 1) := (hv k).mono hΨsub
    have h2 : Ψ = fun z => e k • v k z := by
      funext z
      simp only [hΨdef, smul_eq_mul]
    rw [h2]
    exact h1.const_smul (e k)
  have hhessΨ : ∀ z ∈ ball x 1, hessOp Ψ z = e k • hessOp (v k) z := by
    intro z hz
    have hcd : ContDiffAt ℝ 2 (v k) z := (hv k).contDiffAt (isOpen_ball.mem_nhds (hΨsub hz))
    have h2 : Ψ = fun z => e k * v k z := rfl
    rw [h2]
    exact hessOp_const_mul (e k) hcd
  have heqΨ : ∀ z ∈ ball x 1, s2 (N k + hessOp Ψ z) = 1 := by
    intro z hz
    rw [hhessΨ z hz]
    exact heq k z (hΨsub hz)
  have hposΨ : ∀ z ∈ ball x 1, 0 < trOp (N k + hessOp Ψ z) := by
    intro z hz
    rw [hhessΨ z hz]
    exact hpos k z (hΨsub hz)
  have hlow : ∀ z ∈ ball x 1, -(e k) ≤ Ψ z := by
    intro z hz
    have h1 := hbdd k z (hΨsub hz)
    simp only [hΨdef]
    have h2 : -(1 : ℝ) ≤ v k z := (abs_le.mp h1).1
    nlinarith [h2, he0 k]
  have hup : ∀ z ∈ ball x 1, Ψ z ≤ e k := by
    intro z hz
    have h1 := hbdd k z (hΨsub hz)
    simp only [hΨdef]
    have h2 : v k z ≤ 1 := (abs_le.mp h1).2
    nlinarith [h2, he0 k]
  have hsmall : e k - -(e k) ≤ c₁ * 1 ^ 2 * (1 / 2 : ℝ) ^ (2 * s) := by
    linarith [hK k hk]
  have hYb : 2 * trOp (cofOp (N k)) / c ≤ 8 * c' / c := by
    have h1 : trOp (cofOp (N k)) ≤ 4 * c' := trOp_le_of_quadform_le (hcq' k)
    have h2 : 0 < c := hc
    rw [div_le_div_iff₀ h2 h2]
    nlinarith [h1, hc.le]
  have hres := H (N k) (hN k) (hN1 k) (htrN k) (hcq k) (hcq' k) hYb Ψ x (1 : ℝ) s (-(e k)) (e k)
    (by norm_num) hΨ2 heqΨ hposΨ hlow hup hsmall
  have hxy' : y ∈ closedBall x ((1 : ℝ) ^ 0 * (1 / 2 : ℝ) ^ (s + 1)) := by
    rw [mem_closedBall, dist_comm]
    simpa using hxy
  have hxx : x ∈ closedBall x ((1 : ℝ) ^ 0 * (1 / 2 : ℝ) ^ (s + 1)) := by
    rw [mem_closedBall, dist_self]
    positivity
  have h1 := hres s le_rfl x hxx y hxy'
  have h2 := hres s le_rfl y hxy' x hxx
  simp only [hΨdef] at h1 h2
  have h3 : e k * v k x - e k * v k y ≤ (1 - δ) ^ s * (e k - -(e k)) := h1
  have h4 : e k * v k y - e k * v k x ≤ (1 - δ) ^ s * (e k - -(e k)) := h2
  rw [abs_le]
  constructor
  · -- `-(1/(j+1)) ≤ v k x - v k y`
    have h5 : (1 - δ) ^ s * (e k + e k) ≤ (1 / (j + 1)) * e k := by
      have h6 : (1 - δ) ^ s * (2 * e k) ≤ (1 / (j + 1)) * e k := by
        nlinarith [hs, he0 k]
      nlinarith [h6]
    nlinarith [h4, h5, he0 k]
  · have h5 : (1 - δ) ^ s * (e k + e k) ≤ (1 / (j + 1)) * e k := by
      have h6 : (1 - δ) ^ s * (2 * e k) ≤ (1 / (j + 1)) * e k := by
        nlinarith [hs, he0 k]
      nlinarith [h6]
    nlinarith [h3, h5, he0 k]

/-- **Arzelà--Ascoli**: the family `v k` has a subsequence converging uniformly on
`closedBall 0 (1/2)`.  (The bases `N k` are then handled by passing to a further subsequence on
which `N` converges.) -/
theorem exists_subseq_tendstoUniformly
    {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {v : ℕ → ℝ⁴ → ℝ} {c c' p M : ℝ}
    (hc : 0 < c) (hc'pos : 0 < c') (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p)
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (hcq : ∀ k u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (N k) u, u⟫)
    (hcq' : ∀ k u, ⟪cofOp (N k) u, u⟫ ≤ c' * ‖u‖ ^ 2)
    (he0 : ∀ k, 0 < e k) (hetend : Tendsto e atTop (𝓝 0))
    (hv : ∀ k, ContDiffOn ℝ 2 (v k) (ball 0 2))
    (heq : ∀ k, ∀ x ∈ ball 0 2, s2 (N k + e k • hessOp (v k) x) = 1)
    (hpos : ∀ k, ∀ x ∈ ball 0 2, 0 < trOp (N k + e k • hessOp (v k) x))
    (hbdd : ∀ k, ∀ x ∈ ball 0 2, |v k x| ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ⁴ → ℝ,
      TendstoUniformlyOn (fun k => v (φ k)) g atTop (closedBall 0 1) := by
  have hthr := equicontinuous_threshold hc hc'pos hp hM1 hM hpbig hN hN1 htrN hcq hcq' he0
    hetend hv heq hpos hbdd
  refine Commons.Topology.Metric.arzelaAscoli_threshold (K := closedBall 0 1)
    (isCompact_closedBall 0 1) ?_ hthr
  refine ⟨1, by norm_num, fun k x hx => ?_⟩
  have h1 : x ∈ ball 0 2 := by
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]
    linarith
  exact hbdd k x h1

/-- The trace functional is continuous along a convergent family of operators. -/
theorem tendsto_trOp {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {Nlim : ℝ⁴ →L[ℝ] ℝ⁴}
    (h : Tendsto N atTop (𝓝 Nlim)) : Tendsto (fun k => trOp (N k)) atTop (𝓝 (trOp Nlim)) := by
  have h1 : ∀ i : Fin 4, Tendsto (fun k => ⟪N k (stdB4 i), stdB4 i⟫) atTop
      (𝓝 ⟪Nlim (stdB4 i), stdB4 i⟫) := by
    intro i
    have hcont : Continuous (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => ⟪M (stdB4 i), stdB4 i⟫) :=
      Continuous.inner ((ContinuousLinearMap.apply ℝ ℝ⁴ (stdB4 i)).continuous) continuous_const
    exact (hcont.tendsto Nlim).comp h
  have h2 := tendsto_finset_sum Finset.univ (fun i _ => h1 i)
  rw [show (fun k => trOp (N k)) = fun k => ∑ i : Fin 4, ⟪N k (stdB4 i), stdB4 i⟫ from
      funext fun k => trOp_eq_sum (N k),
    show trOp Nlim = ∑ i : Fin 4, ⟪Nlim (stdB4 i), stdB4 i⟫ from trOp_eq_sum Nlim]
  simpa using h2

/-- `cofOp` is continuous along a convergent family of operators. -/
theorem tendsto_cofOp {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {Nlim : ℝ⁴ →L[ℝ] ℝ⁴}
    (h : Tendsto N atTop (𝓝 Nlim)) : Tendsto (fun k => cofOp (N k)) atTop (𝓝 (cofOp Nlim)) := by
  have h1 : Tendsto (fun k => trOp (N k) • (1 : ℝ⁴ →L[ℝ] ℝ⁴)) atTop
      (𝓝 (trOp Nlim • (1 : ℝ⁴ →L[ℝ] ℝ⁴))) := (tendsto_trOp h).smul tendsto_const_nhds
  have h3 := h1.sub h
  rw [show (fun k => cofOp (N k)) = fun k => trOp (N k) • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - N k from
    funext fun k => rfl,
    show cofOp Nlim = trOp Nlim • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - Nlim from rfl]
  exact h3

/-- **The viscosity limit in the `s2`-form**: this is the form in which Proposition 4.1 uses
`isViscSolution_limit`. -/
theorem isViscSolution_limit_s2 {s : Set ℝ⁴} (hs : IsOpen s)
    {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {e : ℕ → ℝ} {v : ℕ → ℝ⁴ → ℝ} {Nlim : ℝ⁴ →L[ℝ] ℝ⁴} {g : ℝ⁴ → ℝ}
    {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 ≤ c')
    (hN : ∀ k, (N k).IsSymmetric) (hN1 : ∀ k, s2 (N k) = 1) (htrN : ∀ k, 0 < trOp (N k))
    (he0 : ∀ k, 0 < e k)
    (hcq : ∀ k u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (N k) u, u⟫)
    (hcq' : ∀ k u, ⟪cofOp (N k) u, u⟫ ≤ c' * ‖u‖ ^ 2)
    (hNtend : Tendsto N atTop (𝓝 Nlim)) (hetend : Tendsto e atTop (𝓝 0))
    (hv : ∀ k, ContDiffOn ℝ 2 (v k) s)
    (heq : ∀ k, ∀ x ∈ s, s2 (N k + e k • hessOp (v k) x) = 1)
    (hpos : ∀ k, ∀ x ∈ s, 0 < trOp (N k + e k • hessOp (v k) x))
    (hconv : ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn v g atTop K) :
    IsViscSolution (fun M => -pairOp (cofOp Nlim) M) g s := by
  refine isViscSolution_limit (C := fun k => cofOp (N k)) (Cstar := cofOp Nlim) (N := N)
    (w := v) (g := g) (s := s) (c := c) (c' := c') hs hc hc' hN hN1 htrN
    (fun k => rfl) he0 (fun k => cofOp_isSymmetric (hN k)) hcq hcq' (tendsto_cofOp hNtend)
    hetend hv ?_ hpos hconv
  intro k x hx
  have hsym : (hessOp (v k) x).IsSymmetric :=
    hessOp_symm_of_contDiffAt ((hv k).contDiffAt (hs.mem_nhds hx))
  exact (fop_eq_zero_iff_s2 (hN k) hsym (ne_of_gt (he0 k)) (hN1 k)).mpr (heq k x hx)

end

end Submission
