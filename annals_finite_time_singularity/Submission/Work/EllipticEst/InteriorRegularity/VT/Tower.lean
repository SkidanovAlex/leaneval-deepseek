/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): the Sobolev tower.

This file proves the local regularity gain for a pair `(V, G)` of integrable functions satisfying
the weak identity `∫ V · Kop ψ = ∫ G · ψ` on a set `W`:

  for every `x₀` with `closedBall x₀ (δ/8) ⊆ W`, and every `m`, there is a smooth compactly
  supported cut-off `χ` with `χ x₀ = 1` and `Td (χ · V) ∈ H^{m+2}`.

The proof uses a chain of nested cut-offs `χ_j` (`j = 0, …, N`, `N = m + 4`) with
`tsupport χ_j ⊆ {χ_{j+1} = 1}`, the localized distributional equation `localEqDist`, and the
two-round gain lemma `gain_step` applied at order `σ-1`: each step gains one derivative, because
the commutator terms `2 (∂_iχ_j) ∂_i Td (χ_{j+1} · V)` only reach `H^{σ-1}`.

The base case is `Td (χ_N · V) ∈ H^{-2}` (`memSobolev_neg_two`).
-/
import Mathlib.Analysis.Distribution.Sobolev
import Submission.Work.EllipticEst.InteriorRegularity.VT.VInteg
import Submission.Work.EllipticEst.InteriorRegularity.VT.Smooth
import Submission.Work.EllipticEst.InteriorRegularity.VT.DerivAux
import Submission.Work.EllipticEst.InteriorRegularity.VT.DistEq
import Submission.Work.EllipticEst.InteriorRegularity.gain_step
import Submission.Work.EllipticEst.InteriorRegularity.memSobolev_neg_two
import Submission.Work.EllipticEst.InteriorRegularity.Q0.SobChain
import Submission.Work.EllipticEst.InteriorRegularity.Q0.laplacian_smulLeftCLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The local Sobolev tower.** -/
theorem tower {V G : E2 → ℂ} (hV : Integrable V) (hG : Integrable G)
    (hGs : ∀ n : ℕ, ContDiff ℝ n G) {W : Set E2}
    (hweak : ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Function.support ψ ⊆ W → ∫ x, V x * Kop ψ x = ∫ x, G x * ψ x)
    {x₀ : E2} {δ : ℝ} (hδ : 0 < δ) (hxδ : δ ≤ x₀ 1) (hyδ : δ ≤ Real.pi / 2 - x₀ 1)
    (hWball : Metric.closedBall x₀ (δ / 8) ⊆ W) (m : ℕ) :
    ∃ χ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n χ) ∧ HasCompactSupport χ ∧
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Metric.closedBall x₀ ρ, χ x = 1) ∧
      ∀ (h : Integrable (fun x => χ x * V x)),
        TemperedDistribution.MemSobolev ((m : ℝ) + 2) 2 (Td (fun x => χ x * V x) h) := by
  classical
  set N : ℕ := m + 4 with hNdef
  set e : ℕ → ℝ := fun j => δ / (64 * 4 ^ N) * 4 ^ j with he
  have he_pos : ∀ j, 0 < e j := by
    intro j
    rw [he]
    positivity
  have he_succ : ∀ j, e (j + 1) = 4 * e j := by
    intro j
    simp only [he, pow_succ]
    ring
  have he_le : ∀ j ≤ N, e j ≤ e N := by
    intro j hj
    simp only [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
  have he_N : e N = δ / 64 := by
    rw [he]
    field_simp
  have h3eN : 3 * e N ≤ δ / 8 := by
    rw [he_N]
    linarith
  have h8eN : 8 * e N < δ / 2 := by
    rw [he_N]
    linarith
  -- the balls `ball x₀ (3 e j)` lie in the strip and in `W`
  have hU_strip : ∀ j ≤ N, Metric.ball x₀ (3 * e j) ⊆ stripE := by
    intro j hj x hx
    rw [mem_stripE]
    exact mem_Ioo_of_mem_ball hδ hxδ hyδ
      (Metric.ball_subset_ball (by linarith [he_le j hj]) hx)
  have hU_W : ∀ j ≤ N, Metric.ball x₀ (3 * e j) ⊆ W := by
    intro j hj x hx
    apply hWball
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h3 : 3 * e j ≤ 3 * e N := by linarith [he_le j hj]
    linarith
  -- the cut-off family
  let χ : ℕ → E2 → ℂ := fun j => cfun x₀ (e j) (he_pos j)
  have hχ_smooth : ∀ j (n : ℕ), ContDiff ℝ n (χ j) :=
    fun j n => cfun_contDiff x₀ (e j) (he_pos j) n
  have hχ_cc : ∀ j, HasCompactSupport (χ j) := fun j => cfun_hasCompactSupport x₀ (e j) (he_pos j)
  have hχ_ts : ∀ j, tsupport (χ j) = Metric.closedBall x₀ (2 * e j) :=
    fun j => cfun_tsupport x₀ (e j) (he_pos j)
  have hχ_one : ∀ j, ∀ x ∈ Metric.closedBall x₀ (e j), χ j x = 1 :=
    fun j x hx => cfun_one (he_pos j) hx
  have htsU : ∀ j, tsupport (χ j) ⊆ Metric.ball x₀ (3 * e j) := by
    intro j x hx
    rw [hχ_ts j, Metric.mem_closedBall, dist_eq_norm] at hx
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [he_pos j]
  have hsucc_one : ∀ j, ∀ x ∈ Metric.ball x₀ (3 * e j), χ (j + 1) x = 1 := by
    intro j x hx
    have hx' : ‖x - x₀‖ < 3 * e j := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    apply hχ_one (j + 1)
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h4 : e (j + 1) = 4 * e j := he_succ j
    have h5 : (0 : ℝ) < e j := he_pos j
    linarith
  have hmul_eq : ∀ j, (fun x => χ j x * (χ (j + 1) x * V x)) = fun x => χ j x * V x := by
    intro j
    funext x
    by_cases hx : χ j x = 0
    · simp [hx]
    · have hxU : x ∈ Metric.ball x₀ (3 * e j) :=
        htsU j (subset_closure (Function.mem_support.mpr hx))
      rw [hsucc_one j x hxU]
      ring
  -- integrability witnesses and the distributions `θ j`
  have hInt : ∀ j, Integrable (fun x => χ j x * V x) :=
    fun j => integrable_mul_of_cc hV (hχ_cc j) (hχ_smooth j)
  have hIntG : ∀ j, Integrable (fun x => χ j x * G x) :=
    fun j => integrable_mul_of_cc hG (hχ_cc j) (hχ_smooth j)
  let θ : ℕ → 𝓢'(E2, ℂ) := fun j => Td (fun x => χ j x * V x) (hInt j)
  have hθ_apply : ∀ j (ψ : 𝓢(E2, ℂ)), θ j ψ = ∫ x, ψ x • (χ j x * V x) :=
    fun j ψ => Td_apply _ _ ψ
  have hθ_eq : ∀ j, TemperedDistribution.smulLeftCLM ℂ (χ j) (θ (j + 1)) = θ j := by
    intro j
    ext ψ
    rw [TemperedDistribution.smulLeftCLM_apply_apply, hθ_apply (j + 1), hθ_apply j]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ((SchwartzMap.smulLeftCLM ℂ (χ j)) ψ) x • (χ (j + 1) x * V x)
      = ψ x • (χ j x * V x)
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_of_cc (hχ_cc j) (hχ_smooth j))]
    simp only [smul_eq_mul]
    by_cases hx : χ j x = 0
    · simp [hx]
    · have hxU : x ∈ Metric.ball x₀ (3 * e j) :=
        htsU j (subset_closure (Function.mem_support.mpr hx))
      rw [hsucc_one j x hxU]
      ring
  -- the induction
  have hP : ∀ k, k ≤ N → TemperedDistribution.MemSobolev (-2 + (k : ℝ)) 2 (θ (N - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      have h := Td_memSobolev_neg_two (hInt N)
      have hm : (-2 : ℝ) + ((0 : ℕ) : ℝ) ≤ -2 := by norm_num
      exact h.mono hm
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      have hj1 : N - (k + 1) + 1 = N - k := by omega
      set j : ℕ := N - (k + 1) with hjdef
      have hIH : TemperedDistribution.MemSobolev (-2 + (k : ℝ)) 2 (θ (j + 1)) := by
        rw [hj1]
        exact ih hkN
      -- the tangent cut-off for the current step
      have hr4 : 0 < 4 * e j := by linarith [he_pos j]
      set tt : E2 → ℂ :=
        fun x => cfun x₀ (4 * e j) hr4 x * (Real.tan (x 1) : ℂ) with httdef
      have hcf_ts : tsupport (cfun x₀ (4 * e j) hr4) ⊆ Metric.ball x₀ (δ / 2) := by
        rw [cfun_tsupport]
        refine Metric.closedBall_subset_ball ?_
        have h := he_le j (by omega : j ≤ N)
        linarith
      have htt_smooth : ∀ n : ℕ, ContDiff ℝ n tt := by
        intro n
        rw [httdef]
        exact contDiff_mul_of_tsupport_subset (contDiffOn_tan_coord hδ hxδ hyδ n)
          Metric.isOpen_ball (cfun_contDiff x₀ (4 * e j) hr4) hcf_ts
      have htt_cc : HasCompactSupport tt := by
        rw [httdef]
        exact (cfun_hasCompactSupport x₀ (4 * e j) hr4).mul_right
      have htt_one : ∀ x ∈ Metric.ball x₀ (3 * e j), tt x = (Real.tan (x 1) : ℂ) := by
        intro x hx
        rw [Metric.mem_ball, dist_eq_norm] at hx
        have h4 : x ∈ Metric.closedBall x₀ (4 * e j) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          linarith [he_pos j]
        show cfun x₀ (4 * e j) hr4 x * (Real.tan (x 1) : ℂ) = (Real.tan (x 1) : ℂ)
        rw [cfun_one hr4 h4, one_mul]
      -- the localized distributional equation
      have heq := localEqDist (V := V) (G := G) (W := W) hweak
        (hχ_cc j) (hχ_smooth j) (hχ_cc (j + 1)) (hχ_smooth (j + 1))
        (hχ_cc (j + 1)) (hχ_smooth (j + 1)) htt_cc htt_smooth
        Metric.isOpen_ball (htsU j) (hU_W j (by omega)) (fun x hx => hsucc_one j x hx)
        (fun x hx => hsucc_one j x hx) htt_one
        hV hG (hInt j) (hInt (j + 1)) (hIntG j)
      -- the source of the gain step
      set Gc : 𝓢'(E2, ℂ) :=
        (- Td (fun x => χ j x * G x) (hIntG j)
            + TemperedDistribution.smulLeftCLM ℂ (rho0 (χ j) tt) (θ (j + 1))
            + TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d0 (χ j) x)
                (LineDeriv.lineDerivOp e0 (θ (j + 1)))
            + TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d1 (χ j) x)
                (LineDeriv.lineDerivOp e1 (θ (j + 1)))) with hGcdef
      have heqG : Laplacian.laplacian (θ j)
          = Gc
            + TemperedDistribution.smulLeftCLM ℂ (fun x => 5 * χ (j + 1) x)
                (LineDeriv.lineDerivOp e0 (θ j))
            + TemperedDistribution.smulLeftCLM ℂ
                (fun x => -(χ (j + 1) x * tt x))
                (LineDeriv.lineDerivOp e1 (θ j))
            + TemperedDistribution.smulLeftCLM ℂ (fun x => -6 * χ (j + 1) x) (θ j) := by
        rw [hGcdef]
        exact heq
      have hGc_mem : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2 Gc := by
        rw [hGcdef]
        have h1 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (Td (fun x => χ j x * G x) (hIntG j)) :=
          Td_memSobolev_of_smooth_compact (hIntG j) ((hχ_cc j).mul_right)
            (fun n => (hχ_smooth j n).mul (hGs n)) _
        have h2 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (TemperedDistribution.smulLeftCLM ℂ (rho0 (χ j) tt) (θ (j + 1))) :=
          Q0.mulSob (hasCompactSupport_rho0 (hχ_cc j) (hχ_smooth j))
            (contDiff_rho0 (hχ_smooth j) htt_smooth) (hIH.mono (by linarith))
        have h3 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d0 (χ j) x)
              (LineDeriv.lineDerivOp e0 (θ (j + 1)))) :=
          Q0.mulSob
            (hasCompactSupport_const_mul (hasCompactSupport_d0 (hχ_cc j) (hχ_smooth j)) 2)
            (fun n => contDiff_const.mul (contDiff_d0 (hχ_smooth j) n))
            (TemperedDistribution.MemSobolev.lineDerivOp (m := e0) hIH)
        have h4 : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2
            (TemperedDistribution.smulLeftCLM ℂ (fun x => 2 * d1 (χ j) x)
              (LineDeriv.lineDerivOp e1 (θ (j + 1)))) :=
          Q0.mulSob
            (hasCompactSupport_const_mul (hasCompactSupport_d1 (hχ_cc j) (hχ_smooth j)) 2)
            (fun n => contDiff_const.mul (contDiff_d1 (hχ_smooth j) n))
            (TemperedDistribution.MemSobolev.lineDerivOp (m := e1) hIH)
        exact ((h1.neg.add h2).add h3).add h4
      have hθ_mem : TemperedDistribution.MemSobolev (-2 + (k : ℝ) - 1) 2 (θ j) := by
        have h := Q0.mulSob (hχ_cc j) (hχ_smooth j) hIH
        rw [hθ_eq j] at h
        exact h.mono (by linarith)
      have hb_cc : HasCompactSupport (fun x => 5 * χ (j + 1) x) :=
        hasCompactSupport_const_mul (hχ_cc (j + 1)) 5
      have hb_sm : ∀ n : ℕ, ContDiff ℝ n (fun x => 5 * χ (j + 1) x) :=
        fun n => contDiff_const.mul (hχ_smooth (j + 1) n)
      have hb'_cc : HasCompactSupport (fun x => -(χ (j + 1) x * tt x)) :=
        ((hχ_cc (j + 1)).mul_right).neg
      have hb'_sm : ∀ n : ℕ, ContDiff ℝ n (fun x => -(χ (j + 1) x * tt x)) :=
        fun n => ((hχ_smooth (j + 1) n).mul (htt_smooth n)).neg
      have hc_cc : HasCompactSupport (fun x => -6 * χ (j + 1) x) :=
        hasCompactSupport_const_mul (hχ_cc (j + 1)) (-6)
      have hc_sm : ∀ n : ℕ, ContDiff ℝ n (fun x => -6 * χ (j + 1) x) :=
        fun n => contDiff_const.mul (hχ_smooth (j + 1) n)
      have hmain := gain_step (E := E2) (σ := -2 + (k : ℝ) - 1) (u := θ j) (G := Gc)
        (b := fun x => 5 * χ (j + 1) x)
        (b' := fun x => -(χ (j + 1) x * tt x))
        (c := fun x => -6 * χ (j + 1) x) e0 e1
        hb_cc hb_sm hb'_cc hb'_sm hc_cc hc_sm hGc_mem hθ_mem heqG
      have hk1 : (-2 + (k : ℝ) - 1) + 2 = -2 + ((k + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hk1] at hmain
      exact hmain
  -- conclusion
  have hfinal : TemperedDistribution.MemSobolev ((m : ℝ) + 2) 2 (θ 0) := by
    have h := hP N le_rfl
    rw [Nat.sub_self] at h
    have : (-2 + (N : ℝ)) = (m : ℝ) + 2 := by
      rw [hNdef]
      push_cast
      ring
    rwa [this] at h
  refine ⟨χ 0, hχ_smooth 0, hχ_cc 0, ?_, ?_⟩
  · exact ⟨e 0, he_pos 0, fun x hx => hχ_one 0 x hx⟩
  · intro h
    exact hfinal

end Work.EllipticEst.InteriorRegularity.VT
