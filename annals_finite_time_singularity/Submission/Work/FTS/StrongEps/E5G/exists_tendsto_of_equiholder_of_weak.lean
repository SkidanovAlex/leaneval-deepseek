import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.exists_normed_bump_test
import Submission.Work.FTS.StrongEps.E5G.dist_setIntegral_mul_le
import Submission.Work.FTS.StrongEps.E5G.continuousOn_of_pointwise_of_equiholder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter Metric
open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-- **Equi-Hölder implies continuity on compacta.**  A function which is `C`-Hölder of
exponent `1/2` on a set is continuous there. -/
private lemma continuousOn_of_equiholder_aux {g : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ p ∈ K, ∀ q ∈ K, dist (g p) (g q) ≤ C * dist p q ^ (1 / 2 : ℝ)) :
    ContinuousOn g K := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ 2, by positivity, fun a ha hab => ?_⟩
  have hstep : dist a b ^ (1 / 2 : ℝ) ≤ ε / (C + 1) := by
    have hsq : ((ε / (C + 1)) ^ 2) ^ (1 / 2 : ℝ) = ε / (C + 1) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    have h1 : dist a b ^ (1 / 2 : ℝ) ≤ ((ε / (C + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow dist_nonneg hab.le (by norm_num)
    rwa [hsq] at h1
  have h2 : dist (g a) (g b) ≤ C * (ε / (C + 1)) :=
    le_trans (h a ha b hb) (mul_le_mul_of_nonneg_left hstep hC)
  have h3 : C * (ε / (C + 1)) < ε := by
    have h4 : C * (ε / (C + 1)) = C * ε / (C + 1) := by ring
    rw [h4, div_lt_iff₀ hC1]
    nlinarith
  linarith

/-- **The pointwise limit exists.**  Under the weak test-integral convergence hypothesis, the
equi-Hölder family `mixed j i (V n)` converges at every point of the quadrant `Q0`. -/
private lemma exists_tendsto_pointwise {V : ℕ → Fn} (j i : ℕ)
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) p.1 p.2 * φ p.1 p.2) Filter.atTop (nhds L))
    (q : ℝ × ℝ) (hq : q ∈ Work.FTS.EllipticEst.Q0) :
    ∃ L : ℝ, Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2)
      Filter.atTop (nhds L) := by
  classical
  -- a ball around `q` inside the open quadrant
  obtain ⟨ρ, hρpos, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq)
  -- the compact set carrying the Hölder bound
  set K : Set (ℝ × ℝ) := Metric.closedBall q (ρ / 2) with hKdef
  have hKcomp : IsCompact K := isCompact_closedBall q (ρ / 2)
  have hKQ : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    hρsub (Metric.closedBall_subset_ball (by linarith) hp)
  obtain ⟨C, hCnn, hCb⟩ := hequi K hKcomp hKQ
  have hqK : q ∈ K := Metric.mem_closedBall_self (by linarith)
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  set δ : ℝ := min (ρ / 2) ((ε / (4 * (C + 1))) ^ 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by linarith) (by positivity)
  have hδρ : δ ≤ ρ / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδε : δ ≤ (ε / (4 * (C + 1))) ^ 2 := by rw [hδdef]; exact min_le_right _ _
  -- the averaging bump at scale `δ`
  obtain ⟨ψ, hψsm, hψcs, hψnn, hψint, hψdist, hψzero, hψKint, hψball⟩ :=
    exists_normed_bump_test q hρpos hδpos hδρ
  have hψKint' : (∫ p in K, ψ p) = 1 := by rw [hKdef]; exact hψKint
  -- the bump lives in `Q0` *including its topological support*
  have htsupp : tsupport ψ ⊆ Work.FTS.EllipticEst.Q0 := by
    have hsupp : Function.support ψ ⊆ Metric.ball q δ := by
      intro p hp
      rw [Metric.mem_ball]
      by_contra hcon
      exact hp (hψzero p (le_of_not_gt hcon))
    calc tsupport ψ ⊆ closure (Metric.ball q δ) := closure_mono hsupp
      _ ⊆ Metric.closedBall q δ := Metric.closure_ball_subset_closedBall
      _ ⊆ Metric.closedBall q (ρ / 2) := Metric.closedBall_subset_closedBall (by linarith)
      _ ⊆ Metric.ball q ρ := Metric.closedBall_subset_ball (by linarith)
      _ ⊆ Work.FTS.EllipticEst.Q0 := hρsub
  -- the same bump, curried, as a test function
  set φ : ℝ → ℝ → ℝ := fun z θ => ψ (z, θ) with hφdef
  have huncurry : Function.uncurry φ = ψ := rfl
  obtain ⟨L, hL⟩ := hweak φ (fun n => huncurry ▸ hψsm n) (huncurry ▸ hψcs)
    (huncurry ▸ htsupp)
  set A : ℕ → ℝ := fun n => ∫ p in Work.FTS.EllipticEst.Q0,
    Work.Spaces.mixed j i (V n) p.1 p.2 * ψ p with hAdef
  have hL' : Filter.Tendsto A Filter.atTop (nhds L) := by
    rw [show A = (fun n => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) p.1 p.2 * φ p.1 p.2) from rfl]
    exact hL
  -- the averaging estimate
  have hbound : ∀ k : ℕ, dist (Work.Spaces.mixed j i (V k) q.1 q.2) (A k)
      ≤ C * δ ^ (1 / 2 : ℝ) := by
    intro k
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (V k) p.1 p.2) K :=
      continuousOn_of_equiholder_aux hCnn (fun p hp b hb => by
        rw [Real.dist_eq]
        exact hCb k p hp b hb)
    have hψcont : ContinuousOn ψ K := ((hψsm 1).continuous).continuousOn
    have hψK : ∀ p, ψ p ≠ 0 → p ∈ K := fun p hp =>
      Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le (hψdist p hp) hδρ))
    have hbd : ∀ p ∈ K, dist (Work.Spaces.mixed j i (V k) p.1 p.2)
        (Work.Spaces.mixed j i (V k) q.1 q.2) ≤ C * dist p q ^ (1 / 2 : ℝ) := fun p hp => by
      rw [Real.dist_eq]
      exact hCb k p hp q hqK
    have hδb : ∀ p, ψ p ≠ 0 → dist p q ≤ δ := fun p hp => (hψdist p hp).le
    have hest := dist_setIntegral_mul_le (K := K)
      (f := fun p : ℝ × ℝ => Work.Spaces.mixed j i (V k) p.1 p.2) (ψ := ψ) (q := q)
      (C := C) (δ := δ) hKcomp hCnn hδpos.le hcont hψcont hψnn hψK hψKint' hbd hδb
    have hAeq : A k = ∫ p in K, Work.Spaces.mixed j i (V k) p.1 p.2 * ψ p := by
      rw [hAdef]
      exact MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        Work.FTS.EllipticEst.isOpen_Q0.measurableSet hKQ (fun p hp => by
          have hpk : p ∉ K := hp.2
          have hlt : ρ / 2 < dist p q :=
            not_le.mp (fun hle => hpk (Metric.mem_closedBall.mpr hle))
          have hψp : ψ p = 0 := hψzero p (le_trans hδρ hlt.le)
          simp [hψp])
    rw [hAeq, dist_comm]
    exact hest
  have hAcauchy : CauchySeq A := hL'.cauchySeq
  rw [Metric.cauchySeq_iff] at hAcauchy
  obtain ⟨N, hN⟩ := hAcauchy (ε / 2) (by linarith)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsqle : δ ^ (1 / 2 : ℝ) ≤ ε / (4 * (C + 1)) := by
    have hsq : ((ε / (4 * (C + 1))) ^ 2) ^ (1 / 2 : ℝ) = ε / (4 * (C + 1)) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    have h1 : δ ^ (1 / 2 : ℝ) ≤ ((ε / (4 * (C + 1))) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hδpos.le hδε (by norm_num)
    rwa [hsq] at h1
  have hcsq : C * δ ^ (1 / 2 : ℝ) ≤ ε / 4 := by
    have h1 : C * (ε / (4 * (C + 1))) ≤ ε / 4 := by
      have h2 : C * (ε / (4 * (C + 1))) = (C * ε) / (4 * (C + 1)) := by ring
      rw [h2, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (C + 1))]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hsqle hCnn) h1
  have hbm : dist (Work.Spaces.mixed j i (V m) q.1 q.2) (A m) ≤ ε / 4 :=
    le_trans (hbound m) hcsq
  have hbn : dist (A n) (Work.Spaces.mixed j i (V n) q.1 q.2) ≤ ε / 4 := by
    rw [dist_comm]
    exact le_trans (hbound n) hcsq
  have hA : dist (A m) (A n) < ε / 2 := hN m hm n hn
  have hmid : dist (Work.Spaces.mixed j i (V m) q.1 q.2) (A m) + dist (A m) (A n)
      + dist (A n) (Work.Spaces.mixed j i (V n) q.1 q.2) < ε := by
    have h2 := add_lt_add_of_le_of_lt hbm hA
    have h3 := add_lt_add_of_lt_of_le h2 hbn
    have h4 : ε / 4 + ε / 2 + ε / 4 = ε := by ring
    rwa [h4] at h3
  exact lt_of_le_of_lt (dist_triangle4 _ _ _ _) hmid

theorem exists_tendsto_of_equiholder_of_weak {V : ℕ → Work.FTS.Galerkin.Fn} (j i : ℕ)
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j i (V n) p.1 p.2 * φ p.1 p.2) Filter.atTop (nhds L)) :
    ∃ Φ : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 ∧
      ∀ q ∈ Work.FTS.EllipticEst.Q0,
        Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
          (nhds (Φ q.1 q.2)) := by
  classical
  have hpt : ∀ q : ℝ × ℝ, q ∈ Work.FTS.EllipticEst.Q0 →
      ∃ L : ℝ, Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2)
        Filter.atTop (nhds L) := fun q hq => exists_tendsto_pointwise j i hequi hweak q hq
  choose Φ₀ hΦ₀ using hpt
  refine ⟨fun z θ => if h : (z, θ) ∈ Work.FTS.EllipticEst.Q0 then Φ₀ (z, θ) h else 0,
    ?_, ?_⟩
  · refine continuousOn_of_pointwise_of_equiholder
      (f := fun n p => Work.Spaces.mixed j i (V n) p.1 p.2)
      (Φ := fun p : ℝ × ℝ =>
        if h : p ∈ Work.FTS.EllipticEst.Q0 then Φ₀ p h else 0)
      Work.FTS.EllipticEst.isOpen_Q0 ?_ ?_
    · intro q hq
      show Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds ((if h : q ∈ Work.FTS.EllipticEst.Q0 then Φ₀ q h else 0)))
      rw [dite_eq_left hq]
      exact hΦ₀ q hq
    · intro K hK hKQ
      obtain ⟨C, hCnn, hCb⟩ := hequi K hK hKQ
      exact ⟨C, hCnn, fun n p hp q hq => by
        rw [Real.dist_eq]
        exact hCb n p hp q hq⟩
  · intro q hq
    show Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
      (nhds ((if h : q ∈ Work.FTS.EllipticEst.Q0 then Φ₀ q h else 0)))
    rw [dite_eq_left hq]
    exact hΦ₀ q hq

end Work.FTS.StrongEps.E5G
