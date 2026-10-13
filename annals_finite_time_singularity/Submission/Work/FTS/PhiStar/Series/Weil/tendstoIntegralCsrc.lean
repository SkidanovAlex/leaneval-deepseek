import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Series.Weil.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

/-- The partial sums `csrc` of the source series factor through the angular partial sums of the
model `ψ`:  `csrc α ψ N z θ = α² · 𝒜φ(z) · Σ_{m ≤ N} bmode m ψ · eFam m θ`.
(`cmode_RemSource` computes `cmode m (RemSource α ψ) z = α²𝒜φ(z)·bmode m ψ`.) -/
lemma csrc_eq_partialSum (α : ℝ) (ψ : ℝ → ℝ) (N : ℕ) (z θ : ℝ) :
    csrc α ψ N z θ = α ^ 2 * Work.FTS.VocabO.phiA α z *
      (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  simp only [csrc, Work.FTS.PhiStar.Series.cmode_RemSource]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/-- Pointwise convergence of the partial sums of the source series at a fixed angular point,
from the uniform convergence hypothesis on the angular model. -/
lemma tendsto_csrc (α : ℝ) (ψ : ℝ → ℝ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |(∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ| ≤ ε)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => csrc α ψ N z θ) Filter.atTop
      (nhds (Work.FTS.PhiStar.RemSource α ψ z θ)) := by
  have hS : Filter.Tendsto (fun n : ℕ => ∑ m ∈ Finset.range (n + 1),
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      Filter.atTop (nhds (ψ θ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by linarith)
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      have h := hN n hn θ hθ
      linarith⟩
  simp only [csrc_eq_partialSum, Work.FTS.PhiStar.RemSource]
  exact hS.const_mul (α ^ 2 * Work.FTS.VocabO.phiA α z)

theorem tendstoIntegralCsrc (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hbound : ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |(∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ| ≤ ε)
    {φ : ℝ → ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.Weil.csrc α ψ N p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  classical
  obtain ⟨M, hMpos, hbound⟩ := hbound
  -- a compact box containing the support of the test function
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcomp.isClosed.measurableSet
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hφ0 : ∀ p : ℝ × ℝ, p ∉ K → φ p.1 p.2 = 0 := by
    intro p hp
    refine hbox p ?_
    rintro ⟨h1, h2⟩
    exact hp ⟨⟨le_of_lt h1.1, le_of_lt h1.2⟩, ⟨le_of_lt h2.1, le_of_lt h2.2⟩⟩
  -- continuity of the individual factors on `K`
  have hphiK : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.VocabO.phiA α p.1) K := by
    intro p hp
    exact (Work.FTS.PhiStar.contDiffAt_phiA α (lt_of_lt_of_le ha hp.1.1)).continuousAt
      |>.comp_continuousWithinAt continuousWithinAt_fst
  have hφK : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) K :=
    (hφ 0).continuous.continuousOn
  have hwK : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ ((5 - α) / α) * Real.cos p.2) K :=
    (continuous_fst.continuousOn.rpow_const
        (fun p hp => Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))).mul
      (Real.continuous_cos.comp continuous_snd).continuousOn
  have hSNcont : ∀ N : ℕ, ContinuousOn (fun p : ℝ × ℝ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) K :=
    fun N => continuousOn_finsetSum _ (fun m _ =>
      (continuous_const.mul ((continuous_eFam m).comp continuous_snd)).continuousOn)
  -- the dominated convergence theorem on the box
  have hmain : Filter.Tendsto
      (fun N : ℕ => ∫ p in K, csrc α ψ N p.1 p.2 * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in K, Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict K)
      (fun p : ℝ × ℝ => α ^ 2 * 20 * M * |φ p.1 p.2|
        * |p.1 ^ ((5 - α) / α) * Real.cos p.2|) ?_ ?_ ?_ ?_
    · intro N
      have hcont : ContinuousOn (fun p : ℝ × ℝ => α ^ 2 * Work.FTS.VocabO.phiA α p.1
          * (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) K :=
        ((continuousOn_const (c := α ^ 2)).mul hphiK |>.mul (hSNcont N) |>.mul hφK |>.mul hwK)
      exact (hcont.aestronglyMeasurable hKmeas).congr
        (Filter.Eventually.of_forall (fun p => by simp only [csrc_eq_partialSum]))
    · have hcontb : ContinuousOn (fun p : ℝ × ℝ => α ^ 2 * 20 * M * |φ p.1 p.2|
          * |p.1 ^ ((5 - α) / α) * Real.cos p.2|) K :=
        (continuousOn_const (c := α ^ 2 * 20 * M)).mul hφK.abs |>.mul hwK.abs
      exact ContinuousOn.integrableOn_compact hKcomp hcontb
    · intro N
      filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
      obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKsub hp)
      have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ1, le_of_lt hθ2⟩
      have hS : |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2| ≤ M := hbound N p.2 hθI
      have hphiA : |Work.FTS.VocabO.phiA α p.1| ≤ 20 :=
        Work.FTS.PhiStar.phiA_abs_le hα (by linarith) (le_of_lt hz)
      have hcs : |csrc α ψ N p.1 p.2| ≤ α ^ 2 * 20 * M := by
        rw [csrc_eq_partialSum, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg α)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hphiA (sq_nonneg α)) hS (abs_nonneg _)
          (by positivity)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcs (abs_nonneg _))
        (abs_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
      obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKsub hp)
      have hθI : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ1, le_of_lt hθ2⟩
      have hlim : Filter.Tendsto (fun N : ℕ => csrc α ψ N p.1 p.2) Filter.atTop
          (nhds (Work.FTS.PhiStar.RemSource α ψ p.1 p.2)) := tendsto_csrc α ψ hconv hθI
      exact (hlim.mul tendsto_const_nhds).mul tendsto_const_nhds
  -- restrict both integrals from the quadrant to the box
  have hrew : ∀ (g : ℝ × ℝ → ℝ), (∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, g p = 0) →
      (∫ p in Work.FTS.EllipticEst.Q0, g p) = ∫ p in K, g p := fun g hg =>
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet hKsub hg
  have hQK : (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = fun N : ℕ => ∫ p in K,
        csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
    funext N
    refine hrew (fun p => csrc α ψ N p.1 p.2 * φ p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) ?_
    intro p hp
    show csrc α ψ N p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
    rw [hφ0 p hp.2]
    ring
  have hQK' : (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
    refine hrew (fun p => Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) ?_
    intro p hp
    show Work.FTS.PhiStar.RemSource α ψ p.1 p.2 * φ p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
    rw [hφ0 p hp.2]
    ring
  rw [hQK, hQK']
  exact hmain

end Work.FTS.PhiStar.Series.Weil
