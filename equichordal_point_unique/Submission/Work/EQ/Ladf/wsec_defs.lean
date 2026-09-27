import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.LAFree
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.Ladf.candChain_fwdW_bwdW
import Submission.Work.EQ.germC_leaf
import Submission.Work.EQ.invBranch_ugermC_noGamma
import Submission.Work.EQ.HeteroGerm

/-!
# Vocabulary for the one-sided section lemma `la_witness_section`

`IsSectAt a h g u₀ ρ` records that `g` is an *analytic local section of `⁰H`* over the
`ψ₁`-plane at `u₀`: every value is a chain in `H0 a h`, its stable parameter is the parameter
itself, and all chain coordinates are analytic on the ball.

The two interface lemmas proved against this vocabulary are

* `Work.EQ.Ladf.wsec_tails` — on a neighbourhood of the witness `u₀` **both tails at depth `M`**
  of the section chains are the germs (the "principal descent" through the middle window);
* `Work.EQ.Ladf.wsec_words` — on an open set accumulating at `u₀` (a *one-sided* sector, when `u₀`
  lies on the cut locus of a middle radicand) the depth-`M` words of the section chains are the
  words of the witness (local constancy of the branch letters off the cut loci).
-/

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

/-- An analytic local section of `⁰H` at `u₀` on the ball of radius `ρ`. -/
def IsSectAt (a : ℝ) (h : ℂ → ℂ) (g : ℂ → ChainData) (u₀ : ℂ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ g u₀ ∈ H0 a h ∧
    (∀ u ∈ Metric.ball u₀ ρ, g u ∈ H0 a h ∧ (g u).2.1 = u) ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (g u).1 n) (Metric.ball u₀ ρ)) ∧
    AnalyticOnNhd ℂ (fun u => (g u).2.2) (Metric.ball u₀ ρ)

/-- On a section with constant value `c`, the unstable parameter is `c / u`. -/
theorem IsSectAt.psi2 {a : ℝ} {h : ℂ → ℂ} {g : ℂ → ChainData} {u₀ : ℂ} {ρ : ℝ} {c : ℂ}
    (hg : IsSectAt a h g u₀ ρ) (hval : ∀ u ∈ Metric.ball u₀ ρ, (g u).2.1 * (g u).2.2 = c)
    {u : ℂ} (hu : u ∈ Metric.ball u₀ ρ) (h0 : u ≠ 0) : (g u).2.2 = c / u := by
  have h1 : (g u).2.1 = u := (hg.2.2.1 u hu).2
  have h2 : u * (g u).2.2 = c := by
    have := hval u hu
    rwa [h1] at this
  exact (eq_div_iff h0).mpr (by rw [mul_comm]; exact h2)

end Work.EQ.Ladf

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology

/-- The forward tail of the candidate chain is the stable germ from its reading depth on. -/
theorem candChain_fwd_tail {a : ℝ} {h : ℂ → ℂ} {f b : List Bool} {M : ℕ} (hf : f.length = M)
    (c u : ℂ) {n : ℕ} (hn : M ≤ n) :
    (candChain a h f [] b M c u).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * u) := by
  rw [candChain_fst_apply]
  rw [ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]
  by_cases hc : n ≤ M
  · rw [ite_eq_left hc, List.drop_eq_nil_of_le (by omega)]
    rfl
  · rw [ite_eq_right hc, zpow_natCast]

/-- The backward tail of the candidate chain is the unstable germ strictly beyond its reading
depth. -/
theorem candChain_bwd_tail {a : ℝ} {h : ℂ → ℂ} {f b : List Bool} {M : ℕ}
    (c u : ℂ) {n : ℕ} (hn : M < n) :
    (candChain a h f [] b M c u).1 (-(n : ℤ)) =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (c / u)) := by
  rw [candChain_fst_apply, ite_eq_right (by omega : ¬ ((0:ℤ) ≤ -(n:ℤ)))]
  rw [show (-(-(n:ℤ))).toNat = n by rw [neg_neg, Int.toNat_natCast]]
  rw [ite_eq_right (by omega : ¬ (n ≤ M)), zpow_natCast]
  simp only [List.drop_nil, fan_nil, ugermC]

end Work.EQ.Ladf

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

/-- **The germ steps.** Near `0`, the principal branches invert the germ steps in all four
combinations (stable/unstable germ, forward/backward step), for an arbitrary stable germ. -/
theorem wsec_germ_step {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
        invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u) ∧
      (∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
        fwdC a (germC a h u) = germC a h ((eqLam a : ℂ) * u)) ∧
      (∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
        fwdC a (ugermC a h u) = ugermC a h (u / (eqLam a : ℂ))) ∧
      (∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
        invBranch a true (ugermC a h u) = ugermC a h ((eqLam a : ℂ) * u)) := by
  obtain ⟨-, -, -, ⟨δ₀, hδ₀, hstep⟩⟩ := germC_leaf ha0 ha1 hh
  obtain ⟨δ₁, hδ₁, hfwd⟩ := fwdC_germC_noGamma ha0 ha1 hh
  obtain ⟨δ₂, hδ₂, hinvU⟩ := invBranch_ugermC_noGamma ha0 ha1 hh
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlne : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hl0)
  refine ⟨min (min (eqLam a * δ₀) δ₁) δ₂, by positivity, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hu' : ‖u‖ < min (min (eqLam a * δ₀) δ₁) δ₂ := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hle : min (min (eqLam a * δ₀) δ₁) δ₂ ≤ eqLam a * δ₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hlt : ‖u‖ < δ₀ := by
      have h1 : ‖u‖ < eqLam a * δ₀ := lt_of_lt_of_le hu' hle
      nlinarith [h1, hl0, hl1, hδ₀, norm_nonneg u]
    exact hstep u (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
  · intro u hu
    have hu' : ‖u‖ < min (min (eqLam a * δ₀) δ₁) δ₂ := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hle : min (min (eqLam a * δ₀) δ₁) δ₂ ≤ δ₁ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    exact hfwd u (by simpa [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hu' hle)
  · intro u hu
    have hu' : ‖u‖ < min (min (eqLam a * δ₀) δ₁) δ₂ := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hle : min (min (eqLam a * δ₀) δ₁) δ₂ ≤ eqLam a * δ₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hlt : ‖u / (eqLam a : ℂ)‖ < δ₀ := by
      have h1 : ‖u‖ < eqLam a * δ₀ := lt_of_lt_of_le hu' hle
      rw [norm_div, Complex.norm_of_nonneg (le_of_lt hl0)]
      rw [div_lt_iff₀ hl0]
      linarith
    have h1 := hstep (u / (eqLam a : ℂ))
      (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
    have hmul : (eqLam a : ℂ) * (u / (eqLam a : ℂ)) = u := mul_div_cancel₀ u hlne
    rw [hmul] at h1
    have hconj : invBranch a true (germC a h u) = eqMirror (fwdC a (ugermC a h u)) := by
      have := invBranch_true_eqMirror_fwdC (a := a) (germC a h u)
      simpa [ugermC, eqMirror_eqMirror] using this
    rw [hconj] at h1
    have h2 := congrArg eqMirror h1
    simpa [ugermC, eqMirror_eqMirror] using h2
  · intro u hu
    have hu' : ‖u‖ < min (min (eqLam a * δ₀) δ₁) δ₂ := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hle : min (min (eqLam a * δ₀) δ₁) δ₂ ≤ δ₂ := min_le_right _ _
    exact hinvU u (by simpa [Metric.mem_ball, dist_zero_right] using lt_of_lt_of_le hu' hle)

end Work.EQ.Ladf
