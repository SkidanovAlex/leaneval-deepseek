import Mathlib
import Submission.Work.KMTContract.Defs
import Submission.Work.KMTContract.kernel_l1_of_decay
import Submission.Work.KMTContract.bound_of_memLp_count
import Submission.Work.KMTContract.tendsto_sum_Icc_atTop

namespace Work.KMTContract

open MeasureTheory Filter Finset
open scoped NNReal ENNReal
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

noncomputable section

/-- **The truncated Ionescu--Wainger projection is the partial sum of the kernel against `f`.**
`truncZ K f` vanishes off `[-K,K]`, so each summand `iwKernel … j * f (n - j)` of the defining
series is killed by the truncation as soon as `|n - j| > K`, i.e. as soon as
`j ∉ Icc (n - K) (n + K)`; the series is therefore the finite sum over that interval. -/
theorem kmtProj_truncZ_eq_sumIcc (ρ : ℝ) (l : ℕ) (k : ℤ) (K : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    kmtProj ρ l k (truncZ K f) n
      = ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)),
          iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j
            * f (n - j) := by
  have hiff : ∀ j : ℤ,
      |n - j| ≤ (K : ℤ) ↔ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)) := by
    intro j
    rw [Finset.mem_Icc, abs_le]
    omega
  rw [kmtProj_apply]
  have hzero : ∀ b : ℤ, b ∉ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)) →
      iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) b
        * truncZ K f (n - b) = 0 := by
    intro b hb
    rw [truncZ_of_gt (K := K) (f := f) (x := n - b) ?_, mul_zero]
    by_contra h
    exact hb ((hiff b).mp (le_of_not_gt h))
  rw [tsum_eq_sum (s := Finset.Icc (n - (K : ℤ)) (n + (K : ℤ))) hzero]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [truncZ_of_le (K := K) (f := f) (x := n - b) ((hiff b).mpr hb)]

/-! ## The target -/

/-- **Pointwise convergence of the truncated Ionescu--Wainger projections.**
If the IW kernel decays like `j^{-2}` (the target `kmtKernel_decay`, taken here as a hypothesis so
that the two can be proved independently), then for every `f ∈ ℓ^p(ℤ)` with `1 < p` the
truncations `truncZ K f = f · 1_{[-K,K]}` give pointwise convergence
`kmtProj ρ l k (truncZ K f) n → kmtProj ρ l k f n`.

The point of the hypothesis: for `f ∈ ℓ^p` the family `j ↦ kernel j * f (n - j)` is absolutely
summable — by Hölder with the kernel in `ℓ^{p'}` (`p' = p/(p-1)`), which the `j^{-2}` decay gives
for every `p' > 1/2` — so the series defining `kmtProj ρ l k f n` converges, and the truncations
are its partial sums over the increasing sets `{j : |n - j| ≤ K}`. (Without *some* decay of the
kernel the statement is false: for `f ≡ 1` the truncations converge to the value of the symbol at
`0`, while the non-summable `tsum` is junk.) -/
theorem kmtProj_tendsto_truncZ (ρ : ℝ) (l : ℕ) (k : ℤ)
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖
        ≤ C / (1 + |(j : ℝ)|) ^ 2)
    {p : ENNReal} (hp : 1 < p) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) (n : ℤ) :
    Filter.Tendsto (fun K : ℕ => Work.KMTContract.kmtProj ρ l k (Work.KMTContract.truncZ K f) n)
      Filter.atTop (nhds (Work.KMTContract.kmtProj ρ l k f n)) := by
  obtain ⟨C, _hC, hdec⟩ := hdecay
  -- the kernel is in `ℓ¹`
  have hk : Summable (fun j : ℤ => ‖iwKernel
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j‖) :=
    kernel_l1_of_decay hdec
  -- `f` is bounded
  obtain ⟨M, hM⟩ := bound_of_memLp_count hp hf
  -- hence the family `j ↦ kernel j * f (n - j)` is absolutely summable
  have hg : Summable (fun j : ℤ => iwKernel
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j * f (n - j)) := by
    refine Summable.of_norm_bounded (hk.mul_left (M : ℝ)) (fun j => ?_)
    rw [norm_mul]
    calc ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j‖
            * ‖f (n - j)‖
        ≤ ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j‖ * (M : ℝ) :=
          mul_le_mul_of_nonneg_left (hM (n - j)) (norm_nonneg _)
      _ = (M : ℝ) * ‖iwKernel
            (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j‖ := mul_comm _ _
  -- the truncated projections are the partial sums over the expanding intervals
  have hsum := tendsto_sum_Icc_atTop hg n
  have h1 : (fun K : ℕ => kmtProj ρ l k (truncZ K f) n)
      = fun K : ℕ => ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)),
          iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j
            * f (n - j) :=
    funext fun K => kmtProj_truncZ_eq_sumIcc ρ l k K f n
  rw [h1, kmtProj_apply]
  exact hsum

end

end Work.KMTContract
