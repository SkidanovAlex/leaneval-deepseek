import Mathlib
import Submission.Work.Param.CriticalKit
import Submission.Work.Param.extend_step

namespace Work.Param.CriticalKit

open Filter Topology
open scoped Topology

noncomputable section

/-- **Values of a local Koenigs solution lie in the basin of `0`.**  If `‖l‖ < 1` and `ψ` is a
normalized local solution of `Q l (ψ w) = ψ (l * w)` on `Metric.ball 0 r` (`Good l r ψ`), then the
`Q l`-orbit of `ψ w` converges to `0` for every `w` in that ball: indeed the functional equation
gives `(Q l)^[n] (ψ w) = ψ (l ^ n * w)`, and `l ^ n * w → 0` while `ψ` is continuous at `0` with
`ψ 0 = 0`. -/
theorem values_mem_basin_of_good (l : ℂ) (hl : ‖l‖ < 1) {r : ℝ} {ψ : ℂ → ℂ}
    (h : Good l r ψ) : ∀ w ∈ Metric.ball 0 r, Basin l (ψ w) := by
  obtain ⟨hr, hdiff, hψ0, _hψd, heq⟩ := h
  intro w hw
  have hwn : ‖w‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hw
  -- the whole orbit of `w` under multiplication by `l` stays in the disc
  have hmem_all : ∀ n : ℕ, l ^ n * w ∈ Metric.ball 0 r := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖l ^ n * w‖ = ‖l ^ n‖ * ‖w‖ := norm_mul _ _
      _ = ‖l‖ ^ n * ‖w‖ := by rw [norm_pow]
      _ ≤ 1 * ‖w‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
          exact pow_le_one₀ (norm_nonneg l) (le_of_lt hl)
      _ = ‖w‖ := one_mul _
      _ < r := hwn
  have hiter : ∀ n : ℕ, (Q l)^[n] (ψ w) = ψ (l ^ n * w) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, heq (l ^ n * w) (hmem_all n)]
      simp only [pow_succ]
      ring
  rw [Basin]
  have hcont : ContinuousAt ψ 0 :=
    hdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
  have htend : Tendsto (fun n : ℕ => ψ (l ^ n * w)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ψ (l ^ n * w)) atTop (nhds (ψ 0)) := by
      apply hcont.tendsto.comp
      have h2 : Tendsto (fun n : ℕ => l ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hl
      simpa using h2.mul tendsto_const_nhds
    rwa [hψ0] at h1
  rw [show (fun n : ℕ => (Q l)^[n] (ψ w)) = (fun n : ℕ => ψ (l ^ n * w)) from
    funext hiter]
  exact htend

/-- **The critical value `-l²/4` is not attained by a local Koenigs solution** when the critical
point `-l/2` is not in the basin of `0`.  Indeed `Q l (-(l/2)) = -(l^2)/4`, and if `ψ w = -(l^2)/4`
for some `w` in the disc then `Q l (-(l/2))` lies in the basin (values of `ψ` do); backward
invariance of the basin (`basin_of_basin_Q`) then puts `-l/2` in the basin. -/
theorem good_critical_value_ne (l : ℂ) (hl : ‖l‖ < 1) {r : ℝ} {ψ : ℂ → ℂ} (h : Good l r ψ)
    (hnot : ¬ Basin l (-(l / 2))) : ∀ w ∈ Metric.ball 0 r, ψ w ≠ -(l ^ 2) / 4 := by
  intro w hw hval
  refine hnot ?_
  have hb : Basin l (ψ w) := values_mem_basin_of_good l hl h w hw
  rw [hval] at hb
  have hQ : Q l (-(l / 2)) = -(l ^ 2) / 4 := by simp only [Q]; ring
  rw [← hQ] at hb
  exact basin_of_basin_Q l hb

/-- **Unlimited extension of a local Koenigs solution when the critical orbit fails to converge.**
Let `0 < ‖l‖ < 1`, let `ψ` be a normalized local solution of the Koenigs equation on
`Metric.ball 0 R` (`Good l R ψ`), and suppose the critical point `-(l/2)` is *not* in the basin of
`0`.  Then the disc of definition can be enlarged indefinitely: for every `n` there is a normalized
local solution on `Metric.ball 0 (R / ‖l‖ ^ n)`.

Proof.  By induction on `n`.  At stage `n` one has `Good l (R / ‖l‖ ^ n) ψ`; the critical value
`-(l ^ 2) / 4` is not attained on the ball, because `Q l (-(l/2)) = -(l ^ 2)/4`, values of a
solution lie in the basin (`(Q l)^[k] (ψ w) = ψ (l ^ k * w) → ψ 0 = 0`, using `‖l‖ < 1`), and the
basin is backward invariant (`basin_of_basin_Q`); attaining it would give
`Basin l (-(l/2))`, contradicting `hnot`.  Hence `Work.Param.extend_step` produces a normalized
solution on the disc of radius `(R / ‖l‖ ^ n) / ‖l‖ = R / ‖l‖ ^ (n+1)`.

NOTE: the "values lie in the basin" fact is proved *inside* this lemma (do not wait for other
files); `Submission.Work.Param.CriticalKit` and `Submission.Work.Param.extend_step` are the only
imports needed. -/
theorem exists_good_iterate (l : ℂ) (hl : ‖l‖ < 1) (hl0 : l ≠ 0) {R : ℝ} (hR : 0 < R)
    {ψ : ℂ → ℂ} (hψ : Good l R ψ) (hnot : ¬ Basin l (-(l / 2))) :
    ∀ n : ℕ, ∃ φ : ℂ → ℂ, Good l (R / ‖l‖ ^ n) φ := by
  have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  intro n
  induction n with
  | zero => exact ⟨ψ, by simpa using hψ⟩
  | succ n ih =>
    obtain ⟨φ, hφ⟩ := ih
    have hv : ∀ w ∈ Metric.ball 0 (R / ‖l‖ ^ n), φ w ≠ -(l ^ 2) / 4 :=
      good_critical_value_ne l hl hφ hnot
    obtain ⟨φ', hd', h0', hd1', heq', _⟩ :=
      extend_step hl hl0 hφ.1 hφ.2.1 hφ.2.2.1 hφ.2.2.2.1 hφ.2.2.2.2 hv
    have hpow : R / ‖l‖ ^ n / ‖l‖ = R / ‖l‖ ^ (n + 1) := by
      rw [div_div, ← pow_succ]
    have hgood : Good l (R / ‖l‖ ^ n / ‖l‖) φ' :=
      ⟨div_pos hφ.1 hlpos, hd', h0', hd1', heq'⟩
    rw [hpow] at hgood
    exact ⟨φ', hgood⟩

end

end Work.Param.CriticalKit
