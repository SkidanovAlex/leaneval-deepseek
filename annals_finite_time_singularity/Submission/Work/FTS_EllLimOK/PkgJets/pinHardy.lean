import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS_EllLimOK.PkgJets.pinMid
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.one_le_mul_w
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.LimitFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-- `lam m ≥ 0`. -/
theorem lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg' m

/-- The weighted coefficient sequence, in the exact shape of the two coefficient bounds. -/
def uq (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) (k : ℕ) : ℝ :=
  Work.EllipticEst.ModalSolution.eNorm k * (Work.FTS.PhiStar.Series.acoeff α k F z) ^ 2
    + Work.FTS.PhiStar.Gegenbauer.lam k * Work.EllipticEst.ModalSolution.eNorm k
      * (Work.FTS.PhiStar.Series.acoeff α k F z) ^ 2

/-- `uq` is nonnegative. -/
theorem uq_nonneg (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) (k : ℕ) : 0 ≤ uq α F z k := by
  rw [uq]
  exact add_nonneg
    (mul_nonneg (eNorm_nonneg k) (sq_nonneg _))
    (mul_nonneg (mul_nonneg (lam_nonneg k) (eNorm_nonneg k)) (sq_nonneg _))

/-- **The partial sums of `uq` are bounded by `2 D z⁻¹`** whenever `D` bounds both coefficient
sums in the shape of `coeffSq_le`. -/
theorem sum_uq_le {α D z : ℝ} {F : ℝ → ℝ → ℝ}
    (hD : ∀ z : ℝ, 0 < z → ∀ N : ℕ,
      ((∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) ≤ D * z ^ (-(1 : ℝ))) ∧
      ((∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) ≤ D * z ^ (-(1 : ℝ))))
    (hz : 0 < z) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), uq α F z k) ≤ 2 * D * z ^ (-(1 : ℝ)) := by
  have hsplit : (∑ k ∈ Finset.range (N + 1), uq α F z k)
      = (∑ k ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm k
          * (Work.FTS.PhiStar.Series.acoeff α k F z) ^ 2)
        + (∑ k ∈ Finset.range (N + 1), Work.FTS.PhiStar.Gegenbauer.lam k
          * Work.EllipticEst.ModalSolution.eNorm k
          * (Work.FTS.PhiStar.Series.acoeff α k F z) ^ 2) :=
    Finset.sum_add_distrib
  rw [hsplit]
  linarith [(hD z hz N).1, (hD z hz N).2]

/-- The weighted coefficient sequence is summable. -/
theorem summable_uq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : 0 < z) : Summable (uq α F z) := by
  obtain ⟨D, hD0, hD⟩ := coeffSq_le α hα hα1 horth hsm hL2
  refine summable_of_sum_range_le (c := 2 * D * z ^ (-(1 : ℝ)))
    (fun k => uq_nonneg α F z k) (fun n => ?_)
  rcases n with _ | m
  · rw [Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (by norm_num) hD0) (Real.rpow_nonneg hz.le _)
  · exact sum_uq_le (F := F) hD hz m

/-- The tail of the `uq`-series tends to `0`. -/
theorem uq_tail_tendsto (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun M : ℕ => (∑' k, uq α F z k) - ∑ k ∈ Finset.range (M + 1),
      uq α F z k) Filter.atTop (nhds 0) := by
  have hu := summable_uq α hα hα1 horth hsm hL2 hz
  have hU : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, uq α F z k)
      Filter.atTop (nhds (∑' k, uq α F z k)) := hu.hasSum.tendsto_sum_nat
  have h : Filter.Tendsto (fun n : ℕ => (∑' k, uq α F z k)
      - ∑ k ∈ Finset.range n, uq α F z k) Filter.atTop
      (nhds ((∑' k, uq α F z k) - (∑' k, uq α F z k))) :=
    tendsto_const_nhds.sub hU
  have h' : Filter.Tendsto (fun n : ℕ => (∑' k, uq α F z k)
      - ∑ k ∈ Finset.range n, uq α F z k) Filter.atTop (nhds 0) := by simpa using h
  exact h'.comp (Filter.tendsto_add_atTop_nat 1)

/-- The two coefficient sums of the tail bound, expanded in the shape of `uq`. -/
theorem tail_sum_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) (M N : ℕ) :
    (∑ m ∈ Finset.Icc (M + 1) N,
        (∫ θ' in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2
          * Real.cos θ') * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
      + (∑ m ∈ Finset.Icc (M + 1) N, Work.FTS.PhiStar.Gegenbauer.lam m
          * (∫ θ' in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2
            * Real.cos θ')
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
      = ∑ m ∈ Finset.Icc (M + 1) N, uq α F z m := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => rfl)

/-- **Uniform Cauchy property of the partial sums on a closed angular subinterval.** -/
theorem psiTrunc_cauchyUniform (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {c d : ℝ} (hcd : c < d) (hc0 : 0 < c) (hd : d < π / 2)
    {z : ℝ} (hz : 0 < z) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ m n : ℕ, N₀ ≤ m → N₀ ≤ n → ∀ θ ∈ Set.Icc c d,
      |Work.FTS.PhiStar.Series.psiTrunc α F n z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F m z θ| < ε := by
  obtain ⟨K, hK0, hK⟩ := psiTruncTailBound (F := F) α hcd hc0 hd
  have hu_sum : Summable (uq α F z) := summable_uq α hα hα1 horth hsm hL2 hz
  have hu_nn : ∀ k : ℕ, 0 ≤ uq α F z k := uq_nonneg α F z
  have htail := uq_tail_tendsto α hα hα1 horth hsm hL2 hz
  have hkey : ∀ M N : ℕ, M ≤ N → ∀ θ ∈ Set.Icc c d,
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
      ≤ K * Real.sqrt ((∑' k, uq α F z k) - ∑ k ∈ Finset.range (M + 1), uq α F z k) := by
    intro M N hMN θ hθ
    refine le_trans (hK z θ M N hθ hMN) ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hK0.le
    rw [tail_sum_eq]
    have hIcc : Finset.Icc (M + 1) N = Finset.range (N + 1) \ Finset.range (M + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range]
      omega
    rw [hIcc]
    have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) :=
      Finset.range_subset_range.mpr (Nat.succ_le_succ hMN)
    have hsd := Finset.sum_sdiff hsub (f := uq α F z)
    have hle : ∑ k ∈ Finset.range (N + 1), uq α F z k ≤ ∑' k, uq α F z k :=
      hu_sum.sum_le_tsum _ (fun i _ => hu_nn i)
    linarith [hsd, hle]
  intro ε hε
  have hδ : 0 < ε ^ 2 / (2 * (K ^ 2 + 1)) := by positivity
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (htail.eventually (eventually_lt_nhds hδ))
  have hKs : K ≤ Real.sqrt (2 * (K ^ 2 + 1)) := by
    rw [Real.le_sqrt hK0.le (by positivity)]
    nlinarith
  have hlim : ∀ M : ℕ, N₀ ≤ M →
      Real.sqrt ((∑' k, uq α F z k) - ∑ k ∈ Finset.range (M + 1), uq α F z k)
        < ε / K := by
    intro M hM
    have hnn : 0 ≤ (∑' k, uq α F z k) - ∑ k ∈ Finset.range (M + 1), uq α F z k :=
      sub_nonneg.mpr (hu_sum.sum_le_tsum _ (fun i _ => hu_nn i))
    refine lt_of_lt_of_le (Real.sqrt_lt_sqrt hnn (hN₀ M hM)) ?_
    rw [Real.sqrt_div (sq_nonneg ε), Real.sqrt_sq hε.le]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hK0]
    exact mul_le_mul_of_nonneg_left hKs hε.le
  refine ⟨N₀, fun m n hm hn θ hθ => ?_⟩
  rcases le_total m n with hmn | hnm
  · refine lt_of_le_of_lt (hkey m n hmn θ hθ) ?_
    have h1 := mul_lt_mul_of_pos_left (hlim m hm) hK0
    have h2 : K * (ε / K) = ε := by field_simp
    rw [h2] at h1
    exact h1
  · rw [abs_sub_comm]
    refine lt_of_le_of_lt (hkey n m hnm θ hθ) ?_
    have h1 := mul_lt_mul_of_pos_left (hlim n hn) hK0
    have h2 : K * (ε / K) = ε := by field_simp
    rw [h2] at h1
    exact h1

/-- The partial sums converge to `Psi`. -/
theorem psiTrunc_tendsto_Psi (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
      (nhds (Work.FTS.H2.ModalSol.Psi α F z θ)) := by
  obtain ⟨c, d, hcd, hc0, hθcd, hd⟩ :
      ∃ c d : ℝ, c < d ∧ 0 < c ∧ θ ∈ Set.Icc c d ∧ d < π / 2 :=
    ⟨θ / 2, (θ + π / 2) / 2, by linarith [Real.pi_pos], by linarith [hθ.1],
      ⟨le_of_lt (by linarith [hθ.1]), le_of_lt (by linarith [hθ.2, Real.pi_pos])⟩,
      by linarith [hθ.2, Real.pi_pos]⟩
  have hC : CauchySeq (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := psiTrunc_cauchyUniform α hα hα1 horth hsm hL2 hcd hc0 hd hz ε hε
    exact ⟨N₀, fun m hm n hn =>
      by simpa only [Real.dist_eq, abs_sub_comm] using hN₀ m n hm hn θ hθcd⟩
  exact Work.FTS.H2.ModalSol.Psi_tendsto_of_cauchy hC

/-- **Uniform-in-`N` bound on the partial sums** on a closed angular subinterval. -/
theorem psiTrunc_bound_on (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {c d : ℝ} (hcd : c < d) (hc0 : 0 < c) (hd : d < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Icc c d →
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ| ≤ C * z ^ (-(1 / 2) : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := psiTruncTailBound (F := F) α hcd hc0 hd
  obtain ⟨D, hD0, hD⟩ := coeffSq_le α hα hα1 horth hsm hL2
  have hA0 : ∀ z, Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := acoeff_zero_of_orth horth α
  have hsqrt0 : 0 ≤ Real.sqrt (2 * D) := Real.sqrt_nonneg _
  refine ⟨K * (Real.sqrt (2 * D) + 1), mul_pos hK0 (by linarith), fun N z θ hz hθ => ?_⟩
  have hpsi0 : Work.FTS.PhiStar.Series.psiTrunc α F 0 z θ = 0 := by
    rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.range_one, Finset.sum_singleton, hA0 z]
    ring
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [hpsi0, abs_zero]
    exact mul_nonneg (mul_nonneg hK0.le (by linarith)) (Real.rpow_nonneg hz.le _)
  · have h1 := hK z θ 0 N hθ (Nat.zero_le N)
    rw [hpsi0, sub_zero] at h1
    refine le_trans h1 ?_
    rw [tail_sum_eq]
    have hS : (∑ m ∈ Finset.Icc (0 + 1) N, uq α F z m) ≤ 2 * D * z ^ (-(1 : ℝ)) := by
      have hsub : Finset.Icc (0 + 1) N ⊆ Finset.range (N + 1) := by
        intro i hi
        simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
        omega
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => uq_nonneg α F z i)) (sum_uq_le (F := F) hD hz N)
    have hsqrtle : Real.sqrt (∑ m ∈ Finset.Icc (0 + 1) N, uq α F z m)
        ≤ Real.sqrt (2 * D * z ^ (-(1 : ℝ))) := Real.sqrt_le_sqrt hS
    refine le_trans (mul_le_mul_of_nonneg_left hsqrtle hK0.le) ?_
    rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * D)]
    rw [show Real.sqrt (z ^ (-(1 : ℝ))) = z ^ (-(1 / 2) : ℝ) from by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]; norm_num]
    have hnn : 0 ≤ K * z ^ (-(1 / 2) : ℝ) :=
      mul_nonneg hK0.le (Real.rpow_nonneg hz.le _)
    nlinarith [hnn, hsqrt0]

/-- **Continuity of the angular slices of the limit.** -/
theorem Psi_slice_continuous (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.FTS.H2.ModalSol.Psi α F z θ) (Set.Ioo 0 (π / 2)) := by
  intro θ hθ
  obtain ⟨c, d, hcd, hc0, hcθ, hθd, hd, hθcd⟩ :
      ∃ c d : ℝ, c < d ∧ 0 < c ∧ c < θ ∧ θ < d ∧ d < π / 2 ∧ θ ∈ Set.Icc c d :=
    ⟨θ / 2, (θ + π / 2) / 2, by linarith [Real.pi_pos], by linarith [hθ.1],
      by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos],
      ⟨le_of_lt (by linarith [hθ.1]), le_of_lt (by linarith [hθ.2, Real.pi_pos])⟩⟩
  have hcontN : ∀ N : ℕ, ContinuousOn (fun θ' : ℝ =>
      Work.FTS.PhiStar.Series.psiTrunc α F N z θ') (Set.Icc c d) := by
    intro N
    have hfin : (fun θ' : ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ')
        = fun θ' : ℝ => ∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.acoeff α m F z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ' := by
      funext θ'; rfl
    rw [hfin]
    exact continuousOn_finsetSum _ (fun m _ =>
      continuousOn_const.mul
        ((Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).comp_continuousOn
          continuousOn_id))
  have hunif : TendstoUniformlyOn
      (fun N : ℕ => fun θ' : ℝ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ')
      (fun θ' : ℝ => Work.FTS.H2.ModalSol.Psi α F z θ') Filter.atTop (Set.Icc c d) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := psiTrunc_cauchyUniform α hα hα1 horth hsm hL2 hcd hc0 hd hz
      (ε / 2) (by linarith)
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    intro θ' hθ'
    rw [Real.dist_eq]
    have hlim := psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 hz
      ⟨lt_of_lt_of_le hc0 hθ'.1, lt_of_le_of_lt hθ'.2 hd⟩
    have hbd : ∀ m : ℕ, N₀ ≤ m →
        |Work.FTS.PhiStar.Series.psiTrunc α F N z θ'
          - Work.FTS.PhiStar.Series.psiTrunc α F m z θ'| ≤ ε / 2 := by
      intro m hm
      have h := hN₀ N m hN hm θ' hθ'
      rw [abs_sub_comm] at h
      exact le_of_lt h
    have hfin : |Work.FTS.H2.ModalSol.Psi α F z θ'
        - Work.FTS.PhiStar.Series.psiTrunc α F N z θ'| ≤ ε / 2 := by
      rw [abs_sub_comm]
      exact le_of_tendsto ((tendsto_const_nhds.sub hlim).abs)
        (Filter.eventually_ge_atTop N₀ |>.mono hbd)
    linarith
  have hcont : ContinuousOn (fun θ' : ℝ => Work.FTS.H2.ModalSol.Psi α F z θ')
      (Set.Icc c d) :=
    hunif.continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hcontN))
  exact (hcont.continuousAt (Icc_mem_nhds hcθ hθd)).continuousWithinAt

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.pinHardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS_EllLimOK.PkgJets
end
end
