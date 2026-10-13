/-
# `FTS/PhiStar/Honesty/NodeAux2` — continuity, pointwise bound and decay of the modal solution

Second auxiliary module for `Honesty/bslSolExists_moment_of_node_hyp`; it uses the clean uniform
tail estimate `NodeAux.psiTrunc_tail_uniform` to reprove, for the modal solution
`ModalSol.Psi α F`,

* `tendstoUniformlyOn_psiTrunc_box` — uniform convergence of the partial sums on a box of the
  open quadrant (the version in `FTS/H2/ModalSol/Basic.lean` rests on the statement-only
  `psiTrunc_tail`);
* `continuousOn_uncurry_Psi_mod` — joint continuity on the open quadrant;
* `Psi_bound_mod` and `Psi_tendsto_atTop_zero_mod` — the `z^{-1/2}` bound on a closed angular
  subinterval and the pointwise decay at `z → ∞`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.NodeAux
import Submission.Work.FTS.H2.ModalSol.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.NodeAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-- **Uniform convergence of the partial sums on a rectangular box inside the quadrant.** -/
theorem tendstoUniformlyOn_psiTrunc_box {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c < d) (hd : d < π / 2) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => psiTrunc α F N p.1 p.2)
      (fun p : ℝ × ℝ => Psis α F p.1 p.2) atTop (Set.Icc a b ×ˢ Set.Icc c d) := by
  obtain ⟨K, hK0, b, hbnn, hbT, htail⟩ := psiTrunc_tail_uniform hα hα1 hsm hL2 hcd hc0 hd
  have haK : 0 < K * a ^ (-(1 / 2) : ℝ) := mul_pos hK0 (Real.rpow_pos_of_pos ha _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε' : 0 < ε / (K * a ^ (-(1 / 2) : ℝ)) := by positivity
  have hev : ∀ᶠ N in Filter.atTop, b N < ε / (K * a ^ (-(1 / 2) : ℝ)) :=
    hbT.eventually (eventually_lt_nhds hε')
  filter_upwards [hev] with N hN
  intro p hp
  have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
  have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) :=
    ⟨lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hlim := Work.FTS.H2.ModalSolR.psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 hp1 hp2
  have hdiff : Tendsto (fun M : ℕ => |psiTrunc α F N p.1 p.2 - psiTrunc α F M p.1 p.2|)
      Filter.atTop (nhds |psiTrunc α F N p.1 p.2 - Psis α F p.1 p.2|) :=
    (tendsto_const_nhds.sub hlim).abs
  have hbd : Tendsto (fun M : ℕ => K * a ^ (-(1 / 2) : ℝ) * (b N + b M)) Filter.atTop
      (nhds (K * a ^ (-(1 / 2) : ℝ) * (b N + 0))) :=
    (tendsto_const_nhds.add hbT).const_mul _
  have hstep : ∀ M : ℕ, |psiTrunc α F N p.1 p.2 - psiTrunc α F M p.1 p.2|
      ≤ K * a ^ (-(1 / 2) : ℝ) * (b N + b M) := by
    intro M
    have h := htail N M p.1 p.2 hp1 hp.2
    have hp1a : p.1 ^ (-(1 / 2) : ℝ) ≤ a ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)
    calc |psiTrunc α F N p.1 p.2 - psiTrunc α F M p.1 p.2|
        ≤ K * p.1 ^ (-(1 / 2) : ℝ) * (b N + b M) := h
      _ ≤ K * a ^ (-(1 / 2) : ℝ) * (b N + b M) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hbnn N, hbnn M])
          exact mul_le_mul_of_nonneg_left hp1a hK0.le
  have hle : |psiTrunc α F N p.1 p.2 - Psis α F p.1 p.2| ≤ K * a ^ (-(1 / 2) : ℝ) * b N := by
    have h0 := le_of_tendsto_of_tendsto' hdiff hbd hstep
    simpa using h0
  have h2 : K * a ^ (-(1 / 2) : ℝ) * b N < ε := by
    rw [lt_div_iff₀ haK] at hN
    calc K * a ^ (-(1 / 2) : ℝ) * b N = b N * (K * a ^ (-(1 / 2) : ℝ)) := by ring
      _ < ε := hN
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt hle h2

/-- **The modal solution is continuous on the open quadrant** (clean reproof). -/
theorem continuousOn_uncurry_Psi_mod (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0) :
    ContinuousOn (Function.uncurry (Psis α F)) Q0 := by
  refine continuousOn_of_forall_continuousAt (fun p hp => ?_)
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  set ε : ℝ := min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεz : ε ≤ p.1 / 2 := min_le_left _ _
  have hεθ : ε ≤ p.2 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεπ : ε ≤ (π / 2 - p.2) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hbox : Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε) ⊆ Q0 := by
    intro q hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [hq.1.1, hεz, hz0], by linarith [hq.2.1, hεθ, hθ0],
        by linarith [hq.2.2, hεπ, hθ1]⟩
  have hunif := tendstoUniformlyOn_psiTrunc_box hα hα1 horth hsm hL2
    (a := p.1 - ε) (b := p.1 + ε) (c := p.2 - ε) (d := p.2 + ε)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hcont : ContinuousOn (Function.uncurry (Psis α F))
      (Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε)) :=
    hunif.continuousOn (Filter.Eventually.of_forall (fun N =>
      (Work.FTS.H2.ModalSolR.continuousOn_uncurry_psiTrunc α hα hα1 hsm hL2 N).mono
        hbox)).frequently
  have hnb : Set.Ioo (p.1 - ε) (p.1 + ε) ×ˢ Set.Ioo (p.2 - ε) (p.2 + ε) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hbox_nhds : Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε) ∈ 𝓝 p :=
    Filter.mem_of_superset hnb (fun q hq =>
      ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩)
  exact hcont.continuousAt hbox_nhds

/-- **The modal solution is bounded by `z^{-1/2}` on a closed angular subinterval**, with a
constant coming from the uniform tail estimate and the vanishing of the `m = 0` mode. -/
theorem Psi_bound_mod (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < π / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      |Psis α F z θ| ≤ C * z ^ (-(1 / 2) : ℝ) := by
  have hcd : δ < π / 2 - δ := by linarith [Real.pi_pos]
  have hd : π / 2 - δ < π / 2 := by linarith
  obtain ⟨K, hK0, b, hbnn, hbT, htail⟩ :=
    psiTrunc_tail_uniform hα hα1 hsm hL2 hcd hδ0 hd
  have hpsi0 : ∀ z θ : ℝ, psiTrunc α F 0 z θ = 0 := by
    intro z θ
    rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.range_one, Finset.sum_singleton,
      Work.FTS.H2.ModalSol.acoeff_zero_of_orth horth α z]
    ring
  refine ⟨max 1 (K * b 0), lt_max_of_lt_left one_pos, fun z hz θ hθ => ?_⟩
  have hθ0 : 0 < θ := lt_of_lt_of_le hδ0 hθ.1
  have hθ1 : θ < π / 2 := lt_of_le_of_lt hθ.2 (by linarith [hδ0])
  have hlim := Work.FTS.H2.ModalSolR.psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 hz
    (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)
  have hdiff : Tendsto (fun N : ℕ => |psiTrunc α F 0 z θ - psiTrunc α F N z θ|) Filter.atTop
      (nhds |psiTrunc α F 0 z θ - Psis α F z θ|) := (tendsto_const_nhds.sub hlim).abs
  have hbd : Tendsto (fun N : ℕ => K * z ^ (-(1 / 2) : ℝ) * (b 0 + b N)) Filter.atTop
      (nhds (K * z ^ (-(1 / 2) : ℝ) * (b 0 + 0))) :=
    (tendsto_const_nhds.add hbT).const_mul _
  have hle : |psiTrunc α F 0 z θ - Psis α F z θ| ≤ K * z ^ (-(1 / 2) : ℝ) * b 0 := by
    have h := le_of_tendsto_of_tendsto' hdiff hbd (fun N => htail 0 N z θ hz hθ)
    simpa using h
  rw [hpsi0, zero_sub, abs_neg] at hle
  refine le_trans hle ?_
  calc K * z ^ (-(1 / 2) : ℝ) * b 0 = (K * b 0) * z ^ (-(1 / 2) : ℝ) := by ring
    _ ≤ max 1 (K * b 0) * z ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hz.le _)

/-- **The modal solution decays at `z → ∞` in every direction of `Iθ`** (clean reproof). -/
theorem Psi_tendsto_atTop_zero_mod (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0) :
    ∀ θ ∈ Iθ, Tendsto (fun z => Psis α F z θ) atTop (nhds 0) := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | rfl
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | rfl
    · set δ : ℝ := min θ (π / 2 - θ) / 2 with hδdef
      have hδ0 : 0 < δ := div_pos (lt_min hθ0 (sub_pos.mpr hθ1)) (by norm_num)
      have hδ4 : δ < π / 4 := by
        have h2 : δ ≤ θ / 2 := by
          rw [hδdef]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith
      have hmem : θ ∈ Set.Icc δ (π / 2 - δ) := by
        refine ⟨?_, ?_⟩
        · rw [hδdef]
          exact le_trans (div_le_self (le_of_lt (lt_min hθ0 (sub_pos.mpr hθ1)))
            (by norm_num : (1 : ℝ) ≤ 2)) (min_le_left _ _)
        · rw [hδdef]
          have h2 : min θ (π / 2 - θ) ≤ π / 2 - θ := min_le_right _ _
          linarith
      obtain ⟨C, hC0, hbnd⟩ := Psi_bound_mod α hα hα1 horth hsm hL2 hδ0 hδ4
      have h1 : Tendsto (fun z : ℝ => C * z ^ (-(1 / 2) : ℝ)) atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) ?_ h1
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      rw [Real.norm_eq_abs]
      exact hbnd z hz θ hmem
    · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall
        (fun z => (Work.FTS.H2.ModalSol.Psi_apply_pi_half α F z).symm))
  · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall
      (fun z => (Work.FTS.H2.ModalSol.Psi_apply_zero α F z).symm))

end Work.FTS.PhiStar.Honesty.NodeAux
