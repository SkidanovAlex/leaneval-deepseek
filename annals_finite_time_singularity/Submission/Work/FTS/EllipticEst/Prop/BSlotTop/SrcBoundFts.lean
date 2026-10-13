/-
Work module for the Elgindi finite-time singularity project.

# `BSlotTop/SrcBoundFts`: the source slot bound of the `ℋ^k` induction step

This is the clean-cone copy of `Work.FTS.EllipticEst.remov.TopCoreB.srcBound`
(`Submission/Work/FTS/EllipticEst/remov/TopCoreB/srcBound.lean`), which is the *only*
analytic input of the source estimate of the paper's §"General `ℋ^k` case`: the
`sin(2θ)^{2k-γ}`-weighted `k`-th angular derivative of the angular source

  `G = SrcG α F Ψ = F + α²·z²∂_z²Ψ + α(5+α)·D_zΨ`

is dominated by the `ℋ^k`-slots of `F`, the `ℋ^k`-slot of `A = z²∂_z²Ψ` and its level-`(k-1)`
slots, and the level-`(k-1)` slots of `∂_θ²(D_zΨ)`.

The proof has three ingredients, all available in the workspace:

* the **pointwise slot recursion** `remov.TopCoreB.slotRecAll`
  (`(∂_θ^mX)²σ^{2m-γ} ≤ C Σ_{t≤m}(D_θ^tX)²σ^{-γ}` on the open angular interval), applied to
  `F`, `A` and to `h := ∂_θ²(D_zΨ)` — for the last one to the order `k-2`, after the
  `pthIter_addT` identity `∂_θ^k(D_zΨ) = ∂_θ^{k-2}(∂_θ²(D_zΨ))` and the domination
  `σ^{2k-γ} ≤ σ^{2(k-2)-γ}`;
* the **identification of the `D_θ`-slots with the `ℋ^k`-integrand**
  (`Work.Spaces.sq_le_HkIntegrand_mixed` for the slots with `1 ≤ t`, and the radial slot
  `(D_z^0 X · w/σ^{η/2})²` combined with `σ^{-γ} ≤ σ^{-η}` for `t = 0`);
* **honesty** (`HkMem`) of the three data, from `EllWeakPos`, `HkMem_Dz_shift` and
  `HkMem_congr_Q0` (for `∂_θ²(D_zΨ) ↔ D_z(∂_θ²Ψ)`, which agree on the open quadrant by
  `Dz_pthIter_two_comm`).
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.CleanBase
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.SlotRec
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.SlotIntegrable
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.SrcBoundDefs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.TT.ESW.ChainAux
import Submission.Work.FTS.EllipticEst.TT.ESW.U_le_of_1d

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The reverse expansion without the `r = 0` term -/

/-- `(Finset.range m).erase 0 = Finset.Icc 1 (m - 1)` (for `m ≥ 1`). -/
theorem range_erase_zero (m : ℕ) : (Finset.range m).erase 0 = Finset.Icc 1 (m - 1) := by
  ext r
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
  omega

/-- **The reverse expansion with the vanishing `r = 0` coefficient dropped.**  For `m ≥ 1` the
exact expansion `D_θ^m f = Σ_{r ≤ m} dthCoef m r · ∂_θ^r f` has `dthCoef m 0 = 0`, so the
plain `m`-th derivative is dominated by `D_θ^m f` and the *orders `1, …, m-1`* only. -/
theorem revExp1 (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry f) (z, θ)) →
      |Real.sin (2 * θ)| ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ K * (|Work.Spaces.DthIter m f z θ|
          + ∑ r ∈ Finset.Icc 1 (m - 1),
              |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, one_pos, ?_⟩
    intro f z θ hf
    simp only [Nat.reduceSub, Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0),
      Finset.sum_empty, add_zero, pow_zero, one_mul, Work.Spaces.pthIter_zero,
      Work.Spaces.DthIter_zero]
    exact le_rfl
  · choose Kc hKcpos hKcbd using fun r =>
      Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound m r
    refine ⟨1 + ∑ r ∈ Finset.range (m + 1), Kc r, ?_, ?_⟩
    · have hnn : 0 ≤ ∑ r ∈ Finset.range (m + 1), Kc r :=
        Finset.sum_nonneg fun r _ => (hKcpos r).le
      linarith
    · intro f z θ hf
      have hKsum : ∀ r ∈ Finset.Icc 1 (m - 1),
          Kc r ≤ 1 + ∑ r ∈ Finset.range (m + 1), Kc r := by
        intro r hr
        have hmem : r ∈ Finset.range (m + 1) := by
          simp only [Finset.mem_range]
          have := Finset.mem_Icc.mp hr
          omega
        have := Finset.single_le_sum (f := Kc) (fun i _ => (hKcpos i).le) hmem
        linarith
      -- the exact expansion, split at the top term
      have hexp := Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local m f z θ hf
      have hself : Work.FTS.EllipticEst.remov.selfdth.dthCoef m m θ
          = Real.sin (2 * θ) ^ m :=
        congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_self m) θ
      have hzero : Work.FTS.EllipticEst.remov.selfdth.dthCoef m 0 θ = 0 := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [hj, Work.FTS.EllipticEst.remov.selfdth.dthCoef_succ_zero]
        rfl
      set Serr : ℝ := ∑ r ∈ Finset.Icc 1 (m - 1),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ
        with hSerr
      have hsumrange : (∑ r ∈ Finset.range m,
            Work.FTS.EllipticEst.remov.selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ)
          = Serr := by
        rw [hSerr, ← range_erase_zero m]
        have hmem : 0 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
        have h := Finset.sum_erase_add (Finset.range m)
          (fun r => Work.FTS.EllipticEst.remov.selfdth.dthCoef m r θ
            * Work.Spaces.pthIter r f z θ) hmem
        rw [hzero, zero_mul, add_zero] at h
        exact h.symm
      have hsplit : Real.sin (2 * θ) ^ m * Work.Spaces.pthIter m f z θ
          = Work.Spaces.DthIter m f z θ - Serr := by
        rw [hexp, Finset.sum_range_succ, hself, hsumrange]
        ring
      -- the tail bound
      have htail : |Serr| ≤ (1 + ∑ r ∈ Finset.range (m + 1), Kc r)
          * ∑ r ∈ Finset.Icc 1 (m - 1),
              |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ| := by
        have h1 : |Serr| ≤ ∑ r ∈ Finset.Icc 1 (m - 1),
            |Work.FTS.EllipticEst.remov.selfdth.dthCoef m r θ|
              * |Work.Spaces.pthIter r f z θ| := by
          rw [hSerr]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
          exact Finset.sum_congr rfl fun r _ => abs_mul _ _
        refine le_trans h1 ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun r hr => ?_
        have hc : |Work.FTS.EllipticEst.remov.selfdth.dthCoef m r θ|
            ≤ Kc r * |Real.sin (2 * θ)| ^ r := hKcbd r θ
        calc |Work.FTS.EllipticEst.remov.selfdth.dthCoef m r θ|
                * |Work.Spaces.pthIter r f z θ|
            ≤ (Kc r * |Real.sin (2 * θ)| ^ r) * |Work.Spaces.pthIter r f z θ| :=
              mul_le_mul_of_nonneg_right hc (abs_nonneg _)
          _ ≤ ((1 + ∑ r ∈ Finset.range (m + 1), Kc r) * |Real.sin (2 * θ)| ^ r)
                * |Work.Spaces.pthIter r f z θ| := by
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_right (hKsum r hr) (by positivity)
          _ = (1 + ∑ r ∈ Finset.range (m + 1), Kc r)
                * (|Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by ring
      calc |Real.sin (2 * θ)| ^ m * |Work.Spaces.pthIter m f z θ|
          = |Real.sin (2 * θ) ^ m * Work.Spaces.pthIter m f z θ| := by
            rw [abs_mul, abs_pow]
        _ = |Work.Spaces.DthIter m f z θ - Serr| := by rw [hsplit]
        _ ≤ |Work.Spaces.DthIter m f z θ| + |Serr| := by
            have h := abs_add_le (Work.Spaces.DthIter m f z θ) (-Serr)
            simpa [sub_eq_add_neg, abs_neg] using h
        _ ≤ |Work.Spaces.DthIter m f z θ|
              + (1 + ∑ r ∈ Finset.range (m + 1), Kc r)
                * ∑ r ∈ Finset.Icc 1 (m - 1),
                    |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ| :=
            add_le_add le_rfl htail
        _ ≤ (1 + ∑ r ∈ Finset.range (m + 1), Kc r)
              * (|Work.Spaces.DthIter m f z θ|
                + ∑ r ∈ Finset.Icc 1 (m - 1),
                    |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by
            have h1 : (1 : ℝ) ≤ 1 + ∑ r ∈ Finset.range (m + 1), Kc r := by
              have hnn : 0 ≤ ∑ r ∈ Finset.range (m + 1), Kc r :=
                Finset.sum_nonneg fun r _ => (hKcpos r).le
              linarith
            have hDle : |Work.Spaces.DthIter m f z θ|
                ≤ (1 + ∑ r ∈ Finset.range (m + 1), Kc r)
                  * |Work.Spaces.DthIter m f z θ| := by
              have h := mul_le_mul_of_nonneg_right h1
                (abs_nonneg (Work.Spaces.DthIter m f z θ))
              simpa using h
            rw [mul_add]
            exact add_le_add hDle le_rfl

/-! ## The slot recursion without the `t = 0` slot -/

/-- **The pointwise step of the slot recursion** (variant of
`remov.TopCoreB.slotRecStep` without the `t = 0` slot).  From `revExp1` and Cauchy–Schwarz for
the `m - 1` terms of the tail one gets, for `m ≥ 1`,

  `(∂_θ^mf)²σ^{2m-γ} ≤ 2K²m·((D_θ^mf)²σ^{-γ} + Σ_{1≤r≤m-1}(∂_θ^rf)²σ^{2r-γ})`. -/
theorem slotStep1 (γ : ℝ) (m : ℕ) (hm : 1 ≤ m) {K : ℝ} (hK : 0 < K)
    (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hrev : |Real.sin (2 * θ)| ^ m * |Work.Spaces.pthIter m f z θ|
      ≤ K * (|Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.Icc 1 (m - 1),
            |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|)) :
    (Work.Spaces.pthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - γ)
      ≤ 2 * K ^ 2 * (m : ℝ)
        * ((Work.Spaces.DthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
          + ∑ r ∈ Finset.Icc 1 (m - 1),
              (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ)) := by
  set s : ℝ := Real.sin (2 * θ) with hsdef
  have hs : 0 < s := Work.FTS.EllipticEst.remov.TopCoreB.sin_two_pos_of_Ioo hθ
  have hsabs : ∀ r : ℕ, |s| ^ r = s ^ r := fun r => by rw [abs_of_pos hs]
  set S : ℝ := ∑ r ∈ Finset.Icc 1 (m - 1), s ^ r * |Work.Spaces.pthIter r f z θ| with hSdef
  have hrev' : s ^ m * |Work.Spaces.pthIter m f z θ|
      ≤ K * (|Work.Spaces.DthIter m f z θ| + S) := by
    have h := hrev
    simp only [hsabs] at h
    rw [← hSdef] at h
    exact h
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (pow_nonneg hs.le r) (abs_nonneg _)
  have hstep1 : (s ^ m) ^ 2 * (Work.Spaces.pthIter m f z θ) ^ 2
      ≤ K ^ 2 * (|Work.Spaces.DthIter m f z θ| + S) ^ 2 := by
    have h := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ s ^ m * |Work.Spaces.pthIter m f z θ|) hrev' 2
    simp only [mul_pow, sq_abs] at h
    exact h
  have hBS : (|Work.Spaces.DthIter m f z θ| + S) ^ 2
      ≤ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2) := by
    nlinarith [sq_nonneg (|Work.Spaces.DthIter m f z θ| - S),
      sq_abs (Work.Spaces.DthIter m f z θ), abs_nonneg (Work.Spaces.DthIter m f z θ)]
  set Sig : ℝ := ∑ r ∈ Finset.Icc 1 (m - 1),
    (s ^ r) ^ 2 * (Work.Spaces.pthIter r f z θ) ^ 2 with hSigdef
  have hSig_nn : 0 ≤ Sig := by
    rw [hSigdef]; exact Finset.sum_nonneg fun r _ => by positivity
  have hcard : (((Finset.Icc 1 (m - 1)).card : ℕ) : ℝ) ≤ (m : ℝ) := by
    have h1 : (Finset.Icc 1 (m - 1)).card = m - 1 := by
      rw [Nat.card_Icc]; omega
    rw [h1]
    exact_mod_cast Nat.sub_le m 1
  have hCS : S ^ 2 ≤ (m : ℝ) * Sig := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 (m - 1))
      (f := fun r => s ^ r * |Work.Spaces.pthIter r f z θ|)
    have h2 : (∑ r ∈ Finset.Icc 1 (m - 1),
        (s ^ r * |Work.Spaces.pthIter r f z θ|) ^ 2) = Sig := by
      rw [hSigdef]
      exact Finset.sum_congr rfl fun r _ => by rw [mul_pow, sq_abs]
    rw [← hSdef, h2] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right hcard hSig_nn
  have hcore : (s ^ m) ^ 2 * (Work.Spaces.pthIter m f z θ) ^ 2
      ≤ 2 * K ^ 2 * (m : ℝ) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig) := by
    have h1 : K ^ 2 * (|Work.Spaces.DthIter m f z θ| + S) ^ 2
        ≤ K ^ 2 * (2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2)) :=
      mul_le_mul_of_nonneg_left hBS hK2
    have h2 : K ^ 2 * (2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2))
        ≤ 2 * K ^ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig) := by
      nlinarith [hCS, hK2]
    have h3 : 2 * K ^ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig)
        ≤ 2 * K ^ 2 * ((m : ℝ)
            * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig)) := by
      have hb : (Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig
          ≤ (m : ℝ) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig) := by
        nlinarith [sq_nonneg (Work.Spaces.DthIter m f z θ), hSig_nn, hm1]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    calc (s ^ m) ^ 2 * (Work.Spaces.pthIter m f z θ) ^ 2
        ≤ K ^ 2 * (|Work.Spaces.DthIter m f z θ| + S) ^ 2 := hstep1
      _ ≤ K ^ 2 * (2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + S ^ 2)) := h1
      _ ≤ 2 * K ^ 2 * ((Work.Spaces.DthIter m f z θ) ^ 2 + (m : ℝ) * Sig) := h2
      _ ≤ 2 * K ^ 2 * ((m : ℝ) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig)) := h3
      _ = 2 * K ^ 2 * (m : ℝ) * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig) := by ring
  have hpowL : s ^ (2 * (m : ℝ) - γ) = (s ^ m) ^ 2 * s ^ (-γ) := by
    have e1 : s ^ (2 * (m : ℝ)) = (s ^ m) ^ 2 := by
      have h1 : s ^ ((m : ℝ) * (2 : ℝ)) = (s ^ m) ^ (2 : ℝ) :=
        Real.rpow_natCast_mul (le_of_lt hs) m 2
      have h2 : (s ^ m) ^ (2 : ℝ) = (s ^ m) ^ (2 : ℕ) := Real.rpow_natCast _ 2
      rw [show 2 * (m : ℝ) = (m : ℝ) * 2 by ring, h1, h2]
    rw [show 2 * (m : ℝ) - γ = 2 * (m : ℝ) + (-γ) by ring, Real.rpow_add hs, e1]
  have hpowR : ∀ r : ℕ, s ^ (2 * (r : ℝ) - γ) = (s ^ r) ^ 2 * s ^ (-γ) := by
    intro r
    have e1 : s ^ (2 * (r : ℝ)) = (s ^ r) ^ 2 := by
      have h1 : s ^ ((r : ℝ) * (2 : ℝ)) = (s ^ r) ^ (2 : ℝ) :=
        Real.rpow_natCast_mul (le_of_lt hs) r 2
      have h2 : (s ^ r) ^ (2 : ℝ) = (s ^ r) ^ (2 : ℕ) := Real.rpow_natCast _ 2
      rw [show 2 * (r : ℝ) = (r : ℝ) * 2 by ring, h1, h2]
    rw [show 2 * (r : ℝ) - γ = 2 * (r : ℝ) + (-γ) by ring, Real.rpow_add hs, e1]
  have key := mul_le_mul_of_nonneg_right hcore (le_of_lt (Real.rpow_pos_of_pos hs (-γ)))
  have hexp : (2 * K ^ 2 * (m : ℝ)
        * ((Work.Spaces.DthIter m f z θ) ^ 2 + Sig)) * s ^ (-γ)
      = 2 * K ^ 2 * (m : ℝ)
          * ((Work.Spaces.DthIter m f z θ) ^ 2 * s ^ (-γ)
            + ∑ r ∈ Finset.Icc 1 (m - 1),
                (Work.Spaces.pthIter r f z θ) ^ 2 * s ^ (2 * (r : ℝ) - γ)) := by
    rw [hSigdef]
    simp only [hpowR]
    rw [show (∑ r ∈ Finset.Icc 1 (m - 1),
            (Work.Spaces.pthIter r f z θ) ^ 2 * ((s ^ r) ^ 2 * s ^ (-γ)))
          = (∑ r ∈ Finset.Icc 1 (m - 1),
              (Work.Spaces.pthIter r f z θ) ^ 2 * (s ^ r) ^ 2) * s ^ (-γ) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun r _ => by ring]
    ring
  have hgoalL : Work.Spaces.pthIter m f z θ ^ 2 * s ^ (2 * (m : ℝ) - γ)
      = (s ^ m) ^ 2 * Work.Spaces.pthIter m f z θ ^ 2 * s ^ (-γ) := by
    rw [hpowL]; ring
  have hgoalR : 2 * K ^ 2 * (m : ℝ)
        * (Work.Spaces.DthIter m f z θ ^ 2 * s ^ (-γ)
          + ∑ r ∈ Finset.Icc 1 (m - 1),
              (Work.Spaces.pthIter r f z θ) ^ 2 * s ^ (2 * (r : ℝ) - γ))
      = (2 * K ^ 2 * (m : ℝ) * (Work.Spaces.DthIter m f z θ ^ 2 + Sig)) * s ^ (-γ) :=
    hexp.symm
  rw [hgoalL, hgoalR]
  exact key

/-- **The slot recursion, for all orders `1 ≤ m ≤ M` at once.**  There is `C > 0` with

  `(∂_θ^mf)²σ^{2m-γ} ≤ C Σ_{1≤t≤m}(D_θ^tf)²σ^{-γ}`   for all `1 ≤ m ≤ M`,

on the open angular interval, for `f` smooth on the open quadrant.  Unlike
`remov.TopCoreB.slotRecAll`, no `t = 0` term occurs, so every summand is a *mixed* slot of
`HkIntegrand`. -/
theorem slotRecAll1 (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (γ : ℝ) (m : ℕ), 1 ≤ m → m ≤ M → ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter m f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - γ)
        ≤ C * ∑ t ∈ Finset.Icc 1 m,
            (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) := by
  induction M with
  | zero =>
      refine ⟨1, one_pos, fun γ m hm hmM f z θ hf hθ => ?_⟩
      have : ¬ (1 ≤ m) := by omega
      exact absurd hm this
  | succ M ih =>
      obtain ⟨C₀, hC₀pos, hC₀⟩ := ih
      obtain ⟨K, hKpos, hK⟩ := revExp1 (M + 1)
      refine ⟨max C₀ (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + ((M : ℝ) + 1) * C₀)), ?_, ?_⟩
      · exact lt_max_of_lt_left hC₀pos
      · intro γ m hm hmM f z θ hf hθ
        rcases Nat.lt_or_ge m (M + 1) with hlt | hge
        · refine le_trans (hC₀ γ m hm (by omega) f z θ hf hθ)
            (mul_le_mul_of_nonneg_right (le_max_left C₀ _) ?_)
          exact Finset.sum_nonneg fun t _ =>
            Work.FTS.EllipticEst.remov.TopCoreB.slotTerm_nonneg γ hθ _
        · obtain rfl : m = M + 1 := by omega
          have hm1 : 1 ≤ M + 1 := by omega
          have hstep := slotStep1 γ (M + 1) hm1 hKpos f z θ hθ (hK f z θ hf)
          set Ssum : ℝ := ∑ t ∈ Finset.Icc 1 (M + 1),
              (Work.Spaces.DthIter t f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ) with hSsum
          have hSnn : 0 ≤ Ssum := by
            rw [hSsum]
            exact Finset.sum_nonneg fun t _ =>
              Work.FTS.EllipticEst.remov.TopCoreB.slotTerm_nonneg γ hθ _
          -- the lower orders, by the induction hypothesis
          have hlow : ∀ r ∈ Finset.Icc 1 (M + 1 - 1),
              (Work.Spaces.pthIter r f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ) ≤ C₀ * Ssum := by
            intro r hr
            obtain ⟨hr1, hrM⟩ := Finset.mem_Icc.mp hr
            have hrM' : r ≤ M := by omega
            refine le_trans (hC₀ γ r hr1 hrM' f z θ hf hθ) ?_
            refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
            rw [hSsum]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro t ht
              simp only [Finset.mem_Icc] at ht ⊢
              omega
            · intro t _ _
              exact Work.FTS.EllipticEst.remov.TopCoreB.slotTerm_nonneg γ hθ _
          have hsumle : (∑ r ∈ Finset.Icc 1 (M + 1 - 1),
                (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ))
              ≤ ((M : ℝ) + 1) * (C₀ * Ssum) := by
            calc (∑ r ∈ Finset.Icc 1 (M + 1 - 1),
                  (Work.Spaces.pthIter r f z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ))
                ≤ ∑ _r ∈ Finset.Icc 1 (M + 1 - 1), C₀ * Ssum := Finset.sum_le_sum hlow
              _ = ((Finset.Icc 1 (M + 1 - 1)).card : ℝ) * (C₀ * Ssum) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ((M : ℝ) + 1) * (C₀ * Ssum) := by
                  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC₀pos.le hSnn)
                  have h1 : (Finset.Icc 1 (M + 1 - 1)).card = M := by
                    rw [Nat.card_Icc]; omega
                  rw [h1]
                  push_cast
                  linarith
          have htop : (Work.Spaces.DthIter (M + 1) f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
              ≤ Ssum := by
            rw [hSsum]
            exact Finset.single_le_sum
              (f := fun t => (Work.Spaces.DthIter t f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-γ))
              (fun t _ => Work.FTS.EllipticEst.remov.TopCoreB.slotTerm_nonneg γ hθ _)
              (Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ M + 1), le_rfl⟩)
          have hinner : ((Work.Spaces.DthIter (M + 1) f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-γ)
              + ∑ r ∈ Finset.Icc 1 (M + 1 - 1),
                  (Work.Spaces.pthIter r f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - γ))
              ≤ (1 + ((M : ℝ) + 1) * C₀) * Ssum := by
            have h := add_le_add htop hsumle
            have heq : Ssum + ((M : ℝ) + 1) * (C₀ * Ssum)
                = (1 + ((M : ℝ) + 1) * C₀) * Ssum := by ring
            exact heq ▸ h
          have hmain : (Work.Spaces.pthIter (M + 1) f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * ((M + 1 : ℕ) : ℝ) - γ)
              ≤ 2 * K ^ 2 * (((M + 1 : ℕ)) : ℝ) * ((1 + ((M : ℝ) + 1) * C₀) * Ssum) :=
            le_trans hstep (mul_le_mul_of_nonneg_left hinner (by positivity))
          calc (Work.Spaces.pthIter (M + 1) f z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * ((M + 1 : ℕ) : ℝ) - γ)
              ≤ 2 * K ^ 2 * (((M + 1 : ℕ)) : ℝ) * ((1 + ((M : ℝ) + 1) * C₀) * Ssum) := hmain
            _ = (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + ((M : ℝ) + 1) * C₀)) * Ssum := by
                push_cast; ring
            _ ≤ max C₀ (2 * K ^ 2 * ((M : ℝ) + 1) * (1 + ((M : ℝ) + 1) * C₀)) * Ssum :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hSnn

/-! ## Weight facts and the slot/`ℋ^k`-integrand comparison -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, ← div_pow]
  exact sq_nonneg _

/-- `(Wt α z θ)² = w(z)²·sin(2θ)^{-γ}` on the open angular interval. -/
theorem Wt_sq_of_Ioo (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Work.FTS.EllipticEst.remov.TopCoreB.sin_two_pos_of_Ioo hθ
  have hexp : -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)
      = -(Work.Spaces.gam α) := by ring
  have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hs, hexp]
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hsq]

/-- A single `D_θ`-slot is dominated by the `ℋ^k`-integrand. -/
theorem slotsum_le_HkIntegrand (α : ℝ) (k m : ℕ) (hmk : m ≤ k) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (∑ t ∈ Finset.Icc 1 m,
        (Work.Spaces.mixed 0 t X z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ (m : ℝ) * Work.Spaces.HkIntegrand α k X z θ := by
  calc (∑ t ∈ Finset.Icc 1 m,
        (Work.Spaces.mixed 0 t X z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∑ _t ∈ Finset.Icc 1 m, Work.Spaces.HkIntegrand α k X z θ := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨ht1, htm⟩ := Finset.mem_Icc.mp ht
        simpa only [Work.Spaces.mixed_zero_left] using
          Work.Spaces.sq_le_HkIntegrand_mixed α k X z θ t 0 ht1 (by omega)
    _ = (m : ℝ) * Work.Spaces.HkIntegrand α k X z θ := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]

/-- Splitting off the top term of a slot sum. -/
theorem slotsum_split (f : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 k, f t) = (∑ t ∈ Finset.Icc 1 (k - 1), f t) + f k := by
  conv_lhs => rw [show k = (k - 1) + 1 from by omega]
  rw [Finset.sum_Icc_succ_top (by omega)]
  rw [show k - 1 + 1 = k from by omega]

/-- **The pointwise slot recursion in weight form**: for `1 ≤ m ≤ k` and `X` smooth on the open
quadrant, the plain `m`-th angular derivative of `X`, weighted by `σ^{2m-γ}w²`, is dominated by
the `D_θ`-slots of `X`.  The constant is independent of `α` (and of `γ = gam α`). -/
theorem pthSlot_le_slots (k m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry X) (z, θ)) →
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Work.Spaces.pthIter m X z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2
        ≤ C * ∑ t ∈ Finset.Icc 1 m,
            (Work.Spaces.mixed 0 t X z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  obtain ⟨Cs, hCspos, hCs⟩ := slotRecAll1 k
  refine ⟨Cs, hCspos, fun α X z θ hX hz hθ => ?_⟩
  have h := hCs (Work.Spaces.gam α) m hm hmk X z θ hX hθ
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (Work.Spaces.w z))
  have hgoal : (Cs * ∑ t ∈ Finset.Icc 1 m,
        (Work.Spaces.DthIter t X z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) * (Work.Spaces.w z) ^ 2
      = Cs * ∑ t ∈ Finset.Icc 1 m,
          (Work.Spaces.mixed 0 t X z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Work.Spaces.mixed_zero_left, mul_pow, Wt_sq_of_Ioo α hθ]
    ring
  rw [hgoal] at hmul
  exact hmul

/-- `(a+b+c)² ≤ 3(a²+b²+c²)`. -/
theorem sq_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The arithmetic core of the source slot bound: comparing the three slot chains with the
constant `12·M0·(k+2)` of the target. -/
theorem srcArith {M0 α kk C1 C2 u v w0 t A1 A2 A3 : ℝ}
    (hM0 : 0 < M0) (hC1pos : 0 < C1) (hC2pos : 0 < C2) (hC1 : C1 ≤ M0) (hC2 : C2 ≤ M0)
    (hk : 3 ≤ kk) (hα0 : 0 < α) (hα4 : α ≤ 1 / 4)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w0) (ht : 0 ≤ t)
    (hA1nn : 0 ≤ A1) (hA2nn : 0 ≤ A2) (hA3nn : 0 ≤ A3)
    (hA1 : A1 ≤ kk * u) (hA2 : A2 ≤ (kk - 1) * v + w0) (hA3 : A3 ≤ (kk - 2) * t) :
    3 * (C1 * A1 + α ^ 4 * (C1 * A2) + (α * (5 + α)) ^ 2 * (C2 * A3))
      ≤ (12 * M0 * (kk + 2)) * (u + α ^ 4 * (v + w0) + t) := by
  have hα4nn : 0 ≤ α ^ 4 := by positivity
  have hc2 : (α * (5 + α)) ^ 2 ≤ 4 := by
    have hnn : 0 ≤ α * (5 + α) := by nlinarith [hα0]
    have hle : α * (5 + α) ≤ 2 := by nlinarith [hα0, hα4]
    nlinarith [hnn, hle]
  have hM0nn : 0 ≤ M0 := hM0.le
  have hkk : 0 < kk := by linarith
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hC2nn : 0 ≤ C2 := hC2pos.le
  have ca : 3 * C1 * kk ≤ 12 * M0 * (kk + 2) := by nlinarith [hC1, hM0, hk]
  have cb : 3 * C1 ≤ 12 * M0 * (kk + 2) := by nlinarith [hC1, hM0, hk]
  have cc : 12 * C2 * (kk - 2) ≤ 12 * M0 * (kk + 2) := by nlinarith [hC2, hM0, hk]
  have e1 : C1 * A1 ≤ C1 * (kk * u) := mul_le_mul_of_nonneg_left hA1 hC1nn
  have e2 : C1 * A2 ≤ C1 * ((kk - 1) * v + w0) := mul_le_mul_of_nonneg_left hA2 hC1nn
  have e3 : C2 * A3 ≤ C2 * ((kk - 2) * t) := mul_le_mul_of_nonneg_left hA3 hC2nn
  have f1 : α ^ 4 * (C1 * A2) ≤ α ^ 4 * (C1 * ((kk - 1) * v + w0)) :=
    mul_le_mul_of_nonneg_left e2 hα4nn
  have f2 : (α * (5 + α)) ^ 2 * (C2 * A3) ≤ 4 * (C2 * ((kk - 2) * t)) := by
    have h1 : (α * (5 + α)) ^ 2 * (C2 * A3) ≤ 4 * (C2 * A3) :=
      mul_le_mul_of_nonneg_right hc2 (mul_nonneg hC2nn hA3nn)
    have h2 : 4 * (C2 * A3) ≤ 4 * (C2 * ((kk - 2) * t)) :=
      mul_le_mul_of_nonneg_left e3 (by norm_num)
    linarith
  have hsum : 3 * (C1 * A1 + α ^ 4 * (C1 * A2) + (α * (5 + α)) ^ 2 * (C2 * A3))
      ≤ 3 * (C1 * (kk * u) + α ^ 4 * (C1 * ((kk - 1) * v + w0))
          + 4 * (C2 * ((kk - 2) * t))) := by
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    calc 3 * (C1 * A1 + α ^ 4 * (C1 * A2) + (α * (5 + α)) ^ 2 * (C2 * A3))
        = 3 * (C1 * A1) + 3 * (α ^ 4 * (C1 * A2))
          + 3 * ((α * (5 + α)) ^ 2 * (C2 * A3)) := by ring
      _ ≤ 3 * (C1 * (kk * u)) + 3 * (α ^ 4 * (C1 * ((kk - 1) * v + w0)))
            + 3 * (4 * (C2 * ((kk - 2) * t))) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_of_nonneg_left e1 h3
          · exact mul_le_mul_of_nonneg_left f1 h3
          · exact mul_le_mul_of_nonneg_left f2 h3
      _ = 3 * (C1 * (kk * u) + α ^ 4 * (C1 * ((kk - 1) * v + w0))
            + 4 * (C2 * ((kk - 2) * t))) := by ring
  have g1 : 3 * (C1 * (kk * u)) ≤ (12 * M0 * (kk + 2)) * u := by
    have h : 3 * (C1 * kk) ≤ 12 * M0 * (kk + 2) := by nlinarith [ca]
    calc 3 * (C1 * (kk * u)) = (3 * (C1 * kk)) * u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h hu
  have g2 : 3 * (α ^ 4 * (C1 * ((kk - 1) * v + w0)))
      ≤ (12 * M0 * (kk + 2)) * (α ^ 4 * (v + w0)) := by
    have hvv : (kk - 1) * v + w0 ≤ (kk + 2) * (v + w0) := by nlinarith [hv, hw, hkk]
    have h1 : C1 * ((kk - 1) * v + w0) ≤ C1 * ((kk + 2) * (v + w0)) :=
      mul_le_mul_of_nonneg_left hvv hC1nn
    have h2 : 3 * (C1 * ((kk + 2) * (v + w0))) ≤ (12 * M0 * (kk + 2)) * (v + w0) := by
      rw [show 3 * (C1 * ((kk + 2) * (v + w0))) = (3 * C1 * (kk + 2)) * (v + w0) from by ring]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith : (0 : ℝ) ≤ v + w0)
      nlinarith [cb, hkk, hM0nn]
    have h4 : 3 * (α ^ 4 * (C1 * ((kk - 1) * v + w0)))
        ≤ 3 * (α ^ 4 * (C1 * ((kk + 2) * (v + w0)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hα4nn) (by norm_num)
    refine le_trans h4 ?_
    calc 3 * (α ^ 4 * (C1 * ((kk + 2) * (v + w0))))
        = α ^ 4 * (3 * (C1 * ((kk + 2) * (v + w0)))) := by ring
      _ ≤ α ^ 4 * ((12 * M0 * (kk + 2)) * (v + w0)) :=
          mul_le_mul_of_nonneg_left h2 hα4nn
      _ = (12 * M0 * (kk + 2)) * (α ^ 4 * (v + w0)) := by ring
  have g3 : 3 * (4 * (C2 * ((kk - 2) * t))) ≤ (12 * M0 * (kk + 2)) * t := by
    calc 3 * (4 * (C2 * ((kk - 2) * t))) = (12 * C2 * (kk - 2)) * t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right cc ht
  refine le_trans hsum ?_
  have h := add_le_add (add_le_add g1 g2) g3
  calc 3 * (C1 * (kk * u) + α ^ 4 * (C1 * ((kk - 1) * v + w0))
          + 4 * (C2 * ((kk - 2) * t)))
      = 3 * (C1 * (kk * u)) + 3 * (α ^ 4 * (C1 * ((kk - 1) * v + w0)))
        + 3 * (4 * (C2 * ((kk - 2) * t))) := by ring
    _ ≤ (12 * M0 * (kk + 2)) * u + (12 * M0 * (kk + 2)) * (α ^ 4 * (v + w0))
        + (12 * M0 * (kk + 2)) * t := h
    _ = (12 * M0 * (kk + 2)) * (u + α ^ 4 * (v + w0) + t) := by ring

/-- **The source slot bound** (the clean-cone copy of `remov.TopCoreB.srcBound`). -/
theorem srcBoundFts (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F) →
      (α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F) →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)))
        ≤ C * (Work.Spaces.HkSq α k F
            + α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  z θ * Work.Spaces.Wt α z θ) ^ 2)
            + Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            + α ^ 4 * Work.Spaces.HkSq α (k - 1)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  intro k hk
  obtain ⟨C1, hC1pos, hC1⟩ := pthSlot_le_slots k k (by omega) (le_refl k)
  obtain ⟨C2, hC2pos, hC2⟩ := pthSlot_le_slots (k - 1) (k - 2) (by omega) (by omega)
  let M0 : ℝ := max 1 (max C1 C2)
  have hM0pos : 0 < M0 := lt_max_of_lt_left one_pos
  have hC1le : C1 ≤ M0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2le : C2 ≤ M0 := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨12 * M0 * ((k : ℝ) + 2), by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk hH1 hH2
  let CM : ℝ := 12 * M0 * ((k : ℝ) + 2)
  have hCMpos : 0 < CM := by rw [show CM = 12 * M0 * ((k : ℝ) + 2) from rfl]; positivity
  have hCMnn : 0 ≤ CM := le_of_lt hCMpos
  -- ## the data
  have hsoΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hsoF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen_of_bslOp_eq hsoΨ
      (fun z θ hz hθ hlt => hwk.eq z hz θ hθ hlt)
  let A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
  let hB : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)
  have hsoA : Work.FTS.EllipticEst.SmoothOpen A :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hsoΨ 2)
  have hsoDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hsoΨ
  have hsoB : Work.FTS.EllipticEst.SmoothOpen hB := (hsoDz.pth).pth
  have memF : Work.Spaces.HkMem α k F := hwk.memF
  have memA : Work.Spaces.HkMem α k A := hwk.memA
  have memAk1 : Work.Spaces.HkMem α (k - 1) A :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) (hsoA.forall) memA
  have memh : Work.Spaces.HkMem α (k - 1) hB :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1)
      (Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (by omega) ((hsoΨ.pth).pth) hwk.memB)
      (fun z hz θ hθ => Work.FTS.EllipticEst.AeMom.Repair.Dz_pthIter_two_comm hsoΨ z θ hz hθ.1 hθ.2)
  have hslotTop :=
    Work.FTS.EllipticEst.remov.TopCoreB.slotIntegrable α k hsoA memA 0 k (by omega) (by omega)
  -- ## the pointwise bound
  have cda : ∀ {X : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen X → ∀ (z θ : ℝ),
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      ∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry X) (z, θ) := fun hX z θ hz hθ n =>
    (hX.forall n).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
  have haeIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
        = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_congr_set
        (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
    rw [← h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
        ≤ CM * (Work.Spaces.HkIntegrand α k F z θ
            + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
            + Work.Spaces.HkIntegrand α (k - 1) hB z θ) := by
    intro z θ hz hθ0 hθ1
    have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hσ : 0 < Real.sin (2 * θ) :=
      Work.FTS.EllipticEst.remov.TopCoreB.sin_two_pos_of_Ioo hθI
    have hσnn : 0 ≤ Real.sin (2 * θ) := le_of_lt hσ
    -- the three slot sums
    set SF : ℝ := ∑ t ∈ Finset.Icc 1 k,
        (Work.Spaces.mixed 0 t F z θ * Work.Spaces.Wt α z θ) ^ 2 with hSFdef
    set SA : ℝ := ∑ t ∈ Finset.Icc 1 k,
        (Work.Spaces.mixed 0 t A z θ * Work.Spaces.Wt α z θ) ^ 2 with hSAdef
    set Sh : ℝ := ∑ t ∈ Finset.Icc 1 (k - 2),
        (Work.Spaces.mixed 0 t hB z θ * Work.Spaces.Wt α z θ) ^ 2 with hShdef
    -- the additivity of `∂_θ^k` over the source
    have hsoAcs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α ^ 2 * A z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hsoA
    have hsoc : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α)) hsoDz
    have hsum : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + α ^ 2 * A z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl hsoF hsoAcs
    have hadd1 : Work.Spaces.pthIter k
          (fun z θ => F z θ + α ^ 2 * A z θ + (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) z θ
        = Work.Spaces.pthIter k (fun z θ => F z θ + α ^ 2 * A z θ) z θ
          + Work.Spaces.pthIter k
              (fun z θ => (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) z θ :=
      Work.FTS.EllipticEst.TT.ESW.pthIter_add_on_Q0_fts hsum hsoc k z θ hz hθ0 hθ1
    have hadd2 : Work.Spaces.pthIter k (fun z θ => F z θ + α ^ 2 * A z θ) z θ
        = Work.Spaces.pthIter k F z θ
          + Work.Spaces.pthIter k (fun z θ => α ^ 2 * A z θ) z θ :=
      Work.FTS.EllipticEst.TT.ESW.pthIter_add_on_Q0_fts hsoF hsoAcs k z θ hz hθ0 hθ1
    have hcm1 : Work.Spaces.pthIter k (fun z θ => α ^ 2 * A z θ) z θ
        = α ^ 2 * Work.Spaces.pthIter k A z θ := by
      rw [Work.FTS.EllipticEst.TT.ESW.pthIter_const_mul_fts (α ^ 2) k A]
    have hcm2 : Work.Spaces.pthIter k
          (fun z θ => (α * (5 + α)) * Work.Spaces.DzIter 1 Ψ z θ) z θ
        = (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ := by
      rw [Work.FTS.EllipticEst.TT.ESW.pthIter_const_mul_fts (α * (5 + α)) k
        (Work.Spaces.DzIter 1 Ψ)]
    have hid : Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ
        = Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
          + (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ := by
      have h := hadd1
      rw [hadd2, hcm1, hcm2] at h
      exact h
    -- the three slot bounds
    have hbF : (Work.Spaces.pthIter k F z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2 ≤ C1 * SF :=
      hC1 α F z θ (cda hsoF z θ hz hθI) hz hθI
    have hbA : (Work.Spaces.pthIter k A z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2 ≤ C1 * SA :=
      hC1 α A z θ (cda hsoA z θ hz hθI) hz hθI
    have hDzrel : Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ
        = Work.Spaces.pthIter (k - 2) hB z θ := by
      have h := Work.FTS.EllipticEst.remov.TopCoreB.pthIter_addT (k - 2) 2
        (Work.Spaces.DzIter 1 Ψ)
      rw [show k - 2 + 2 = k from by omega] at h
      exact congrFun (congrFun h z) θ
    have hσle : (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α) := by
      refine Real.rpow_le_rpow_of_exponent_ge hσ (Real.sin_le_one _) ?_
      have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]; push_cast; ring
      rw [hcast]; linarith
    have hbDz : (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2 ≤ C2 * Sh := by
      rw [hDzrel]
      refine le_trans ?_ (hC2 α hB z θ (cda hsoB z θ hz hθI) hz hθI)
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg (Work.Spaces.w z))
      exact mul_le_mul_of_nonneg_left hσle (sq_nonneg _)
    -- the sums against the `ℋ^k`-integrands
    have hSFb : SF ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k F z θ :=
      slotsum_le_HkIntegrand α k k (le_refl k) F z θ
    have hSAs : (∑ t ∈ Finset.Icc 1 (k - 1),
          (Work.Spaces.mixed 0 t A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ((k - 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α (k - 1) A z θ :=
      slotsum_le_HkIntegrand α (k - 1) (k - 1) (le_refl _) A z θ
    have hSAb : SA ≤ ((k - 1 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α (k - 1) A z θ
        + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hSAdef, slotsum_split (fun t => (Work.Spaces.mixed 0 t A z θ
        * Work.Spaces.Wt α z θ) ^ 2) k (by omega)]
      linarith [hSAs]
    have hShb : Sh ≤ ((k - 2 : ℕ) : ℝ) * Work.Spaces.HkIntegrand α (k - 1) hB z θ :=
      slotsum_le_HkIntegrand α (k - 1) (k - 2) (by omega) hB z θ
    -- the algebraic combination of the three slot bounds
    have hth : (Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
          + (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
        ≤ 3 * (C1 * SF + α ^ 4 * (C1 * SA) + (α * (5 + α)) ^ 2 * (C2 * Sh)) := by
      have hsq := sq_three_le (Work.Spaces.pthIter k F z θ)
        (α ^ 2 * Work.Spaces.pthIter k A z θ)
        ((α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ)
      have hb : (α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2
          = α ^ 4 * (Work.Spaces.pthIter k A z θ) ^ 2 := by ring
      have hc : ((α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
          = (α * (5 + α)) ^ 2
            * (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 := by ring
      rw [hb, hc] at hsq
      have hσw : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2 := mul_nonneg (Real.rpow_nonneg hσnn _) (sq_nonneg _)
      have hstep := mul_le_mul_of_nonneg_right hsq hσw
      rw [show (Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
            + (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
          = (Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
            + (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * ((Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
              * (Work.Spaces.w z) ^ 2) from by ring]
      refine le_trans hstep ?_
      rw [show 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            + α ^ 4 * (Work.Spaces.pthIter k A z θ) ^ 2
            + (α * (5 + α)) ^ 2 * (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2)
          * ((Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2)
          = 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2
            + α ^ 4 * ((Work.Spaces.pthIter k A z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2)
            + (α * (5 + α)) ^ 2 * ((Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
              * (Work.Spaces.w z) ^ 2)) from by ring]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 3)
      have f2 : α ^ 4 * ((Work.Spaces.pthIter k A z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w z) ^ 2) ≤ α ^ 4 * (C1 * SA) :=
        mul_le_mul_of_nonneg_left hbA (by positivity)
      have f3 : (α * (5 + α)) ^ 2
            * ((Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
              * (Work.Spaces.w z) ^ 2) ≤ (α * (5 + α)) ^ 2 * (C2 * Sh) :=
        mul_le_mul_of_nonneg_left hbDz (sq_nonneg _)
      linarith [hbF, f2, f3]
    -- the final pointwise bound
    rw [hid]
    refine le_trans hth ?_
    have hHiFnn : 0 ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.HkIntegrand_nonneg α k F z θ
    have hHiAnn : 0 ≤ Work.Spaces.HkIntegrand α (k - 1) A z θ :=
      Work.Spaces.HkIntegrand_nonneg α (k - 1) A z θ
    have hHihnn : 0 ≤ Work.Spaces.HkIntegrand α (k - 1) hB z θ :=
      Work.Spaces.HkIntegrand_nonneg α (k - 1) hB z θ
    have htopnn : 0 ≤ (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2 := sq_nonneg _
    have hSFnn : (0 : ℝ) ≤ SF := by
      rw [hSFdef]; exact Finset.sum_nonneg fun t _ => sq_nonneg _
    have hSAnn : (0 : ℝ) ≤ SA := by
      rw [hSAdef]; exact Finset.sum_nonneg fun t _ => sq_nonneg _
    have hShnn : (0 : ℝ) ≤ Sh := by
      rw [hShdef]; exact Finset.sum_nonneg fun t _ => sq_nonneg _
    have hA1' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring
    have hA3' : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ k)]; push_cast; ring
    have hSAb' : SA ≤ ((k : ℝ) - 1) * Work.Spaces.HkIntegrand α (k - 1) A z θ
        + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [← hA1']; exact hSAb
    have hShb' : Sh ≤ ((k : ℝ) - 2) * Work.Spaces.HkIntegrand α (k - 1) hB z θ := by
      rw [← hA3']; exact hShb
    exact srcArith (M0 := M0) (α := α) (kk := (k : ℝ)) (C1 := C1) (C2 := C2)
      (u := Work.Spaces.HkIntegrand α k F z θ)
      (v := Work.Spaces.HkIntegrand α (k - 1) A z θ)
      (w0 := (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
      (t := Work.Spaces.HkIntegrand α (k - 1) hB z θ)
      (A1 := SF) (A2 := SA) (A3 := Sh)
      hM0pos hC1pos hC2pos hC1le hC2le (by exact_mod_cast hk) hα hα4
      hHiFnn hHiAnn htopnn hHihnn hSFnn hSAnn hShnn hSFb hSAb' hShb'
  -- ## the integration
  have hIntF : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k F z θ) Work.Spaces.Iθ :=
    fun z hz => memF.1 z hz
  have hIntA : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α (k - 1) A z θ) Work.Spaces.Iθ :=
    fun z hz => memAk1.1 z hz
  have hIntTop : ∀ z ∈ Work.Spaces.Iz, IntegrableOn
      (fun θ => (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ := fun z hz => hslotTop.1 z hz
  have hInth : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α (k - 1) hB z θ) Work.Spaces.Iθ :=
    fun z hz => memh.1 z hz
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w z) ^ 2)
        ≤ CM * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
            + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ)) := by
    intro z hz
    have hsliceF := hIntF z hz
    have hsliceA := hIntA z hz
    have hsliceT := hIntTop z hz
    have hsliceh := hInth z hz
    have hIF : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k F z θ
        + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)) Work.Spaces.Iθ :=
      hsliceF.add ((hsliceA.add hsliceT).const_mul (α ^ 4))
    have hIF2 : IntegrableOn (fun θ => (Work.Spaces.HkIntegrand α k F z θ
        + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
        + Work.Spaces.HkIntegrand α (k - 1) hB z θ) Work.Spaces.Iθ := hIF.add hsliceh
    have hmaj : IntegrableOn (fun θ => CM * ((Work.Spaces.HkIntegrand α k F z θ
        + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
            + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
        + Work.Spaces.HkIntegrand α (k - 1) hB z θ)) Work.Spaces.Iθ := hIF2.const_mul CM
    have hmono : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w z) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, CM * ((Work.Spaces.HkIntegrand α k F z θ
            + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
                + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
            + Work.Spaces.HkIntegrand α (k - 1) hB z θ) :=
      MeasureTheory.integral_mono_of_nonneg ?_ hmaj ?_
    · rw [MeasureTheory.integral_const_mul] at hmono
      refine le_trans hmono (le_of_eq ?_)
      have h1 : (∫ θ in Work.Spaces.Iθ, ((Work.Spaces.HkIntegrand α k F z θ
              + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
                  + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
              + Work.Spaces.HkIntegrand α (k - 1) hB z θ))
          = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α k F z θ
              + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
                  + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)))
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ) :=
        MeasureTheory.integral_add hIF hsliceh
      have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α k F z θ
              + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
                  + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)))
          = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
            + (∫ θ in Work.Spaces.Iθ, α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
                + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)) :=
        MeasureTheory.integral_add hsliceF ((hsliceA.add hsliceT).const_mul (α ^ 4))
      have h3 : (∫ θ in Work.Spaces.Iθ, α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          = α ^ 4 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)) :=
        MeasureTheory.integral_const_mul (α ^ 4) _
      have h4 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          = (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2) :=
        MeasureTheory.integral_add hsliceA hsliceT
      rw [h1, h2, h3, h4]
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      have hσnn : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσnn _)) (sq_nonneg _)
    · rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
      · rw [← hz0]
        refine Filter.Eventually.of_forall fun θ => ?_
        show (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) 0 θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w 0) ^ 2 ≤ CM * ((Work.Spaces.HkIntegrand α k F 0 θ
              + α ^ 4 * (Work.Spaces.HkIntegrand α (k - 1) A 0 θ
                  + (Work.Spaces.mixed 0 k A 0 θ * Work.Spaces.Wt α 0 θ) ^ 2))
              + Work.Spaces.HkIntegrand α (k - 1) hB 0 θ)
        rw [show (Work.Spaces.w 0) ^ 2 = 0 from by norm_num [Work.Spaces.w], mul_zero]
        refine mul_nonneg hCMnn ?_
        have h1 := Work.Spaces.HkIntegrand_nonneg α k F 0 θ
        have h2 := Work.Spaces.HkIntegrand_nonneg α (k - 1) A 0 θ
        have h3 := Work.Spaces.HkIntegrand_nonneg α (k - 1) hB 0 θ
        have h4 : (0 : ℝ) ≤ (Work.Spaces.mixed 0 k A 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 :=
          sq_nonneg _
        have h5 : (0 : ℝ) ≤ α ^ 4 := by positivity
        exact add_nonneg (add_nonneg h1 (mul_nonneg h5 (add_nonneg h2 h4))) h3
      · filter_upwards [haeIoo] with θ hθ
        exact hpt z θ hzpos hθ.1 hθ.2
  -- ## the radial integration
  have hIntF' : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) Work.Spaces.Iz := memF.2
  have hIntA' : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α (k - 1) A z θ) Work.Spaces.Iz := memAk1.2
  have hIntTop' : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iz := hslotTop.2
  have hInth' : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α (k - 1) hB z θ) Work.Spaces.Iz := memh.2
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, CM * ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ)
          + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ)) := by
    have hA1' : IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ)
          + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))) Work.Spaces.Iz :=
      hIntF'.add ((hIntA'.add hIntTop').const_mul (α ^ 4))
    have hA2' : IntegrableOn (fun z => ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ)
          + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)))
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ)) Work.Spaces.Iz :=
      hA1'.add hInth'
    have hMz : IntegrableOn (fun z => CM * ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F z θ)
          + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ))) Work.Spaces.Iz :=
      hA2'.const_mul CM
    refine MeasureTheory.integral_mono_of_nonneg ?_ hMz
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
    refine Filter.Eventually.of_forall fun z => ?_
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ => by
      have hθ' : θ ∈ Work.Spaces.Iθ := hθ
      have hσnn : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ'.1], by linarith [hθ'.2, Real.pi_pos]⟩
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσnn _)) (sq_nonneg _)
  -- ## evaluating the majorant
  have hval : (∫ z in Work.Spaces.Iz, CM * ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F z θ)
      + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
        + (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ)))
      = CM * (Work.Spaces.HkSq α k F
          + α ^ 4 * (Work.Spaces.HkSq α (k - 1) A
            + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          + Work.Spaces.HkSq α (k - 1) hB) := by
    have h1 : (∫ z in Work.Spaces.Iz, (((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F z θ)
            + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)))
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) hB z θ)))
        = (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F z θ)
            + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))))
          + (∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) hB z θ)) :=
      MeasureTheory.integral_add
        (hIntF'.add ((hIntA'.add hIntTop').const_mul (α ^ 4))) hInth'
    have h2 : (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F z θ)
            + α ^ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))))
        = (∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F z θ))
          + (∫ z in Work.Spaces.Iz, α ^ 4 * ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) A z θ)
              + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))) :=
      MeasureTheory.integral_add hIntF' ((hIntA'.add hIntTop').const_mul (α ^ 4))
    have h3 : (∫ z in Work.Spaces.Iz, α ^ 4 * ((∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)))
        = α ^ 4 * (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))) :=
      MeasureTheory.integral_const_mul (α ^ 4) _
    have h4 : (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) A z θ)
            + (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)))
        = (∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α (k - 1) A z θ))
          + (∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)) :=
      MeasureTheory.integral_add hIntA' hIntTop'
    rw [MeasureTheory.integral_const_mul, h1, h2, h3, h4]
    simp only [Work.Spaces.HkSq]
  -- ## assembling
  have hfinal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          * (Work.Spaces.w z) ^ 2)
      ≤ CM * (Work.Spaces.HkSq α k F
          + α ^ 4 * (Work.Spaces.HkSq α (k - 1) A
            + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          + Work.Spaces.HkSq α (k - 1) hB) := le_trans houter (le_of_eq hval)
  -- ## assembling
  have hconv : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
            (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w z) ^ 2 := by
    have hpteq : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w z) ^ 2 := by
      intro z
      rw [MeasureTheory.integral_mul_const]
      ring
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpteq)
  have hTknn : 0 ≤ (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2) :=
    integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
            (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter k (Work.FTS.EllipticEst.remov.TopCoreB.SrcG α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            * (Work.Spaces.w z) ^ 2) := hconv
    _ ≤ CM * (Work.Spaces.HkSq α k F
          + α ^ 4 * (Work.Spaces.HkSq α (k - 1) A
            + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2))
          + Work.Spaces.HkSq α (k - 1) hB) := le_trans houter (le_of_eq hval)
    _ ≤ (12 * M0 * ((k : ℝ) + 2)) * (Work.Spaces.HkSq α k F
          + α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 k A z θ * Work.Spaces.Wt α z θ) ^ 2)
          + Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          + α ^ 4 * Work.Spaces.HkSq α (k - 1) A) := by
        refine mul_le_mul_of_nonneg_left ?_ hCMnn
        linarith [hTknn, Work.Spaces.HkSq_nonneg α k F,
          Work.Spaces.HkSq_nonneg α (k - 1) A, Work.Spaces.HkSq_nonneg α (k - 1) hB,
          show Work.Spaces.HkSq α (k - 1) hB
            = Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            from rfl]
end Work.FTS.EllipticEst.Prop.BSlotTop
