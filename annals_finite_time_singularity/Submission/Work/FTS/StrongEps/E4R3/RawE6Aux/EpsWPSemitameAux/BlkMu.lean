/-
# `bdata_blkMu` — the `BData` of the `mubar·AK` block
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.Common

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem bdata_blkMu (C₀ : ℝ) :
    ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ KM : ℝ, 0 < KM ∧ ∀ {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KM
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg) := by
  intro α hαI
  obtain ⟨KAK, hKAKpos, hAK⟩ := Work.FTS.StrongPersist.AK6_mem_norm
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  set KM : ℝ := (1 + CT * C₀) ^ 2 * KAK ^ 2 + 1 with hKM
  have hKMpos : 0 < KM := by rw [hKM]; positivity
  refine ⟨KM, hKMpos, ?_⟩
  intro Φs w Φg hcls hXw hμ
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hAKmem : Work.Spaces.HkMem α 6 (Work.Construction.AK α) := (hAK α hα0 hα1).1
  have hAKnorm : Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ KAK := (hAK α hα0 hα1).2
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hm4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
  have htr : |Work.Coercivity.L12f (Work.Coercivity.Transport w) 0|
      ≤ CT * Work.FTS.Nonlin.Xn α w := hCT α w hα0 hα1 hm4w
  -- `C₀ ≥ 0`, so that `C₀ α² ≤ C₀` for `α ≤ 1`
  have hC₀0 : 0 ≤ C₀ := by
    by_contra hneg
    have hlt : C₀ < 0 := lt_of_not_ge hneg
    have hprod : C₀ * α ^ 2 < 0 := mul_neg_of_neg_of_pos hlt (by positivity)
    have hxw : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
    linarith [hXw, hprod, hxw]
  -- the modulation identity: `2α μ = mubar + L₁₂(Transport w)(0)`
  have hkey := Work.Construction.two_mul_mufunS α
    (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
    (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) w
    (ne_of_gt hα0)
  have hmuBlk : Work.Construction.mufunS α
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) w
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg := rfl
  rw [hmuBlk] at hkey
  have hL12eq : Work.Construction.L12 (Work.Coercivity.Transport w) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport w) 0 := rfl
  rw [hL12eq] at hkey
  have hmubar : Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      = 2 * α * Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg
        - Work.Coercivity.L12f (Work.Coercivity.Transport w) 0 := by
    linarith [hkey]
  -- the bound on the scalar `mubar`
  have h1 : |2 * α * Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hα0]
    have hprod : α * |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 := by
      have hmm := mul_le_mul hα1 hμ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith [hmm]
    linarith [hprod]
  have h2 : |Work.Coercivity.L12f (Work.Coercivity.Transport w) 0|
      ≤ CT * (C₀ * α ^ 2) := le_trans htr (mul_le_mul_of_nonneg_left hXw hCTpos.le)
  have h4 : α ^ 2 ≤ 1 := by
    have h := mul_self_le_mul_self hα0.le hα1
    nlinarith [h]
  have h3 : CT * (C₀ * α ^ 2) ≤ CT * C₀ := by
    refine mul_le_mul_of_nonneg_left ?_ hCTpos.le
    have hle : α ^ 2 * C₀ ≤ 1 * C₀ := mul_le_mul_of_nonneg_right h4 hC₀0
    linarith [hle]
  have hMBex : |Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))|
      ≤ 1 + CT * C₀ := by
    rw [hmubar]
    refine (abs_sub _ _).trans ?_
    linarith [h1, h2, h3]
  have hMB0 : 0 ≤ 1 + CT * C₀ := by
    have hC0 : 0 ≤ CT * C₀ := mul_nonneg hCTpos.le hC₀0
    linarith
  -- `AK`'s level-six energy
  have hAKsq : Work.Spaces.HkSq α 6 (Work.Construction.AK α) ≤ KAK ^ 2 := by
    have hs := Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (Work.Construction.AK α))
    rw [Work.Spaces.HkNorm] at hAKnorm
    have h2 := Real.sqrt_nonneg (Work.Spaces.HkSq α 6 (Work.Construction.AK α))
    nlinarith [hAKnorm, h2, hs, hKAKpos]
  have hAKsq4 : Work.Spaces.HkSq α 4 (Work.Construction.AK α) ≤ KAK ^ 2 :=
    le_trans (Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hAKmem) hAKsq
  -- the block is the scalar `mubar` times `AK α`
  have hshape : Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg
      = fun z θ => Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
          (Work.Construction.N α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + Φg z θ)) * Work.Construction.AK α z θ := rfl
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg) := by
    rw [hshape]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hAKsmo
  have hmem : Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg) := by
    rw [hshape]
    exact Work.FTS.LocData.HkMem_const_mul α 6 _ hAKmem
  have hMBsq : (Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))) ^ 2
      ≤ (1 + CT * C₀) ^ 2 := by
    calc (Work.Construction.mubar _ _) ^ 2 = |Work.Construction.mubar _ _| ^ 2 := (sq_abs _).symm
      _ ≤ (1 + CT * C₀) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hMBex 2
  have hconst : KAK ^ 2 * (1 + CT * C₀) ^ 2 ≤ KM := by
    rw [hKM]; linarith [sq_nonneg KAK, sq_nonneg (1 + CT * C₀)]
  refine ⟨hsm, hmem, ?_, ?_⟩
  · rw [hshape, Work.FTS.StrongEps.HkSq_const_mul]
    have hSs5 : 0 ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
    have h1 : Work.Spaces.HkSq α 4 (Work.Construction.AK α)
        * (Work.Construction.mubar _ _) ^ 2 ≤ KAK ^ 2 * (1 + CT * C₀) ^ 2 :=
      mul_le_mul hAKsq4 hMBsq (sq_nonneg _) (sq_nonneg KAK)
    have h2 : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
    nlinarith [h1, hconst, hSs5, hKMpos]
  · rw [hshape, Work.FTS.StrongEps.HkSq_const_mul]
    have hSs6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
    have hSs7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
    have h1 : Work.Spaces.HkSq α 6 (Work.Construction.AK α)
        * (Work.Construction.mubar _ _) ^ 2 ≤ KAK ^ 2 * (1 + CT * C₀) ^ 2 :=
      mul_le_mul hAKsq hMBsq (sq_nonneg _) (sq_nonneg KAK)
    have h2 : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
    have h3 : (0 : ℝ) ≤ KM * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by positivity
    nlinarith [h1, hconst, hSs7, h2, h3, hKMpos]

end Work.FTS.StrongEps.E4R3.RawE6Aux
