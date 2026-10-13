/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6N0Aux/row_l12_dz` — the level-six transport row with the coefficient
`c₂ₘ(θ)·L₁₂(f)(z)·D_z f`

The row is the pairing `∫_z ∫_θ ρ·D_z^bD_θ^a(c₂ₘ·L₁₂(f)·D_z f)·D_z^bD_θ^a f` at the slots
`a + b ≤ 6` with the leaf weights `ρ ∈ IsLeafW α a`, bounded by
`C·α^{-3}·(1+|f|_{ℋ⁴})⁴·(1+|f|²_{ℋ⁶})`.

## Structure of the proof

`D_z`-Leibniz (`T5bAux2.t5bExpand` / `t5bPairExpand`) expands the differentiated coefficient as
the sum of the summands `T5bAux.t5bPiece f ρ a b k i` over `k ≤ b`, `i ≤ a`:

`t5bPiece f ρ a b k i (z,θ)
 = ρ·(D_z^kL₁₂(f))(z)·(D_θ^i c₂ₘ)(θ)·D_z^{b-k+1}D_θ^{a-i}f(z,θ)·D_z^bD_θ^af(z,θ)`;

* the **lead** summand `(k,i) = (0,0)` — the only one that sees the level-seven slot
  `D_z^{b+1}D_θ^a f` — is the radial self-pairing of `T5bAux.T5bZeroTerm` (`HkMem α 7 f` is used
  there, in the integrability of the `z∂_z`-slot);
* every **other** summand is bounded pointwise by `T5bAux.t5bPieceBound` (its `f`-slots have
  order `≤ 6`), its product-integrability being `T5bAux.t5bPiecePtwIntegrable`;
* the two `L₁₂`-jet bounds are `L12Sup4` (order `≤ 4`) and `L12Sup6` (order `≤ 6`), and the
  angular jets of `c₂ₘ` are `T5bAux.c2mJets`;
* the sum over the `(k,i)` and the closing arithmetic are `t5bSumBound` / `t5bFinalArith`
  (`T5bAssem`), using `X²Y ≤ (1+X)⁴(1+Y²)` etc.

The assembly below is the level-six row's Leibniz/integrability/AM–GM glue: this same claim,
with its proof, is also recorded as `Work.FTS.StrongPersist.H6Pair6Aux.T5bRow` in the parent
directory (`Submission/Work/FTS/StrongPersist/H6Pair6Aux/T5bRow.lean`), the two files having
been produced from the same set of proved pieces; the proof term here is independent of that
module (it imports only the pieces `T5bZeroTerm`, `t5bPieceBound`, `t5bPiecePtwIntegrable`,
`t5bExpand`/`t5bPairExpand`, `L12Sup4`, `L12Sup6`, `c2mJets`, `t5bSumBound`, `t5bFinalArith`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAssem
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroTerm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPieceBound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem row_l12_dz : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
            * Work.Spaces.Dz f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cc, hCcpos, hCcsm, hCcbd, hCcg⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨C0, hC0pos, hC0bnd⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroTerm
  obtain ⟨C4, hC4pos, hsup4raw⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨C6, hC6pos, hsup6raw⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  refine ⟨49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ (4096 * 4096) * 49 * Cc * (2 * C4 + C6) := by positivity
    linarith [hC0pos]
  intro α hα f a b ρ hso hm6 hm7 hvan haxis hl12 hab hleaf
  have hα0 : (0 : ℝ) < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the `L₁₂`-jet bounds
  have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα0 hα1 hso hm7 (by norm_num)
    exact (h.of_le (by norm_num)).congr
      (fun z _ => (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm)
  have hsup4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hsup4raw α f hα0 hα1 hso hm6 hl12 k hk z hz
  have hsup6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun k hk z hz => hsup6raw α f hα0 hα1 hso hm6 hm7 hl12 k hk z hz
  -- ## the coefficient function
  set V : ℝ → ℝ → ℝ := fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
    * Work.Spaces.Dz f z θ with hV
  -- ## the a.e. expansion of the paired integrand
  have hpt : (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      =ᵐ[((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i p) := by
    refine ae_prod_Ioo (p := fun z θ => ρ z θ * Work.Spaces.mixed b a V z θ
        * Work.Spaces.mixed b a f z θ
        = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
            ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i (z, θ)) ?_
    intro θ hθ z hz
    have h := t5bPairExpand (ρ := ρ) hso hCcsm hXsm hab z θ hz hθ.1 hθ.2
    rwa [← hV] at h
  -- ## integrability of the individual summands
  have hIntPiece : ∀ k ∈ Finset.range (b + 1), ∀ i ∈ Finset.range (a + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => t5bPiece f ρ a b k i p)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro k hk i hi
    exact (Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable hα0 hα1 hso hCcsm
      hm6 hm7 hab hleaf hC4pos.le hC6pos.le hCcpos.le hsup4 hsup6 hCcbd hCcg
      (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2
  -- ## integrability of the sum and of the total integrand
  have hIntSum : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * t5bPiece f ρ a b k i p)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integrable_finsetSum _ fun k hk => ?_
    refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
    exact (hIntPiece k hk i hi).const_mul _
  have hIntTot : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hIntSum.congr hpt.symm
  -- ## the pairing as a product integral
  have hbridge : Work.FTS.TransportS.slotPairing ρ a b V f
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.TransportS.slotPairing]
    exact (MeasureTheory.integral_prod _ hIntTot).symm
  -- ## the expansion of the product integral
  have hlin : (∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a V p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
          ((b.choose k : ℝ) * (a.choose i : ℝ))
            * (∫ p, t5bPiece f ρ a b k i p
                ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_congr_ae hpt]
    rw [MeasureTheory.integral_finsetSum _ (fun k hk =>
      MeasureTheory.integrable_finsetSum _ fun i hi => (hIntPiece k hk i hi).const_mul _)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun i hi => (hIntPiece k hk i hi).const_mul _)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_const_mul]
  -- ## the per-term bounds
  have hterm : ∀ k ∈ Finset.range (b + 1), ∀ i ∈ Finset.range (a + 1),
      |∫ p, t5bPiece f ρ a b k i p
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
        ≤ (if k = 0 ∧ i = 0
           then C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)
           else ((b.choose k : ℝ) * (a.choose i : ℝ)) * Cc *
             (if k ≤ 4
              then C4 * Work.Spaces.HkNorm α 4 f
                   * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                      + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
              else C6 * Work.Spaces.HkNorm α 6 f
                   * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) := by
    intro k hk i hi
    have hkb : k ≤ b := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hia : i ≤ a := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hiter : (∫ p, t5bPiece f ρ a b k i p
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t5bPiece f ρ a b k i (z, θ) :=
      MeasureTheory.integral_prod _ (hIntPiece k hk i hi)
    rw [hiter]
    by_cases h00 : k = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [if_pos ⟨rfl, rfl⟩]
      have hcongr : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, t5bPiece f ρ a b 0 0 (z, θ))
          = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
              * (Work.Construction.c2m θ * Work.Construction.L12 f z)
              * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only [t5bPiece, Work.Elliptic.DzdIter_zero, Work.Spaces.DthIter_zero,
          Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
        ring
      rw [hcongr]
      exact hC0bnd α hα f a b ρ hso hm6 hm7 hvan haxis hl12 hab hleaf
    · rw [if_neg h00]
      exact Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPieceBound hα0 hα1 hso hm6 hab
        hleaf hC4pos.le hC6pos.le hCcpos.le hsup4 hsup6 hCcbd hCcg hkb hia h00
  -- ## normal form of the per-term bounds
  have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hZnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hN6sq : Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f
      = Work.Spaces.HkSq α 6 f := by
    rw [Work.Spaces.HkNorm, ← pow_two, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
  have hS2 : (1 + Work.Spaces.HkNorm α 6 f ^ 2) = (1 + Work.Spaces.HkSq α 6 f) := by
    rw [pow_two, hN6sq]
  -- ## the sum of the per-term bounds
  have hmain : (∑ k ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ((b.choose k : ℝ) * (a.choose i : ℝ))
          * |∫ p, t5bPiece f ρ a b k i p
              ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|)
      ≤ 49 * (C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkNorm α 6 f ^ 2)
          + 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)))) := by
    refine le_trans (Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => ?_)
      (t5bSumBound hC0pos.le hCcpos.le hC4pos.le hC6pos.le hXnn hZnn hab)
    by_cases h00 : k = 0 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [if_pos ⟨rfl, rfl⟩, hS2]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
      have h := hterm 0 hk 0 hi
      rwa [if_pos ⟨rfl, rfl⟩] at h
    · rw [if_neg h00]
      have h := hterm k hk i hi
      rw [if_neg h00] at h
      have hb : b ≤ 6 := by omega
      have ha : a ≤ 6 := by omega
      have hc1 : ((b.choose k : ℕ) : ℝ) ≤ 64 := by
        have h2 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
        have h3 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb
        exact_mod_cast (le_trans h2 (le_trans h3 (by norm_num)))
      have hc2 : ((a.choose i : ℕ) : ℝ) ≤ 64 := by
        have h2 : a.choose i ≤ 2 ^ a := Nat.choose_le_two_pow a i
        have h3 : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) ha
        exact_mod_cast (le_trans h2 (le_trans h3 (by norm_num)))
      have hcf0 : (0 : ℝ) ≤ (b.choose k : ℝ) * (a.choose i : ℝ) := by positivity
      have hcf : ((b.choose k : ℝ) * (a.choose i : ℝ)) ≤ 4096 := by nlinarith
      have hcf2 : ((b.choose k : ℝ) * (a.choose i : ℝ))
            * ((b.choose k : ℝ) * (a.choose i : ℝ)) ≤ 4096 * 4096 := by
        nlinarith [hcf0, hcf]
      have hAnn : (0 : ℝ) ≤ C4 * Work.Spaces.HkNorm α 4 f
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
               + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f) := by positivity
      have hBnn : (0 : ℝ) ≤ C6 * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by positivity
      have hE : (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            else C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))
          ≤ C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) := by
        by_cases hk4 : k ≤ 4
        · rw [if_pos hk4]; linarith
        · rw [if_neg hk4]; linarith
      have hCE : Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            else C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))
          ≤ Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) :=
        mul_le_mul_of_nonneg_left hE hCcpos.le
      calc ((b.choose k : ℝ) * (a.choose i : ℝ))
            * |∫ p, t5bPiece f ρ a b k i p
                ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))|
          ≤ ((b.choose k : ℝ) * (a.choose i : ℝ))
              * (((b.choose k : ℝ) * (a.choose i : ℝ)) * Cc
                * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                    * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                       + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
                  else C6 * Work.Spaces.HkNorm α 6 f
                    * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) :=
            mul_le_mul_of_nonneg_left h hcf0
        _ = (((b.choose k : ℝ) * (a.choose i : ℝ))
              * ((b.choose k : ℝ) * (a.choose i : ℝ)))
              * (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                  * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                     + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
                else C6 * Work.Spaces.HkNorm α 6 f
                  * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) := by ring
        _ ≤ (4096 * 4096) * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) :=
            mul_le_mul hcf2 hCE (by positivity) (by norm_num)
        _ = 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f))) := by ring
  -- ## the bound on the pairing
  have hbound : |Work.FTS.TransportS.slotPairing ρ a b V f|
      ≤ 49 * (C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkNorm α 6 f ^ 2)
          + 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)))) := by
    rw [hbridge, hlin]
    refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun k hk => Finset.abs_sum_le_sum_abs _ _)) ?_
    refine le_trans (le_of_eq ?_) hmain
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun i hi => ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  -- ## the final bound
  have hfin := t5bFinalArith (X := Work.Spaces.HkNorm α 4 f)
    (Y := Work.Spaces.HkNorm α 6 f) (α := α)
    hC0pos.le hCcpos.le hC4pos.le hC6pos.le hXnn hZnn hα0 hα1
  have hXn : Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f := rfl
  calc |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
          * Work.Spaces.Dz f z θ) f|
      = |Work.FTS.TransportS.slotPairing ρ a b V f| := by rw [hV]
    _ ≤ 49 * (C0 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkNorm α 6 f ^ 2)
          + 4096 * 4096 * (Cc * (C4 * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                 + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
            + C6 * Work.Spaces.HkNorm α 6 f
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)))) := hbound
    _ ≤ (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkNorm α 6 f ^ 2) := hfin
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          rw [hS2]
    _ = (49 * C0 + (4096 * 4096) * 49 * Cc * (2 * C4 + C6) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
          rw [hXn]

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
