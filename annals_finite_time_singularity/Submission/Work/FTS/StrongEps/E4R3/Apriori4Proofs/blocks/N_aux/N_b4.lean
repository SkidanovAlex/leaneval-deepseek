import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.SmHm
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Aux
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_ctx
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_g1
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_g2
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_s
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.StrongEps.H5.Nb5Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.N_b4` — the level-`4` semi-tame estimate of the `N`-block, `α`-free

The proof is the assembly of four ingredients, all in this directory:

* `N_aux.N_b4_ctx` — the pricing context `NB4Ctx C C₀ Ce Cs α Φs w Φg` at an `α`-free constant
  `C` (`N_aux.NB4Aux` holds the structure and the absorption lemmas `mulQo_absorb`,
  `mulW_absorb`);
* `N_aux.N_b4_g1`, `N_aux.N_b4_g2`, `N_aux.N_b4_s` — the twenty pieces
  `ClassCRHS.NBlk α w Φs Φg k`, each `ℋ⁴`-honest and priced by `K·(1 + HkNorm α 5 w)`;
* the identity `N = ∑_{k<20} NBlk k` on the open quadrant, from `ClassCRHS.nb_data` (its `B`-slot
  is instantiated with `HkNorm α 6 w`), and the closure `ClassCRHS.HkSumOpenClosure`.

Everything is summed with `HkNorm_finset_sum_le` (`√(2²⁰) = 1024`, twenty pieces) and the final
arithmetic `(1 + HkNorm α 5 w)² ≤ 2(1 + HkSq α 5 w)`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The level-4 semi-tame estimate of the `N`-block**, with an `α`-free constant.

This is the `b4` field of `BData α w K (blkN α Φs w Φg)`: the ℋ⁴-energy of
`N α (Ftot α w) (Φs + Φg)`, priced by `1 + HkSq α 5 w` (the `HkNorm α 5 w` of the slot shifts).

Route (see `Submission/Work/FTS/StrongEps/E4R3/Apriori4Proofs/blocks/N_aux/NOTES_N_BData.md`,
§1–§2 for the details and the list of available α-free atom prices):

* use the twenty-piece decomposition `ClassCRHS.NBlk α w Φs Φg` (`ClassCRHS.HkMemXnNDefs`), whose
  sum equals `N α (Ftot α w) (Φs+Φg)` on the open quadrant (`ClassCRHS.HkMemXnNIdent`);
* price every piece at level `4` with the level-4 product rules of `OpenPkg`
  (`prod_field`, `wprod_field_winf`, `ang_mul_HkSq_le`): each coefficient is α-small at level 4
  (perturbed coefficients have `HkNorm α 4 ≤ Ce·Xn α w ≤ Ce C₀ α²` by `EllPkgGo`; the star
  coefficients have `WlInf α 4 ≤ Cs α` by `StarPkg6`; `FK w` has `HkNorm α 4 ≤ C·Xn α w`;
  the fixed atoms are bounded by `alpha`-powers by `Nonlinear.FstarPkg`/`H5.fixed_atoms5`), and
  each slot is either a `w`-slot (`HkNorm α 4 ≤ HkNorm α 5 w` by the level shifts
  `StrongPersist.H6Aux.HkSq_Dth_le_succ'`, `HkSq_Dz_le_succ'`) or an `F_*`-slot (`HkNorm α 4 ≤ C`);
  after squaring, the `α^{-1}` of the product rule is absorbed by the α-smallness of the
  coefficient, so a single `K` independent of `α ∈ (0,1]` works;
* sum with the additivity of `HkSq` and conclude
  `HkNorm α 4 N ≤ C·(1 + HkNorm α 5 w)`, hence
  `HkSq α 4 N ≤ 2C²(1 + HkSq α 5 w)`.

`ClassCRHS.HkMemXnN`/`nb_data` is the template, but it carries an extra `HkNorm α 6 w ≤ B` with
`B` fixed before `w`, and its constants depend on `α`; both must be removed here. -/
theorem N_b4 (C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.Spaces.HkSq α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨C, hCpos, hctx⟩ := N_b4_ctx C₀ Ce Cs
  obtain ⟨K1, hK1, hg1⟩ := N_b4_g1 C C₀ Ce Cs
  obtain ⟨K2, hK2, hg2⟩ := N_b4_g2 C C₀ Ce Cs
  obtain ⟨K3, hK3, hs⟩ := N_b4_s C C₀ Ce Cs
  obtain ⟨C1, hC1, hs1⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
  obtain ⟨C2, hC2, hs2⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
  refine ⟨(1024 * 20 * (K1 + K2 + K3)) ^ 2 * 2 + 1, by positivity, ?_⟩
  intro α hαmem Φs w Φg hw hXw hzero hell hK6 hstar
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hstar2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hstar.toStarPkgo2
  -- the pricing context of the twenty pieces
  have hcx : NB4Ctx C C₀ Ce Cs α Φs w Φg := hctx α hαmem Φs w Φg hw hXw hell hstar
  -- the identity `N = ∑_{k<20} NBlk k` on the open quadrant (and the `SmoothOpen` of the pieces),
  -- through `nb_data` at `B := HkNorm α 6 w`
  obtain ⟨Kbig, hKbig, hdata⟩ :=
    Work.FTS.StrongEps.ClassCRHS.nb_data hαmem hC1 hC2 (hs1 α hαmem) (hs2 α hαmem)
  obtain ⟨hsmAll, -, hid⟩ := hdata hw hXw (le_refl (Work.Spaces.HkNorm α 6 w)) hell hstar2
  -- the per-piece data, in the form consumed by `HkSumOpenClosure`
  set K : ℝ := K1 + K2 + K3 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith [hK1.le, hK2.le, hK3.le]
  have hGnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w := zero_le_G
  have hpiece : ∀ k ∈ Finset.range 20,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    have key : ∀ k ∈ ({0, 2, 4, 6, 8} : Finset ℕ),
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
      intro k hk'
      obtain ⟨hm, hx⟩ := hg1 α hαmem Φs w Φg hcx k hk'
      exact ⟨hm, le_trans hx (mul_le_mul_of_nonneg_right
        (by rw [hKdef]; linarith [hK2.le, hK3.le] : K1 ≤ K) hGnn)⟩
    have key2 : ∀ k ∈ ({10, 12, 14, 16, 18} : Finset ℕ),
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
      intro k hk'
      obtain ⟨hm, hx⟩ := hg2 α hαmem Φs w Φg hcx k hk'
      exact ⟨hm, le_trans hx (mul_le_mul_of_nonneg_right
        (by rw [hKdef]; linarith [hK1.le, hK3.le] : K2 ≤ K) hGnn)⟩
    have key3 : ∀ k ∈ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19} : Finset ℕ),
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
      intro k hk'
      obtain ⟨hm, hx⟩ := hs α hαmem Φs w Φg hcx k hk'
      exact ⟨hm, le_trans hx (mul_le_mul_of_nonneg_right
        (by rw [hKdef]; linarith [hK1.le, hK2.le] : K3 ≤ K) hGnn)⟩
    interval_cases k
    · exact key 0 (by decide)
    · exact key3 1 (by decide)
    · exact key 2 (by decide)
    · exact key3 3 (by decide)
    · exact key 4 (by decide)
    · exact key3 5 (by decide)
    · exact key 6 (by decide)
    · exact key3 7 (by decide)
    · exact key 8 (by decide)
    · exact key3 9 (by decide)
    · exact key2 10 (by decide)
    · exact key3 11 (by decide)
    · exact key2 12 (by decide)
    · exact key3 13 (by decide)
    · exact key2 14 (by decide)
    · exact key3 15 (by decide)
    · exact key2 16 (by decide)
    · exact key3 17 (by decide)
    · exact key2 18 (by decide)
    · exact key3 19 (by decide)
  -- the closure
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
        (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
        p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hw hell hstar2).2.2.2.2 α 4
  obtain ⟨hmemN, hbndN⟩ := Work.FTS.StrongEps.ClassCRHS.HkSumOpenClosure hα0 hcont hsmAll
    (fun k hk => (hpiece k hk).1) (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  -- the sum bound
  have hsum : (∑ k ∈ Finset.range 20,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k))
      ≤ 20 * (K * (1 + Work.Spaces.HkNorm α 5 w)) := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpiece k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have hsqrt : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hXnN : Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) ≤ 1024 * (20 * (K * (1 + Work.Spaces.HkNorm α 5 w))) := by
    refine le_trans hbndN ?_
    rw [hsqrt]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  -- conclude
  have hsq : Work.Spaces.HkSq α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ))
      = (Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ))) ^ 2 := by
    have h1 : Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))
        = Real.sqrt (Work.Spaces.HkSq α 4 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ))) := rfl
    rw [h1, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
  rw [hsq]
  have hG2 : (1 + Work.Spaces.HkNorm α 5 w) ^ 2 ≤ 2 * (1 + Work.Spaces.HkSq α 5 w) := by
    have h5 : (Work.Spaces.HkNorm α 5 w) ^ 2 = Work.Spaces.HkSq α 5 w := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5 w)]
    nlinarith [h5, sq_nonneg (Work.Spaces.HkNorm α 5 w - 1)]
  have hstep : (Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ))) ^ 2
      ≤ (1024 * 20 * K) ^ 2 * (2 * (1 + Work.Spaces.HkSq α 5 w)) := by
    have h1 : (1024 * (20 * (K * (1 + Work.Spaces.HkNorm α 5 w)))) ^ 2
        = (1024 * 20 * K) ^ 2 * (1 + Work.Spaces.HkNorm α 5 w) ^ 2 := by ring
    have h2 : (Work.FTS.Nonlin.Xn α (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))) ^ 2
        ≤ (1024 * (20 * (K * (1 + Work.Spaces.HkNorm α 5 w)))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hXnN 2
    rw [h1] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_left hG2 (sq_nonneg _))
  have hfin : (1024 * 20 * K) ^ 2 * (2 * (1 + Work.Spaces.HkSq α 5 w))
      ≤ ((1024 * 20 * K) ^ 2 * 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
    have hnn : 0 ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith [Work.Spaces.HkSq_nonneg α 5 w]
    nlinarith [hnn, sq_nonneg (1024 * 20 * K)]
  exact le_trans hstep hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
