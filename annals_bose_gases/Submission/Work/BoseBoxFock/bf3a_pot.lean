import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.potsplit_integrable
import Submission.Work.BoseFixB1.chemPair_eq_qLHSword
import Submission.Work.BoseFixB2.Band.integrableOn_potOnePiece
import Submission.Work.BoseFixB2.Band.integrableOn_potPairPiece
import Submission.Work.BoseFixR.integrableOn_chemP_loc
import Submission.Work.BoseFixR.integrableOn_wPairC_pair_loc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.bf3a_pot` — the potential rows of the BF3a reduction

The BF3a node (`box_to_model`, FS `prop:Hamilton2ndQuant`, l. 1668–1683) splits the
box word `wordB = kinFormB + chemPartB + pairPartB` against the first-quantised
`H_Λ^{2nd}` word `W₂ = W2kinB + W2potB`.  This module proves the **potential half**:

    `W2potB − C·errB·normB ≤ chemPartB + pairPartB + (b/100)·(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H)`

on the class `Adm v ε₀ μ`, `n ≤ 2μℓ³`, from FS `lem:potsplit` together with the
`NodeB3B` (`lem:Q3-splitting1`) hypothesis and the manifest-square nonnegativity of `Q₄`.

## The three ingredients

1. `chemPair_eq_qLHSword_honest` — `chemPartB + pairPartB = qLHSword` at the honest
   kernels `wLoc ℓ v 0 = wPairC ℓ v`, `wLoc ℓ (g₀ v h) 0`.  This is the *integrability*
   repair of `Work.BoseFixB1.chemPair_eq_qLHSword` (which is **false** without it; the
   ambient hypotheses `MemLp v 1`, `tsupport v ⊆ ball 0 R` supply the integrability of the
   two summands).  The pointwise identity of the brackets is
   `Work.BoseBox.bracket_qLHSword_eq_potWordU`; the integral split is
   `Work.BoseFixB1.chemPair_eq_qLHSword_of_integrable`.

2. `potsplit_integrable` (`Submission.Work.BoseBoxFock.potsplit_integrable`) — FS
   `lem:potsplit`: `qLHSword = q₀ + q₁ + q₂ + q₃ + q₄` at kernels satisfying
   `w₁ = w(1−ω)`, `w₂ = w(1−ω²)`, with the *integrability* of the finitely many pieces
   in place of continuity of the kernels (which the honest kernels do not have).

3. `Submission.BoseGases.q4_nonneg` — `q₄ ≥ 0` for a pointwise nonnegative kernel, and
   the `NodeB3B` hypothesis, which pays `q₃^{low}` by `q₃ + ¼q₄ + (b/100)(ℓ⁻²n₊ + …)`.

## Value conventions

`wPairC` is `wPair` curried; `wLoc ℓ g 0 = wPairC ℓ g` as functions
(`wLoc_zero_eq_wPairC_fun`), and the *box* fibre `w1Fibre ℓ (wPairC ℓ g) z` is the
whole-space `y`-integral `∫_y wLoc ℓ g 0 z y` (`χ_ℓ` vanishes off the cube).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- With translation parameter `u = 0` the localisation kernel `wLoc` *is* the
χ-renormalised two-body kernel `wPairC`, as functions (function-level companion of
`Work.BoseFixR.wLoc_zero_eq_wPairC`). -/
lemma wLoc_zero_eq_wPairC_fun (ℓ : ℝ) (g : ℝ³ → ℝ) :
    Submission.BoseGases.wLoc ℓ g 0 = Submission.BoseGases.wPairC ℓ g := by
  funext a b
  rw [Submission.BoseGases.wPairC_apply]
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-- The box fibre of the χ-renormalised kernel equals the whole-space `y`-integral of the
localisation kernel at `u = 0` (the `χ_ℓ` factor vanishes off the cube). -/
lemma w1Fibre_wPairC_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (g : ℝ³ → ℝ) (z : ℝ³) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ g) z
      = ∫ y : ℝ³, Submission.BoseGases.wLoc ℓ g 0 z y := by
  rw [← wLoc_zero_eq_wPairC_fun ℓ g]
  unfold Submission.BoseGases.w1Fibre
  exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    have hz : Submission.BoseGases.chiU ℓ 0 y = 0 := by
      simp only [Submission.BoseGases.chiU, sub_zero]
      exact Submission.BoseGases.chiScale_eq_zero_of_notMem_acube hℓ hy
    simp only [Submission.BoseGases.wLoc, hz, mul_zero])

/-- `w1Fibre ℓ (wPairC ℓ g)` is integrable on the box for a locally integrable numerator
`g`: the box fibre of `wPairC ℓ g` is the whole-space fibre of `wLoc ℓ g 0`, i.e. `chemP`. -/
lemma w1Fibre_wPairC_integrable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ³ → ℝ}
    (hg : MeasureTheory.LocallyIntegrable g) (i : Fin N) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ g) (x i))
      (Submission.BoseGases.abox N ℓ) := by
  refine (Work.BoseFixR.integrableOn_chemP_loc (n := N) hℓ hg i).congr_fun ?_
    (Submission.BoseGases.abox_measurable N ℓ)
  intro x _
  simp only [Work.BoseFixR.chemP]
  rw [w1Fibre_wPairC_eq ℓ hℓ g (x i)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y =>
    (congrFun (congrFun (wLoc_zero_eq_wPairC_fun ℓ g) (x i)) y).symm))

/-- Multiplying an integrable function on the box by the square of a continuous state
preserves integrability (the state is bounded on the compact box). -/
lemma integrableOn_sq_mul {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {f : Submission.BoseGases.X N → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Submission.BoseGases.abox N ℓ)) :
    MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2 * f x) (Submission.BoseGases.abox N ℓ) := by
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
    (hΦc.pow 2).continuousOn
  have hbdd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      ‖(Φ x) ^ 2‖ ≤ B :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mpr
      (Filter.Eventually.of_forall (fun x hx => by
        simpa [Real.norm_eq_abs] using hB x hx))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    ((hΦc.pow 2).aestronglyMeasurable).mono_measure MeasureTheory.Measure.restrict_le_self
  exact (hf.mul_bdd hmeas hbdd).congr (Filter.Eventually.of_forall (fun x => by ring))

/-- **`chemPartB + pairPartB = qLHSword`** at the honest kernels `wPairC ℓ v`,
`wPairC ℓ (g₀ v h)` — the integrability-repaired form of
`Work.BoseFixB1.chemPair_eq_qLHSword` (which is false without the integrability
hypotheses; here `MemLp v 1` and `tsupport v ⊆ ball 0 R` supply them). -/
theorem chemPair_eq_qLHSword_honest {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseKinLoc.chemPartB N (Submission.BoseGases.g0 v h) ℓ μ Φ
      + Work.BoseKinLoc.pairPartB N v ℓ Φ
      = Submission.BoseGases.qLHSword (N := N) ℓ μ
          (Submission.BoseGases.wPairC ℓ v)
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := by
  have hg0 : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hvint : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  -- the chemical half
  have hone : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
        (∫ y : ℝ³, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
      (Submission.BoseGases.abox N ℓ) :=
    fun i => integrableOn_sq_mul hℓ hΦc
      (Work.BoseFixB2.Band.integrableOn_potOnePiece (N := N) hℓ hg0 i)
  have hA : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
        (-μ * (∑ i : Fin N, ∫ y : ℝ³,
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox N ℓ) := by
    have hsum : MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N => ∑ i : Fin N, (Φ x) ^ 2 *
          (∫ y : ℝ³, Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
        (Submission.BoseGases.abox N ℓ) :=
      integrable_finsetSum Finset.univ (fun i _ => hone i)
    refine (hsum.const_mul (-μ)).congr ?_
    filter_upwards with x
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- the pair half, as `potWordU − (chemical half)` (this keeps the ordered-pair index
  -- type of `potWordU`, which is the one `pairPartB` uses)
  have hAB : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
      (Submission.BoseGases.abox N ℓ) :=
    integrableOn_sq_mul hℓ hΦc
      (Work.BoseFixB2.Pot.potWordU_integrable (v := v) h (R := R) hR hv_supp hv1
        (μ := μ) (n := N) ℓ)
  have hB : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox N ℓ) := by
    refine (hAB.sub hA).congr ?_
    filter_upwards with x
    simp only [Pi.sub_apply]
    unfold Work.BoseKinLoc.potWordU
    ring
  exact Work.BoseFixB1.chemPair_eq_qLHSword_of_integrable h hvrad hℓ hΦc hA hB

/-! ## The BF3a potential bound -/

/-- **BF3a, potential rows.**  The potential part `W2potB` of the first-quantised
`H_Λ^{2nd}` word is dominated by the box potential word `chemPartB + pairPartB` plus the
reserves `(b/100)(ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H)`, up to the `errB` error — for every state in the
class `Adm v ε₀ μ`, `n ≤ 2μℓ³`.  Uses FS `lem:potsplit` (`potsplit_integrable` +
`chemPair_eq_qLHSword_honest`), the `Q₄ ≥ 0` square and the `NodeB3B` hypothesis. -/
theorem bf3a_pot (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc : Work.BoseBoxFix.LowCut) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          Work.BoseBoxFock.W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
              - C * Work.BoseBoxFock.errB v R μ * Work.BoseBoxFix.normB v μ n Φ
            ≤ Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h)
                (Work.BoseBox.sideAt μ (BoseGases.a v)) μ (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseKinLoc.pairPartB n v (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Φ : Submission.BoseGases.X n → ℝ)
              + ((Work.BoseBox.paramsAt μ (BoseGases.a v)).b / 100) *
                  (Work.BoseBox.sideAt μ (BoseGases.a v) ^ (-2 : ℤ)
                      * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
                          (Φ : Submission.BoseGases.X n → ℝ)
                    + (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT *
                        ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                          * Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (-2 : ℤ)
                      * Work.BoseBoxFix.nPlusHB (Work.BoseBox.sideAt μ (BoseGases.a v))
                          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                          (Φ : Submission.BoseGases.X n → ℝ)) := by
  obtain ⟨C, ε₀, hC0, hε0, hB3'⟩ := hB3
  refine ⟨C, ε₀, hC0, hε0, ?_⟩
  intro μ hAdm n Φ hnc
  have hμ : 0 < μ := hAdm.1
  let ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v)
  have hℓ : 0 < ℓ := Work.BoseBox.sideAt_pos hμ hav
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- `NodeB3B` at this state, kernels in `wPairC` form
  have h3 := hB3' μ hAdm n Φ hnc
  rw [wLoc_zero_eq_wPairC_fun (Work.BoseBox.sideAt μ (BoseGases.a v))
    (Submission.BoseGases.g0 v h)] at h3
  rw [wLoc_zero_eq_wPairC_fun (Work.BoseBox.sideAt μ (BoseGases.a v)) v] at h3
  -- FS `lem:potsplit` at the honest kernels
  have hsplit : Submission.BoseGases.qLHSword (N := n) ℓ μ
        (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
        (Φ : Submission.BoseGases.X n → ℝ)
      = Submission.BoseGases.q0word (N := n) ℓ μ
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h))
          (Φ : Submission.BoseGases.X n → ℝ)
        + Submission.BoseGases.q1word (N := n) ℓ μ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h))
            (Φ : Submission.BoseGases.X n → ℝ)
        + Submission.BoseGases.q2word (N := n) ℓ μ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h))
            (Φ : Submission.BoseGases.X n → ℝ)
        + Submission.BoseGases.q3word (N := n) ℓ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
            (Φ : Submission.BoseGases.X n → ℝ)
        + Submission.BoseGases.q4word (N := n) ℓ (Submission.BoseGases.wPairC ℓ v)
            (Submission.BoseGases.omC (Classical.choose h))
            (Φ : Submission.BoseGases.X n → ℝ) := by
    have hvloc : MeasureTheory.LocallyIntegrable v :=
      (MeasureTheory.memLp_one_iff_integrable.mp hv1).locallyIntegrable
    have hg0loc : MeasureTheory.LocallyIntegrable (Submission.BoseGases.g0 v h) :=
      (Submission.BoseGases.g0_integrable hR hv_supp h).locallyIntegrable
    have hg2loc : MeasureTheory.LocallyIntegrable (Submission.BoseGases.g2 v h) :=
      (Submission.BoseGases.g2_integrable hR hv hvrad hv_supp h).locallyIntegrable
    exact potsplit_integrable (N := n) (ℓ := ℓ) (μ := μ)
      (w := Submission.BoseGases.wPairC ℓ v)
      (w1 := Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
      (w2 := Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h))
      (om := Submission.BoseGases.omC (Classical.choose h))
      (Φ := (Φ : Submission.BoseGases.X n → ℝ))
      hℓ
      (Submission.BoseGases.wPairC_v_sym hvrad ℓ)
      (Submission.BoseGases.omC_chosen_sym h)
      (Submission.BoseGases.w1rel_chosen h ℓ)
      (Submission.BoseGases.w2rel_chosen h ℓ)
      hΦc
      (fun i => w1Fibre_wPairC_integrable hℓ hg0loc i)
      (fun i _ hij => Work.BoseFixR.integrableOn_wPairC_pair_loc hℓ hvloc hij)
      (fun i _ hij => Work.BoseFixR.integrableOn_wPairC_pair_loc hℓ hg0loc hij)
      (fun i _ hij => Work.BoseFixR.integrableOn_wPairC_pair_loc hℓ hg2loc hij)
  -- `chemPartB + pairPartB = qLHSword`
  have hcp := chemPair_eq_qLHSword_honest (μ := μ) h hv1 hvrad hR hv_supp hℓ hΦc
  -- `Q₄` is a manifest square
  have hq4 : 0 ≤ Submission.BoseGases.q4word (N := n) ℓ (Submission.BoseGases.wPairC ℓ v)
      (Submission.BoseGases.omC (Classical.choose h)) (Φ : Submission.BoseGases.X n → ℝ) :=
    Submission.BoseGases.q4_nonneg hℓ (Submission.BoseGases.wPairC_nonneg hv ℓ)
  -- everything to the `sideAt` spelling of the goal
  rw [show ℓ = Work.BoseBox.sideAt μ (BoseGases.a v) from rfl] at hsplit hcp hq4
  -- `W2potB` unfolded, at the `wPairC` kernels
  have hW2 : W2potB v h μ n fc (Φ : Submission.BoseGases.X n → ℝ)
      = Submission.BoseGases.q0word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g0 v h))
          (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.g2 v h))
          (Φ : Submission.BoseGases.X n → ℝ)
        + Submission.BoseGases.q1word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h))
            (Φ : Submission.BoseGases.X n → ℝ)
        + Submission.BoseGases.q2word (N := n) (Work.BoseBox.sideAt μ (BoseGases.a v)) μ
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g2 v h))
            (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseBoxFix.q3lowWord fc
            ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹
            (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Submission.BoseGases.wPairC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Submission.BoseGases.g0 v h))
            (Φ : Submission.BoseGases.X n → ℝ) := by
    simp only [W2potB]
    rw [wLoc_zero_eq_wPairC_fun (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Submission.BoseGases.g0 v h),
      wLoc_zero_eq_wPairC_fun (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Submission.BoseGases.g2 v h)]
  -- the error term in the `NodeB3B` normal form
  have herr : C * errB v R μ * Work.BoseBoxFix.normB v μ n Φ
      = C * μ ^ 2 * BoseGases.a v * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 *
          ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              ^ (2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).M - 1))
            + R ^ 2 / Work.BoseBox.sideAt μ (BoseGases.a v) ^ 2)
          * Work.BoseBoxFix.normB v μ n Φ := by
    simp only [errB]
    ring
  rw [hW2, herr]
  linarith [h3, hq4, hsplit, hcp]

end Work.BoseBoxFock

