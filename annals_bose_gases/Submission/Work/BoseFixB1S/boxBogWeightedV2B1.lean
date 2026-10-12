import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxBogWeightedV2B1` — **FALSE as written** (state hypothesis too weak)

Verdict: **mis-stated / `declare_false`.**  See
`Submission/Work/BoseFixB1S/FINDING_boxBogWeightedV2B1_FALSE.md` for the full diagnosis.

Summary.  The statement is FS `lm:appbogolubov` (`eq:refinedaprioribog`) at the sliding box with
the box-mass-weighted payer, and it is *true for smooth states* — but it quantifies over merely
`Continuous Φ`, whereas the source (and the corpus's own proved D1
`SmallBoxD1Final.lm_appbogolubov_pWord_holds`) require `ContDiff ℝ ∞ Φ`.  The right-hand side's
spectral word `tBwordKinInd` is an integral over all `p ∈ ℝ³` of a *nonnegative* integrand; for a
state whose windowed slot fibre is not in `H¹` that integral diverges, so (Lean's Bochner
convention for a nonnegative non-integrable function, `integral_undef`) its value is `0` — while
the pairing `boxA2` stays an honest integral and, as the workspace itself recorded
(`SmallBoxA0/README.md` §28.5), is unbounded below like `−γ₀‖𝒲‖₂/(2√V)`, i.e. `−Ω(V^{−1/2})`,
against a demand of `O(V^{−1})` for `C` fixed.  Hence for every fixed `C` there are admissible
data (`V = (ℓd)³` large, `sbCut μ (a v) ~ V^{−1/2}`, `u = 0`, a small non-`H¹` perturbation of
the pairing-optimising state) violating the conclusion.  The fix is to require
`ContDiff ℝ ∞ Φ` (or integrability of the `p`-integrand), as in the source.

The sign toolkit below is kept: it is needed by any correct version of the statement.

-/

namespace Work.BoseFixB1S

/-! ## Elementary sign facts for the statement (needed by any proof)

The target's left-hand side is a sum of terms each of which is `−(nonnegative scalar)`, so any
proof reduces it to a lower bound on `tBwordKinInd + boxA2`.  The scalar facts are collected
here.  (`M2 − M1 ≥ 0` for the sliding kernels — the remaining scalar fact — is
`wSmallPair_g2_eq_mul` (+ `0 ≤ w` a.e.) transported through the integrability of the localised
kernels; see the status note `FINDING_boxBogWeightedV2B1_status.md`.) -/

/-- `1 + |log y| ≥ 0`. -/
lemma one_add_abs_log_nonneg_v2 (y : ℝ) : 0 ≤ 1 + |Real.log y| := by
  have := abs_nonneg (Real.log y)
  linarith

/-- FS's spectral cut-off `(dsℓ)⁻¹` is positive at positive data (the three factors are positive). -/
lemma sbCut_pos_v2 {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) : 0 < Work.BoseFixB1.sbCut μ a := by
  have ht : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  have hd : 0 < (Work.BoseBox.paramsAt μ a).d := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  have hs : 0 < (Work.BoseBox.paramsAt μ a).s := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  have hside : 0 < Work.BoseBox.sideAt μ a :=
    Work.BoseBox.boxSide_pos hμ ha (Work.BoseBox.fsXp_pos ht)
  simp only [Work.BoseFixB1.sbCut]
  exact inv_pos.mpr (mul_pos (mul_pos hd hs) hside)

/-- The cutoff mass `chiMass M ℓ d u = ∫ χ_{B(u)}²` is nonnegative. -/
lemma chiMass_nonneg_v2 (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u :=
  Work.SmallBoxSliding.chiMass_nonneg M ℓ d u

/-- The excited count `n₊(B) = Σ_i ‖Q_{B,i}Ψ‖²` is nonnegative. -/
lemma cnPlusBoxInd_nonneg_v2 (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.UBBInputs8.cnPlusBoxInd a A volA Ψ := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- **The box-mass sandwich, order form**: `boxM1 ≤ boxM2` for the sliding kernels
(`Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1`, proved from the pointwise identity
`w₂ = w₁(1+ω)` and `0 ≤ ω ≤ 1` a.e.).  This is the scalar fact that makes every `boxM2 − boxM1`
coefficient of the target's left-hand side nonnegative. -/
lemma boxM1_le_boxM2_slidingB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) :=
  sub_nonneg.mp (Work.BoseFixB1S.boxM2_sub_boxM1_nonneg_slidingB1 hv_supp hR0 hv hvrad hv1
    h hav hM hℓ hd hR hRχ u)

theorem boxBogWeightedV2B1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
        (hdil : 2 * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) * (_root_.BoseGases.a v) ≤ 1)
        (u : EuclideanSpace ℝ (Fin 3))
        (hu : u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ)
        {N : ℕ} (hN : 1 ≤ N) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1),
        - (1 / 2) * (1 + C * (R / (ℓ * d) + (_root_.BoseGases.a v) / ℓ))
              * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
                  - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u))
              * (((N : ℝ) + 1) * (N : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u ^ 2)
          - C * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
                  - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u))
              * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
              * (1 + |Real.log (1 / (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)
                  * _root_.BoseGases.a v))|)
              * (((N : ℝ) + 1) * (N : ℝ) / Work.SmallBoxSliding.boxMass ℓ d u ^ 2)
          - C * (Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
                  - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u))
              * (_root_.BoseGases.a v) ^ 3
              * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (-(3 : ℝ))
              * (((N : ℝ) + 1) ^ 3 * (N : ℝ))
              / Work.SmallBoxSliding.boxMass ℓ d u ^ 4
          - C * (_root_.BoseGases.a v)
              * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (3 : ℝ)
              * ((N : ℝ) * Work.SmallBoxSliding.chiMass M ℓ d u
                  / Work.SmallBoxSliding.boxMass ℓ d u)
          - C * (_root_.BoseGases.a v)
              * (((N : ℝ) + 1) / Work.SmallBoxSliding.boxMass ℓ d u)
              * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Work.SmallBoxSliding.boxMass ℓ d u) Φ
        ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.chiB ℓ d u)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ
          + Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ := by sorry

end Work.BoseFixB1S
