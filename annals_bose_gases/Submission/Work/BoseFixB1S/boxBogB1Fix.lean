import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixB1.tBwordKinInd_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxBogB1Fix` — FS `lm:appbogolubov` at the sliding box (`n`-quadratic mass)

**VERDICT (this session): `declare_false`.  The requested statement is FALSE as written** — the
volume-normalisation defect of the workspace's sliding-box Bogoliubov rungs.

The statement (kept verbatim) is FS's `lm:appbogolubov` (`eq:refinedaprioribog`,
`final_v2.tex` l. 3762-3780) at the sliding box `B(u) = dlBox ℓ d u`, with the
particle-number-quadratic mass `(N+1)N/chiMass`, quantified over arbitrary sliding parameters
`(ℓ, d, μ)` with `R ≤ ℓd/16`, `R ≤ ℓ·chiR0`, `u ∈ interiorSet ℓ d μ`.

### Why it is false

The **payer** `tBwordKinInd` is `tBdiagFormInd` at the *ambient* slot normalisation `(a³)⁻¹ = ℓ⁻³`
(`Submission/Work/UBBInputs8/Defs.lean:112`), while the pairing `boxA2` — and *every* row on the
left — is normalised by the **box** volume `boxMass ℓ d u = |dlBox ℓ d u|`.  The two are
commensurable only at `ℓ³ = boxMass ℓ d u`.

In the admissible regime `ℓd = D` fixed, `ℓ = D³`, `d = D⁻²` (so `V := boxMass ≈ D³`,
`d³ = V/ℓ³ = D⁻⁶ → 0`, `u = 0 ∈ interiorSet ℓ d μ` for `μ = 1` and `D` large) with the exact
two-particle minimiser of the pairing (`Work.BoseFixB1.boxA2TwoParticleAttained`) one has

    boxA2 = −Θ(√chiMass·‖𝒲‖₂/V) = −Θ(V^{−1/2}),

while the payer is `O(V/ℓ³) = O(D^{−6})` and the whole displayed error bracket is at most
`C·(the κ-bracket's minimum) + O(V^{−1})`; the bracket `κ³N + κ⁻³(N+1)³N/x³ + κ·log·(N+1)N/x` is
minimal at `κ* = (N+1)^{3/4}/x^{3/4} = Θ(V^{−3/4})` (admissible: `κ* ≫ κ_min`, and `μ` is free),
where it equals `2N(N+1)^{9/4}/x^{9/4} = Θ(V^{−9/4})`.  Hence for every fixed `C` the left-hand
side is `−o(V^{−1/2})` while the right-hand side is `−Θ(V^{−1/2})`: the inequality fails for
`V` large, i.e. for every `C ≥ 0`.

### The workspace already records this defect

* `Submission/Work/BoseFixB1B/localisedAppBogBoxA2Norm.lean` (**`declare_false`**): the *same*
  rung (same words, same parameter range, with the mass written `(n+1)n·chiMass/boxMass²` — a
  *larger* payment, i.e. a weaker claim, still false).
* `Submission/Work/BoseFixB1B/FINDING_localisedAppBogBoxA2Norm_false.md` — the full diagnosis.
* `Submission/Work/BoseFixB1/FINDING_boxSimpleA2Sharp_volA_mismatch.md` — the same defect in the
  general-box D1 (`boxSimpleA2Sharp`, `boxSimpleA2TwoWindow`, both refuted); an independent child
  re-derived the same refutation of `boxSimpleA2TwoWindowSharp` this session.

The defect disappears exactly at `ℓ³ = boxMass` (the *cube* case, where
`Work.BoseFixB1.simpleA2_sharp` and the proved D1 `Submission.BoseGases.lm_appbogolubov_pWord_holds`
live).  Repair: box-normalise the payer (`(boxMass)⁻¹` in place of `(a³)⁻¹`), i.e. state the rung
for the *box-normalised* kinetic word.

## What is proved here

* `pairSet_one_eq_empty`, `boxA2_one_eq_zero` — the pairing word vanishes for `N = 1`;
* `cnPlusBoxInd_nonneg`, `boxMass_nonneg`, `sbCut_pos`, `one_div_nonneg`,
  `rpow_neg_three_nonneg`, `rpow_three_nonneg`, `one_add_abs_log_nonneg` — the sign facts;
* the `N = 1` case of the target (`boxBogB1Fix_N_eq_one`): there `boxA2 = 0` and
  `tBwordKinInd ≥ 0`, so any `C ≥ 0` works.

## The remaining content: the analytic core

For `N ≥ 2` the statement is FS's *sharp* Bogoliubov bound at the sliding box: the negativity of
the pairing word `boxA2` — which is genuinely signed (`Submission/Work/SmallBoxA0/README.md`
§28.5: the pairing alone is unbounded below like `-‖w₁‖_{L²}s^{-3/2}`) — must be paid by the
kinetic word `tBwordKinInd` together with the explicit error bracket displayed in the statement.
In this workspace that bound is the content of the general-box two-window rungs
`Submission/Work/BoseFixB1/boxSimpleA2TwoWindow`, `…boxSimpleA2TwoWindowC`, `…boxSimpleA2Sharp`
and of `Submission/Work/BoseFixB1/lm_appbogolubov_localisedB` — all of them *stated and unproved*
(skeleton `sorry`s) — while the corpus's only PROVED Bogoliubov rendering
`Submission.BoseGases.lm_appbogolubov_pWord_holds` lives at the *p-space* words and, by the
`kinPWord`/`kinWord` obstruction of `SmallBoxDesignNote.md` Session-286, does not transfer to the
words of this statement.  This file isolates precisely that gap.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `pairSet N` is empty for `N = 1`. -/
lemma pairSet_one_eq_empty : Submission.BoseGases.pairSet 1 = ∅ := by
  rw [Submission.BoseGases.pairSet, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact hp (Subsingleton.elim p.1 p.2)

/-- **The pairing word vanishes for `N = 1`** (there are no pairs of distinct slots). -/
lemma boxA2_one_eq_zero (ℓ volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X 1 → ℝ) :
    Work.BoseFixB1.boxA2 ℓ volA A w1 Φ = 0 := by
  rw [Work.BoseFixB1.boxA2, pairSet_one_eq_empty, Finset.sum_empty]

/-- `cnPlusBoxInd` is a sum of integrals of squares, hence nonnegative. -/
lemma cnPlusBoxInd_nonneg (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ) {N : ℕ}
    (Ψ : Submission.BoseGases.X N → ℝ) : 0 ≤ Work.UBBInputs8.cnPlusBoxInd a A volA Ψ := by
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

/-- The box volume is nonnegative. -/
lemma boxMass_nonneg (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  simp only [Work.SmallBoxSliding.boxMass]
  exact integral_nonneg fun x => by
    simp only [Work.SmallBoxSliding.boxInd]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- `1 / x ≥ 0` for `x ≥ 0`. -/
lemma one_div_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 / x := div_nonneg zero_le_one hx

/-- `x ^ (-(3 : ℝ)) ≥ 0` for `x ≥ 0`. -/
lemma rpow_neg_three_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x ^ (-(3 : ℝ) : ℝ) :=
  Real.rpow_nonneg hx _

/-- `x ^ (3 : ℝ) ≥ 0` for `x ≥ 0`. -/
lemma rpow_three_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x ^ (3 : ℝ) := Real.rpow_nonneg hx _

/-- `1 + |log y| ≥ 0`. -/
lemma one_add_abs_log_nonneg (y : ℝ) : 0 ≤ 1 + |Real.log y| := by
  have := abs_nonneg (Real.log y)
  linarith

/-- FS's spectral cut-off `(dsℓ)⁻¹` is positive. -/
lemma sbCut_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) : 0 < Work.BoseFixB1.sbCut μ a := by
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

/-- **The target for `N = 1` and `C = 0`.** -/
theorem boxBogB1Fix_N_eq_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
      (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
      (u : EuclideanSpace ℝ (Fin 3))
      (hu : u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ)
      {Φ : Submission.BoseGases.X 1 → ℝ} (hΦc : Continuous Φ)
      (hnorm : (∫ x in Submission.BoseGases.abox 1 ℓ, (Φ x) ^ 2) = 1),
      - (1 / 2) * (1 + (0 : ℝ) * (R / (ℓ * d) + (_root_.BoseGases.a v) / ℓ))
            * (∫ z : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h z * Classical.choose h z)
            * ((((1 : ℕ) : ℝ) + 1) * ((1 : ℕ) : ℝ) / Work.SmallBoxSliding.chiMass M ℓ d u)
        - (0 : ℝ) * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
            * (1 + |Real.log (1 / (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)
                * _root_.BoseGases.a v))|)
            * ((((1 : ℕ) : ℝ) + 1) * ((1 : ℕ) : ℝ) / Work.SmallBoxSliding.chiMass M ℓ d u)
        - (0 : ℝ) * (_root_.BoseGases.a v)
            * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (-(3 : ℝ))
            * ((((1 : ℕ) : ℝ) + 1) ^ 3 * ((1 : ℕ) : ℝ))
              / (Work.SmallBoxSliding.chiMass M ℓ d u) ^ 3
        - (0 : ℝ) * (_root_.BoseGases.a v)
            * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (3 : ℝ) * ((1 : ℕ) : ℝ)
        - (0 : ℝ) * (_root_.BoseGases.a v)
            * ((((1 : ℕ) : ℝ) + 1) / Work.SmallBoxSliding.chiMass M ℓ d u)
            * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.chiB ℓ d u)
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ
        + Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ := by
  intro ℓ d μ hℓ hd hμ hR hRχ u hu Φ hΦc hnorm
  have hG : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.g0 v h z * Classical.choose h z :=
    Work.SmallBoxA0.g0w0Mass_nonneg_general hR0 hv_supp h
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u :=
    Work.SmallBoxSliding.chiMass_nonneg M ℓ d u
  have hT : 0 ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ :=
    Work.BoseFixB1.tBwordKinInd_nonneg Φ
  have hdiv : 0 ≤ (∫ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.g0 v h z * Classical.choose h z)
      / Work.SmallBoxSliding.chiMass M ℓ d u := div_nonneg hG hχ
  rw [boxA2_one_eq_zero, add_zero]
  have hsimp : - (1 / 2) * (1 + (0 : ℝ) * (R / (ℓ * d) + (_root_.BoseGases.a v) / ℓ))
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.g0 v h z * Classical.choose h z)
          * ((((1 : ℕ) : ℝ) + 1) * ((1 : ℕ) : ℝ) / Work.SmallBoxSliding.chiMass M ℓ d u)
      - (0 : ℝ) * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
          * (1 + |Real.log (1 / (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)
              * _root_.BoseGases.a v))|)
          * ((((1 : ℕ) : ℝ) + 1) * ((1 : ℕ) : ℝ) / Work.SmallBoxSliding.chiMass M ℓ d u)
      - (0 : ℝ) * (_root_.BoseGases.a v)
          * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (-(3 : ℝ))
          * ((((1 : ℕ) : ℝ) + 1) ^ 3 * ((1 : ℕ) : ℝ))
            / (Work.SmallBoxSliding.chiMass M ℓ d u) ^ 3
      - (0 : ℝ) * (_root_.BoseGases.a v)
          * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (3 : ℝ) * ((1 : ℕ) : ℝ)
      - (0 : ℝ) * (_root_.BoseGases.a v)
          * ((((1 : ℕ) : ℝ) + 1) / Work.SmallBoxSliding.chiMass M ℓ d u)
          * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      = - ((∫ z : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.g0 v h z * Classical.choose h z)
          / Work.SmallBoxSliding.chiMass M ℓ d u) := by
    ring
  rw [hsimp]
  linarith

/-- FS `lm:appbogolubov` at the sliding box, particle-number-quadratic mass.  See the module
docstring: the `N ≥ 2` case is the workspace's unproved general-box two-window Bogoliubov rung. -/
theorem boxBogB1Fix {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3))
        (hu : u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ)
        {N : ℕ} (hN : 1 ≤ N) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
        (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1),
        - (1 / 2) * (1 + C * (R / (ℓ * d) + (_root_.BoseGases.a v) / ℓ))
              * (∫ z : EuclideanSpace ℝ (Fin 3),
                  Submission.BoseGases.g0 v h z * Classical.choose h z)
              * (((N : ℝ) + 1) * (N : ℝ) / Work.SmallBoxSliding.chiMass M ℓ d u)
          - C * (_root_.BoseGases.a v) * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
              * (1 + |Real.log (1 / (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)
                  * _root_.BoseGases.a v))|)
              * (((N : ℝ) + 1) * (N : ℝ) / Work.SmallBoxSliding.chiMass M ℓ d u)
          - C * (_root_.BoseGases.a v)
              * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (-(3 : ℝ))
              * (((N : ℝ) + 1) ^ 3 * (N : ℝ)) / (Work.SmallBoxSliding.chiMass M ℓ d u) ^ 3
          - C * (_root_.BoseGases.a v)
              * (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ (3 : ℝ) * (N : ℝ)
          - C * (_root_.BoseGases.a v)
              * (((N : ℝ) + 1) / Work.SmallBoxSliding.chiMass M ℓ d u)
              * Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
                  (Work.SmallBoxSliding.boxMass ℓ d u) Φ
        ≤ Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.chiB ℓ d u)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ
          + Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ := by
  refine ⟨0, le_refl 0, ?_⟩
  intro ℓ d μ hℓ hd hμ hR hRχ u hu N hN Φ hΦc hnorm
  by_cases hN1 : N = 1
  · subst hN1
    exact boxBogB1Fix_N_eq_one (v := v) (R := R) hv_supp hR0 hv hvrad hv1 h hav hM
      hℓ hd hμ hR hRχ u hu hΦc hnorm
  · sorry

end Work.BoseFixB1S
