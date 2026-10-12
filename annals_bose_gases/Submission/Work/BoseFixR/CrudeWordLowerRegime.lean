import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.paramsAt_facts
import Submission.Work.BoseFixR.CrudeWordLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/CrudeWordLowerRegime`

The **régime-restricted** crude word bound of `Work.BoseFixR.CrudeWordLower`
(whose unrestricted form was machine-refuted in that file's docstring): in the
dilute régime `R ≤ ℓ·chiR0` the box word `wordB` dominates
`−C·μ·(a v)·n·‖Ψ‖²` with the *universal* constant `C = chiSup²·2·8π`.

The mechanism is the elementary one recorded in
`Work.BoseKinLoc.Word.bddBelow_boxState_ratio_physical`, transported to an
arbitrary smooth (not necessarily symmetric, possibly zero) state:

* `wordB = boxFormB` splits as `kinFormB + ∫_{abox} Ψ²·potWordU`;
* the kinetic part is `≥ 0` (`kinFormB_nonneg_of_continuous` below, a copy of
  `Work.BoseKinLoc.Word.kinFormB_nonneg` for states that are merely continuous
  — `BoxState` demands symmetry and non-vanishing, which the requested
  statement does not have);
* in `potWordU` the pair sum is `≥ 0` (`Work.BoseFixR.wLoc_zero_nonneg`, `hv`)
  and the chemical sum is `−μ Σᵢ ∫_y wLoc ℓ (g₀) 0 (xᵢ) y` with each fibre
  integral bounded by `chiSup²·2·8π(a v)` (`Work.BoseFixR.fibre_wLoc_g0_abs_le`,
  the dilute-régime fibre bound), so the potential word is `≥ −(|μ|·n·K)Φ²`
  with `K = chiSup²·2·8π(a v)`.

The only analytic point is that the pointwise bound has to be turned into a
bound on `∫_{abox} Ψ²·potWordU`: if that integrand is integrable this is
`setIntegral_mono_on` against the integrable comparison function
`−(|μ|nK)Ψ²`; if it is not integrable the Bochner integral is `0` by
convention, which is `≥ −(|μ|nK)·‖Ψ‖²` because the comparison constant is `≤ 0`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The kinetic word is nonnegative for arbitrary continuous states -/

/-- **The box-restricted kinetic word is nonnegative for a merely continuous
state.**  Same proof as `Work.BoseKinLoc.Word.kinFormB_nonneg`, which is stated
for `BoxState` (symmetric, non-vanishing); the proof only ever uses continuity
of the state. -/
lemma kinFormB_nonneg_of_continuous {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hs : 0 < s) (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b)
    {Ψ : X n → ℝ} (hΨ : Continuous Ψ) :
    0 ≤ Work.BoseKinLoc.kinFormB n ℓ d s εT b Ψ := by
  unfold Work.BoseKinLoc.kinFormB
  refine mul_nonneg (zpow_nonneg hℓ.le _) (Finset.sum_nonneg fun i _ => ?_)
  refine integral_nonneg fun x => ?_
  exact mul_nonneg (Work.BoseKinLoc.Word.kinFormB_indU_nonneg ℓ 0 (x i))
    (Work.BoseKinLoc.Word.fsT_nonneg_of_continuous hℓ hd hs hεT hεT1 hb 0
      (Work.BoseKinLoc.Word.kinFormB_fibre_continuous i x hΨ))

/-! ## 2. The potential word, bounded below pointwise -/

/-- The `m`-fold sum of the one-body (chemical) fibre integrals is bounded in
absolute value by `m·K` when each fibre integral is. -/
private lemma abs_chem_sum_le {g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ x : EuclideanSpace ℝ (Fin 3),
      |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 x y| ≤ K)
    (m : ℕ) (x : X m) :
    |∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y| ≤ (m : ℝ) * K := by
  have h1 : |∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y|
      ≤ ∑ i : Fin m, |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y| := by
    simpa using Finset.abs_sum_le_sum_abs
      (fun i : Fin m => ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y) Finset.univ
  have h2 : (∑ i : Fin m, |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y|)
      ≤ (m : ℝ) * K := by
    calc (∑ i : Fin m, |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y|)
        ≤ ∑ _i : Fin m, K := Finset.sum_le_sum fun i _ => hg (x i)
      _ = (m : ℝ) * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- **The potential word of FS `eq:Def_HB` is bounded below pointwise** by
`−(|μ|·m·K)`: the pair sum is nonnegative (`hv`) and the chemical word is `−μ`
times a sum of `m` fibre integrals, each of modulus `≤ K` (`hg`). -/
private lemma potWordU_lower {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ wLoc ℓ v 0 x y)
    (hg : ∀ x : EuclideanSpace ℝ (Fin 3),
      |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 x y| ≤ K)
    (m : ℕ) (x : X m) :
    -(|μ| * (m : ℝ) * K) ≤ Work.BoseKinLoc.potWordU m v g ℓ μ 0 x := by
  rw [Work.BoseKinLoc.potWordU]
  have hSabs : |∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y|
      ≤ (m : ℝ) * K := abs_chem_sum_le hK hg m x
  have hPair : 0 ≤ ∑ ij : {ij : Fin m × Fin m | ij.1 < ij.2},
      wLoc ℓ v 0 (x ij.1.1) (x ij.1.2) :=
    Finset.sum_nonneg fun ij _ => hv (x ij.1.1) (x ij.1.2)
  have hμS : -(|μ| * (m : ℝ) * K)
      ≤ -μ * (∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y) := by
    have h := neg_le_abs ((-μ) * (∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3),
      wLoc ℓ g 0 (x i) y))
    rw [abs_mul, abs_neg] at h
    have h2 : |μ| * |∑ i : Fin m, ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 (x i) y|
        ≤ |μ| * ((m : ℝ) * K) := mul_le_mul_of_nonneg_left hSabs (abs_nonneg μ)
    linarith
  linarith

/-! ## 3. The box word dominates `−(|μ|·m·K)·‖Ψ‖²` -/

/-- **The box-restricted word is bounded below** by `−(|μ|·m·K)·‖Ψ‖²` as soon
as the pair kernel `wLoc ℓ v 0` is pointwise nonnegative and the one-body
kernel has fibre integrals bounded by `K`.  No symmetry, no non-vanishing and
no support condition on the state. -/
lemma boxFormB_lower {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ d s εT b K : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b)
    (hK : 0 ≤ K) (hv : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ wLoc ℓ v 0 x y)
    (hg : ∀ x : EuclideanSpace ℝ (Fin 3),
      |∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ g 0 x y| ≤ K)
    {m : ℕ} {Ψ : X m → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    -(|μ| * (m : ℝ) * K) * Work.BoseKinLoc.sqNormB m ℓ Ψ
      ≤ Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Ψ := by
  have hcont : Continuous Ψ := hΨ.continuous
  have hSnn : 0 ≤ Work.BoseKinLoc.sqNormB m ℓ Ψ := by
    rw [Work.BoseKinLoc.sqNormB]
    exact integral_nonneg fun x => sq_nonneg _
  have hsqint : IntegrableOn (fun x : X m => (Ψ x) ^ 2) (abox m ℓ) :=
    ContinuousOn.integrableOn_compact (abox_compact m hℓ) ((hcont.pow 2).continuousOn)
  have hpoint : ∀ x : X m,
      -(|μ| * (m : ℝ) * K) * (Ψ x) ^ 2
        ≤ (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU m v g ℓ μ 0 x := by
    intro x
    have h1 : -(|μ| * (m : ℝ) * K) ≤ Work.BoseKinLoc.potWordU m v g ℓ μ 0 x :=
      potWordU_lower hK hv hg m x
    rw [mul_comm (-(|μ| * (m : ℝ) * K)) ((Ψ x) ^ 2)]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hkin : 0 ≤ Work.BoseKinLoc.kinFormB m ℓ d s εT b Ψ :=
    kinFormB_nonneg_of_continuous hℓ hd hs hεT hεT1 hb hcont
  have hbox : Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Ψ
      = Work.BoseKinLoc.kinFormB m ℓ d s εT b Ψ
        + ∫ x in abox m ℓ, (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU m v g ℓ μ 0 x := rfl
  have key : -(|μ| * (m : ℝ) * K) * Work.BoseKinLoc.sqNormB m ℓ Ψ
      ≤ Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Ψ := by
    rw [hbox]
    by_cases hFint : IntegrableOn (fun x : X m =>
        (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU m v g ℓ μ 0 x) (abox m ℓ)
    · have hlint : IntegrableOn (fun x : X m =>
          -(|μ| * (m : ℝ) * K) * (Ψ x) ^ 2) (abox m ℓ) :=
        MeasureTheory.Integrable.const_mul hsqint (-(|μ| * (m : ℝ) * K))
      have hmono := setIntegral_mono_on hlint hFint
        (abox_measurable m ℓ) (fun x _ => hpoint x)
      have hLI : ∫ x in abox m ℓ, -(|μ| * (m : ℝ) * K) * (Ψ x) ^ 2
          = -(|μ| * (m : ℝ) * K) * Work.BoseKinLoc.sqNormB m ℓ Ψ := by
        rw [Work.BoseKinLoc.sqNormB, MeasureTheory.integral_const_mul]
      rw [hLI] at hmono
      linarith
    · rw [MeasureTheory.integral_undef hFint]
      have hc : -(|μ| * (m : ℝ) * K) * Work.BoseKinLoc.sqNormB m ℓ Ψ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg (mul_nonneg (abs_nonneg μ) (Nat.cast_nonneg m)) hK))
          hSnn
      linarith
  exact key

theorem CrudeWordLowerRegime {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} {μ : ℝ}, 0 < μ →
      Work.BoseBoxFix.Adm v 1 μ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 →
      ∀ {Ψ : Submission.BoseGases.X n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      -(C * μ * _root_.BoseGases.a v * (n : ℝ)) * Work.BoseBoxFix.normB v μ n Ψ
        ≤ Work.BoseBoxFix.wordB v h μ n Ψ := by
  refine ⟨Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π), ?_, ?_⟩
  · have h1 : 0 ≤ Submission.BoseGases.chiSup ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    have h3 : (0 : ℝ) ≤ 8 * π := by linarith [Real.pi_pos]
    exact mul_nonneg (mul_nonneg h1 h2) h3
  · intro n μ hμ hAdm hreg Ψ hΨ
    obtain ⟨ha, hd, hs, heT0, heT1, hb, hKl⟩ :=
      Work.BoseBox.paramsAt_facts (a := _root_.BoseGases.a v) hμ hAdm.2.2
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseBox.sideAt_pos hμ ha
    have hKnn :
        0 ≤ Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * _root_.BoseGases.a v) := by
      have hA : 0 ≤ Submission.BoseGases.chiSup ^ 2 * 2 :=
        mul_nonneg (sq_nonneg _) (by norm_num)
      have hB : 0 ≤ 8 * π * _root_.BoseGases.a v :=
        mul_nonneg (by linarith [Real.pi_pos]) ha.le
      exact mul_nonneg hA hB
    have hg : ∀ x : EuclideanSpace ℝ (Fin 3),
        |∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.g0 v h) 0 x y|
          ≤ Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * _root_.BoseGases.a v) :=
      fun x => Work.BoseFixR.fibre_wLoc_g0_abs_le h hR hv hvrad hv_supp hℓ hreg x
    have hv' : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.wLoc
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) v 0 x y :=
      fun x y => Work.BoseFixR.wLoc_zero_nonneg hv _ x y
    have hmain := boxFormB_lower (v := v) (g := Submission.BoseGases.g0 v h)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (μ := μ)
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
      (εT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
      (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b)
      (K := Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * _root_.BoseGases.a v))
      hℓ hd hs heT0 heT1 hb hKnn hv' hg hΨ
    have hval : -(Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π) * μ
          * _root_.BoseGases.a v * (n : ℝ))
        = -(|μ| * (n : ℝ)
            * (Submission.BoseGases.chiSup ^ 2 * 2 * (8 * π * _root_.BoseGases.a v))) := by
      rw [abs_of_pos hμ]
      ring
    rw [hval, Work.BoseBoxFix.wordB, Work.BoseBoxFix.normB]
    exact hmain

end Work.BoseFixR
