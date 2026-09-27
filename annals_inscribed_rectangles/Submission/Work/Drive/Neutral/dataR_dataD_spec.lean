import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.dataChord_spec
import Submission.Work.Drive.Neutral.contDiffOn_curvePtAt

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology

/-! ## The capping radius and disk coordinate of a chord

`Work.Drive.Neutral.dataR γ x s = sqrt (‖dataMid‖² + ‖dataChord‖²)` and `dataD = dataMid / dataR` are the
capping radius and the disk coordinate of the chord `{γ (x e^{i sClamp s}), γ (x e^{-i sClamp s})}`.
This file records what the downstream `dataRbOf`/`dataVbOf` blends need:

* positivity of `dataR` away from `x = 0` (at `x ≠ 0` the two endpoints are nonzero, so they cannot
  both vanish);
* `‖dataD‖ ≤ 1` (the midpoint is at distance `≤ dataR` from the origin, by definition of `dataR`);
* joint `C^∞`-smoothness of both on `{x ≠ 0}`, from the smoothness of `dataMid`/`dataChord`
  (`contDiffOn_dataMid_of_ne`/`contDiffOn_dataChord_of_ne`) and of `sqrt` where its argument is
  positive;
* evenness in the opening `s`, from the evenness of `dataMid` and the oddness of `dataChord`. -/

/-- `Complex.normSq` is `C^∞` (it is the polynomial `z ↦ z.re² + z.im²`). -/
lemma contDiff_complexNormSq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.normSq := by
  have h : Complex.normSq = fun z : ℂ => z.re * z.re + z.im * z.im := by
    funext z
    rw [Complex.normSq_apply]
  rw [h]
  exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

/-! ## Parity of the opening -/

lemma dataMid_neg (γ : Circle → ℝ × ℝ) (x : ℂ) (s : ℝ) :
    dataMid γ x (-s) = dataMid γ x s := by
  simp only [dataMid, endPlus, endMinus, neg_neg]
  ring

lemma dataChord_neg (γ : Circle → ℝ × ℝ) (x : ℂ) (s : ℝ) :
    dataChord γ x (-s) = -dataChord γ x s := by
  simp only [dataChord, endPlus, endMinus, neg_neg]
  ring

lemma dataR_neg (γ : Circle → ℝ × ℝ) (x : ℂ) (s : ℝ) :
    dataR γ x (-s) = dataR γ x s := by
  rw [dataR, dataR, dataMid_neg γ x s, dataChord_neg γ x s, Complex.normSq_neg]

lemma dataD_neg (γ : Circle → ℝ × ℝ) (x : ℂ) (s : ℝ) :
    dataD γ x (-s) = dataD γ x s := by
  rw [dataD, dataD, dataMid_neg γ x s, dataR_neg γ x s]

/-! ## Positivity and the unit bound -/

/-- At `x ≠ 0` the two endpoints of the chord are nonzero (`γ` never vanishes), so `dataMid` and
`dataChord` cannot both vanish. -/
lemma curvePtAt_ne_zero {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    (x : ℂ) (s : ℝ) (hx : x ≠ 0) : curvePtAt γ x s ≠ 0 := by
  intro h
  rw [curvePtAt_eq γ (p := (x, s)) hx] at h
  exact hγne _ (symmC_eq_zero_iff.mp h)

/-- The squared capping radius is positive away from `x = 0`. -/
lemma dataNormSq_pos (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {x : ℂ} (hx : x ≠ 0) (s : ℝ) :
    0 < Complex.normSq (dataMid γ x s) + Complex.normSq (dataChord γ x s) := by
  by_contra hle
  push_neg at hle
  have hA : 0 ≤ Complex.normSq (dataMid γ x s) := Complex.normSq_nonneg _
  have hB : 0 ≤ Complex.normSq (dataChord γ x s) := Complex.normSq_nonneg _
  have hA0 : Complex.normSq (dataMid γ x s) = 0 := le_antisymm (by linarith) hA
  have hB0 : Complex.normSq (dataChord γ x s) = 0 := le_antisymm (by linarith) hB
  have hM0 : dataMid γ x s = 0 := Complex.normSq_eq_zero.mp hA0
  have hC0 : dataChord γ x s = 0 := Complex.normSq_eq_zero.mp hB0
  have hsplit : curvePtAt γ x s = dataMid γ x s + dataChord γ x s / 2 := by
    simp only [dataMid, dataChord, endPlus, endMinus]
    ring
  exact curvePtAt_ne_zero hγne x s hx (by rw [hsplit, hM0, hC0]; ring)

/-- The capping radius is positive away from `x = 0`. -/
lemma dataR_pos (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {x : ℂ} (hx : x ≠ 0) (s : ℝ) : 0 < dataR γ x s := by
  rw [dataR, Real.sqrt_pos]
  exact dataNormSq_pos γ hγne hx s

/-- The disk coordinate has norm `≤ 1`: the midpoint is one of the two terms whose squares make up
`dataR²`. -/
lemma dataD_norm_le_one (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {x : ℂ} (hx : x ≠ 0) (s : ℝ) : ‖dataD γ x s‖ ≤ 1 := by
  have hRpos : 0 < dataR γ x s := dataR_pos γ hγne hx s
  have hle : ‖dataMid γ x s‖ ≤ dataR γ x s := by
    have h1 : ‖dataMid γ x s‖ = Real.sqrt (‖dataMid γ x s‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, dataR, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (‖dataChord γ x s‖)]
  rw [dataD, norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
  exact div_le_one_of_le₀ hle hRpos.le

/-! ## Joint smoothness -/

theorem dataR_dataD_spec (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    (∀ x s, x ≠ 0 → 0 < Work.Drive.Neutral.dataR γ x s) ∧
      (∀ x s, x ≠ 0 → ‖Work.Drive.Neutral.dataD γ x s‖ ≤ 1) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => Work.Drive.Neutral.dataR γ p.1 p.2)
        {p : ℂ × ℝ | p.1 ≠ 0} ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => Work.Drive.Neutral.dataD γ p.1 p.2)
        {p : ℂ × ℝ | p.1 ≠ 0} ∧
      (∀ x s, Work.Drive.Neutral.dataR γ x (-s) = Work.Drive.Neutral.dataR γ x s) ∧
      (∀ x s, Work.Drive.Neutral.dataD γ x (-s) = Work.Drive.Neutral.dataD γ x s) := by
  have hγ' : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ := hγ
  have hM : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataMid γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := contDiffOn_dataMid_of_ne γ hγ'
  have hC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataChord γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := contDiffOn_dataChord_of_ne γ hγ'
  have hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ =>
        Complex.normSq (dataMid γ p.1 p.2) + Complex.normSq (dataChord γ p.1 p.2))
      {p : ℂ × ℝ | p.1 ≠ 0} :=
    (contDiff_complexNormSq.comp_contDiffOn hM).add (contDiff_complexNormSq.comp_contDiffOn hC)
  have hAne : ∀ p ∈ {p : ℂ × ℝ | p.1 ≠ 0},
      Complex.normSq (dataMid γ p.1 p.2) + Complex.normSq (dataChord γ p.1 p.2) ≠ 0 :=
    fun p hp => ne_of_gt (dataNormSq_pos γ hγne hp p.2)
  have hdataR : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataR γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := by
    refine (hA.sqrt hAne).congr (fun p hp => ?_)
    simp only [dataR]
  have hdataD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℂ × ℝ => dataD γ p.1 p.2)
      {p : ℂ × ℝ | p.1 ≠ 0} := by
    have hRc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℝ => ((dataR γ p.1 p.2 : ℝ) : ℂ)) {p : ℂ × ℝ | p.1 ≠ 0} :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hdataR
    have hne : ∀ p ∈ {p : ℂ × ℝ | p.1 ≠ 0}, ((dataR γ p.1 p.2 : ℝ) : ℂ) ≠ 0 :=
      fun p hp => Complex.ofReal_ne_zero.mpr (ne_of_gt (dataR_pos γ hγne hp p.2))
    have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℂ × ℝ => (((dataR γ p.1 p.2 : ℝ) : ℂ))⁻¹) {p : ℂ × ℝ | p.1 ≠ 0} :=
      hRc.inv hne
    refine (hM.mul hinv).congr (fun p hp => ?_)
    simp only [dataD, div_eq_mul_inv]
  exact ⟨fun x s hx => dataR_pos γ hγne hx s,
    fun x s hx => dataD_norm_le_one γ hγne hx s,
    hdataR, hdataD, fun x s => dataR_neg γ x s, fun x s => dataD_neg γ x s⟩

end Work.Drive.Neutral
