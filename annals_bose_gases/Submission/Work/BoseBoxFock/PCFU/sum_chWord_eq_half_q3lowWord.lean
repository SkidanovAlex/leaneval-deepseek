import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseBoxFock.PCFU.lowSlot_boxRestrictR_factor
import Submission.Work.BoseBoxFock.PCFU.wordSplitIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.sum_chWord_eq_half_q3lowWord`

The **dictionary identity** matching the word part of the four `MiddleU` channels,

    `chWord = chAword − chBword − chCword + chDword`  (`PCFU/ChWordChains.lean`),

against the frozen cubic word `Work.BoseBoxFix.q3lowWord`:

    Σ_{p ∈ pairSet n} chWord v h fc fu μ N p.1 p.2 (boxRestrictR ℓ Φ)
      = ½ · q3lowWord fc (chKappa v μ) ℓ (wLoc ℓ (g₀ v h) 0) Φ ,     ℓ = ellH v μ .

Both sides are integrals over the box `abox n ℓ`, and *all four* channel words carry the same
low-slot factor `Q_{L,j}(Q_j P_i Θ)` — they differ only in the multiplier
`Θ, P_iΘ, P_jΘ, P_iP_jΘ`.  Since the `{P_i,Q_i} ⊗ {P_j,Q_j}` completeness gives

    Θ − P_iΘ − P_jΘ + P_iP_jΘ = Q_jQ_iΦ     on `abox n ℓ`     (Θ = boxRestrictR ℓ Φ),

with `Q_jQ_iΦ = Φ − P_iΦ − P_jΦ + P_i(P_jΦ)` (`aP_aQ_comm`), the identity is that expansion
together with the fact that `lowSlot` reads its state only through the cube indicator
(`lowSlot_boxRestrictR_agree`).  The `1/2` on the right is `q3lowWord`'s own factor `2` (the
`+ h.c.` of FS's `Q̃₃^{(1)}`).

The only non-elementary ingredients are

* integrability of the four channel integrands: `wordSplitIntegrable`, whose analytic content is the
  exact cancellation `χ_ℓ ⋆ χ_ℓ = ℓ³·convScale ℓ` (`chiW1_integrable`), together with the global
  boundedness of `boxRestrictR ℓ Φ` for continuous `Φ`;
* the interval-reflection of the low slot between `boxRestrictR ℓ Φ` and `Φ`
  (`lowSlot_boxRestrictR_agree`, `aP_boxRestrictR`, `aP_aP_boxRestrictR`);
* the corpus's slot algebra (`aP_comm`, `aP_aQ_comm`).

All of this is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. Vocabulary -/

/-- The integrand of the `q3lowWord` summand at the pair `(i,j)` (with `w₁` instantiated at
`wLoc ℓ (g₀ v h) 0`). -/
noncomputable def q3lowTerm {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (v : E3 → ℝ)
    (h : Work.UBB.ScatSol v) (μ : ℝ) (i j : Fin n) (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) : ℝ :=
  Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
      (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Φ)) x
    * Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aQ (ellH v μ) i Φ) x
    * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)

/-! ## 1. The box restriction of a continuous state -/

/-- The real box restriction of a continuous state is measurable. -/
private lemma measurable_boxRestrictR {n : ℕ} (ℓ : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) : Measurable (boxRestrictR ℓ Φ) := by
  unfold boxRestrictR
  exact hΦ.measurable.mul
    (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ))

/-- The real box restriction of a continuous state is globally bounded (the box is compact). -/
private lemma bound_boxRestrictR {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |boxRestrictR ℓ Φ x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hsplit : boxRestrictR ℓ Φ x
      = Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x := rfl
  rw [hsplit]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
    exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
    exact le_max_right _ _

/-! ## 2. The slot algebra: `Q_jQ_iΦ` expanded -/

/-- `Q_j Q_i Φ`, expanded in the four slot means of `Φ`. -/
private lemma aQ_aQ_expand {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
      = Φ x - Submission.BoseGases.aP ℓ i Φ x - Submission.BoseGases.aP ℓ j Φ x
        + Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x := by
  have h1 : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
      = Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aP ℓ j Φ) x :=
    Submission.BoseGases.aP_aQ_comm hℓ hij.symm hΦc x
  calc Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
      = Submission.BoseGases.aQ ℓ i Φ x
          - Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x := rfl
    _ = Submission.BoseGases.aQ ℓ i Φ x
          - Submission.BoseGases.aQ ℓ i (Submission.BoseGases.aP ℓ j Φ) x := by rw [h1]
    _ = (Φ x - Submission.BoseGases.aP ℓ i Φ x)
          - (Submission.BoseGases.aP ℓ j Φ x
              - Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) := rfl
    _ = Φ x - Submission.BoseGases.aP ℓ i Φ x - Submission.BoseGases.aP ℓ j Φ x
          + Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x := by ring

/-! ## 3. The four channel words as real integrals -/

/-- The complexification step: an integral of a product of three coerced real functions is the
coercion of the integral of the product.  (Both ingredients used below are hypothesis-free:
`integral_ofReal` and `integral_congr_ae` are unconditional.) -/
private lemma chanword_integral_eq {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (M L : Submission.BoseGases.X n → ℝ) :
    (∫ x in Submission.BoseGases.abox n (ellH v μ),
        ((M x : ℝ) : ℂ)
          * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              : ℝ) : ℂ)
          * ((L x : ℝ) : ℂ))
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            M x * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * L x) : ℝ) : ℂ) := by
  have h1 : (∫ x in Submission.BoseGases.abox n (ellH v μ),
        ((M x : ℝ) : ℂ)
          * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              : ℝ) : ℂ)
          * ((L x : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox n (ellH v μ),
          ((M x * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * L x : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ((M x : ℝ) : ℂ)
          * ((Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              : ℝ) : ℂ)
          * ((L x : ℝ) : ℂ)
        = ((M x * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * L x : ℝ) : ℂ)
    simp only [Complex.ofReal_mul]
  rw [h1]
  exact integral_ofReal

/-- The `(A)`-channel word, as the complexification of its real integral. -/
private lemma chAword_eq {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    chAword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Θ x * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i Θ)) x) : ℝ) : ℂ) := by
  have hh := chanword_integral_eq (n := n) (i := i) (j := j) (v := v) (h := h) (fc := fc) (μ := μ)
    (M := Θ)
    (L := fun x => Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
      (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x)
  simpa only [chAword] using hh

/-- The `(B)`-channel word, as the complexification of its real integral. -/
private lemma chBword_eq {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    chBword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) i Θ x
              * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i Θ)) x) : ℝ) : ℂ) := by
  have hh := chanword_integral_eq (n := n) (i := i) (j := j) (v := v) (h := h) (fc := fc) (μ := μ)
    (M := Submission.BoseGases.aP (ellH v μ) i Θ)
    (L := fun x => Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
      (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x)
  simpa only [chBword] using hh

/-- The `(C)`-channel word, as the complexification of its real integral. -/
private lemma chCword_eq {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    chCword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) j Θ x
              * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i Θ)) x) : ℝ) : ℂ) := by
  have hh := chanword_integral_eq (n := n) (i := i) (j := j) (v := v) (h := h) (fc := fc) (μ := μ)
    (M := Submission.BoseGases.aP (ellH v μ) j Θ)
    (L := fun x => Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
      (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x)
  simpa only [chCword] using hh

/-- The `(D)`-channel word, as the complexification of its real integral. -/
private lemma chDword_eq {n : ℕ} (i j : Fin n) (v : E3 → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (Θ : Submission.BoseGases.X n → ℝ) :
    chDword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
              * Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
              * Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
                  (Submission.BoseGases.aQ (ellH v μ) j
                    (Submission.BoseGases.aP (ellH v μ) i Θ)) x) : ℝ) : ℂ) := by
  have hh := chanword_integral_eq (n := n) (i := i) (j := j) (v := v) (h := h) (fc := fc) (μ := μ)
    (M := Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ))
    (L := fun x => Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
      (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x)
  simpa only [chDword] using hh

/-! ## 4. Integrability of the channel integrands -/

/-- A bounded measurable multiplier times `wordB` is integrable on the box. -/
private lemma integrableOn_mul_wordB {n : ℕ} {i j : Fin n} (hij : i ≠ j) {v : E3 → ℝ}
    (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut} {ℓ κ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ)
    {M Ψ : Submission.BoseGases.X n → ℝ} {CM Cψ : ℝ} (hCM0 : 0 ≤ CM) (hMm : Measurable M)
    (hMb : ∀ x, |M x| ≤ CM) (hCψ0 : 0 ≤ Cψ) (hΨm : Measurable Ψ)
    (hΨb : ∀ x, |Ψ x| ≤ Cψ) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
        M x * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
          * Work.BoseBoxFix.lowSlot fc κ ℓ j
              (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ)) x)
      (Submission.BoseGases.abox n ℓ) volume := by
  have hw : IntegrableOn (wordB v h fc κ ℓ i j Ψ) (Submission.BoseGases.abox n ℓ) volume :=
    (wordSplitIntegrable (n := n) (i := i) (j := j) hij (v := v) h (fc := fc)
      (ℓ := ℓ) (κ := κ) (Cθ := Cψ) hℓ hκ (Θ := Ψ) hΨm hΨb hCψ0).1
  have h1 : Integrable (fun x : Submission.BoseGases.X n => M x * wordB v h fc κ ℓ i j Ψ x)
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    hw.bdd_mul (c := CM) hMm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hMb x)
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  show M x * (Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ)) x
      * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j))
    = M x * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
      * Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ)) x
  ring

/-! ## 5. The per-pair identity -/

/-- **The per-pair dictionary identity**: the word part of the combined channel difference at the
pair `(i,j)`, evaluated at the box restriction of `Φ`, is the `q3lowWord` summand. -/
private theorem chWord_eq_term {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : E3 → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hℓ : 0 < ellH v μ) (hκ : 0 < chKappa v μ) :
    chWord v h fc fu μ N i j (boxRestrictR (ellH v μ) Φ)
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            q3lowTerm fc v h μ i j Φ x) : ℝ) : ℂ) := by
  obtain ⟨Cθ, hCθ0, hCθb⟩ := bound_boxRestrictR hℓ hΦc
  set Θ : Submission.BoseGases.X n → ℝ := boxRestrictR (ellH v μ) Φ with hΘdef
  have hΘm : Measurable Θ := by rw [hΘdef]; exact measurable_boxRestrictR _ hΦc
  have hΘb : ∀ x, |Θ x| ≤ Cθ := fun x => by rw [hΘdef]; exact hCθb x
  -- the two factors shared by the four channel integrands
  set wl : Submission.BoseGases.X n → ℝ :=
    fun x => Submission.BoseGases.wLoc (ellH v μ) (Submission.BoseGases.g0 v h) 0 (x i) (x j)
    with hwldef
  set L : Submission.BoseGases.X n → ℝ :=
    fun x => Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
      (Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)) x
    with hLdef
  -- the four channel words as real integrals
  have hA : chAword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ), Θ x * wl x * L x) : ℝ) : ℂ) := by
    rw [chAword_eq (n := n) i j v h fc fu μ N Θ]
  have hB : chBword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x) : ℝ) : ℂ) := by
    rw [chBword_eq (n := n) i j v h fc fu μ N Θ]
  have hC : chCword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x) : ℝ) : ℂ) := by
    rw [chCword_eq (n := n) i j v h fc fu μ N Θ]
  have hD : chDword v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
              * wl x * L x) : ℝ) : ℂ) := by
    rw [chDword_eq (n := n) i j v h fc fu μ N Θ]
  -- integrability of the four channel integrands
  have hPiΘm : Measurable (Submission.BoseGases.aP (ellH v μ) i Θ) :=
    Work.BoseBoxFock.Weak.aP_measurable i hΘm
  have hPiΘb : ∀ x, |Submission.BoseGases.aP (ellH v μ) i Θ x| ≤ Cθ :=
    Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ0 hΘb
  have hPjΘm : Measurable (Submission.BoseGases.aP (ellH v μ) j Θ) :=
    Work.BoseBoxFock.Weak.aP_measurable j hΘm
  have hPjΘb : ∀ x, |Submission.BoseGases.aP (ellH v μ) j Θ x| ≤ Cθ :=
    Work.BoseBoxFock.Weak.aP_abs_le hℓ j hCθ0 hΘb
  have hPiPjΘm : Measurable
      (Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ)) :=
    Work.BoseBoxFock.Weak.aP_measurable i hPjΘm
  have hPiPjΘb : ∀ x,
      |Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x| ≤ Cθ :=
    Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ0 hPjΘb
  have hIAon := integrableOn_mul_wordB (i := i) (j := j) hij (v := v) h (fc := fc)
    (ℓ := ellH v μ) (κ := chKappa v μ) (M := Θ) (Ψ := Θ) (CM := Cθ) (Cψ := Cθ)
    hℓ hκ hCθ0 hΘm hΘb hCθ0 hΘm hΘb
  have hIBon := integrableOn_mul_wordB (i := i) (j := j) hij (v := v) h (fc := fc)
    (ℓ := ellH v μ) (κ := chKappa v μ) (M := Submission.BoseGases.aP (ellH v μ) i Θ)
    (Ψ := Θ) (CM := Cθ) (Cψ := Cθ) hℓ hκ hCθ0 hPiΘm hPiΘb hCθ0 hΘm hΘb
  have hICon := integrableOn_mul_wordB (i := i) (j := j) hij (v := v) h (fc := fc)
    (ℓ := ellH v μ) (κ := chKappa v μ) (M := Submission.BoseGases.aP (ellH v μ) j Θ)
    (Ψ := Θ) (CM := Cθ) (Cψ := Cθ) hℓ hκ hCθ0 hPjΘm hPjΘb hCθ0 hΘm hΘb
  have hIDon := integrableOn_mul_wordB (i := i) (j := j) hij (v := v) h (fc := fc)
    (ℓ := ellH v μ) (κ := chKappa v μ)
    (M := Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ))
    (Ψ := Θ) (CM := Cθ) (Cψ := Cθ) hℓ hκ hCθ0 hPiPjΘm hPiPjΘb hCθ0 hΘm hΘb
  have hIA : Integrable (fun x : Submission.BoseGases.X n => Θ x * wl x * L x)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (ellH v μ))) := by
    exact hIAon.integrable
  have hIB : Integrable (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (ellH v μ))) := by
    exact hIBon.integrable
  have hIC : Integrable (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (ellH v μ))) := by
    exact hICon.integrable
  have hID : Integrable (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
          * wl x * L x)
      ((volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n (ellH v μ))) := by
    exact hIDon.integrable
  -- the real integral identity
  have hreal : (∫ x in Submission.BoseGases.abox n (ellH v μ), Θ x * wl x * L x)
        - (∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
        - (∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x)
        + (∫ x in Submission.BoseGases.abox n (ellH v μ),
            Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
              * wl x * L x)
      = ∫ x in Submission.BoseGases.abox n (ellH v μ), q3lowTerm fc v h μ i j Φ x := by
    have e1 : (∫ x in Submission.BoseGases.abox n (ellH v μ), Θ x * wl x * L x)
          - (∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
        = ∫ x in Submission.BoseGases.abox n (ellH v μ),
            (Θ x * wl x * L x - Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x) :=
      (MeasureTheory.integral_sub hIA hIB).symm
    have e2 : (∫ x in Submission.BoseGases.abox n (ellH v μ),
            (Θ x * wl x * L x - Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x))
          - (∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x)
        = ∫ x in Submission.BoseGases.abox n (ellH v μ),
            ((Θ x * wl x * L x - Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
              - Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x) :=
      (MeasureTheory.integral_sub (hIA.sub hIB) hIC).symm
    have e3 : (∫ x in Submission.BoseGases.abox n (ellH v μ),
            ((Θ x * wl x * L x - Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
              - Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x))
          + (∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
                * wl x * L x)
        = ∫ x in Submission.BoseGases.abox n (ellH v μ),
            (((Θ x * wl x * L x - Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
              - Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x)
              + Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
                * wl x * L x) :=
      (MeasureTheory.integral_add ((hIA.sub hIB).sub hIC) hID).symm
    have e4 : (∫ x in Submission.BoseGases.abox n (ellH v μ),
            (((Θ x * wl x * L x - Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
              - Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x)
              + Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
                * wl x * L x))
        = ∫ x in Submission.BoseGases.abox n (ellH v μ), q3lowTerm fc v h μ i j Φ x := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable n (ellH v μ))] with x hx
      have hΘx : Θ x = Φ x := by
        rw [hΘdef]
        have hsplit : boxRestrictR (ellH v μ) Φ x
            = Φ x * (Submission.BoseGases.abox n (ellH v μ)).indicator
                (fun _ => (1 : ℝ)) x := rfl
        rw [hsplit, Set.indicator_of_mem hx, mul_one]
      have hPix : Submission.BoseGases.aP (ellH v μ) i Θ x
          = Submission.BoseGases.aP (ellH v μ) i Φ x := by
        rw [hΘdef]; exact Work.BoseBoxFock.aP_boxRestrictR i Φ hx
      have hPjx : Submission.BoseGases.aP (ellH v μ) j Θ x
          = Submission.BoseGases.aP (ellH v μ) j Φ x := by
        rw [hΘdef]; exact Work.BoseBoxFock.aP_boxRestrictR j Φ hx
      have hPiPjx : Submission.BoseGases.aP (ellH v μ) i
            (Submission.BoseGases.aP (ellH v μ) j Θ) x
          = Submission.BoseGases.aP (ellH v μ) i
              (Submission.BoseGases.aP (ellH v μ) j Φ) x := by
        rw [hΘdef]; exact Work.BoseBoxFock.aP_aP_boxRestrictR (i, j) Φ hx
      have hLx : L x = Work.BoseBoxFix.lowSlot fc (chKappa v μ) (ellH v μ) j
          (Submission.BoseGases.aQ (ellH v μ) j
            (Submission.BoseGases.aP (ellH v μ) i Φ)) x := by
        rw [hLdef]
        exact Work.BoseBoxFock.PCFU.lowSlot_boxRestrictR_agree fc (chKappa v μ) (ellH v μ) i j Φ hx
      have hQQ : Submission.BoseGases.aQ (ellH v μ) j
            (Submission.BoseGases.aQ (ellH v μ) i Φ) x
          = Φ x - Submission.BoseGases.aP (ellH v μ) i Φ x
              - Submission.BoseGases.aP (ellH v μ) j Φ x
              + Submission.BoseGases.aP (ellH v μ) i
                  (Submission.BoseGases.aP (ellH v μ) j Φ) x :=
        aQ_aQ_expand hℓ hij hΦc x
      simp only [q3lowTerm]
      rw [hΘx, hPix, hPjx, hPiPjx, hLx, hQQ]
      ring
    linarith [e1, e2, e3, e4]
  calc chWord v h fc fu μ N i j Θ
      = (((∫ x in Submission.BoseGases.abox n (ellH v μ), Θ x * wl x * L x) : ℝ) : ℂ)
          - (((∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x) : ℝ) : ℂ)
          - (((∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x) : ℝ) : ℂ)
          + (((∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
                * wl x * L x) : ℝ) : ℂ) := by
        simp only [chWord, hA, hB, hC, hD]
    _ = ((((∫ x in Submission.BoseGases.abox n (ellH v μ), Θ x * wl x * L x)
          - (∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) i Θ x * wl x * L x)
          - (∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) j Θ x * wl x * L x)
          + (∫ x in Submission.BoseGases.abox n (ellH v μ),
              Submission.BoseGases.aP (ellH v μ) i (Submission.BoseGases.aP (ellH v μ) j Θ) x
                * wl x * L x)) : ℝ) : ℂ) := by
        push_cast
        ring
    _ = (((∫ x in Submission.BoseGases.abox n (ellH v μ), q3lowTerm fc v h μ i j Φ x)
          : ℝ) : ℂ) := by rw [hreal]

/-! ## 6. The sum identity -/

theorem sum_chWord_eq_half_q3lowWord (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBoxFock.ellH v μ))
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < Work.BoseBoxFock.PCFU.chKappa v μ) :
    (∑ p ∈ Submission.BoseGases.pairSet n,
        Work.BoseBoxFock.PCFU.chWord v h fc fu μ N p.1 p.2
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ)))
      = (((1 / 2) * Work.BoseBoxFix.q3lowWord fc (Work.BoseBoxFock.PCFU.chKappa v μ)
            (Work.BoseBoxFock.ellH v μ)
            (Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ)
              (Submission.BoseGases.g0 v h) 0)
            (Φ : Submission.BoseGases.X n → ℝ) : ℝ) : ℂ) := by
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hterm : ∀ p ∈ Submission.BoseGases.pairSet n,
      chWord v h fc fu μ N p.1 p.2
          (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
        = (((∫ x in Submission.BoseGases.abox n (ellH v μ),
              q3lowTerm fc v h μ p.1 p.2 (Φ : Submission.BoseGases.X n → ℝ) x)
            : ℝ) : ℂ) := by
    intro p hp
    exact chWord_eq_term p.1 p.2 (Finset.mem_filter.mp hp).2 v h fc fu μ N hΦc hℓ hκ
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, Complex.ofReal_inj]
  rw [Work.BoseBoxFix.q3lowWord]
  simp only [q3lowTerm]
  ring

end Work.BoseBoxFock.PCFU
