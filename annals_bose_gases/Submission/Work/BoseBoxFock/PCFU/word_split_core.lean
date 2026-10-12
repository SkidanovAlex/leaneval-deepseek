import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.aP_aP_wordB_eq_smear
import Submission.Work.BoseBoxFock.PCFU.aP_comm_of_integrable
import Submission.Work.BoseBoxFock.PCFU.aP_sym_box_L1
import Submission.Work.BoseBoxFock.PCFU.wordB_integrable_family
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.word_split_core`

The **main-term** (`Ĉ`-)piece of the `(D)`-channel word split: the
slot-`j` low-momentum lift of `Q_jP_iΘ` against the windowed pair kernel
`χ_Λ(x_i)W₁(x_i−x_j)χ_Λ(x_j)` is transported back onto `Θ` by the two slot
means, at the price of the volume factor `ℓ⁶`.

The proof is the assembly recorded in `FINDING_Dchan_dzero_word_split_FALSE.md`
§4, step 3:

* `aP_aP_wordB_eq_smear` (`PCFU/aP_aP_wordB_eq_smear`, PROVED) computes the
  pointwise identity `ℓ⁶·(P_iP_jB)(x) = ∫_z χ_Λ z · (χ_Λ ⋆ W₁)(z) · F(x,z)`;
* the support hypothesis `Function.support Θ ⊆ abox n ℓ` moves `∫_{X n}` to
  `∫_{abox n ℓ}`;
* `P_iP_j(B) = P_jP_i(B)` a.e. by the Fubini-form commutativity
  `aP_comm_of_integrable` (PROVED), whose integrability input is the fourth
  conjunct of `wordB_integrable_family`;
* `aP_sym_box_L1` (PROVED) moves each slot mean from `B = Q_{L,j}Q_jP_iΘ·w₁` onto
  `Θ`, the two `IntegrableOn` hypotheses being supplied by
  `wordB_integrable_family` together with the uniform bounds on `aP`;
* finally `∫_{abox}` is compared with `((∫_{abox} · : ℝ) : ℂ)` by the
  hypothesis-free `integral_ofReal` and `Complex.ofReal_mul`.

All the complex/real bookkeeping is definitional (or
`Complex.ofReal_mul`/`integral_ofReal`), because `chiLam ℓ = chiScale ℓ`
definitionally.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The corpus box bump `χ_Λ` is the scaled bump `χ(·/ℓ)`, definitionally. -/
lemma wsc_chiLam_eq_chiScale (ℓ : ℝ) :
    Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl

/-- **The real-valued core identity** of the `Ĉ`-piece of the word split. -/
theorem wsc_real_core {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut}
    {ℓ κ Cθ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∀ y, |Θ y| ≤ Cθ) (hCθ : 0 ≤ Cθ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∫ x : Submission.BoseGases.X n,
        Θ x * (∫ z : E3, Submission.BoseGases.chiScale ℓ z *
          Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
          Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z))
      = ℓ ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x *
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) *
              Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x) := by
  classical
  obtain ⟨hFam1, hFam2, hFam3, hFam4⟩ :=
    wordB_integrable_family hij h hℓ hκ hΘm hΘb hCθ
  -- Notation.
  set B : Submission.BoseGases.X n → ℝ :=
    Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ with hB
  -- ### Step 1: the pointwise value of the inner `z`-integral.
  have hinner : ∀ x : Submission.BoseGases.X n,
      (∫ z : E3, Submission.BoseGases.chiScale ℓ z *
          Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
          Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z)
        = ℓ ^ 6 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x := by
    intro x
    exact (Work.BoseBoxFock.PCFU.aP_aP_wordB_eq_smear (i := i) (j := j) hij (h := h)
      (fc := fc) (ℓ := ℓ) (κ := κ) (Cθ := Cθ) hℓ (Θ := Θ) hΘm hΘb hCθ x).symm
  -- ### Step 2: pull `ℓ⁶` out of the `x`-integral.
  have hstep1 : (∫ x : Submission.BoseGases.X n,
        Θ x * (∫ z : E3, Submission.BoseGases.chiScale ℓ z *
          Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
          Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z))
      = ℓ ^ 6 * (∫ x : Submission.BoseGases.X n,
          Θ x * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x) := by
    have h1 : (∫ x : Submission.BoseGases.X n,
          Θ x * (∫ z : E3, Submission.BoseGases.chiScale ℓ z *
            Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
            Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z))
        = ∫ x : Submission.BoseGases.X n,
            ℓ ^ 6 * (Θ x * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        dsimp only; rw [hinner x]; ring)
    rw [h1, MeasureTheory.integral_const_mul]
  -- ### Step 3: the support hypothesis reduces the `x`-integral to the box.
  have hstep2 : (∫ x : Submission.BoseGases.X n,
          Θ x * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Θ x * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro x hx
    have h0 : Θ x = 0 := by
      by_contra hne
      exact hx (hΘs (Function.mem_support.mpr hne))
    rw [h0, zero_mul]
  -- ### Step 4: the two slot means commute (`i ≠ j`).
  have hcomm : ∀ x : Submission.BoseGases.X n,
      (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x
        = (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i B)) x :=
    fun x => Work.BoseBoxFock.PCFU.aP_comm_of_integrable (ℓ := ℓ) hℓ (i := i) (j := j) hij
      (Φ := B) x (hFam4 x)
  have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ,
          Θ x * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B)) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Θ x * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i B)) x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; rw [hcomm x])
  -- ### Step 5: move the slot-`j` mean off `Θ` (self-adjointness, slot `j`).
  have hΘj_bdd : ∀ x : Submission.BoseGases.X n, |Submission.BoseGases.aP ℓ j Θ x| ≤ Cθ :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓ j hCθ hΘb x
  have hstep4 : (∫ x in Submission.BoseGases.abox n ℓ,
          Θ x * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i B)) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ j Θ) x * (Submission.BoseGases.aP ℓ i B) x := by
    refine (Work.BoseBoxFock.PCFU.aP_sym_box_L1 (ℓ := ℓ) hℓ j (Φ := Θ)
      (Ψ := Submission.BoseGases.aP ℓ i B) ?_ ?_).symm
    · exact (hFam2).bdd_mul ((Work.BoseBoxFock.Weak.aP_measurable j hΘm).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hΘj_bdd x)
    · exact (hFam3).bdd_mul hΘm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hΘb x)
  -- ### Step 6: move the slot-`i` mean off `aP_j Θ` (self-adjointness, slot `i`).
  have hΘij_bdd : ∀ x : Submission.BoseGases.X n,
      |Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x| ≤ Cθ :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ
      (fun y => Work.BoseBoxFock.Weak.aP_abs_le hℓ j hCθ hΘb y) x
  have hstep5 : (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ j Θ) x * (Submission.BoseGases.aP ℓ i B) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ)) x * B x := by
    refine (Work.BoseBoxFock.PCFU.aP_sym_box_L1 (ℓ := ℓ) hℓ i
      (Φ := Submission.BoseGases.aP ℓ j Θ) (Ψ := B) ?_ ?_).symm
    · exact (hFam1).bdd_mul
        ((Work.BoseBoxFock.Weak.aP_measurable i
          (Work.BoseBoxFock.Weak.aP_measurable j hΘm))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hΘij_bdd x)
    · exact (hFam2).bdd_mul ((Work.BoseBoxFock.Weak.aP_measurable j hΘm).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hΘj_bdd x)
  -- ### Step 7: unfold `B` into the window times the low-slot factor.
  have hstep6 : (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ)) x * B x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x *
            Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) *
              Work.BoseBoxFix.lowSlot fc κ ℓ j
                (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hB, Work.BoseBoxFock.PCFU.wordB]
    ring
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, hstep6]

/-- **The `(D)`-channel word split, core identity**: the `Ĉ`-piece. -/
theorem word_split_core {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut}
    {ℓ κ Cθ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∀ y, |Θ y| ≤ Cθ) (hCθ : 0 ≤ Cθ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                * ((∫ y : EuclideanSpace ℝ (Fin 3),
                    Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((ℓ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ)) := by
  classical
  -- ### The inner `z`-integral, in complex form, is the cast of the real one.
  have hz_eq : ∀ x : Submission.BoseGases.X n,
      (∫ z : E3,
          ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
            * ((∫ y : E3, Work.BoseK15.corpusBox.chiLam ℓ y
                  * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
            * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                  (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                  (Function.update x j z) : ℝ) : ℂ))
        = ((∫ z : E3, Submission.BoseGases.chiScale ℓ z *
              Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
              Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z : ℝ) : ℂ) := by
    intro x
    have hcast : ((∫ z : E3, Submission.BoseGases.chiScale ℓ z *
              Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
              Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z : ℝ) : ℂ)
        = ∫ z : E3, ((Submission.BoseGases.chiScale ℓ z *
              Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
              Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z : ℝ) : ℂ) :=
      (integral_ofReal).symm
    rw [hcast]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [wsc_chiLam_eq_chiScale ℓ]
    simp only [Work.BoseBoxFock.PCFU.smearW, Work.BoseBoxFock.PCFU.wordF]
    push_cast
    ring
  -- ### The complex left-hand side is the cast of the real left-hand side.
  have hLHS :
      (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                * ((∫ y : EuclideanSpace ℝ (Fin 3),
                    Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((∫ x : Submission.BoseGases.X n,
            Θ x * (∫ z : E3, Submission.BoseGases.chiScale ℓ z *
              Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
              Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z) : ℝ) : ℂ) := by
    have h1 : (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
                * ((∫ y : EuclideanSpace ℝ (Fin 3),
                    Work.BoseK15.corpusBox.chiLam ℓ y
                      * (Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
        = ∫ x : Submission.BoseGases.X n,
            ((Θ x * (∫ z : E3, Submission.BoseGases.chiScale ℓ z *
              Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z *
              Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z) : ℝ) : ℂ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [hz_eq x, ← Complex.ofReal_mul])
    exact h1.trans integral_ofReal
  -- ### The complex right-hand side is the cast of the real one.
  have hRHS :
      ((ℓ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ))
      = ((ℓ ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x *
                Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) *
                  Work.BoseBoxFix.lowSlot fc κ ℓ j
                    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x) : ℝ) : ℂ) := by
    have hii : (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc κ ℓ j
                      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ))
        = ((∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x *
                Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) *
                  Work.BoseBoxFix.lowSlot fc κ ℓ j
                    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ) := by
      have hcast : ((∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x *
                Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) *
                  Work.BoseBoxFix.lowSlot fc κ ℓ j
                    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ)
          = ∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x *
                Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) *
                  Work.BoseBoxFix.lowSlot fc κ ℓ j
                    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) x : ℝ) : ℂ) :=
        (integral_ofReal).symm
      rw [hcast]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by push_cast; ring)
    rw [hii, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [hLHS, hRHS]
  exact congrArg Complex.ofReal
    (wsc_real_core (i := i) (j := j) hij (h := h) (fc := fc) hℓ hκ hΘm hΘb hCθ hΘs)

end Work.BoseBoxFock.PCFU
