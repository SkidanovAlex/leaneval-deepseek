import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.chanA_canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chan_int_y_generic`

**The generic `y`-integration identity of the `(a)`-channel.**  For the sharp box
indicator `θ_Λ = 1_{Λ(ℓ)}` (`Work.BoseB4.BoxData.thetaFun` at the corpus box), the
two-slot integral

    ∫_{Λ(ℓ)²}  G(x)·Θ(x[i↦y][j↦u])·F(x,u) dy du

equals `ℓ³ = |Λ(ℓ)|` times the single-slot integral in which the `i`-th slot is
replaced by the slot mean `aP ℓ i` (the average over the centred cube `acube ℓ`).
The identity is the Fubini/Tonelli rearrangement of the pair integral together with
the definitional identity `ℓ³·aP ℓ i Ψ x = ∫_{y ∈ acube ℓ} Ψ(x[i↦y])`.

The `ℓ³` factor is the *volume* of the box; the two sharp indicators supply it.  The
hypotheses `0 < ℓ`, measurability and uniform boundedness of `G, Θ, F` are used only
to make the Bochner integrals/`Fubini` legitimate (the integrands are bounded and
supported in a *finite-measure* box, since `G` is supported in `abox n ℓ`).

Everything here is `sorry`-free.
-/

noncomputable section
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The integrands, as named definitions

Naming the four functions keeps the statements of the auxiliary lemmas readable; each is
definitionally the corresponding expression of the target. -/

/-- The left-hand integrand of `chan_int_y_generic`: the two-slot (windowed) pairing. -/
noncomputable def chanL {n : ℕ} (i j : Fin n) (ℓ : ℝ) (G : Submission.BoseGases.X n → ℂ)
    (Θ : Submission.BoseGases.X n → ℝ) (F : Submission.BoseGases.X n → E3 → ℂ) :
    Submission.BoseGases.X n × (E3 × E3) → ℂ :=
  fun q => G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun ℓ q.2.1
    * Work.BoseK15.corpusBox.thetaFun ℓ q.2.2
    * F q.1 q.2.2

/-- The right-hand integrand of `chan_int_y_generic`: the slot mean `aP` in slot `i`. -/
noncomputable def chanR {n : ℕ} (i j : Fin n) (ℓ : ℝ) (G : Submission.BoseGases.X n → ℂ)
    (Θ : Submission.BoseGases.X n → ℝ) (F : Submission.BoseGases.X n → E3 → ℂ) :
    Submission.BoseGases.X n × E3 → ℂ :=
  fun p => G p.1 * F p.1 p.2 * Work.BoseK15.corpusBox.thetaFun ℓ p.2
    * ((Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ)

/-- The inner (two-slot) integrand of the left-hand side, at a fixed configuration `x`. -/
noncomputable def chanK {n : ℕ} (i j : Fin n) (ℓ : ℝ) (Θ : Submission.BoseGases.X n → ℝ)
    (F : Submission.BoseGases.X n → E3 → ℂ) (x : Submission.BoseGases.X n) : E3 × E3 → ℂ :=
  fun z => ((Θ (Function.update (Function.update x i z.1) j z.2) : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun ℓ z.1
    * Work.BoseK15.corpusBox.thetaFun ℓ z.2
    * F x z.2

/-- The inner (one-slot) integrand of the right-hand side, at a fixed configuration `x`. -/
noncomputable def chanM {n : ℕ} (i j : Fin n) (ℓ : ℝ) (Θ : Submission.BoseGases.X n → ℝ)
    (F : Submission.BoseGases.X n → E3 → ℂ) (x : Submission.BoseGases.X n) : E3 → ℂ :=
  fun u => F x u * Work.BoseK15.corpusBox.thetaFun ℓ u
    * ((Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ)

/-- Evaluation form of `chanL` (definitional). -/
lemma chanL_apply {n : ℕ} (i j : Fin n) (ℓ : ℝ) (G : Submission.BoseGases.X n → ℂ)
    (Θ : Submission.BoseGases.X n → ℝ) (F : Submission.BoseGases.X n → E3 → ℂ)
    (x : Submission.BoseGases.X n) (y u : E3) :
    chanL i j ℓ G Θ F (x, (y, u))
      = G x * ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ y
        * Work.BoseK15.corpusBox.thetaFun ℓ u * F x u := rfl

/-- Evaluation form of `chanR` (definitional). -/
lemma chanR_apply {n : ℕ} (i j : Fin n) (ℓ : ℝ) (G : Submission.BoseGases.X n → ℂ)
    (Θ : Submission.BoseGases.X n → ℝ) (F : Submission.BoseGases.X n → E3 → ℂ)
    (x : Submission.BoseGases.X n) (u : E3) :
    chanR i j ℓ G Θ F (x, u)
      = G x * F x u * Work.BoseK15.corpusBox.thetaFun ℓ u
        * ((Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ) :=
  rfl

/-- Evaluation form of `chanK` (definitional). -/
lemma chanK_apply {n : ℕ} (i j : Fin n) (ℓ : ℝ) (Θ : Submission.BoseGases.X n → ℝ)
    (F : Submission.BoseGases.X n → E3 → ℂ) (x : Submission.BoseGases.X n) (y u : E3) :
    chanK i j ℓ Θ F x (y, u)
      = ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ y
        * Work.BoseK15.corpusBox.thetaFun ℓ u * F x u := rfl

/-- Evaluation form of `chanM` (definitional). -/
lemma chanM_apply {n : ℕ} (i j : Fin n) (ℓ : ℝ) (Θ : Submission.BoseGases.X n → ℝ)
    (F : Submission.BoseGases.X n → E3 → ℂ) (x : Submission.BoseGases.X n) (u : E3) :
    chanM i j ℓ Θ F x u = F x u * Work.BoseK15.corpusBox.thetaFun ℓ u
      * ((Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ) :=
  rfl

/-! ## 1. Norm and measurability toolbox -/

lemma mul5_le_of_le {a b c d e A B C D E : ℝ} (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C)
    (h4 : d ≤ D) (h5 : e ≤ E) (h2n : 0 ≤ b) (h3n : 0 ≤ c) (h4n : 0 ≤ d) (h5n : 0 ≤ e)
    (hAn : 0 ≤ A) (hBn : 0 ≤ B) (hCn : 0 ≤ C) (hDn : 0 ≤ D) (hEn : 0 ≤ E) :
    a * b * c * d * e ≤ A * B * C * D * E := by gcongr

lemma mul4_le_of_le {a b c d A B C D : ℝ} (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C)
    (h4 : d ≤ D) (h2n : 0 ≤ b) (h3n : 0 ≤ c) (h4n : 0 ≤ d)
    (hAn : 0 ≤ A) (hBn : 0 ≤ B) (hCn : 0 ≤ C) (hDn : 0 ≤ D) :
    a * b * c * d ≤ A * B * C * D := by gcongr

lemma norm_mul_five_le (a b c d e : ℂ) :
    ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  calc ‖a * b * c * d * e‖ ≤ ‖a * b * c * d‖ * ‖e‖ := norm_mul_le _ _
    _ ≤ (‖a * b * c‖ * ‖d‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((‖a * b‖ * ‖c‖) * ‖d‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (((‖a‖ * ‖b‖) * ‖c‖) * ‖d‖) * ‖e‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by ring

lemma norm_mul_four_le (a b c d : ℂ) :
    ‖a * b * c * d‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
  calc ‖a * b * c * d‖ ≤ ‖a * b * c‖ * ‖d‖ := norm_mul_le _ _
    _ ≤ (‖a * b‖ * ‖c‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((‖a‖ * ‖b‖) * ‖c‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
    _ = ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by ring

/-- The norm of a real scalar viewed in `ℂ`. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  rw [show r * r = r ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- `θ_Λ` is a 0/1 function: its norm is at most `1`. -/
lemma norm_thetaFun_le_one (ℓ : ℝ) (y : E3) :
    ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖ ≤ 1 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-- `θ_Λ` vanishes off the centred cube `acube ℓ = Λ(ℓ)`. -/
lemma thetaFun_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {y : E3}
    (hy : y ∉ Submission.BoseGases.acube ℓ) :
    Work.BoseK15.corpusBox.thetaFun ℓ y = 0 := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  have hy' : y ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    rwa [Work.BoseBoxFock.boxL_eq_acube hℓ]
  simp [hy']

/-- `θ_Λ` is measurable. -/
lemma measurable_thetaFun {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  rw [Work.BoseBoxFock.thetaFun_eq_indicator hℓ]
  exact (measurable_const : Measurable (fun _ : E3 => (1 : ℂ))).indicator
    (Submission.BoseGases.acube_measurable ℓ)

/-- Multiplication by `θ_Λ` is the indicator of the centred cube. -/
lemma thetaFun_mul_eq_indicator {ℓ : ℝ} (hℓ : 0 < ℓ) (f : E3 → ℂ) :
    (fun y : E3 => Work.BoseK15.corpusBox.thetaFun ℓ y * f y)
      = (Submission.BoseGases.acube ℓ).indicator f := by
  funext y
  rw [Work.BoseBoxFock.thetaFun_eq_indicator hℓ]
  by_cases hy : y ∈ Submission.BoseGases.acube ℓ
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

/-- The `aP` normalisation, real form: the unnormalised slot integral is `ℓ³·aP`.

Kept `private`: the same helper name is declared (with a different signature) in
`PCFU/integral_Ksfr_slot_split.lean`, so the two modules could not otherwise be imported together. -/
private lemma pow_mul_aP_eq_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    (ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    ℓ ^ 3 * Submission.BoseGases.aP ℓ i ψ x
      = ∫ y in Submission.BoseGases.acube ℓ, ψ (Function.update x i y) := by
  rw [Submission.BoseGases.aP, ← mul_assoc, one_div,
    mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

/-- The `aP` normalisation, complex form (kept `private`, see `pow_mul_aP_eq_integral`). -/
private lemma ofReal_pow_mul_aP_eq_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    (ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    ((ℓ : ℂ)) ^ 3 * ((Submission.BoseGases.aP ℓ i ψ x : ℝ) : ℂ)
      = ∫ y in Submission.BoseGases.acube ℓ, ((ψ (Function.update x i y) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, pow_mul_aP_eq_integral hℓ i ψ x,
    integral_complex_ofReal]

/-- **The `y`-integral against `θ_Λ` is `ℓ³·aP`.** -/
lemma theta_mul_Theta_integral {n : ℕ} {i j : Fin n} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (u : E3) :
    (∫ y : E3, Work.BoseK15.corpusBox.thetaFun ℓ y
        * ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ))
      = ((ℓ : ℂ)) ^ 3 * ((Submission.BoseGases.aP ℓ i
          (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ) := by
  rw [thetaFun_mul_eq_indicator hℓ]
  rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  exact (ofReal_pow_mul_aP_eq_integral hℓ i (fun x' => Θ (Function.update x' j u)) x).symm

/-- A bounded measurable function supported in a finite-measure set is integrable. -/
lemma integrable_of_bounded_support {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hsupp : ∀ z ∉ s, f z = 0) : Integrable f μ :=
  (MeasureTheory.IntegrableOn.of_bound hs hf.aestronglyMeasurable.restrict M
    (Filter.Eventually.of_forall hM)).integrable_of_forall_notMem_eq_zero hsupp

lemma measurable_update_update_pair {n : ℕ} (i j : Fin n) :
    Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
      Function.update (Function.update q.1 i q.2.1) j q.2.2) :=
  measurable_update'.comp
    ((measurable_update'.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
      measurable_snd.snd)

/-- The slot-mean `aP ℓ i` applied to a state that depends on a further parameter `u` is
jointly measurable. -/
lemma measurable_aP_param {n : ℕ} (i j : Fin n) {ℓ : ℝ} {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) :
    Measurable (fun p : Submission.BoseGases.X n × E3 =>
      Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j p.2)) p.1) := by
  have huncurry : StronglyMeasurable
      (fun q : (Submission.BoseGases.X n × E3) × E3 =>
        Θ (Function.update (Function.update q.1.1 i q.2) j q.1.2)) :=
    (hΘm.comp (measurable_update'.comp
      ((measurable_update'.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
        measurable_fst.snd))).stronglyMeasurable
  have hS : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    inferInstance
  have h := huncurry.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
  unfold Submission.BoseGases.aP
  exact (h.const_mul (1 / ℓ ^ 3)).measurable

/-! ## 2. Finiteness of the boxes -/

lemma volume_acube_prod_acube_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure (E3 × E3))
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) < ⊤ := by
  change (volume.prod volume : Measure (E3 × E3))
    (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) < ⊤
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
    (Submission.BoseGases.acube_lt_top ℓ hℓ.le)

lemma volume_abox_prod_acube_prod_acube_lt_top (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure (Submission.BoseGases.X n × (E3 × E3)))
      (Submission.BoseGases.abox n ℓ ×ˢ (Submission.BoseGases.acube ℓ ×ˢ
        Submission.BoseGases.acube ℓ)) < ⊤ := by
  change (volume.prod volume : Measure (Submission.BoseGases.X n × (E3 × E3)))
    (Submission.BoseGases.abox n ℓ ×ˢ (Submission.BoseGases.acube ℓ ×ˢ
      Submission.BoseGases.acube ℓ)) < ⊤
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
    (volume_acube_prod_acube_lt_top hℓ)

lemma volume_abox_prod_acube_lt_top (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (volume : Measure (Submission.BoseGases.X n × E3))
      (Submission.BoseGases.abox n ℓ ×ˢ Submission.BoseGases.acube ℓ) < ⊤ := by
  change (volume.prod volume : Measure (Submission.BoseGases.X n × E3))
    (Submission.BoseGases.abox n ℓ ×ˢ Submission.BoseGases.acube ℓ) < ⊤
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
    (Submission.BoseGases.acube_lt_top ℓ hℓ.le)

/-! ## 3. The main theorem -/

theorem chan_int_y_generic {n : ℕ} {i j : Fin n} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (G : Submission.BoseGases.X n → ℂ) (hGm : Measurable G) (Cg : ℝ) (hGb : ∀ x, ‖G x‖ ≤ Cg)
    (hGs : Function.support G ⊆ Submission.BoseGases.abox n ℓ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ) (Cθ : ℝ) (hΘb : ∀ x, |Θ x| ≤ Cθ)
    (F : Submission.BoseGases.X n → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hFm : Measurable (fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) => F p.1 p.2))
    (Cf : ℝ) (hFb : ∀ p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3), ‖F p.1 p.2‖ ≤ Cf) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.1
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.2
          * F q.1 q.2.2)
      = ((ℓ : ℂ)) ^ 3 * ∫ p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3),
          G p.1 * F p.1 p.2 * Work.BoseK15.corpusBox.thetaFun ℓ p.2
            * ((Submission.BoseGases.aP ℓ i
                (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ) := by
  change (∫ q : Submission.BoseGases.X n × (E3 × E3), chanL i j ℓ G Θ F q)
      = ((ℓ : ℂ)) ^ 3 * ∫ p : Submission.BoseGases.X n × E3, chanR i j ℓ G Θ F p
  -- nonnegativity of the three constants
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (G 0)) (hGb 0)
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hΘb 0)
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (F 0 0)) (hFb (0, 0))
  -- ## integrability of the left-hand integrand
  have hLm : Measurable (chanL i j ℓ G Θ F) := by
    have hupd : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        Function.update (Function.update q.1 i q.2.1) j q.2.2) :=
      measurable_update_update_pair i j
    have h1 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hΘm.comp hupd)
    have h2 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) :=
      (hGm.comp measurable_fst).mul h1
    have h3 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.1) :=
      h2.mul ((measurable_thetaFun hℓ).comp measurable_snd.fst)
    have h4 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.1
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.2) :=
      h3.mul ((measurable_thetaFun hℓ).comp measurable_snd.snd)
    have h5 : Measurable (fun q : Submission.BoseGases.X n × (E3 × E3) =>
        G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.1
          * Work.BoseK15.corpusBox.thetaFun ℓ q.2.2
          * F q.1 q.2.2) :=
      h4.mul (hFm.comp (measurable_fst.prodMk measurable_snd.snd))
    exact h5
  have hLb : ∀ q : Submission.BoseGases.X n × (E3 × E3),
      ‖chanL i j ℓ G Θ F q‖ ≤ Cg * Cθ * Cf := by
    rintro ⟨x, y, u⟩
    have hΘn : ‖((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [norm_ofReal_eq_abs]
      exact hΘb _
    rw [chanL_apply]
    calc ‖G x * ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y
            * Work.BoseK15.corpusBox.thetaFun ℓ u * F x u‖
        ≤ ‖G x‖ * ‖((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ u‖ * ‖F x u‖ :=
          norm_mul_five_le _ _ _ _ _
      _ ≤ Cg * Cθ * 1 * 1 * Cf :=
          mul5_le_of_le (hGb x) hΘn (norm_thetaFun_le_one ℓ y) (norm_thetaFun_le_one ℓ u)
            (hFb (x, u)) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
            hCg0 hCθ0 zero_le_one zero_le_one hCf0
      _ = Cg * Cθ * Cf := by ring
  have hLsupp : ∀ q ∉ Submission.BoseGases.abox n ℓ ×ˢ (Submission.BoseGases.acube ℓ ×ˢ
      Submission.BoseGases.acube ℓ), chanL i j ℓ G Θ F q = 0 := by
    rintro ⟨x, y, u⟩ hq
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · have hz : u ∉ Submission.BoseGases.acube ℓ := fun hz =>
          hq (by simp [hx, hy, hz])
        rw [chanL_apply, thetaFun_eq_zero_of_notMem_acube hℓ hz]
        ring
      · rw [chanL_apply, thetaFun_eq_zero_of_notMem_acube hℓ hy]
        ring
    · have hG0 : G x = 0 := by
        by_contra hne
        exact hx (hGs (Function.mem_support.mpr hne))
      rw [chanL_apply, hG0]
      ring
  have hIntL : Integrable (chanL i j ℓ G Θ F)
      (volume : Measure (Submission.BoseGases.X n × (E3 × E3))) :=
    integrable_of_bounded_support (volume_abox_prod_acube_prod_acube_lt_top n hℓ) hLm hLb
      hLsupp
  -- ## integrability of the inner left-hand integrand at every `x`
  have hIntK : ∀ x : Submission.BoseGases.X n,
      Integrable (chanK i j ℓ Θ F x) (volume : Measure (E3 × E3)) := by
    intro x
    have hupd : Measurable (fun z : E3 × E3 =>
        Function.update (Function.update x i z.1) j z.2) :=
      measurable_update'.comp (((measurable_update x).comp measurable_fst).prodMk measurable_snd)
    have h1 : Measurable (fun z : E3 × E3 =>
        ((Θ (Function.update (Function.update x i z.1) j z.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hΘm.comp hupd)
    have h3 : Measurable (fun z : E3 × E3 =>
        ((Θ (Function.update (Function.update x i z.1) j z.2) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ z.1) :=
      h1.mul ((measurable_thetaFun hℓ).comp measurable_fst)
    have h4 : Measurable (fun z : E3 × E3 =>
        ((Θ (Function.update (Function.update x i z.1) j z.2) : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ z.1
          * Work.BoseK15.corpusBox.thetaFun ℓ z.2) :=
      h3.mul ((measurable_thetaFun hℓ).comp measurable_snd)
    have h5 : Measurable (chanK i j ℓ Θ F x) := by
      have h6 : Measurable (fun z : E3 × E3 =>
          ((Θ (Function.update (Function.update x i z.1) j z.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ z.1
            * Work.BoseK15.corpusBox.thetaFun ℓ z.2
            * F x z.2) :=
        h4.mul (hFm.comp (measurable_const.prodMk measurable_snd))
      exact h6
    have hb : ∀ z : E3 × E3, ‖chanK i j ℓ Θ F x z‖ ≤ Cθ * Cf := by
      rintro ⟨y, u⟩
      have hΘn : ‖((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)‖ ≤ Cθ := by
        rw [norm_ofReal_eq_abs]
        exact hΘb _
      rw [chanK_apply]
      calc ‖((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ y
              * Work.BoseK15.corpusBox.thetaFun ℓ u * F x u‖
          ≤ ‖((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)‖
              * ‖Work.BoseK15.corpusBox.thetaFun ℓ y‖
              * ‖Work.BoseK15.corpusBox.thetaFun ℓ u‖ * ‖F x u‖ :=
            norm_mul_four_le _ _ _ _
        _ ≤ Cθ * 1 * 1 * Cf :=
            mul4_le_of_le hΘn (norm_thetaFun_le_one ℓ y) (norm_thetaFun_le_one ℓ u)
              (hFb (x, u)) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hCθ0
              zero_le_one zero_le_one hCf0
        _ = Cθ * Cf := by ring
    have hsupp : ∀ z ∉ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        chanK i j ℓ Θ F x z = 0 := by
      rintro ⟨y, u⟩ hz
      by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · have hu : u ∉ Submission.BoseGases.acube ℓ := fun hu => hz (by simp [hy, hu])
        rw [chanK_apply, thetaFun_eq_zero_of_notMem_acube hℓ hu]
        ring
      · rw [chanK_apply, thetaFun_eq_zero_of_notMem_acube hℓ hy]
        ring
    exact integrable_of_bounded_support (volume_acube_prod_acube_lt_top hℓ) h5 hb hsupp
  -- ## integrability of the right-hand integrand
  have hRm : Measurable (chanR i j ℓ G Θ F) := by
    have h1 : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j p.2)) p.1) :=
      measurable_aP_param i j hΘm
    have h2 : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        ((Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp h1
    have h3 : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * F p.1 p.2) :=
      (hGm.comp measurable_fst).mul (hFm.comp (measurable_fst.prodMk measurable_snd))
    have h4 : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * F p.1 p.2 * Work.BoseK15.corpusBox.thetaFun ℓ p.2) :=
      h3.mul ((measurable_thetaFun hℓ).comp measurable_snd)
    have h5 : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * F p.1 p.2 * Work.BoseK15.corpusBox.thetaFun ℓ p.2
          * ((Submission.BoseGases.aP ℓ i
              (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ)) :=
      h4.mul h2
    exact h5
  have hRb : ∀ p : Submission.BoseGases.X n × E3,
      ‖chanR i j ℓ G Θ F p‖ ≤ Cg * Cf * Cθ := by
    rintro ⟨x, u⟩
    have hAP : |Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j u)) x| ≤ Cθ :=
      Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ0 (fun x => hΘb _) x
    have hAPn : ‖((Submission.BoseGases.aP ℓ i
        (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [norm_ofReal_eq_abs]
      exact hAP
    rw [chanR_apply]
    calc ‖G x * F x u * Work.BoseK15.corpusBox.thetaFun ℓ u
            * ((Submission.BoseGases.aP ℓ i (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ)‖
        ≤ ‖G x‖ * ‖F x u‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ u‖
            * ‖((Submission.BoseGases.aP ℓ i
                (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ)‖ :=
          norm_mul_four_le _ _ _ _
      _ ≤ Cg * Cf * 1 * Cθ :=
          mul4_le_of_le (hGb x) (hFb (x, u)) (norm_thetaFun_le_one ℓ u) hAPn
            (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hCg0 hCf0 zero_le_one hCθ0
      _ = Cg * Cf * Cθ := by ring
  have hRsupp : ∀ p ∉ Submission.BoseGases.abox n ℓ ×ˢ Submission.BoseGases.acube ℓ,
      chanR i j ℓ G Θ F p = 0 := by
    rintro ⟨x, u⟩ hp
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · have hu : u ∉ Submission.BoseGases.acube ℓ := fun hu => hp (by simp [hx, hu])
      rw [chanR_apply, thetaFun_eq_zero_of_notMem_acube hℓ hu]
      ring
    · have hG0 : G x = 0 := by
        by_contra hne
        exact hx (hGs (Function.mem_support.mpr hne))
      rw [chanR_apply, hG0]
      ring
  have hIntR : Integrable (chanR i j ℓ G Θ F)
      (volume : Measure (Submission.BoseGases.X n × E3)) :=
    integrable_of_bounded_support (volume_abox_prod_acube_lt_top n hℓ) hRm hRb hRsupp
  -- ## the per-`x` core identity
  have hCore : ∀ x : Submission.BoseGases.X n,
      (∫ z : E3 × E3, chanK i j ℓ Θ F x z)
        = ((ℓ : ℂ)) ^ 3 * ∫ u : E3, chanM i j ℓ Θ F x u := by
    intro x
    calc (∫ z : E3 × E3, chanK i j ℓ Θ F x z)
        = ∫ u : E3, ∫ y : E3, chanK i j ℓ Θ F x (y, u) :=
          MeasureTheory.integral_prod_symm (chanK i j ℓ Θ F x) (hIntK x)
      _ = ∫ u : E3, ((ℓ : ℂ)) ^ 3 * chanM i j ℓ Θ F x u := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          simp only [chanK_apply, chanM_apply]
          calc (∫ y : E3, ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun ℓ y
                  * Work.BoseK15.corpusBox.thetaFun ℓ u * F x u)
              = ∫ y : E3, (Work.BoseK15.corpusBox.thetaFun ℓ u * F x u)
                  * (Work.BoseK15.corpusBox.thetaFun ℓ y
                    * ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ)) := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with y
                ring
            _ = (Work.BoseK15.corpusBox.thetaFun ℓ u * F x u)
                  * ∫ y : E3, Work.BoseK15.corpusBox.thetaFun ℓ y
                    * ((Θ (Function.update (Function.update x i y) j u) : ℝ) : ℂ) :=
                MeasureTheory.integral_const_mul _ _
            _ = (Work.BoseK15.corpusBox.thetaFun ℓ u * F x u)
                  * (((ℓ : ℂ)) ^ 3 * ((Submission.BoseGases.aP ℓ i
                      (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ)) := by
                rw [theta_mul_Theta_integral hℓ Θ x u]
            _ = ((ℓ : ℂ)) ^ 3 * (F x u * Work.BoseK15.corpusBox.thetaFun ℓ u
                  * ((Submission.BoseGases.aP ℓ i
                      (fun x' => Θ (Function.update x' j u)) x : ℝ) : ℂ)) := by ring
      _ = ((ℓ : ℂ)) ^ 3 * ∫ u : E3, chanM i j ℓ Θ F x u :=
          MeasureTheory.integral_const_mul _ _
  -- ## the two Fubini reductions
  have hLHS : (∫ q : Submission.BoseGases.X n × (E3 × E3), chanL i j ℓ G Θ F q)
      = ∫ x : Submission.BoseGases.X n, G x * ∫ z : E3 × E3, chanK i j ℓ Θ F x z := by
    calc (∫ q : Submission.BoseGases.X n × (E3 × E3), chanL i j ℓ G Θ F q)
        = ∫ x : Submission.BoseGases.X n, ∫ z : E3 × E3, chanL i j ℓ G Θ F (x, z) :=
          MeasureTheory.integral_prod (chanL i j ℓ G Θ F) hIntL
      _ = ∫ x : Submission.BoseGases.X n, G x * ∫ z : E3 × E3, chanK i j ℓ Θ F x z := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with z
          obtain ⟨y, u⟩ := z
          rw [chanL_apply, chanK_apply]
          ring
  have hRHS : (∫ p : Submission.BoseGases.X n × E3, chanR i j ℓ G Θ F p)
      = ∫ x : Submission.BoseGases.X n, G x * ∫ u : E3, chanM i j ℓ Θ F x u := by
    calc (∫ p : Submission.BoseGases.X n × E3, chanR i j ℓ G Θ F p)
        = ∫ x : Submission.BoseGases.X n, ∫ u : E3, chanR i j ℓ G Θ F (x, u) :=
          MeasureTheory.integral_prod (chanR i j ℓ G Θ F) hIntR
      _ = ∫ x : Submission.BoseGases.X n, G x * ∫ u : E3, chanM i j ℓ Θ F x u := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          rw [chanR_apply, chanM_apply]
          ring
  -- ## assembly
  calc (∫ q : Submission.BoseGases.X n × (E3 × E3), chanL i j ℓ G Θ F q)
      = ∫ x : Submission.BoseGases.X n, G x * ∫ z : E3 × E3, chanK i j ℓ Θ F x z := hLHS
    _ = ∫ x : Submission.BoseGases.X n, G x * (((ℓ : ℂ)) ^ 3 * ∫ u : E3,
          chanM i j ℓ Θ F x u) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [hCore x]
    _ = ∫ x : Submission.BoseGases.X n, ((ℓ : ℂ)) ^ 3 * (G x * ∫ u : E3,
          chanM i j ℓ Θ F x u) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
    _ = ((ℓ : ℂ)) ^ 3 * ∫ x : Submission.BoseGases.X n, G x * ∫ u : E3,
          chanM i j ℓ Θ F x u := MeasureTheory.integral_const_mul _ _
    _ = ((ℓ : ℂ)) ^ 3 * ∫ p : Submission.BoseGases.X n × E3,
          chanR i j ℓ G Θ F p := by rw [← hRHS]

end Work.BoseBoxFock.PCFU
