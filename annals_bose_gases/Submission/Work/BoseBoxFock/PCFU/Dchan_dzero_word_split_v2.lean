import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.Dchan_eq_imageSum
import Submission.Work.BoseBoxFock.PCFU.aP_sym_box_L1
import Submission.Work.BoseBoxFock.PCFU.chiW1_integrable
import Submission.Work.BoseBoxFock.PCFU.integrableOn_pairKernel_lowSlot
import Submission.Work.BoseBoxFock.PCFU.lowSlot_aQ_aP_measurable_bounded
import Submission.Work.BoseFixB1S.fibreVoidB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## §1  Structural facts about the objects of the target -/

lemma update_update_comm_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : Submission.BoseGases.X n)
    (y z : E3) :
    (Function.update (Function.update x i y) j z) = Function.update (Function.update x j z) i y :=
  Function.update_comm hij y z x

/-- The `0`-translate of the bump is the corpus box bump: `χ_u` at `u = 0` is `χ_Λ`. -/
lemma chiU_zero_eq_chiLam (ℓ : ℝ) (x : E3) :
    Submission.BoseGases.chiU ℓ 0 x = Work.BoseK15.corpusBox.chiLam ℓ x := by
  simp [Submission.BoseGases.chiU, Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]

/-- The localised pair kernel at `u = 0` is `χ_Λ(x)·W₁(x−y)·χ_Λ(y)`. -/
lemma wLoc_g0_eq (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ℓ : ℝ) (x y : E3) :
    Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 x y
      = Work.BoseK15.corpusBox.chiLam ℓ x * Work.BoseFixR.W1fun v h ℓ (x - y)
        * Work.BoseK15.corpusBox.chiLam ℓ y := by
  rw [Submission.BoseGases.wLoc, Work.BoseFixR.W1fun, Submission.BoseGases.wScaled,
    chiU_zero_eq_chiLam, chiU_zero_eq_chiLam]

/-- **`χ_Λ` is supported in the centred cube `acube ℓ`**: `χ_Λ(x) ≠ 0` forces `‖x‖_∞ ≤ ℓ/2`. -/
lemma chiLam_supp_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.support (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Submission.BoseGases.acube ℓ := by
  intro x hx
  have hmem : (ℓ⁻¹) • x ∈ Work.BoseB4.unitCell := by
    refine Work.BoseK15.chi_support_subset_unitCell ?_
    simpa [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi] using hx
  intro m
  have h2 : |((ℓ⁻¹) • x) m| ≤ (1 / 2 : ℝ) := hmem m
  have h3 : |(ℓ⁻¹) * (x m)| ≤ (1 / 2 : ℝ) := by simpa using h2
  have h4 : |x m| ≤ ℓ / 2 := by
    have h5 : ℓ⁻¹ * |x m| ≤ 1 / 2 := by
      simpa [abs_mul, abs_of_pos (inv_pos.mpr hℓ)] using h3
    have h5' : |x m| / ℓ ≤ 1 / 2 := by
      rw [div_eq_mul_inv, mul_comm]
      exact h5
    have h8 := (div_le_iff₀ hℓ).mp h5'
    linarith
  exact ⟨by linarith [neg_abs_le (x m)], by linarith [le_abs_self (x m)]⟩

/-- The double slot mean unfolds as the double cube average. -/
lemma aP_two_unfold {n : ℕ} {ℓ : ℝ} {i j : Fin n} (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x
      = (1 / ℓ ^ 3) ^ 2 *
          ∫ y in Submission.BoseGases.acube ℓ,
            ∫ z in Submission.BoseGases.acube ℓ,
              Φ (Function.update (Function.update x i y) j z) := by
  simp only [Submission.BoseGases.aP]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- A function that is constant in the `i`-th slot stays so after a slot-`j` mean (`j ≠ i`). -/
lemma aP_update_eq_of_free {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ∀ x y, Φ (Function.update x i y) = Φ x) (x : Submission.BoseGases.X n) (y : E3) :
    Submission.BoseGases.aP ℓ j Φ (Function.update x i y) = Submission.BoseGases.aP ℓ j Φ x := by
  simp only [Submission.BoseGases.aP]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
    (fun z _ => ?_)
  rw [Function.update_comm hij y z x]
  exact hΦ (Function.update x j z) y

/-- **`ψ = Q_j P_i Θ` is constant in the `i`-th slot** (`i ≠ j`). -/
lemma aQ_aP_free {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    {Θ : Submission.BoseGases.X n → ℝ} :
    ∀ x y, Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
        (Function.update x i y)
      = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x := by
  intro x y
  have h1 : ∀ u v, Submission.BoseGases.aP ℓ i Θ (Function.update u i v)
      = Submission.BoseGases.aP ℓ i Θ u :=
    fun u v => Work.BoseBoxFock.Weak.aP_const_in_coord i Θ u v
  have h2 := aP_update_eq_of_free (ℓ := ℓ) hij h1 x y
  simp only [Submission.BoseGases.aQ]
  rw [h1 x y, h2]

/-- **The slot-`j` low-momentum lift of an `i`-free state is itself `i`-free** (`i ≠ j`):
replacing the `i`-th slot does not change `Γ_j ψ`. -/
lemma lowSlot_update_eq_of_free {n : ℕ} {ℓ κ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {ψ : Submission.BoseGases.X n → ℝ}
    (hψ : ∀ x y, ψ (Function.update x i y) = ψ x) (x : Submission.BoseGases.X n) (y : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x i y)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x := by
  have h1 : (Function.update x i y) j = x j := Function.update_of_ne hij.symm y x
  have h2 : (fun z : E3 => ψ (Function.update (Function.update x i y) j z))
      = fun z => ψ (Function.update x j z) := by
    funext z
    rw [Function.update_comm hij y z x]
    exact hψ (Function.update x j z) y
  simp only [Work.BoseBoxFix.lowSlot]
  rw [h1, h2]

/-! ## §2  Integrability of the pair kernel `χ_Λ(x)·W₁(x−y)·χ_Λ(y)` and one-slot bounds -/

/-- `χ_Λ` is bounded by `(∫χ²)^{-1/2}`. -/
lemma chiLam_abs_le (ℓ : ℝ) (x : E3) :
    |Work.BoseK15.corpusBox.chiLam ℓ x| ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  rw [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]
  exact Submission.BoseGases.abs_chi_le _

/-- `χ_Λ ≥ 0`. -/
lemma chiLam_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ Work.BoseK15.corpusBox.chiLam ℓ x := by
  rw [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]
  simpa using Work.BoseK15.corpusBox_chi_nonneg (ℓ⁻¹ • x)

/-- `χ_Λ` is continuous. -/
lemma chiLam_continuous (ℓ : ℝ) :
    Continuous (fun x : E3 => Work.BoseK15.corpusBox.chiLam ℓ x) := by
  rw [show (fun x : E3 => Work.BoseK15.corpusBox.chiLam ℓ x)
      = fun x : E3 => Submission.BoseGases.chi ((ℓ⁻¹) • x) by
    funext x
    rw [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]]
  exact Submission.BoseGases.chi_continuous.comp (continuous_const_smul _)

/-- In the dilute regime `R ≤ ℓ·chiR0` the renormalised kernel `W₁ = wScaled ℓ (g₀)` is
pointwise dominated by `2|g₀|`. -/
lemma abs_W1fun_le_two_g0 {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 ≤ R)
    (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (z : E3) :
    |Work.BoseFixR.W1fun v h ℓ z| ≤ 2 * |Submission.BoseGases.g0 v h z| := by
  rw [Work.BoseFixR.W1fun]
  exact Submission.BoseGases.wScaled_abs_le_two hℓ hR hRℓ
    (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) z

/-- `∫ y, |g₀(y + c)| = ∫ |g₀|`. -/
lemma integral_abs_g0_add_eq {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (c : E3) :
    (∫ y : E3, |Submission.BoseGases.g0 v h (y + c)|)
      = ∫ y : E3, |Submission.BoseGases.g0 v h y| := by
  rw [show (fun y : E3 => |Submission.BoseGases.g0 v h (y + c)|)
      = fun y : E3 => |Submission.BoseGases.g0 v h (c + y)| by
        funext y; rw [add_comm]]
  exact Submission.BoseGases.integral_comp_add_left
    (fun y : E3 => |Submission.BoseGases.g0 v h y|) c

/-- Integrability of `y ↦ |g₀(y + c)|`. -/
lemma integrable_abs_g0_add {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (c : E3) :
    Integrable (fun y : E3 => |Submission.BoseGases.g0 v h (y + c)|) := by
  have hg : Integrable (fun z : E3 => |Submission.BoseGases.g0 v h z|) :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).abs
  have hmp : MeasurePreserving (fun y : E3 => y + c) volume volume :=
    measurePreserving_add_right (μ := (volume : Measure E3)) c
  exact hmp.integrable_comp_of_integrable hg

/-- `∫ y, |g₀(y − c)| = ∫ |g₀|`. -/
lemma integral_abs_g0_sub'_eq {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (c : E3) :
    (∫ y : E3, |Submission.BoseGases.g0 v h (y - c)|)
      = ∫ y : E3, |Submission.BoseGases.g0 v h y| := by
  rw [show (fun y : E3 => |Submission.BoseGases.g0 v h (y - c)|)
      = fun y : E3 => |Submission.BoseGases.g0 v h (y + -c)| by
        funext y; rw [sub_eq_add_neg]]
  exact integral_abs_g0_add_eq h (-c)

/-- Integrability of `y ↦ |g₀(y − c)|`. -/
lemma integrable_abs_g0_sub' {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (c : E3) :
    Integrable (fun y : E3 => |Submission.BoseGases.g0 v h (y - c)|) := by
  rw [show (fun y : E3 => |Submission.BoseGases.g0 v h (y - c)|)
      = fun y : E3 => |Submission.BoseGases.g0 v h (y + -c)| by
        funext y; rw [sub_eq_add_neg]]
  exact integrable_abs_g0_add (v := v) (h := h) hR hv_supp (-c)

/-- `∫ y, |g₀(u − y)| = ∫ |g₀|`. -/
lemma integral_abs_g0_left_sub_eq {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (u : E3) :
    (∫ y : E3, |Submission.BoseGases.g0 v h (u - y)|)
      = ∫ y : E3, |Submission.BoseGases.g0 v h y| := by
  rw [show (fun y : E3 => |Submission.BoseGases.g0 v h (u - y)|)
      = fun y : E3 => |Submission.BoseGases.g0 v h (u + -y)| by
        funext y; rw [sub_eq_add_neg]]
  rw [Submission.BoseGases.integral_comp_neg
    (fun y : E3 => |Submission.BoseGases.g0 v h (u + y)|)]
  exact Submission.BoseGases.integral_comp_add_left
    (fun y : E3 => |Submission.BoseGases.g0 v h y|) u

/-- Integrability of `y ↦ |g₀(u − y)|`. -/
lemma integrable_abs_g0_left_sub {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (u : E3) :
    Integrable (fun y : E3 => |Submission.BoseGases.g0 v h (u - y)|) := by
  have hg : Integrable (fun z : E3 => |Submission.BoseGases.g0 v h z|) :=
    (Submission.BoseGases.g0_integrable hR hv_supp h).abs
  have hmp : MeasurePreserving (fun y : E3 => u - y) volume volume :=
    Submission.BoseGases.measurePreserving_sub_left u
  exact hmp.integrable_comp_of_integrable hg

/-- `∫_{z∈acube ℓ} |g₀(u − z)| ≤ ∫ |g₀|`. -/
lemma setIntegral_abs_g0_left_sub_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ : ℝ} (u : E3) :
    (∫ z in Submission.BoseGases.acube ℓ, |Submission.BoseGases.g0 v h (u - z)|)
      ≤ ∫ z : E3, |Submission.BoseGases.g0 v h z| := by
  rw [← integral_abs_g0_left_sub_eq h u]
  exact MeasureTheory.setIntegral_le_integral
    (integrable_abs_g0_left_sub (v := v) (h := h) hR hv_supp u)
    (Filter.Eventually.of_forall (fun z => abs_nonneg _))

/-- `∫_{z∈acube ℓ} |g₀(z − c)| ≤ ∫ |g₀|`. -/
lemma setIntegral_abs_g0_sub'_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ : ℝ} (c : E3) :
    (∫ z in Submission.BoseGases.acube ℓ, |Submission.BoseGases.g0 v h (z - c)|)
      ≤ ∫ z : E3, |Submission.BoseGases.g0 v h z| := by
  rw [← integral_abs_g0_sub'_eq h c]
  exact MeasureTheory.setIntegral_le_integral
    (integrable_abs_g0_sub' (v := v) (h := h) hR hv_supp c)
    (Filter.Eventually.of_forall (fun z => abs_nonneg _))

/-- **`W₁ = wScaled ℓ (g₀)` is `L¹`** in the dilute regime. -/
lemma W1fun_integrable {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    Integrable (Work.BoseFixR.W1fun v h ℓ) := by
  rw [Work.BoseFixR.W1fun]
  exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ

/-- A.e.-measurability of the shifted kernel `y ↦ W₁(y + c)`. -/
lemma aemeasurable_W1fun_add {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (c : E3) :
    AEMeasurable (fun y : E3 => Work.BoseFixR.W1fun v h ℓ (y + c)) volume := by
  have hmp : MeasurePreserving (fun y : E3 => y + c) volume volume :=
    measurePreserving_add_right (μ := (volume : Measure E3)) c
  have h1 : AEMeasurable (Work.BoseFixR.W1fun v h ℓ)
      (volume.map (fun y : E3 => y + c)) := by
    rw [hmp.map_eq]
    exact (W1fun_integrable (v := v) (h := h) hR hℓ hv_supp hRℓ).aemeasurable
  exact AEMeasurable.comp_measurable h1 (by fun_prop)

/-- A.e.-measurability of the reflected kernel `y ↦ W₁(u − y)`. -/
lemma aemeasurable_W1fun_left {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : E3) :
    AEMeasurable (fun y : E3 => Work.BoseFixR.W1fun v h ℓ (u - y)) volume := by
  have hmp : MeasurePreserving (fun y : E3 => u - y) volume volume :=
    Submission.BoseGases.measurePreserving_sub_left u
  have h1 : AEMeasurable (Work.BoseFixR.W1fun v h ℓ)
      (volume.map (fun y : E3 => u - y)) := by
    rw [hmp.map_eq]
    exact (W1fun_integrable (v := v) (h := h) hR hℓ hv_supp hRℓ).aemeasurable
  exact AEMeasurable.comp_measurable h1 (by fun_prop)

/-- **`chiW1_integrable` with the corpus bump**: the pair kernel `χ_Λ(x)W₁(x−y)χ_Λ(y)` is
integrable on `ℝ³ × ℝ³`. -/
lemma chiW1_chiLam_integrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Integrable (fun p : E3 × E3 =>
      (Work.BoseK15.corpusBox.chiLam ℓ p.1) * (Work.BoseFixR.W1fun v h ℓ (p.1 - p.2))
        * (Work.BoseK15.corpusBox.chiLam ℓ p.2))
      ((volume : Measure E3).prod volume) := by
  refine (chiW1_integrable h hℓ).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Submission.BoseGases.chiScale, Work.BoseB4.BoxData.chiLam,
    Work.BoseK15.corpusBox_chi]

/-- **Joint integrability of the `(y,z)`-integrand** of the slot identity: for a measurable
`Γ` bounded by `K`, the function `(y,z) ↦ χ_Λ(y)W₁(y−z)χ_Λ(z)Γ(x[j↦z])` is integrable on
`volume × volume`. -/
lemma integrable_pair_kernel_gamma {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) {Γ : Submission.BoseGases.X n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hΓm : Measurable Γ) (hΓb : ∀ y, |Γ y| ≤ K) (x : Submission.BoseGases.X n) :
    Integrable (Function.uncurry fun (y z : E3) =>
      (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
        * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z))
      ((volume : Measure E3).prod volume) := by
  set kern : E3 × E3 → ℝ := fun p =>
    (Work.BoseK15.corpusBox.chiLam ℓ p.1) * (Work.BoseFixR.W1fun v h ℓ (p.1 - p.2))
      * (Work.BoseK15.corpusBox.chiLam ℓ p.2) with hkern
  have hkint : Integrable kern ((volume : Measure E3).prod volume) := chiW1_chiLam_integrable h hℓ
  have hGm : AEMeasurable (fun p : E3 × E3 => Γ (Function.update x j p.2))
      ((volume : Measure E3).prod volume) :=
    (hΓm.comp (by fun_prop : Measurable fun p : E3 × E3 => Function.update x j p.2)).aemeasurable
  have hFeq : (Function.uncurry fun (y z : E3) =>
        (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z))
      = fun p : E3 × E3 => kern p * Γ (Function.update x j p.2) := rfl
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (y z : E3) =>
        (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z))
      ((volume : Measure E3).prod volume) := by
    rw [hFeq]
    exact (hkint.aemeasurable.mul hGm).aestronglyMeasurable
  refine Integrable.mono' (hkint.norm.const_mul K) hmeas
    (Filter.Eventually.of_forall fun p => ?_)
  show ‖kern p * Γ (Function.update x j p.2)‖ ≤ K * ‖kern p‖
  rw [Real.norm_eq_abs, abs_mul]
  calc |kern p| * |Γ (Function.update x j p.2)| ≤ |kern p| * K :=
        mul_le_mul_of_nonneg_left (hΓb _) (abs_nonneg _)
    _ = K * ‖kern p‖ := by rw [Real.norm_eq_abs]; ring

/-- **Boundedness of `Ĉ(z) = ∫_y χ_Λ(y)W₁(y−z) dy`** in the dilute regime. -/
lemma chiHat_abs_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3,
      |∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))| ≤ C := by
  refine ⟨2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
      (∫ z : E3, |Submission.BoseGases.g0 v h z|), by positivity, fun z => ?_⟩
  have hdom : ∀ y : E3,
      |(Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))|
        ≤ 2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
            |Submission.BoseGases.g0 v h (y - z)| := by
    intro y
    rw [abs_mul]
    have h1 := chiLam_abs_le ℓ y
    have h2 := abs_W1fun_le_two_g0 (v := v) (h := h) hR.le hℓ hv_supp hRℓ (y - z)
    have h3 : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by positivity
    calc |Work.BoseK15.corpusBox.chiLam ℓ y| * |Work.BoseFixR.W1fun v h ℓ (y - z)|
        ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
            * (2 * |Submission.BoseGases.g0 v h (y - z)|) :=
          mul_le_mul h1 h2 (abs_nonneg _) h3
      _ = 2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
            * |Submission.BoseGases.g0 v h (y - z)| := by ring
  have hg : Integrable (fun y : E3 =>
      2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
        |Submission.BoseGases.g0 v h (y - z)|) :=
    (integrable_abs_g0_sub' (v := v) (h := h) hR hv_supp z).const_mul _
  have hf : Integrable (fun y : E3 =>
      |(Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))|) := by
    refine Integrable.mono' hg ?_
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_abs]; exact hdom y))
    have hWm : AEMeasurable (fun y : E3 => Work.BoseFixR.W1fun v h ℓ (y + -z)) volume :=
      aemeasurable_W1fun_add (v := v) (h := h) hR hℓ hv_supp hRℓ (-z)
    have hfun : (fun y : E3 =>
          |(Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))|)
        = fun y : E3 =>
          |(Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y + -z))| := by
      funext y; rw [sub_eq_add_neg]
    rw [hfun]
    exact (((chiLam_continuous ℓ).aemeasurable).mul hWm).abs.aestronglyMeasurable
  have step1 : |∫ y : E3,
        (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))|
      ≤ ∫ y : E3,
          |(Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun y : E3 => (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z)))
  calc |∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))|
      ≤ ∫ y : E3,
          |(Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))| := step1
    _ ≤ ∫ y : E3, 2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
          |Submission.BoseGases.g0 v h (y - z)| := integral_mono hf hg hdom
    _ = 2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
          ∫ y : E3, |Submission.BoseGases.g0 v h (y - z)| := by
        rw [MeasureTheory.integral_const_mul]
    _ = 2 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ *
          ∫ y : E3, |Submission.BoseGases.g0 v h y| := by rw [integral_abs_g0_sub'_eq h z]

/-- **The slot mean of the localised pair kernel is uniformly bounded**: the cube average of
`χ_Λ W₁(y−z) χ_Λ` smears the `L¹`-kernel into a bounded function. -/
lemma aP_wLoc_gamma_abs_le {n : ℕ} {i j : Fin n} (hij : i ≠ j) {v : E3 → ℝ}
    {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {Γ : Submission.BoseGases.X n → ℝ} {K : ℝ} (hK : 0 ≤ K) (hΓm : Measurable Γ)
    (hΓb : ∀ y, |Γ y| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Submission.BoseGases.X n,
      |Submission.BoseGases.aP ℓ j (fun y =>
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y) x|
        ≤ C := by
  set chiInf : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hchiInf
  have hchiInf0 : 0 ≤ chiInf := by rw [hchiInf]; positivity
  refine ⟨(1 / ℓ ^ 3) * (chiInf * chiInf * K * 2) * (∫ z : E3, |Submission.BoseGases.g0 v h z|),
    by positivity, fun x => ?_⟩
  have hexp : ∀ z : E3,
      Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0
          (Function.update x j z i) (Function.update x j z j) * Γ (Function.update x j z)
        = (Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
            * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z) := by
    intro z
    rw [Function.update_of_ne hij z x, Function.update_self, wLoc_g0_eq v h ℓ (x i) z]
  have hpt : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |(Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)|
        ≤ (chiInf * chiInf * K * 2) * |Submission.BoseGases.g0 v h (x i - z)| := by
    intro z _
    rw [abs_mul, abs_mul, abs_mul]
    have h1 : |Work.BoseK15.corpusBox.chiLam ℓ (x i)| ≤ chiInf := by
      rw [hchiInf]; exact chiLam_abs_le ℓ (x i)
    have h2 : |Work.BoseK15.corpusBox.chiLam ℓ z| ≤ chiInf := by
      rw [hchiInf]; exact chiLam_abs_le ℓ z
    have h3 : |Work.BoseFixR.W1fun v h ℓ (x i - z)|
        ≤ 2 * |Submission.BoseGases.g0 v h (x i - z)| :=
      abs_W1fun_le_two_g0 (v := v) (h := h) hR.le hℓ hv_supp hRℓ (x i - z)
    have h4 : |Γ (Function.update x j z)| ≤ K := hΓb _
    have A : |Work.BoseK15.corpusBox.chiLam ℓ (x i)| * |Work.BoseK15.corpusBox.chiLam ℓ z|
        ≤ chiInf * chiInf := mul_le_mul h1 h2 (abs_nonneg _) hchiInf0
    have B : |Work.BoseFixR.W1fun v h ℓ (x i - z)| * |Γ (Function.update x j z)|
        ≤ (2 * |Submission.BoseGases.g0 v h (x i - z)|) * K :=
      mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
    calc |Work.BoseK15.corpusBox.chiLam ℓ (x i)| * |Work.BoseFixR.W1fun v h ℓ (x i - z)|
          * |Work.BoseK15.corpusBox.chiLam ℓ z| * |Γ (Function.update x j z)|
        = (|Work.BoseK15.corpusBox.chiLam ℓ (x i)| * |Work.BoseK15.corpusBox.chiLam ℓ z|)
          * (|Work.BoseFixR.W1fun v h ℓ (x i - z)| * |Γ (Function.update x j z)|) := by
          ring
      _ ≤ (chiInf * chiInf) * ((2 * |Submission.BoseGases.g0 v h (x i - z)|) * K) :=
          mul_le_mul A B (by positivity) (by positivity)
      _ = (chiInf * chiInf * K * 2) * |Submission.BoseGases.g0 v h (x i - z)| := by ring
  have haP : Submission.BoseGases.aP ℓ j (fun y =>
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y) x
      = (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ,
          ((Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
            * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)) := by
    simp only [Submission.BoseGases.aP]
    congr 1
    exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun z _ => hexp z)
  have hpsint : IntegrableOn (fun z : E3 =>
      (chiInf * chiInf * K * 2) * |Submission.BoseGases.g0 v h (x i - z)|)
      (Submission.BoseGases.acube ℓ) volume :=
    ((integrable_abs_g0_left_sub (v := v) (h := h) hR hv_supp (x i)).const_mul _).integrableOn
  have hphm : AEMeasurable (fun z : E3 =>
      |(Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
        * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)|) volume := by
    have hWm : AEMeasurable (fun z : E3 => Work.BoseFixR.W1fun v h ℓ (x i - z)) volume :=
      aemeasurable_W1fun_left (v := v) (h := h) hR hℓ hv_supp hRℓ (x i)
    have hGc : AEMeasurable (fun z : E3 => Γ (Function.update x j z)) volume :=
      (hΓm.comp (by fun_prop : Measurable fun z : E3 => Function.update x j z)).aemeasurable
    exact ((((aemeasurable_const.mul hWm).mul
      ((chiLam_continuous ℓ).aemeasurable)).mul hGc).abs)
  have hpint : IntegrableOn (fun z : E3 =>
      |(Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
        * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)|)
      (Submission.BoseGases.acube ℓ) volume := by
    refine Integrable.mono' hpsint
      (hphm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)]
      with z hz
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt z hz
  have hmono : (∫ z in Submission.BoseGases.acube ℓ,
        |(Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)|)
      ≤ ∫ z in Submission.BoseGases.acube ℓ,
          (chiInf * chiInf * K * 2) * |Submission.BoseGases.g0 v h (x i - z)| := by
    refine integral_mono_ae hpint hpsint ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)]
      with z hz
    exact hpt z hz
  rw [haP, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3) * |∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)|
      ≤ (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ,
          |(Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
            * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)| :=
        mul_le_mul_of_nonneg_left (by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) (fun z : E3 =>
              (Work.BoseK15.corpusBox.chiLam ℓ (x i)) * (Work.BoseFixR.W1fun v h ℓ (x i - z))
                * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)))) (by positivity)
    _ ≤ (1 / ℓ ^ 3) * ∫ z in Submission.BoseGases.acube ℓ,
          (chiInf * chiInf * K * 2) * |Submission.BoseGases.g0 v h (x i - z)| :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (1 / ℓ ^ 3) * ((chiInf * chiInf * K * 2) * ∫ z in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.g0 v h (x i - z)|) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (1 / ℓ ^ 3) * ((chiInf * chiInf * K * 2) * ∫ z : E3,
          |Submission.BoseGases.g0 v h z|) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        exact setIntegral_abs_g0_left_sub_le (v := v) (h := h) hR hv_supp (x i)
    _ = (1 / ℓ ^ 3) * (chiInf * chiInf * K * 2)
          * (∫ z : E3, |Submission.BoseGases.g0 v h z|) := by ring

/-- The `k`-frame `KχfrU` is bounded (a finite sum of unimodular phases). -/
lemma KχfrU_norm_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z‖ ≤ C := by
  refine ⟨∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k|, ?_, fun z => ?_⟩
  · exact Finset.sum_nonneg fun k _ => abs_nonneg _
  · rw [Work.BoseBoxFock.PCFU.KχfrU]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]

/-! ## §3  The slot identity: the `Ĉ`-integral is `ℓ⁶` times the double slot mean -/

/-- **The slot identity (★)**.  For a state `Γ` that is constant in the `i`-th slot and bounded
by `K`, the `z`-integral of `χ_Λ(z)·Ĉ(z)·Γ(x[j↦z])` with `Ĉ(z) = ∫_y χ_Λ(y)W₁(y−z) dy` equals
`ℓ⁶` times the double slot mean of the localised pair kernel `χ_Λ(y)W₁(y−z)χ_Λ(z)Γ`. -/
lemma star_identity {n : ℕ} {i j : Fin n} (hij : i ≠ j) {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {ℓ : ℝ} (hℓ : 0 < ℓ) {Γ : Submission.BoseGases.X n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hΓm : Measurable Γ) (hΓb : ∀ y, |Γ y| ≤ K)
    (hΓi : ∀ x y, Γ (Function.update x i y) = Γ x) (x : Submission.BoseGases.X n) :
    (∫ z : E3, (Work.BoseK15.corpusBox.chiLam ℓ z)
        * (∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z)))
        * Γ (Function.update x j z))
      = ℓ ^ 6 * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j
          (fun y => Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y))
            x := by
  set B : Submission.BoseGases.X n → ℝ := fun y =>
    Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y with hBdef
  have hBpt : ∀ y z : E3, B (Function.update (Function.update x i y) j z)
      = (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
        * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z) := by
    intro y z
    have hc1 : (Function.update (Function.update x i y) j z) i = y := by
      rw [Function.update_of_ne hij z (Function.update x i y), Function.update_self]
    have hc2 : (Function.update (Function.update x i y) j z) j = z :=
      Function.update_self j z (Function.update x i y)
    have hGeq : Γ (Function.update (Function.update x i y) j z) = Γ (Function.update x j z) := by
      rw [Function.update_comm hij y z x]
      exact hΓi (Function.update x j z) y
    rw [hBdef]
    simp only [hc1, hc2, hGeq, wLoc_g0_eq v h ℓ y z]
  have hRHS : ℓ ^ 6 * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
            * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z) := by
    rw [aP_two_unfold]
    have hconst : ℓ ^ 6 * (1 / ℓ ^ 3) ^ 2 = 1 := by
      field_simp
    rw [← mul_assoc, hconst, one_mul]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y _ => ?_)
    exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun z _ => hBpt y z)
  rw [hRHS]
  -- the left-hand side as a double integral over `ℝ³ × ℝ³`
  have hLHS1 : (∫ z : E3, (Work.BoseK15.corpusBox.chiLam ℓ z)
        * (∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z)))
        * Γ (Function.update x j z))
      = ∫ z : E3, ∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ z)
          * ((Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
              * Γ (Function.update x j z)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [mul_assoc, (MeasureTheory.integral_mul_const _ _).symm,
      ← MeasureTheory.integral_const_mul]
  rw [hLHS1]
  -- integrability of the swapped uncurried integrand
  have hint : Integrable (Function.uncurry fun (y z : E3) =>
      (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
        * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z))
      ((volume : Measure E3).prod volume) :=
    integrable_pair_kernel_gamma (v := v) h hℓ (j := j) (K := K) hK hΓm hΓb x
  have hint' : Integrable (Function.uncurry fun (z y : E3) =>
      (Work.BoseK15.corpusBox.chiLam ℓ z)
        * ((Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
            * Γ (Function.update x j z)))
      ((volume : Measure E3).prod volume) := by
    have hswap := hint.swap
    have hfun : ((Function.uncurry fun (y z : E3) =>
        (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)) ∘ Prod.swap)
        = Function.uncurry fun (z y : E3) =>
            (Work.BoseK15.corpusBox.chiLam ℓ z)
              * ((Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
                  * Γ (Function.update x j z)) := by
      funext p
      obtain ⟨a, b⟩ := p
      rw [Function.comp_apply, Prod.swap_prod_mk]
      show (Work.BoseK15.corpusBox.chiLam ℓ b) * (Work.BoseFixR.W1fun v h ℓ (b - a))
            * (Work.BoseK15.corpusBox.chiLam ℓ a) * Γ (Function.update x j a)
          = (Work.BoseK15.corpusBox.chiLam ℓ a)
            * ((Work.BoseK15.corpusBox.chiLam ℓ b) * (Work.BoseFixR.W1fun v h ℓ (b - a))
                * Γ (Function.update x j a))
      ring_nf
    rw [hfun] at hswap
    exact hswap
  rw [MeasureTheory.integral_integral_swap hint']
  -- rearrange the (commuting) factors pointwise
  have hstep1 : (∫ y : E3, ∫ z : E3, (Work.BoseK15.corpusBox.chiLam ℓ z)
        * ((Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
            * Γ (Function.update x j z)))
      = ∫ y : E3, ∫ z : E3, (Work.BoseK15.corpusBox.chiLam ℓ y)
          * (Work.BoseFixR.W1fun v h ℓ (y - z)) * (Work.BoseK15.corpusBox.chiLam ℓ z)
          * Γ (Function.update x j z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [hstep1]
  -- the support reduction: the integrand vanishes unless `y, z ∈ acube ℓ`
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.acube ℓ) (f := fun y : E3 => ∫ z in Submission.BoseGases.acube ℓ,
      (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
        * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z)) (fun y hy => ?_)]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hz0 : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
        (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))
          * (Work.BoseK15.corpusBox.chiLam ℓ z) * Γ (Function.update x j z) = 0 := by
      intro z hz
      have hχ0 : Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
        by_contra hne
        exact hz (chiLam_supp_acube hℓ (Function.mem_support.mpr hne))
      rw [hχ0, mul_zero, zero_mul]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hz0).symm
  · refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun z _ => ?_)
    have hχ0 : Work.BoseK15.corpusBox.chiLam ℓ y = 0 := by
      by_contra hne
      exact hy (chiLam_supp_acube hℓ (Function.mem_support.mpr hne))
    rw [hχ0, zero_mul, zero_mul, zero_mul]

/-! ## §4  The real core: the box pairing with the slot means moved onto `Θ` -/

/-- An a.e.-strongly-measurable function bounded by `C` is integrable on the centred box. -/
lemma integrableOn_of_bdd {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Submission.BoseGases.X n → ℝ}
    {C : ℝ} (hfm : AEStronglyMeasurable f (volume.restrict (Submission.BoseGases.abox n ℓ)))
    (hfb : ∀ x, |f x| ≤ C) :
    IntegrableOn f (Submission.BoseGases.abox n ℓ) volume :=
  IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le) hfm
    C (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb x)

/-- A bounded measurable factor of a function integrable on the box is again integrable there. -/
lemma integrableOn_mul_of_bdd {n : ℕ} {ℓ : ℝ} {f g : Submission.BoseGases.X n → ℝ} {C : ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ C)
    (hg : IntegrableOn g (Submission.BoseGases.abox n ℓ) volume) :
    IntegrableOn (fun x => f x * g x) (Submission.BoseGases.abox n ℓ) volume := by
  refine Integrable.mono' (hg.norm.const_mul C)
    (hfm.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hfb x) (abs_nonneg _)

/-! ## §3bis  A.e.-strong measurability of slot means of `L¹`-on-the-box functions -/

/-- **A slot mean of a function which is `L¹` on the box is a.e. strongly measurable there.**
`aP ℓ j B = ℓ⁻³ ∫_{z∈acube ℓ} B(x[j↦z]) dz`, and the collapsing map `(x,z) ↦ update x j z`
pushes `(vol ↾ abox) × (vol ↾ acube)` onto `ℓ³ • (vol ↾ abox)`
(`Work.BoseFixB1S.pushforward_update_abox`).  Hence the null set of a measurable representative
of `B` pulls back to a null set of the product, and the slot mean is a.e. equal to the (strongly
measurable) slot mean of that representative. -/
lemma aeStronglyMeasurable_aP_of_integrableOn {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {B : Submission.BoseGases.X n → ℝ}
    (hB : IntegrableOn B (Submission.BoseGases.abox n ℓ) volume) :
    AEStronglyMeasurable (Submission.BoseGases.aP ℓ j B)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
  classical
  set μ : Measure (Submission.BoseGases.X n) := volume.restrict (Submission.BoseGases.abox n ℓ)
    with hμ
  set ν : Measure E3 := volume.restrict (Submission.BoseGases.acube ℓ) with hν
  set B' : Submission.BoseGases.X n → ℝ := hB.aestronglyMeasurable.mk B with hB'def
  have hB'm : Measurable B' := hB.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hB'ae : B =ᵐ[μ] B' := hB.aestronglyMeasurable.ae_eq_mk
  set F : Submission.BoseGases.X n × E3 → Submission.BoseGases.X n :=
    fun p => Function.update p.1 j p.2 with hFdef
  have hFm : Measurable F := by rw [hFdef]; fun_prop
  have hpush : Measure.map F (μ.prod ν) = ν Set.univ • μ := by
    rw [hμ, hν, hFdef]
    exact Work.BoseFixB1S.pushforward_update_abox (n := n) (ℓ := ℓ) hℓ j
  have hae : (B ∘ F) =ᵐ[μ.prod ν] (B' ∘ F) := by
    show ∀ᵐ p ∂(μ.prod ν), (B ∘ F) p = (B' ∘ F) p
    have hS : μ {y : Submission.BoseGases.X n | ¬ (B y = B' y)} = 0 := by
      rw [← MeasureTheory.ae_iff]
      exact hB'ae
    have hS'0 : μ (MeasureTheory.toMeasurable μ {y : Submission.BoseGases.X n | ¬ (B y = B' y)})
        = 0 := by
      rw [MeasureTheory.measure_toMeasurable]
      exact hS
    rw [MeasureTheory.ae_iff]
    refine le_antisymm ?_ zero_le
    have hsub : {p : Submission.BoseGases.X n × E3 | ¬ (B (F p) = B' (F p))}
        ⊆ F ⁻¹' (MeasureTheory.toMeasurable μ
            {y : Submission.BoseGases.X n | ¬ (B y = B' y)}) := by
      intro p hp
      exact MeasureTheory.subset_toMeasurable μ _
        (by simpa [Function.comp_apply] using hp)
    calc (μ.prod ν) {p : Submission.BoseGases.X n × E3 | ¬ (B (F p) = B' (F p))}
        ≤ (μ.prod ν) (F ⁻¹' (MeasureTheory.toMeasurable μ
            {y : Submission.BoseGases.X n | ¬ (B y = B' y)})) := measure_mono hsub
      _ = (Measure.map F (μ.prod ν)) (MeasureTheory.toMeasurable μ
            {y : Submission.BoseGases.X n | ¬ (B y = B' y)}) := by
          rw [Measure.map_apply hFm (MeasureTheory.measurableSet_toMeasurable ..)]
      _ = (ν Set.univ • μ) (MeasureTheory.toMeasurable μ
            {y : Submission.BoseGases.X n | ¬ (B y = B' y)}) := by rw [hpush]
      _ = ν Set.univ * μ (MeasureTheory.toMeasurable μ
            {y : Submission.BoseGases.X n | ¬ (B y = B' y)}) := Measure.smul_apply ..
      _ = 0 := by rw [hS'0, mul_zero]
  have hcomp : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 => B (F p))
      (μ.prod ν) :=
    ((hB'm.comp hFm).aestronglyMeasurable).congr hae.symm
  have hint : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∫ z : E3, B (Function.update x j z) ∂ν) μ := hcomp.integral_prod_right'
  have hgoal : Submission.BoseGases.aP ℓ j B
      = fun x : Submission.BoseGases.X n => (1 / ℓ ^ 3) * ∫ z : E3, B (Function.update x j z) ∂ν := by
    funext x
    rw [Submission.BoseGases.aP, hν]
  rw [hgoal]
  exact hint.const_mul _

/-- **Measurability of `Ĉ(z) = ∫_y χ_Λ(y)W₁(y−z) dy`** in the dilute regime.  Writing
`Ĉ z = ∫_u W₁(u)·χ_Λ(z+u) du` (translation invariance), the joint integrand is a.e. measurable
because `W₁` is a.e. measurable, and a parametric integral of an a.e.-strongly-measurable
function is a.e. strongly measurable. -/
lemma aemeasurable_chiHat {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    AEMeasurable (fun z : E3 => ∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y)
      * (Work.BoseFixR.W1fun v h ℓ (y - z))) volume := by
  have hW : AEMeasurable (Work.BoseFixR.W1fun v h ℓ) volume :=
    (W1fun_integrable (v := v) (h := h) hR hℓ hv_supp hRℓ).aemeasurable
  have hjoint : AEStronglyMeasurable (fun p : E3 × E3 =>
      (Work.BoseFixR.W1fun v h ℓ) p.2 * (Work.BoseK15.corpusBox.chiLam ℓ (p.1 + p.2)))
      (volume.prod volume) :=
    ((hW.comp_snd).mul
      (((chiLam_continuous ℓ).comp (by fun_prop : Continuous
        fun p : E3 × E3 => p.1 + p.2)).aemeasurable)).aestronglyMeasurable
  have hAE : AEStronglyMeasurable (fun z : E3 => ∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y)
      * (Work.BoseFixR.W1fun v h ℓ (y - z))) volume := by
    refine (hjoint.integral_prod_right').congr ?_
    filter_upwards with z
    have h1 : (∫ u : E3, (Work.BoseFixR.W1fun v h ℓ) u
          * (Work.BoseK15.corpusBox.chiLam ℓ (z + u)))
        = ∫ u : E3, (Work.BoseK15.corpusBox.chiLam ℓ (z + u))
            * (Work.BoseFixR.W1fun v h ℓ ((z + u) - z)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [mul_comm]
      congr 1
      abel
    rw [h1]
    exact Submission.BoseGases.integral_comp_add_left
      (fun y : E3 => (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z))) z
  exact hAE.aemeasurable

/-- Bounded functions supported in the cube are integrable on `ℝ³`. -/
lemma integrable_of_support_acube {ℓ C : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hfb : ∀ z, ‖f z‖ ≤ C)
    (hs : ∀ z, z ∉ Submission.BoseGases.acube ℓ → f z = 0) :
    Integrable f volume := by
  have hOn : IntegrableOn f (Submission.BoseGases.acube ℓ) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      (hfm.mono_measure Measure.restrict_le_self) C (Filter.Eventually.of_forall hfb)
  have h1 : Integrable ((Submission.BoseGases.acube ℓ).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)).mpr hOn
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]
    exact (hs z hz).symm

/-- Bounded a.e.-strongly-measurable functions supported in the box are integrable on `X n`. -/
lemma integrable_of_support_abox {n : ℕ} {ℓ C : ℝ} (hℓ : 0 < ℓ) {f : Submission.BoseGases.X n → ℂ}
    (hfm : AEStronglyMeasurable f volume) (hfb : ∀ x, ‖f x‖ ≤ C)
    (hs : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → f x = 0) :
    Integrable f volume := by
  have hOn : IntegrableOn f (Submission.BoseGases.abox n ℓ) volume :=
    IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hfm.mono_measure Measure.restrict_le_self) C (Filter.Eventually.of_forall hfb)
  have h1 : Integrable ((Submission.BoseGases.abox n ℓ).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff (Submission.BoseGases.abox_measurable n ℓ)).mpr hOn
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact (hs x hx).symm

/-- **The real core of the `(D)`-channel word split.**  For a state `Γ` constant in the `i`-th
slot, bounded by `K`, with `wLoc·Γ` integrable on the box, and a bounded measurable `Θ` supported
in the box, the `Ĉ`-integral pairing equals `ℓ⁶` times the box pairing of the localised pair
kernel with the two slot means on `Θ`. -/
lemma real_core {n : ℕ} {i j : Fin n} (hij : i ≠ j) {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {Γ : Submission.BoseGases.X n → ℝ} {K : ℝ} (hK : 0 ≤ K) (hΓm : Measurable Γ)
    (hΓb : ∀ y, |Γ y| ≤ K) (hΓi : ∀ x y, Γ (Function.update x i y) = Γ x)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ)
    {C : ℝ} (hC : 0 ≤ C) (hΘb : ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hBint : IntegrableOn (fun y : Submission.BoseGases.X n =>
      Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y)
      (Submission.BoseGases.abox n ℓ) volume) :
    (∫ x : Submission.BoseGases.X n, Θ x * (∫ z : E3,
        (Work.BoseK15.corpusBox.chiLam ℓ z)
          * (∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z)))
          * Γ (Function.update x j z)))
      = ℓ ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x
            * (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j) * Γ x)) := by
  set B : Submission.BoseGases.X n → ℝ := fun y =>
    Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y with hBdef
  have hBint' : IntegrableOn B (Submission.BoseGases.abox n ℓ) volume := hBint
  have hstar : ∀ x, (∫ z : E3,
        (Work.BoseK15.corpusBox.chiLam ℓ z)
          * (∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z)))
          * Γ (Function.update x j z))
      = ℓ ^ 6 * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x :=
    fun x => star_identity hij hℓ hK hΓm hΓb hΓi x
  have hPΘm : Measurable (Submission.BoseGases.aP ℓ i Θ) :=
    Work.BoseBoxFock.Weak.aP_measurable i hΘm
  have hPΘb : ∀ x, |Submission.BoseGases.aP ℓ i Θ x| ≤ C :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓ i hC hΘb x
  obtain ⟨D₂, hD₂0, hD₂b⟩ := aP_wLoc_gamma_abs_le hij hR hℓ hv_supp hRℓ hK hΓm hΓb
  have hPjBae : AEStronglyMeasurable (Submission.BoseGases.aP ℓ j B)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    aeStronglyMeasurable_aP_of_integrableOn hℓ j hBint'
  have hPjBint : IntegrableOn (Submission.BoseGases.aP ℓ j B)
      (Submission.BoseGases.abox n ℓ) volume :=
    integrableOn_of_bdd (C := D₂) hℓ hPjBae hD₂b
  have hPiPjBae : AEStronglyMeasurable (Submission.BoseGases.aP ℓ i
        (Submission.BoseGases.aP ℓ j B)) (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    aeStronglyMeasurable_aP_of_integrableOn hℓ i hPjBint
  have hPiPjBb : ∀ x, |Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x| ≤ D₂ :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓ i hD₂0 hD₂b x
  have hPjPiΘb : ∀ x, |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ C :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓ j hC hPΘb x
  have hΘae : AEStronglyMeasurable Θ (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    hΘm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hzero : ∀ x : Submission.BoseGases.X n, x ∉ Submission.BoseGases.abox n ℓ →
      Θ x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x = 0 := by
    intro x hx
    have h0 : Θ x = 0 := by
      by_contra hne
      exact hx (hΘs (Function.mem_support.mpr hne))
    rw [h0, zero_mul]
  have hL : (∫ x : Submission.BoseGases.X n, Θ x * (∫ z : E3,
        (Work.BoseK15.corpusBox.chiLam ℓ z)
          * (∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y) * (Work.BoseFixR.W1fun v h ℓ (y - z)))
          * Γ (Function.update x j z)))
      = ∫ x : Submission.BoseGases.X n,
          Θ x * (ℓ ^ 6 * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [hstar x])
  have hL2 : (∫ x : Submission.BoseGases.X n,
        Θ x * (ℓ ^ 6 * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x))
      = ℓ ^ 6 * ∫ x : Submission.BoseGases.X n,
          Θ x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x := by
    rw [show (fun x : Submission.BoseGases.X n =>
          Θ x * (ℓ ^ 6 * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x))
        = fun x : Submission.BoseGases.X n =>
          (ℓ ^ 6) * (Θ x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x) from
      funext fun x => by ring]
    rw [MeasureTheory.integral_const_mul]
  have hR : (∫ x : Submission.BoseGases.X n,
        Θ x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Θ x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  rw [hL, hL2, hR]
  congr 1
  have hs1 : (∫ x in Submission.BoseGases.abox n ℓ,
        Θ x * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j B) x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Θ x * Submission.BoseGases.aP ℓ j B x :=
    (aP_sym_box_L1 hℓ i
      (integrableOn_mul_of_bdd hPΘm hPΘb hPjBint)
      (integrableOn_of_bdd (C := C * D₂) hℓ (hΘae.mul hPiPjBae) (fun x => by
        rw [abs_mul]
        exact mul_le_mul (hΘb x) (hPiPjBb x) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hΘb x))))).symm
  have hs2 : (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Θ x * Submission.BoseGases.aP ℓ j B x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x * B x :=
    (aP_sym_box_L1 hℓ j
      (integrableOn_mul_of_bdd (Work.BoseBoxFock.Weak.aP_measurable j hPΘm) hPjPiΘb hBint')
      (integrableOn_mul_of_bdd hPΘm hPΘb hPjBint)).symm
  have hcomm : (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x * B x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x * B x := by
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
      (fun x _ => ?_)
    rw [Work.BoseBoxFock.Weak.aP_comm hℓ hij hC hΘm hΘb x]
  rw [hs1, hs2, hcomm]

/-! ## §5  `ℂ`-valued assembly helpers for the word split -/

/-- **An integral vanishing outside the centred cube is bounded by a constant times the cube
volume.** -/
lemma norm_integral_le_const_of_support_acube {ℓ C : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hb : ∀ z, ‖f z‖ ≤ C) (hs : ∀ z, z ∉ Submission.BoseGases.acube ℓ → f z = 0) :
    ‖∫ z : E3, f z‖ ≤ C * (volume : Measure E3).real (Submission.BoseGases.acube ℓ) := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  exact MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae
    (Submission.BoseGases.acube_lt_top ℓ hℓ.le) (Filter.Eventually.of_forall hb)

/-- **`χ_Λ` times two bounded a.e.-strongly-measurable factors is integrable, with an explicit
bound on its integral.** -/
lemma chiLam_mul_bdd_integrable_and_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : E3 → ℂ} {A B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hfb : ∀ z, ‖f z‖ ≤ A)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ z, ‖g z‖ ≤ B) :
    Integrable (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * f z * g z) volume
      ∧ ‖∫ z : E3, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * f z * g z‖
          ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * A * B
              * (volume : Measure E3).real (Submission.BoseGases.acube ℓ) := by
  have hχ0 : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by positivity
  have hpt : ∀ z : E3, ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * f z * g z‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * A * B := by
    intro z
    have hnorm : ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
        = |Work.BoseK15.corpusBox.chiLam ℓ z| := RCLike.norm_ofReal _
    rw [norm_mul, norm_mul, hnorm]
    have hA : (0 : ℝ) ≤ A := le_trans (norm_nonneg _) (hfb z)
    have hχA : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * A := mul_nonneg hχ0 hA
    exact mul_le_mul (mul_le_mul (chiLam_abs_le ℓ z) (hfb z) (norm_nonneg _) hχ0) (hgb z)
      (norm_nonneg _) hχA
  have hsupp : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * f z * g z = 0 := by
    intro z hz
    have h0 : Work.BoseK15.corpusBox.chiLam ℓ z = 0 := by
      by_contra hne
      exact hz (chiLam_supp_acube hℓ (Function.mem_support.mpr hne))
    simp only [h0, Complex.ofReal_zero, zero_mul]
  refine ⟨?_, norm_integral_le_const_of_support_acube hℓ hpt hsupp⟩
  refine integrable_of_support_acube (ℓ := ℓ)
    (C := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * A * B) hℓ ?_ hpt hsupp
  exact (((Complex.continuous_ofReal.comp (chiLam_continuous ℓ)).aestronglyMeasurable).mul
    hfm).mul hgm

/-- **A bounded measurable weight times a bounded a.e.-strongly-measurable complex function
supported in the box is integrable.** -/
lemma integrable_ofReal_mul_of_support_abox {n : ℕ} {ℓ Cθ CJ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ Cθ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    {J : Submission.BoseGases.X n → ℂ} (hJae : AEStronglyMeasurable J volume)
    (hJb : ∀ x, ‖J x‖ ≤ CJ) :
    Integrable (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ) * J x) volume := by
  have hCθ0 : (0 : ℝ) ≤ Cθ := le_trans (abs_nonneg _) (hΘb 0)
  refine integrable_of_support_abox (n := n) (ℓ := ℓ) (C := Cθ * CJ) hℓ ?_ ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hΘm.aestronglyMeasurable).mul hJae
  · intro x
    have hnorm : ‖((Θ x : ℝ) : ℂ)‖ = |Θ x| := RCLike.norm_ofReal _
    rw [norm_mul, hnorm]
    exact mul_le_mul (hΘb x) (hJb x) (norm_nonneg _) hCθ0
  · intro x hx
    have h0 : Θ x = 0 := by
      by_contra hne
      exact hx (hΘs (Function.mem_support.mpr hne))
    rw [h0, Complex.ofReal_zero, zero_mul]

/-- **The `ℂ`-flavoured `integral_ofReal`.**  Mathlib's `integral_ofReal` is stated with the
`RCLike` coercion `↑ : ℝ → K`, which does not match the `Complex.ofReal` coercion of the goal
syntactically; this restatement does. -/
lemma integral_ofReal_coe {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ} :
    (∫ x, ((f x : ℝ) : ℂ) ∂μ) = ((∫ x, f x ∂μ : ℝ) : ℂ) := integral_ofReal

/-- **Continuity of the `χ̂`-weighted `k`-frame** (a finite sum of plane waves). -/
lemma continuous_KχfrU_char {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Continuous (fun z : E3 => Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z) := by
  simp only [Work.BoseBoxFock.PCFU.KχfrU]
  fun_prop


theorem Dchan_dzero_word_split_v2 {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Submission.BoseGases.X n,
        ((Θ x : ℝ) : ℂ)
          * (∫ z : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                      (Function.update x j z) : ℝ) : ℂ)))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc (Work.BoseBoxFock.ellH v μ)
                      (Submission.BoseGases.g0 v h) 0 (x i) (x j) : ℝ) : ℂ)
                * ((Work.BoseBoxFix.lowSlot fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                        (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)) x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ z : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)
                      * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                          - (∫ y : EuclideanSpace ℝ (Fin 3),
                              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
                                * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)
                                    (y - z) : ℝ) : ℂ)))
                      * ((Work.BoseBoxFix.lowSlot fc
                            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                            (Work.BoseBoxFock.ellH v μ) j
                            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                            (Function.update x j z) : ℝ) : ℂ))) := by
  obtain ⟨Cθ, hCθb⟩ := hΘb
  have hCθ0 : (0 : ℝ) ≤ Cθ := le_trans (abs_nonneg _) (hCθb 0)
  set ℓ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  set Γ : Submission.BoseGases.X n → ℝ := fun y => Work.BoseBoxFix.lowSlot fc κ ℓ j
    (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) y with hΓdef
  set B : Submission.BoseGases.X n → ℝ := fun y =>
    Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (y i) (y j) * Γ y with hBdef
  set Ĉ : E3 → ℝ := fun z => ∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y)
    * (Work.BoseFixR.W1fun v h ℓ (y - z)) with hCdef
  set χc : E3 → ℂ := fun z => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) with hχcdef
  set Kc : E3 → ℂ := fun z => Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z with hKcdef
  set Ĉc : E3 → ℂ := fun z => ((Ĉ z : ℝ) : ℂ) with hĈcdef
  set Γc : Submission.BoseGases.X n → ℂ := fun y => ((Γ y : ℝ) : ℂ) with hΓcdef
  set Krem : E3 → ℂ := fun z => Kc z - (∫ y : E3,
    ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
      * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)) with hKremdef
  change (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, χc z * Kc z * Γc (Function.update x j z)))
      = ((ℓ : ℂ)) ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
              * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
                  : ℝ) : ℂ)
              * ((Γ x : ℝ) : ℂ))
        + (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
            * (∫ z : E3, χc z * Krem z * Γc (Function.update x j z)))
  have hκ' : 0 < κ := hκ
  obtain ⟨hΓm, D, hD0, hΓb⟩ :=
    lowSlot_aQ_aP_measurable_bounded (μ := μ) (ℓ := ℓ) (κ := κ) (fc := fc) (i := i) (j := j)
      hℓ hκ' hCθ0 hΘm hCθb
  have hΓi : ∀ x y, Γ (Function.update x i y) = Γ x := by
    intro x y
    have h := lowSlot_update_eq_of_free (ℓ := ℓ) (κ := κ) (i := i) (j := j) hij fc
      (ψ := Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
      (aQ_aP_free (Θ := Θ) (ℓ := ℓ) (i := i) (j := j) hij) x y
    simpa only [hΓdef] using h
  have hBint : IntegrableOn B (Submission.BoseGases.abox n ℓ) volume := by
    have h := integrableOn_pairKernel_lowSlot (n := n) (i := i) (j := j) hij (v := v) (h := h)
      (ψ := Γ) hR hv_supp hℓ hRℓ hΓm hD0 hΓb
    simpa only [hℓdef, hBdef] using h
  have hreal : (∫ x : Submission.BoseGases.X n, Θ x * (∫ z : E3,
        (Work.BoseK15.corpusBox.chiLam ℓ z) * Ĉ z * Γ (Function.update x j z)))
      = ℓ ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x * B x) := by
    have h := real_core (i := i) (j := j) hij (v := v) (h := h) (R := R) (ℓ := ℓ)
      hR hℓ hv_supp hRℓ (Γ := Γ) (K := D) hD0 hΓm hΓb hΓi (Θ := Θ) (C := Cθ)
      hΘm hCθ0 hCθb hΘs (by simpa only [hBdef] using hBint)
    simpa only [hCdef, hBdef] using h
  have hCH : ∀ z : E3, (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)) = ((Ĉ z : ℝ) : ℂ) := by
    intro z
    have hdef : Ĉ z = ∫ y : E3, (Work.BoseK15.corpusBox.chiLam ℓ y)
        * (Work.BoseFixR.W1fun v h ℓ (y - z)) := by simp only [hCdef]
    rw [hdef, ← integral_ofReal_coe]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    push_cast
    ring
  obtain ⟨CK, hCK0, hCKb⟩ := KχfrU_norm_le (v := v) h μ fu N
  obtain ⟨CC, hCC0, hCCb⟩ := chiHat_abs_le (v := v) (h := h) (R := R) (ℓ := ℓ)
    hR hℓ hv_supp hRℓ
  have hĈae : AEMeasurable Ĉ volume := by
    have h := aemeasurable_chiHat (v := v) (h := h) (R := R) (ℓ := ℓ) hR hℓ hv_supp hRℓ
    simpa only [hCdef] using h
  have hKmeas : Measurable Kc := by
    have h := continuous_KχfrU_char (v := v) h μ fu N
    simpa only [hKcdef] using h.measurable
  have hz1 : ∀ x : Submission.BoseGases.X n,
      Integrable (fun z : E3 => χc z * Ĉc z * Γc (Function.update x j z)) volume
        ∧ ‖∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z)‖
            ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * CC * D
                * (volume : Measure E3).real (Submission.BoseGases.acube ℓ) := by
    intro x
    have hfram : Measurable (fun z : E3 => Γ (Function.update x j z)) :=
      hΓm.comp (by fun_prop : Measurable fun z : E3 => Function.update x j z)
    have hfac : AEStronglyMeasurable (fun z : E3 => Γc (Function.update x j z)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hfram.aestronglyMeasurable
    have hfacb : ∀ z : E3, ‖Γc (Function.update x j z)‖ ≤ D := by
      intro z
      have hnorm : ‖((Γ (Function.update x j z) : ℝ) : ℂ)‖ = |Γ (Function.update x j z)| :=
        RCLike.norm_ofReal _
      simpa only [hΓcdef, hnorm] using hΓb (Function.update x j z)
    have hĈcae : AEStronglyMeasurable Ĉc volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hĈae.aestronglyMeasurable
    have hĈcb : ∀ z : E3, ‖Ĉc z‖ ≤ CC := by
      intro z
      have hsub : Ĉc z = ((Ĉ z : ℝ) : ℂ) := by simp only [hĈcdef]
      have hnorm : ‖((Ĉ z : ℝ) : ℂ)‖ = |Ĉ z| := RCLike.norm_ofReal _
      rw [hsub, hnorm]
      simpa only [hCdef] using hCCb z
    have h := chiLam_mul_bdd_integrable_and_norm_le (ℓ := ℓ) hℓ (f := Ĉc)
      (g := fun z : E3 => Γc (Function.update x j z)) (A := CC) (B := D)
      hĈcae hĈcb hfac hfacb
    simpa only [hχcdef] using h
  have hz2 : ∀ x : Submission.BoseGases.X n,
      Integrable (fun z : E3 => χc z * (Kc z - Ĉc z) * Γc (Function.update x j z)) volume
        ∧ ‖∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z)‖
            ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * (CK + CC) * D
                * (volume : Measure E3).real (Submission.BoseGases.acube ℓ) := by
    intro x
    have hfram : Measurable (fun z : E3 => Γ (Function.update x j z)) :=
      hΓm.comp (by fun_prop : Measurable fun z : E3 => Function.update x j z)
    have hfac : AEStronglyMeasurable (fun z : E3 => Γc (Function.update x j z)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hfram.aestronglyMeasurable
    have hfacb : ∀ z : E3, ‖Γc (Function.update x j z)‖ ≤ D := by
      intro z
      have hnorm : ‖((Γ (Function.update x j z) : ℝ) : ℂ)‖ = |Γ (Function.update x j z)| :=
        RCLike.norm_ofReal _
      simpa only [hΓcdef, hnorm] using hΓb (Function.update x j z)
    have hKcb : ∀ z : E3, ‖Kc z - Ĉc z‖ ≤ CK + CC := by
      intro z
      have h1 : ‖Kc z‖ ≤ CK := by
        simpa only [hKcdef] using hCKb z
      have h2 : ‖Ĉc z‖ ≤ CC := by
        have hsub : Ĉc z = ((Ĉ z : ℝ) : ℂ) := by simp only [hĈcdef]
        have hnorm : ‖((Ĉ z : ℝ) : ℂ)‖ = |Ĉ z| := RCLike.norm_ofReal _
        rw [hsub, hnorm]
        simpa only [hCdef] using hCCb z
      exact (norm_sub_le _ _).trans (by linarith)
    have hKcae : AEStronglyMeasurable (fun z : E3 => Kc z - Ĉc z) volume :=
      hKmeas.aestronglyMeasurable.sub
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hĈae.aestronglyMeasurable)
    have h := chiLam_mul_bdd_integrable_and_norm_le (ℓ := ℓ) hℓ
      (f := fun z : E3 => Kc z - Ĉc z) (g := fun z : E3 => Γc (Function.update x j z))
      (A := CK + CC) (B := D) hKcae hKcb hfac hfacb
    simpa only [hχcdef] using h
  have hJ1ae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z)) volume := by
    have hjoint : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 =>
        χc p.2 * Ĉc p.2 * Γc (Function.update p.1 j p.2)) (volume.prod volume) := by
      have hχ : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 => χc p.2)
          (volume.prod volume) :=
        ((Complex.continuous_ofReal.comp (chiLam_continuous ℓ)).measurable.comp
          measurable_snd).aestronglyMeasurable
      have hĈ : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 => Ĉc p.2)
          (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          (hĈae.comp_snd).aestronglyMeasurable
      have hΓ : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 =>
          Γc (Function.update p.1 j p.2)) (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          ((hΓm.comp (by fun_prop : Measurable fun p : Submission.BoseGases.X n × E3 =>
            Function.update p.1 j p.2)).aestronglyMeasurable)
      exact (hχ.mul hĈ).mul hΓ
    simpa using hjoint.integral_prod_right'
  have hJ2ae : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z)) volume := by
    have hjoint : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 =>
        χc p.2 * (Kc p.2 - Ĉc p.2) * Γc (Function.update p.1 j p.2)) (volume.prod volume) := by
      have hχ : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 => χc p.2)
          (volume.prod volume) :=
        ((Complex.continuous_ofReal.comp (chiLam_continuous ℓ)).measurable.comp
          measurable_snd).aestronglyMeasurable
      have hK : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 => Kc p.2)
          (volume.prod volume) :=
        (hKmeas.comp measurable_snd).aestronglyMeasurable
      have hĈ : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 => Ĉc p.2)
          (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          (hĈae.comp_snd).aestronglyMeasurable
      have hΓ : AEStronglyMeasurable (fun p : Submission.BoseGases.X n × E3 =>
          Γc (Function.update p.1 j p.2)) (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          ((hΓm.comp (by fun_prop : Measurable fun p : Submission.BoseGases.X n × E3 =>
            Function.update p.1 j p.2)).aestronglyMeasurable)
      exact (hχ.mul (hK.sub hĈ)).mul hΓ
    simpa using hjoint.integral_prod_right'
  have hI1 : Integrable (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)
      * (∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z))) volume :=
    integrable_ofReal_mul_of_support_abox (n := n) (ℓ := ℓ) hℓ hΘm hCθb hΘs hJ1ae
      (fun x => (hz1 x).2)
  have hI2 : Integrable (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)
      * (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z))) volume :=
    integrable_ofReal_mul_of_support_abox (n := n) (ℓ := ℓ) hℓ hΘm hCθb hΘs hJ2ae
      (fun x => (hz2 x).2)
  have hsplit : ∀ x : Submission.BoseGases.X n,
      (∫ z : E3, χc z * Kc z * Γc (Function.update x j z))
        = (∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z))
          + (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z)) := by
    intro x
    rw [← MeasureTheory.integral_add (hz1 x).1 (hz2 x).1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    ring
  have hx1 : (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, χc z * Kc z * Γc (Function.update x j z)))
      = ∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * ((∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z))
            + (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z))) :=
    (by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [hsplit x])
  have hx2 : (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * ((∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z))
            + (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z))))
      = (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
            * (∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z)))
        + (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
            * (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z))) := by
    rw [← MeasureTheory.integral_add hI1 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  have hLC : (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z)))
      = ((ℓ : ℂ)) ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
              * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
                  : ℝ) : ℂ)
              * ((Γ x : ℝ) : ℂ)) := by
    have hinner : ∀ x : Submission.BoseGases.X n,
        (∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z))
          = ((∫ z : E3, (Work.BoseK15.corpusBox.chiLam ℓ z) * Ĉ z
              * Γ (Function.update x j z) : ℝ) : ℂ) := by
      intro x
      rw [← integral_ofReal_coe]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hχcdef, hĈcdef, hΓcdef]
      push_cast
      ring
    have h1 : (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
          * (∫ z : E3, χc z * Ĉc z * Γc (Function.update x j z)))
        = (((∫ x : Submission.BoseGases.X n, Θ x * (∫ z : E3,
            (Work.BoseK15.corpusBox.chiLam ℓ z) * Ĉ z * Γ (Function.update x j z))
            : ℝ) : ℂ)) := by
      rw [← integral_ofReal_coe]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [hinner x]
      push_cast
      ring
    have h2 : (((∫ x : Submission.BoseGases.X n, Θ x * (∫ z : E3,
            (Work.BoseK15.corpusBox.chiLam ℓ z) * Ĉ z * Γ (Function.update x j z))
            : ℝ) : ℂ))
        = ((ℓ ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x * B x)
            : ℝ) : ℂ) := by
      rw [hreal]
    have h3 : ((ℓ ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x * B x)
            : ℝ) : ℂ)
        = ((ℓ : ℂ)) ^ 6 * (∫ x in Submission.BoseGases.abox n ℓ,
            ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
              * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
                  : ℝ) : ℂ)
              * ((Γ x : ℝ) : ℂ)) := by
      have h3a : ((∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x * B x
            : ℝ) : ℂ)
          = (∫ x in Submission.BoseGases.abox n ℓ,
              ((Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Θ) x : ℝ) : ℂ)
                * ((Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)
                    : ℝ) : ℂ)
                * ((Γ x : ℝ) : ℂ)) := by
        rw [← integral_ofReal_coe]
        refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
          (fun x _ => ?_)
        simp only [hBdef]
        push_cast
        ring
      rw [← h3a, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [h1, h2, h3]
  have hRC : (∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z)))
      = ∫ x : Submission.BoseGases.X n, ((Θ x : ℝ) : ℂ)
        * (∫ z : E3, χc z * Krem z * Γc (Function.update x j z)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    have hγ : (∫ z : E3, χc z * (Kc z - Ĉc z) * Γc (Function.update x j z))
        = (∫ z : E3, χc z * Krem z * Γc (Function.update x j z)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hĈcdef, hKremdef]
      rw [← hCH z]
    rw [hγ]
  rw [hx1, hx2, hLC, hRC]

end Work.BoseBoxFock.PCFU
