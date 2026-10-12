import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.chAimg_arith6
import Submission.Work.BoseBoxFock.PCFU.chAimg_dirBounded
import Submission.Work.BoseBoxFock.PCFU.chAimg_dirichletLe
import Submission.Work.BoseBoxFock.PCFU.chAimg_psL2
import Submission.Work.BoseBoxFock.PCFU.chAimg_sliceLe
import Submission.Work.BoseBoxFock.PCFU.chBimg_arith_aux
import Submission.Work.BoseBoxFock.PCFU.chBimg_state_le
import Submission.Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le
import Submission.Work.BoseBoxFock.PCFU.kinetic_le_of_isLowB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 4000000

set_option maxRecDepth 4000

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.chAimg_bound`

The `(A)`-channel lattice-image slot `chAimg` obeys the per-slot bound of `SlotPiece`
(budget `K0·μ·(a v)`, i.e. `A μ = K0·(a v)/(8μ(ℓ³+1))`, `ℓ = ellH v μ`).

Two inputs (see `PCFU/FINDING_chAimg_bound_session2.md`):

* the `χ_ℓ(x_j)`-weighted lattice-image factor of the low cut-off kernel is *pointwise* small
  (`chiScale_lowKer_image_le`, the rescaled `M`-th order flatness bound
  `‖χ_ℓ(b)·Σ'_{e≠0}Κ_κ(u−b+ℓe)‖ ≤ C·d^{2M}/ℓ³`, `κ = (d²ℓ)⁻¹`, `M = 96`), giving
  `Cimg = C₀·d^{192}/ℓ³`;
* the local `L²` mass of the `KfrU`-frame over a box (`chAimg_KfrU_localL2`,
  `∫_{acube ℓ}‖KfrU(q−z)‖² ≤ C_A·ℓ⁶`), which turns the weighted state pairing into a plain
  fibre-Cauchy–Schwarz estimate (`chAimg_stateWeightedL2`, `≤ C_B·ℓ³·√K·normB`).

The arithmetic `Cimg·C_B·ℓ³·√(C_A ℓ⁶) = C₀C_B√C_A·d^{192}ℓ³` against the budget
`A μ = K0(av)/(8μ(1+ℓ³))` is the identity `d^{192}ℓ³ = a³t^{663/323}` plus
`t^{166/323} ≤ 1/(μ(1+ℓ³))` (`t = μa³`), i.e. `chAimg_arith2`.
-/

open MeasureTheory

/-- **The exact scaling of the low-momentum kernel**: `Κ_κ(z) = κ³·Κ₁(κz)`
(the symbol `f(‖p‖/κ)` is the `κ`-dilate of `f(‖p‖)`). -/
private lemma lowKer_smul_scale (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (z : E3) :
    lowKer fc κ z = κ ^ 3 * lowKer fc 1 (κ • z) := by
  have hG : ∀ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z)
      = fc.f (‖q‖ / 1) * Real.cos (inner ℝ q (κ • z)) := by
    intro q
    have h1 : ‖κ • q‖ / κ = ‖q‖ / 1 := by
      rw [norm_smul, Real.norm_of_nonneg hκ.le, div_one]
      field_simp
    have h2 : inner ℝ (κ • q) z = inner ℝ q (κ • z) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [h1, h2]
  have hsub := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure E3))
    (f := fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) κ (hR := hκ.le)
  have hfin : Module.finrank ℝ E3 = 3 := by simp [EuclideanSpace]
  rw [hfin] at hsub
  rw [lowKer_apply, lowKer_apply]
  have hkey : (∫ p : E3, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z))
      = κ ^ 3 * ∫ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z) := by
    rw [hsub, smul_eq_mul]
    have hne : κ ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
    field_simp
  rw [hkey, integral_congr_ae (Filter.Eventually.of_forall hG)]
  ring

/-- `Κ` does not see the cutoff trivialities: the `corpusBox` bump is the corpus bump. -/
private lemma chiLam_eq_chiScale (ℓ : ℝ) :
    Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl

/-- The `κ`-dilate of a centered cube is the centered cube of the rescaled side. -/
private lemma mem_acube_smul {κ ℓ : ℝ} (hκ : 0 < κ) {u : E3}
    (hu : u ∈ Submission.BoseGases.acube ℓ) : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := by
  rw [Submission.BoseGases.mem_acube_iff] at hu ⊢
  intro m
  have hm := hu m
  have hcomp : (κ • u).ofLp m = κ * u.ofLp m := by
    rw [WithLp.ofLp_smul]
    rfl
  rw [hcomp]
  constructor
  · nlinarith [hm.1, hκ]
  · nlinarith [hm.2, hκ]

/-- The `χ`-weighted lattice-image bound of the low-momentum kernel, with the smallness in the
box ratio `d`: at the tied cutoff `κ = 1/(d²ℓ)` the kernel's rescaled width is frozen and the
proved `chiScale_imageSum_lowKer_le` at `κ = 1` gives `d^{2M}/ℓ³`. -/
private lemma chiScale_lowKer_image_le (fc : Work.BoseBoxFix.LowCut) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ d ℓ : ℝ}, 0 < d → 0 < ℓ → κ = 1 / (d ^ 2 * ℓ) →
      ∀ (b u : E3), u ∈ Submission.BoseGases.acube ℓ →
        ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
          * (∑' e : Fin 3 → ℤ, if e = 0 then 0
              else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
          ≤ C * d ^ (2 * M) / ℓ ^ 3 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le fc (κ := 1) one_pos M
  refine ⟨C₁, hC₁0, ?_⟩
  intro κ d ℓ hd hℓ hκeq b u hu
  have hκpos : 0 < κ := by rw [hκeq]; positivity
  have hκℓpos : 0 < κ * ℓ := mul_pos hκpos hℓ
  -- the `χ`-identity `χ_{κℓ}(κb) = χ_ℓ(b)`
  have hchi : Submission.BoseGases.chiScale (κ * ℓ) (κ • b)
      = Submission.BoseGases.chiScale ℓ b := by
    rw [Submission.BoseGases.chiScale, Submission.BoseGases.chiScale, smul_smul]
    congr 1
    field_simp
  -- the rescaled argument identity
  have harg : ∀ e : Fin 3 → ℤ,
      κ • (u - b + ℓ • Work.BoseBoxFock.latVec e)
        = κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e := by
    intro e
    rw [smul_add, smul_sub, smul_smul]
  -- the termwise scaling identity (complex-valued)
  have hterm : ∀ e : Fin 3 → ℤ,
      ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)
        = ((κ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseBoxFock.PCFU.lowKer fc 1
              (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) := by
    intro e
    have h := lowKer_smul_scale fc hκpos (u - b + ℓ • Work.BoseBoxFock.latVec e)
    rw [h, harg e]
    push_cast
    ring
  -- the two sums
  set S₁ : ℂ := ∑' e : Fin 3 → ℤ, if e = 0 then 0
      else ((Work.BoseBoxFock.PCFU.lowKer fc 1
        (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) with hS₁
  have hS : (∑' e : Fin 3 → ℤ, if e = 0 then 0
        else ((Work.BoseBoxFock.PCFU.lowKer fc κ
          (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)) = ((κ ^ 3 : ℝ) : ℂ) * S₁ := by
    have h1 : (∑' e : Fin 3 → ℤ, if e = 0 then 0
          else ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
        = ∑' e : Fin 3 → ℤ, ((κ ^ 3 : ℝ) : ℂ) * (if e = 0 then 0
            else ((Work.BoseBoxFock.PCFU.lowKer fc 1
              (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)) := by
      refine tsum_congr (fun e => ?_)
      by_cases he : e = 0
      · subst he; simp
      · rw [if_neg he, if_neg he]
        exact hterm e
    rw [h1, tsum_mul_left, hS₁]
  -- the `κ = 1` lemma at `ℓ̃ = κℓ`, `b̃ = κb`, `ũ = κu`
  have hac : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := mem_acube_smul hκpos hu
  have hb := hC₁ hκℓpos (κ • b) (κ • u) hac
  -- extract `‖χ_{κℓ}(κb)·S₁‖` from the lemma's norm
  have hb' : ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖
      ≤ C₁ / (κ * ℓ) ^ (M + 3) := by
    rw [← hS₁] at hb
    have hnorm : ‖((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ)
          * (((κ * ℓ) ^ 3 : ℝ) : ℂ) * S₁‖
        = (κ * ℓ) ^ 3 * ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖ := by
      rw [← hchi]
      rw [show ((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ)
            * (((κ * ℓ) ^ 3 : ℝ) : ℂ) * S₁
          = (((κ * ℓ) ^ 3 : ℝ) : ℂ)
            * (((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ) * S₁) from by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnorm] at hb
    have hsplit : C₁ / (κ * ℓ) ^ M = (κ * ℓ) ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3)) := by
      rw [pow_add]
      field_simp
    rw [hsplit] at hb
    exact le_of_mul_le_mul_left hb (by positivity)
  -- the arithmetic identity
  have hκℓ : κ * ℓ = (d ^ 2)⁻¹ := by
    rw [hκeq]; field_simp
  have harith : κ ^ 3 / (κ * ℓ) ^ (M + 3) = d ^ (2 * M) / ℓ ^ 3 := by
    rw [div_eq_div_iff (by positivity) (by positivity), ← mul_pow]
    rw [pow_add, pow_mul, ← mul_assoc, ← mul_pow]
    have hd2κℓ : d ^ 2 * (κ * ℓ) = 1 := by
      rw [hκℓ]; field_simp
    rw [hd2κℓ]
    simp
  -- assembly
  calc ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ
              (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
      = ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((κ ^ 3 : ℝ) : ℂ) * S₁)‖ := by
        rw [hS]
      _ = κ ^ 3 * ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖ := by
        rw [show ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((κ ^ 3 : ℝ) : ℂ) * S₁)
            = (((κ ^ 3 : ℝ) : ℂ)) * (((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁) from by
              ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ κ ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3)) := by
        refine mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = C₁ * d ^ (2 * M) / ℓ ^ 3 := by
        rw [show κ ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3))
              = C₁ * (κ ^ 3 / (κ * ℓ) ^ (M + 3)) from by ring, harith]
        ring
/-- The `j`-slot fibre `L¹` of the state deviation `Q_jP_iΘ`, as a function of the configuration. -/
private noncomputable def slotFibre {n : ℕ} (ℓ : ℝ) (i j : Fin n)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℝ :=
  ∫ u in Submission.BoseGases.acube ℓ,
    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|

/-- The slot mean of a bounded configuration function is bounded by the same constant. -/
private lemma aP_abs_le_of_bounded {n : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘb : ∀ x, |Θ x| ≤ B) (i : Fin n)
    (x : Submission.BoseGases.X n) :
    |Submission.BoseGases.aP ℓ i Θ x| ≤ B := by
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (Submission.BoseGases.acube_isBounded ℓ hℓ.le)
  have hmeas : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  rw [Submission.BoseGases.aP, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ℓ ^ 3)]
  have h1 : |∫ y in Submission.BoseGases.acube ℓ, Θ (Function.update x i y)|
      ≤ ∫ y in Submission.BoseGases.acube ℓ, |Θ (Function.update x i y)| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun y : E3 => Θ (Function.update x i y)))
  have h2 : ∫ y in Submission.BoseGases.acube ℓ, |Θ (Function.update x i y)|
      ≤ ∫ y in Submission.BoseGases.acube ℓ, B := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      ?_ (Filter.Eventually.of_forall (fun y => hΘb _))
    refine IntegrableOn.of_bound hvol aestronglyMeasurable_const B
      (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg hB]
  have h4 : (volume : Measure E3).real (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def]
    have h := Submission.BoseGases.real_volume_acube ℓ hℓ.le
    rw [Measure.real_def, Measure.restrict_apply_univ] at h
    exact h
  have h3 : ∫ y in Submission.BoseGases.acube ℓ, B = B * ℓ ^ 3 := by
    rw [setIntegral_const, smul_eq_mul, h4, mul_comm]
  calc (1 / ℓ ^ 3) * |∫ y in Submission.BoseGases.acube ℓ, Θ (Function.update x i y)|
      ≤ (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, |Θ (Function.update x i y)| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (1 / ℓ ^ 3) * (B * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left (le_trans h2 h3.le) (by positivity)
    _ = B := by field_simp

/-- The state deviation of a bounded configuration function is bounded by twice the bound. -/
private lemma aQ_aP_abs_le {n : ℕ} {ℓ B : ℝ} (hℓ : 0 < ℓ) (hB : 0 ≤ B)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘb : ∀ x, |Θ x| ≤ B) (i j : Fin n)
    (x : Submission.BoseGases.X n) :
    |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ 2 * B := by
  have h1 : ∀ y, |Submission.BoseGases.aP ℓ i Θ y| ≤ B :=
    fun y => aP_abs_le_of_bounded hℓ hB hΘb i y
  have h2 : |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ B :=
    aP_abs_le_of_bounded hℓ hB h1 j x
  rw [Submission.BoseGases.aQ]
  calc |Submission.BoseGases.aP ℓ i Θ x
        - Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x|
      = |Submission.BoseGases.aP ℓ i Θ x
          + -(Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x)| := by ring_nf
    _ ≤ |Submission.BoseGases.aP ℓ i Θ x|
          + |-(Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x)| := abs_add_le _ _
    _ = |Submission.BoseGases.aP ℓ i Θ x|
          + |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x| := by rw [abs_neg]
    _ ≤ B + B := add_le_add (h1 x) h2
    _ = 2 * B := by ring

/-- **The inner slot-integral bound**: the `χ`-weighted lattice-image factor paired with the
state deviation is bounded by `Cimg` times the fibre `L¹` of the deviation. -/
private lemma chBimg_inner_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B) {fc : Work.BoseBoxFix.LowCut} {κ Cimg : ℝ}
    (himg : ∀ (b u : E3), u ∈ Submission.BoseGases.acube ℓ →
      ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖ ≤ Cimg)
    (x : Submission.BoseGases.X n) :
    |Work.BoseK15.corpusBox.chiLam ℓ (x j)|
      * ‖∫ u in Submission.BoseGases.acube ℓ,
          (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
          * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u) : ℝ) : ℂ)‖
      ≤ Cimg * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|) := by
  have hvol : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (Submission.BoseGases.acube_isBounded ℓ hℓ.le)
  set c : ℂ := ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) with hc
  set Sf : E3 → ℂ := fun u => ∑' e : Fin 3 → ℤ, if e = 0 then 0
      else ((lowKer fc κ (u - x j + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) with hSf
  set Ψf : E3 → ℂ := fun u => ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
      (Function.update x j u) : ℝ) : ℂ) with hΨf
  set ψf : E3 → ℝ := fun u => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
      (Function.update x j u) with hψf
  have hψm : Measurable ψf := by
    have hupd : Measurable (Function.update x j : E3 → Submission.BoseGases.X n) := by
      refine measurable_pi_iff.mpr (fun k => ?_)
      have hfun : (fun u : E3 => Function.update x j u k)
          = (if k = j then (fun u : E3 => u) else (fun _ => x k)) := by
        funext u
        by_cases hk : k = j
        · rw [hk, if_pos rfl]
          exact Function.update_self j u x
        · rw [if_neg hk]
          exact Function.update_of_ne hk u x
      rw [hfun]
      by_cases hk : k = j
      · rw [if_pos hk]; exact measurable_id
      · rw [if_neg hk]; exact measurable_const
    exact (Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)).comp
      hupd
  have hΨm : Measurable Ψf := Complex.measurable_ofReal.comp hψm
  have hψb : ∀ u : E3, ‖ψf u‖ ≤ 2 * B := fun u => by
    rw [hψf, Real.norm_eq_abs]
    exact aQ_aP_abs_le hℓ hB hΘb i j (Function.update x j u)
  have hΨb : ∀ u : E3, ‖Ψf u‖ ≤ 2 * B := fun u => by
    simp only [hΨf, Complex.norm_real, Real.norm_eq_abs]
    exact hψb u
  have hInt : Integrable Ψf ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    IntegrableOn.of_bound hvol hΨm.aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall hΨb)
  have hcn : ‖c‖ = |Work.BoseK15.corpusBox.chiLam ℓ (x j)| := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
  have hpull : (∫ u in Submission.BoseGases.acube ℓ, c * Sf u * Ψf u)
      = c * ∫ u in Submission.BoseGases.acube ℓ, Sf u * Ψf u := by
    rw [show (fun u : E3 => c * Sf u * Ψf u) = (fun u : E3 => c * (Sf u * Ψf u)) from
      funext (fun u => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hmain : ‖∫ u in Submission.BoseGases.acube ℓ, c * Sf u * Ψf u‖
      ≤ ∫ u in Submission.BoseGases.acube ℓ, Cimg * |ψf u| := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg _)) ?_ ?_
    · refine (hInt.norm.const_mul Cimg).congr ?_
      filter_upwards with u
      simp only [hΨf, hψf, Complex.norm_real, Real.norm_eq_abs]
    · filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)]
        with u hu
      rw [norm_mul]
      have hcS : ‖c * Sf u‖ ≤ Cimg := by
        have h := himg (x j) u hu
        rw [← chiLam_eq_chiScale] at h
        simpa only [hc, hSf] using h
      have hΨu : ‖Ψf u‖ = |ψf u| := by
        simp only [hΨf, hψf, Complex.norm_real, Real.norm_eq_abs]
      rw [hΨu]
      exact mul_le_mul_of_nonneg_right hcS (abs_nonneg _)
  have hlast : (∫ u in Submission.BoseGases.acube ℓ, Cimg * |ψf u|)
      = Cimg * ∫ u in Submission.BoseGases.acube ℓ, |ψf u| :=
    MeasureTheory.integral_const_mul _ _
  calc |Work.BoseK15.corpusBox.chiLam ℓ (x j)|
        * ‖∫ u in Submission.BoseGases.acube ℓ, Sf u * Ψf u‖
      = ‖c * (∫ u in Submission.BoseGases.acube ℓ, Sf u * Ψf u)‖ := by rw [← hcn, norm_mul]
    _ = ‖∫ u in Submission.BoseGases.acube ℓ, c * Sf u * Ψf u‖ := by rw [hpull]
    _ ≤ ∫ u in Submission.BoseGases.acube ℓ, Cimg * |ψf u| := hmain
    _ = Cimg * ∫ u in Submission.BoseGases.acube ℓ, |ψf u| := hlast
    _ = Cimg * (∫ u in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x j u)|) := by
        rw [hψf]

/-- **The measure-theoretic reduction of the `chAimg` slot**: given the pointwise smallness of the
`χ_ℓ`-weighted lattice-image factor and the integrability of the resulting majorant, the slot is
bounded by `Cimg` times the weighted state integral controlled by `chAimg_stateWeighted`. -/
private theorem chAimg_chain {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    {B : ℝ} (hB0 : 0 ≤ B) (hΘb : ∀ x, |Θ x| ≤ B)
    {Cimg : ℝ} (hCimg0 : 0 ≤ Cimg)
    (himg : ∀ (b u : E3), u ∈ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ) →
      ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
              (u - b + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
        ≤ Cimg)
    (hmajInt : Integrable (fun x : Submission.BoseGases.X n =>
        Cimg *
          (|Θ x|
            * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)‖
            * ‖KfrU v h μ fu N (x j - x i)‖
            * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                |Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                  (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u)|)))) :
    ‖chAimg v h fc fu μ N i j Θ‖ ≤ Cimg *
      (∫ x : Submission.BoseGases.X n,
        |Θ x|
          * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)‖
          * ‖KfrU v h μ fu N (x j - x i)‖
          * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
              |Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                (Function.update x j u)|)) := by
  set Ps : Submission.BoseGases.X n → ℝ := fun x =>
      ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        |Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
          (Function.update x j u)| with hPs
  set Im : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
            (u - x j + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
            (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
            (Function.update x j u) : ℝ) : ℂ) with hIm
  set χi : Submission.BoseGases.X n → ℂ := fun x =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ) with hχi
  set χj : Submission.BoseGases.X n → ℂ := fun x =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ) with hχj
  set Kf : Submission.BoseGases.X n → ℂ := fun x => KfrU v h μ fu N (x j - x i) with hKf
  have hinner : ∀ x : Submission.BoseGases.X n, ‖χj x‖ * ‖Im x‖ ≤ Cimg * Ps x := by
    intro x
    have h := chBimg_inner_le (ℓ := Work.BoseBoxFock.ellH v μ) (i := i) (j := j)
      (Work.BoseBoxFock.ellH_pos v μ) hΘm hB0 hΘb
      (Cimg := Cimg) (κ := Work.BoseBoxFock.PCFU.chKappa v μ) himg x
    simpa only [hPs, hIm, hχj, Complex.norm_real, Real.norm_eq_abs] using h
  have hpt : ∀ x : Submission.BoseGases.X n,
      ‖(Θ x : ℂ) * χi x * χj x * Kf x * Im x‖
        ≤ Cimg * (|Θ x| * ‖χi x‖ * ‖Kf x‖ * Ps x) := by
    intro x
    have hin := hinner x
    calc ‖(Θ x : ℂ) * χi x * χj x * Kf x * Im x‖
        = (|Θ x| * ‖χi x‖ * ‖Kf x‖) * (‖χj x‖ * ‖Im x‖) := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          ring
      _ ≤ (|Θ x| * ‖χi x‖ * ‖Kf x‖) * (Cimg * Ps x) :=
          mul_le_mul_of_nonneg_left hin
            (mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      _ = Cimg * (|Θ x| * ‖χi x‖ * ‖Kf x‖ * Ps x) := by ring
  have hmajInt' : Integrable (fun x : Submission.BoseGases.X n =>
      Cimg * (|Θ x| * ‖χi x‖ * ‖Kf x‖ * Ps x)) := by
    simpa only [hχi, hKf, hPs] using hmajInt
  have hstep : ‖∫ x : Submission.BoseGases.X n, (Θ x : ℂ) * χi x * χj x * Kf x * Im x‖
      ≤ ∫ x : Submission.BoseGases.X n,
          Cimg * (|Θ x| * ‖χi x‖ * ‖Kf x‖ * Ps x) := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => norm_nonneg _)) hmajInt'
      (Filter.Eventually.of_forall hpt)
  have hfinal : (∫ x : Submission.BoseGases.X n,
        Cimg * (|Θ x| * ‖χi x‖ * ‖Kf x‖ * Ps x))
      = Cimg * (∫ x : Submission.BoseGases.X n,
          |Θ x| * ‖χi x‖ * ‖Kf x‖ * Ps x) :=
    MeasureTheory.integral_const_mul Cimg _
  have hLHS : chAimg v h fc fu μ N i j Θ
      = ∫ x : Submission.BoseGases.X n, (Θ x : ℂ) * χi x * χj x * Kf x * Im x := by
    rw [chAimg]
  rw [hLHS]
  exact hstep.trans (le_of_eq hfinal)

/-- **The per-slot bound for `chAimg`.** -/
theorem chAimg_bound (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chAimg v h fc fu μ N i j Θ) := by
  classical
  obtain ⟨C₀, hC₀0, himgB⟩ := chiScale_lowKer_image_le fc 96
  obtain ⟨Cs, hCs0, hsliceB⟩ := chAimg_sliceLe v h hv hv1 hvrad hR hv_supp hav fu
  obtain ⟨Ck, hCk0, hkinB⟩ := kinetic_le_of_isLowB v h hv hv1 hvrad hR hv_supp hav
  obtain ⟨M, hM0, hMdB⟩ := Work.BoseBoxFock.exists_fderiv_chiScale_bound_inv
  obtain ⟨K0, hK0pos, harith⟩ := chAimg_arith6 (a := BoseGases.a v) (ε₀ := ε₀)
    (C0 := C₀) (Cs := Cs) (Ck := Ck) (M := M) (R := R) (nB := 1)
    hav hC₀0 hCs0 hCk0 hM0 hR.le (by norm_num)
  refine ⟨K0, hK0pos,
    (fun μ => if 0 < μ then K0 * BoseGases.a v / (8 * μ * (1 + (ellH v μ) ^ 3)) else 0),
    (fun _ => 0), ?_, ?_, ?_⟩
  · intro μ
    dsimp only
    by_cases hμ : 0 < μ
    · rw [if_pos hμ]
      have hℓ : (0 : ℝ) < ellH v μ := ellH_pos v μ
      exact div_nonneg (mul_nonneg (le_of_lt hK0pos) (le_of_lt hav)) (by positivity)
    · rw [if_neg hμ]
  · intro μ hμ
    dsimp only
    rw [if_pos hμ]
    have hℓ : (0 : ℝ) < ellH v μ := ellH_pos v μ
    have h1 : (ellH v μ) ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    have h2 : (1 : ℝ) + (ellH v μ) ^ 3 ≠ 0 := by positivity
    have hbud : 2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))
              * (K0 * BoseGases.a v / (8 * μ * (1 + (ellH v μ) ^ 3))))
        = K0 * (μ * BoseGases.a v) := by
      field_simp
      ring
    exact le_of_eq hbud
  · intro Nmin hNth hT hreg HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    have hμpos : 0 < μ := hAdm.1
    have hμa3 : μ * (BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
    have hreg' := hreg μ hAdm
    have hRℓ : R ≤ ellH v μ * Submission.BoseGases.chiR0 := hreg'.1
    have h4R : 4 * R ≤ ellH v μ := hreg'.2
    have h2R : 2 * R ≤ ellH v μ := by linarith
    have hℓpos : (0 : ℝ) < ellH v μ := ellH_pos v μ
    -- ## the arithmetic data
    set t : ℝ := μ * (BoseGases.a v) ^ 3 with htdef
    have htpos : (0 : ℝ) < t := by rw [htdef]; positivity
    have htε : t ≤ ε₀ := by rw [htdef]; exact hμa3
    have hdeq : (Work.BoseBox.paramsAt μ (BoseGases.a v)).d = Work.BoseBox.fsXp t 6 := by
      rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, htdef]
    have hdpos : (0 : ℝ) < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
      rw [hdeq]; exact Work.BoseBox.fsXp_pos htpos
    have hμeq : μ = t / (BoseGases.a v) ^ 3 := by rw [htdef]; field_simp
    have hℓeq : ellH v μ = Work.BoseBox.fsXp t (-(3 / 2 : ℝ))
        * (t / (BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ)) := by
      have hside : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) :=
        if_pos (Work.BoseBox.sideAt_pos hμpos hav)
      have hKleq : (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
          = Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) := by
        rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, htdef]
      rw [hside, Work.BoseBox.sideAt, Work.BoseBox.boxSide, hKleq]
      congr 1
      have hbase : μ * BoseGases.a v = t / (BoseGases.a v) ^ 2 := by
        rw [htdef]; field_simp
      rw [hbase]
    have hκeq : Work.BoseBoxFock.PCFU.chKappa v μ
        = 1 / ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ) := by
      rw [Work.BoseBoxFock.PCFU.chKappa, one_div]
      congr 1
      rw [show ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) from
        if_pos (Work.BoseBox.sideAt_pos hμpos hav)]
    -- ## the vacuous cases
    cases n with
    | zero => exact Fin.elim0 i
    | succ m =>
      cases m with
      | zero => exact absurd (Fin.ext (by omega)) hij
      | succ p =>
      -- ## the state
      set Θ : Submission.BoseGases.X (p + 2) → ℝ :=
        Work.BoseBoxFock.boxRestrictR (ellH v μ)
          (Φ : Submission.BoseGases.X (p + 2) → ℝ) with hΘdef
      have hΦc : Continuous (Φ : Submission.BoseGases.X (p + 2) → ℝ) := Φ.contDiff.continuous
      have hΘm : Measurable Θ := by
        rw [hΘdef]
        exact hΦc.measurable.mul
          (measurable_const.indicator (Submission.BoseGases.abox_measurable (p + 2) (ellH v μ)))
      obtain ⟨B, hB0, hΘb⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |Θ x| ≤ B := by
        obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact (p + 2) hℓpos).exists_bound_of_continuousOn
          (s := Submission.BoseGases.abox (p + 2) (ellH v μ))
          (f := (Φ : Submission.BoseGases.X (p + 2) → ℝ)) hΦc.continuousOn
        refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
        rw [hΘdef, Work.BoseBoxFock.boxRestrictR]
        by_cases hx : x ∈ Submission.BoseGases.abox (p + 2) (ellH v μ)
        · rw [Set.indicator_of_mem hx, mul_one]
          exact le_trans (by simpa [Real.norm_eq_abs] using hB x hx) (le_max_left _ _)
        · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
          exact le_max_right _ _
      have hΘsupp : ∀ x, x ∉ Submission.BoseGases.abox (p + 2) (ellH v μ) → Θ x = 0 := by
        intro x hx
        rw [hΘdef, Work.BoseBoxFock.boxRestrictR]
        simp [hx]
      haveI hΘfin : IsFiniteMeasure
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 2))).restrict
            (Submission.BoseGases.abox (p + 2) (ellH v μ))) :=
        ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
            exact Submission.BoseGases.abox_lt_top (p + 2) (ellH v μ) hℓpos.le⟩
      have hΘmem : MeasureTheory.MemLp Θ 2
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 2))).restrict
            (Submission.BoseGases.abox (p + 2) (ellH v μ))) := by
        refine MeasureTheory.MemLp.of_bound hΘm.aestronglyMeasurable.restrict B
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact hΘb x
      -- ## the flatness data
      have himg : ∀ (b u : E3), u ∈ Submission.BoseGases.acube (ellH v μ) →
          ‖((Submission.BoseGases.chiScale (ellH v μ) b : ℝ) : ℂ)
            * (∑' e : Fin 3 → ℤ, if e = 0 then 0
                else ((lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (u - b + (ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
          ≤ C₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d) ^ (2 * 96)
              / (ellH v μ) ^ 3 :=
        fun b u hu => himgB hdpos hℓpos hκeq b u hu
      set Cimg : ℝ := C₀ * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d) ^ (2 * 96)
          / (ellH v μ) ^ 3 with hCimgdef
      have hCimg0 : 0 ≤ Cimg := by rw [hCimgdef]; positivity
      -- ## the deviation fibre and the image factor
      set Ps : Submission.BoseGases.X (p + 2) → ℝ := fun x =>
        ∫ u in Submission.BoseGases.acube (ellH v μ),
          |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
            (Function.update x j u)| with hPsdef
      set Ga : Submission.BoseGases.X (p + 2) → ℂ := fun x =>
        ∫ u in Submission.BoseGases.acube (ellH v μ),
          (∑' e : Fin 3 → ℤ, if e = 0 then 0 else
              ((lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (u - x j + (ellH v μ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
            * ((Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
                  (Function.update x j u) : ℝ) : ℂ) with hGadef
      -- ## the pointwise flatness bound
      have hΓpt : ∀ x : Submission.BoseGases.X (p + 2),
          |Work.BoseK15.corpusBox.chiLam (ellH v μ) (x j)| * ‖Ga x‖ ≤ Cimg * Ps x := by
        intro x
        have h := chBimg_inner_le (ℓ := ellH v μ) (i := i) (j := j) hℓpos hΘm hB0 hΘb
          (fc := fc) (κ := Work.BoseBoxFock.PCFU.chKappa v μ) (Cimg := Cimg) himg x
        simpa only [hPsdef, hGadef, Complex.norm_real, Real.norm_eq_abs] using h
      -- ## the `i`-slot peel of the slot integrand
      obtain ⟨j', hj'⟩ := (Fin.exists_succAbove_eq_iff (x := i) (y := j)).mpr hij.symm
      set F : Submission.BoseGases.X (p + 2) → ℂ := fun x => ((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu (HM μ).N (x j - x i)
          * Ga x with hFdef
      have hchA : chAimg v h fc fu μ (HM μ).N i j Θ = ∫ x : Submission.BoseGases.X (p + 2), F x := by
        rw [chAimg, hFdef]
      -- ## the `N`-threshold
      have hN1 : 1 ≤ (HM μ).N := by
        have h2 : (2 : ℕ) ≤ ⌈Work.BoseBoxFock.chNThresh v μ⌉₊ := by
          have h2' : (2 : ℝ) ≤ Work.BoseBoxFock.chNThresh v μ := by
            rw [Work.BoseBoxFock.chNThresh]
            have hd2 : (0 : ℝ) < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ :=
              mul_pos (pow_pos hdpos 2) hℓpos
            have h1 : 0 ≤ 4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * ellH v μ)⁻¹ * ellH v μ / (2 * Real.pi) := by
              refine div_nonneg ?_ (by positivity)
              exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hd2.le)) hℓpos.le
            linarith
          calc (2 : ℕ) = ⌈(2 : ℝ)⌉₊ := (Nat.ceil_natCast 2).symm
            _ ≤ ⌈Work.BoseBoxFock.chNThresh v μ⌉₊ := Nat.ceil_mono h2'
        have h3 := hNth μ
        have h4 := hMono μ
        omega
      -- ## `Ga` is independent of the `i`-slot
      have hji : j ≠ i := by
        rw [← hj']
        exact Fin.succAbove_ne i j'
      have hbox_acube : Work.BoseK15.corpusBox.boxL (ellH v μ)
          ⊆ Submission.BoseGases.acube (ellH v μ) := by
        intro w hw
        rw [Submission.BoseGases.mem_acube_iff]
        intro m
        have h2 := Work.BoseFixR.mem_cell.mp (by
          rw [← Work.BoseBoxFock.corpusBox_boxL_eq_cell hℓpos]; exact hw) m
        exact ⟨by simpa only [neg_div] using (abs_le.mp h2).1, (abs_le.mp h2).2⟩
      have hGa_inv : ∀ (x : Submission.BoseGases.X (p + 2)) (z : E3),
          Ga (Function.update x i z) = Ga x := by
        intro x z
        rw [hGadef]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        have hxj : (Function.update x i z) j = x j := Function.update_of_ne hji z x
        have hcomm : Function.update (Function.update x i z) j u
            = Function.update (Function.update x j u) i z :=
          Function.update_comm hij z u x
        rw [hxj, hcomm, aQ_aP_update_invariant hij (Function.update x j u) z]
      -- ## abbreviations for the peeled quantities
      set GaP : Submission.BoseGases.X (p + 1) → ℂ := fun r =>
        ((Work.BoseK15.corpusBox.chiLam (ellH v μ)
            ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j)
          * Ga (Submission.BoseGases.kcInsN (p + 1) i (0, r)) : ℂ)) with hGaPdef
      set Sl : Submission.BoseGases.X (p + 1) → ℂ := fun r =>
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          (((Submission.BoseGases.chiScale (ellH v μ) y
            * Θ (Submission.BoseGases.kcInsN (p + 1) i (y, r)) : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu (HM μ).N
                ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j - y)) with hSldef
      set SlΦ : Submission.BoseGases.X (p + 1) → ℂ := fun r =>
        ∫ y in Submission.BoseGases.acube (ellH v μ),
          (((Submission.BoseGases.chiScale (ellH v μ) y
            * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (y, r)) : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu (HM μ).N
                ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j - y)) with hSlΦdef
      set Psm : Submission.BoseGases.X (p + 1) → ℝ := fun r =>
        Ps (Submission.BoseGases.kcInsN (p + 1) i (0, r)) with hPsmdef
      set Dirm : Submission.BoseGases.X (p + 1) → ℝ := fun r =>
        slotDir (fun w : E3 => Submission.BoseGases.chiScale (ellH v μ) w
          * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (w, r))) with hDirmdef
      set Ks : ℝ := Cs * (1 + R) ^ 3 * (ellH v μ) ^ 3
        * (Real.sqrt (2 * ellH v μ / Real.pi) + Real.sqrt (BoseGases.a v)) with hKsdef
      have hKs0 : 0 ≤ Ks := by
        rw [hKsdef]
        refine mul_nonneg ?_ (by positivity)
        exact mul_nonneg (mul_nonneg hCs0 (by positivity)) (by positivity)
      haveI hνfin : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
          (Submission.BoseGases.abox (p + 1) (ellH v μ))) :=
        ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
            exact Submission.BoseGases.abox_lt_top (p + 1) (ellH v μ) hℓpos.le⟩
      obtain ⟨E, hE0, hEdir⟩ := chAimg_dirBounded (ℓ := ellH v μ) (i := i) hℓpos
        (Φ := (Φ : Submission.BoseGases.X (p + 2) → ℝ)) Φ.contDiff
      -- ## the deviation fibre: measurability and boundedness
      have hPsm_meas : MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X (p + 1) =>
          Ps (Submission.BoseGases.kcInsN (p + 1) i (0, r)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
            (Submission.BoseGases.abox (p + 1) (ellH v μ))) := by
        rw [hPsdef]
        refine AEStronglyMeasurable.integral_prod_right' (α := Submission.BoseGases.X (p + 1))
          (E := ℝ)
          (μ := (MeasureTheory.volume : MeasureTheory.Measure
            (Submission.BoseGases.X (p + 1))).restrict (Submission.BoseGases.abox (p + 1) (ellH v μ)))
          (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube (ellH v μ)))
          (f := fun pp : Submission.BoseGases.X (p + 1) × E3 =>
            |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
              (Function.update (Submission.BoseGases.kcInsN (p + 1) i (0, pp.1)) j pp.2)|) ?_
        have hq : Measurable (fun x : Submission.BoseGases.X (p + 2) =>
            Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ) x) :=
          Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
        exact ((hq.comp (by fun_prop : Measurable fun pp : (Submission.BoseGases.X (p + 1)) × E3 =>
          Function.update (Submission.BoseGases.kcInsN (p + 1) i (0, pp.1)) j pp.2))).abs
            |>.aestronglyMeasurable
      have hPsm_bd : ∀ r : Submission.BoseGases.X (p + 1),
          |Ps (Submission.BoseGases.kcInsN (p + 1) i (0, r))| ≤ 2 * B * (ellH v μ) ^ 3 := by
        intro r
        have h1 := norm_integral_le_integral_norm
          (μ := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
            (Submission.BoseGases.acube (ellH v μ)))
          (fun u : E3 => |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
            (Function.update (Submission.BoseGases.kcInsN (p + 1) i (0, r)) j u)|)
        simp only [Real.norm_eq_abs, abs_abs] at h1
        have h2 : (∫ u in Submission.BoseGases.acube (ellH v μ),
            |Submission.BoseGases.aQ (ellH v μ) j (Submission.BoseGases.aP (ellH v μ) i Θ)
              (Function.update (Submission.BoseGases.kcInsN (p + 1) i (0, r)) j u)|)
            ≤ ∫ u in Submission.BoseGases.acube (ellH v μ), (2 * B) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun u => abs_nonneg _) (integrable_const _)
            (Filter.Eventually.of_forall fun u => ?_)
          exact aQ_aP_abs_le hℓpos hB0 hΘb i j
            (Function.update (Submission.BoseGases.kcInsN (p + 1) i (0, r)) j u)
        rw [hPsdef]
        exact h1.trans (h2.trans_eq (Submission.BoseGases.integral_const_acube (ellH v μ) hℓpos (2 * B)))
      -- ## the slices agree on the box
      have hSlice_eq : ∀ r ∈ Submission.BoseGases.abox (p + 1) (ellH v μ), Sl r = SlΦ r := by
        intro r hr
        rw [hSldef, hSlΦdef]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        have hfun : Submission.BoseGases.chiScale (ellH v μ) y
              * Θ (Submission.BoseGases.kcInsN (p + 1) i (y, r))
            = Submission.BoseGases.chiScale (ellH v μ) y
              * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (y, r)) := by
          by_cases hw : Submission.BoseGases.chiScale (ellH v μ) y = 0
          · rw [hw, zero_mul, zero_mul]
          · have hsupp : y ∈ Function.support (Work.BoseK15.corpusBox.chiLam (ellH v μ)) :=
              Function.mem_support.mpr (by rw [chiLam_eq_chiScale (ellH v μ)]; exact hw)
            have hwm : y ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
              Work.BoseK15.corpusBox.chiLam_supp hℓpos hsupp
            have hw' : y ∈ Submission.BoseGases.acube (ellH v μ) := hbox_acube hwm
            have hx : Submission.BoseGases.kcInsN (p + 1) i (y, r)
                ∈ Submission.BoseGases.abox (p + 2) (ellH v μ) :=
              Work.BoseBoxFock.PCFU.kcInsN_mem_abox i hr hw'
            rw [hΘdef, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]
        rw [hfun]
      -- ## the slicewise bound, applied to the smooth (`Φ`-)slices
      have hsliceBd : ∀ r : Submission.BoseGases.X (p + 1), ‖SlΦ r‖ ≤ Ks * Real.sqrt (Dirm r) := by
        intro r
        have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun w : E3 => Submission.BoseGases.chiScale (ellH v μ) w
            * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (w, r))) := by
          refine (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓpos)).mul ?_
          rw [show (fun w : E3 => (Φ : Submission.BoseGases.X (p + 2) → ℝ)
                (Submission.BoseGases.kcInsN (p + 1) i (w, r)))
              = fun w : E3 => (Φ : Submission.BoseGases.X (p + 2) → ℝ)
                  (Function.update (Submission.BoseGases.kcInsN (p + 1) i (0, r)) i w) from by
            funext w; rw [Work.BoseBoxFock.PCFU.kcInsN_eq_update]]
          exact Φ.contDiff.comp (contDiff_update (⊤ : ℕ∞)
            (Submission.BoseGases.kcInsN (p + 1) i (0, r)) i)
        have hsupp : tsupport (fun w : E3 => Submission.BoseGases.chiScale (ellH v μ) w
            * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (w, r)))
            ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
          refine closure_minimal (fun w hw => ?_)
            (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (ellH v μ)).isClosed
          by_contra hc
          refine hw ?_
          have hχ : Submission.BoseGases.chiScale (ellH v μ) w = 0 :=
            (Function.notMem_support (f := Work.BoseK15.corpusBox.chiLam (ellH v μ))).mp
              (fun hmem => hc (Work.BoseK15.corpusBox.chiLam_supp hℓpos hmem))
          simp [hχ]
        have hmain := hsliceB (μ := μ) hμpos (N := (HM μ).N) hN1 hRℓ
          ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j)
          (fun w : E3 => Submission.BoseGases.chiScale (ellH v μ) w
            * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (w, r)))
          hcd hsupp
        have hset : (∫ y in Submission.BoseGases.acube (ellH v μ),
              (((Submission.BoseGases.chiScale (ellH v μ) y
                * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (y, r)) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu (HM μ).N
                    ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j - y)))
            = (∫ y : E3, (((Submission.BoseGases.chiScale (ellH v μ) y
                * (Φ : Submission.BoseGases.X (p + 2) → ℝ) (Submission.BoseGases.kcInsN (p + 1) i (y, r)) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu (HM μ).N
                    ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j - y))) := by
          rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
          intro y hy
          have hy' : y ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) := fun hmem => hy (hbox_acube hmem)
          have hχ : Submission.BoseGases.chiScale (ellH v μ) y = 0 :=
            (Function.notMem_support (f := Work.BoseK15.corpusBox.chiLam (ellH v μ))).mp
              (fun hmem => hy' (Work.BoseK15.corpusBox.chiLam_supp hℓpos hmem))
          rw [hχ]; simp
        rw [hSlΦdef, hDirmdef]
        beta_reduce
        rw [hset]
        exact hmain
      -- ## the peel and the slice identity
      change ‖chAimg v h fc fu μ (HM μ).N i j Θ‖ ≤
        (fun μ => if 0 < μ then K0 * BoseGases.a v / (8 * μ * (1 + (ellH v μ) ^ 3)) else 0) μ
          * Work.BoseBoxFix.normB v μ (p + 2) Φ
      beta_reduce
      rw [if_pos hμpos, hchA]
      by_cases hInt : IntegrableOn F (Submission.BoseGases.abox (p + 2) (ellH v μ)) MeasureTheory.volume
      · have hboxeq : (∫ x : Submission.BoseGases.X (p + 2), F x)
            = ∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), F x :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
            simp [hFdef, hΘsupp x hx])).symm
        rw [hboxeq, Work.BoseBoxFock.PCFU.abox_integral_peelC i F hInt]
        have hsliceId : ∀ᵐ r ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
            (Submission.BoseGases.abox (p + 1) (ellH v μ))),
            (∫ y in Submission.BoseGases.acube (ellH v μ), F (Submission.BoseGases.kcInsN (p + 1) i (y, r)))
              = GaP r * Sl r := by
          filter_upwards with r
          have hpt : ∀ y : E3, F (Submission.BoseGases.kcInsN (p + 1) i (y, r))
              = GaP r * (((Submission.BoseGases.chiScale (ellH v μ) y
                  * Θ (Submission.BoseGases.kcInsN (p + 1) i (y, r)) : ℝ) : ℂ)
                  * Work.BoseBoxFock.PCFU.KfrU v h μ fu (HM μ).N
                      ((Submission.BoseGases.kcInsN (p + 1) i (0, r)) j - y)) := by
            intro y
            have hxi : (Submission.BoseGases.kcInsN (p + 1) i (y, r)) i = y :=
              Submission.BoseGases.kc_insN_apply_same (p + 1) i y r
            have hxj : (Submission.BoseGases.kcInsN (p + 1) i (y, r)) j
                = (Submission.BoseGases.kcInsN (p + 1) i (0, r)) j :=
              Submission.BoseGases.kc_insN_other_indep (p + 1) i y 0 r j hji
            have hGa : Ga (Submission.BoseGases.kcInsN (p + 1) i (y, r))
                = Ga (Submission.BoseGases.kcInsN (p + 1) i (0, r)) := by
              rw [Work.BoseBoxFock.PCFU.kcInsN_eq_update i r y]
              exact hGa_inv (Submission.BoseGases.kcInsN (p + 1) i (0, r)) y
            rw [hFdef]
            simp only
            rw [hxi, hxj, hGa, hGaPdef]
            push_cast
            rw [chiLam_eq_chiScale (ellH v μ)]
            ring
          rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
          rw [MeasureTheory.integral_const_mul]
        -- ## the pointwise bound and Cauchy–Schwarz
        have hDirmnn : 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
            (Submission.BoseGases.abox (p + 1) (ellH v μ)))] Dirm :=
          Filter.Eventually.of_forall fun r =>
            MeasureTheory.integral_nonneg fun w => Finset.sum_nonneg fun k _ => sq_nonneg _
        have hPsm_nn : ∀ r : Submission.BoseGases.X (p + 1), 0 ≤ Psm r := by
          intro r
          rw [hPsmdef, hPsdef]
          exact MeasureTheory.integral_nonneg fun u => abs_nonneg _
        have hpt2 : ∀ᵐ r ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
            (Submission.BoseGases.abox (p + 1) (ellH v μ))),
            ‖GaP r * Sl r‖ ≤ (Cimg * Ks) * (Psm r * Real.sqrt (Dirm r)) := by
          filter_upwards [MeasureTheory.self_mem_ae_restrict
            (Submission.BoseGases.abox_measurable (p + 1) (ellH v μ))] with r hr
          rw [norm_mul, hSlice_eq r hr]
          have h1 : ‖GaP r‖ * ‖SlΦ r‖ ≤ Cimg * Psm r * (Ks * Real.sqrt (Dirm r)) := by
            refine mul_le_mul ?_ (hsliceBd r) (norm_nonneg _) (by positivity)
            have h := hΓpt (Submission.BoseGases.kcInsN (p + 1) i (0, r))
            simpa only [hGaPdef, hPsmdef, Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_mul] using h
          calc ‖GaP r‖ * ‖SlΦ r‖ ≤ Cimg * Psm r * (Ks * Real.sqrt (Dirm r)) := h1
            _ = (Cimg * Ks) * (Psm r * Real.sqrt (Dirm r)) := by ring
        have hPsm_memlp : MeasureTheory.MemLp Psm 2
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
              (Submission.BoseGases.abox (p + 1) (ellH v μ))) := by
          refine MeasureTheory.MemLp.of_bound ?_ (2 * B * (ellH v μ) ^ 3)
            (Filter.Eventually.of_forall fun r => ?_)
          · rw [hPsmdef]; exact hPsm_meas
          · rw [Real.norm_eq_abs, hPsmdef]; exact hPsm_bd r
        have hDirm_memlp : MeasureTheory.MemLp Dirm 2
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
              (Submission.BoseGases.abox (p + 1) (ellH v μ))) := by
          refine MeasureTheory.MemLp.of_bound ?_ E ?_
          · rw [hDirmdef]; exact hEdir.2
          · filter_upwards [MeasureTheory.self_mem_ae_restrict
              (Submission.BoseGases.abox_measurable (p + 1) (ellH v μ))] with r hr
            have hnn : 0 ≤ Dirm r := by
              rw [hDirmdef]
              exact MeasureTheory.integral_nonneg fun w => Finset.sum_nonneg fun k _ => sq_nonneg _
            rw [Real.norm_eq_abs, abs_of_nonneg hnn, hDirmdef]
            exact hEdir.1 r hr
        have hCs := cs_sqrt_bound (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
            (Submission.BoseGases.abox (p + 1) (ellH v μ)))
          (f := Psm) (g := Dirm) hPsm_memlp hDirm_memlp hDirmnn
        have hCs' : (∫ r : Submission.BoseGases.X (p + 1), Psm r * Real.sqrt (Dirm r)
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                (Submission.BoseGases.abox (p + 1) (ellH v μ))))
            ≤ Real.sqrt (∫ r : Submission.BoseGases.X (p + 1), (Psm r) ^ 2
                ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                  (Submission.BoseGases.abox (p + 1) (ellH v μ))))
              * Real.sqrt (∫ r : Submission.BoseGases.X (p + 1), Dirm r
                ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                  (Submission.BoseGases.abox (p + 1) (ellH v μ)))) := by
          refine le_trans (le_of_eq ?_) hCs
          apply MeasureTheory.integral_congr_ae
          filter_upwards with r
          rw [Real.norm_of_nonneg (hPsm_nn r)]
        have hSqrt_memlp : MeasureTheory.MemLp (fun r : Submission.BoseGases.X (p + 1) =>
            Real.sqrt (Dirm r)) 2
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
              (Submission.BoseGases.abox (p + 1) (ellH v μ))) := by
          refine MeasureTheory.MemLp.of_bound ?_ (Real.sqrt E) ?_
          · rw [hDirmdef]
            exact Real.continuous_sqrt.comp_aestronglyMeasurable hEdir.2
          · filter_upwards [MeasureTheory.self_mem_ae_restrict
              (Submission.BoseGases.abox_measurable (p + 1) (ellH v μ))] with r hr
            have hsq : 0 ≤ Real.sqrt (Dirm r) := Real.sqrt_nonneg _
            rw [Real.norm_eq_abs, abs_of_nonneg hsq]
            exact Real.sqrt_le_sqrt (hEdir.1 r hr)
        have hmaj : Integrable (fun r : Submission.BoseGases.X (p + 1) =>
            (Cimg * Ks) * (Psm r * Real.sqrt (Dirm r)))
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
              (Submission.BoseGases.abox (p + 1) (ellH v μ))) :=
          Integrable.const_mul (hPsm_memlp.integrable_mul hSqrt_memlp) _
        have hstep : ‖∫ r : Submission.BoseGases.X (p + 1), GaP r * Sl r
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                (Submission.BoseGases.abox (p + 1) (ellH v μ)))‖
            ≤ (Cimg * Ks) * (Real.sqrt (∫ r : Submission.BoseGases.X (p + 1), (Psm r) ^ 2
                  ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                    (Submission.BoseGases.abox (p + 1) (ellH v μ))))
                * Real.sqrt (∫ r : Submission.BoseGases.X (p + 1), Dirm r
                  ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                    (Submission.BoseGases.abox (p + 1) (ellH v μ))))) := by
          refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
          refine le_trans (MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun r => norm_nonneg _) hmaj hpt2) ?_
          rw [MeasureTheory.integral_const_mul]
          exact mul_le_mul_of_nonneg_left hCs' (by positivity)
        -- ## the two integral bounds
        have hnormB_eq : Work.BoseBoxFix.normB v μ (p + 2) Φ
            = ∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2 := by
          have hbox : Submission.BoseGases.abox (p + 2) (Work.BoseBox.sideAt μ (BoseGases.a v))
              = Submission.BoseGases.abox (p + 2) (ellH v μ) := by
            rw [show Work.BoseBox.sideAt μ (BoseGases.a v) = ellH v μ from
              (if_pos (Work.BoseBox.sideAt_pos hμpos hav)).symm]
          rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hbox]
        have hΘsq : (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), (Θ x) ^ 2)
            = ∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MeasureTheory.self_mem_ae_restrict
            (Submission.BoseGases.abox_measurable (p + 2) (ellH v μ))] with x hx
          rw [hΘdef, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]
        have hTheta2 : (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), (Θ x) ^ 2)
            = Work.BoseBoxFix.normB v μ (p + 2) Φ := by
          rw [hΘsq, ← hnormB_eq]
        have hPsm2b : (∫ r : Submission.BoseGases.X (p + 1), (Psm r) ^ 2
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                (Submission.BoseGases.abox (p + 1) (ellH v μ))))
            ≤ (ellH v μ) ^ 3 *
                (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2) := by
          have hp := chAimg_psL2 (ℓ := ellH v μ) (i := i) (j := j) hℓpos hij hΘm hB0 hΘb hΘmem
          rw [hPsmdef]
          exact hp.trans_eq (by rw [hΘsq])
        have hDirSum : (∫ r : Submission.BoseGases.X (p + 1), Dirm r
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
                (Submission.BoseGases.abox (p + 1) (ellH v μ))))
            ≤ 2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3 *
                  (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
              + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹ *
                  (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2) := by
          have hkin' := hkinB μ hAdm ⟨hRℓ, h2R⟩ hJ (p + 2) Φ hn hnorm hlowB i
          rw [hnormB_eq] at hkin'
          have hmain := chAimg_dirichletLe (ℓ := ellH v μ) (i := i) hℓpos
            (Φ := (Φ : Submission.BoseGases.X (p + 2) → ℝ)) Φ.contDiff
            (Ck := Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3 *
              (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
            (M := M) (by positivity) hM0 (hMdB (ellH v μ) hℓpos) hkin'
          rw [← MeasureTheory.Measure.restrict_restrict_of_subset
            (Set.Subset.refl (Submission.BoseGases.abox (p + 1) (ellH v μ)))]
          rw [hDirmdef]
          beta_reduce
          exact hmain
        -- ## the arithmetic
        have hnB : 0 ≤ (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2) :=
          MeasureTheory.integral_nonneg fun x => sq_nonneg _
        have har := harith t (ellH v μ) μ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d)
          htpos htε hℓeq hμeq hdeq
        rw [MeasureTheory.integral_congr_ae hsliceId]
        rw [hnormB_eq]
        refine le_trans hstep ?_
        rw [hCimgdef, hKsdef, hdeq]
        refine le_trans (mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.sqrt_le_sqrt hPsm2b) (Real.sqrt_le_sqrt hDirSum)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)) ?_
        -- the two square roots are `I`-homogeneous
        have hZ0 : (0 : ℝ) ≤ 2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
            + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹ := by positivity
        have hfac : Real.sqrt ((ellH v μ) ^ 3
                * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
              * Real.sqrt (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3
                    * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
                  + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹
                    * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
            = (Real.sqrt ((ellH v μ) ^ 3)
                * Real.sqrt (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
                  + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹))
              * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2) := by
          rw [show 2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3
                  * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
                + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹
                  * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2)
              = (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
                  + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹)
                * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2)
              from by ring]
          rw [Real.sqrt_mul (show (0 : ℝ) ≤ (ellH v μ) ^ 3 by positivity), Real.sqrt_mul hZ0]
          calc Real.sqrt ((ellH v μ) ^ 3)
                * Real.sqrt (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2)
                * (Real.sqrt (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
                    + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹)
                  * Real.sqrt (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2))
              = (Real.sqrt ((ellH v μ) ^ 3)
                  * Real.sqrt (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
                    + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹))
                * (Real.sqrt (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2)
                  * Real.sqrt (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2)) := by ring
            _ = (Real.sqrt ((ellH v μ) ^ 3)
                  * Real.sqrt (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
                    + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹))
                * (∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), Φ.toFun x ^ 2) := by
                rw [Real.mul_self_sqrt hnB]
        rw [hfac]
        have har' : C₀ * (Work.BoseBox.fsXp t 6) ^ (2 * 96) / (ellH v μ) ^ 3
              * (Cs * (1 + R) ^ 3 * (ellH v μ) ^ 3
                * (Real.sqrt (2 * (ellH v μ) / Real.pi) + Real.sqrt (BoseGases.a v)))
              * (Real.sqrt ((ellH v μ) ^ 3)
                * Real.sqrt (2 * (Ck * μ ^ 2 * BoseGases.a v * (ellH v μ) ^ 3)
                  + 2 * M ^ 2 * ((ellH v μ) ^ 2)⁻¹))
            ≤ K0 * BoseGases.a v / (8 * μ * (1 + (ellH v μ) ^ 3)) := by
          have h := har
          rw [hdeq] at h
          simpa only [mul_one, Real.sqrt_one] using h
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right har' hnB)
        ring
      · have hboxeq : (∫ x : Submission.BoseGases.X (p + 2), F x)
            = ∫ x in Submission.BoseGases.abox (p + 2) (ellH v μ), F x :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
            simp [hFdef, hΘsupp x hx])).symm
        rw [hboxeq, MeasureTheory.integral_undef (μ := MeasureTheory.volume.restrict
          (Submission.BoseGases.abox (p + 2) (ellH v μ))) hInt]
        simp only [norm_zero]
        positivity

end Work.BoseBoxFock.PCFU
