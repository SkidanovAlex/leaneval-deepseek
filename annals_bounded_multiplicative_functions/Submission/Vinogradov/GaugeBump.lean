/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.DecouplingClass
import Submission.Commons.Analysis.Fourier.aniso_gauge_bump
import Submission.Commons.Analysis.Convolution.integrable_aniso_tent


/-!
# The gauge bump of a plate (GLYZ §3, geometric half)

The uncertainty principle `IsFourierRep.uncertainty` needs, for a plate `𝒰_J = plate k δ c`,
a function `ψ` with `ψ̂ ≡ 1` on `𝒰_J` and `|ψ| ≤ C φ_J`, where `φ_J` is the `L¹`-normalised
bump adapted to the *polar* plate `𝒰_J^o = polarPlate k δ c`.  This module supplies the
**geometric half** of that construction:

* `diagFact k` — the diagonal map `e_i ↦ (i+1)! · e_i`, sending the standard box `[-1,1]^k`
  onto `plateBox k` (`diagFact_image_box`);
* `plateMapLin k δ c` — the linear map with `e_i ↦ δ^(i+1) • γ^(i+1)(c)`
  (`plateMapLin_single`); it sends the standard box `[-1,1]^k` onto `plate k δ c − γ(c)`
  (`plateMapLin_image_box`), and it is invertible (`plateMapLin_injective`) as the composite
  of `affVecDualLin` (`Plate.affVecDual_bijective`) with the invertible diagonal `diagFact`;
* `plateGaugeLin k δ c` — the transpose of `plateMapLin`, whose coordinates are exactly the
  gauge coordinates of `polarPlate k δ c`:
  `(plateGaugeLin x)_i = δ^(i+1) · ⟪x, γ^(i+1)(c)⟫`
  (`inner_plateMapLin_plateGaugeLin`).  Hence `LinearMap.det (plateGaugeLin k δ c) ≠ 0`
  (`plateGaugeLin_det_ne_zero`) — everything the change-of-variables formula needs, with no
  determinant *value* and no transpose-determinant identity.

The analytic half (`psiPlate`, `phiBump`, the Fourier identity, the two `L¹` bounds) is the
next module; see `ROADMAP.lean`, session 30, section (C).
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option maxHeartbeats 2000000

namespace Submission.Vinogradov

/-! ## 1. The diagonal factorial rescaling -/

/-- The diagonal map `e_i ↦ (i+1)! · e_i` on `E k`. -/
noncomputable def diagFact (k : ℕ) : E k →ₗ[ℝ] E k where
  toFun x := (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => ((i.val + 1).factorial : ℝ) * x i)
  map_add' x y := by
    ext i
    change ((i.val + 1).factorial : ℝ) * (x + y).ofLp i
      = ((i.val + 1).factorial : ℝ) * x.ofLp i
        + ((i.val + 1).factorial : ℝ) * y.ofLp i
    rw [show (x + y).ofLp i = x.ofLp i + y.ofLp i from rfl, mul_add]
  map_smul' c x := by
    ext i
    change ((i.val + 1).factorial : ℝ) * (c • x).ofLp i
      = c * (((i.val + 1).factorial : ℝ) * x.ofLp i)
    rw [show (c • x).ofLp i = c * x.ofLp i from rfl]
    ring

/-- Defining equation of `diagFact`. -/
lemma diagFact_apply (k : ℕ) (x : E k) (i : Fin k) :
    diagFact k x i = ((i.val + 1).factorial : ℝ) * x i := by
  rw [diagFact]
  simp

/-- `diagFact` on the standard basis vectors. -/
lemma diagFact_single (k : ℕ) (i : Fin k) :
    diagFact k (PiLp.single 2 i 1) = ((i.val + 1).factorial : ℝ) • PiLp.single 2 i 1 := by
  ext j
  rw [diagFact_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- **`diagFact` maps the standard box onto `plateBox k`.** -/
lemma diagFact_image_box (k : ℕ) :
    diagFact k '' {y : E k | ∀ i : Fin k, |y i| ≤ 1} = plateBox k := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i
    have hfac : (0 : ℝ) < ((i.val + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    rw [diagFact_apply, abs_mul, abs_of_nonneg (le_of_lt hfac)]
    calc ((i.val + 1).factorial : ℝ) * |y i| ≤ ((i.val + 1).factorial : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (le_of_lt hfac)
      _ = ((i.val + 1).factorial : ℝ) := mul_one _
  · intro hz
    refine ⟨(WithLp.equiv 2 (Fin k → ℝ)).symm
      (fun i => (((i.val + 1).factorial : ℝ))⁻¹ * z i), ?_, ?_⟩
    · intro i
      have hfac : (0 : ℝ) < ((i.val + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
      change |(((i.val + 1).factorial : ℝ))⁻¹ * z i| ≤ 1
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hfac))]
      calc (((i.val + 1).factorial : ℝ))⁻¹ * |z i|
          ≤ (((i.val + 1).factorial : ℝ))⁻¹ * ((i.val + 1).factorial : ℝ) :=
            mul_le_mul_of_nonneg_left (hz i) (inv_nonneg.mpr (le_of_lt hfac))
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hfac)
    · ext i
      rw [diagFact_apply]
      change ((i.val + 1).factorial : ℝ) * ((((i.val + 1).factorial : ℝ))⁻¹ * z i) = z i
      rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
        one_mul]

/-! ## 2. The plate map -/

/-- **The plate map**: the linear map sending the standard box `[-1,1]^k` onto
`plate k δ c − γ(c)`.  Explicitly `e_i ↦ δ^(i+1) • γ^(i+1)(c)`. -/
noncomputable def plateMapLin (k : ℕ) (δ c : ℝ) : E k →ₗ[ℝ] E k :=
  (affVecDualLin k δ c).comp (diagFact k)

/-- Defining equation of `plateMapLin`. -/
lemma plateMapLin_apply (k : ℕ) (δ c : ℝ) (x : E k) :
    plateMapLin k δ c x = affVecDual k δ c (diagFact k x) := rfl

/-- The plate map on the standard basis vectors: `e_i ↦ δ^(i+1) • γ^(i+1)(c)`. -/
lemma plateMapLin_single (k : ℕ) (δ c : ℝ) (i : Fin k) :
    plateMapLin k δ c (PiLp.single 2 i 1)
      = δ ^ (i.val + 1) • gammaDeriv k (i.val + 1) c := by
  rw [plateMapLin_apply, diagFact_single, ← affVecDualLin_apply, map_smul,
    affVecDualLin_apply, affVecDual_single, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]

/-- A vector of `E k` is the sum of its coordinates times the standard basis vectors. -/
lemma sum_single_eq (k : ℕ) (x : E k) :
    (∑ i : Fin k, x i • PiLp.single 2 i 1) = x := by
  conv_rhs => rw [← Module.Basis.sum_repr (PiLp.basisFun 2 ℝ (Fin k)) x]
  exact Finset.sum_congr rfl fun i _ => by
    rw [PiLp.basisFun_apply]
    congr 1

/-- **The plate map sends the standard box onto `plate k δ c − γ(c)`.** -/
lemma plateMapLin_image_box (k : ℕ) (δ c : ℝ) :
    plateMapLin k δ c '' {y : E k | ∀ i : Fin k, |y i| ≤ 1}
      = (fun z => z - gammaVec k c) '' plate k δ c := by
  have h1 : plateMapLin k δ c ''
      {y : E k | ∀ i : Fin k, |y i| ≤ 1} = affVecDualLin k δ c '' plateBox k := by
    ext z
    constructor
    · rintro ⟨y, hy, hz⟩
      exact ⟨diagFact k y, by rw [← diagFact_image_box]; exact Set.mem_image_of_mem _ hy, hz⟩
    · rintro ⟨y, hy, hz⟩
      rw [← diagFact_image_box] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨y', hy', hz⟩
  have h2 : (fun z => z - gammaVec k c) '' plate k δ c
      = affVecDualLin k δ c '' plateBox k := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [plate] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      exact ⟨y, hy, by simp only [affMap_apply]; abel⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨gammaVec k c + affVecDualLin k δ c y, by
        rw [plate]; exact ⟨y, hy, rfl⟩, by simp only [add_sub_cancel_left]⟩
  rw [h1, h2]

/-! ## 3. The gauge coordinates -/

/-- **The gauge coordinates of the polar plate**: `x ↦ (δ^(i+1)⟪x, γ^(i+1)(c)⟫)_i`. -/
noncomputable def plateGaugeLin (k : ℕ) (δ c : ℝ) : E k →ₗ[ℝ] E k where
  toFun x := (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun i => δ ^ (i.val + 1) * ⟪x, gammaDeriv k (i.val + 1) c⟫)
  map_add' x y := by
    ext i
    change δ ^ (i.val + 1) * ⟪x + y, gammaDeriv k (i.val + 1) c⟫
      = δ ^ (i.val + 1) * ⟪x, gammaDeriv k (i.val + 1) c⟫
        + δ ^ (i.val + 1) * ⟪y, gammaDeriv k (i.val + 1) c⟫
    rw [inner_add_left, mul_add]
  map_smul' a x := by
    ext i
    change δ ^ (i.val + 1) * ⟪a • x, gammaDeriv k (i.val + 1) c⟫
      = a * (δ ^ (i.val + 1) * ⟪x, gammaDeriv k (i.val + 1) c⟫)
    rw [real_inner_smul_left]
    ring

/-- Defining equation of `plateGaugeLin`. -/
lemma plateGaugeLin_apply (k : ℕ) (δ c : ℝ) (x : E k) (i : Fin k) :
    plateGaugeLin k δ c x i = δ ^ (i.val + 1) * ⟪x, gammaDeriv k (i.val + 1) c⟫ := by
  rw [plateGaugeLin]
  simp

/-! ## 3b. The transpose identity and the invertibility of the gauge map -/

/-- **`plateGaugeLin` is the transpose of `plateMapLin`.** -/
lemma inner_plateMapLin_plateGaugeLin (k : ℕ) (δ c : ℝ) (u x : E k) :
    ⟪plateMapLin k δ c u, x⟫ = ⟪u, plateGaugeLin k δ c x⟫ := by
  conv_lhs => rw [← sum_single_eq k u]
  rw [map_sum, sum_inner, inner_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, real_inner_smul_left, plateMapLin_single, real_inner_smul_left,
    plateGaugeLin_apply, real_inner_comm]

/-- `plateMapLin` is injective (it is the composite of two bijections). -/
lemma plateMapLin_injective (k : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    Function.Injective (plateMapLin k δ c) := by
  intro x y h
  have h2 : affVecDualLin k δ c (diagFact k x) = affVecDualLin k δ c (diagFact k y) := h
  have h3 : diagFact k x = diagFact k y := (affVecDual_bijective k hδ c).1 h2
  ext i
  have h4 := congrArg (fun z : E k => z i) h3
  rw [diagFact_apply, diagFact_apply] at h4
  exact mul_left_cancel₀ (by positivity : ((i.val + 1).factorial : ℝ) ≠ 0) h4

/-- `plateMapLin` is surjective. -/
lemma plateMapLin_surjective (k : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    Function.Surjective (plateMapLin k δ c) :=
  LinearMap.injective_iff_surjective.mp (plateMapLin_injective k hδ c)

/-- `plateGaugeLin` is injective, being the transpose of a surjective map. -/
lemma plateGaugeLin_injective (k : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    Function.Injective (plateGaugeLin k δ c) := by
  intro x y h
  have hzero : plateGaugeLin k δ c (x - y) = 0 := by rw [map_sub, h, sub_self]
  have h0 : x - y = 0 := by
    obtain ⟨u, hu⟩ := plateMapLin_surjective k hδ c (x - y)
    have hz : plateGaugeLin k δ c (plateMapLin k δ c u) = 0 := by rw [hu]; exact hzero
    have h1 : ⟪x - y, x - y⟫ = 0 := by
      rw [← hu, inner_plateMapLin_plateGaugeLin, hz, inner_zero_right]
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp h1
  exact sub_eq_zero.mp h0

lemma plateGaugeLin_ker_eq_bot (k : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    (plateGaugeLin k δ c).ker = ⊥ :=
  LinearMap.ker_eq_bot'.mpr fun x hx => plateGaugeLin_injective k hδ c (by
    rw [map_zero]; exact hx)

/-- **The determinant of `plateGaugeLin` is nonzero** (no matrix computation: it follows
from injectivity). -/
lemma plateGaugeLin_det_ne_zero (k : ℕ) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    LinearMap.det (plateGaugeLin k δ c) ≠ 0 := fun h =>
  (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) (plateGaugeLin_ker_eq_bot k hδ c)

/-! ## 4. The analytic half: the gauge bump of a plate -/

/-- The sup-norm gauge `max_i |x_i|` on `E k`. -/
noncomputable def gauge (k : ℕ) (hk : 1 ≤ k) (x : E k) : ℝ :=
  (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => |x i|

lemma gauge_nonneg (k : ℕ) (hk : 1 ≤ k) (x : E k) : 0 ≤ gauge k hk x :=
  le_trans (abs_nonneg _)
    (Finset.le_sup' (s := Finset.univ) (fun i : Fin k => |x i|)
      (Finset.mem_univ (⟨0, hk⟩ : Fin k)))

lemma le_gauge (k : ℕ) (hk : 1 ≤ k) (x : E k) (i : Fin k) : |x i| ≤ gauge k hk x :=
  Finset.le_sup' (s := Finset.univ) (fun i : Fin k => |x i|) (Finset.mem_univ i)

/-- The character `chat k (-z) ξ` as the exponential appearing in the anisotropic bump. -/
lemma chat_neg_eq (k : ℕ) (z ξ : E k) :
    chat k (-z) ξ
      = Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i : Fin k, ξ i * z i : ℝ) : ℂ)) := by
  have h : ⟪-z, ξ⟫ = -((∑ i : Fin k, ξ i * z i : ℝ)) := by
    rw [inner_neg_left, inner_coord]
    rw [Finset.sum_congr rfl (fun i _ => mul_comm (z i) (ξ i))]
  rw [chat, h]
  congr 1
  push_cast
  ring

/-- The character on `-y` at `ξ` equals the character on `y` at `-ξ`. -/
lemma chat_neg_left (k : ℕ) (y ξ : E k) : chat k (-y) ξ = chat k y (-ξ) := by
  rw [chat, chat, inner_neg_left, inner_neg_right, Complex.ofReal_neg]

/-- Integrability of the gauge power. -/
lemma integrable_gauge_rpow (k : ℕ) (hk : 1 ≤ k) {A : ℝ} (hA : (k : ℝ) < A) :
    Integrable (fun z : E k => (max 1 (gauge k hk z)) ^ (-A)) := by
  have h0 : Integrable (fun y : Fin k → ℝ =>
      (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |y i|)) ^ (-A)) := Commons.Analysis.Convolution.integrable_aniso_tent k hk hA
  have hiff := (PiLp.volume_preserving_ofLp (Fin k)).integrable_comp h0.aestronglyMeasurable
  rw [show (fun z : E k => (max 1 (gauge k hk z)) ^ (-A))
      = (fun y : Fin k → ℝ => (max 1 ((Finset.univ : Finset (Fin k)).sup'
          ⟨⟨0, hk⟩, Finset.mem_univ _⟩ fun i => |y i|)) ^ (-A)) ∘ WithLp.ofLp from rfl]
  exact hiff.mpr h0

/-- **The anisotropic bump, transferred to `E k`.** -/
theorem exists_bump_at_one (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : (k : ℝ) < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ ψ : E k → ℂ, Integrable ψ ∧
      (∀ ξ : E k, (∀ i : Fin k, |ξ i| ≤ 1) → (∫ z, ψ z * chat k (-z) ξ) = 1) ∧
      (∀ x : E k, ‖ψ x‖ ≤ C * (max 1 (gauge k hk x)) ^ (-A)) ∧
      (∫ z, ‖ψ z‖) ≤ C := by
  obtain ⟨C, hC, ψ, hψint, hψhat, hψdecay, hψL1⟩ :=
    Commons.Analysis.Fourier.aniso_gauge_bump k hk A hA
  refine ⟨C, hC, fun z => ψ 1 z.ofLp, ?_, ?_, ?_, ?_⟩
  · exact (PiLp.volume_preserving_ofLp (Fin k)).integrable_comp
      (hψint 1 one_pos le_rfl).aestronglyMeasurable |>.mpr (hψint 1 one_pos le_rfl)
  · intro ξ hξ
    have hme : MeasurableEmbedding (WithLp.toLp 2 : (Fin k → ℝ) → E k) :=
      (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurableEmbedding
    have hcomp := (PiLp.volume_preserving_toLp (ι := Fin k)).integral_comp hme
      (fun z : E k => ψ 1 z.ofLp * chat k (-z) ξ)
    rw [← hcomp]
    rw [show (fun y : Fin k → ℝ => ψ 1 (WithLp.toLp 2 y).ofLp * chat k (-(WithLp.toLp 2 y)) ξ)
        = fun y : Fin k → ℝ => ψ 1 y
          * Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ i : Fin k, ξ i * y i : ℝ) : ℂ))
        from funext fun y => by rw [WithLp.ofLp_toLp, chat_neg_eq]]
    exact hψhat 1 one_pos le_rfl (fun i => ξ i) (fun i => by simpa using hξ i)
  · intro x
    simpa [gauge] using hψdecay 1 one_pos le_rfl x.ofLp
  · have h := hψL1 1 one_pos le_rfl
    have hcomp := (PiLp.volume_preserving_ofLp (Fin k)).integral_comp
      (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm)
      (fun z : Fin k → ℝ => ‖ψ 1 z‖)
    rw [← hcomp] at h
    simpa using h

/-! ## 5. The change of variables under `plateGaugeLin` -/

lemma integrable_comp_plateGaugeLin {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) {F : E k → G} (hF : Integrable F) :
    Integrable (fun x : E k => F (plateGaugeLin k δ c x)) := by
  have hdet := plateGaugeLin_det_ne_zero k hδ c
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (E k)) hdet
  have hae : AEMeasurable (plateGaugeLin k δ c) volume :=
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
  have h1 : Integrable F (Measure.map (plateGaugeLin k δ c) volume) := by
    rw [hmap]
    have hc0 : ENNReal.ofReal |(LinearMap.det (plateGaugeLin k δ c))⁻¹| ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact abs_pos.mpr (inv_ne_zero hdet)
    rw [MeasureTheory.integrable_smul_measure hc0 ENNReal.ofReal_ne_top]
    exact hF
  exact (MeasureTheory.integrable_map_measure h1.aestronglyMeasurable hae).mp h1

lemma integral_comp_plateGaugeLin {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) {F : E k → G} (hF : Integrable F) :
    (∫ x : E k, F (plateGaugeLin k δ c x))
      = (|(LinearMap.det (plateGaugeLin k δ c))⁻¹| : ℝ) • ∫ y : E k, F y := by
  have hdet := plateGaugeLin_det_ne_zero k hδ c
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (E k)) hdet
  have hae : AEMeasurable (plateGaugeLin k δ c) volume :=
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
  have h1 : Integrable F (Measure.map (plateGaugeLin k δ c) volume) := by
    rw [hmap]
    have hc0 : ENNReal.ofReal |(LinearMap.det (plateGaugeLin k δ c))⁻¹| ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      exact abs_pos.mpr (inv_ne_zero hdet)
    rw [MeasureTheory.integrable_smul_measure hc0 ENNReal.ofReal_ne_top]
    exact hF
  rw [← MeasureTheory.integral_map hae h1.aestronglyMeasurable, hmap,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Continuity of the character in its second variable. -/
lemma continuous_chat_right (k : ℕ) (ξ : E k) : Continuous (fun x : E k => chat k x ξ) := by
  unfold chat
  fun_prop

/-! ## 6. The gauge bump of a plate (the analytic half of GLYZK §3) -/

/-- **The bump attached to a plate**: the inverse Fourier transform of a bump adapted to
the plate `plate k δ c`, normalised so that its Fourier transform is `1` on the plate. -/
noncomputable def psiPlate (k : ℕ) (δ c : ℝ) (ψ : E k → ℂ) : E k → ℂ :=
  fun x => ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
    * (chat k x (gammaVec k c) * ψ (plateGaugeLin k δ c x))

/-- The `L¹`-normalised bump adapted to the polar plate, written in the gauge coordinates
of `plateGaugeLin k δ c`. -/
noncomputable def phiPlate (k : ℕ) (hk : 1 ≤ k) (δ c A Cφ : ℝ) : E k → ℝ :=
  fun x => Cφ * |LinearMap.det (plateGaugeLin k δ c)|
    * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A)

/-- The modulus of the plate bump. -/
lemma norm_psiPlate (k : ℕ) (δ c : ℝ) (ψ : E k → ℂ) (x : E k) :
    ‖psiPlate k δ c ψ x‖
      = |LinearMap.det (plateGaugeLin k δ c)| * ‖ψ (plateGaugeLin k δ c x)‖ := by
  rw [psiPlate, norm_mul, norm_mul, chat_norm, one_mul]
  simp

/-- The polar bump is nonnegative. -/
lemma phiPlate_nonneg (k : ℕ) (hk : 1 ≤ k) (δ c A Cφ : ℝ) (hCφ : 0 ≤ Cφ) (x : E k) :
    0 ≤ phiPlate k hk δ c A Cφ x := by
  rw [phiPlate]
  exact mul_nonneg (mul_nonneg hCφ (abs_nonneg _))
    (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)

/-- **The Fourier transform of the plate bump is `1` on the plate.** -/
theorem psiPlate_hat_eq_one (k : ℕ) (δ c : ℝ) (hδ : 0 < δ) {ψ : E k → ℂ}
    (hψint : Integrable ψ)
    (hψ : ∀ ξ : E k, (∀ i : Fin k, |ξ i| ≤ 1) → (∫ z, ψ z * chat k (-z) ξ) = 1)
    {ξ : E k} (hξ : ξ ∈ plate k δ c) :
    (∫ y, psiPlate k δ c ψ y * chat k (-y) ξ) = 1 := by
  have hδne : δ ≠ 0 := ne_of_gt hδ
  -- a point `v` of the standard box with `plateMapLin v = ξ - γ(c)`
  obtain ⟨v, hv, hvξ⟩ : ∃ v : E k, (∀ i : Fin k, |v i| ≤ 1)
      ∧ plateMapLin k δ c v = ξ - gammaVec k c := by
    have hmem : ξ - gammaVec k c ∈
        plateMapLin k δ c '' {y : E k | ∀ i : Fin k, |y i| ≤ 1} := by
      rw [plateMapLin_image_box]
      exact ⟨ξ, hξ, by simp⟩
    simpa using hmem
  -- the scalar identity
  have hscalar : ∀ y : E k, chat k y (gammaVec k c) * chat k (-y) ξ
      = chat k (-(plateGaugeLin k δ c y)) v := by
    intro y
    have hinner : ⟪y, -(plateMapLin k δ c v)⟫ = ⟪-(plateGaugeLin k δ c y), v⟫ := by
      rw [inner_neg_right, inner_neg_left, ← real_inner_comm y (plateMapLin k δ c v),
        inner_plateMapLin_plateGaugeLin, ← real_inner_comm v (plateGaugeLin k δ c y)]
    have h1 : gammaVec k c - ξ = -(plateMapLin k δ c v) := by rw [hvξ, neg_sub]
    rw [chat_neg_left k y ξ, ← chat_add]
    show chat k y (gammaVec k c - ξ) = chat k (-(plateGaugeLin k δ c y)) v
    rw [h1, chat, chat, hinner]
  -- the integrand `z ↦ ψ z * chat k (-z) v` is integrable
  have hF : Integrable (fun z : E k => ψ z * chat k (-z) v) := by
    refine hψint.norm.mono' ?_ ?_
    · exact hψint.aestronglyMeasurable.mul
        ((continuous_chat_right k v).comp continuous_neg).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_mul, chat_norm, mul_one]
  have hpt : ∀ y : E k, psiPlate k δ c ψ y * chat k (-y) ξ
      = ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
        * (ψ (plateGaugeLin k δ c y) * chat k (-(plateGaugeLin k δ c y)) v) := by
    intro y
    calc psiPlate k δ c ψ y * chat k (-y) ξ
        = ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
          * (ψ (plateGaugeLin k δ c y) * (chat k y (gammaVec k c) * chat k (-y) ξ)) := by
          rw [psiPlate]; ring
      _ = ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
          * (ψ (plateGaugeLin k δ c y) * chat k (-(plateGaugeLin k δ c y)) v) := by
          rw [hscalar y]
  have hstep : (∫ y, psiPlate k δ c ψ y * chat k (-y) ξ)
      = ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
        * ∫ y, ψ (plateGaugeLin k δ c y) * chat k (-(plateGaugeLin k δ c y)) v := by
    rw [show (fun y : E k => psiPlate k δ c ψ y * chat k (-y) ξ)
        = fun y : E k => ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
          * (ψ (plateGaugeLin k δ c y) * chat k (-(plateGaugeLin k δ c y)) v)
        from funext hpt]
    rw [integral_const_mul]
  have hchange : (∫ y, ψ (plateGaugeLin k δ c y) * chat k (-(plateGaugeLin k δ c y)) v)
      = ((|(LinearMap.det (plateGaugeLin k δ c))⁻¹| : ℝ) : ℂ)
        * ∫ z, ψ z * chat k (-z) v := by
    rw [integral_comp_plateGaugeLin hδne c hF, Complex.real_smul]
  have habs : |LinearMap.det (plateGaugeLin k δ c)|
      * |(LinearMap.det (plateGaugeLin k δ c))⁻¹| = 1 := by
    rw [← abs_mul, mul_inv_cancel₀ (plateGaugeLin_det_ne_zero k hδne c), abs_one]
  have hmul : ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
      * ((|(LinearMap.det (plateGaugeLin k δ c))⁻¹| : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, habs, Complex.ofReal_one]
  rw [hstep, hchange, ← mul_assoc, hmul, one_mul]
  exact hψ v hv

/-- **The gauge bump of a plate.**  For `k ≥ 1` and `A > k` there is a constant `Cg` such
that every plate `plate k δ c` (`0 < δ ≤ 1`) carries a pair `(ψ, φ)` with `ψ̂ ≡ 1` on the
plate, `|ψ| ≤ φ`, and both `∫‖ψ‖` and `∫φ` bounded by `Cg`.  This is the gauge bump of
Guo–Li–Yung–Zorin-Kranich (arXiv:1912.09798) and it is precisely the input of the
uncertainty principle `IsFourierRep.uncertainty`. -/
theorem exists_plate_gauge_bump (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : (k : ℝ) < A) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ δ c : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (ψ : E k → ℂ) (φ : E k → ℝ),
        Integrable ψ ∧ Integrable φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, ‖ψ x‖ ≤ φ x) ∧
        (∫ x, φ x) ≤ Cg ∧ (∫ x, ‖ψ x‖) ≤ Cg ∧
        (∀ ξ ∈ plate k δ c, (∫ y, ψ y * chat k (-y) ξ) = 1) := by
  obtain ⟨C, hC, ψ₀, hψ₀int, hψ₀hat, hψ₀decay, hψ₀L1⟩ := exists_bump_at_one k hk A hA
  have hQint : Integrable (fun z : E k => (max 1 (gauge k hk z)) ^ (-A)) :=
    integrable_gauge_rpow k hk hA
  set Q : ℝ := ∫ z : E k, (max 1 (gauge k hk z)) ^ (-A) with hQ
  have hQnn : 0 ≤ Q := integral_nonneg fun z =>
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  refine ⟨(C + 1) * (1 + Q), by positivity, ?_⟩
  intro δ c hδ hδ1
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hdet := plateGaugeLin_det_ne_zero k hδne c
  have habs : |LinearMap.det (plateGaugeLin k δ c)|
      * |(LinearMap.det (plateGaugeLin k δ c))⁻¹| = 1 := by
    rw [← abs_mul, mul_inv_cancel₀ hdet, abs_one]
  have hBint : Integrable (fun x : E k => ψ₀ (plateGaugeLin k δ c x)) :=
    integrable_comp_plateGaugeLin hδne c hψ₀int
  have hQcomp : Integrable (fun x : E k =>
      (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A)) :=
    integrable_comp_plateGaugeLin hδne c hQint
  refine ⟨psiPlate k δ c ψ₀, phiPlate k hk δ c A C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- integrability of the plate bump
    refine (hBint.norm.const_mul |LinearMap.det (plateGaugeLin k δ c)|).mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun x : E k => ψ₀ (plateGaugeLin k δ c x)) volume :=
        hBint.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun x : E k => chat k x (gammaVec k c)) volume :=
        (continuous_chat_right k (gammaVec k c)).aestronglyMeasurable
      show AEStronglyMeasurable (fun x : E k =>
        ((|LinearMap.det (plateGaugeLin k δ c)| : ℝ) : ℂ)
          * (chat k x (gammaVec k c) * ψ₀ (plateGaugeLin k δ c x))) volume
      exact aestronglyMeasurable_const.mul (h2.mul h1)
    · filter_upwards with x
      rw [norm_psiPlate]
  · -- integrability of the polar bump
    exact hQcomp.const_mul (C * |LinearMap.det (plateGaugeLin k δ c)|)
  · exact fun x => phiPlate_nonneg k hk δ c A C hC.le x
  · -- the pointwise domination `|ψ| ≤ φ`
    intro x
    rw [norm_psiPlate, phiPlate]
    calc |LinearMap.det (plateGaugeLin k δ c)| * ‖ψ₀ (plateGaugeLin k δ c x)‖
        ≤ |LinearMap.det (plateGaugeLin k δ c)|
            * (C * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A)) :=
          mul_le_mul_of_nonneg_left (hψ₀decay (plateGaugeLin k δ c x)) (abs_nonneg _)
      _ = C * |LinearMap.det (plateGaugeLin k δ c)|
            * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A) := by ring
  · -- `∫ φ ≤ Cg`
    have hint : (∫ x, (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A))
        = |(LinearMap.det (plateGaugeLin k δ c))⁻¹| * Q := by
      rw [integral_comp_plateGaugeLin hδne c hQint, smul_eq_mul,
        show (∫ y : E k, (max 1 (gauge k hk y)) ^ (-A)) = Q from hQ.symm]
    have hCQ : C * |LinearMap.det (plateGaugeLin k δ c)|
        * (|(LinearMap.det (plateGaugeLin k δ c))⁻¹| * Q) = C * Q := by
      calc C * |LinearMap.det (plateGaugeLin k δ c)|
            * (|(LinearMap.det (plateGaugeLin k δ c))⁻¹| * Q)
          = C * ((|LinearMap.det (plateGaugeLin k δ c)|
              * |(LinearMap.det (plateGaugeLin k δ c))⁻¹|) * Q) := by ring
        _ = C * Q := by rw [habs, one_mul]
    have hphi : (∫ x, phiPlate k hk δ c A C x) = C * Q := by
      simp only [phiPlate]
      rw [integral_const_mul, hint, hCQ]
    rw [hphi]
    nlinarith [hC, hQnn]
  · -- `∫ ‖ψ‖ ≤ Cg`
    have hchange : (∫ x, ‖ψ₀ (plateGaugeLin k δ c x)‖)
        = |(LinearMap.det (plateGaugeLin k δ c))⁻¹| * ∫ z, ‖ψ₀ z‖ := by
      rw [integral_comp_plateGaugeLin hδne c hψ₀int.norm, smul_eq_mul]
    have hstep : (∫ x, ‖psiPlate k δ c ψ₀ x‖)
        = |LinearMap.det (plateGaugeLin k δ c)|
          * (|(LinearMap.det (plateGaugeLin k δ c))⁻¹| * ∫ z, ‖ψ₀ z‖) := by
      rw [show (∫ x, ‖psiPlate k δ c ψ₀ x‖)
          = ∫ x, |LinearMap.det (plateGaugeLin k δ c)| * ‖ψ₀ (plateGaugeLin k δ c x)‖ from
        integral_congr_ae (Filter.Eventually.of_forall fun x => norm_psiPlate k δ c ψ₀ x)]
      rw [integral_const_mul, hchange]
    rw [hstep,
      show |LinearMap.det (plateGaugeLin k δ c)|
          * (|(LinearMap.det (plateGaugeLin k δ c))⁻¹| * ∫ z, ‖ψ₀ z‖) = ∫ z, ‖ψ₀ z‖ from by
        rw [← mul_assoc, habs, one_mul]]
    exact hψ₀L1.trans (by nlinarith [hC, hQnn])
  · exact fun ξ hξ => psiPlate_hat_eq_one k δ c hδ hψ₀int hψ₀hat hξ


end Submission.Vinogradov
