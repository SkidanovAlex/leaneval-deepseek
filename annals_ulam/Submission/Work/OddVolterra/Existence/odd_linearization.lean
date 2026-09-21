import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.Geometry.Ulam.AbelBeta
import Submission.Work.OddVolterra.Existence.diag_K1_explicit
import Submission.Work.OddVolterra.Existence.Godd_zero_diag
import Submission.Work.OddVolterra.Existence.diag_K2_explicit

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam

noncomputable section

/-! ## The diagonal data of the unperturbed odd Volterra map

At `h = 0` and `σ = s` the map `Godd` is (see `Godd_zero_diag`)

`Godd n 0 s z = ![z 0, z 1, I (K₁(s,s,-z 0) z 2 + K₁(s,s,z 1) z 3), I (K₂(s,s,-z 0) z 2 + K₂(s,s,z 1) z 3)]`

with `I = ∫₀¹ dτ/√(τ(1-τ)) = π` the Abel weight mass, and the diagonal kernels are the
explicit `K₁(s,s,t) = C₁(s) |t|^{2n+1}`, `K₂(s,s,t) = C₂(s) t |t|^{2n-1}`.
Hence the `fderiv` in `z` at the base state `(p,p,q,q)`, `p = profileX s`, `q = (profileX)' s`,
is the explicit block-triangular map with rows

`[1,0,0,0]`, `[0,1,0,0]`, `[α,α,a,a]`, `[γ,-γ,c,-c]`,

whose `2×2` block `[[a,a],[c,-c]]` has determinant `-2ac ≠ 0`; this file builds that
linearization as a `≃L[ℝ]`, shows it is the derivative, and bounds its inverse. -/

/-- The Abel weight mass `∫₀¹ dτ / √(τ(1-τ))`, equal to `π`. -/
def abelMass : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹

lemma abelMass_eq_pi : abelMass = Real.pi := by
  have h : (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹)
      = fun τ : ℝ => 1 / Real.sqrt (τ * ((1 : ℝ) - τ)) := by
    funext τ
    rw [one_div]
  rw [abelMass, h, integral_one_div_sqrt_tau_one_sub_tau_eq_pi]

lemma abelMass_pos : 0 < abelMass := by
  rw [abelMass_eq_pi]; exact Real.pi_pos

lemma abelMass_ne_zero : abelMass ≠ 0 := ne_of_gt abelMass_pos

/-- The `s`-dependent constant of `K₁(s,s,t) = C₁(s)|t|^{2n+1}`. -/
def diagC1 (n : ℕ) (s : ℝ) : ℝ :=
  ((Nat.doubleFactorial (2 * n + 1) : ℝ)) * (-s) ^ (n + 1) / Real.sqrt (2 * s)

/-- The `s`-dependent constant of `K₂(s,s,t) = C₂(s) t |t|^{2n-1}`. -/
def diagC2 (n : ℕ) (s : ℝ) : ℝ :=
  ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-s) ^ n / Real.sqrt (2 * s)

/-- The `(2,2)` and `(2,3)` entries of the diagonal linearization. -/
def linA (n : ℕ) (s : ℝ) : ℝ := abelMass * diagC1 n s * (profileX s) ^ (2 * n + 1)

/-- The `(3,2)` entry of the diagonal linearization (the `(3,3)` entry is its negative). -/
def linC (n : ℕ) (s : ℝ) : ℝ := -(abelMass * diagC2 n s * (profileX s) ^ (2 * n))

/-- The `(2,0)` and `(2,1)` entries of the diagonal linearization. -/
def linAA (n : ℕ) (s : ℝ) : ℝ :=
  abelMass * diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n)) * deriv profileX s

/-- The `(3,0)` entry of the diagonal linearization (the `(3,1)` entry is its negative). -/
def linGG (n : ℕ) (s : ℝ) : ℝ :=
  -(abelMass * (((2 * n : ℕ) : ℝ) * diagC2 n s) * (profileX s) ^ (2 * n - 1) * deriv profileX s)

lemma continuous_profileX : Continuous profileX :=
  RyaboginVolterra.contDiff_profileX.continuous

lemma continuous_deriv_profileX : Continuous (deriv profileX) :=
  RyaboginVolterra.contDiff_profileX.continuous_deriv (WithTop.coe_le_coe.mpr le_top)

/-- The square-root factor `s ↦ √(2s)` is nonvanishing on `[a,b]` for `0 < a`. -/
lemma sqrt_two_mul_ne_zero {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Icc a b) :
    Real.sqrt (2 * s) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (by linarith [hs.1, ha]))

lemma continuousOn_sqrt_two_mul {a b : ℝ} :
    ContinuousOn (fun s : ℝ => Real.sqrt (2 * s)) (Set.Icc a b) :=
  (Real.continuous_sqrt.comp (by fun_prop : Continuous fun s : ℝ => 2 * s)).continuousOn

lemma continuousOn_diagC1 (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => diagC1 n s) (Set.Icc a b) := by
  show ContinuousOn
    (fun s : ℝ => ((Nat.doubleFactorial (2 * n + 1) : ℝ)) * (-s) ^ (n + 1)
      / Real.sqrt (2 * s)) (Set.Icc a b)
  exact ContinuousOn.div (by fun_prop) (continuousOn_sqrt_two_mul (a := a) (b := b))
    (fun s hs => sqrt_two_mul_ne_zero ha hs)

lemma continuousOn_diagC2 (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => diagC2 n s) (Set.Icc a b) := by
  show ContinuousOn
    (fun s : ℝ => ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-s) ^ n
      / Real.sqrt (2 * s)) (Set.Icc a b)
  exact ContinuousOn.div (by fun_prop) (continuousOn_sqrt_two_mul (a := a) (b := b))
    (fun s hs => sqrt_two_mul_ne_zero ha hs)

lemma continuousOn_linA (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => linA n s) (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ => abelMass * diagC1 n s * (profileX s) ^ (2 * n + 1))
    (Set.Icc a b)
  exact (continuousOn_const.mul (continuousOn_diagC1 n ha)).mul
    (continuous_profileX.continuousOn.pow (2 * n + 1))

lemma continuousOn_linC (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => linC n s) (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ => -(abelMass * diagC2 n s * (profileX s) ^ (2 * n)))
    (Set.Icc a b)
  exact ((continuousOn_const.mul (continuousOn_diagC2 n ha)).mul
    (continuous_profileX.continuousOn.pow (2 * n))).neg

lemma continuousOn_linAA (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => linAA n s) (Set.Icc a b) := by
  show ContinuousOn
    (fun s : ℝ => abelMass * diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n))
      * deriv profileX s) (Set.Icc a b)
  exact ((continuousOn_const.mul (continuousOn_diagC1 n ha)).mul
    (continuousOn_const.mul (continuous_profileX.continuousOn.pow (2 * n)))).mul
    continuous_deriv_profileX.continuousOn

lemma continuousOn_linGG (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => linGG n s) (Set.Icc a b) := by
  show ContinuousOn
    (fun s : ℝ => -(abelMass * (((2 * n : ℕ) : ℝ) * diagC2 n s) * (profileX s) ^ (2 * n - 1)
      * deriv profileX s)) (Set.Icc a b)
  exact (((continuousOn_const.mul (continuousOn_const.mul (continuousOn_diagC2 n ha))).mul
    (continuous_profileX.continuousOn.pow (2 * n - 1))).mul
    continuous_deriv_profileX.continuousOn).neg

lemma profileX_pos_of_mem {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Icc a b) :
    0 < profileX s := profileX_pos s (by linarith [hs.1, ha])

lemma diagC1_ne_zero {n : ℕ} {s : ℝ} (hs : 0 < s) : diagC1 n s ≠ 0 := by
  unfold diagC1
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne')
      (pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hs)))
  · exact ne_of_gt (Real.sqrt_pos.2 (by linarith))

lemma diagC2_ne_zero {n : ℕ} {s : ℝ} (hs : 0 < s) : diagC2 n s ≠ 0 := by
  unfold diagC2
  refine div_ne_zero ?_ ?_
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne')
      (pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hs)))
  · exact ne_of_gt (Real.sqrt_pos.2 (by linarith))

lemma linA_ne_zero (n : ℕ) {s : ℝ} (hs : 0 < s) : linA n s ≠ 0 := by
  unfold linA
  exact mul_ne_zero (mul_ne_zero abelMass_ne_zero (diagC1_ne_zero hs))
    (pow_ne_zero _ (ne_of_gt (profileX_pos s hs)))

lemma linC_ne_zero (n : ℕ) {s : ℝ} (hs : 0 < s) : linC n s ≠ 0 := by
  unfold linC
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero abelMass_ne_zero (diagC2_ne_zero hs))
    (pow_ne_zero _ (ne_of_gt (profileX_pos s hs))))

/-! ## The two linear maps -/

/-- The rows of the diagonal derivative. -/
def phiRows (n : ℕ) (s : ℝ) : Fin 4 → St →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj (0 : Fin 4), ContinuousLinearMap.proj (1 : Fin 4),
    linAA n s • ContinuousLinearMap.proj (0 : Fin 4)
      + linAA n s • ContinuousLinearMap.proj (1 : Fin 4)
      + linA n s • ContinuousLinearMap.proj (2 : Fin 4)
      + linA n s • ContinuousLinearMap.proj (3 : Fin 4),
    linGG n s • ContinuousLinearMap.proj (0 : Fin 4)
      - linGG n s • ContinuousLinearMap.proj (1 : Fin 4)
      + linC n s • ContinuousLinearMap.proj (2 : Fin 4)
      - linC n s • ContinuousLinearMap.proj (3 : Fin 4)]

/-- The candidate for `fderiv ℝ (Godd n 0 s ·) (baseState s)`. -/
def PhiCLM (n : ℕ) (s : ℝ) : St →L[ℝ] St := ContinuousLinearMap.pi (phiRows n s)

lemma PhiCLM_coord_zero (n : ℕ) (s : ℝ) (z : St) : (PhiCLM n s z) 0 = z 0 := by
  simp [PhiCLM, phiRows, ContinuousLinearMap.pi_apply]

lemma PhiCLM_coord_one (n : ℕ) (s : ℝ) (z : St) : (PhiCLM n s z) 1 = z 1 := by
  simp [PhiCLM, phiRows, ContinuousLinearMap.pi_apply]

lemma PhiCLM_coord_two (n : ℕ) (s : ℝ) (z : St) :
    (PhiCLM n s z) 2 = linAA n s * z 0 + linAA n s * z 1 + linA n s * z 2 + linA n s * z 3 := by
  simp [PhiCLM, phiRows, ContinuousLinearMap.pi_apply]

lemma PhiCLM_coord_three (n : ℕ) (s : ℝ) (z : St) :
    (PhiCLM n s z) 3 = linGG n s * z 0 - linGG n s * z 1 + linC n s * z 2 - linC n s * z 3 := by
  simp [PhiCLM, phiRows, ContinuousLinearMap.pi_apply]

/-- The scalar coefficient `u` of the inverse matrix. -/
def invU (n : ℕ) (s : ℝ) : ℝ := linAA n s / (2 * linA n s) + linGG n s / (2 * linC n s)

/-- The scalar coefficient `v` of the inverse matrix. -/
def invV (n : ℕ) (s : ℝ) : ℝ := linAA n s / (2 * linA n s) - linGG n s / (2 * linC n s)

/-- The rows of the candidate inverse. -/
def psiRows (n : ℕ) (s : ℝ) : Fin 4 → St →L[ℝ] ℝ :=
  ![ContinuousLinearMap.proj (0 : Fin 4), ContinuousLinearMap.proj (1 : Fin 4),
    - (invU n s) • ContinuousLinearMap.proj (0 : Fin 4)
      - (invV n s) • ContinuousLinearMap.proj (1 : Fin 4)
      + (2 * linA n s)⁻¹ • ContinuousLinearMap.proj (2 : Fin 4)
      + (2 * linC n s)⁻¹ • ContinuousLinearMap.proj (3 : Fin 4),
    - (invV n s) • ContinuousLinearMap.proj (0 : Fin 4)
      - (invU n s) • ContinuousLinearMap.proj (1 : Fin 4)
      + (2 * linA n s)⁻¹ • ContinuousLinearMap.proj (2 : Fin 4)
      - (2 * linC n s)⁻¹ • ContinuousLinearMap.proj (3 : Fin 4)]

/-- The candidate inverse of `PhiCLM n s`. -/
def PsiCLM (n : ℕ) (s : ℝ) : St →L[ℝ] St := ContinuousLinearMap.pi (psiRows n s)

lemma PsiCLM_apply (n : ℕ) (s : ℝ) (w : St) :
    PsiCLM n s w = ![w 0, w 1,
      - (linAA n s / (2 * linA n s) + linGG n s / (2 * linC n s)) * w 0
        - (linAA n s / (2 * linA n s) - linGG n s / (2 * linC n s)) * w 1
        + w 2 / (2 * linA n s) + w 3 / (2 * linC n s),
      - (linAA n s / (2 * linA n s) - linGG n s / (2 * linC n s)) * w 0
        - (linAA n s / (2 * linA n s) + linGG n s / (2 * linC n s)) * w 1
        + w 2 / (2 * linA n s) - w 3 / (2 * linC n s)] := by
  funext i
  fin_cases i <;>
    simp [PsiCLM, psiRows, ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, invU, invV,
      div_eq_mul_inv] <;>
    ring

lemma PsiCLM_coord_zero (n : ℕ) (s : ℝ) (w : St) : (PsiCLM n s w) 0 = w 0 := by
  simp [PsiCLM, psiRows, ContinuousLinearMap.pi_apply]

lemma PsiCLM_coord_one (n : ℕ) (s : ℝ) (w : St) : (PsiCLM n s w) 1 = w 1 := by
  simp [PsiCLM, psiRows, ContinuousLinearMap.pi_apply]

lemma PsiCLM_coord_two (n : ℕ) (s : ℝ) (w : St) :
    (PsiCLM n s w) 2 = - (invU n s) * w 0 - (invV n s) * w 1
      + w 2 / (2 * linA n s) + w 3 / (2 * linC n s) := by
  simp [PsiCLM, psiRows, ContinuousLinearMap.pi_apply, div_eq_mul_inv]
  ring

lemma PsiCLM_coord_three (n : ℕ) (s : ℝ) (w : St) :
    (PsiCLM n s w) 3 = - (invV n s) * w 0 - (invU n s) * w 1
      + w 2 / (2 * linA n s) - w 3 / (2 * linC n s) := by
  simp [PsiCLM, psiRows, ContinuousLinearMap.pi_apply, div_eq_mul_inv]
  ring


/-! ## The two maps are mutually inverse -/

lemma PsiCLM_PhiCLM_coord_two (n : ℕ) (s : ℝ) (hA : linA n s ≠ 0) (hC : linC n s ≠ 0)
    (z : St) : (PsiCLM n s (PhiCLM n s z)) 2 = z 2 := by
  rw [PsiCLM_coord_two, PhiCLM_coord_zero, PhiCLM_coord_one, PhiCLM_coord_two,
    PhiCLM_coord_three]
  simp only [invU, invV, div_eq_mul_inv]
  field_simp [hA, hC]
  ring

lemma PsiCLM_PhiCLM_coord_three (n : ℕ) (s : ℝ) (hA : linA n s ≠ 0) (hC : linC n s ≠ 0)
    (z : St) : (PsiCLM n s (PhiCLM n s z)) 3 = z 3 := by
  rw [PsiCLM_coord_three, PhiCLM_coord_zero, PhiCLM_coord_one, PhiCLM_coord_two,
    PhiCLM_coord_three]
  simp only [invU, invV, div_eq_mul_inv]
  field_simp [hA, hC]
  ring

lemma PhiCLM_PsiCLM_coord_two (n : ℕ) (s : ℝ) (hA : linA n s ≠ 0) (hC : linC n s ≠ 0)
    (w : St) : (PhiCLM n s (PsiCLM n s w)) 2 = w 2 := by
  rw [PhiCLM_coord_two, PsiCLM_coord_zero, PsiCLM_coord_one, PsiCLM_coord_two,
    PsiCLM_coord_three]
  simp only [invU, invV, div_eq_mul_inv]
  field_simp [hA, hC]
  ring

lemma PhiCLM_PsiCLM_coord_three (n : ℕ) (s : ℝ) (hA : linA n s ≠ 0) (hC : linC n s ≠ 0)
    (w : St) : (PhiCLM n s (PsiCLM n s w)) 3 = w 3 := by
  rw [PhiCLM_coord_three, PsiCLM_coord_zero, PsiCLM_coord_one, PsiCLM_coord_two,
    PsiCLM_coord_three]
  simp only [invU, invV, div_eq_mul_inv]
  field_simp [hA, hC]
  ring

lemma PsiCLM_leftInverse (n : ℕ) (s : ℝ) (hA : linA n s ≠ 0) (hC : linC n s ≠ 0) :
    Function.LeftInverse (fun w : St => PsiCLM n s w) (fun z : St => PhiCLM n s z) := by
  intro z
  funext i
  fin_cases i
  · exact PsiCLM_coord_zero n s (PhiCLM n s z) |>.trans (PhiCLM_coord_zero n s z)
  · exact PsiCLM_coord_one n s (PhiCLM n s z) |>.trans (PhiCLM_coord_one n s z)
  · exact PsiCLM_PhiCLM_coord_two n s hA hC z
  · exact PsiCLM_PhiCLM_coord_three n s hA hC z

lemma PsiCLM_rightInverse (n : ℕ) (s : ℝ) (hA : linA n s ≠ 0) (hC : linC n s ≠ 0) :
    Function.RightInverse (fun w : St => PsiCLM n s w) (fun z : St => PhiCLM n s z) := by
  intro w
  funext i
  fin_cases i
  · exact PhiCLM_coord_zero n s (PsiCLM n s w) |>.trans (PsiCLM_coord_zero n s w)
  · exact PhiCLM_coord_one n s (PsiCLM n s w) |>.trans (PsiCLM_coord_one n s w)
  · exact PhiCLM_PsiCLM_coord_two n s hA hC w
  · exact PhiCLM_PsiCLM_coord_three n s hA hC w

/-! ## Continuity of the inverse family -/

lemma continuousOn_inv_two_linA (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => (2 * linA n s)⁻¹) (Set.Icc a b) :=
  ContinuousOn.inv₀ (continuousOn_const.mul (continuousOn_linA n ha))
    (fun s hs => mul_ne_zero two_ne_zero (linA_ne_zero n (by linarith [ha, hs.1])))

lemma continuousOn_inv_two_linC (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => (2 * linC n s)⁻¹) (Set.Icc a b) :=
  ContinuousOn.inv₀ (continuousOn_const.mul (continuousOn_linC n ha))
    (fun s hs => mul_ne_zero two_ne_zero (linC_ne_zero n (by linarith [ha, hs.1])))

lemma continuousOn_invU (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => invU n s) (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ => linAA n s / (2 * linA n s) + linGG n s / (2 * linC n s))
    (Set.Icc a b)
  exact (ContinuousOn.div (continuousOn_linAA n ha)
      (continuousOn_const.mul (continuousOn_linA n ha))
      (fun s hs => mul_ne_zero two_ne_zero (linA_ne_zero n (by linarith [ha, hs.1])))).add
    (ContinuousOn.div (continuousOn_linGG n ha)
      (continuousOn_const.mul (continuousOn_linC n ha))
      (fun s hs => mul_ne_zero two_ne_zero (linC_ne_zero n (by linarith [ha, hs.1]))))

lemma continuousOn_invV (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => invV n s) (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ => linAA n s / (2 * linA n s) - linGG n s / (2 * linC n s))
    (Set.Icc a b)
  exact (ContinuousOn.div (continuousOn_linAA n ha)
      (continuousOn_const.mul (continuousOn_linA n ha))
      (fun s hs => mul_ne_zero two_ne_zero (linA_ne_zero n (by linarith [ha, hs.1])))).sub
    (ContinuousOn.div (continuousOn_linGG n ha)
      (continuousOn_const.mul (continuousOn_linC n ha))
      (fun s hs => mul_ne_zero two_ne_zero (linC_ne_zero n (by linarith [ha, hs.1]))))

lemma continuousOn_smul_proj_const {c : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn c (Set.Icc a b))
    (i : Fin 4) :
    ContinuousOn (fun s : ℝ => c s • (ContinuousLinearMap.proj i : St →L[ℝ] ℝ))
      (Set.Icc a b) :=
  hc.smul continuousOn_const

lemma continuousOn_psiRows_two (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => psiRows n s 2) (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ =>
      - (invU n s) • (ContinuousLinearMap.proj (0 : Fin 4) : St →L[ℝ] ℝ)
      - (invV n s) • (ContinuousLinearMap.proj (1 : Fin 4) : St →L[ℝ] ℝ)
      + (2 * linA n s)⁻¹ • (ContinuousLinearMap.proj (2 : Fin 4) : St →L[ℝ] ℝ)
      + (2 * linC n s)⁻¹ • (ContinuousLinearMap.proj (3 : Fin 4) : St →L[ℝ] ℝ))
    (Set.Icc a b)
  exact (((continuousOn_smul_proj_const (continuousOn_invU n ha).neg 0).sub
    (continuousOn_smul_proj_const (continuousOn_invV n ha) 1)).add
    (continuousOn_smul_proj_const (continuousOn_inv_two_linA n ha) 2)).add
    (continuousOn_smul_proj_const (continuousOn_inv_two_linC n ha) 3)

lemma continuousOn_psiRows_three (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => psiRows n s 3) (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ =>
      - (invV n s) • (ContinuousLinearMap.proj (0 : Fin 4) : St →L[ℝ] ℝ)
      - (invU n s) • (ContinuousLinearMap.proj (1 : Fin 4) : St →L[ℝ] ℝ)
      + (2 * linA n s)⁻¹ • (ContinuousLinearMap.proj (2 : Fin 4) : St →L[ℝ] ℝ)
      - (2 * linC n s)⁻¹ • (ContinuousLinearMap.proj (3 : Fin 4) : St →L[ℝ] ℝ))
    (Set.Icc a b)
  exact (((continuousOn_smul_proj_const (continuousOn_invV n ha).neg 0).sub
    (continuousOn_smul_proj_const (continuousOn_invU n ha) 1)).add
    (continuousOn_smul_proj_const (continuousOn_inv_two_linA n ha) 2)).sub
    (continuousOn_smul_proj_const (continuousOn_inv_two_linC n ha) 3)

lemma continuousOn_psiRows (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => psiRows n s) (Set.Icc a b) := by
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · exact continuousOn_const
  · exact continuousOn_const
  · exact continuousOn_psiRows_two n ha
  · exact continuousOn_psiRows_three n ha

lemma continuousOn_PsiCLM (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => PsiCLM n s) (Set.Icc a b) := by
  have hrows := continuousOn_psiRows (n := n) (a := a) (b := b) ha
  have hcomp := (ContinuousLinearMap.piEquivL ℝ St (fun _ : Fin 4 => ℝ)).continuous.comp_continuousOn
    hrows
  simpa [PsiCLM, ContinuousLinearMap.piEquivL_apply, Function.comp_def] using hcomp

/-! ## The diagonal derivatives of `K₁`, `K₂` and of `Godd` -/

lemma diag_K1_hasDerivAt_pos (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => K1 n (fun _ : ℝ => 0) s s u)
      (diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n))) t := by
  have h2s : 0 < 2 * s := by linarith
  have hev : (fun u : ℝ => K1 n (fun _ : ℝ => 0) s s u)
      =ᶠ[𝓝 t] (fun u : ℝ => diagC1 n s * u ^ (2 * n + 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    rw [diag_K1_explicit n hs u, abs_of_pos hu]
    unfold diagC1
    rw [div_mul_eq_mul_div]
  rw [hev.hasDerivAt_iff]
  simpa using (hasDerivAt_pow (2 * n + 1) t).const_mul (diagC1 n s)

lemma diag_K1_hasDerivAt_neg (n : ℕ) {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    HasDerivAt (fun u : ℝ => K1 n (fun _ : ℝ => 0) s s u)
      (-(diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (-t) ^ (2 * n)))) t := by
  have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
  have hev : (fun u : ℝ => K1 n (fun _ : ℝ => 0) s s u)
      =ᶠ[𝓝 t] (fun u : ℝ => diagC1 n s * (-u) ^ (2 * n + 1)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
    rw [diag_K1_explicit n hs u, abs_of_neg hu]
    unfold diagC1
    rw [div_mul_eq_mul_div]
  rw [hev.hasDerivAt_iff]
  have hfun : (fun u : ℝ => diagC1 n s * (-u) ^ (2 * n + 1))
      = fun u : ℝ => (-(diagC1 n s)) * u ^ (2 * n + 1) := by
    funext u
    rw [hodd.neg_pow]
    ring
  rw [hfun]
  have h := (hasDerivAt_pow (2 * n + 1) t).const_mul (-(diagC1 n s))
  refine HasDerivAt.congr_deriv h ?_
  rw [Even.neg_pow ⟨n, by ring⟩, Nat.add_sub_cancel]
  ring

lemma diag_K2_hasDerivAt_pos (n : ℕ) (hn : 1 ≤ n) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => K2 n (fun _ : ℝ => 0) s s u)
      (diagC2 n s * (((2 * n : ℕ) : ℝ) * t ^ (2 * n - 1))) t := by
  have hpow : ∀ u : ℝ, u * u ^ (2 * n - 1) = u ^ (2 * n) := by
    intro u
    conv_lhs => rw [← pow_succ']
    rw [show 2 * n - 1 + 1 = 2 * n by omega]
  have hev : (fun u : ℝ => K2 n (fun _ : ℝ => 0) s s u)
      =ᶠ[𝓝 t] (fun u : ℝ => diagC2 n s * u ^ (2 * n)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    rw [diag_K2_explicit n hn hs u, abs_of_pos hu, ← hpow u]
    unfold diagC2
    rw [div_mul_eq_mul_div]
  rw [hev.hasDerivAt_iff]
  exact (hasDerivAt_pow (2 * n) t).const_mul (diagC2 n s)

lemma diag_K2_hasDerivAt_neg (n : ℕ) (hn : 1 ≤ n) {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    HasDerivAt (fun u : ℝ => K2 n (fun _ : ℝ => 0) s s u)
      (diagC2 n s * (((2 * n : ℕ) : ℝ) * (-t) ^ (2 * n - 1))) t := by
  have hodd : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  have hpowpos : ∀ u : ℝ, u * u ^ (2 * n - 1) = u ^ (2 * n) := by
    intro u
    conv_lhs => rw [← pow_succ']
    rw [show 2 * n - 1 + 1 = 2 * n by omega]
  have hpow : ∀ u : ℝ, u * (-u) ^ (2 * n - 1) = -(u ^ (2 * n)) := by
    intro u
    have h1 : u * (-u) ^ (2 * n - 1) = -(u * u ^ (2 * n - 1)) := by
      rw [hodd.neg_pow]; ring
    rw [h1, hpowpos u]
  have hev : (fun u : ℝ => K2 n (fun _ : ℝ => 0) s s u)
      =ᶠ[𝓝 t] (fun u : ℝ => diagC2 n s * (-(u ^ (2 * n)))) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
    rw [diag_K2_explicit n hn hs u, abs_of_neg hu, ← hpow u]
    unfold diagC2
    rw [div_mul_eq_mul_div]
  rw [hev.hasDerivAt_iff]
  have hfun : (fun u : ℝ => diagC2 n s * (-(u ^ (2 * n))))
      = fun u : ℝ => diagC2 n s * ((-1 : ℝ) * u ^ (2 * n)) := by
    funext u; ring
  rw [hfun]
  have h := (hasDerivAt_pow (2 * n) t).const_mul (-1)
  have h2 := h.const_mul (diagC2 n s)
  refine HasDerivAt.congr_deriv h2 ?_
  rw [hodd.neg_pow]
  ring

/-! ## The `z`-derivative of `Godd` at the base state -/

/-- The second row of `Godd n 0 s` at `σ = s`. -/
def GoddRow2 (n : ℕ) (s : ℝ) : St → ℝ :=
  fun z => abelMass * (K1 n (fun _ : ℝ => 0) s s (-(z 0)) * z 2
    + K1 n (fun _ : ℝ => 0) s s (z 1) * z 3)

/-- The third row of `Godd n 0 s` at `σ = s`. -/
def GoddRow3 (n : ℕ) (s : ℝ) : St → ℝ :=
  fun z => abelMass * (K2 n (fun _ : ℝ => 0) s s (-(z 0)) * z 2
    + K2 n (fun _ : ℝ => 0) s s (z 1) * z 3)

lemma Godd_coord_zero (n : ℕ) (s : ℝ) (z : St) : (Godd n 0 s z) 0 = z 0 := by
  rw [Godd_zero_diag]
  simp

lemma Godd_coord_one (n : ℕ) (s : ℝ) (z : St) : (Godd n 0 s z) 1 = z 1 := by
  rw [Godd_zero_diag]
  simp

lemma Godd_coord_two (n : ℕ) (s : ℝ) (z : St) : (Godd n 0 s z) 2 = GoddRow2 n s z := by
  rw [Godd_zero_diag]
  rfl

lemma Godd_coord_three (n : ℕ) (s : ℝ) (z : St) : (Godd n 0 s z) 3 = GoddRow3 n s z := by
  rw [Godd_zero_diag]
  rfl

/-- The `j`-th coordinate functional on `St`. -/
def coord (j : Fin 4) : St →L[ℝ] ℝ where
  toFun := fun z => z j
  map_add' := fun x y => rfl
  map_smul' := fun c x => rfl

@[simp] lemma coord_apply (j : Fin 4) (z : St) : coord j z = z j := rfl

def negCoord (j : Fin 4) : St →L[ℝ] ℝ where
  toFun := fun z => -(z j)
  map_add' := by intro x y; simp [add_comm]
  map_smul' := by intro c x; simp

@[simp] lemma negCoord_apply (j : Fin 4) (z : St) : negCoord j z = -(z j) := rfl

lemma negCoord_eq (j : Fin 4) :
    (negCoord j : St →L[ℝ] ℝ) = -(ContinuousLinearMap.proj j : St →L[ℝ] ℝ) := by
  ext z
  simp [ContinuousLinearMap.proj_apply]

lemma hasFDerivAt_coord {j : Fin 4} {x : St} :
    HasFDerivAt (fun z : St => z j) (coord j) x := by
  convert (coord j).hasFDerivAt (x := x) using 1
  funext z; rfl

lemma hasFDerivAt_negCoord {j : Fin 4} {x : St} :
    HasFDerivAt (fun z : St => -(z j)) (negCoord j) x := by
  convert (negCoord j).hasFDerivAt (x := x) using 1
  funext z; rfl

lemma toSpanSingleton_comp_coord {c : ℝ} {j : Fin 4} :
    (ContinuousLinearMap.toSpanSingleton ℝ c).comp (coord j) = c • (coord j) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, coord_apply, smul_eq_mul]
  ring

lemma toSpanSingleton_comp_negCoord {c : ℝ} {j : Fin 4} :
    (ContinuousLinearMap.toSpanSingleton ℝ c).comp (negCoord j) = c • (negCoord j) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, negCoord_apply, smul_eq_mul]
  ring

lemma comp_coord_hasFDerivAt {f : ℝ → ℝ} {f' : ℝ} {j : Fin 4} {x : St}
    (hf : HasDerivAt f f' (x j)) :
    HasFDerivAt (fun z : St => f (z j)) (f' • (coord j)) x := by
  have h := hf.hasFDerivAt.comp x (hasFDerivAt_coord (j := j) (x := x))
  rw [toSpanSingleton_comp_coord] at h
  convert h using 1
  all_goals first | rfl | (funext z; rfl)

lemma comp_neg_coord_hasFDerivAt {f : ℝ → ℝ} {f' : ℝ} {j : Fin 4} {x : St}
    (hf : HasDerivAt f f' (-(x j))) :
    HasFDerivAt (fun z : St => f (-(z j))) ((-f') • (coord j)) x := by
  have h := hf.hasFDerivAt.comp x (hasFDerivAt_negCoord (j := j) (x := x))
  rw [toSpanSingleton_comp_negCoord, negCoord_eq, smul_neg, ← neg_smul] at h
  convert h using 1
  all_goals first | rfl | (funext z; rfl)

lemma mul_coord_hasFDerivAt {f : St → ℝ} {f' : St →L[ℝ] ℝ} {j : Fin 4} {x : St}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun z : St => f z * z j) (f x • (coord j) + x j • f') x := by
  have h : HasFDerivAt (fun z : St => f z * z j) (f x • (coord j) + x j • f') x :=
    hf.mul (hasFDerivAt_coord (j := j) (x := x))
  convert h using 1
  all_goals first | rfl | (funext z; rfl)

lemma pow_two_mul_eq_mul (x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    x ^ (2 * n) = x * x ^ (2 * n - 1) := by
  conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 by omega, pow_succ']

lemma diag_K2_explicit_pos (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 < t) :
    K2 n (fun _ : ℝ => 0) s s t =
      ((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-s) ^ n * t ^ (2 * n) / Real.sqrt (2 * s) := by
  have h := diag_K2_explicit n hn hs t
  rw [abs_of_pos ht] at h
  rw [h, pow_two_mul_eq_mul t hn]

lemma diag_K2_explicit_neg (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : t < 0) :
    K2 n (fun _ : ℝ => 0) s s t =
      -(((Nat.doubleFactorial (2 * n - 1) : ℝ)) * (-s) ^ n * (-t) ^ (2 * n) / Real.sqrt (2 * s)) := by
  have h := diag_K2_explicit n hn hs t
  rw [abs_of_neg ht] at h
  have h2 : t * (-t) ^ (2 * n - 1) = -((-t) ^ (2 * n)) := by
    have h3 : (-t) ^ (2 * n) = (-t) * (-t) ^ (2 * n - 1) := pow_two_mul_eq_mul (-t) hn
    rw [h3]; ring
  rw [h, h2]
  ring

lemma row2_clm (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    abelMass • (K1 n (fun _ : ℝ => 0) s s (-(baseState s 0)) • (coord 2)
        + (baseState s 2)
            • ((diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n))) • (coord 0))
        + (K1 n (fun _ : ℝ => 0) s s (baseState s 1) • (coord 3)
          + (baseState s 3)
              • ((diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n))) • (coord 1))))
      = linAA n s • (coord 0) + linAA n s • (coord 1) + linA n s • (coord 2) + linA n s • (coord 3) := by
  have hb0 : baseState s 0 = profileX s := rfl
  have hb1 : baseState s 1 = profileX s := rfl
  have hb2 : baseState s 2 = deriv profileX s := rfl
  have hb3 : baseState s 3 = deriv profileX s := rfl
  ext z
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, coord_apply, hb0, hb1, hb2, hb3]
  rw [diag_K1_explicit n hs (-(profileX s)), diag_K1_explicit n hs (profileX s),
    abs_neg, abs_of_pos (profileX_pos s hs)]
  unfold linAA linA diagC1
  ring

lemma row3_clm (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    abelMass • (K2 n (fun _ : ℝ => 0) s s (-(baseState s 0)) • (coord 2)
        + (baseState s 2)
            • ((-(diagC2 n s * (((2 * n : ℕ) : ℝ) * (profileX s) ^ (2 * n - 1)))) • (coord 0))
        + (K2 n (fun _ : ℝ => 0) s s (baseState s 1) • (coord 3)
          + (baseState s 3)
              • ((diagC2 n s * (((2 * n : ℕ) : ℝ) * (profileX s) ^ (2 * n - 1))) • (coord 1))))
      = linGG n s • (coord 0) - linGG n s • (coord 1)
        + linC n s • (coord 2) - linC n s • (coord 3) := by
  have hp : 0 < profileX s := profileX_pos s hs
  have hb0 : baseState s 0 = profileX s := rfl
  have hb1 : baseState s 1 = profileX s := rfl
  have hb2 : baseState s 2 = deriv profileX s := rfl
  have hb3 : baseState s 3 = deriv profileX s := rfl
  ext z
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, coord_apply, hb0, hb1, hb2, hb3]
  rw [diag_K2_explicit_neg n hn hs (show -(profileX s) < 0 by linarith),
    diag_K2_explicit_pos n hn hs hp]
  unfold linGG linC diagC2
  ring

lemma hasFDerivAt_godd_row2 (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    HasFDerivAt (GoddRow2 n s)
      (linAA n s • (coord 0) + linAA n s • (coord 1)
        + linA n s • (coord 2) + linA n s • (coord 3)) (baseState s) := by
  have hp : 0 < profileX s := profileX_pos s hs
  have hnegp : -(profileX s) < 0 := by linarith
  have hb0 : baseState s 0 = profileX s := rfl
  have hb1 : baseState s 1 = profileX s := rfl
  have hb2 : baseState s 2 = deriv profileX s := rfl
  have hb3 : baseState s 3 = deriv profileX s := rfl
  have hK1p := diag_K1_hasDerivAt_pos (n := n) (s := s) hs hp
  have hK1n := diag_K1_hasDerivAt_neg (n := n) (s := s) hs hnegp
  have h1 : HasFDerivAt (fun z : St => K1 n (fun _ : ℝ => 0) s s (-(z 0)))
      ((diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n)))
        • (coord 0)) (baseState s) := by
    simpa using comp_neg_coord_hasFDerivAt (j := 0) (x := baseState s) hK1n
  have h2 : HasFDerivAt (fun z : St => K1 n (fun _ : ℝ => 0) s s (z 1))
      ((diagC1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n)))
        • (coord 1)) (baseState s) := by
    simpa using comp_coord_hasFDerivAt (j := 1) (x := baseState s) hK1p
  have hm1 := mul_coord_hasFDerivAt (j := 2) h1
  have hm2 := mul_coord_hasFDerivAt (j := 3) h2
  have h := (hm1.add hm2).const_mul abelMass
  convert h using 1
  all_goals first
    | exact (row2_clm n hn hs).symm
    | exact row2_clm n hn hs
    | rfl
    | (funext z; rfl)

lemma hasFDerivAt_godd_row3 (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    HasFDerivAt (GoddRow3 n s)
      (linGG n s • (coord 0) - linGG n s • (coord 1)
        + linC n s • (coord 2) - linC n s • (coord 3)) (baseState s) := by
  have hp : 0 < profileX s := profileX_pos s hs
  have hnegp : -(profileX s) < 0 := by linarith
  have hb0 : baseState s 0 = profileX s := rfl
  have hb1 : baseState s 1 = profileX s := rfl
  have hb2 : baseState s 2 = deriv profileX s := rfl
  have hb3 : baseState s 3 = deriv profileX s := rfl
  have hK2p : HasDerivAt (fun u : ℝ => K2 n (fun _ : ℝ => 0) s s u)
      (diagC2 n s * (((2 * n : ℕ) : ℝ) * (profileX s) ^ (2 * n - 1))) (profileX s) :=
    diag_K2_hasDerivAt_pos n hn hs hp
  have hK2n : HasDerivAt (fun u : ℝ => K2 n (fun _ : ℝ => 0) s s u)
      (diagC2 n s * (((2 * n : ℕ) : ℝ) * (profileX s) ^ (2 * n - 1))) (-(profileX s)) := by
    simpa using diag_K2_hasDerivAt_neg n hn hs hnegp
  have h1 : HasFDerivAt (fun z : St => K2 n (fun _ : ℝ => 0) s s (-(z 0)))
      ((-(diagC2 n s * (((2 * n : ℕ) : ℝ) * (profileX s) ^ (2 * n - 1))))
        • (coord 0)) (baseState s) := by
    simpa using comp_neg_coord_hasFDerivAt (j := 0) (x := baseState s) hK2n
  have h2 : HasFDerivAt (fun z : St => K2 n (fun _ : ℝ => 0) s s (z 1))
      ((diagC2 n s * (((2 * n : ℕ) : ℝ) * (profileX s) ^ (2 * n - 1)))
        • (coord 1)) (baseState s) := by
    simpa using comp_coord_hasFDerivAt (j := 1) (x := baseState s) hK2p
  have hm1 := mul_coord_hasFDerivAt (j := 2) h1
  have hm2 := mul_coord_hasFDerivAt (j := 3) h2
  have h := (hm1.add hm2).const_mul abelMass
  convert h using 1
  all_goals first
    | exact (row3_clm n hn hs).symm
    | exact row3_clm n hn hs
    | rfl
    | (funext z; rfl)

lemma proj_comp_PhiCLM_zero (n : ℕ) (s : ℝ) :
    (ContinuousLinearMap.proj (0 : Fin 4)).comp (PhiCLM n s)
      = (ContinuousLinearMap.proj (0 : Fin 4)) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    PhiCLM_coord_zero]

lemma proj_comp_PhiCLM_one (n : ℕ) (s : ℝ) :
    (ContinuousLinearMap.proj (1 : Fin 4)).comp (PhiCLM n s)
      = (ContinuousLinearMap.proj (1 : Fin 4)) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    PhiCLM_coord_one]

lemma proj_comp_PhiCLM_two (n : ℕ) (s : ℝ) :
    (ContinuousLinearMap.proj (2 : Fin 4)).comp (PhiCLM n s)
      = (linAA n s • ContinuousLinearMap.proj (0 : Fin 4)
        + linAA n s • ContinuousLinearMap.proj (1 : Fin 4)
        + linA n s • ContinuousLinearMap.proj (2 : Fin 4)
        + linA n s • ContinuousLinearMap.proj (3 : Fin 4)) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    PhiCLM_coord_two, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

lemma proj_comp_PhiCLM_three (n : ℕ) (s : ℝ) :
    (ContinuousLinearMap.proj (3 : Fin 4)).comp (PhiCLM n s)
      = (linGG n s • ContinuousLinearMap.proj (0 : Fin 4)
        - linGG n s • ContinuousLinearMap.proj (1 : Fin 4)
        + linC n s • ContinuousLinearMap.proj (2 : Fin 4)
        - linC n s • ContinuousLinearMap.proj (3 : Fin 4)) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    PhiCLM_coord_three, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma hasFDerivAt_godd_coord_zero (n : ℕ) (s : ℝ) :
    HasFDerivAt (fun z : St => (Godd n 0 s z) 0)
      ((ContinuousLinearMap.proj (0 : Fin 4)).comp (PhiCLM n s)) (baseState s) := by
  rw [proj_comp_PhiCLM_zero]
  rw [show (fun z : St => (Godd n 0 s z) 0) = fun z : St => z 0 by
    funext z; exact Godd_coord_zero n s z]
  convert (ContinuousLinearMap.proj (0 : Fin 4)).hasFDerivAt (x := baseState s) using 1
  all_goals first | rfl | (funext z; rfl)

lemma hasFDerivAt_godd_coord_one (n : ℕ) (s : ℝ) :
    HasFDerivAt (fun z : St => (Godd n 0 s z) 1)
      ((ContinuousLinearMap.proj (1 : Fin 4)).comp (PhiCLM n s)) (baseState s) := by
  rw [proj_comp_PhiCLM_one]
  rw [show (fun z : St => (Godd n 0 s z) 1) = fun z : St => z 1 by
    funext z; exact Godd_coord_one n s z]
  convert (ContinuousLinearMap.proj (1 : Fin 4)).hasFDerivAt (x := baseState s) using 1
  all_goals first | rfl | (funext z; rfl)

lemma hasFDerivAt_godd_coord_two (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    HasFDerivAt (fun z : St => (Godd n 0 s z) 2)
      ((ContinuousLinearMap.proj (2 : Fin 4)).comp (PhiCLM n s)) (baseState s) := by
  rw [proj_comp_PhiCLM_two]
  rw [show (fun z : St => (Godd n 0 s z) 2) = GoddRow2 n s by
    funext z; exact Godd_coord_two n s z]
  exact hasFDerivAt_godd_row2 n hn hs

lemma hasFDerivAt_godd_coord_three (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    HasFDerivAt (fun z : St => (Godd n 0 s z) 3)
      ((ContinuousLinearMap.proj (3 : Fin 4)).comp (PhiCLM n s)) (baseState s) := by
  rw [proj_comp_PhiCLM_three]
  rw [show (fun z : St => (Godd n 0 s z) 3) = GoddRow3 n s by
    funext z; exact Godd_coord_three n s z]
  exact hasFDerivAt_godd_row3 n hn hs

lemma hasFDerivAt_Godd_zero (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    HasFDerivAt (fun z : St => Godd n 0 s z) (PhiCLM n s) (baseState s) := by
  refine hasFDerivAt_pi'' (Φ := fun z : St => Godd n 0 s z) (Φ' := PhiCLM n s) ?_
  intro i
  fin_cases i
  · exact hasFDerivAt_godd_coord_zero n s
  · exact hasFDerivAt_godd_coord_one n s
  · exact hasFDerivAt_godd_coord_two n hn hs
  · exact hasFDerivAt_godd_coord_three n hn hs

/-! ## The linearization family -/

/-- The family of linear equivalences realizing the diagonal derivative, on `[a,b]`. -/
noncomputable def linFamily (n : ℕ) (a b : ℝ) (ha : 0 < a) : ℝ → St ≃L[ℝ] St :=
  fun s =>
    if hs : s ∈ Set.Icc a b then
      ContinuousLinearEquiv.equivOfInverse (PhiCLM n s) (PsiCLM n s)
        (PsiCLM_leftInverse n s (linA_ne_zero n (lt_of_lt_of_le ha hs.1))
          (linC_ne_zero n (lt_of_lt_of_le ha hs.1)))
        (PsiCLM_rightInverse n s (linA_ne_zero n (lt_of_lt_of_le ha hs.1))
          (linC_ne_zero n (lt_of_lt_of_le ha hs.1)))
    else ContinuousLinearEquiv.refl ℝ St

lemma clm_linFamily (n : ℕ) {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Icc a b) :
    (linFamily n a b ha s : St →L[ℝ] St) = PhiCLM n s := by
  rw [linFamily, dif_pos hs]
  rfl

lemma symm_linFamily (n : ℕ) {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Icc a b) :
    ((linFamily n a b ha s).symm : St →L[ℝ] St) = PsiCLM n s := by
  rw [linFamily, dif_pos hs]
  ext w
  rfl

theorem odd_linearization (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ (A : ℝ → Work.OddVolterra.St ≃L[ℝ] Work.OddVolterra.St) (B : ℝ), 0 < B ∧
      (∀ s ∈ Set.Icc a b, (A s : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St) =
        fderiv ℝ (fun z => Work.OddVolterra.Godd n 0 s z) (Work.OddVolterra.baseState s)) ∧
      ContinuousOn (fun s => ((A s).symm : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St))
        (Set.Icc a b) ∧
      (∀ s ∈ Set.Icc a b,
        ‖((A s).symm : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St)‖ ≤ B) := by
  have hcont : ContinuousOn
      (fun s : ℝ => ((linFamily n a b ha s).symm : St →L[ℝ] St)) (Set.Icc a b) :=
    (continuousOn_PsiCLM (n := n) (a := a) (b := b) ha).congr
      (fun s hs => symm_linFamily n ha hs)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨linFamily n a b ha, max B 1, lt_max_of_lt_right (by norm_num), ?_, hcont, ?_⟩
  · intro s hs
    rw [clm_linFamily n ha hs]
    exact (hasFDerivAt_Godd_zero n hn (lt_of_lt_of_le ha hs.1)).fderiv.symm
  · intro s hs
    exact le_trans (hB s hs) (le_max_left B 1)

end

end Work.OddVolterra.Existence
