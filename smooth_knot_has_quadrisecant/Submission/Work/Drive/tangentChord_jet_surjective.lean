import Mathlib
import Submission.Work.Drive.trigBasisDD

/-!
# The second-order jet interpolation for the tangent-chord rank computation

The degree-`≤ 4` trigonometric basis `trigBasis` of `knotPerturbDefs` realises arbitrary
*value differences at two points, first derivatives at both and the second derivative at the
first*: for real `a b` with `Real.cos (b - a) ≠ 1` and arbitrary `β ξ η ζ : Space` there is
`c : Fin 9 → Space` with

`Σ j, (trigBasis j b - trigBasis j a) • c j = β`, `Σ j, trigBasisD j a • c j = ξ`,
`Σ j, trigBasisD j b • c j = η`, `Σ j, trigBasisDD j a • c j = ζ`.

The proof uses only the four functions `cos (t-a), sin (t-a), cos (2(t-a)), sin (2(t-a))`: in
those four coordinates the `4 × 4` jet matrix is

`![![c-1, 2*c^2-2, σ, 2*σ*c], ![0, 0, 1, 2], ![-σ, -2*σ*c, c, 2*c^2-1], ![-1, -4, 0, 0]]`

(`c = cos (b-a)`, `σ = sin (b-a)`), whose kernel is trivial for `c ≠ 1`; finite-dimensionality
then upgrades injectivity to surjectivity, and the four shifted basis functions are explicit
`ℝ`-linear combinations of `trigBasis 0, …, trigBasis 4`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The four shifted basis functions as coefficient vectors -/

/-- Coefficients of `t ↦ cos (t - a)` in the degree-`≤ 4` basis. -/
def jcCos (a : ℝ) : Fin 9 → ℝ
  | 1 => Real.cos a
  | 2 => Real.sin a
  | _ => 0

/-- Coefficients of `t ↦ cos (2 * (t - a))`. -/
def jcCos2 (a : ℝ) : Fin 9 → ℝ
  | 3 => Real.cos (2 * a)
  | 4 => Real.sin (2 * a)
  | _ => 0

/-- Coefficients of `t ↦ sin (t - a)`. -/
def jcSin (a : ℝ) : Fin 9 → ℝ
  | 1 => -Real.sin a
  | 2 => Real.cos a
  | _ => 0

/-- Coefficients of `t ↦ sin (2 * (t - a))`. -/
def jcSin2 (a : ℝ) : Fin 9 → ℝ
  | 3 => -Real.sin (2 * a)
  | 4 => Real.cos (2 * a)
  | _ => 0

/-! ## Evaluation of the twelve partial sums -/

lemma sum_jcCos (a t : ℝ) : (∑ j : Fin 9, trigBasis j t * jcCos a j) = Real.cos (t - a) := by
  simp [Fin.sum_univ_succ, jcCos, trigBasis]
  rw [Real.cos_sub]
  try ring

lemma sum_jcCos2 (a t : ℝ) :
    (∑ j : Fin 9, trigBasis j t * jcCos2 a j) = Real.cos (2 * (t - a)) := by
  simp [Fin.sum_univ_succ, jcCos2, trigBasis]
  rw [show (2:ℝ) * (t - a) = 2 * t - 2 * a by ring, Real.cos_sub]
  try ring

lemma sum_jcSin (a t : ℝ) : (∑ j : Fin 9, trigBasis j t * jcSin a j) = Real.sin (t - a) := by
  simp [Fin.sum_univ_succ, jcSin, trigBasis]
  rw [Real.sin_sub]
  try ring

lemma sum_jcSin2 (a t : ℝ) :
    (∑ j : Fin 9, trigBasis j t * jcSin2 a j) = Real.sin (2 * (t - a)) := by
  simp [Fin.sum_univ_succ, jcSin2, trigBasis]
  rw [show (2:ℝ) * (t - a) = 2 * t - 2 * a by ring, Real.sin_sub]
  try ring

lemma sumD_jcCos (a t : ℝ) :
    (∑ j : Fin 9, trigBasisD j t * jcCos a j) = -Real.sin (t - a) := by
  simp [Fin.sum_univ_succ, jcCos, trigBasisD]
  rw [Real.sin_sub]
  try ring

lemma sumD_jcCos2 (a t : ℝ) :
    (∑ j : Fin 9, trigBasisD j t * jcCos2 a j) = -2 * Real.sin (2 * (t - a)) := by
  simp [Fin.sum_univ_succ, jcCos2, trigBasisD]
  rw [show (2:ℝ) * (t - a) = 2 * t - 2 * a by ring, Real.sin_sub]
  try ring

lemma sumD_jcSin (a t : ℝ) :
    (∑ j : Fin 9, trigBasisD j t * jcSin a j) = Real.cos (t - a) := by
  simp [Fin.sum_univ_succ, jcSin, trigBasisD]
  rw [Real.cos_sub]
  try ring

lemma sumD_jcSin2 (a t : ℝ) :
    (∑ j : Fin 9, trigBasisD j t * jcSin2 a j) = 2 * Real.cos (2 * (t - a)) := by
  simp [Fin.sum_univ_succ, jcSin2, trigBasisD]
  rw [show (2:ℝ) * (t - a) = 2 * t - 2 * a by ring, Real.cos_sub]
  try ring

lemma sumDD_jcCos (a t : ℝ) :
    (∑ j : Fin 9, trigBasisDD j t * jcCos a j) = -Real.cos (t - a) := by
  simp [Fin.sum_univ_succ, jcCos, trigBasisDD]
  rw [Real.cos_sub]
  try ring

lemma sumDD_jcCos2 (a t : ℝ) :
    (∑ j : Fin 9, trigBasisDD j t * jcCos2 a j) = -4 * Real.cos (2 * (t - a)) := by
  simp [Fin.sum_univ_succ, jcCos2, trigBasisDD]
  rw [show (2:ℝ) * (t - a) = 2 * t - 2 * a by ring, Real.cos_sub]
  try ring

lemma sumDD_jcSin (a t : ℝ) :
    (∑ j : Fin 9, trigBasisDD j t * jcSin a j) = -Real.sin (t - a) := by
  simp [Fin.sum_univ_succ, jcSin, trigBasisDD]
  rw [Real.sin_sub]
  try ring

lemma sumDD_jcSin2 (a t : ℝ) :
    (∑ j : Fin 9, trigBasisDD j t * jcSin2 a j) = -4 * Real.sin (2 * (t - a)) := by
  simp [Fin.sum_univ_succ, jcSin2, trigBasisDD]
  rw [show (2:ℝ) * (t - a) = 2 * t - 2 * a by ring, Real.sin_sub]
  try ring

/-! ## The coefficient vector of a shifted combination -/

/-- The coefficient vector in the degree-`≤ 4` basis of
`x 0 * cos (t-a) + x 1 * cos (2(t-a)) + x 2 * sin (t-a) + x 3 * sin (2(t-a))`. -/
def jetShift (a : ℝ) (x : Fin 4 → ℝ) : Fin 9 → ℝ :=
  x 0 • jcCos a + x 1 • jcCos2 a + x 2 • jcSin a + x 3 • jcSin2 a

lemma sum_jetShift (a t : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, trigBasis j t * jetShift a x j)
      = x 0 * Real.cos (t - a) + x 1 * Real.cos (2 * (t - a)) + x 2 * Real.sin (t - a)
        + x 3 * Real.sin (2 * (t - a)) := by
  have hc : ∀ j : Fin 9, trigBasis j t * (x 0 * jcCos a j + x 1 * jcCos2 a j
      + x 2 * jcSin a j + x 3 * jcSin2 a j)
      = x 0 * (trigBasis j t * jcCos a j) + x 1 * (trigBasis j t * jcCos2 a j)
        + x 2 * (trigBasis j t * jcSin a j) + x 3 * (trigBasis j t * jcSin2 a j) :=
    fun j => by ring
  simp only [jetShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hc j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_jcCos, sum_jcCos2, sum_jcSin, sum_jcSin2]

lemma sumD_jetShift (a t : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, trigBasisD j t * jetShift a x j)
      = -x 0 * Real.sin (t - a) - 2 * x 1 * Real.sin (2 * (t - a)) + x 2 * Real.cos (t - a)
        + 2 * x 3 * Real.cos (2 * (t - a)) := by
  have hc : ∀ j : Fin 9, trigBasisD j t * (x 0 * jcCos a j + x 1 * jcCos2 a j
      + x 2 * jcSin a j + x 3 * jcSin2 a j)
      = x 0 * (trigBasisD j t * jcCos a j) + x 1 * (trigBasisD j t * jcCos2 a j)
        + x 2 * (trigBasisD j t * jcSin a j) + x 3 * (trigBasisD j t * jcSin2 a j) :=
    fun j => by ring
  simp only [jetShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hc j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sumD_jcCos, sumD_jcCos2, sumD_jcSin, sumD_jcSin2]
  ring

lemma sumDD_jetShift (a t : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, trigBasisDD j t * jetShift a x j)
      = -x 0 * Real.cos (t - a) - 4 * x 1 * Real.cos (2 * (t - a)) - x 2 * Real.sin (t - a)
        - 4 * x 3 * Real.sin (2 * (t - a)) := by
  have hc : ∀ j : Fin 9, trigBasisDD j t * (x 0 * jcCos a j + x 1 * jcCos2 a j
      + x 2 * jcSin a j + x 3 * jcSin2 a j)
      = x 0 * (trigBasisDD j t * jcCos a j) + x 1 * (trigBasisDD j t * jcCos2 a j)
        + x 2 * (trigBasisDD j t * jcSin a j) + x 3 * (trigBasisDD j t * jcSin2 a j) :=
    fun j => by ring
  simp only [jetShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hc j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sumDD_jcCos, sumDD_jcCos2, sumDD_jcSin, sumDD_jcSin2]
  ring

/-! ## The four jet coordinates in the shifted basis -/

/-- The value difference `f b - f a`. -/
def jetC0 (a b : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (Real.cos (b - a) - 1) • (LinearMap.proj 0) + (Real.cos (2 * (b - a)) - 1) • (LinearMap.proj 1)
    + Real.sin (b - a) • (LinearMap.proj 2) + Real.sin (2 * (b - a)) • (LinearMap.proj 3)

/-- The first derivative at `a`. -/
def jetC1 (a b : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj 2) + (2 : ℝ) • (LinearMap.proj 3)

/-- The first derivative at `b`. -/
def jetC2 (a b : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (-(Real.sin (b - a))) • (LinearMap.proj 0) + (-(2 * Real.sin (2 * (b - a)))) • (LinearMap.proj 1)
    + Real.cos (b - a) • (LinearMap.proj 2) + (2 * Real.cos (2 * (b - a))) • (LinearMap.proj 3)

/-- The second derivative at `a`. -/
def jetC3 (a b : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  (-1 : ℝ) • (LinearMap.proj 0) + (-4 : ℝ) • (LinearMap.proj 1)

lemma jetC0_apply (a b : ℝ) (x : Fin 4 → ℝ) :
    jetC0 a b x = (Real.cos (b - a) - 1) * x 0 + (Real.cos (2 * (b - a)) - 1) * x 1
      + Real.sin (b - a) * x 2 + Real.sin (2 * (b - a)) * x 3 := by
  simp only [jetC0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  try ring

lemma jetC1_apply (a b : ℝ) (x : Fin 4 → ℝ) : jetC1 a b x = x 2 + 2 * x 3 := by
  simp only [jetC1, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  try ring

lemma jetC2_apply (a b : ℝ) (x : Fin 4 → ℝ) :
    jetC2 a b x = -(Real.sin (b - a)) * x 0 - (2 * Real.sin (2 * (b - a))) * x 1
      + Real.cos (b - a) * x 2 + (2 * Real.cos (2 * (b - a))) * x 3 := by
  simp only [jetC2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  try ring

lemma jetC3_apply (a b : ℝ) (x : Fin 4 → ℝ) : jetC3 a b x = -x 0 - 4 * x 1 := by
  simp only [jetC3, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  try ring

/-- The `4 × 4` jet map in the coordinates of the four shifted basis functions. -/
def jetMap (a b : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((jetC0 a b).prod (jetC1 a b)).prod ((jetC2 a b).prod (jetC3 a b))

@[simp] lemma jetMap_apply (a b : ℝ) (x : Fin 4 → ℝ) :
    jetMap a b x = ((jetC0 a b x, jetC1 a b x), (jetC2 a b x, jetC3 a b x)) := rfl

/-! ## The jet map is injective -/

theorem jetMap_injective (a b : ℝ) (h : Real.cos (b - a) ≠ 1) :
    Function.Injective (jetMap a b) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [jetMap_apply] at hx
  have h0 : jetC0 a b x = 0 := by
    have := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1) hx; simpa using this
  have h1 : jetC1 a b x = 0 := by
    have := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.2) hx; simpa using this
  have h2f : jetC2 a b x = 0 := by
    have := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1) hx; simpa using this
  have h3 : jetC3 a b x = 0 := by
    have := congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.2) hx; simpa using this
  rw [jetC0_apply] at h0
  rw [jetC1_apply] at h1
  rw [jetC2_apply] at h2f
  rw [jetC3_apply] at h3
  set c := Real.cos (b - a) with hc
  set s := Real.sin (b - a) with hs
  have hcne : c ≠ 1 := by rw [hc]; exact h
  have hsq : s ^ 2 + c ^ 2 = 1 := by rw [hs, hc]; exact Real.sin_sq_add_cos_sq (b - a)
  have e1 : (c - 1) * x 0 + (2 * c ^ 2 - 2) * x 1 + s * x 2 + (2 * s * c) * x 3 = 0 := by
    have h' := h0
    rw [Real.cos_two_mul, Real.sin_two_mul, ← hc, ← hs] at h'
    linear_combination h'
  have e2 : x 2 + 2 * x 3 = 0 := h1
  have e3 : -s * x 0 - (4 * s * c) * x 1 + c * x 2 + (4 * c ^ 2 - 2) * x 3 = 0 := by
    have h' := h2f
    rw [Real.cos_two_mul, Real.sin_two_mul, ← hc, ← hs] at h'
    linear_combination h'
  have e4 : -x 0 - 4 * x 1 = 0 := h3
  have hx0 : x 0 = -4 * x 1 := by linarith [e4]
  have hx2 : x 2 = -2 * x 3 := by linarith [e2]
  have hA : x 1 * (c - 1) + x 3 * s = 0 := by
    have hA' : 2 * (c - 1) * (x 1 * (c - 1) + x 3 * s) = 0 := by
      linear_combination e1 - (c - 1) * hx0 - s * hx2
    rcases mul_eq_zero.mp hA' with hh | hh
    · rcases mul_eq_zero.mp hh with hh' | hh'
      · exact absurd hh' two_ne_zero
      · exact absurd hh' (sub_ne_zero.mpr hcne)
    · exact hh
  have hB : -2 * x 1 * s + x 3 * (2 * c + 1) = 0 := by
    have hB' : 2 * (c - 1) * (-2 * x 1 * s + x 3 * (2 * c + 1)) = 0 := by
      linear_combination e3 + s * hx0 - c * hx2
    rcases mul_eq_zero.mp hB' with hh | hh
    · rcases mul_eq_zero.mp hh with hh' | hh'
      · exact absurd hh' two_ne_zero
      · exact absurd hh' (sub_ne_zero.mpr hcne)
    · exact hh
  have hx1 : x 1 = 0 := by
    have h1' : x 1 * (1 - c) = 0 := by
      linear_combination (2 * c + 1) * hA - s * hB - (2 * x 1) * hsq
    rcases mul_eq_zero.mp h1' with hh | hh
    · exact hh
    · exact absurd hh (sub_ne_zero.mpr (Ne.symm hcne))
  have hx3 : x 3 = 0 := by
    have h3' : x 3 * (1 - c) = 0 := by
      linear_combination (2 * s) * hA + (c - 1) * hB - (2 * x 3) * hsq
    rcases mul_eq_zero.mp h3' with hh | hh
    · exact hh
    · exact absurd hh (sub_ne_zero.mpr (Ne.symm hcne))
  funext i
  fin_cases i
  · show x 0 = 0
    rw [hx0, hx1]; ring
  · show x 1 = 0
    exact hx1
  · show x 2 = 0
    rw [hx2, hx3]; ring
  · show x 3 = 0
    exact hx3

theorem jetMap_surjective (a b : ℝ) (h : Real.cos (b - a) ≠ 1) :
    Function.Surjective (jetMap a b) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_prod])).mp (jetMap_injective a b h)

/-! ## The sums of the shifted coefficients -/

lemma jetShift_spec0 (a b : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, (trigBasis j b - trigBasis j a) * jetShift a x j) = (jetMap a b x).1.1 := by
  rw [jetMap_apply, jetC0_apply]
  have hsplit : ∀ j : Fin 9, (trigBasis j b - trigBasis j a) * jetShift a x j
      = trigBasis j b * jetShift a x j - trigBasis j a * jetShift a x j := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_sub_distrib,
    sum_jetShift a b x, sum_jetShift a a x]
  simp only [sub_self, Real.cos_zero, Real.sin_zero, mul_zero]
  ring

lemma jetShift_spec1 (a b : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, trigBasisD j a * jetShift a x j) = (jetMap a b x).1.2 := by
  rw [jetMap_apply, jetC1_apply, sumD_jetShift a a x]
  simp only [sub_self, Real.cos_zero, Real.sin_zero, mul_zero]
  ring

lemma jetShift_spec2 (a b : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, trigBasisD j b * jetShift a x j) = (jetMap a b x).2.1 := by
  rw [jetMap_apply, jetC2_apply, sumD_jetShift a b x]
  ring

lemma jetShift_spec3 (a b : ℝ) (x : Fin 4 → ℝ) :
    (∑ j : Fin 9, trigBasisDD j a * jetShift a x j) = (jetMap a b x).2.2 := by
  rw [jetMap_apply, jetC3_apply, sumDD_jetShift a a x]
  simp only [sub_self, Real.cos_zero, Real.sin_zero, mul_zero]
  ring

/-! ## The scalar interpolation statement -/

theorem tangentChord_jet_scalar (a b : ℝ) (h : Real.cos (b - a) ≠ 1) (p q r u : ℝ) :
    ∃ d : Fin 9 → ℝ,
      (∑ j : Fin 9, (trigBasis j b - trigBasis j a) * d j) = p ∧
      (∑ j : Fin 9, trigBasisD j a * d j) = q ∧
      (∑ j : Fin 9, trigBasisD j b * d j) = r ∧
      (∑ j : Fin 9, trigBasisDD j a * d j) = u := by
  obtain ⟨x, hx⟩ := jetMap_surjective a b h ((p, q), (r, u))
  refine ⟨jetShift a x, ?_, ?_, ?_, ?_⟩
  · rw [jetShift_spec0, hx]
  · rw [jetShift_spec1, hx]
  · rw [jetShift_spec2, hx]
  · rw [jetShift_spec3, hx]

/-! ## The `Space`-valued interpolation statement -/

theorem tangentChord_jet_surjective {a b : ℝ} (h : Real.cos (b - a) ≠ 1)
    (β ξ η ζ : Space) :
    ∃ c : Fin 9 → Space,
      (∑ j : Fin 9, (trigBasis j b - trigBasis j a) • c j) = β ∧
      (∑ j : Fin 9, (trigBasisD j a) • c j) = ξ ∧
      (∑ j : Fin 9, (trigBasisD j b) • c j) = η ∧
      (∑ j : Fin 9, (trigBasisDD j a) • c j) = ζ := by
  obtain ⟨d0, hd0⟩ := tangentChord_jet_scalar a b h 1 0 0 0
  obtain ⟨d1, hd1⟩ := tangentChord_jet_scalar a b h 0 1 0 0
  obtain ⟨d2, hd2⟩ := tangentChord_jet_scalar a b h 0 0 1 0
  obtain ⟨d3, hd3⟩ := tangentChord_jet_scalar a b h 0 0 0 1
  refine ⟨fun j => (d0 j) • β + (d1 j) • ξ + (d2 j) • η + (d3 j) • ζ, ?_, ?_, ?_, ?_⟩
  · have hcongr : ∀ j : Fin 9,
        (trigBasis j b - trigBasis j a) • ((d0 j) • β + (d1 j) • ξ + (d2 j) • η + (d3 j) • ζ)
          = ((trigBasis j b - trigBasis j a) * d0 j) • β
            + ((trigBasis j b - trigBasis j a) * d1 j) • ξ
            + ((trigBasis j b - trigBasis j a) * d2 j) • η
            + ((trigBasis j b - trigBasis j a) * d3 j) • ζ := fun j => by
      rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul,
      ← Finset.sum_smul]
    rw [hd0.1, hd1.1, hd2.1, hd3.1]
    simp
  · have hcongr : ∀ j : Fin 9,
        trigBasisD j a • ((d0 j) • β + (d1 j) • ξ + (d2 j) • η + (d3 j) • ζ)
          = (trigBasisD j a * d0 j) • β + (trigBasisD j a * d1 j) • ξ
            + (trigBasisD j a * d2 j) • η + (trigBasisD j a * d3 j) • ζ := fun j => by
      rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul,
      ← Finset.sum_smul]
    rw [hd0.2.1, hd1.2.1, hd2.2.1, hd3.2.1]
    simp
  · have hcongr : ∀ j : Fin 9,
        trigBasisD j b • ((d0 j) • β + (d1 j) • ξ + (d2 j) • η + (d3 j) • ζ)
          = (trigBasisD j b * d0 j) • β + (trigBasisD j b * d1 j) • ξ
            + (trigBasisD j b * d2 j) • η + (trigBasisD j b * d3 j) • ζ := fun j => by
      rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul,
      ← Finset.sum_smul]
    rw [hd0.2.2.1, hd1.2.2.1, hd2.2.2.1, hd3.2.2.1]
    simp
  · have hcongr : ∀ j : Fin 9,
        trigBasisDD j a • ((d0 j) • β + (d1 j) • ξ + (d2 j) • η + (d3 j) • ζ)
          = (trigBasisDD j a * d0 j) • β + (trigBasisDD j a * d1 j) • ξ
            + (trigBasisDD j a * d2 j) • η + (trigBasisDD j a * d3 j) • ζ := fun j => by
      rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul,
      ← Finset.sum_smul]
    rw [hd0.2.2.2, hd1.2.2.2, hd2.2.2.2, hd3.2.2.2]
    simp

end

end Work.Drive
