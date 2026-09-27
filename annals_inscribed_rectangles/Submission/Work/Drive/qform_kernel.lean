import Mathlib
import Submission.Work.Drive.squareSystemForm

/-!
# The kernel of the class-difference form `qform`

`Work.Drive.qform v w` is the imaginary part of the quaternion product `v · conj w`, i.e. (for
`v = (v₀, v')`, `w = (w₀, w') ∈ Eucl 3 = ℝ⁴ ≅ ℍ`)

`qform v w = w₀ • v' - v₀ • w' - (v' × w')`,

bilinear and antisymmetric on the whole of `ℝ⁴ × ℝ⁴`.  Its vanishing expresses that `v` and `w`
represent the *same* class in `ℝP³ ≅ ℍ/±1`, so its kernel in the second variable is exactly the real
line spanned by `v`:

`qform v w = 0 ↔ w ∈ ℝ ∙ v`   for `v ≠ 0`   (`Work.Drive.qform_kernel`, below).

The proof is the standard quaternion computation, written in coordinates:

* `qform v w = 0` says `v' × w' = w₀ v' - v₀ w'` (`qform_coord`);
* pairing that identity with `v' × w'` and using that `v' × w'` is orthogonal to both `v'` and `w'`
  gives `‖v' × w'‖² = 0`, hence `v' × w' = 0` (`crossProduct_imagFun_eq_zero`) — this is where the
  kernel structure genuinely enters;
* together with `w₀ v' = v₀ w'` (`smul_imagFun_eq`) this forces `w` to be a multiple of `v`: if
  `v₀ ≠ 0` the multiple is `w₀ / v₀`, and if `v₀ = 0` then `v' ≠ 0` and `w' ∈ ℝ v'` by the
  three-dimensional fact that the kernel of the cross product is the line
  (`exists_smul_of_crossProduct_eq_zero`, from `crossProduct_ne_zero_iff_linearIndependent`).

The converse is `qform v (c • v) = 0` (`qform_smul_self`), since `v · conj v` is real.
-/

namespace Work.Drive

open scoped ContDiff Topology

noncomputable section

/-- The imaginary part of `v ∈ Eucl 3 = ℝ⁴`, as a raw function `Fin 3 → ℝ` (the pointwise version
of `Work.Drive.imagPart`). -/
def imagFun (v : Eucl 3) : Fin 3 → ℝ := fun i => v (Fin.succ i)

lemma imagFun_apply (v : Eucl 3) (i : Fin 3) : imagFun v i = v (Fin.succ i) := rfl

/-- `imagPart`, read as a function of `Fin 3`. -/
lemma imagPart_eq_imagFun (v : Eucl 3) : (imagPart v : Fin 3 → ℝ) = imagFun v := by
  funext i; exact imagPart_ofLp v i

lemma imagFun_smul (c : ℝ) (v : Eucl 3) : imagFun (c • v) = c • imagFun v := by
  funext i; simp [imagFun, Pi.smul_apply]

/-- Coordinate form of `qform v w = 0`: the imaginary part of `v · conj w` is `w₀ v' - v₀ w'`. -/
lemma qform_coord (v w : Eucl 3) (h : qform v w = 0) (k : Fin 3) :
    crossProduct (imagFun v) (imagFun w) k = w 0 * imagFun v k - v 0 * imagFun w k := by
  have hk : (qform v w) k = 0 := by rw [h]; simp
  rw [qform_ofLp] at hk
  rw [imagPart_eq_imagFun v, imagPart_eq_imagFun w] at hk
  simp only [imagFun] at hk ⊢
  linarith

/-- **The key point**: `qform v w = 0` forces the cross product of the imaginary parts to vanish.
Indeed the coordinate identity reads `v' × w' = w₀ v' - v₀ w'`; pairing it with `v' × w'`, which is
orthogonal to `v'` and `w'`, gives `‖v' × w'‖² = 0`. -/
lemma crossProduct_imagFun_eq_zero (v w : Eucl 3) (h : qform v w = 0) :
    crossProduct (imagFun v) (imagFun w) = 0 := by
  have hdec : crossProduct (imagFun v) (imagFun w) = w 0 • imagFun v - v 0 • imagFun w := by
    funext k
    rw [qform_coord v w h k]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hCC : dotProduct (crossProduct (imagFun v) (imagFun w))
      (crossProduct (imagFun v) (imagFun w)) = 0 := by
    nth_rewrite 1 [hdec]
    rw [sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      dot_self_cross, dot_cross_self]
    ring
  exact dotProduct_self_eq_zero.mp hCC

/-- The second half of the vanishing condition: `qform v w = 0` gives `w₀ v' = v₀ w'`. -/
lemma smul_imagFun_eq (v w : Eucl 3) (h : qform v w = 0) :
    w 0 • imagFun v = v 0 • imagFun w := by
  have hdec : crossProduct (imagFun v) (imagFun w) = w 0 • imagFun v - v 0 • imagFun w := by
    funext k
    rw [qform_coord v w h k]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h0 := crossProduct_imagFun_eq_zero v w h
  have : w 0 • imagFun v - v 0 • imagFun w = 0 := by rw [← hdec]; exact h0
  exact sub_eq_zero.mp this

/-- Extensionality for `Eucl 3 = ℝ⁴` from the "real" coordinate and the three imaginary ones. -/
lemma eq_of_apply {v w : Eucl 3} (h0 : v 0 = w 0)
    (h : ∀ i : Fin 3, v (Fin.succ i) = w (Fin.succ i)) : v = w := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa using h0
  · intro j; simpa using h j

/-- In dimension three the kernel of the cross product is the line spanned by the first factor
(`crossProduct_ne_zero_iff_linearIndependent`). -/
lemma exists_smul_of_crossProduct_eq_zero {A B : Fin 3 → ℝ} (hA : A ≠ 0)
    (h : crossProduct A B = 0) : ∃ μ : ℝ, B = μ • A := by
  by_contra hcon
  push Not at hcon
  have hli : LinearIndependent ℝ ![A, B] :=
    (LinearIndependent.pair_iff' hA).mpr fun a => (hcon a).symm
  exact (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h

/-- If `qform v w = 0` and `v ≠ 0` then `w` is a real multiple of `v`. -/
lemma exists_smul_of_qform_eq_zero {v w : Eucl 3} (hv : v ≠ 0) (h : qform v w = 0) :
    ∃ μ : ℝ, w = μ • v := by
  have h0 := crossProduct_imagFun_eq_zero v w h
  have hAB := smul_imagFun_eq v w h
  by_cases hv0 : v 0 = 0
  · -- `v₀ = 0`, so `v' ≠ 0`: the form is the cross product and its kernel is `ℝ v'`.
    have hAne : imagFun v ≠ 0 := by
      intro hA0
      apply hv
      apply eq_of_apply (v := v) (w := 0)
      · simpa using hv0
      · intro j
        have : imagFun v j = 0 := by rw [hA0]; rfl
        simpa [imagFun] using this
    obtain ⟨μ, hμ⟩ := exists_smul_of_crossProduct_eq_zero hAne h0
    have hw0 : w 0 = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, imagFun v j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hAne (funext fun i => hc i)
      have h1 := congrFun hAB j
      simp only [Pi.smul_apply, smul_eq_mul, hv0, zero_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_right hj
    refine ⟨μ, ?_⟩
    apply eq_of_apply
    · simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hw0, hv0, mul_zero]
    · intro i
      have h1 := congrFun hμ i
      simp only [imagFun, Pi.smul_apply, smul_eq_mul] at h1
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      simpa only [imagFun, Pi.smul_apply, smul_eq_mul] using h1
  · -- `v₀ ≠ 0`: the multiple is `w₀ / v₀`.
    refine ⟨w 0 / v 0, ?_⟩
    apply eq_of_apply
    · simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hv0]
    · intro i
      have h1 := congrFun hAB i
      simp only [imagFun, Pi.smul_apply, smul_eq_mul] at h1
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff hv0]
      linarith

/-- The converse direction: `qform` vanishes on the diagonal line, since `v · conj v = ‖v‖²` is
real. -/
lemma qform_smul_self (v : Eucl 3) (c : ℝ) : qform v (c • v) = 0 := by
  apply WithLp.ofLp_injective (p := 2)
  funext k
  rw [qform_ofLp]
  rw [imagPart_eq_imagFun v, imagPart_eq_imagFun (c • v), imagFun_smul]
  rw [map_smul, cross_self]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_zero, Pi.zero_apply,
    mul_zero, sub_zero]
  ring

/-- **The kernel of `qform` in the second variable is the line `ℝ v`.**  For `v ≠ 0`,
`qform v w = 0` if and only if `w` is a real multiple of `v`, i.e. `v` and `w` represent the same
class in `ℝP³`. -/
theorem qform_kernel (v w : Work.Drive.Eucl 3) (hv : v ≠ 0) :
    Work.Drive.qform v w = 0 ↔ w ∈ Submodule.span ℝ ({v} : Set (Work.Drive.Eucl 3)) := by
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := exists_smul_of_qform_eq_zero hv h
    rw [Submodule.mem_span_singleton]
    exact ⟨μ, by rw [hμ]⟩
  · intro hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨μ, hμ⟩ := hw
    rw [← hμ]
    exact qform_smul_self v μ

end

end Work.Drive
