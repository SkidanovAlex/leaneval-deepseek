import Mathlib
import Submission.Work.BW.Minkowski2.shear_volume

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory

/-- The shear map `x ↦ Function.update x i (c * x i + g x)` is a bijection whose inverse
`y ↦ Function.update y i ((y i - g y)/c)` is measurable when `g` is.  Hence it maps measurable
sets to measurable sets, and (by `shear_volume`) multiplies Lebesgue measure by `c`. -/
theorem shear_volume_measurable {d : ℕ} (i : Fin d) {c : ℝ} (hc : 0 < c)
    {g : (Fin d → ℝ) → ℝ} (hg : Measurable g)
    (hgi : ∀ x y : Fin d → ℝ, (∀ m : Fin d, m ≠ i → x m = y m) → g x = g y)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    MeasureTheory.volume ((fun x : Fin d → ℝ => Function.update x i (c * x i + g x)) '' A)
      = ENNReal.ofReal c * MeasureTheory.volume A
    ∧ MeasurableSet ((fun x : Fin d → ℝ => Function.update x i (c * x i + g x)) '' A) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  let T : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (c * x i + g x)
  let Tinv : (Fin d → ℝ) → (Fin d → ℝ) := fun y => Function.update y i ((y i - g y) / c)
  have hT_apply : ∀ x, T x i = c * x i + g x := by
    intro x
    show Function.update x i (c * x i + g x) i = c * x i + g x
    rw [Function.update_apply, if_pos rfl]
  have hTinv_apply : ∀ y, Tinv y i = (y i - g y) / c := by
    intro y
    show Function.update y i ((y i - g y) / c) i = (y i - g y) / c
    rw [Function.update_apply, if_pos rfl]
  -- The inverse shear is measurable, since `g` is.
  have hTinv_meas : Measurable Tinv := by
    show Measurable (fun y : Fin d → ℝ => Function.update y i ((y i - g y) / c))
    rw [measurable_pi_iff]
    intro j
    have hcoord : (fun y : Fin d → ℝ => Function.update y i ((y i - g y) / c) j)
        = fun y : Fin d → ℝ => if j = i then (y i - g y) / c else y j := by
      funext y
      rw [Function.update_apply]
    rw [hcoord]
    by_cases hj : j = i
    · have : (fun y : Fin d → ℝ => if j = i then (y i - g y) / c else y j)
          = fun y : Fin d → ℝ => (y i - g y) / c := by
        funext y
        rw [if_pos hj]
      rw [this]
      exact ((measurable_pi_apply i).sub hg).div_const c
    · have : (fun y : Fin d → ℝ => if j = i then (y i - g y) / c else y j)
          = fun y : Fin d → ℝ => y j := by
        funext y
        rw [if_neg hj]
      rw [this]
      exact measurable_pi_apply j
  have hupd_self : ∀ (x : Fin d → ℝ) (v : ℝ),
      Function.update (Function.update x i v) i (x i) = x := by
    intro x v
    rw [Function.update_idem, Function.update_eq_self]
  have hgT : ∀ x, g (T x) = g x := by
    intro x
    apply hgi
    intro m hm
    show Function.update x i (c * x i + g x) m = x m
    rw [Function.update_apply, if_neg hm]
  have hgTinv : ∀ y, g (Tinv y) = g y := by
    intro y
    apply hgi
    intro m hm
    show Function.update y i ((y i - g y) / c) m = y m
    rw [Function.update_apply, if_neg hm]
  have hTinv_T : ∀ x, Tinv (T x) = x := by
    intro x
    have hdiv : ((T x) i - g (T x)) / c = x i := by
      rw [hT_apply x, hgT x, div_eq_iff hcne]
      ring
    show Function.update (T x) i (((T x) i - g (T x)) / c) = x
    rw [hdiv]
    show Function.update (Function.update x i (c * x i + g x)) i (x i) = x
    exact hupd_self x (c * x i + g x)
  have hT_Tinv : ∀ y, T (Tinv y) = y := by
    intro y
    have hdiv : c * ((Tinv y) i) + g (Tinv y) = y i := by
      rw [hTinv_apply y, hgTinv y]
      field_simp [hcne]
      ring
    show Function.update (Tinv y) i (c * (Tinv y) i + g (Tinv y)) = y
    rw [hdiv]
    show Function.update (Function.update y i ((y i - g y) / c)) i (y i) = y
    exact hupd_self y ((y i - g y) / c)
  -- `T` is a bijection, so the image of `A` is the preimage of `A` under `Tinv`.
  have hImg : T '' A = Tinv ⁻¹' A := by
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩
      show Tinv (T x) ∈ A
      rw [hTinv_T x]
      exact hx
    · intro hz
      exact ⟨Tinv z, hz, hT_Tinv z⟩
  change MeasureTheory.volume (T '' A) = ENNReal.ofReal c * MeasureTheory.volume A
      ∧ MeasurableSet (T '' A)
  refine ⟨?_, ?_⟩
  · exact shear_volume i hc hg hgi hA
  · rw [hImg]
    exact hA.preimage hTinv_meas

end Work.BW.Minkowski2
