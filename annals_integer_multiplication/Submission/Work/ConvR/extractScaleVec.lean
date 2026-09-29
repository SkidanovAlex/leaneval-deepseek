import Mathlib
import Submission.Work.ConvR.scaleFacts
import Submission.Work.ConvR.scaleInject

/-!
# ConvR: extracting a coefficient vector from a list of scaled values

This file proves `Work.ConvR.extractScaleVec`, the "extraction" step which turns a list of
*values* produced by a scaled pointwise map back into the coefficient vector they encode.

The mathematical content is entirely combinatorial: the input stack holds
`u.map cfxVal` (one value per coefficient of `u`), the output stack holds the values `ys`,
and the pointwise relation `List.Forall₂` pairs the `i`-th value of `u` with the `i`-th
value of `ys`, each of which is `cfxVal vᵢ` for some coefficient `vᵢ` satisfying the
scaled-approximation bound.  Since `cfxVal` is injective, the coefficients are determined
and `ys` is literally `(v.map cfxVal)` encoded as a list; the accumulator lemma is
`exists_map_cfxVal_of_forall₂`.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- **Extraction of a coefficient vector from a list of values.**
If `ys` is pointwise paired with `us.map cfxVal` so that the `i`-th pair consists of
`cfxVal uᵢ` and `cfxVal vᵢ` with `R uᵢ vᵢ`, then `ys = v.map cfxVal` for the vector `v` of
the second coordinates, and the same alignment "with default" holds: for every index
`i < us.length` (and hence in particular for `i < r` when `us.length = r`) the pair of
`getD`s satisfies `R` — note that the `getD` defaults can be chosen freely, here `(0,0)`,
because the indices considered are always in range. -/
theorem exists_map_cfxVal_of_forall₂ {R : (ℤ × ℤ) → (ℤ × ℤ) → Prop}
    (us : List (ℤ × ℤ)) :
    ∀ {ys : List HvdH.Val}, List.Forall₂ (fun x y => ∃ z w : ℤ × ℤ, x = cfxVal z ∧
        y = cfxVal w ∧ R z w) (us.map cfxVal) ys →
      ∃ vs : List (ℤ × ℤ), ys = vs.map cfxVal ∧ vs.length = us.length ∧
        ∀ i, i < us.length → R (us.getD i (0, 0)) (vs.getD i (0, 0)) := by
  intro ys h
  induction us generalizing ys with
  | nil =>
    cases h with
    | nil => exact ⟨[], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a us ih =>
    cases h with
    | cons hhead htail =>
      rcases hhead with ⟨z, w, hz, hw, hR⟩
      -- the head value of `ys` is `cfxVal w`, and injectivity of `cfxVal` forces `z = a`
      subst hw
      rw [← (cfxVal_injective_scaleInject hz)] at hR
      obtain ⟨vs, hys, hlen, hP⟩ := ih htail
      refine ⟨w :: vs, by simp [hys], by simp [hlen], ?_⟩
      intro i hi
      cases i with
      | zero => simpa using hR
      | succ j =>
        have hj : j < us.length := by simpa using hi
        simpa using hP j hj

/-- **Scaled extraction.**  Given a coefficient vector `u ∈ C̃◦^r` whose values
`u.map cfxVal` are pointwise paired with a list `ys` of output values — each output being
`cfxVal w` for a coefficient `w` in the disc that satisfies the scaled approximation bound
of `FxLib.scale` against the corresponding coefficient of `u` — the list `ys` is the
encoding `cvecVal v` of a coefficient vector `v ∈ C̃◦^r`, and the scaled bound holds
coefficientwise, i.e. by index. -/
theorem extractScaleVec {p c r : ℕ} {u : List (ℤ × ℤ)} (hu : HvdH.InDiscVec p r u)
    {ys : List HvdH.Val}
    (h : List.Forall₂ (fun x y => ∃ z w : ℤ × ℤ, x = HvdH.cfxVal z ∧ y = HvdH.cfxVal w ∧
        HvdH.inDisc p w ∧
        ∀ x₀ : ℂ, (c : ℝ) * ‖x₀‖ ≤ 1 →
          (2 : ℝ) ^ p * ‖HvdH.fxC p w - (c : ℂ) * x₀‖ <
            2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p z - x₀‖) + 3) (u.map HvdH.cfxVal) ys) :
    ∃ v : List (ℤ × ℤ), HvdH.ofList ys = HvdH.cvecVal v ∧ HvdH.InDiscVec p r v ∧
      ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
        (2 : ℝ) ^ p * ‖HvdH.fxC p (v.getD j (0, 0)) - (c : ℂ) * x‖ <
          2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p (u.getD j (0, 0)) - x‖) + 3 := by
  obtain ⟨v, hys, hlen, hP⟩ := exists_map_cfxVal_of_forall₂ u
    (R := fun z w => inDisc p w ∧ ∀ x₀ : ℂ, (c : ℝ) * ‖x₀‖ ≤ 1 →
      (2 : ℝ) ^ p * ‖fxC p w - (c : ℂ) * x₀‖ <
        2 * c * ((2 : ℝ) ^ p * ‖fxC p z - x₀‖) + 3) h
  refine ⟨v, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- `ys` is a `cfxVal`-image, so its encoding is `cvecVal` of the coefficient vector
    rw [hys]; rfl
  · -- the extracted vector has length `r`
    rw [hlen, hu.1]
  · -- and all its coefficients lie in the disc
    intro z hz
    obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < u.length := by rw [← hlen]; exact hi
    have h1 : inDisc p (v.getD i (0, 0)) := (hP i hi').1
    rw [List.getD_eq_getElem _ _ hi, hiz] at h1
    exact h1
  · -- the scaled bound transfers index by index
    intro j x hx
    have hj : (j : ℕ) < u.length := by rw [hu.1]; exact j.isLt
    exact (hP j hj).2 x hx

end Work.ConvR
