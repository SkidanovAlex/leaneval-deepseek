import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.minkGeoSeg
import Submission.Work.Mostow.minkNullOrthTimelike
import Submission.Work.Mostow.minkCoshFrame

/-!
# A Minkowski line is determined by its two-point function

Let `X : ℝ → ℝ^{Fin n ⊕ Fin 1}` satisfy `⟨X s, X t⟩ = -cosh (s - t)` for the Minkowski form
`mink x y = Σᵢ xᵢ yᵢ - x₀ y₀`.  Then `X` is the unit speed parametrisation of a geodesic line:
for every `s`,

  `X s = cosh s • X 0 + sinh s • ((sinh 1)⁻¹ • (X 1 - cosh 1 • X 0))`.

The proof shows that the difference `Z = X s - Y s` between `X s` and the corresponding point `Y s`
of the geodesic through `X 0` and `X 1` is (i) Minkowski orthogonal to `X s` and (ii) null; since
`X s` is timelike, a null vector orthogonal to it must vanish.

## Main results

* `minkSub_left`, `minkSub_right`, `minkSmul_left`, `minkSmul_right`: bilinearity of `mink`;
* `minkLineDecomp`: the decomposition.
-/

namespace Work.Mostow

variable {n : ℕ}

/-! ## Bilinearity of `mink` for subtraction and scalar multiplication -/

lemma minkSub_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink (x - y) z = mink x z - mink y z := by
  simp only [mink, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring

lemma minkSub_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink x (y - z) = mink x y - mink x z := by
  simp only [mink, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring

lemma minkSmul_left (c : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (c • x) y = c * mink x y := by
  conv_lhs => rw [← one_smul ℝ y]
  rw [minkSeg_smul, mul_one]

lemma minkSmul_right (c : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x (c • y) = c * mink x y := by
  conv_lhs => rw [← one_smul ℝ x]
  rw [minkSeg_smul, one_mul]

theorem minkLineDecomp (n : ℕ) (X : ℝ → Fin n ⊕ Fin 1 → ℝ)
    (hX : ∀ s t : ℝ, Work.Mostow.mink (X s) (X t) = -Real.cosh (s - t)) :
    ∀ s : ℝ, X s = Real.cosh s • X 0 + Real.sinh s •
      ((Real.sinh 1)⁻¹ • (X 1 - Real.cosh 1 • X 0)) := by
  intro s
  set W : Fin n ⊕ Fin 1 → ℝ := (Real.sinh 1)⁻¹ • (X 1 - Real.cosh 1 • X 0) with hW
  have h00 : mink (X 0) (X 0) = -1 := by
    have h := hX 0 0; rw [sub_self, Real.cosh_zero] at h; exact h
  have h11 : mink (X 1) (X 1) = -1 := by
    have h := hX 1 1; rw [sub_self, Real.cosh_zero] at h; exact h
  have h01 : mink (X 0) (X 1) = -Real.cosh 1 := by
    have h := hX 0 1; rw [zero_sub, Real.cosh_neg] at h; exact h
  obtain ⟨hf1, hf2, hf3⟩ := minkCoshFrame (X 0) (X 1) h00 h11 h01
  have hss : mink (X s) (X s) = -1 := by
    have h := hX s s; rw [sub_self, Real.cosh_zero] at h; exact h
  have hY0 : mink (Real.cosh s • X 0 + Real.sinh s • W) (X 0) = -Real.cosh s := by
    have h := hf1 s; rwa [← hW] at h
  have hY1 : mink (Real.cosh s • X 0 + Real.sinh s • W) (X 1) = -Real.cosh (s - 1) := by
    have h := hf2 s; rwa [← hW] at h
  have hYY : mink (Real.cosh s • X 0 + Real.sinh s • W)
      (Real.cosh s • X 0 + Real.sinh s • W) = -1 := by
    have h := hf3 s s; rw [sub_self, Real.cosh_zero] at h; rwa [← hW] at h
  have hZ0 : mink (X s - (Real.cosh s • X 0 + Real.sinh s • W)) (X 0) = 0 := by
    rw [minkSub_left]
    have h := hX s 0; rw [sub_zero] at h
    rw [h, hY0]; ring
  have hZ1 : mink (X s - (Real.cosh s • X 0 + Real.sinh s • W)) (X 1) = 0 := by
    rw [minkSub_left]; rw [hX s 1, hY1]; ring
  have hZW : mink (X s - (Real.cosh s • X 0 + Real.sinh s • W)) W = 0 := by
    rw [hW, minkSmul_right, minkSub_right, minkSmul_right, hZ1, hZ0]; ring
  have hZYe : mink (X s - (Real.cosh s • X 0 + Real.sinh s • W))
      (Real.cosh s • X 0 + Real.sinh s • W) = 0 := by
    rw [minkSeg_add_right, minkSmul_right, minkSmul_right, hZ0, hZW]; ring
  have hXY : mink (X s) (Real.cosh s • X 0 + Real.sinh s • W) = -1 := by
    have hsplit : X s = (X s - (Real.cosh s • X 0 + Real.sinh s • W))
        + (Real.cosh s • X 0 + Real.sinh s • W) := (sub_add_cancel _ _).symm
    rw [hsplit, minkSeg_add_left, hZYe, hYY]; ring
  have hZX : mink (X s - (Real.cosh s • X 0 + Real.sinh s • W)) (X s) = 0 := by
    rw [minkSub_left, hss, minkSeg_comm, hXY]; ring
  have hZZ : mink (X s - (Real.cosh s • X 0 + Real.sinh s • W))
      (X s - (Real.cosh s • X 0 + Real.sinh s • W)) = 0 := by
    rw [minkSub_right, hZX, hZYe]; ring
  have hZeq : X s - (Real.cosh s • X 0 + Real.sinh s • W) = 0 :=
    minkNullOrthTimelike (X s) (X s - (Real.cosh s • X 0 + Real.sinh s • W)) hss hZX hZZ
  rw [sub_eq_zero] at hZeq
  rw [hZeq, hW]

end Work.Mostow
