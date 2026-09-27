import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.minkGeoSeg

/-!
# The `cosh`-frame along a geodesic of the hyperboloid

Given two points `P`, `Q` of the hyperboloid model with
`⟨P,P⟩ = ⟨Q,Q⟩ = -1` and `⟨P,Q⟩ = -cosh 1`, the vectors

  `U(s) = cosh s • P + sinh s • V`,  `V = (sinh 1)⁻¹ • (Q - cosh 1 • P)`

form a moving frame along the geodesic through `P` and `Q`: `V` is the unit
spacelike vector orthogonal to `P` pointing from `P` towards `Q`.  The three
pairings `⟨U(s),P⟩`, `⟨U(s),Q⟩`, `⟨U(s),U(t)⟩` are `-cosh s`, `-cosh (s-1)`
and `-cosh (s-t)` respectively; these are the Minkowski-space expressions of
the hyperbolic distance identities `d(U(s),P) = |s|`,
`d(U(s),Q) = |s-1|`, `d(U(s),U(t)) = |s-t|`.

The proof is a direct bilinear-algebra computation: expand `mink` by
bilinearity, use the three given pairings together with `⟨P,V⟩ = 0`,
`⟨V,V⟩ = 1`, `⟨V,Q⟩ = sinh 1`, and reduce the remaining hyperbolic identities
to `cosh² - sinh² = 1` and the addition formula for `cosh`.
-/

namespace Work.Mostow

variable {n : ℕ}

/-! ## Bilinearity helpers for `mink` -/

lemma minkFrame_smul_left (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) y = r * mink x y := by
  have := minkSeg_smul r 1 x y
  simpa using this

lemma minkFrame_smul_right (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x (r • y) = r * mink x y := by
  have := minkSeg_smul 1 r x y
  simpa using this

lemma minkFrame_neg_left (x y : Fin n ⊕ Fin 1 → ℝ) : mink (-x) y = -mink x y := by
  have h : (-x : Fin n ⊕ Fin 1 → ℝ) = (-1 : ℝ) • x := by ext i; simp
  rw [h, minkFrame_smul_left]; ring

lemma minkFrame_neg_right (x y : Fin n ⊕ Fin 1 → ℝ) : mink x (-y) = -mink x y := by
  have h : (-y : Fin n ⊕ Fin 1 → ℝ) = (-1 : ℝ) • y := by ext i; simp
  rw [h, minkFrame_smul_right]; ring

lemma minkFrame_sub_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink (x - y) z = mink x z - mink y z := by
  rw [sub_eq_add_neg, minkSeg_add_left, minkFrame_neg_left]; ring

lemma minkFrame_sub_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink x (y - z) = mink x y - mink x z := by
  rw [sub_eq_add_neg, minkSeg_add_right, minkFrame_neg_right]; ring

lemma minkFrame_add_add (x1 x2 y1 y2 : Fin n ⊕ Fin 1 → ℝ) :
    mink (x1 + x2) (y1 + y2) = mink x1 y1 + mink x1 y2 + mink x2 y1 + mink x2 y2 := by
  rw [minkSeg_add_left, minkSeg_add_right, minkSeg_add_right]; ring

theorem minkCoshFrame {n : ℕ} (P Q : Fin n ⊕ Fin 1 → ℝ)
    (hP : Work.Mostow.mink P P = -1) (hQ : Work.Mostow.mink Q Q = -1)
    (hPQ : Work.Mostow.mink P Q = -Real.cosh 1) :
    (∀ s : ℝ, Work.Mostow.mink
        (Real.cosh s • P + Real.sinh s • ((Real.sinh 1)⁻¹ • (Q - Real.cosh 1 • P))) P
        = -Real.cosh s) ∧
    (∀ s : ℝ, Work.Mostow.mink
        (Real.cosh s • P + Real.sinh s • ((Real.sinh 1)⁻¹ • (Q - Real.cosh 1 • P))) Q
        = -Real.cosh (s - 1)) ∧
    (∀ s t : ℝ, Work.Mostow.mink
        (Real.cosh s • P + Real.sinh s • ((Real.sinh 1)⁻¹ • (Q - Real.cosh 1 • P)))
        (Real.cosh t • P + Real.sinh t • ((Real.sinh 1)⁻¹ • (Q - Real.cosh 1 • P)))
        = -Real.cosh (s - t)) := by
  set V : Fin n ⊕ Fin 1 → ℝ := (Real.sinh 1)⁻¹ • (Q - Real.cosh 1 • P) with hV
  have hs : Real.sinh 1 ≠ 0 := (Real.sinh_pos_iff.mpr one_pos).ne'
  have hQP : mink Q P = -Real.cosh 1 := by rw [minkSeg_comm]; exact hPQ
  have hPV : mink P V = 0 := by
    rw [hV, minkFrame_smul_right, minkFrame_sub_right, minkFrame_smul_right, hPQ, hP]
    ring
  have hVP : mink V P = 0 := by rw [minkSeg_comm]; exact hPV
  have hVQ : mink V Q = Real.sinh 1 := by
    rw [hV, minkFrame_smul_left, minkFrame_sub_left, minkFrame_smul_left, hQ, hPQ]
    have h1 : -1 - Real.cosh 1 * -Real.cosh 1 = Real.sinh 1 ^ 2 := by
      have h := Real.cosh_sq_sub_sinh_sq 1
      nlinarith [h]
    rw [h1, pow_two, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hkey : mink (Q - Real.cosh 1 • P) (Q - Real.cosh 1 • P) = Real.sinh 1 ^ 2 := by
    rw [minkFrame_sub_right, minkFrame_sub_left, minkFrame_sub_left,
        minkFrame_smul_left, minkFrame_smul_right, minkSeg_smul, hQ, hQP, hPQ, hP]
    have h := Real.cosh_sq_sub_sinh_sq 1
    nlinarith [h]
  have hVV : mink V V = 1 := by
    rw [hV, minkSeg_smul, hkey]
    rw [← sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hs)]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have h1 : mink (Real.cosh s • P + Real.sinh s • V) P
        = Real.cosh s * mink P P + Real.sinh s * mink V P := by
      rw [minkSeg_add_left, minkFrame_smul_left, minkFrame_smul_left]
    rw [h1, hP, hVP]; ring
  · intro s
    have h1 : mink (Real.cosh s • P + Real.sinh s • V) Q
        = Real.cosh s * mink P Q + Real.sinh s * mink V Q := by
      rw [minkSeg_add_left, minkFrame_smul_left, minkFrame_smul_left]
    rw [h1, hPQ, hVQ, Real.cosh_sub]; ring
  · intro s t
    have h1 : mink (Real.cosh s • P + Real.sinh s • V) (Real.cosh t • P + Real.sinh t • V)
        = Real.cosh s * Real.cosh t * mink P P + Real.cosh s * Real.sinh t * mink P V
          + Real.sinh s * Real.cosh t * mink V P + Real.sinh s * Real.sinh t * mink V V := by
      rw [minkFrame_add_add, minkSeg_smul, minkSeg_smul, minkSeg_smul, minkSeg_smul]
    rw [h1, hP, hPV, hVP, hVV, Real.cosh_sub]; ring

end Work.Mostow
