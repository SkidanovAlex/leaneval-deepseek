/-
# A `T`-triple of `S`-shifted points in the socket lies in `U₀`

`O = U₀ ∪ W₁ ∪ W₋₁` is the socket region (`Socket.O`).  The second recurrence
`S₂(F) = 0` for the socket layer reads `F` at the three points `S • τ`, `S • (τ+1)`, `S • (τ+2)`;
those are not a translate-triple, but in the coordinate `S • τ = x` they are `x`, `x/(1-x)`,
`x/(1-2x)` — an orbit of the parabolic Möbius map `A = S T S⁻¹`, which in the reciprocal
coordinate `1/x` is just translation by `-1`.

The lemma below records the geometry that makes the second recurrence reduce to the *paper* layer:
a triple `x, A x, A²x` lying in the socket already lies in `U₀` (where `F₂` agrees with the paper
layer).

The proof is a case analysis on the three pieces of `O`, using two kinds of input.

* *Shape lemmas*: a point of `W₁` with `Re < 1` lies in `U₀` (`Socket.mem_U0_of_W1_shape`), and a
  point of `W₋₁` with `Re > -1` lies in `U₀` (`Socket.mem_U0_of_Wm1_shape`).
* *Image-of-half-plane lemmas*: the Möbius maps `w ↦ w/(1-2w)`, `w ↦ w/(1+2w)`, `w ↦ w/(1+w)` of
  the half-planes `Re ≥ 1`, `Re ≤ -1` land in *closed* Farey discs of radius `1/4`; a point of such
  a closed disc, and its translate by `+1`, are outside `U₀`, which contradicts the hypothesis.

The chain of implications is: `x ∈ O ∧ z ∈ O ⟹ x ∈ U₀`; then `z ∈ O ∧ x ∈ U₀ ⟹ z ∈ U₀`; then
`y ∈ O ∧ x, z ∈ U₀ ⟹ y ∈ U₀`.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Region
import Submission.Work.CKFinal.Socket.T_triple_mem_Wm1
import Submission.Work.CKFinal.Socket.mem_U0_of_W1_shape
import Submission.Work.CKFinal.Socket.mem_U0_of_Wm1_shape
import Submission.Work.CKFinal.Socket.disc_A2_ge
import Submission.Work.CKFinal.Socket.disc_B2_ge
import Submission.Work.CKFinal.Socket.disc_B_ge

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-! ## The three points in coordinates -/

/-- **`S` of a translate.**  Writing `S • σ = -1/σ`, a shift of `σ` by `m ∈ ℝ` corresponds to
`S • (m +ᵥ σ) = (S • σ) / (1 - m (S • σ))` in `ℂ`. -/
lemma S_smul_vadd_coe (m : ℝ) (σ : ℍ) :
    ((ModularGroup.S • (m +ᵥ σ) : ℍ) : ℂ)
      = ((ModularGroup.S • σ : ℍ) : ℂ) / (1 - (m : ℂ) * ((ModularGroup.S • σ : ℍ) : ℂ)) := by
  rw [Work.Kernels.S_smul_coe, Work.Kernels.S_smul_coe, UpperHalfPlane.coe_vadd]
  have hw : (σ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero σ
  have hwm : (σ : ℂ) + (m : ℂ) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (m : ℂ)).im = 0 := by rw [h]; simp
    rw [Complex.add_im, Complex.ofReal_im, add_zero] at him
    exact absurd him (ne_of_gt (UpperHalfPlane.im_pos σ))
  field_simp
  ring

/-! ## The image-of-half-plane lemmas for `Re ≤ -1` -/

/-- The mirror of `Socket.disc_A2_ge`: for `Re w ≤ -1` the point `w/(1-2w)` lies in the closed
disc of radius `1/4` about `-1/4`.  It is `disc_A2_ge` applied to `-w`. -/
lemma disc_A2_le (w : ℂ) (h : w.re ≤ -1) : ‖w / (1 - 2 * w) + 1 / 4‖ ≤ 1 / 4 := by
  have h' : 1 ≤ (-w).re := by simp; linarith
  have hb := disc_B2_ge (-w) h'
  rw [show (1 : ℂ) + 2 * (-w) = 1 - 2 * w by ring] at hb
  have h2 : (-w) / (1 - 2 * w) - 1 / 4 = -(w / (1 - 2 * w) + 1 / 4) := by ring
  rw [h2, norm_neg] at hb
  exact hb

/-- The mirror of `Socket.disc_A2_ge`: for `Re w ≤ -1` the point `w/(1+2w)` lies in the closed
disc of radius `1/4` about `3/4`.  It is `disc_A2_ge` applied to `-w`. -/
lemma disc_B2_le (w : ℂ) (h : w.re ≤ -1) : ‖w / (1 + 2 * w) - 3 / 4‖ ≤ 1 / 4 := by
  have h' : 1 ≤ (-w).re := by simp; linarith
  have hb := disc_A2_ge (-w) h'
  rw [show (1 : ℂ) - 2 * (-w) = 1 + 2 * w by ring] at hb
  have h2 : (-w) / (1 + 2 * w) + 3 / 4 = -(w / (1 + 2 * w) - 3 / 4) := by ring
  rw [h2, norm_neg] at hb
  exact hb

/-- The mirror of `Socket.disc_B_ge`: for `Re w ≤ -1` the point `w/(1-w)` lies in the closed disc
of radius `1/4` about `-3/4`.  It is `disc_B_ge` applied to `-w`. -/
lemma disc_B_le (w : ℂ) (h : w.re ≤ -1) : ‖w / (1 - w) + 3 / 4‖ ≤ 1 / 4 := by
  have h' : 1 ≤ (-w).re := by simp; linarith
  have hb := disc_B_ge (-w) h'
  rw [show (1 : ℂ) + (-w) = 1 - w by ring] at hb
  have h2 : (-w) / (1 - w) - 3 / 4 = -(w / (1 - w) + 3 / 4) := by ring
  rw [h2, norm_neg] at hb
  exact hb

/-! ## Small coordinate lemmas -/

/-- If `‖w + 3/4‖ ≤ 1/4` then `Re w ≤ 0`. -/
lemma re_nonpos_of_norm_add_three_quarters {w : ℂ} (h : ‖w + 3 / 4‖ ≤ 1 / 4) : w.re ≤ 0 := by
  have h1 : |(w + 3 / 4).re| ≤ ‖w + 3 / 4‖ := Complex.abs_re_le_norm _
  have h2 : (w + 3 / 4).re = w.re + 3 / 4 := by
    simp only [Complex.add_re]
    norm_num
  have h3 := (abs_le.mp (le_trans h1 h)).2
  rw [h2] at h3
  linarith

/-- If `‖w + 1/4‖ ≤ 1/4` then `Re w ≤ 0`. -/
lemma re_nonpos_of_norm_add_quarter {w : ℂ} (h : ‖w + 1 / 4‖ ≤ 1 / 4) : w.re ≤ 0 := by
  have h1 : |(w + 1 / 4).re| ≤ ‖w + 1 / 4‖ := Complex.abs_re_le_norm _
  have h2 : (w + 1 / 4).re = w.re + 1 / 4 := by
    simp only [Complex.add_re]
    norm_num
  have h3 := (abs_le.mp (le_trans h1 h)).2
  rw [h2] at h3
  linarith

/-- `(1 +ᵥ z) - 1/4 = z + 3/4` in `ℂ`. -/
lemma coe_one_vadd_sub_quarter (z : ℍ) :
    (((1 : ℝ) +ᵥ z : ℍ) : ℂ) - 1 / 4 = (z : ℂ) + 3 / 4 := by
  rw [UpperHalfPlane.coe_vadd]; push_cast; ring

/-- `(1 +ᵥ z) - 3/4 = z + 1/4` in `ℂ`. -/
lemma coe_one_vadd_sub_threequarter (z : ℍ) :
    (((1 : ℝ) +ᵥ z : ℍ) : ℂ) - 3 / 4 = (z : ℂ) + 1 / 4 := by
  rw [UpperHalfPlane.coe_vadd]; push_cast; ring

/-! ## The main lemma -/

/-- **The three `S`-shifted points of a `T`-triple in the socket lie in `U₀`.** -/
theorem F2_S2op_triple_U0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : UpperHalfPlane} (h1 : ModularGroup.S • τ ∈ Work.CKFinal.Socket.O ℓ d hd)
    (h2 : ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.CKFinal.Socket.O ℓ d hd)
    (h3 : ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ Work.CKFinal.Socket.O ℓ d hd) :
    ModularGroup.S • τ ∈ Work.CKFinal.U0 ∧
      ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.CKFinal.U0 ∧
      ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ Work.CKFinal.U0 := by
  -- name the three points (this also rewrites `h1`, `h2`, `h3`)
  set X : ℍ := ModularGroup.S • τ with hX
  set Y : ℍ := ModularGroup.S • ((1 : ℝ) +ᵥ τ) with hY
  set Z : ℍ := ModularGroup.S • ((2 : ℝ) +ᵥ τ) with hZ
  -- the parabolic relation between the three points
  have hXZ : (Z : ℂ) = (X : ℂ) / (1 - 2 * (X : ℂ)) := by
    have h := S_smul_vadd_coe 2 τ
    rw [← hX, ← hZ] at h
    simpa using h
  have hZX : (X : ℂ) = (Z : ℂ) / (1 + 2 * (Z : ℂ)) := by
    have h := S_smul_vadd_coe (-2) ((2 : ℝ) +ᵥ τ)
    rw [show ((-2 : ℝ) +ᵥ ((2 : ℝ) +ᵥ τ)) = τ by rw [← add_vadd]; norm_num] at h
    rw [← hX, ← hZ] at h
    simpa using h
  have hYX : (X : ℂ) = (Y : ℂ) / (1 + (Y : ℂ)) := by
    have h := S_smul_vadd_coe (-1) ((1 : ℝ) +ᵥ τ)
    rw [show ((-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) = τ by rw [← add_vadd]; norm_num] at h
    rw [← hX, ← hY] at h
    simpa using h
  have hZY : (Z : ℂ) = (Y : ℂ) / (1 - (Y : ℂ)) := by
    have h := S_smul_vadd_coe 1 ((1 : ℝ) +ᵥ τ)
    rw [show ((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) = ((2 : ℝ) +ᵥ τ) by rw [← add_vadd]; norm_num] at h
    rw [← hZ, ← hY] at h
    simpa using h
  -- ## Step 1: `X ∈ U₀`
  have hXU0 : X ∈ U0 := by
    rw [O] at h1
    rcases h1 with (h1 | h1) | h1
    · exact h1
    · -- `X ∈ W₁`
      by_cases hlt : X.re < 1
      · exact mem_U0_of_W1_shape (W1_re_bounds h1).1 hlt (W1_thin h1)
      · exfalso
        have hge : (1 : ℝ) ≤ X.re := not_lt.mp hlt
        have hdisc : ‖(Z : ℂ) + 3 / 4‖ ≤ 1 / 4 := by
          rw [hXZ]; exact disc_A2_ge (X : ℂ) (by simpa using hge)
        have hZre : Z.re ≤ 0 := re_nonpos_of_norm_add_three_quarters hdisc
        rw [O] at h3
        rcases h3 with (h3 | h3) | h3
        · have hc := (Work.CKFinal.mem_U0_iff.mp h3).2.2.2.2.2
          linarith
        · have hc := (W1_re_bounds h3).1
          linarith
        · have hc := (Work.CKFinal.mem_U0_iff.mp (mem_Wm1.mp h3).1).2.2.1
          have hdisc' : ‖(((1 : ℝ) +ᵥ Z : ℍ) : ℂ) - 1 / 4‖ ≤ 1 / 4 := by
            rw [coe_one_vadd_sub_quarter Z]; exact hdisc
          linarith
    · -- `X ∈ W₋₁`
      by_cases hlt : -1 < X.re
      · exact mem_U0_of_Wm1_shape hlt (Wm1_re_bounds h1).2 (mem_Wm1.mp h1).2.2
      · exfalso
        have hle : X.re ≤ -1 := not_lt.mp hlt
        have hdisc : ‖(Z : ℂ) + 1 / 4‖ ≤ 1 / 4 := by
          rw [hXZ]; exact disc_A2_le (X : ℂ) (by simpa using hle)
        have hZre : Z.re ≤ 0 := re_nonpos_of_norm_add_quarter hdisc
        rw [O] at h3
        rcases h3 with (h3 | h3) | h3
        · have hc := (Work.CKFinal.mem_U0_iff.mp h3).2.2.2.1
          linarith
        · have hc := (W1_re_bounds h3).1
          linarith
        · have hc := (Work.CKFinal.mem_U0_iff.mp (mem_Wm1.mp h3).1).2.2.2.2.1
          have hdisc' : ‖(((1 : ℝ) +ᵥ Z : ℍ) : ℂ) - 3 / 4‖ ≤ 1 / 4 := by
            rw [coe_one_vadd_sub_threequarter Z]; exact hdisc
          linarith
  -- ## Step 2: `Z ∈ U₀`
  have hZU0 : Z ∈ U0 := by
    rw [O] at h3
    rcases h3 with (h3 | h3) | h3
    · exact h3
    · -- `Z ∈ W₁`
      by_cases hlt : Z.re < 1
      · exact mem_U0_of_W1_shape (W1_re_bounds h3).1 hlt (W1_thin h3)
      · exfalso
        have hge : (1 : ℝ) ≤ Z.re := not_lt.mp hlt
        have hdisc : ‖(X : ℂ) - 1 / 4‖ ≤ 1 / 4 := by
          rw [hZX]; exact disc_B2_ge (Z : ℂ) (by simpa using hge)
        have hc := (Work.CKFinal.mem_U0_iff.mp hXU0).2.2.1
        linarith
    · -- `Z ∈ W₋₁`
      by_cases hlt : -1 < Z.re
      · exact mem_U0_of_Wm1_shape hlt (Wm1_re_bounds h3).2 (mem_Wm1.mp h3).2.2
      · exfalso
        have hle : Z.re ≤ -1 := not_lt.mp hlt
        have hdisc : ‖(X : ℂ) - 3 / 4‖ ≤ 1 / 4 := by
          rw [hZX]; exact disc_B2_le (Z : ℂ) (by simpa using hle)
        have hc := (Work.CKFinal.mem_U0_iff.mp hXU0).2.2.2.2.1
        linarith
  -- ## Step 3: `Y ∈ U₀`
  have hYU0 : Y ∈ U0 := by
    rw [O] at h2
    rcases h2 with (h2 | h2) | h2
    · exact h2
    · -- `Y ∈ W₁`
      by_cases hlt : Y.re < 1
      · exact mem_U0_of_W1_shape (W1_re_bounds h2).1 hlt (W1_thin h2)
      · exfalso
        have hge : (1 : ℝ) ≤ Y.re := not_lt.mp hlt
        have hdisc : ‖(X : ℂ) - 3 / 4‖ ≤ 1 / 4 := by
          rw [hYX]; exact disc_B_ge (Y : ℂ) (by simpa using hge)
        have hc := (Work.CKFinal.mem_U0_iff.mp hXU0).2.2.2.2.1
        linarith
    · -- `Y ∈ W₋₁`
      by_cases hlt : -1 < Y.re
      · exact mem_U0_of_Wm1_shape hlt (Wm1_re_bounds h2).2 (mem_Wm1.mp h2).2.2
      · exfalso
        have hle : Y.re ≤ -1 := not_lt.mp hlt
        have hdisc : ‖(Z : ℂ) + 3 / 4‖ ≤ 1 / 4 := by
          rw [hZY]; exact disc_B_le (Y : ℂ) (by simpa using hle)
        have hc := (Work.CKFinal.mem_U0_iff.mp hZU0).2.2.2.2.2
        linarith
  exact ⟨hXU0, hYU0, hZU0⟩

end Socket
end Work.CKFinal
