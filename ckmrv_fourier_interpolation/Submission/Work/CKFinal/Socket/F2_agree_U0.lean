import Mathlib
import Submission.Work.CKFinal.Socket.Construction
import Submission.Work.CKFinal.Socket.LadderNoHFN

namespace Work.CKFinal.Socket

open UpperHalfPlane

/-! ## Geometry: `τ ∈ U0 ∩ Wm1` puts `τ + 1` in the fundamental domain `𝒟` with `Re > 0`

This is what allows the first recurrence to be read off from the `T`-ladder identity
`Work.Asymptotics.lh_paperLayer_vadd_ladder_socket` (which is stated at a point `u ∈ 𝒟` with
`Re u > 0`), instead of from `Work.LayerCont.T2op_paperLayer` (which would require contour
cleanliness at the far point `τ + 2`, not available from the definition of the window chart). -/

private lemma vadd_one_im (τ : ℍ) : ((1 : ℝ) +ᵥ τ).im = τ.im := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]
  simp

private lemma norm_sub_half_sq' (x : ℍ) :
    ‖(x : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (x.re - 1 / 2) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_add_half_sq' (x : ℍ) :
    ‖(x : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (x.re + 1 / 2) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- **`τ + 1` lies in `𝒟` with positive real part** whenever `0 < Re τ + 1 < thin (Im τ)`.
The thinness hypothesis is the one carried by `Wm1`; the positivity is what `U0` adds
(`-1 < Re τ`). -/
theorem vadd_one_mem_DomainD {τ : ℍ} (hδ : 0 < τ.re + 1)
    (hthin : |τ.re + 1| < thin τ.im) :
    (1 : ℝ) +ᵥ τ ∈ Work.Asymptotics.DomainD ∧ 0 < ((1 : ℝ) +ᵥ τ).re := by
  have hy : 0 < τ.im := τ.im_pos
  have hthin1 : τ.re + 1 < 1 / 4 := by
    have := lt_of_lt_of_le (abs_lt.mp (lt_of_lt_of_le hthin (thin_le_quarter τ.im))).2 (le_refl _)
    linarith
  have hthinY : τ.re + 1 < τ.im ^ 2 / 4 := by
    have h := lt_of_lt_of_le hthin (thin_le_quarter τ.im)
    have h2 : thin τ.im ≤ τ.im ^ 2 / 4 := by
      rw [thin]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have := abs_lt.mp (lt_of_lt_of_le hthin h2)
    exact this.2
  have hre : ((1 : ℝ) +ᵥ τ).re = τ.re + 1 := vadd_one_re τ
  refine ⟨?_, by rw [hre]; exact hδ⟩
  rw [Work.Asymptotics.mem_DomainD]
  refine ⟨by rw [hre]; linarith, by rw [hre]; linarith, ?_, ?_⟩
  · rw [← Real.sqrt_sq (norm_nonneg _), Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [norm_sub_half_sq', hre, vadd_one_im]
    nlinarith [hδ, hthinY, sq_nonneg (τ.im)]
  · rw [← Real.sqrt_sq (norm_nonneg _), Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [norm_add_half_sq', hre, vadd_one_im]
    nlinarith [hδ, hy]

private lemma vadd_one_add_one' (τ : ℍ) : (2 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) := by
  ext <;> simp [UpperHalfPlane.coe_vadd] <;> ring

private lemma vadd_neg_one_add_one (τ : ℍ) : (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) = τ := by
  ext <;> simp [UpperHalfPlane.coe_vadd] <;> ring

/-- **`F₂` agrees with the paper's layer on `U₀`.**

On `U₀ ∖ Wm1` this is by definition of `F2` (`F2 = G` and `G = layerFn` on `U₀`).

On `U₀ ∩ Wm1` the definition of `F2` reads

`F₂(τ) = 2 G(τ+1) - G(τ+2) - T2op (gaussTerm · r) τ`,

and each term is known: `G(τ+1) = layerFn(τ+1)` (because `τ+1 ∈ U₀`), while at the far point
`τ+2` (with `Re(τ+2) = 1 + (Re τ + 1) > 1`, the thinness in `Wm1` and `-1 < Re τ` forcing the
real part to exceed `1` strictly) the far clause of the window chart gives
`G(τ+2) = layerFn(τ+2) + sinSqC r · resCorr r (τ+2)`, and
`Work.Residues.resCorr_vadd_two` says that the residue correction is exactly
`-T2op (gaussTerm · r) τ`.  Hence `F₂(τ) = 2 layerFn(τ+1) - layerFn(τ+2)`, and the `T`-ladder
identity at `u = τ+1` (which lies in `𝒟` with `Re u > 0`, by the geometry above) gives
`layerFn(τ+2) = 2 layerFn(τ+1) - layerFn(τ)`. -/
theorem F2_agree_U0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    {τ : UpperHalfPlane} (h : τ ∈ Work.CKFinal.U0) :
    Work.CKFinal.Socket.F2 ℓ d hd r τ = Work.CKFinal.Socket.layerFn ℓ d r τ := by
  by_cases hW : τ ∈ Wm1 ℓ d hd
  · obtain ⟨hU1, hW1, hthin⟩ := mem_Wm1.mp hW
    -- the ladder point
    have hδ : 0 < τ.re + 1 := by
      have := (Work.CKFinal.mem_U0_iff.mp h).1
      linarith
    obtain ⟨hD, hreD⟩ := vadd_one_mem_DomainD hδ hthin
    -- `G (τ+1) = layerFn (τ+1)`
    have hG1 : G ℓ d hd r ((1 : ℝ) +ᵥ τ) = layerFn ℓ d r ((1 : ℝ) +ᵥ τ) :=
      G_of_mem_U0 ℓ d hd r hU1
    -- `G (τ+2) = layerFn (τ+2) + sinSqC r * resCorr r (τ+2)`
    obtain ⟨s, hs, hb⟩ := mem_W1.mp hW1
    have hre2 : 1 < ((2 : ℝ) +ᵥ τ).re := by
      rw [vadd_two_re]
      have := (Work.CKFinal.mem_U0_iff.mp h).1
      linarith
    have hG2 : G ℓ d hd r ((2 : ℝ) +ᵥ τ)
        = layerFn ℓ d r ((2 : ℝ) +ᵥ τ)
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r ((2 : ℝ) +ᵥ τ) := by
      rw [G_of_mem_W1 ℓ d hd r hW1, ← chartVal_spec ℓ d hd r hW1 s hs hb]
      exact chartFun_far ℓ d hd s hs r (winBall_subset_eps ℓ d hd s hs hb) hre2
    -- the two algebraic inputs: the residue correction, and the `T`-ladder at `τ + 1`
    have hres := Work.Residues.resCorr_vadd_two r τ
    have hlad := Work.Asymptotics.lh_paperLayer_vadd_ladder_socket ℓ d hd ((1 : ℝ) +ᵥ τ) hD hreD r
    -- the ladder, in the direction used below
    have hladder : layerFn ℓ d r ((2 : ℝ) +ᵥ τ)
        = 2 * layerFn ℓ d r ((1 : ℝ) +ᵥ τ) - layerFn ℓ d r τ := by
      have h := hlad
      simp only [layerFn] at h ⊢
      rw [← vadd_one_add_one' τ, vadd_neg_one_add_one] at h
      exact h
    rw [F2_of_mem_Wm1 ℓ d hd r hW]
    simp only [layerFn] at hG1 hG2 hladder ⊢
    rw [hG1, hG2, hladder, hres]
    ring
  · rw [F2_of_not_mem_Wm1 ℓ d hd r hW, G_of_mem_U0 ℓ d hd r h]

end Work.CKFinal.Socket
