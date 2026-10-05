import Mathlib
import Submission.Work.RPB.B5.noL_defs
import Submission.Work.RPB.B5.signedArea_scale_shift

namespace Work.RPB.B5

/-!
# Geometry of the far shape `fsh`

The far shape of the no-level-data collar is
`fsh CI δ k τ σ t = (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ)`:
a real homothety (factor `rd σ = √(2+2σ)`) of the curve `CI.c` at the *reparametrised* time
`rpf δ σ * τ` (which lands in `[0,1]` whenever `τ ∈ [0,1]`, since `rpf δ σ ∈ [0,1]`), together
with a shift of the parameter by `phc δ k σ`.

Each of the three conclusions is therefore inherited from the corresponding field of
`CurveIsotopy`:

* the signed area from `signedArea_scale_shift` (scale by `rd σ`, shift by `phc δ k σ`) together
  with `rd σ ^ 2 = 2 + 2σ`;
* the nonvanishing of the derivative from `CI.imm`, after `deriv_const_mul_field` and
  `deriv_comp_add_const`, using `rd σ ≠ 0`;
* the injectivity up to `2πℤ` from `CI.inj`, after cancelling the nonzero factor `rd σ`.
-/

/-- The far shape, unfolded. -/
private lemma fsh_pointwise (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (τ σ : ℝ) :
    ∀ t : ℝ, Work.RPB.B5.fsh CI δ k τ σ t
      = (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ) := by
  intro t
  unfold Work.RPB.B5.fsh
  rfl

private lemma rpf_nonneg (δ σ : ℝ) : 0 ≤ rpf δ σ := by
  have h := stp_le_one ((σ - δ) / δ)
  simp only [rpf]
  linarith

private lemma rpf_le_one (δ σ : ℝ) : rpf δ σ ≤ 1 := by
  have h := stp_nonneg ((σ - δ) / δ)
  simp only [rpf]
  linarith

private lemma rd_ne_zero {σ : ℝ} (hσ : 0 ≤ σ) : rd σ ≠ 0 := by
  have h : 0 < 2 + 2 * σ := by linarith
  unfold rd
  exact ne_of_gt (Real.sqrt_pos.2 h)

private lemma rd_sq {σ : ℝ} (hσ : 0 ≤ σ) : (rd σ) ^ 2 = 2 + 2 * σ := by
  have h : 0 ≤ 2 + 2 * σ := by linarith
  unfold rd
  rw [Real.sq_sqrt h]

private lemma rd_mul_le_one (δ τ σ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    rpf δ σ * τ ≤ 1 :=
  le_trans (mul_le_of_le_one_left hτ0 (rpf_le_one δ σ)) hτ1

theorem noL_fsh_geom (CI : Work.RPV.CurveIsotopy) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 0 ≤ σ →
      Work.RPB.signedArea (fun t : ℝ => Work.RPB.B5.fsh CI δ k τ σ t)
          = 2 * Real.pi * (1 + σ) ∧
      (∀ t : ℝ, deriv (fun u : ℝ => Work.RPB.B5.fsh CI δ k τ σ u) t ≠ 0) ∧
      (∀ t t' : ℝ, Work.RPB.B5.fsh CI δ k τ σ t = Work.RPB.B5.fsh CI δ k τ σ t' →
        ∃ m : ℤ, t' = t + 2 * Real.pi * m) := by
  intro τ hτ σ hσ
  -- `δ > 0` is not needed: `rpf δ σ ∈ [0,1]` holds for every `δ`
  have _ := hδ
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  have hτ1 : τ ≤ 1 := hτ.2
  have hfsh := fsh_pointwise CI δ k τ σ
  have hfun : (fun t : ℝ => Work.RPB.B5.fsh CI δ k τ σ t)
      = fun t : ℝ => (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ) := funext hfsh
  -- the reparametrised time stays in `[0,1]`
  have hρ : rpf δ σ * τ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (rpf_nonneg δ σ) hτ0, rd_mul_le_one δ τ σ hτ0 hτ1⟩
  have hRd : rd σ ≠ 0 := rd_ne_zero hσ
  have hRdC : (rd σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRd
  refine ⟨?_, ?_, ?_⟩
  · -- signed area
    rw [hfun, Work.RPB.B5.signedArea_scale_shift CI (rpf δ σ * τ) (rd σ) (phc δ k σ) hρ,
      rd_sq hσ]
    ring
  · -- nonvanishing derivative
    intro t
    rw [hfun, deriv_const_mul_field, deriv_comp_add_const]
    exact mul_ne_zero hRdC (CI.imm (rpf δ σ * τ) hρ (t + phc δ k σ))
  · -- injectivity up to `2πℤ`
    intro t t' h
    have h2 : (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ)
        = (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t' + phc δ k σ) := by
      simpa only [hfsh] using h
    have h3 : CI.c (rpf δ σ * τ) (t + phc δ k σ)
        = CI.c (rpf δ σ * τ) (t' + phc δ k σ) := mul_left_cancel₀ hRdC h2
    obtain ⟨m, hm⟩ := CI.inj (rpf δ σ * τ) hρ (t + phc δ k σ) (t' + phc δ k σ) h3
    exact ⟨m, by linarith⟩

end Work.RPB.B5
