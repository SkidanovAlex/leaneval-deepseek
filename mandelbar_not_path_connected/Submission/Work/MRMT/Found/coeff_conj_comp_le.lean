import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo
import Submission.Work.MRMT.Found.dz_star_comp
import Submission.Work.MRMT.Found.dzbar_star_comp
import Submission.Work.MRMT.Sobolev.QCCompAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Pointwise dilatation estimate for the conjugate pull-back `conj ∘ F ∘ f ∘ F⁻¹`

Let `F : ℂ ≃ₜ ℂ` be a `C¹` diffeomorphism of the plane whose complex dilatation is the
field `μF` (`∂̄F = μF · ∂F` everywhere, with `‖μF‖ ≤ k < 1`), and let `f` be
anti-holomorphic (`star ∘ f` is complex differentiable).  Writing

`G = star ∘ F ∘ f ∘ F.symm`

this file proves the pointwise estimate

`‖∂̄G(w)‖ (1 - k²) ≤ ‖∂G(w)‖ · ‖conj(μF (f a)) · ∂̄f(a) / conj(∂̄f(a)) - μF(a)‖`,  `a = F⁻¹ w`

(statement `Work.MRMT.Found.coeff_conj_comp_le`).

The mathematical content is a chain-rule computation.  With `α = ∂F(a)`, `A = ∂F(f a)`,
`r = ∂̄f(a)`, `μ_a = μF a`, `μ_b = μF (f a)` and `D = det (DF(a))`, the Wirtinger chain rules
(`Work.MRMT.Wirtinger.dz_comp`, `dzbar_comp`) and the inversion of the Beltrami relation give
the two *exact* identities

`D · ∂̄G(w) = α · (A · (μ_b r) - μ_a · (A · conj r))`,
`D · ∂G(w)  = conj α · (A · conj r - conj μ_a · (A · conj μ_b · r))`,

i.e. `D ∂̄G(w) = α A conj r · C` and `D ∂G(w) = conj α A conj r · (1 - conj μ_a conj μ_b r / conj r)`
with `C = conj μ_b r / conj r - μ_a`.  Taking norms and using `D > 0`, together with
`‖1 - conj μ_a conj μ_b r / conj r‖ ≥ 1 - k²`, gives the claim.

Since `F` is a `C¹` *diffeomorphism*, `D = det (DF(a)) ≠ 0` (in fact `D > 0`): the inverse is
`C¹` as well, so `DF(F⁻¹w) ∘ DF(a) = id` and `DF(a) ≠ 0`, which with the pointwise Beltrami
relation and `det DF = ‖∂F‖²(1 - ‖μF‖²)` forces `det DF(a) > 0`.
-/

noncomputable section

open Complex Function

namespace Work.MRMT.Found

/-- For a `C¹` homeomorphism `F : ℂ ≃ₜ ℂ` whose inverse is `C¹` as well, the real Fréchet
derivative of `F` is nowhere zero.  (Chain rule applied to `F.symm ∘ F = id`.) -/
theorem fderiv_ne_zero_of_contDiff_homeomorph (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ))) (a : ℂ) :
    fderiv ℝ (F : ℂ → ℂ) a ≠ 0 := by
  intro h0
  have hdF : DifferentiableAt ℝ (F : ℂ → ℂ) a := hF.contDiffAt.differentiableAt (by norm_num)
  have hdFs : DifferentiableAt ℝ (F.symm : ℂ → ℂ) ((F : ℂ → ℂ) a) :=
    hFs.contDiffAt.differentiableAt (by norm_num)
  have hcomp : ((F.symm : ℂ → ℂ) ∘ (F : ℂ → ℂ)) = id := by
    funext z; simp [Function.comp_apply]
  have hchain : fderiv ℝ ((F.symm : ℂ → ℂ) ∘ (F : ℂ → ℂ)) a
      = (fderiv ℝ (F.symm : ℂ → ℂ) ((F : ℂ → ℂ) a)) ∘SL (fderiv ℝ (F : ℂ → ℂ) a) :=
    fderiv_comp a hdFs hdF
  have h1 : ((fderiv ℝ (F.symm : ℂ → ℂ) ((F : ℂ → ℂ) a)) ∘SL (fderiv ℝ (F : ℂ → ℂ) a)) 1 = 1 := by
    rw [← hchain, hcomp, fderiv_id]; rfl
  rw [h0] at h1
  simp at h1

/-- The determinant of the derivative of a `C¹` diffeomorphism with pointwise Beltrami
relation `∂̄F = μF · ∂F` and `‖μF‖ ≤ k < 1` is strictly positive. -/
theorem det_pos_of_beltrami_homeomorph {F : ℂ ≃ₜ ℂ} {μF : ℂ → ℂ} {k : ℝ} (hk1 : k < 1)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hbelt : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μF z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (hμ : ∀ z : ℂ, ‖μF z‖ ≤ k) (a : ℂ) : 0 < (fderiv ℝ (F : ℂ → ℂ) a).det := by
  have hne : fderiv ℝ (F : ℂ → ℂ) a ≠ 0 := fderiv_ne_zero_of_contDiff_homeomorph F hF hFs a
  have hdet := Work.MRMT.Sobolev.det_fderiv_eq (F : ℂ → ℂ) a
  have hμa : ‖μF a‖ < 1 := lt_of_le_of_lt (hμ a) hk1
  have hfac : (fderiv ℝ (F : ℂ → ℂ) a).det
      = ‖Work.MRMT.dz (F : ℂ → ℂ) a‖ ^ 2 * (1 - ‖μF a‖ ^ 2) := by
    rw [hdet, hbelt a, norm_mul]; ring
  have hpos : 0 < 1 - ‖μF a‖ ^ 2 := by nlinarith [hμa, norm_nonneg (μF a)]
  have hnn : 0 ≤ (fderiv ℝ (F : ℂ → ℂ) a).det := by
    rw [hfac]; exact mul_nonneg (sq_nonneg _) hpos.le
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hz : Work.MRMT.dz (F : ℂ → ℂ) a = 0 := by
      have h2 : ‖Work.MRMT.dz (F : ℂ → ℂ) a‖ ^ 2 * (1 - ‖μF a‖ ^ 2) = 0 := by
        rw [← hfac]; exact h.symm
      have h3 : ‖Work.MRMT.dz (F : ℂ → ℂ) a‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h2 with h' | h'
        · exact h'
        · exact absurd h' (ne_of_gt hpos)
      have h4 : ‖Work.MRMT.dz (F : ℂ → ℂ) a‖ = 0 := sq_eq_zero_iff.mp h3
      exact norm_eq_zero.mp h4
    have hzb : Work.MRMT.dzbar (F : ℂ → ℂ) a = 0 := by rw [hbelt a, hz, mul_zero]
    apply hne
    ext v
    rw [Work.MRMT.Wirtinger.fderiv_apply_eq]
    change Work.MRMT.dz (F : ℂ → ℂ) a * v + Work.MRMT.dzbar (F : ℂ → ℂ) a * star v = 0
    rw [hz, hzb]; simp

/-- Elementary norm bound: for `‖μa‖ ≤ k`, `‖μb‖ ≤ k`, `k ≥ 0`,
`1 - k² ≤ ‖1 - conj μa · conj μb · r / conj r‖`. -/
theorem one_sub_sq_le_norm_aux {μa μb r : ℂ} {k : ℝ} (hk0 : 0 ≤ k)
    (ha : ‖μa‖ ≤ k) (hb : ‖μb‖ ≤ k) :
    1 - k ^ 2 ≤ ‖1 - star μa * star μb * r / star r‖ := by
  have hr : ‖r / star r‖ ≤ 1 := by
    rw [norm_div, norm_star]
    rcases eq_or_ne r 0 with h | h
    · rw [h]; simp
    · rw [div_self (norm_ne_zero_iff.mpr h)]
  have hnorm : ‖star μa * star μb * r / star r‖ ≤ k ^ 2 := by
    have heq : ‖star μa * star μb * r / star r‖ = ‖μa‖ * ‖μb‖ * ‖r / star r‖ := by
      rw [show star μa * star μb * r / star r = star μa * star μb * (r / star r) by ring]
      rw [norm_mul, norm_mul, norm_star, norm_star]
    rw [heq]
    calc ‖μa‖ * ‖μb‖ * ‖r / star r‖ ≤ k * k * 1 := by
          apply mul_le_mul
          · exact mul_le_mul ha hb (norm_nonneg _) hk0
          · exact hr
          · exact norm_nonneg _
          · exact mul_nonneg hk0 hk0
      _ = k ^ 2 := by ring
  have h1 : 1 - ‖star μa * star μb * r / star r‖ ≤ ‖1 - star μa * star μb * r / star r‖ := by
    have := norm_add_le ((1:ℂ) - star μa * star μb * r / star r) (star μa * star μb * r / star r)
    simp only [sub_add_cancel, norm_one] at this
    linarith
  linarith [h1, hnorm]

/-- **Inverse-composition identity for `∂̄`.**  If `U = W ∘ F` and `F` satisfies the Beltrami
relation `∂̄F = μF ∂F` at `a`, then

`det(DF a) · ∂̄W (F a) = ∂F(a) · (∂̄U a - μF a · ∂U a)`.

This is the chain rule for `W = U ∘ F.symm` combined with the linear algebra
`c·(∂̄U) - d·(∂U) = ∂̄W·(c conj c - d conj d)` (`c = ∂F a`, `d = ∂̄F a = μF a · c`). -/
theorem det_mul_dzbar_of_eq_comp {F U W μF : ℂ → ℂ} {a : ℂ}
    (hFa : DifferentiableAt ℝ F a) (hdW : DifferentiableAt ℝ W (F a)) (hUeq : U = W ∘ F)
    (hrel : Work.MRMT.dzbar F a = μF a * Work.MRMT.dz F a) :
    ((fderiv ℝ F a).det : ℂ) * Work.MRMT.dzbar W (F a)
      = Work.MRMT.dz F a * (Work.MRMT.dzbar U a - μF a * Work.MRMT.dz U a) := by
  have hdz := Work.MRMT.Wirtinger.dz_comp (f := F) (g := W) hdW hFa
  have hdzbar := Work.MRMT.Wirtinger.dzbar_comp (f := F) (g := W) hdW hFa
  rw [← hUeq] at hdz hdzbar
  have hdet : ((fderiv ℝ F a).det : ℂ)
      = Work.MRMT.dz F a * star (Work.MRMT.dz F a)
        - Work.MRMT.dzbar F a * star (Work.MRMT.dzbar F a) := by
    rw [Work.MRMT.Sobolev.det_fderiv_eq, Complex.ofReal_sub]
    congr 1 <;> simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hdet, hdzbar, hdz, hrel, star_mul]
  ring

/-- **Inverse-composition identity for `∂`.**  If `U = W ∘ F` and `F` satisfies the Beltrami
relation `∂̄F = μF ∂F` at `a`, then

`det(DF a) · ∂W (F a) = conj(∂F a) · (∂U a - conj(μF a) · ∂̄U a)`. -/
theorem det_mul_dz_of_eq_comp {F U W μF : ℂ → ℂ} {a : ℂ}
    (hFa : DifferentiableAt ℝ F a) (hdW : DifferentiableAt ℝ W (F a)) (hUeq : U = W ∘ F)
    (hrel : Work.MRMT.dzbar F a = μF a * Work.MRMT.dz F a) :
    ((fderiv ℝ F a).det : ℂ) * Work.MRMT.dz W (F a)
      = star (Work.MRMT.dz F a) * (Work.MRMT.dz U a - star (μF a) * Work.MRMT.dzbar U a) := by
  have hdz := Work.MRMT.Wirtinger.dz_comp (f := F) (g := W) hdW hFa
  have hdzbar := Work.MRMT.Wirtinger.dzbar_comp (f := F) (g := W) hdW hFa
  rw [← hUeq] at hdz hdzbar
  have hdet : ((fderiv ℝ F a).det : ℂ)
      = Work.MRMT.dz F a * star (Work.MRMT.dz F a)
        - Work.MRMT.dzbar F a * star (Work.MRMT.dzbar F a) := by
    rw [Work.MRMT.Sobolev.det_fderiv_eq, Complex.ofReal_sub]
    congr 1 <;> simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hdet, hdzbar, hdz, hrel, star_mul]
  ring

theorem coeff_conj_comp_le {F : ℂ ≃ₜ ℂ} {μF f : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hbelt : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μF z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (hμ : ∀ z : ℂ, ‖μF z‖ ≤ k) (hf : Differentiable ℂ (star ∘ f)) (w : ℂ) :
    ‖Work.MRMT.dzbar (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) w‖ * (1 - k ^ 2) ≤
      ‖Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) w‖ *
        ‖star (μF (f ((F.symm : ℂ → ℂ) w))) * Work.MRMT.dzbar f ((F.symm : ℂ → ℂ) w)
            / star (Work.MRMT.dzbar f ((F.symm : ℂ → ℂ) w)) - μF ((F.symm : ℂ → ℂ) w)‖ := by
  set G : ℂ → ℂ := star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ) with hG
  set α : ℂ := Work.MRMT.dz (F : ℂ → ℂ) ((F.symm : ℂ → ℂ) w) with hα
  set A : ℂ := Work.MRMT.dz (F : ℂ → ℂ) (f ((F.symm : ℂ → ℂ) w)) with hA
  set r : ℂ := Work.MRMT.dzbar f ((F.symm : ℂ → ℂ) w) with hr
  set μa : ℂ := μF ((F.symm : ℂ → ℂ) w) with hμa
  set μb : ℂ := μF (f ((F.symm : ℂ → ℂ) w)) with hμb
  set Cc : ℂ := star μb * r / star r - μa with hCc
  set sb : ℂ := 1 - star μa * star μb * r / star r with hsb
  set D : ℝ := (fderiv ℝ (F : ℂ → ℂ) ((F.symm : ℂ → ℂ) w)).det with hD
  have hDpos : 0 < D := by
    rw [hD]
    exact det_pos_of_beltrami_homeomorph hk1 hF hFs hbelt hμ _
  -- differentiability
  have hfat : DifferentiableAt ℂ (star ∘ f) ((F.symm : ℂ → ℂ) w) := hf.differentiableAt
  have hfa : DifferentiableAt ℝ f ((F.symm : ℂ → ℂ) w) :=
    Work.MRMT.Wirtinger.differentiableAt_of_antiholo hfat
  have hdzf : Work.MRMT.dz f ((F.symm : ℂ → ℂ) w) = 0 :=
    Work.MRMT.Wirtinger.dz_of_antiholo hfat
  have hFfa : DifferentiableAt ℝ (F : ℂ → ℂ) (f ((F.symm : ℂ → ℂ) w)) :=
    hF.contDiffAt.differentiableAt (by norm_num)
  have hFsa : DifferentiableAt ℝ (F : ℂ → ℂ) ((F.symm : ℂ → ℂ) w) :=
    hF.contDiffAt.differentiableAt (by norm_num)
  have hFsw : DifferentiableAt ℝ (F.symm : ℂ → ℂ) w :=
    hFs.contDiffAt.differentiableAt (by norm_num)
  have hGw : DifferentiableAt ℝ G w := by
    rw [hG]
    exact (Work.MRMT.Wirtinger.differentiableAt_star _).comp w
      (hFfa.comp w (hfa.comp w hFsw))
  have hGw' : DifferentiableAt ℝ G ((F : ℂ → ℂ) ((F.symm : ℂ → ℂ) w)) := by
    simpa [Homeomorph.apply_symm_apply] using hGw
  -- the auxiliary identities
  have hUeq : (star ∘ (F : ℂ → ℂ) ∘ f) = G ∘ (F : ℂ → ℂ) := by
    rw [hG]; funext z; simp [Function.comp_apply]
  have hIdzbar := det_mul_dzbar_of_eq_comp (F := (F : ℂ → ℂ)) (U := star ∘ (F : ℂ → ℂ) ∘ f)
      (W := G) (μF := μF) hFsa hGw' hUeq (hbelt ((F.symm : ℂ → ℂ) w))
  have hIdz := det_mul_dz_of_eq_comp (F := (F : ℂ → ℂ)) (U := star ∘ (F : ℂ → ℂ) ∘ f)
      (W := G) (μF := μF) hFsa hGw' hUeq (hbelt ((F.symm : ℂ → ℂ) w))
  -- values of the Wirtinger derivatives of `U`
  have hdzU : Work.MRMT.dz (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w) = star A * star r := by
    rw [Work.MRMT.Found.dz_star_comp hFfa hfa (hbelt _), hdzf, mul_zero, add_zero, ← hA, ← hr]
  have hdzbarU : Work.MRMT.dzbar (star ∘ (F : ℂ → ℂ) ∘ f) ((F.symm : ℂ → ℂ) w)
      = star A * (star μb * r) := by
    rw [Work.MRMT.Found.dzbar_star_comp hFfa hfa (hbelt _), hdzf, star_zero, zero_add,
      ← hA, ← hr, ← hμb]
  have hIdzbar1 : (D : ℂ) * Work.MRMT.dzbar G w
      = α * (star A * (star μb * r) - μa * (star A * star r)) := by
    have h := hIdzbar
    simp only [Homeomorph.apply_symm_apply] at h
    rw [← hD, hdzbarU, hdzU, ← hα, ← hμa] at h
    exact h
  have hIdz1 : (D : ℂ) * Work.MRMT.dz G w
      = star α * (star A * star r - star μa * (star A * (star μb * r))) := by
    have h := hIdz
    simp only [Homeomorph.apply_symm_apply] at h
    rw [← hD, hdzbarU, hdzU, ← hα, ← hμa] at h
    exact h
  -- the two norm identities
  have hCr : star r * Cc = star μb * r - μa * star r := by
    rw [hCc]
    by_cases h : star r = 0
    · have hr0 : r = 0 := by simpa using h
      rw [hr0]; simp
    · rw [mul_sub, mul_div_cancel₀ _ h]; ring
  have hCs : star r * sb = star r - star μa * star μb * r := by
    rw [hsb]
    by_cases h : star r = 0
    · have hr0 : r = 0 := by simpa using h
      rw [hr0]; simp
    · rw [mul_sub, mul_one, mul_div_cancel₀ _ h]
  have hN1 : D * ‖Work.MRMT.dzbar G w‖ = ‖α‖ * ‖A‖ * ‖r‖ * ‖Cc‖ := by
    have hfac : star A * (star μb * r) - μa * (star A * star r)
        = star A * (star μb * r - μa * star r) := by ring
    have h : (D : ℂ) * Work.MRMT.dzbar G w = α * star A * star r * Cc := by
      rw [hIdzbar1, hfac, ← hCr]; ring
    have h2 := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [abs_of_pos hDpos] at h2
    exact h2
  have hN2 : D * ‖Work.MRMT.dz G w‖ = ‖α‖ * ‖A‖ * ‖r‖ * ‖sb‖ := by
    have hfac : star A * star r - star μa * (star A * (star μb * r))
        = star A * (star r - star μa * star μb * r) := by ring
    have h : (D : ℂ) * Work.MRMT.dz G w = star α * star A * star r * sb := by
      rw [hIdz1, hfac, ← hCs]; ring
    have h2 := congrArg (fun z : ℂ => ‖z‖) h
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [abs_of_pos hDpos] at h2
    exact h2
  have hkey : ‖Work.MRMT.dzbar G w‖ * ‖sb‖ = ‖Work.MRMT.dz G w‖ * ‖Cc‖ := by
    have h1 : D * (‖Work.MRMT.dzbar G w‖ * ‖sb‖) = D * (‖Work.MRMT.dz G w‖ * ‖Cc‖) := by
      calc D * (‖Work.MRMT.dzbar G w‖ * ‖sb‖) = (D * ‖Work.MRMT.dzbar G w‖) * ‖sb‖ := by ring
        _ = (‖α‖ * ‖A‖ * ‖r‖ * ‖Cc‖) * ‖sb‖ := by rw [hN1]
        _ = (‖α‖ * ‖A‖ * ‖r‖ * ‖sb‖) * ‖Cc‖ := by ring
        _ = (D * ‖Work.MRMT.dz G w‖) * ‖Cc‖ := by rw [hN2]
        _ = D * (‖Work.MRMT.dz G w‖ * ‖Cc‖) := by ring
    exact mul_left_cancel₀ (ne_of_gt hDpos) h1
  have hsb_ge : 1 - k ^ 2 ≤ ‖sb‖ := by
    rw [hsb, hμa, hμb, hr]
    exact one_sub_sq_le_norm_aux hk0 (hμ ((F.symm : ℂ → ℂ) w))
      (hμ (f ((F.symm : ℂ → ℂ) w)))
  calc ‖Work.MRMT.dzbar G w‖ * (1 - k ^ 2) ≤ ‖Work.MRMT.dzbar G w‖ * ‖sb‖ :=
        mul_le_mul_of_nonneg_left hsb_ge (norm_nonneg _)
    _ = ‖Work.MRMT.dz G w‖ * ‖Cc‖ := hkey

end Work.MRMT.Found
