import Submission.FUP.Dbar2
import Submission.FUP.WirtingerCalc
import Submission.FUP.KohnMorrey

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# `ϑ₁ ϑ₂ = 0` and the smooth domain of the weak `(0,1) → (0,2)` operator

This module proves the algebraic identity `ϑ₁(ϑ₂Ψ) = 0` for smooth compactly supported `(0,2)`-forms
`Ψ` (with `ϑ₁`, `ϑ₂` the formal adjoints of `∂̄₁`, `∂̄₂`), which is what makes the range of the weak
`∂̄`-operator on functions lie in the kernel of the weak `∂̄`-operator on `(0,1)`-forms.

The proof uses the exponential reformulation: with `Λ = e^{-φ}` (a nonzero scalar function),

  `Λ · ϑ₁(ϑ₂Ψ) = ∑_{j,k} ∂_j ∂_k (Λ · (Ψ_{jk} - Ψ_{kj}))`,

and the right-hand side vanishes because `A_{jk} = Λ(Ψ_{jk} - Ψ_{kj})` is antisymmetric, so that
`∑_{j,k} ∂_j∂_k A_{jk} = -∑_{j,k} ∂_j∂_k A_{jk}` (Clairaut + antisymmetry).

We also prove the weighted integration-by-parts identity for `∂̄₂`, the smooth-domain lemma
`DbarWeak2 φ x (∂̄₂x)`, and the density of the domain of `dbarOp2 φ`.
-/

namespace Submission.FUP

variable {d : ℕ}

section Linearity

/-- `∂_j` is linear in finite sums. -/
lemma partialZ_sum (j : Fin d) {G : FormDu d → Fin d → ℂ} {z : FormDu d}
    (hG : ∀ k, DifferentiableAt ℝ (fun w => G w k) z) :
    partialZ j (fun w => ∑ k, G w k) z = ∑ k, partialZ j (fun w => G w k) z := by
  have hfun : (fun w : FormDu d => ∑ k : Fin d, G w k)
      = ∑ k : Fin d, (fun w => G w k) := by
    funext w; simp [Finset.sum_apply]
  have h : fderiv ℝ (fun w => ∑ k : Fin d, G w k) z
      = ∑ k : Fin d, fderiv ℝ (fun w => G w k) z := by
    rw [hfun, fderiv_sum (u := Finset.univ) (fun k _ => hG k)]
  have h1 : (∑ k : Fin d, fderiv ℝ (fun w => G w k) z) (Pi.single j (1:ℂ) : Fin d → ℂ)
      = ∑ k : Fin d, fderiv ℝ (fun w => G w k) z (Pi.single j (1:ℂ)) :=
    map_sum (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ) : Fin d → ℂ)) _ Finset.univ
  have h2 : (∑ k : Fin d, fderiv ℝ (fun w => G w k) z) (Pi.single j Complex.I : Fin d → ℂ)
      = ∑ k : Fin d, fderiv ℝ (fun w => G w k) z (Pi.single j Complex.I) :=
    map_sum (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I : Fin d → ℂ)) _ Finset.univ
  simp only [partialZ, h]
  rw [h1, h2, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- `∂_j` of a negation. -/
lemma partialZ_neg (j : Fin d) (ψ : FormDu d → ℂ) (z : FormDu d) :
    partialZ j (fun w => -(ψ w)) z = - partialZ j ψ z := by
  have hψ : (fun w : FormDu d => -(ψ w)) = -ψ := rfl
  rw [partialZ, partialZ, hψ, fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

end Linearity

section Comm

/-- **The Wirtinger `∂`-derivatives commute**: `∂_j ∂_k h = ∂_k ∂_j h` for `h ∈ C²`. -/
lemma partialZ_partialZ_comm {h : FormDu d → ℂ} (hh : ContDiff ℝ 2 h) (j k : Fin d)
    (z : FormDu d) :
    partialZ j (fun w => partialZ k h w) z = partialZ k (fun w => partialZ j h w) z := by
  have hZ := fderiv_partialZ_apply hh k z
  have hZj := fderiv_partialZ_apply hh j z
  have h1 : fderiv ℝ (fun w => partialZ k h w) z (Pi.single j (1:ℂ))
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j 1)
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z
              (Pi.single j 1)) := hZ _
  have h2 : fderiv ℝ (fun w => partialZ k h w) z (Pi.single j Complex.I)
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j Complex.I)
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z
              (Pi.single j Complex.I)) := hZ _
  have h3 : fderiv ℝ (fun w => partialZ j h w) z (Pi.single k (1:ℂ))
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k 1)
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z
              (Pi.single k 1)) := hZj _
  have h4 : fderiv ℝ (fun w => partialZ j h w) z (Pi.single k Complex.I)
      = (1 / 2) * (fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k Complex.I)
          - Complex.I * fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z
              (Pi.single k Complex.I)) := hZj _
  rw [partialZ, partialZ, h1, h2, h3, h4]
  have e1 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j 1)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k 1) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e2 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z (Pi.single j 1)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j 1)) z (Pi.single k Complex.I) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e3 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k 1)) z (Pi.single j Complex.I)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z (Pi.single k 1) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  have e4 : fderiv ℝ (fun w => fderiv ℝ h w (Pi.single k Complex.I)) z (Pi.single j Complex.I)
      = fderiv ℝ (fun w => fderiv ℝ h w (Pi.single j Complex.I)) z (Pi.single k Complex.I) :=
    Commons.Analysis.Calculus.fderiv_fderiv_swap hh _ _ z
  rw [e1, e2, e3, e4]
  ring

end Comm

section AntisymmSum

/-- The double sum of an antisymmetric matrix vanishes. -/
lemma sum_sum_antisymm {ι : Type*} (s : Finset ι) (f : ι → ι → ℂ)
    (h : ∀ i j, f j i = - f i j) : ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  have h1 : (∑ i ∈ s, ∑ j ∈ s, f i j) = ∑ j ∈ s, ∑ i ∈ s, f i j := Finset.sum_comm
  have h2 : (∑ j ∈ s, ∑ i ∈ s, f i j) = - (∑ i ∈ s, ∑ j ∈ s, f i j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h]
  have hh : (∑ i ∈ s, ∑ j ∈ s, f i j) = - (∑ i ∈ s, ∑ j ∈ s, f i j) := h1.trans h2
  refine add_self_eq_zero.mp ?_
  simpa only [neg_add_cancel] using congrArg (· + (∑ i ∈ s, ∑ j ∈ s, f i j)) hh

end AntisymmSum

section ExpRule

/-- The chain rule for `Complex.exp`: `∂_k (exp ∘ ψ) = exp(ψ) ∂_k ψ`. -/
lemma partialZ_exp {ψ : FormDu d → ℂ} {k : Fin d} {z : FormDu d}
    (hψ : DifferentiableAt ℝ ψ z) :
    partialZ k (fun w => Complex.exp (ψ w)) z = Complex.exp (ψ z) * partialZ k ψ z := by
  have hd : fderiv ℝ (fun w => Complex.exp (ψ w)) z = Complex.exp (ψ z) • fderiv ℝ ψ z :=
    (hψ.hasFDerivAt.cexp).fderiv
  simp only [partialZ, hd, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `∂_k e^{-φ} = - e^{-φ} ∂_k φ` for a real weight `φ`. -/
lemma partialZ_exp_neg {φ : FormDu d → ℝ} {k : Fin d} {z : FormDu d}
    (hφ : DifferentiableAt ℝ (fun z => ((φ z : ℝ) : ℂ)) z) :
    partialZ k (fun w => Complex.exp (-(((φ w : ℝ) : ℂ)))) z
      = - Complex.exp (-(((φ z : ℝ) : ℂ)))
          * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z := by
  have hneg : DifferentiableAt ℝ (fun w => -(((φ w : ℝ) : ℂ))) z := hφ.neg
  have h := partialZ_exp (ψ := fun w => -(((φ w : ℝ) : ℂ))) hneg (k := k) (z := z)
  rw [h, partialZ_neg]
  ring

end ExpRule

section Main

/-- `ϑ₂Ψ` is componentwise `C¹` when `φ` and `Ψ` are `C²`. -/
lemma contDiff_one_dbarAdjoint2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (hΨ : ∀ i, ContDiff ℝ 2 (fun z => Ψ z i)) :
    ∀ j, ContDiff ℝ 1 (fun z => dbarAdjoint2 φ Ψ z j) := by
  have hΦ2 : ContDiff ℝ 2 (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  intro j
  have hj : (fun z => dbarAdjoint2 φ Ψ z j) = fun z => -∑ k : Fin d,
      (partialZ k (fun w => Ψ w (j, k) - Ψ w (k, j)) z
        - (Ψ z (j, k) - Ψ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) := rfl
  rw [hj]
  refine ContDiff.neg (ContDiff.sum (s := Finset.univ) (fun k _ => ?_))
  refine (contDiff_partialZ_one ((hΨ (j, k)).sub (hΨ (k, j))) k).sub ?_
  exact ((hΨ (j, k)).sub (hΨ (k, j))).of_le (by norm_num) |>.mul
    (contDiff_partialZ_one hΦ2 k)

/-- The function identity `e^{-φ} (ϑ₂Ψ)_j = -∑_k ∂_k(e^{-φ}(Ψ_{jk}-Ψ_{kj}))`. -/
lemma exp_mul_dbarAdjoint2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (hΨ : ∀ i, ContDiff ℝ 2 (fun z => Ψ z i))
    (j : Fin d) :
    (fun z => Complex.exp (-(((φ z : ℝ) : ℂ))) * dbarAdjoint2 φ Ψ z j)
      = fun z => -∑ k, partialZ k (fun w =>
          Complex.exp (-(((φ w : ℝ) : ℂ))) * (Ψ w (j, k) - Ψ w (k, j))) z := by
  have hΦ2 : ContDiff ℝ 2 (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hΦd : ∀ z, DifferentiableAt ℝ (fun z : FormDu d => ((φ z : ℝ) : ℂ)) z :=
    fun z => (hΦ2.differentiable (by norm_num)).differentiableAt
  have hΛ : ContDiff ℝ 2 (fun z : FormDu d => Complex.exp (-(((φ z : ℝ) : ℂ)))) := hΦ2.neg.cexp
  have hΛd : ∀ z, DifferentiableAt ℝ (fun z : FormDu d => Complex.exp (-(((φ z : ℝ) : ℂ)))) z :=
    fun z => (hΛ.differentiable (by norm_num)).differentiableAt
  funext z
  have hΔd : ∀ k, DifferentiableAt ℝ (fun w => Ψ w (j, k) - Ψ w (k, j)) z :=
    fun k => (((hΨ (j, k)).sub (hΨ (k, j))).differentiable (by norm_num)).differentiableAt
  have hprod : ∀ k : Fin d,
      partialZ k (fun w => Complex.exp (-(((φ w : ℝ) : ℂ))) * (Ψ w (j, k) - Ψ w (k, j))) z
        = Complex.exp (-(((φ z : ℝ) : ℂ))) * (partialZ k (fun w => Ψ w (j, k) - Ψ w (k, j)) z
            - (Ψ z (j, k) - Ψ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) := by
    intro k
    rw [partialZ_mul (hΛd z) (hΔd k), partialZ_exp_neg (hΦd z)]
    ring
  simp only [dbarAdjoint2, mul_neg, Finset.mul_sum, neg_inj]
  exact Finset.sum_congr rfl (fun k _ => (hprod k).symm)

/-- The identity `∂_j(e^{-φ} u_j) = e^{-φ}(∂_j u_j - u_j∂_jφ)`. -/
lemma partialZ_exp_mul {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {u : FormDu d → (Fin d → ℂ)} (hu : ∀ j, ContDiff ℝ 1 (fun z => u z j)) (j : Fin d) :
    (fun z => partialZ j (fun w => Complex.exp (-(((φ w : ℝ) : ℂ))) * u w j) z)
      = fun z => Complex.exp (-(((φ z : ℝ) : ℂ))) * (partialZ j (fun w => u w j) z
          - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z) := by
  have hΦ2 : ContDiff ℝ 2 (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hΦd : ∀ z, DifferentiableAt ℝ (fun z : FormDu d => ((φ z : ℝ) : ℂ)) z :=
    fun z => (hΦ2.differentiable (by norm_num)).differentiableAt
  have hΛ : ContDiff ℝ 2 (fun z : FormDu d => Complex.exp (-(((φ z : ℝ) : ℂ)))) := hΦ2.neg.cexp
  funext z
  have hΛd : DifferentiableAt ℝ (fun z : FormDu d => Complex.exp (-(((φ z : ℝ) : ℂ)))) z :=
    (hΛ.differentiable (by norm_num)).differentiableAt
  have hud : DifferentiableAt ℝ (fun w => u w j) z :=
    ((hu j).differentiable (by norm_num)).differentiableAt
  rw [partialZ_mul hΛd hud, partialZ_exp_neg (hΦd z)]
  ring

/-- **`ϑ₁(ϑ₂Ψ) = 0`**: the formal adjoint of `∂̄₁` kills the range of the formal adjoint of `∂̄₂`. -/
theorem dbarAdjoint_dbarAdjoint2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (hΨ : ∀ i, ContDiff ℝ 2 (fun z => Ψ z i)) :
    dbarAdjoint φ (dbarAdjoint2 φ Ψ) = 0 := by
  have hu : ∀ j, ContDiff ℝ 1 (fun z => dbarAdjoint2 φ Ψ z j) :=
    contDiff_one_dbarAdjoint2 hφ hΨ
  have hA2 : ∀ j k, ContDiff ℝ 2 (fun z => Complex.exp (-(((φ z : ℝ) : ℂ)))
      * (Ψ z (j, k) - Ψ z (k, j))) := by
    intro j k
    have hΛ : ContDiff ℝ 2 (fun z : FormDu d => Complex.exp (-(((φ z : ℝ) : ℂ)))) :=
      (Complex.ofRealCLM.contDiff.comp hφ).neg.cexp
    exact hΛ.mul ((hΨ (j, k)).sub (hΨ (k, j)))
  -- step 1: `∂_j(e^{-φ}u_j) = e^{-φ}(∂_j u_j - u_j ∂_j φ)`
  have hstep1 : ∀ z, Complex.exp (-(((φ z : ℝ) : ℂ)))
        * (∑ j : Fin d, (partialZ j (fun w => dbarAdjoint2 φ Ψ w j) z
            - dbarAdjoint2 φ Ψ z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z))
      = ∑ j : Fin d, partialZ j (fun w => Complex.exp (-(((φ w : ℝ) : ℂ)))
          * dbarAdjoint2 φ Ψ w j) z := by
    intro z
    have h : ∀ j : Fin d, partialZ j (fun w => Complex.exp (-(((φ w : ℝ) : ℂ)))
          * dbarAdjoint2 φ Ψ w j) z
        = Complex.exp (-(((φ z : ℝ) : ℂ))) * (partialZ j (fun w => dbarAdjoint2 φ Ψ w j) z
            - dbarAdjoint2 φ Ψ z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z) :=
      fun j => congrFun (partialZ_exp_mul hφ hu j) z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => (h j).symm)
  -- step 2: `e^{-φ} u_j = -∑_k ∂_k A_{jk}`
  have hAanti : ∀ j k z, Complex.exp (-(((φ z : ℝ) : ℂ))) * (Ψ z (k, j) - Ψ z (j, k))
      = - (Complex.exp (-(((φ z : ℝ) : ℂ))) * (Ψ z (j, k) - Ψ z (k, j))) := by
    intro j k z; ring
  have hsub : ∀ j : Fin d,
      (fun w => Complex.exp (-(((φ w : ℝ) : ℂ))) * dbarAdjoint2 φ Ψ w j)
        = fun w => -∑ k, partialZ k (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
            * (Ψ v (j, k) - Ψ v (k, j))) w := fun j => exp_mul_dbarAdjoint2 hφ hΨ j
  -- step 3: differentiate
  have hstep3 : ∀ z, (∑ j : Fin d, partialZ j (fun w => Complex.exp (-(((φ w : ℝ) : ℂ)))
          * dbarAdjoint2 φ Ψ w j) z)
      = - ∑ j : Fin d, ∑ k : Fin d, partialZ j (fun w =>
          partialZ k (fun v => Complex.exp (-(((φ v : ℝ) : ℂ))) * (Ψ v (j, k) - Ψ v (k, j))) w) z := by
    intro z
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hsub j, partialZ_neg]
    have hsum : partialZ j (fun w => ∑ k : Fin d, partialZ k (fun v =>
          Complex.exp (-(((φ v : ℝ) : ℂ))) * (Ψ v (j, k) - Ψ v (k, j))) w) z
        = ∑ k : Fin d, partialZ j (fun w => partialZ k (fun v =>
            Complex.exp (-(((φ v : ℝ) : ℂ))) * (Ψ v (j, k) - Ψ v (k, j))) w) z :=
      partialZ_sum j (fun k => ((contDiff_partialZ_one (hA2 j k) k).differentiable
        (by norm_num)).differentiableAt)
    rw [hsum]
  -- conclude
  funext z
  have hanti : ∀ j k : Fin d,
      partialZ k (fun w => partialZ j (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
            * (Ψ v (k, j) - Ψ v (j, k))) w) z
        = - partialZ j (fun w => partialZ k (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
            * (Ψ v (j, k) - Ψ v (k, j))) w) z := by
    intro j k
    have hAj : ContDiff ℝ 2 (fun v : FormDu d => Complex.exp (-(((φ v : ℝ) : ℂ)))
        * (Ψ v (j, k) - Ψ v (k, j))) := hA2 j k
    have hAkj : (fun v => Complex.exp (-(((φ v : ℝ) : ℂ))) * (Ψ v (k, j) - Ψ v (j, k)))
        = fun v => - (Complex.exp (-(((φ v : ℝ) : ℂ))) * (Ψ v (j, k) - Ψ v (k, j))) := by
      funext v; exact hAanti j k v
    have h1 : (fun w => partialZ j (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
          * (Ψ v (k, j) - Ψ v (j, k))) w)
        = fun w => - (partialZ j (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
          * (Ψ v (j, k) - Ψ v (k, j))) w) := by
      rw [hAkj]
      funext w
      exact partialZ_neg j (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
        * (Ψ v (j, k) - Ψ v (k, j))) w
    rw [h1, partialZ_neg, partialZ_partialZ_comm hAj]
  have hzero := sum_sum_antisymm Finset.univ
    (fun j k => partialZ j (fun w => partialZ k (fun v => Complex.exp (-(((φ v : ℝ) : ℂ)))
      * (Ψ v (j, k) - Ψ v (k, j))) w) z) hanti
  have : Complex.exp (-(((φ z : ℝ) : ℂ)))
      * (∑ j : Fin d, (partialZ j (fun w => dbarAdjoint2 φ Ψ w j) z
          - dbarAdjoint2 φ Ψ z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) = 0 := by
    rw [hstep1 z]
    rw [hstep3 z]
    rw [hzero]
    ring
  have hne : Complex.exp (-(((φ z : ℝ) : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hmain : (∑ j : Fin d, (partialZ j (fun w => dbarAdjoint2 φ Ψ w j) z
        - dbarAdjoint2 φ Ψ z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) = 0 :=
    (mul_eq_zero.mp this).resolve_left hne
  show dbarAdjoint φ (dbarAdjoint2 φ Ψ) z = 0
  rw [show dbarAdjoint φ (dbarAdjoint2 φ Ψ) z
      = - (∑ j : Fin d, (partialZ j (fun w => dbarAdjoint2 φ Ψ w j) z
          - dbarAdjoint2 φ Ψ z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) from rfl]
  rw [hmain, neg_zero]

end Main

section RanKer

/-- An `Lp` element represented by a function that is identically zero is `0`. -/
lemma toLp_eq_zero_of_eq_zero {d : ℕ} {φ : FormDu d → ℝ} {E : Type*}
    [NormedAddCommGroup E] {f : FormDu d → E} (h : MemLp f 2 (wtMeasure φ)) (hz : f = 0) :
    h.toLp f = 0 := by
  apply Lp.ext
  have h1 : (↑↑(h.toLp f) : FormDu d → E) =ᵐ[wtMeasure φ] f := MemLp.coeFn_toLp h
  have h2 : (↑↑(0 : Lp E 2 (wtMeasure φ)) : FormDu d → E) =ᵐ[wtMeasure φ] 0 :=
    Lp.coeFn_zero E 2 (wtMeasure φ)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]
  exact congrFun hz z

/-- `∂_k` of a smooth function is smooth. -/
lemma contDiff_partialZ_top {f : FormDu d → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin d) :
    ContDiff ℝ ∞ (fun z => partialZ j f z) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (Pi.single j (1:ℂ))) :=
    hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hfd.clm_apply contDiff_const
  have h : (fun z => partialZ j f z) = fun z => (fderiv ℝ f z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2 := by
    funext z; rw [partialZ]
  rw [h]
  exact (h1.sub (contDiff_const.mul h2)).div_const 2

/-- `ϑ₂Ψ` is componentwise smooth when `φ` and `Ψ` are smooth. -/
lemma contDiff_dbarAdjoint2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (hΨ : ∀ i, ContDiff ℝ ∞ (fun z => Ψ z i)) :
    ∀ j, ContDiff ℝ ∞ (fun z => dbarAdjoint2 φ Ψ z j) := by
  have hΦ : ContDiff ℝ ∞ (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  intro j
  have hj : (fun z => dbarAdjoint2 φ Ψ z j) = fun z => -∑ k : Fin d,
      (partialZ k (fun w => Ψ w (j, k) - Ψ w (k, j)) z
        - (Ψ z (j, k) - Ψ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) := rfl
  rw [hj]
  refine ContDiff.neg (ContDiff.sum (s := Finset.univ) (fun k _ => ?_))
  refine (contDiff_partialZ_top ((hΨ (j, k)).sub (hΨ (k, j))) k).sub ?_
  exact ((hΨ (j, k)).sub (hΨ (k, j))).mul (contDiff_partialZ_top hΦ k)

/-- The `(0,1)`-form `ϑ₂Ψ` is smooth, as a `FormSpace d`-valued function. -/
lemma contDiff_liftForm_dbarAdjoint2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {Ψ : FormDu d → (Fin d × Fin d → ℂ)} (hΨ : ∀ i, ContDiff ℝ ∞ (fun z => Ψ z i)) :
    ContDiff ℝ ∞ (liftForm (dbarAdjoint2 φ Ψ)) :=
  contDiff_liftForm (contDiff_dbarAdjoint2 hφ hΨ)

/-- **`ran ∂̄₁ ⊆ ker ∂̄₂`**: the range of the weak `∂̄`-operator on functions lies in the kernel of
the weak `(0,1) → (0,2)` operator. -/
theorem dbarWeak_ran_le_ker {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {f : Lp ℂ 2 (wtMeasure φ)} {w : Lp (FormSpace d) 2 (wtMeasure φ)}
    (hw : DbarWeak φ f w) : DbarWeak2 φ w 0 := by
  intro Ψ h1 h2 hΨ hθ
  have hle : (2 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  have hΨ2 : ∀ i, ContDiff ℝ 2 (fun z => toFormFun2 Ψ z i) :=
    fun i => (contDiff_toFormFun2 h1 i).of_le hle
  have hzero : dbarAdjoint φ (dbarAdjoint2 φ (toFormFun2 Ψ)) = 0 :=
    dbarAdjoint_dbarAdjoint2 (hφ.of_le hle) hΨ2
  have hψsmooth : ContDiff ℝ ∞ (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) :=
    contDiff_liftForm_dbarAdjoint2 hφ (fun i => contDiff_toFormFun2 h1 i)
  have hcs : HasCompactSupport (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) :=
    hasCompactSupport_liftForm (hasCompactSupport_dbarAdjoint2 (hasCompactSupport_toFormFun2 h2))
  have hθ' : MemLp (dbarAdjoint φ (toFormFun (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))))
      2 (wtMeasure φ) := hzero.symm ▸ MeasureTheory.MemLp.zero
  have hrel := hw (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) hψsmooth hcs hθ hθ'
  rw [inner_zero_right, hrel]
  have hz : hθ'.toLp (dbarAdjoint φ (toFormFun (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))))) = 0 :=
    toLp_eq_zero_of_eq_zero hθ' hzero
  rw [hz, inner_zero_left]

end RanKer

section PartialZIBP

/-- An integrand of the form `A · e^{-ψ}`, with `A` continuous and compactly supported, is
integrable. -/
lemma integrable_mul_cexp_neg {ψ : FormDu d → ℂ} (hψ : Continuous ψ) {A : FormDu d → ℂ}
    (hA : Continuous A) (hsA : HasCompactSupport A) :
    Integrable (fun z => A z * Complex.exp (-(ψ z))) :=
  (hA.mul (Complex.continuous_exp.comp hψ.neg)).integrable_of_hasCompactSupport hsA.mul_right

/-- The pointwise identity `∂_jF = D_{e_j}F - ∂̄_jF`. -/
lemma partialZ_eq_fderiv_sub (j : Fin d) (F : FormDu d → ℂ) (z : FormDu d) :
    partialZ j F z = fderiv ℝ F z (Pi.single j (1:ℂ)) - partialZbar j F z := by
  simp only [partialZ, partialZbar]; ring


end PartialZIBP

section Dbar2IBP

/-- Auxiliary: the pointwise rearrangement
`∑_{j,k}(∂_kY_j - ∂_jY_k)Θ_{jk} = ∑_{j,k}(∂_kY_j)(Θ_{jk} - Θ_{kj})`. -/
lemma sum_dbar2_rearrange (Y : FormDu d → (Fin d → ℂ)) (Θ : FormDu d → (Fin d × Fin d → ℂ))
    (z : FormDu d) :
    (∑ j : Fin d, ∑ k : Fin d, (partialZ k (fun w => Y w j) z - partialZ j (fun w => Y w k) z)
        * Θ z (j, k))
      = ∑ j : Fin d, ∑ k : Fin d, partialZ k (fun w => Y w j) z * (Θ z (j, k) - Θ z (k, j)) := by
  have hrelabel : (∑ j : Fin d, ∑ k : Fin d, partialZ j (fun w => Y w k) z * Θ z (j, k))
      = ∑ j : Fin d, ∑ k : Fin d, partialZ k (fun w => Y w j) z * Θ z (k, j) := by
    rw [Finset.sum_comm]
  have e1 : (∑ j : Fin d, ∑ k : Fin d, (partialZ k (fun w => Y w j) z
        - partialZ j (fun w => Y w k) z) * Θ z (j, k))
      = (∑ j : Fin d, ∑ k : Fin d, partialZ k (fun w => Y w j) z * Θ z (j, k))
        - (∑ j : Fin d, ∑ k : Fin d, partialZ j (fun w => Y w k) z * Θ z (j, k)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [e1, hrelabel]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **Weighted integration by parts for `∂̄₂`**: the formal adjoint of the `(0,1) → (0,2)` operator
`(∂̄₂Y)_{jk} = ∂̄_kY_j - ∂̄_jY_k` is `ϑ₂`, in the conjugate-free form needed for the weak relation. -/
theorem integral_inner_dbar2_eq {Y : FormDu d → (Fin d → ℂ)}
    {Θ : FormDu d → (Fin d × Fin d → ℂ)} {φ : FormDu d → ℝ}
    (hY : ∀ j, ContDiff ℝ 1 (fun z => Y z j))
    (hΘ : ∀ i, ContDiff ℝ 1 (fun z => Θ z i))
    (hφ : ContDiff ℝ 1 φ)
    (hsY : ∀ j, HasCompactSupport (fun z => Y z j))
    (hsΘ : ∀ i, HasCompactSupport (fun z => Θ z i)) :
    (∫ z, (∑ j, ∑ k, (partialZ k (fun w => Y w j) z - partialZ j (fun w => Y w k) z)
        * Θ z (j, k)) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = ∫ z, (∑ j, Y z j * dbarAdjoint2 φ Θ z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
  have hΦ : ContDiff ℝ 1 (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hΔc : ∀ j k, Continuous (fun z : FormDu d => Θ z (j, k) - Θ z (k, j)) :=
    fun j k => (hΘ (j, k)).continuous.sub (hΘ (k, j)).continuous
  have hIntP : ∀ j k : Fin d, Integrable (fun z => partialZ k (fun w => Y w j) z
      * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j k
    exact integrable_mul_cexp_neg hΦ.continuous
      ((continuous_partialZ (hY j) k).mul (hΔc j k))
      ((hasCompactSupport_partialZ (hsY j) k).mul_right)
  have hIntA : ∀ j k : Fin d, Integrable (fun z => Y z j
      * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j k
    exact integrable_mul_cexp_neg hΦ.continuous
      ((hY j).continuous.mul (continuous_partialZ ((hΘ (j, k)).sub (hΘ (k, j))) k))
      (hsY j).mul_right
  have hIntB : ∀ j k : Fin d, Integrable (fun z => Y z j * (Θ z (j, k) - Θ z (k, j))
      * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j k
    exact integrable_mul_cexp_neg hΦ.continuous
      (((hY j).continuous.mul (hΔc j k)).mul (continuous_partialZ hΦ k))
      ((hsY j).mul_right (f' := fun z => Θ z (j, k) - Θ z (k, j))).mul_right
  have hip : ∀ j k : Fin d, (∫ z, partialZ k (fun w => Y w j) z * (Θ z (j, k) - Θ z (k, j))
        * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = - (∫ z, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
        + (∫ z, Y z j * (Θ z (j, k) - Θ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume) := by
    intro j k
    exact integral_partialZ_mul_weighted_eq_neg (hY j) ((hΘ (j, k)).sub (hΘ (k, j)))
      hΦ (hsY j) ((hsΘ (j, k)).sub (hsΘ (k, j))) k
  have hIntj : ∀ j : Fin d, Integrable (fun z => (∑ k : Fin d, partialZ k (fun w => Y w j) z
      * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j
    rw [show (fun z : FormDu d => (∑ k : Fin d, partialZ k (fun w => Y w j) z
        * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))))
        = fun z => ∑ k : Fin d, partialZ k (fun w => Y w j) z
            * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ))) from by
      funext z; rw [Finset.sum_mul]]
    exact integrable_finsetSum Finset.univ (fun k _ => hIntP j k)
  have hIntFA : ∀ j : Fin d, Integrable (fun z => ∑ k : Fin d, Y z j
      * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := fun j =>
    integrable_finsetSum Finset.univ (fun k _ => hIntA j k)
  have hIntFB : ∀ j : Fin d, Integrable (fun z => ∑ k : Fin d, Y z j
      * (Θ z (j, k) - Θ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := fun j =>
    integrable_finsetSum Finset.univ (fun k _ => hIntB j k)
  have hInt2j : ∀ j : Fin d, Integrable (fun z => Y z j * dbarAdjoint2 φ Θ z j
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j
    exact integrable_mul_cexp_neg hΦ.continuous
      ((hY j).continuous.mul ((continuous_apply j).comp (continuous_dbarAdjoint2 hΘ hΦ)))
      (hsY j).mul_right
  -- the pointwise recombination
  have hpt : ∀ j : Fin d, ∀ z : FormDu d,
      - (∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
        + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
          * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = Y z j * dbarAdjoint2 φ Θ z j * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    intro j z
    have hY : Y z j * dbarAdjoint2 φ Θ z j
        = -(∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z)
          + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
              * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) := by
      rw [dbarAdjoint2, mul_neg, Finset.mul_sum]
      rw [show (∑ k : Fin d, Y z j * (partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            - (Θ z (j, k) - Θ z (k, j)) * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z))
          = (∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z)
            - (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
                * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) from by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring]
      rw [neg_sub]
      ring
    have hEfac : (-(∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z)
          + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
              * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z)) * Complex.exp (-(((φ z : ℝ) : ℂ)))
        = -(∑ k : Fin d, Y z j * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
              * Complex.exp (-(((φ z : ℝ) : ℂ))))
          + (∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
              * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
              * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
      rw [add_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
    rw [hY, hEfac]

  calc (∫ z, (∑ j, ∑ k, (partialZ k (fun w => Y w j) z - partialZ j (fun w => Y w k) z)
          * Θ z (j, k)) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
      = ∫ z, ∑ j : Fin d, (∑ k, partialZ k (fun w => Y w j) z
          * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [sum_dbar2_rearrange, Finset.sum_mul]
    _ = ∑ j : Fin d, ∫ z, (∑ k, partialZ k (fun w => Y w j) z
          * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume :=
        integral_finsetSum Finset.univ (fun j _ => hIntj j)
    _ = ∑ j : Fin d, ∑ k : Fin d, ∫ z, partialZ k (fun w => Y w j) z
          * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (fun z : FormDu d => (∑ k, partialZ k (fun w => Y w j) z
            * (Θ z (j, k) - Θ z (k, j))) * Complex.exp (-(((φ z : ℝ) : ℂ))))
            = fun z => ∑ k : Fin d, partialZ k (fun w => Y w j) z
                * (Θ z (j, k) - Θ z (k, j)) * Complex.exp (-(((φ z : ℝ) : ℂ))) from by
          funext z; rw [Finset.sum_mul]]
        exact integral_finsetSum Finset.univ (fun k _ => hIntP j k)
    _ = ∑ j : Fin d, ∑ k : Fin d, (-(∫ z, Y z j
            * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
          + (∫ z, Y z j * (Θ z (j, k) - Θ z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)) := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hip j k))
    _ = ∑ j : Fin d, (-(∫ z, ∑ k : Fin d, Y z j
            * partialZ k (fun w => Θ w (j, k) - Θ w (k, j)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)
          + (∫ z, ∑ k : Fin d, Y z j * (Θ z (j, k) - Θ z (k, j))
            * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
          ← integral_finsetSum Finset.univ (fun k _ => hIntA j k),
          ← integral_finsetSum Finset.univ (fun k _ => hIntB j k)]
    _ = ∑ j : Fin d, ∫ z, Y z j * dbarAdjoint2 φ Θ z j
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← sub_eq_neg_add, ← integral_sub (hIntFB j) (hIntFA j)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.mul_apply]
        rw [sub_eq_neg_add]
        exact hpt j z
    _ = ∫ z, (∑ j : Fin d, Y z j * dbarAdjoint2 φ Θ z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
        rw [← integral_finsetSum Finset.univ (fun j _ => hInt2j j)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.mul_apply, Finset.sum_mul]

end Dbar2IBP

section SmoothDomain2

/-- `1 ≤ ∞` for the `ContDiff` order. -/
private lemma hle1 : (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top

/-- The pointwise `∂̄` of a `(0,1)`-form, as a `(0,2)`-form. -/
noncomputable def dbarFormFun2 (x : FormDu d → (Fin d → ℂ)) : FormDu d → (Fin d × Fin d → ℂ) :=
  fun z i => partialZbar i.2 (fun w => x w i.1) z - partialZbar i.1 (fun w => x w i.2) z

@[simp] lemma dbarFormFun2_apply (x : FormDu d → (Fin d → ℂ)) (z : FormDu d) (i : Fin d × Fin d) :
    dbarFormFun2 x z i
      = partialZbar i.2 (fun w => x w i.1) z - partialZbar i.1 (fun w => x w i.2) z := rfl

@[simp] lemma liftForm_apply (u : FormDu d → (Fin d → ℂ)) (z : FormDu d) (j : Fin d) :
    liftForm u z j = u z j := rfl

@[simp] lemma liftForm2_apply (Ψ : FormDu d → (Fin d × Fin d → ℂ)) (z : FormDu d)
    (i : Fin d × Fin d) : liftForm2 Ψ z i = Ψ z i := rfl

@[simp] lemma toFormFun2_apply_apply (Ψ : FormDu d → FormSpace2 d) (z : FormDu d)
    (i : Fin d × Fin d) : toFormFun2 Ψ z i = Ψ z i := rfl

/-- The pointwise identity `conj (∂̄_j f) = ∂_j (conj ∘ f)`. -/
lemma star_partialZbar (j : Fin d) (f : FormDu d → ℂ) (z : FormDu d) :
    star (partialZbar j f z) = partialZ j (fun w => star (f w)) z :=
  congrFun (partialZ_star j f).symm z

/-- `conj` commutes with the Bochner integral. -/
lemma integral_star_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℂ) :
    star (∫ x, f x ∂μ) = ∫ x, star (f x) ∂μ :=
  (ContinuousLinearEquiv.integral_comp_comm (μ := μ) Complex.conjCLE f).symm

/-- `star` fixes the real exponential weight. -/
lemma star_cexp_neg {φ : FormDu d → ℝ} (z : FormDu d) :
    star (Complex.exp (-(((φ z : ℝ) : ℂ)))) = Complex.exp (-(((φ z : ℝ) : ℂ))) := by
  rw [show Complex.exp (-(((φ z : ℝ) : ℂ))) = ((Real.exp (-(φ z)) : ℝ) : ℂ) from by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]]
  exact Complex.conj_ofReal _

/-- `∂_k` of a smooth function is smooth. -/
lemma contDiff_partialZbar_top {f : FormDu d → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin d) :
    ContDiff ℝ ∞ (fun z => partialZbar j f z) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (Pi.single j (1:ℂ))) :=
    hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hfd.clm_apply contDiff_const
  have h : (fun z => partialZbar j f z) = fun z => (fderiv ℝ f z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2 := by
    funext z; rw [partialZbar]
  rw [h]
  exact (h1.add (contDiff_const.mul h2)).div_const 2

/-- A `(ι → ℂ)`-valued function has compact support if each component does. -/
lemma hasCompactSupport_pi {ι X : Type*} [Fintype ι] [TopologicalSpace X] {F : X → (ι → ℂ)}
    (h : ∀ i, HasCompactSupport (fun x => F x i)) : HasCompactSupport F := by
  have hsub : tsupport F ⊆ ⋃ i, tsupport (fun x => F x i) := by
    refine closure_minimal ?_ (isClosed_iUnion_of_finite (fun i => isClosed_tsupport _))
    intro x hx
    simp only [Function.mem_support] at hx
    obtain ⟨i, hi⟩ : ∃ i, F x i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx (funext fun i => hc i)
    exact Set.mem_iUnion.mpr ⟨i, subset_tsupport _ hi⟩
  exact (isCompact_iUnion (fun i => (h i).isCompact)).of_isClosed_subset
    (isClosed_tsupport F) hsub

lemma contDiff_dbarFormFun2 {x : FormDu d → (Fin d → ℂ)}
    (hx : ∀ j, ContDiff ℝ ∞ (fun z => x z j)) :
    ∀ i, ContDiff ℝ ∞ (fun z => dbarFormFun2 x z i) := by
  intro i
  exact (contDiff_partialZbar_top (hx i.1) i.2).sub (contDiff_partialZbar_top (hx i.2) i.1)

lemma hasCompactSupport_dbarFormFun2 {x : FormDu d → (Fin d → ℂ)}
    (hsx : ∀ j, HasCompactSupport (fun z => x z j)) :
    HasCompactSupport (dbarFormFun2 x) := by
  refine hasCompactSupport_pi (fun i => ?_)
  exact (hasCompactSupport_partialZbar (hsx i.1) i.2).sub
    (hasCompactSupport_partialZbar (hsx i.2) i.1)

/-- Smooth compactly supported `(0,1)`-forms satisfy the weak `∂̄₂`-relation with `∂̄₂x` computed
pointwise. -/
theorem dbarWeak2_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {x : FormDu d → (Fin d → ℂ)}
    (hx : ∀ j, ContDiff ℝ ∞ (fun z => x z j)) (hsx : ∀ j, HasCompactSupport (fun z => x z j))
    (hmem : MemLp (liftForm x) 2 (wtMeasure φ))
    (hwm : MemLp (liftForm2 (dbarFormFun2 x)) 2 (wtMeasure φ)) :
    DbarWeak2 φ (hmem.toLp (liftForm x)) (hwm.toLp (liftForm2 (dbarFormFun2 x))) := by
  intro Ψ h1 h2 hΨ hθ
  have hx1 : ∀ j, ContDiff ℝ 1 (fun z => x z j) := fun j => (hx j).of_le hle1
  have hΘ1 : ∀ i, ContDiff ℝ 1 (fun z => toFormFun2 Ψ z i) :=
    fun i => (contDiff_toFormFun2 h1 i).of_le hle1
  have hΘ2 : ∀ i, ContDiff ℝ 1 (fun z => ((toFormFun2 Ψ) z i)) := hΘ1
  have hsΘ : ∀ i, HasCompactSupport (fun z => toFormFun2 Ψ z i) := fun i =>
    (hasCompactSupport_toFormFun2 h2).comp_left
      (g := fun v : Fin d × Fin d → ℂ => v i) (by simp)
  have hY1 : ∀ j, ContDiff ℝ 1 (fun z => star (x z j)) := fun j =>
    (Complex.conjCLE.contDiff).comp (hx1 j)
  have hsY : ∀ j, HasCompactSupport (fun z => star (x z j)) := fun j =>
    (hsx j).comp_left (by simp)
  have hA : inner ℂ (hΨ.toLp Ψ) (hwm.toLp (liftForm2 (dbarFormFun2 x)))
      = ∫ z, (∑ i, dbarFormFun2 x z i * star (Ψ z i))
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def]
    have hae : (fun z => inner ℂ ((hΨ.toLp Ψ : FormDu d → FormSpace2 d) z)
          ((hwm.toLp (liftForm2 (dbarFormFun2 x)) : FormDu d → FormSpace2 d) z))
        =ᵐ[wtMeasure φ] (fun z => inner ℂ (Ψ z) (liftForm2 (dbarFormFun2 x) z)) := by
      filter_upwards [MemLp.coeFn_toLp hΨ, MemLp.coeFn_toLp hwm] with z hz1 hz2
      rw [hz1, hz2]
    refine (integral_congr_ae hae).trans ?_
    · rw [integral_wtMeasure hφ.continuous]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change Real.exp (-(φ z)) • inner ℂ (Ψ z) (liftForm2 (dbarFormFun2 x) z)
        = (∑ i, dbarFormFun2 x z i * star (Ψ z i))
          * Complex.exp (-(((φ z : ℝ) : ℂ)))
      rw [PiLp.inner_apply]
      simp only [liftForm2_apply, RCLike.inner_apply, starRingEnd_apply, Complex.real_smul,
        Complex.ofReal_exp, Complex.ofReal_neg]
      ring
  have hB : inner ℂ (hθ.toLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))) (hmem.toLp (liftForm x))
      = ∫ z, (∑ j, x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [MeasureTheory.L2.inner_def]
    have hae : (fun z => inner ℂ ((hθ.toLp (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)))
            : FormDu d → FormSpace d) z)
          ((hmem.toLp (liftForm x) : FormDu d → FormSpace d) z))
        =ᵐ[wtMeasure φ] (fun z => inner ℂ (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) z)
          (liftForm x z)) := by
      filter_upwards [MemLp.coeFn_toLp hθ, MemLp.coeFn_toLp hmem] with z hz1 hz2
      rw [hz1, hz2]
    refine (integral_congr_ae hae).trans ?_
    · rw [integral_wtMeasure hφ.continuous]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change Real.exp (-(φ z)) • inner ℂ (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) z) (liftForm x z)
        = (∑ j, x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ)))
      rw [PiLp.inner_apply]
      simp only [liftForm_apply, RCLike.inner_apply, starRingEnd_apply, Complex.real_smul,
        Complex.ofReal_exp, Complex.ofReal_neg]
      ring
  rw [hA, hB]
  apply star_injective
  rw [integral_star_eq, integral_star_eq]
  have heq1 : (∫ z, star ((∑ i, dbarFormFun2 x z i * star (Ψ z i))
        * Complex.exp (-(((φ z : ℝ) : ℂ)))) ∂volume)
      = ∫ z, (∑ j, ∑ k, (partialZ k (fun w => star (x w j)) z
            - partialZ j (fun w => star (x w k)) z) * toFormFun2 Ψ z (j, k))
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    calc star ((∑ i, dbarFormFun2 x z i * star (Ψ z i))
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
        = star (Complex.exp (-(((φ z : ℝ) : ℂ))))
            * star (∑ i, dbarFormFun2 x z i * star (Ψ z i)) := star_mul _ _
      _ = Complex.exp (-(((φ z : ℝ) : ℂ)))
            * (∑ i, star (dbarFormFun2 x z i * star (Ψ z i))) := by
          rw [star_cexp_neg, star_sum]
      _ = Complex.exp (-(((φ z : ℝ) : ℂ)))
            * (∑ j, ∑ k, (partialZ k (fun w => star (x w j)) z
                - partialZ j (fun w => star (x w k)) z) * toFormFun2 Ψ z (j, k)) := by
          rw [show (∑ i, star (dbarFormFun2 x z i * star (Ψ z i)))
              = ∑ j, ∑ k, (partialZ k (fun w => star (x w j)) z
                  - partialZ j (fun w => star (x w k)) z) * toFormFun2 Ψ z (j, k) from ?_]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [star_mul, star_star, dbarFormFun2_apply, star_sub, star_partialZbar,
            star_partialZbar, toFormFun2_apply_apply]
          ring
      _ = (∑ j, ∑ k, (partialZ k (fun w => star (x w j)) z
                - partialZ j (fun w => star (x w k)) z) * toFormFun2 Ψ z (j, k))
            * Complex.exp (-(((φ z : ℝ) : ℂ))) := by ring
  have heq2 : (∫ z, star ((∑ j, x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
        * Complex.exp (-(((φ z : ℝ) : ℂ)))) ∂volume)
      = ∫ z, (∑ j, star (x z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    calc star ((∑ j, x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
        = star (Complex.exp (-(((φ z : ℝ) : ℂ))))
            * star (∑ j, x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j)) := star_mul _ _
      _ = Complex.exp (-(((φ z : ℝ) : ℂ)))
            * (∑ j, star (x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j))) := by
          rw [star_cexp_neg, star_sum]
      _ = Complex.exp (-(((φ z : ℝ) : ℂ)))
            * (∑ j, star (x z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j) := by
          rw [show (∑ j, star (x z j * star (dbarAdjoint2 φ (toFormFun2 Ψ) z j)))
              = ∑ j, star (x z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j from ?_]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [star_mul, star_star]
          ring
      _ = (∑ j, star (x z j) * dbarAdjoint2 φ (toFormFun2 Ψ) z j)
            * Complex.exp (-(((φ z : ℝ) : ℂ))) := by ring
  rw [heq1, heq2, integral_inner_dbar2_eq (Y := fun z j => star (x z j)) (Θ := toFormFun2 Ψ)
    hY1 hΘ2 hφ hsY hsΘ]

/-- The smooth compactly supported `(0,1)`-forms lie in the domain of `dbarOp2 φ`. -/
theorem mem_domain_dbarOp2_of_smooth {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {x : FormDu d → (Fin d → ℂ)} (hx : ∀ j, ContDiff ℝ ∞ (fun z => x z j))
    (hsx : ∀ j, HasCompactSupport (fun z => x z j)) :
    (memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous (contDiff_liftForm hx)
        (hasCompactSupport_liftForm (hasCompactSupport_pi hsx))).toLp (liftForm x)
      ∈ (dbarOp2 φ).domain :=
  mem_dbarOp2_domain.mpr ⟨_, dbarWeak2_smooth hφ hx hsx _
    (memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous
      (contDiff_liftForm2 (contDiff_dbarFormFun2 hx))
      (hasCompactSupport_liftForm2 (hasCompactSupport_dbarFormFun2 hsx)))⟩

/-- **The domain of the weak `(0,1) → (0,2)` operator is dense** in `L²(μ_φ)`. -/
theorem dense_domain_dbarOp2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Dense ((dbarOp2 φ).domain : Set (Lp (FormSpace d) 2 (wtMeasure φ))) := by
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  refine (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (μ := wtMeasure φ)
    (E := FormDu d) (F := FormSpace d) (by norm_num)).mono ?_
  rintro f ⟨g, hfg, hgs, hgc⟩
  have hgf : ∀ j, ContDiff ℝ ∞ (fun z => toFormFun g z j) := contDiff_toFormFun hgc
  have hsf : ∀ j, HasCompactSupport (fun z => toFormFun g z j) := fun j =>
    (hasCompactSupport_toFormFun hgs).comp_left (g := fun v : Fin d → ℂ => v j) (by simp)
  have hmem : MemLp g 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hgc hgs
  have hfeq : f = hmem.toLp g := Lp.ext (hfg.trans (MemLp.coeFn_toLp hmem).symm)
  have hgl : liftForm (toFormFun g) = g := by funext z; rfl
  rw [hfeq]
  have hm2 : MemLp (liftForm (toFormFun g)) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous (contDiff_liftForm hgf)
      (hasCompactSupport_liftForm (hasCompactSupport_pi hsf))
  have hgoal : hmem.toLp g = hm2.toLp (liftForm (toFormFun g)) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp hmem, MemLp.coeFn_toLp hm2] with z hz1 hz2
    rw [hz1, hz2]
    exact (WithLp.toLp_ofLp 2 (g z)).symm
  rw [hgoal]
  exact mem_domain_dbarOp2_of_smooth hφ hgf hsf

end SmoothDomain2

end Submission.FUP
