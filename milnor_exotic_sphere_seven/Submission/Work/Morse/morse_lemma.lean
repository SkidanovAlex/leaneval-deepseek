import Mathlib
import Submission.Work.Analysis.Hadamard.hadamard_bilinear
import Submission.Work.Analysis.MorseLambda.lambda_local
import Submission.Work.Analysis.BilinOperator.bilin_operator
import Submission.Work.Analysis.LocalDiffeomorph.local_diffeomorph_partial_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology RealInnerProductSpace
open Set Metric

/-- The adjoint of `2 • T + T * Pin * T` for a self-adjoint `Pin`. -/
private lemma star_lambda {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Pin T : E →L[ℝ] E) (hPin : star Pin = Pin) :
    star (2 • T + T * Pin * T) = 2 • star T + star T * Pin * star T := by
  simp only [star_add, star_smul, star_mul, hPin, star_ofNat, mul_assoc]

/-- A solution of `Λ T = W` with `W` self-adjoint is self-adjoint, by injectivity of `Λ`. -/
private lemma lambda_selfadjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (Pin : E →L[ℝ] E) (hPin : star Pin = Pin)
    (eL : OpenPartialHomeomorph (E →L[ℝ] E) (E →L[ℝ] E))
    (heLval : ∀ S ∈ eL.source, eL S = 2 • S + S * Pin * S)
    (T W : E →L[ℝ] E) (hT : T ∈ eL.source) (hTs : star T ∈ eL.source)
    (hW : star W = W) (heq : eL T = W) : star T = T := by
  have key : eL (star T) = eL T := by
    calc eL (star T) = star (2 • T + T * Pin * T) := by
            rw [heLval _ hTs, ← star_lambda Pin T hPin]
      _ = star (eL T) := by rw [heLval _ hT]
      _ = star W := by rw [heq]
      _ = W := hW
      _ = eL T := by rw [heq]
  calc star T = eL.symm (eL (star T)) := (eL.left_inv hTs).symm
    _ = eL.symm (eL T) := by rw [key]
    _ = T := eL.left_inv hT

/-- The congruence identity `A† P₀ A = P₀ + 2 • S + S Pin S` for `A = 1 + Pin S`. -/
private lemma lambda_congruence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (P₀ Pin S : E →L[ℝ] E) (hPin : star Pin = Pin)
    (hL : Pin * P₀ = 1) (hR : P₀ * Pin = 1) (hS : star S = S) :
    star (1 + Pin * S) * P₀ * (1 + Pin * S) = P₀ + (2 • S + S * Pin * S) := by
  have hstar : star (1 + Pin * S) = 1 + S * Pin := by
    rw [star_add, star_one, star_mul, hPin, hS]
  rw [hstar]
  have e1 : (1 + S * Pin) * P₀ = P₀ + S := by
    rw [add_mul, one_mul, mul_assoc, hL, mul_one]
  rw [e1]
  have e2 : (P₀ + S) * (1 + Pin * S) = P₀ + (2 • S + S * Pin * S) := by
    rw [mul_add, mul_one, add_mul, ← mul_assoc, hR, one_mul]
    rw [two_smul]
    abel
  rw [e2]

/-- The pairing `⟪(A† P A) v, v⟫ = ⟪P (A v), A v⟫`. -/
private lemma adjoint_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A P : E →L[ℝ] E) (v : E) :
    ⟪(star A * P * A) v, v⟫ = ⟪P (A v), A v⟫ := by
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem morse_lemma_general {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (h0 : f 0 = 0) (hgrad : fderiv ℝ f 0 = 0)
    (hB : ∀ v : E, (∀ w, (fderiv ℝ (fderiv ℝ f) 0) v w = 0) → v = 0) :
    ∃ ψ : OpenPartialHomeomorph E E, 0 ∈ ψ.source ∧ ψ 0 = 0 ∧
      ContDiffOn ℝ ∞ (⇑ψ) ψ.source ∧ ContDiffOn ℝ ∞ (⇑ψ.symm) ψ.target ∧
      (∀ x ∈ ψ.source, f x = (1 / 2) * ((fderiv ℝ (fderiv ℝ f) 0) (ψ x) (ψ x))) := by
  -- ## Step 1: the Hadamard factorisation
  obtain ⟨B, hBsm, hBsymm, hB0, hBval⟩ := Work.Analysis.Hadamard.hadamard_bilinear (E := E) hf
  -- ## Step 2: the smooth operator family representing `B`
  let G : E → (E →L[ℝ] E) := fun x => InnerProductSpace.continuousLinearMapOfBilin (B x)
  have hGsm : ContDiff ℝ ∞ G := by
    change ContDiff ℝ ∞ (fun x => InnerProductSpace.continuousLinearMapOfBilin (B x))
    have h : (fun x : E => InnerProductSpace.continuousLinearMapOfBilin (B x)) =
        fun x => ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘SL (B x) := by
      funext x; rfl
    rw [h]
    exact ContDiff.clm_comp contDiff_const hBsm
  have hGadj : ∀ x, ContinuousLinearMap.adjoint (G x) = G x := by
    intro x
    ext v
    apply ext_inner_right ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    show ⟪v, G x w⟫ = ⟪G x v, w⟫
    rw [← real_inner_comm v (G x w)]
    simp only [G, InnerProductSpace.continuousLinearMapOfBilin_apply]
    exact hBsymm x w v
  have hGstar : ∀ x, star (G x) = G x := fun x => by
    rw [ContinuousLinearMap.star_eq_adjoint, hGadj x]
  -- ## Step 3: the operator of the Hessian quadratic form and its inverse
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hsymm : ∀ v w, (fderiv ℝ (fderiv ℝ f) 0) v w = (fderiv ℝ (fderiv ℝ f) 0) w v :=
    second_derivative_symmetric
      (fun y => ((hf.contDiffAt (x := y)).differentiableAt (by simp)).hasFDerivAt)
      ((hdf.differentiable (by simp)).differentiableAt.hasFDerivAt)
  obtain ⟨P₀, Pin, hP0eq, hPinL, hPinR, hPinadj, hP0adj⟩ :=
    Work.Analysis.BilinOperator.bilin_operator (E := E) (fderiv ℝ (fderiv ℝ f) 0) (1 / 2)
      (by norm_num) hsymm hB
  have hP0star : star P₀ = P₀ := by rw [ContinuousLinearMap.star_eq_adjoint, hP0adj]
  have hPinstar : star (Pin : E →L[ℝ] E) = Pin := by
    rw [ContinuousLinearMap.star_eq_adjoint, hPinadj]
  have hG0 : G 0 = P₀ := by
    change InnerProductSpace.continuousLinearMapOfBilin (B 0) = P₀
    rw [hP0eq, hB0]
  -- ## Step 4: the local diffeomorphism solving the congruence equation
  obtain ⟨eL, heL0mem, heL0, heLsm, heLsymm, heLval⟩ :=
    Work.Analysis.MorseLambda.lambda_local (E := E) Pin
  let W : E → (E →L[ℝ] E) := fun x => G x - P₀
  have hWsm : ContDiff ℝ ∞ W := hGsm.sub contDiff_const
  have hW0 : W 0 = 0 := by simp [W, hG0]
  have hW0mem : W 0 ∈ eL.target := by
    rw [hW0, ← heL0]
    exact eL.map_source heL0mem
  let S : E → (E →L[ℝ] E) := fun x => eL.symm (W x)
  have hS0 : S 0 = 0 := by
    have h1 : S 0 = eL.symm (0 : E →L[ℝ] E) := by simp [S, hW0]
    have h2 : eL.symm (0 : E →L[ℝ] E) = eL.symm (eL 0) := by rw [heL0]
    rw [h1, h2, eL.left_inv heL0mem]
  have hScont : ContinuousAt S 0 := by
    change ContinuousAt (fun x => eL.symm (W x)) 0
    exact (eL.continuousAt_symm hW0mem).comp hWsm.continuous.continuousAt
  have hUnhds : W ⁻¹' eL.target ∈ 𝓝 (0 : E) :=
    hWsm.continuous.continuousAt.preimage_mem_nhds (eL.open_target.mem_nhds hW0mem)
  have hSsmOn : ContDiffOn ℝ ∞ S (W ⁻¹' eL.target) :=
    heLsymm.comp hWsm.contDiffOn (fun x hx => hx)
  -- ## Step 5: the set on which everything works
  let Vset : Set E :=
    {x | W x ∈ eL.target} ∩ ({x | S x ∈ eL.source} ∩ {x | star (S x) ∈ eL.source})
  have hVset : Vset ∈ 𝓝 (0 : E) := by
    have h1 : {x : E | W x ∈ eL.target} ∈ 𝓝 (0 : E) := hUnhds
    have h2 : {x : E | S x ∈ eL.source} ∈ 𝓝 (0 : E) :=
      hScont.preimage_mem_nhds (eL.open_source.mem_nhds (by rw [hS0]; exact heL0mem))
    have h3 : {x : E | star (S x) ∈ eL.source} ∈ 𝓝 (0 : E) := by
      have hc : ContinuousAt (fun x : E => star (S x)) 0 :=
        continuous_star.continuousAt.comp hScont
      refine hc.preimage_mem_nhds (eL.open_source.mem_nhds ?_)
      show star (S 0) ∈ eL.source
      rw [hS0, star_zero]
      exact heL0mem
    exact Filter.inter_mem h1 (Filter.inter_mem h2 h3)
  -- ## Step 6: `S` is self-adjoint on `Vset`
  have hSstar : ∀ x ∈ Vset, star (S x) = S x := by
    intro x hx
    exact lambda_selfadjoint (Pin : E →L[ℝ] E) hPinstar eL heLval (S x) (W x)
      hx.2.1 hx.2.2 (by simp only [W, star_sub, hGstar x, hP0star]) (eL.right_inv hx.1)
  -- ## Step 7: the map `φ` whose derivative at the origin is invertible
  let φ : E → E := fun x => (1 + (Pin : E →L[ℝ] E) * S x) x
  have hφ0 : φ 0 = 0 := by simp [φ, hS0]
  have hAsmOn : ContDiffOn ℝ ∞ (fun x : E => (1 : E →L[ℝ] E) + (Pin : E →L[ℝ] E) * S x)
      (W ⁻¹' eL.target) :=
    contDiffOn_const.add (contDiffOn_const.clm_comp hSsmOn)
  have hφsm : ContDiffOn ℝ ∞ φ (W ⁻¹' eL.target) := by
    change ContDiffOn ℝ ∞ (fun x => ((1 : E →L[ℝ] E) + (Pin : E →L[ℝ] E) * S x) x)
      (W ⁻¹' eL.target)
    exact hAsmOn.clm_apply contDiffOn_id
  have hφderiv : HasFDerivAt φ (1 : E →L[ℝ] E) 0 := by
    have hA : HasFDerivAt (fun x : E => (1 : E →L[ℝ] E) + (Pin : E →L[ℝ] E) * S x)
        (fderiv ℝ (fun x : E => (1 : E →L[ℝ] E) + (Pin : E →L[ℝ] E) * S x) 0) 0 :=
      ((hAsmOn.contDiffAt hUnhds).differentiableAt (by simp)).hasFDerivAt
    have h2 := hA.clm_apply (hasFDerivAt_id (0 : E))
    have hA0 : (1 : E →L[ℝ] E) + (Pin : E →L[ℝ] E) * S 0 = 1 := by simp [hS0]
    have hflip : (fderiv ℝ (fun x : E => (1 : E →L[ℝ] E) + (Pin : E →L[ℝ] E) * S x) 0).flip
        (0 : E) = 0 := by
      ext v; simp
    have hcomp : (1 : E →L[ℝ] E) ∘SL (ContinuousLinearMap.id ℝ E) = 1 := by
      ext v; simp
    simp only [id_eq] at h2
    rw [hA0, hcomp, hflip, add_zero] at h2
    convert h2 using 1
  -- ## Step 8: apply the inverse function theorem
  obtain ⟨ψ, hψ0mem, hψ0, hψsub, hψsm, hψsymm, hψeq⟩ :=
    Work.Analysis.LocalDiffeomorph.local_diffeomorph_partial_homeomorph
      (φ := φ) (e := ContinuousLinearEquiv.refl ℝ E) (U := W ⁻¹' eL.target) (V := Vset)
      hUnhds hVset hφ0 hφsm (by rw [ContinuousLinearEquiv.coe_refl]; exact hφderiv)
  refine ⟨ψ, hψ0mem, hψ0, hψsm, hψsymm, ?_⟩
  intro x hx
  have hxV : x ∈ Vset := (hψsub hx).2
  have hxφ : ψ x = φ x := hψeq x hx
  rw [hxφ]
  -- ## Step 9: the congruence identity
  have hconj : star (1 + (Pin : E →L[ℝ] E) * S x) * P₀ * (1 + (Pin : E →L[ℝ] E) * S x)
      = G x := by
    rw [lambda_congruence P₀ (Pin : E →L[ℝ] E) (S x) hPinstar hPinL hPinR (hSstar x hxV)]
    rw [← heLval (S x) hxV.2.1, eL.right_inv hxV.1]
    simp only [W]
    abel
  -- ## Step 10: conclude
  have hGx : f x = ⟪G x x, x⟫ := by
    have hv : f x = B x x x := by simpa [h0, hgrad] using hBval x
    rw [hv]
    simp only [G, InnerProductSpace.continuousLinearMapOfBilin_apply]
  calc f x = ⟪G x x, x⟫ := hGx
    _ = ⟪(star (1 + (Pin : E →L[ℝ] E) * S x) * P₀ * (1 + (Pin : E →L[ℝ] E) * S x)) x, x⟫ := by
          rw [hconj]
    _ = ⟪P₀ ((1 + (Pin : E →L[ℝ] E) * S x) x), (1 + (Pin : E →L[ℝ] E) * S x) x⟫ :=
          adjoint_pairing (1 + (Pin : E →L[ℝ] E) * S x) P₀ x
    _ = (1 / 2) * ((fderiv ℝ (fderiv ℝ f) 0) (φ x) (φ x)) := by
          rw [hP0eq, InnerProductSpace.continuousLinearMapOfBilin_apply]
          simp only [smul_apply, smul_eq_mul]
          rfl

theorem morse_lemma {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (h0 : f 0 = 0) (hgrad : fderiv ℝ f 0 = 0)
    (hB : ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ w, (fderiv ℝ (fderiv ℝ f) 0) v w = 0) → v = 0) :
    ∃ ψ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
      0 ∈ ψ.source ∧ ψ 0 = 0 ∧
      ContDiffOn ℝ ∞ (⇑ψ) ψ.source ∧ ContDiffOn ℝ ∞ (⇑ψ.symm) ψ.target ∧
      (∀ x ∈ ψ.source, f x = (1 / 2) * ((fderiv ℝ (fderiv ℝ f) 0) (ψ x) (ψ x))) := by
  exact morse_lemma_general hf h0 hgrad hB

end Work.Morse
