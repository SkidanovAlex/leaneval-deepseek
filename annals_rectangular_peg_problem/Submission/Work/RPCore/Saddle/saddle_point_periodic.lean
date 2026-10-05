import Mathlib
import Submission.Work.RPCore.Saddle.split_spectral_iso
import Submission.Work.RPCore.Saddle.exists_crit_of_saddle_split

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- **C5.**  Saddle-point theorem on `(ℝ / Pdℤ) × ℝ^M` for a bounded `C²` perturbation of the
nondegenerate quadratic form `v ↦ ⟪A v, v⟫ / 2` with `A` self-adjoint and injective.

The proof reduces to the split statement `exists_crit_of_saddle_split`:  the isometry
`split_spectral_iso` diagonalises `A` into a negative definite block `A₁` and a positive definite
block `A₂`, and the (finite-dimensional) linear change of variables `T` that realises this
diagonalisation preserves the `C`-closeness hypotheses up to the factor `√2`. -/
theorem saddle_point_periodic {M : ℕ} (F : ℝ × EuclideanSpace ℝ (Fin M) → ℝ)
    (hF : ContDiff ℝ 2 F) (Pd : ℝ) (hPd : 0 < Pd) (hper : ∀ a v, F (a + Pd, v) = F (a, v))
    (A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M))
    (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) (hAinj : Function.Injective A)
    (C : ℝ) (hC0 : ∀ a v, |F (a, v) - inner ℝ (A v) v / 2| ≤ C)
    (hC1 : ∀ a v, ‖fderiv ℝ F (a, v) - (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A v))‖ ≤ C) :
    ∃ z, fderiv ℝ F z = 0 := by
  classical
  -- Spectral splitting of the self-adjoint injective operator `A`.
  obtain ⟨k, l, hk, e, A₁, A₂, lam, K, hlam, hlamK, hA₁neg, hA₁norm, hA₂pos, hA₂norm, he, hin2⟩ :=
    split_spectral_iso A hA hAinj
  have hKnn : 0 ≤ K := le_trans hlam.le hlamK
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hCnn : 0 ≤ C := by
    have h := hC0 0 0
    have h1 : inner ℝ (A (0 : EuclideanSpace ℝ (Fin M))) 0 / 2 = 0 := by simp
    rw [h1, sub_zero] at h
    exact le_trans (abs_nonneg _) h
  -- The isometry `e` followed by the identification `WithLp 2 (Eₖ × E_l) ≃ Eₖ × E_l`.
  let eLs : WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin M) := e.symm
  let pce : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin l))).symm
  let eL : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin M) := eLs.comp pce
  have heL : ∀ p, eL p = e.symm (WithLp.toLp 2 p) := fun p => rfl
  have heLofLp : ∀ (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)),
      (e (eL p)).ofLp = p := by
    intro p; rw [heL p]; simp
  have heLfst : ∀ (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)),
      (e (eL p)).fst = p.1 := by
    intro p; rw [← WithLp.ofLp_fst (e (eL p)), heLofLp p]
  have heLsnd : ∀ (p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)),
      (e (eL p)).snd = p.2 := by
    intro p; rw [← WithLp.ofLp_snd (e (eL p)), heLofLp p]
  -- The linear change of variables.
  let T : (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) →L[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin M)) :=
    (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))).prod
      (eL.comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))))
  have hT : ∀ z, T z = (z.1, eL z.2) := by
    intro z
    rw [show T = (ContinuousLinearMap.fst ℝ ℝ
          (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))).prod
        (eL.comp (ContinuousLinearMap.snd ℝ ℝ
          (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))) from rfl]
    rw [ContinuousLinearMap.prod_apply]
    rfl
  let F' : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ := fun z => F (T z)
  -- `T` is `√2`-Lipschitz with respect to the product sup-norms.
  have hnorm : ∀ w : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)),
      ‖T w‖ ≤ Real.sqrt 2 * ‖w‖ := by
    intro w
    have hM0 : 0 ≤ ‖w‖ := norm_nonneg w
    have ha : |w.1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_fst_le w
    have hb : ‖w.2.1‖ ≤ ‖w‖ := le_trans (norm_fst_le w.2) (norm_snd_le w)
    have hc : ‖w.2.2‖ ≤ ‖w‖ := le_trans (norm_snd_le w.2) (norm_snd_le w)
    rw [hT w, Prod.norm_mk, Real.norm_eq_abs]
    have heLn : ‖eL w.2‖ = Real.sqrt (‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2) := by
      rw [heL w.2, e.symm.norm_map, WithLp.prod_norm_eq_of_L2]
      rfl
    rw [heLn]
    apply max_le
    · exact le_trans ha (le_mul_of_one_le_left hM0 hsqrt2)
    · have hb2 : ‖w.2.1‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hc2 : ‖w.2.2‖ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
      have hbc : ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 := by linarith
      calc Real.sqrt (‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2) ≤ Real.sqrt (2 * ‖w‖ ^ 2) :=
            Real.sqrt_le_sqrt hbc
        _ = Real.sqrt 2 * ‖w‖ := by
            rw [Real.sqrt_mul (by norm_num) (‖w‖ ^ 2), Real.sqrt_sq hM0]
  have hF' : ContDiff ℝ 2 F' := by
    show ContDiff ℝ 2 (F ∘ ⇑T)
    exact hF.comp T.contDiff
  have hper' : ∀ a q, F' (a + Pd, q) = F' (a, q) := by
    intro a q
    show F (T (a + Pd, q)) = F (T (a, q))
    rw [hT (a + Pd, q), hT (a, q)]
    exact hper a (eL q)
  have hC0'' : ∀ z, |F' z - (inner ℝ (A₁ z.2.1) z.2.1 + inner ℝ (A₂ z.2.2) z.2.2) / 2| ≤ C := by
    intro z
    have h := hC0 z.1 (eL z.2)
    have h2 := hin2 (eL z.2)
    rw [heLfst z.2, heLsnd z.2] at h2
    show |F (T z) - (inner ℝ (A₁ z.2.1) z.2.1 + inner ℝ (A₂ z.2.2) z.2.2) / 2| ≤ C
    rw [hT z, ← h2]
    exact h
  have hC0' : ∀ a v, |F' (a, v) - (inner ℝ (A₁ v.1) v.1 + inner ℝ (A₂ v.2) v.2) / 2| ≤
      Real.sqrt 2 * C :=
    fun a v => le_trans (hC0'' (a, v)) (le_mul_of_one_le_left hCnn hsqrt2)
  have hC1' : ∀ z w, |fderiv ℝ F' z w - (inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2)| ≤
      (Real.sqrt 2 * C) * ‖w‖ := by
    intro z w
    have hdT : DifferentiableAt ℝ (⇑T) z := T.differentiableAt
    have hdF : DifferentiableAt ℝ F (T z) := (hF.differentiable (by norm_num)).differentiableAt
    have hdiff : fderiv ℝ F' z = (fderiv ℝ F (T z)).comp T := by
      show fderiv ℝ (F ∘ ⇑T) z = _
      rw [fderiv_comp z hdF hdT, T.fderiv]
    -- The linearisation of the split quadratic form is exactly `L ∘ T`.
    have hL : (innerSL ℝ (A (T z).2)) (T w).2 =
        inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2 := by
      rw [hT z, hT w]
      show inner ℝ (A (eL z.2)) (eL w.2) = _
      calc inner ℝ (A (eL z.2)) (eL w.2)
          = inner ℝ (e (A (eL z.2))) (e (eL w.2)) := (e.inner_map_map _ _).symm
        _ = inner ℝ (WithLp.toLp 2 (A₁ (e (eL z.2)).fst, A₂ (e (eL z.2)).snd)) (e (eL w.2)) :=
              by rw [he]
        _ = inner ℝ (WithLp.toLp 2 (A₁ (e (eL z.2)).fst, A₂ (e (eL z.2)).snd))
              (WithLp.toLp 2 (e (eL w.2)).ofLp) := by rw [WithLp.toLp_ofLp]
        _ = inner ℝ (A₁ (e (eL z.2)).fst) (e (eL w.2)).ofLp.1
              + inner ℝ (A₂ (e (eL z.2)).snd) (e (eL w.2)).ofLp.2 := by
              rw [WithLp.prod_inner_apply, WithLp.ofLp_toLp]
        _ = inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2 := by
              rw [heLfst z.2, heLsnd z.2, heLofLp w.2]
    have hbound : |fderiv ℝ F (T z) (T w) -
        (inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2)| ≤ C * ‖T w‖ := by
      have hop := hC1 (T z).1 (T z).2
      have h3 : (fderiv ℝ F (T z) - (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A (T z).2))) (T w)
          = fderiv ℝ F (T z) (T w) -
            (inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2) := by
        rw [sub_apply, ContinuousLinearMap.coprod_apply, zero_apply, zero_add, hL]
      have h2 := ContinuousLinearMap.le_opNorm
        (fderiv ℝ F (T z) - (0 : ℝ →L[ℝ] ℝ).coprod (innerSL ℝ (A (T z).2))) (T w)
      rw [h3] at h2
      have h2' : ‖fderiv ℝ F (T z) (T w) -
          (inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2)‖ ≤ C * ‖T w‖ :=
        le_trans h2 (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      rwa [Real.norm_eq_abs] at h2'
    have hval : fderiv ℝ F' z w = fderiv ℝ F (T z) (T w) := by rw [hdiff]; rfl
    rw [hval]
    calc |fderiv ℝ F (T z) (T w) - (inner ℝ (A₁ z.2.1) w.2.1 + inner ℝ (A₂ z.2.2) w.2.2)|
        ≤ C * ‖T w‖ := hbound
      _ ≤ C * (Real.sqrt 2 * ‖w‖) := by gcongr; exact hnorm w
      _ = (Real.sqrt 2 * C) * ‖w‖ := by ring
  -- Apply the split saddle-point theorem.
  obtain ⟨z', hz'⟩ := exists_crit_of_saddle_split F' hF' Pd hPd hper' A₁ A₂ lam K (Real.sqrt 2 * C)
    hlam hKnn (mul_nonneg (Real.sqrt_nonneg 2) hCnn) hA₁neg hA₁norm hA₂pos hA₂norm
    hC0' (fun a v w => hC1' (a, v) w)
  -- Transport the critical point back through the linear change of variables.
  have hdT : DifferentiableAt ℝ (⇑T) z' := T.differentiableAt
  have hdF : DifferentiableAt ℝ F (T z') := (hF.differentiable (by norm_num)).differentiableAt
  have hdiff : fderiv ℝ F' z' = (fderiv ℝ F (T z')).comp T := by
    show fderiv ℝ (F ∘ ⇑T) z' = _
    rw [fderiv_comp z' hdF hdT, T.fderiv]
  have hcomp : (fderiv ℝ F (T z')).comp T = 0 := by rw [← hdiff]; exact hz'
  have hpt : ∀ w, fderiv ℝ F (T z') (T w) = 0 := by
    intro w
    have := congrArg (fun (f : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) →L[ℝ] ℝ) =>
      f w) hcomp
    simpa [ContinuousLinearMap.comp_apply] using this
  refine ⟨T z', ?_⟩
  refine ContinuousLinearMap.ext (fun y => ?_)
  obtain ⟨y1, y2⟩ := y
  have hsurj : T (y1, (e y2).ofLp) = (y1, y2) := by simp [hT, heL]
  rw [← hsurj]
  exact hpt (y1, (e y2).ofLp)

end Work.RPCore.Saddle
