import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Core.Lev.smoothTransition_deriv_data
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds
import Submission.Work.NN.Core.Lev.finset_prod_fderiv_bounds

open scoped ContDiff Topology BigOperators

namespace Work.NN.Core.Lev


/-- A finite product of real numbers in `[0,1]` is `≤ 1`. -/
lemma finset_prod_le_one_of {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.prod_insert his]
      have hi := h i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 := fun j hj => h j (Finset.mem_insert_of_mem hj)
      have ih' := ih hs
      have hnn : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg fun j hj => (hs j hj).1
      nlinarith [hi.1, hi.2, ih', hnn]

/-- **Polydisc cutoffs whose gradient is Lipschitz, with explicit constants.**

This is the second-derivative refinement of `Work.NN.Core.Lev.exists_polydisc_cutoff` (same
construction `χ(z) = Π_j ψ(((‖z_j‖² - R_j²)/((R_j+ε)² - R_j²)))` with a fixed smooth profile `ψ`
satisfying `ψ = 1` on `(-∞,0]`, `ψ = 0` on `[1,∞)`).  Besides the pointwise clauses one gets, with
`R_j ∈ [Rmin,Rmax]`, `Rmin > 0`, the bounds `‖∇χ‖ ≤ K'/ε` and `‖D²χ‖ ≤ K'/ε²` with `K'` depending
only on `n` and on the profile; both are absorbed by `K·(1+ε^{-p})` for suitable constants
`K > 0`, `p > 0` (e.g. `p = 2` works).  (The gradient of `χ̃` vanishes identically off the closed
shell `{∀j, ‖z_j‖ ≤ R_j + ε} ∩ {∃j, ‖z_j‖ ≥ R_j}`, and `∇χ̃ 0 = 0`, so the global bounds on
`‖∇χ̃‖` and on its Lipschitz constant are the same as on the shell.) -/
theorem exists_polydisc_cutoff_lipschitz {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Rmin Rmax : ℝ} (hRmin : 0 < Rmin) (hRmax : 0 < Rmax) :
    ∃ K : ℝ, 0 < K ∧ ∃ p : ℝ, 0 < p ∧
      ∀ (R : Fin n → ℝ) (ε : ℝ),
        (∀ j, Rmin ≤ R j) → (∀ j, R j ≤ Rmax) → 0 < ε →
        ∃ χ : (Fin n → ℂ) → ℝ,
          (∀ m : ℕ, ContDiff ℝ m χ) ∧
          (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
          (∀ z, (∀ j, ‖z j‖ ≤ R j) → χ z = 1) ∧
          (∀ z, (∃ j, R j + ε ≤ ‖z j‖) → χ z = 0) ∧
          (∀ x, ‖fderiv ℝ (fun z => (χ z : ℂ)) x‖ ≤ K * (1 + Real.rpow ε (-p))) ∧
          (∀ x y, ‖fderiv ℝ (fun z => (χ z : ℂ)) x - fderiv ℝ (fun z => (χ z : ℂ)) y‖
              ≤ K * (1 + Real.rpow ε (-p)) * ‖x - y‖) := by
  obtain ⟨C, hCpos, hC⟩ := sharpCut_fderiv_bounds
  have hCnn : 0 ≤ C := hCpos.le
  set A : ℝ := (n : ℝ) * C with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  set B : ℝ := 1 + 1 / Rmin with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  set K : ℝ := 1 + A + A ^ 2 + A * B with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKA : A ≤ K := by rw [hKdef]; nlinarith [hAnn, hBnn, sq_nonneg A]
  have hKA2 : A ^ 2 + A * B ≤ K := by rw [hKdef]; nlinarith [hAnn, hBnn, sq_nonneg A]
  refine ⟨K, hKpos, 2, by norm_num, ?_⟩
  intro R ε hRlo hRhi hε
  have hRpos : ∀ j, 0 < R j := fun j => lt_of_lt_of_le hRmin (hRlo j)
  have hRlt : ∀ j, R j < R j + ε := fun j => by linarith
  have hε2pos : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hinvεnn : 0 ≤ 1 / ε := div_nonneg zero_le_one hε.le
  have h1p : 0 ≤ 1 + 1 / ε ^ 2 :=
    add_nonneg zero_le_one (div_nonneg zero_le_one hε2pos.le)
  have hC1p : 0 ≤ C * (1 + 1 / ε ^ 2) := mul_nonneg hCnn h1p
  have hCB1p : 0 ≤ C * B * (1 + 1 / ε ^ 2) := mul_nonneg (mul_nonneg hCnn hBnn) h1p
  have hRmininvnn : 0 ≤ 1 / Rmin := div_nonneg zero_le_one hRmin.le
  have hCεnn : 0 ≤ C * (1 / ε) := mul_nonneg hCnn hinvεnn
  have hden : ∀ j, 0 ≤ C * (1 / (R j * ε) + 1 / ε ^ 2) := by
    intro j
    have h1 : 0 < R j * ε := mul_pos (hRpos j) hε
    exact mul_nonneg hCnn (add_nonneg (div_nonneg zero_le_one h1.le)
      (div_nonneg zero_le_one hε2pos.le))
  -- ## scalar inequalities in `ε`
  have hinvε : 1 / ε ≤ 1 + 1 / ε ^ 2 := by
    have h2 : (1 + 1 / ε ^ 2 - 1 / ε) = (ε ^ 2 - ε + 1) / ε ^ 2 := by
      field_simp
      ring
    have h3 : 0 ≤ ε ^ 2 - ε + 1 := by nlinarith [sq_nonneg (ε - 1 / 2)]
    have h4 : 0 ≤ 1 + 1 / ε ^ 2 - 1 / ε := by rw [h2]; positivity
    linarith
  have hinvε_sq : (1 / ε) ^ 2 = 1 / ε ^ 2 := by
    rw [div_pow, one_pow]
  have hrpow : Real.rpow ε (-2) = 1 / ε ^ 2 := by
    have h1 : Real.rpow ε (-2) = (Real.rpow ε (2 : ℝ))⁻¹ := Real.rpow_neg hε.le 2
    rw [h1, show Real.rpow ε (2 : ℝ) = ε ^ 2 from Real.rpow_natCast ε 2, one_div]
  -- ## the cutoff factors
  set Ψ : Fin n → (Fin n → ℂ) → ℂ := fun j z => Work.NN.Core.sharpCut (R j) (R j + ε) (z j)
    with hΨdef
  have hcd_sc : ∀ j, ContDiff ℝ ∞ (Work.NN.Core.sharpCut (R j) (R j + ε)) :=
    fun j => Work.NN.Core.contDiff_sharpCut (a := R j) (b := R j + ε)
  have hdiff_Ψ : ∀ (j : Fin n) (x : Fin n → ℂ), DifferentiableAt ℝ (Ψ j) x := by
    intro j x
    rw [show Ψ j = Work.NN.Core.sharpCut (R j) (R j + ε)
        ∘ ⇑((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) from rfl]
    exact DifferentiableAt.comp x (((hcd_sc j).differentiable (by simp)) (x j))
      (ContinuousLinearMap.differentiableAt _)
  have hproj : ∀ j : Fin n,
      ‖(ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ‖ ≤ 1 := by
    intro j
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm v j
  have hcomp_fac : ∀ (j : Fin n) (z : Fin n → ℂ), fderiv ℝ (Ψ j) z
      = (fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (z j)).comp
          ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) := by
    intro j z
    rw [show Ψ j = Work.NN.Core.sharpCut (R j) (R j + ε)
        ∘ ⇑((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ) from rfl]
    rw [fderiv_comp z (((hcd_sc j).differentiable (by simp)) (z j))
      (ContinuousLinearMap.differentiableAt _)]
    rw [ContinuousLinearMap.fderiv]
    rfl
  have hnorm_Ψ : ∀ (j : Fin n) (z : Fin n → ℂ), ‖Ψ j z‖ ≤ 1 :=
    fun j z => Work.NN.Core.norm_sharpCut_le_one (R j) (R j + ε) (z j)
  have hderiv_Ψ : ∀ (j : Fin n) (z : Fin n → ℂ), ‖fderiv ℝ (Ψ j) z‖ ≤ C * (1 / ε) := by
    intro j z
    have h := (hC (R j) (R j + ε) (hRpos j) (hRlt j)).1 (z j)
    rw [show (R j + ε) - R j = ε from by ring] at h
    calc ‖fderiv ℝ (Ψ j) z‖
        ≤ ‖fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (z j)‖
            * ‖(ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ‖ := by
          rw [hcomp_fac j z]
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (z j)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hproj j) (norm_nonneg _)
      _ = _ := mul_one _
      _ ≤ C * (1 / ε) := h
  have hlip_Ψ : ∀ (j : Fin n) (x y : Fin n → ℂ),
      ‖Ψ j x - Ψ j y‖ ≤ (C * (1 / ε)) * ‖x - y‖ := by
    intro j x y
    have h := (hC (R j) (R j + ε) (hRpos j) (hRlt j)).2.1 (x j) (y j)
    rw [show (R j + ε) - R j = ε from by ring] at h
    have hxy : ‖x j - y j‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) j
    calc ‖Ψ j x - Ψ j y‖
        = ‖Work.NN.Core.sharpCut (R j) (R j + ε) (x j)
            - Work.NN.Core.sharpCut (R j) (R j + ε) (y j)‖ := rfl
      _ ≤ C * (1 / ε) * ‖x j - y j‖ := h
      _ ≤ C * (1 / ε) * ‖x - y‖ := mul_le_mul_of_nonneg_left hxy hCεnn
  have hlipd_Ψ : ∀ (j : Fin n) (x y : Fin n → ℂ),
      ‖fderiv ℝ (Ψ j) x - fderiv ℝ (Ψ j) y‖
        ≤ C * (1 / (R j * ε) + 1 / ε ^ 2) * ‖x - y‖ := by
    intro j x y
    have h := (hC (R j) (R j + ε) (hRpos j) (hRlt j)).2.2 (x j) (y j)
    rw [show (R j + ε) - R j = ε from by ring] at h
    have hxy : ‖x j - y j‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) j
    calc ‖fderiv ℝ (Ψ j) x - fderiv ℝ (Ψ j) y‖
        = ‖((fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (x j))
            - (fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (y j))).comp
            ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ)‖ := by
          rw [hcomp_fac j x, hcomp_fac j y, ContinuousLinearMap.sub_comp]
      _ ≤ ‖(fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (x j))
            - (fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (y j))‖
            * ‖(ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).restrictScalars ℝ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (x j))
            - (fderiv ℝ (Work.NN.Core.sharpCut (R j) (R j + ε)) (y j))‖ * 1 :=
          mul_le_mul_of_nonneg_left (hproj j) (norm_nonneg _)
      _ = _ := mul_one _
      _ ≤ C * (1 / (R j * ε) + 1 / ε ^ 2) * ‖x j - y j‖ := h
      _ ≤ C * (1 / (R j * ε) + 1 / ε ^ 2) * ‖x - y‖ := mul_le_mul_of_nonneg_left hxy (hden j)
  -- the `Md` bound needed for the product lemma
  have hMd : ∀ (j : Fin n) (x y : Fin n → ℂ),
      ‖fderiv ℝ (Ψ j) x - fderiv ℝ (Ψ j) y‖ ≤ (C * B * (1 + 1 / ε ^ 2)) * ‖x - y‖ := by
    intro j x y
    refine le_trans (hlipd_Ψ j x y) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have h1 : 1 / (R j * ε) = (1 / R j) * (1 / ε) := by rw [one_div, one_div, one_div, mul_inv]
    have h2 : 1 / R j ≤ 1 / Rmin := one_div_le_one_div_of_le hRmin (hRlo j)
    have h2' : (1 / R j) * (1 / ε) ≤ (1 / Rmin) * (1 / ε) :=
      mul_le_mul_of_nonneg_right h2 hinvεnn
    have h3 : (1 / Rmin) * (1 / ε) ≤ (1 / Rmin) * (1 + 1 / ε ^ 2) :=
      mul_le_mul_of_nonneg_left hinvε hRmininvnn
    have h3' : 1 / ε ^ 2 ≤ 1 + 1 / ε ^ 2 := by linarith
    have hkey : 1 / (R j * ε) + 1 / ε ^ 2 ≤ (1 + 1 / Rmin) * (1 + 1 / ε ^ 2) := by
      have h4 : (1 / Rmin) * (1 + 1 / ε ^ 2) + (1 + 1 / ε ^ 2)
          = (1 + 1 / Rmin) * (1 + 1 / ε ^ 2) := by ring
      rw [h1]; linarith [h2', h3, h3', h4]
    calc C * (1 / (R j * ε) + 1 / ε ^ 2)
        ≤ C * ((1 + 1 / Rmin) * (1 + 1 / ε ^ 2)) := mul_le_mul_of_nonneg_left hkey hCnn
      _ = C * B * (1 + 1 / ε ^ 2) := by rw [hBdef]; ring
  -- ## the cutoff itself
  refine ⟨fun z => ∏ j, Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    have hfac : ∀ j : Fin n, ContDiff ℝ m
        (fun z : Fin n → ℂ =>
          Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j))) := by
      intro j
      refine ((Work.NN.Core.contDiff_sharpCutReal (a := R j) (b := R j + ε)).of_le (by simp)).comp
        ?_
      exact (Work.NN.Core.contDiff_normSq'.of_le (by simp)).comp (contDiff_apply ℝ ℂ j)
    have hind : ∀ s : Finset (Fin n), ContDiff ℝ m
        (fun z : Fin n → ℂ =>
          ∏ j ∈ s, Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using contDiff_const
      | insert j s hjs ih =>
          have hfun : (fun z : Fin n → ℂ =>
                ∏ k ∈ insert j s, Work.NN.Core.sharpCutReal (R k) (R k + ε) (Complex.normSq (z k)))
              = (fun z : Fin n → ℂ =>
                  Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j)))
                * (fun z : Fin n → ℂ =>
                    ∏ k ∈ s, Work.NN.Core.sharpCutReal (R k) (R k + ε) (Complex.normSq (z k))) := by
            funext z
            show (∏ k ∈ insert j s, Work.NN.Core.sharpCutReal (R k) (R k + ε) (Complex.normSq (z k)))
              = Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j))
                * (∏ k ∈ s, Work.NN.Core.sharpCutReal (R k) (R k + ε) (Complex.normSq (z k)))
            rw [Finset.prod_insert hjs]
          rw [hfun]
          exact (hfac j).mul ih
    exact hind Finset.univ
  · intro z
    refine ⟨Finset.prod_nonneg (fun j _ => Work.NN.Core.sharpCutReal_nonneg _ _ _), ?_⟩
    exact finset_prod_le_one_of Finset.univ _
      (fun j _ => ⟨Work.NN.Core.sharpCutReal_nonneg _ _ _, Work.NN.Core.sharpCutReal_le_one _ _ _⟩)
  · intro z hz
    refine Finset.prod_eq_one (fun j _ => ?_)
    refine Work.NN.Core.sharpCutReal_eq_one (le_of_lt (hRpos j)) (hRlt j) ?_
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hz j) 2
  · intro z hz
    obtain ⟨j, hj⟩ := hz
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    refine Work.NN.Core.sharpCutReal_eq_zero (le_of_lt (hRpos j)) (hRlt j) ?_
    rw [Complex.normSq_eq_norm_sq]
    have hpos : (0 : ℝ) ≤ R j + ε := by linarith [hRpos j, hε]
    exact pow_le_pow_left₀ hpos hj 2
  · intro x
    have hcc : (fun z : Fin n → ℂ =>
        ((∏ j, Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j)) : ℝ) : ℂ))
        = fun z => ∏ j, Ψ j z := by
      funext z
      rw [Complex.ofReal_prod]
      rfl
    rw [hcc]
    have hp := fderiv_finset_prod_norm_le (u := Ψ) (x := x) (M := fun _ : Fin n => C * (1 / ε))
      (fun j => hdiff_Ψ j x) (fun j => hderiv_Ψ j x) (fun j => hnorm_Ψ j x)
    have hsum : (∑ _j : Fin n, C * (1 / ε)) = A * (1 / ε) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hAdef]
      ring
    calc ‖fderiv ℝ (fun z => ∏ j, Ψ j z) x‖ ≤ ∑ _j : Fin n, C * (1 / ε) := hp
      _ = A * (1 / ε) := hsum
      _ ≤ A * (1 + 1 / ε ^ 2) := mul_le_mul_of_nonneg_left hinvε hAnn
      _ ≤ K * (1 + 1 / ε ^ 2) := mul_le_mul_of_nonneg_right hKA h1p
      _ = K * (1 + Real.rpow ε (-2)) := by rw [hrpow]
  · intro x y
    have hcc : (fun z : Fin n → ℂ =>
        ((∏ j, Work.NN.Core.sharpCutReal (R j) (R j + ε) (Complex.normSq (z j)) : ℝ) : ℂ))
        = fun z => ∏ j, Ψ j z := by
      funext z
      rw [Complex.ofReal_prod]
      rfl
    rw [hcc]
    have hp := fderiv_finset_prod_sub_le (u := Ψ) (x := x) (y := y)
      (L := fun _ : Fin n => C * (1 / ε)) (M := fun _ : Fin n => C * (1 / ε))
      (Md := fun _ : Fin n => C * B * (1 + 1 / ε ^ 2))
      (fun j => hdiff_Ψ j x) (fun j => hdiff_Ψ j y)
      (fun _ => hCεnn) (fun _ => hCεnn) (fun _ => hCB1p)
      (fun j => hderiv_Ψ j x) (fun j => hlip_Ψ j x y) (fun j => hMd j x y)
      (fun j => hnorm_Ψ j x) (fun j => hnorm_Ψ j y)
    have hsumL : (∑ _j : Fin n, C * (1 / ε)) = A * (1 / ε) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hAdef]
      ring
    have hsumMd : (∑ _j : Fin n, C * B * (1 + 1 / ε ^ 2)) = A * B * (1 + 1 / ε ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hAdef]
      ring
    have hkey : (A * (1 / ε)) * (A * (1 / ε)) + A * B * (1 + 1 / ε ^ 2)
        ≤ K * (1 + 1 / ε ^ 2) := by
      have h1 : (A * (1 / ε)) * (A * (1 / ε)) = A ^ 2 * ((1 / ε) ^ 2) := by ring
      have h1' : A ^ 2 * ((1 / ε) ^ 2) = A ^ 2 * (1 / ε ^ 2) := by rw [hinvε_sq]
      have h2 : A ^ 2 * (1 / ε ^ 2) ≤ A ^ 2 * (1 + 1 / ε ^ 2) := by
        have h2' : 1 / ε ^ 2 ≤ 1 + 1 / ε ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_left h2' (by positivity)
      have h3 : A ^ 2 * (1 + 1 / ε ^ 2) + A * B * (1 + 1 / ε ^ 2)
          = (A ^ 2 + A * B) * (1 + 1 / ε ^ 2) := by ring
      have h4 : (A ^ 2 + A * B) * (1 + 1 / ε ^ 2) ≤ K * (1 + 1 / ε ^ 2) :=
        mul_le_mul_of_nonneg_right hKA2 h1p
      linarith [h1, h1', h2, h3, h4]
    calc ‖fderiv ℝ (fun z => ∏ j, Ψ j z) x - fderiv ℝ (fun z => ∏ j, Ψ j z) y‖
        ≤ ((∑ _j : Fin n, C * (1 / ε)) * (∑ _j : Fin n, C * (1 / ε))
            + ∑ _j : Fin n, C * B * (1 + 1 / ε ^ 2)) * ‖x - y‖ := hp
      _ = ((A * (1 / ε)) * (A * (1 / ε)) + A * B * (1 + 1 / ε ^ 2)) * ‖x - y‖ := by
          rw [hsumL, hsumMd]
      _ ≤ (K * (1 + 1 / ε ^ 2)) * ‖x - y‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      _ = K * (1 + Real.rpow ε (-2)) * ‖x - y‖ := by rw [hrpow]
end Work.NN.Core.Lev
