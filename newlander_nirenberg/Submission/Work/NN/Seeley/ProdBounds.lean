/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Bounds for the shear maps used in the Seeley extension

We bound the global-derivative norms `gDN` and seminorms `gSN` of the functions
`p ↦ u (p.1, c * p.2)` and `p ↦ seeleyCut (c * p.2)`.
-/
import Mathlib
import Submission.Work.NN.Seeley.Glob

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Final

open Work.CR.Flat.Holder

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The linear map `p ↦ (p.1, c * p.2)` on `X × ℝ`. -/
def seeleyLam (c : ℝ) : X × ℝ →L[ℝ] X × ℝ :=
  (ContinuousLinearMap.fst ℝ X ℝ).prod (c • ContinuousLinearMap.snd ℝ X ℝ)

@[simp] lemma seeleyLam_apply (c : ℝ) (p : X × ℝ) :
    seeleyLam (X := X) c p = (p.1, c * p.2) := rfl

lemma norm_seeleyLam_le (c : ℝ) : ‖seeleyLam (X := X) c‖ ≤ max 1 |c| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _)) fun p => ?_
  simp only [seeleyLam_apply, Prod.norm_mk, smul_eq_mul, Real.norm_eq_abs, abs_mul]
  refine max_le ?_ ?_
  · calc ‖p.1‖ ≤ max ‖p.1‖ |p.2| := le_max_left _ _
      _ = 1 * max ‖p.1‖ |p.2| := (one_mul _).symm
      _ ≤ max 1 |c| * max ‖p.1‖ |p.2| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_of_le_left (norm_nonneg p.1))
  · refine mul_le_mul (le_max_right _ _) (le_max_right _ _) (abs_nonneg _) ?_
    exact le_trans zero_le_one (le_max_left _ _)

/-- The chain rule for the iterated derivative of the composition with `seeleyLam`. -/
lemma iteratedFDeriv_comp_seeleyLam {i : ℕ} {u : X × ℝ → ℂ} (hu : ContDiff ℝ i u) (c : ℝ)
    (x : X × ℝ) :
    iteratedFDeriv ℝ i (u ∘ seeleyLam (X := X) c) x
      = (iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)).compContinuousLinearMap
          (fun _ => seeleyLam (X := X) c) := by
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := seeleyLam (X := X) c) (s := Set.univ) (f := u) (x := x) (i := i)
    (contDiffOn_univ.mpr hu) uniqueDiffOn_univ uniqueDiffOn_univ (Set.mem_univ x) le_rfl
  simpa only [iteratedFDerivWithin_univ, Set.preimage_univ, Function.comp_apply,
    seeleyLam_apply] using h

lemma compContinuousLinearMap_sub_const {i : ℕ}
    (a b : ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) ℂ) (c : ℝ) :
    a.compContinuousLinearMap (fun _ => seeleyLam (X := X) c)
      - b.compContinuousLinearMap (fun _ => seeleyLam (X := X) c)
      = (a - b).compContinuousLinearMap (fun _ => seeleyLam (X := X) c) := by
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, sub_apply]

lemma norm_compContinuousLinearMap_const_le {i : ℕ}
    (a : ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) ℂ) (c : ℝ) :
    ‖a.compContinuousLinearMap (fun _ => seeleyLam (X := X) c)‖
      ≤ ‖a‖ * (max 1 |c|) ^ i := by
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_seeleyLam_le c) i)
    (norm_nonneg _)

/-- Sup-norm bound for the pullback under the shear `p ↦ (p.1, c * p.2)`. -/
theorem gDN_comp_prod_snd_le {c : ℝ} {i : ℕ} {u : X × ℝ → ℂ} (hu : ContDiff ℝ i u)
    {Ω : Set (X × ℝ)} :
    gDN i (fun p : X × ℝ => u (p.1, c * p.2)) Ω
      ≤ ENNReal.ofReal ((max 1 |c|) ^ i)
          * gDN i u ((fun p : X × ℝ => (p.1, c * p.2)) '' Ω) := by
  refine iSup₂_le fun x hx => ?_
  rw [show (fun p : X × ℝ => u (p.1, c * p.2)) = u ∘ seeleyLam (X := X) c from rfl,
    iteratedFDeriv_comp_seeleyLam hu c x]
  calc ENNReal.ofReal ‖(iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)).compContinuousLinearMap
          (fun _ => seeleyLam (X := X) c)‖
      ≤ ENNReal.ofReal (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)‖
          * (max 1 |c|) ^ i) :=
        ENNReal.ofReal_le_ofReal (norm_compContinuousLinearMap_const_le _ c)
    _ = ENNReal.ofReal (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)‖)
          * ENNReal.ofReal ((max 1 |c|) ^ i) := ENNReal.ofReal_mul (norm_nonneg _)
    _ = ENNReal.ofReal ((max 1 |c|) ^ i)
          * ENNReal.ofReal (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)‖) := mul_comm _ _
    _ ≤ ENNReal.ofReal ((max 1 |c|) ^ i)
          * gDN i u ((fun p : X × ℝ => (p.1, c * p.2)) '' Ω) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [seeleyLam_apply]
        exact le_gDN i (Set.mem_image_of_mem _ hx)

/-- Hölder-seminorm bound for the pullback under the shear `p ↦ (p.1, c * p.2)`. -/
theorem gSN_comp_prod_snd_le {c : ℝ} {i : ℕ} {α : ℝ} (hα : 0 ≤ α) {u : X × ℝ → ℂ}
    (hu : ContDiff ℝ i u) {Ω : Set (X × ℝ)} :
    gSN i α (fun p : X × ℝ => u (p.1, c * p.2)) Ω
      ≤ ENNReal.ofReal ((max 1 |c|) ^ (i + α))
          * gSN i α u ((fun p : X × ℝ => (p.1, c * p.2)) '' Ω) := by
  have hM1 : (1:ℝ) ≤ max 1 |c| := le_max_left _ _
  have hMpos : 0 < max 1 |c| := lt_of_lt_of_le one_pos hM1
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [show (fun p : X × ℝ => u (p.1, c * p.2)) = u ∘ seeleyLam (X := X) c from rfl,
    iteratedFDeriv_comp_seeleyLam hu c x, iteratedFDeriv_comp_seeleyLam hu c y,
    compContinuousLinearMap_sub_const]
  by_cases hxy' : seeleyLam (X := X) c x = seeleyLam (X := X) c y
  · rw [hxy', sub_self]
    have hz : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) ℂ).compContinuousLinearMap
        (fun _ => seeleyLam (X := X) c) = 0 := by
      ext m
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, zero_apply]
    rw [hz]
    simp only [norm_zero, zero_div, ENNReal.ofReal_zero]
    exact bot_le
  · have hnum : (0:ℝ) < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    have hden : (0:ℝ) < ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy')) _
    have hnorm := norm_compContinuousLinearMap_const_le
      (iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
        - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)) c
    have hle : ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ≤ (max 1 |c|) * ‖x - y‖ := by
      calc ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖
          = ‖seeleyLam (X := X) c (x - y)‖ := by rw [map_sub]
        _ ≤ ‖seeleyLam (X := X) c‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max 1 |c| * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right (norm_seeleyLam_le c) (norm_nonneg _)
    have key : ‖(iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
            - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)).compContinuousLinearMap
            (fun _ => seeleyLam (X := X) c)‖ / ‖x - y‖ ^ α
        ≤ (max 1 |c|) ^ (i + α)
          * (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖
            / ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α) := by
      have h1 : ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α
          ≤ (max 1 |c|) ^ α * ‖x - y‖ ^ α := by
        rw [← Real.mul_rpow hMpos.le (norm_nonneg _)]
        exact Real.rpow_le_rpow (norm_nonneg _) hle hα
      have hkey : (1:ℝ) / ‖x - y‖ ^ α
          ≤ (max 1 |c|) ^ α / ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α := by
        rw [div_le_iff₀ hnum, div_mul_eq_mul_div, le_div_iff₀ hden, one_mul]
        exact h1
      refine (div_le_div_of_nonneg_right hnorm hnum.le).trans ?_
      calc ‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖ * (max 1 |c|) ^ i
              / ‖x - y‖ ^ α
          = (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖ * (max 1 |c|) ^ i)
              * (1 / ‖x - y‖ ^ α) := by ring
        _ ≤ (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖ * (max 1 |c|) ^ i)
              * ((max 1 |c|) ^ α
                / ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (max 1 |c|) ^ (i + α)
              * (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖
                / ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α) := by
            rw [Real.rpow_add hMpos, Real.rpow_natCast]
            ring
    calc ENNReal.ofReal
          (‖(iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)).compContinuousLinearMap
              (fun _ => seeleyLam (X := X) c)‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((max 1 |c|) ^ (i + α)
            * (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖
              / ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α)) :=
          ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal ((max 1 |c|) ^ (i + α))
            * ENNReal.ofReal (‖iteratedFDeriv ℝ i u (seeleyLam (X := X) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := X) c y)‖
              / ‖seeleyLam (X := X) c x - seeleyLam (X := X) c y‖ ^ α) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg hMpos.le _)
      _ ≤ ENNReal.ofReal ((max 1 |c|) ^ (i + α))
            * gSN i α u ((fun p : X × ℝ => (p.1, c * p.2)) '' Ω) := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          rw [seeleyLam_apply, seeleyLam_apply]
          exact le_gSN i α (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy) hxy'


/-! ## Bounds for the cutoff `χ (c * p.2)` -/

/-- The `i`-th iterated derivative of the cutoff composed with `t ↦ c * t`. -/
lemma iteratedFDeriv_cutoff (c : ℝ) (i : ℕ) (p : X × ℝ) :
    iteratedFDeriv ℝ i ((fun p : X × ℝ => seeleyCut (c * p.2)) : X × ℝ → ℝ) p
      = (iteratedFDeriv ℝ i seeleyCut (c * p.2)).compContinuousLinearMap
          (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ) := by
  have hcut : ContDiff ℝ (i : WithTop ENat) (seeleyCut : ℝ → ℝ) :=
    seeleyCut_contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := c • ContinuousLinearMap.snd ℝ X ℝ) (s := Set.univ) (f := seeleyCut)
    (x := p) (i := i) (contDiffOn_univ.mpr hcut) uniqueDiffOn_univ uniqueDiffOn_univ
    (Set.mem_univ p) le_rfl
  have hp : (c • ContinuousLinearMap.snd ℝ X ℝ) p = c * p.2 := by simp
  rw [hp] at h
  rw [show ((fun p : X × ℝ => seeleyCut (c * p.2)) : X × ℝ → ℝ)
      = (seeleyCut ∘ ⇑(c • ContinuousLinearMap.snd ℝ X ℝ)) from rfl]
  simpa only [iteratedFDerivWithin_univ, Set.preimage_univ, Function.comp_apply] using h

lemma compContinuousLinearMap_sub_const' {i : ℕ}
    (a b : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝ) ℝ) (c : ℝ) :
    a.compContinuousLinearMap (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)
      - b.compContinuousLinearMap (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)
      = (a - b).compContinuousLinearMap (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ) := by
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, sub_apply]

/-- The iterated derivatives of the cutoff are Lipschitz with constant `seeleyCutB (i+1)`. -/
lemma cutoff_lipschitz (i : ℕ) (s t : ℝ) :
    ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s - iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖
      ≤ seeleyCutB (i + 1) * |s - t| := by
  have hcut : ContDiff ℝ ∞ (seeleyCut : ℝ → ℝ) := seeleyCut_contDiff
  have hdiff : ∀ u : ℝ, DifferentiableAt ℝ (fun v => iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) v) u :=
    fun u => (hcut.contDiffAt.iteratedFDeriv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hbound : ∀ u : ℝ,
      ‖deriv (fun v => iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) v) u‖ ≤ seeleyCutB (i + 1) := by
    intro u
    have h1 : ‖deriv (fun v => iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) v) u‖
        ≤ ‖fderiv ℝ (fun v => iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) v) u‖ := by
      rw [deriv]
      exact le_trans (ContinuousLinearMap.le_opNorm _ (1:ℝ)) (le_of_eq (by rw [norm_one, mul_one]))
    refine h1.trans ?_
    rw [norm_fderiv_iteratedFDeriv]
    exact norm_iteratedFDeriv_seeleyCut_le (i + 1) u
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (C := seeleyCutB (i + 1))
    (fun u _ => hdiff u) (fun u _ => hbound u) convex_univ (Set.mem_univ t) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs] using h

/-- Sup-norm bound for the normal cutoff `p ↦ seeleyCut (c * p.2)`. -/
theorem gDN_cutoff_le {c : ℝ} {i : ℕ} {Ω : Set (X × ℝ)} :
    gDN i (fun p : X × ℝ => seeleyCut (c * p.2)) Ω
      ≤ ENNReal.ofReal (|c| ^ i * seeleyCutB i) := by
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDeriv_cutoff]
  have hsnd : ‖c • ContinuousLinearMap.snd ℝ X ℝ‖ ≤ |c| := by
    refine le_trans (norm_smul_le c (ContinuousLinearMap.snd ℝ X ℝ)) ?_
    rw [mul_comm]
    refine mul_le_of_le_one_left (abs_nonneg c) ?_
    rw [ContinuousLinearMap.norm_snd]
  have hnorm : ‖(iteratedFDeriv ℝ i seeleyCut (c * x.2)).compContinuousLinearMap
      (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)‖ ≤ seeleyCutB i * |c| ^ i := by
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i seeleyCut (c * x.2))
      (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    refine h1.trans ?_
    exact mul_le_mul (norm_iteratedFDeriv_seeleyCut_le i _)
      (pow_le_pow_left₀ (norm_nonneg _) hsnd i) (by positivity) (seeleyCutB_nonneg i)
  refine le_trans (ENNReal.ofReal_le_ofReal hnorm) (le_of_eq ?_)
  rw [mul_comm]

/-- The `α`-Hölder seminorm of the `i`-th derivative of the cutoff is bounded. -/
lemma cutoff_holder (i : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {s t : ℝ} (hst : s ≠ t) :
    ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s - iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖
        / |s - t| ^ α ≤ 2 * seeleyCutB i + seeleyCutB (i + 1) := by
  have hst' : (0:ℝ) < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
  have hden : (0:ℝ) < |s - t| ^ α := Real.rpow_pos_of_pos hst' _
  have hA : (0:ℝ) ≤ seeleyCutB i := seeleyCutB_nonneg i
  have hB : (0:ℝ) ≤ seeleyCutB (i + 1) := seeleyCutB_nonneg (i + 1)
  rcases le_total |s - t| 1 with hr | hr
  · rw [div_le_iff₀ hden]
    have hrpow : |s - t| ≤ |s - t| ^ α := by
      have h := Real.rpow_le_rpow_of_exponent_ge hst' hr hα1
      rwa [Real.rpow_one] at h
    have h1 := cutoff_lipschitz i s t
    nlinarith [h1, hrpow, hden, hA, hB, hst']
  · rw [div_le_iff₀ hden]
    have hrpow : (1:ℝ) ≤ |s - t| ^ α := Real.one_le_rpow hr hα
    have hnum : ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s
        - iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖ ≤ 2 * seeleyCutB i := by
      calc ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s
            - iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖
          ≤ ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s‖
            + ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖ := norm_sub_le _ _
        _ ≤ seeleyCutB i + seeleyCutB i :=
            add_le_add (norm_iteratedFDeriv_seeleyCut_le i s) (norm_iteratedFDeriv_seeleyCut_le i t)
        _ = 2 * seeleyCutB i := by ring
    nlinarith [hnum, hrpow, hden, hA, hB]

end Work.NN.Final
