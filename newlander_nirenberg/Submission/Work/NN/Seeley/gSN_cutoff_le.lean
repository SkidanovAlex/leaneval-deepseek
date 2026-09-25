/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Hölder-seminorm bound for the normal cutoff `p ↦ seeleyCut (c * p.2)`

We bound the global Hölder seminorm of the `i`-th iterated derivative of the normal cutoff
`p ↦ seeleyCut (c * p.2)` on `X × ℝ` (where `seeleyCut` is a smooth bump equal to `1` on
`[-1,1]` and vanishing off `[-2,2]`) by

  `|c| ^ (i + 1 + α) * (2 * seeleyCutB i + seeleyCutB (i + 1))`.

The two ingredients are

* the chain rule for the iterated derivative of the composition with the shear `p ↦ (p.1, c*p.2)`
  (only the normal variable matters here), which produces the factor `|c| ^ i`; and
* the two-point Hölder bound for the derivatives of the cutoff itself,
  `‖D^i χ s - D^i χ t‖ ≤ (2 * seeleyCutB i + seeleyCutB (i+1)) * |s - t| ^ α`,
  which is the interpolation between the sup-norm bound `seeleyCutB i` and the Lipschitz bound
  `seeleyCutB (i+1)` for `0 ≤ α ≤ 1`.

The comparison `|c * x.2 - c * y.2| ≤ |c| * ‖x - y‖`, together with `1 ≤ |c|`, accounts for the
remaining factor `|c| ^ (1 + α)`.
-/
import Mathlib
import Submission.Work.NN.Seeley.Glob

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Seeley

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Elementary bounds for the derivatives of the cutoff -/

/-- The chain rule for the iterated derivative of the cutoff composed with `t ↦ c * t`; only the
second coordinate of `p` matters. -/
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

/-- Composition with a fixed linear map commutes with differences of multilinear maps. -/
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

/-- Two-point Hölder bound for the derivatives of the cutoff, valid for `0 ≤ α ≤ 1` and all
`(s,t)` (also when `s = t`, where both sides vanish). -/
lemma cutoff_holder_all (i : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (s t : ℝ) :
    ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s - iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖
        ≤ (2 * seeleyCutB i + seeleyCutB (i + 1)) * |s - t| ^ α := by
  have hA : (0:ℝ) ≤ seeleyCutB i := seeleyCutB_nonneg i
  have hB : (0:ℝ) ≤ seeleyCutB (i + 1) := seeleyCutB_nonneg (i + 1)
  rcases eq_or_ne s t with h | h
  · subst h
    rw [sub_self, norm_zero, sub_self, abs_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg le_rfl α)
  · have hst' : (0:ℝ) < |s - t| := abs_pos.mpr (sub_ne_zero.mpr h)
    have hden : (0:ℝ) < |s - t| ^ α := Real.rpow_pos_of_pos hst' _
    rw [← div_le_iff₀ hden]
    rcases lt_or_ge |s - t| 1 with hr | hr
    · -- small distances: the Lipschitz bound is the sharper one
      rw [div_le_iff₀ hden]
      have hrpow : |s - t| ≤ |s - t| ^ α := by
        have h := Real.rpow_le_rpow_of_exponent_ge hst' hr.le hα1
        rwa [Real.rpow_one] at h
      have h1 := cutoff_lipschitz i s t
      nlinarith [h1, hrpow, hden, hA, hB, hst']
    · -- large distances: the sup-norm bound is the sharper one
      rw [div_le_iff₀ hden]
      have hrpow : (1:ℝ) ≤ |s - t| ^ α := Real.one_le_rpow hr hα
      have hnum : ‖iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) s
          - iteratedFDeriv ℝ i (seeleyCut : ℝ → ℝ) t‖ ≤ 2 * seeleyCutB i := by
        refine (norm_sub_le _ _).trans ?_
        rw [two_mul]
        exact add_le_add (norm_iteratedFDeriv_seeleyCut_le i s) (norm_iteratedFDeriv_seeleyCut_le i t)
      nlinarith [hnum, hrpow, hden, hA, hB]

/-! ## The Hölder-seminorm bound -/

/-- Hölder-seminorm bound for the normal cutoff `p ↦ seeleyCut (c * p.2)`. -/
theorem gSN_cutoff_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c : ℝ} (hc : 1 ≤ |c|) {i : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {Ω : Set (X × ℝ)} :
    Work.NN.Final.gSN i α (fun p : X × ℝ => Work.NN.Final.seeleyCut (c * p.2)) Ω
      ≤ ENNReal.ofReal (|c| ^ ((i : ℝ) + 1 + α) *
          (2 * Work.NN.Final.seeleyCutB i + Work.NN.Final.seeleyCutB (i + 1))) := by
  have hc0 : 0 < |c| := lt_of_lt_of_le one_pos hc
  have hK0 : 0 ≤ 2 * seeleyCutB i + seeleyCutB (i + 1) := by
    have h1 := seeleyCutB_nonneg i
    have h2 := seeleyCutB_nonneg (i + 1)
    linarith
  -- the numerical factor: `|c| ^ α * |c| ^ i ≤ |c| ^ (i + 1 + α)` since `1 ≤ |c|`
  have h7 : (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ α * |c| ^ (i : ℝ)
      ≤ |c| ^ ((i : ℝ) + 1 + α) * (2 * seeleyCutB i + seeleyCutB (i + 1)) := by
    have hrw : |c| ^ α * |c| ^ (i : ℝ) = |c| ^ (α + (i : ℝ)) :=
      (Real.rpow_add hc0 α (i : ℝ)).symm
    have hmono : |c| ^ (α + (i : ℝ)) ≤ |c| ^ ((i : ℝ) + 1 + α) :=
      Real.rpow_le_rpow_of_exponent_le hc (by linarith)
    calc (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ α * |c| ^ (i : ℝ)
        = (2 * seeleyCutB i + seeleyCutB (i + 1)) * (|c| ^ α * |c| ^ (i : ℝ)) := by ring
      _ = (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ (α + (i : ℝ)) := by rw [hrw]
      _ ≤ (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ ((i : ℝ) + 1 + α) :=
          mul_le_mul_of_nonneg_left hmono hK0
      _ = |c| ^ ((i : ℝ) + 1 + α) * (2 * seeleyCutB i + seeleyCutB (i + 1)) := by ring
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [iteratedFDeriv_cutoff c i x, iteratedFDeriv_cutoff c i y,
    compContinuousLinearMap_sub_const' (X := X)]
  have hsnd : ‖c • ContinuousLinearMap.snd ℝ X ℝ‖ ≤ |c| := by
    simpa using norm_smul_le c (ContinuousLinearMap.snd ℝ X ℝ)
  have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hdpos α
  -- the composition with the shear brings in the factor `|c| ^ i`
  have hcomp : ‖(iteratedFDeriv ℝ i seeleyCut (c * x.2)
        - iteratedFDeriv ℝ i seeleyCut (c * y.2)).compContinuousLinearMap
        (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)‖
      ≤ ‖iteratedFDeriv ℝ i seeleyCut (c * x.2) - iteratedFDeriv ℝ i seeleyCut (c * y.2)‖
        * |c| ^ (i : ℝ) := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow (norm_nonneg _) hsnd (Nat.cast_nonneg i)
  -- the two-point bound for the derivatives of the cutoff
  have hdiff : ‖iteratedFDeriv ℝ i seeleyCut (c * x.2) - iteratedFDeriv ℝ i seeleyCut (c * y.2)‖
      ≤ (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c * x.2 - c * y.2| ^ α :=
    cutoff_holder_all i hα hα1 (c * x.2) (c * y.2)
  -- the normal coordinate difference is controlled by `‖x - y‖`
  have hcx : |c * x.2 - c * y.2| ≤ |c| * ‖x - y‖ := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    calc |x.2 - y.2| = ‖(x - y).2‖ := by rw [Prod.snd_sub, Real.norm_eq_abs]
      _ ≤ ‖x - y‖ := by rw [Prod.norm_mk]; exact le_max_right _ _
  have hpow : |c * x.2 - c * y.2| ^ α ≤ |c| ^ α * ‖x - y‖ ^ α := by
    calc |c * x.2 - c * y.2| ^ α ≤ (|c| * ‖x - y‖) ^ α :=
          Real.rpow_le_rpow (abs_nonneg _) hcx hα
      _ = |c| ^ α * ‖x - y‖ ^ α := Real.mul_rpow (abs_nonneg c) hdpos.le
  have h5 : ‖(iteratedFDeriv ℝ i seeleyCut (c * x.2)
        - iteratedFDeriv ℝ i seeleyCut (c * y.2)).compContinuousLinearMap
        (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)‖
      ≤ (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ α * |c| ^ (i : ℝ) * ‖x - y‖ ^ α := by
    calc ‖(iteratedFDeriv ℝ i seeleyCut (c * x.2)
          - iteratedFDeriv ℝ i seeleyCut (c * y.2)).compContinuousLinearMap
          (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)‖
        ≤ ‖iteratedFDeriv ℝ i seeleyCut (c * x.2) - iteratedFDeriv ℝ i seeleyCut (c * y.2)‖
            * |c| ^ (i : ℝ) := hcomp
      _ ≤ ((2 * seeleyCutB i + seeleyCutB (i + 1)) * |c * x.2 - c * y.2| ^ α)
            * |c| ^ (i : ℝ) := mul_le_mul_of_nonneg_right hdiff (Real.rpow_nonneg (abs_nonneg c) _)
      _ ≤ ((2 * seeleyCutB i + seeleyCutB (i + 1)) * (|c| ^ α * ‖x - y‖ ^ α))
            * |c| ^ (i : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK0)
            (Real.rpow_nonneg (abs_nonneg c) _)
      _ = (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ α * |c| ^ (i : ℝ) * ‖x - y‖ ^ α := by
          ring
  rw [div_le_iff₀ hdα]
  calc ‖(iteratedFDeriv ℝ i seeleyCut (c * x.2)
        - iteratedFDeriv ℝ i seeleyCut (c * y.2)).compContinuousLinearMap
        (fun _ : Fin i => c • ContinuousLinearMap.snd ℝ X ℝ)‖
      ≤ (2 * seeleyCutB i + seeleyCutB (i + 1)) * |c| ^ α * |c| ^ (i : ℝ) * ‖x - y‖ ^ α := h5
    _ ≤ |c| ^ ((i : ℝ) + 1 + α) * (2 * seeleyCutB i + seeleyCutB (i + 1)) * ‖x - y‖ ^ α :=
        mul_le_mul_of_nonneg_right h7 hdα.le

end Work.NN.Seeley
