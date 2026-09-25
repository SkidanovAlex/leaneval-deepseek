/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Smoothness and derivative bounds for the unfolding map

The unfolding `discUnfold g = g ∘ unfoldMap` of `Unfold.lean` uses the map

`unfoldMap y = (y.1.1, (1 - y.2) • (y.1.2 / ‖y.1.2‖)) = (y.1.1, unP (y.1.2, y.2))`.

This file proves that `discUnfold g` is `C^k` on a region on which `y.1.2` stays in a bounded
region of `ℂ` away from `0`, that its iterated derivatives are bounded there (whenever `g` has
finite `C^{k,α}` norm on `U × ball(0,1)` and `α ≤ 1`), and that it has finite `C^{k,α}` norm
there.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
import Submission.Work.CR.Flat.Holder.comp_bound_aux
import Submission.Work.NN.DiscRadial.Unfold
import Submission.Work.NN.DiscRadial.holderNorm_comp_univ_contDiffOn
import Submission.Work.NN.DiscRadial.holderNorm_one_ne_top_of_one_lt

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.DiscRadial

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Norm of a product of multilinear maps -/

/-- The operator norm of the product of two continuous multilinear maps is at most the sum of
their operator norms. -/
lemma norm_prod_le_of_multilinear {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*}
    [Fintype ι] {M₁ : ι → Type*} [∀ i, NormedAddCommGroup (M₁ i)] [∀ i, NormedSpace 𝕜 (M₁ i)]
    {M₂ M₃ : Type*} [NormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] [NormedAddCommGroup M₃]
    [NormedSpace 𝕜 M₃]
    (f : ContinuousMultilinearMap 𝕜 M₁ M₂) (g : ContinuousMultilinearMap 𝕜 M₁ M₃) :
    ‖f.prod g‖ ≤ ‖f‖ + ‖g‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_mk]
  refine max_le_iff.mpr ⟨?_, ?_⟩
  · calc ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := ContinuousMultilinearMap.le_opNorm f m
      _ ≤ (‖f‖ + ‖g‖) * ∏ i, ‖m i‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg g)) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  · calc ‖g m‖ ≤ ‖g‖ * ∏ i, ‖m i‖ := ContinuousMultilinearMap.le_opNorm g m
      _ ≤ (‖f‖ + ‖g‖) * ∏ i, ‖m i‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg f)) (Finset.prod_nonneg (fun i _ => norm_nonneg _))

/-! ## Bounds for the iterated derivatives of a continuous linear map -/

/-- The iterated derivatives of a continuous linear map are bounded by its operator norm. -/
lemma norm_iteratedFDeriv_coe_clm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (⇑L) x‖ ≤ ‖L‖ := by
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    rw [← iteratedFDerivWithin_univ, norm_iteratedFDerivWithin_one _ uniqueDiffWithinAt_univ,
      fderivWithin_univ, ContinuousLinearMap.fderiv]
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have hn : n ≠ 0 := by omega
    rw [← iteratedFDerivWithin_univ,
      ← norm_iteratedFDerivWithin_fderivWithin (𝕜 := ℝ) (s := Set.univ) (f := ⇑L)
        (n := n) (x := x) uniqueDiffOn_univ (Set.mem_univ x)]
    rw [show fderivWithin ℝ (⇑L) Set.univ = (fun _ : E => L) from by
      rw [fderivWithin_univ]; exact funext fun y => ContinuousLinearMap.fderiv L]
    rw [iteratedFDerivWithin_const_of_ne hn L]
    simp

/-! ## The normalisation map `u ↦ u / ‖u‖` -/

/-- The "analytic core" of the unfolding: `(u, σ) ↦ (1 - σ) • (u / ‖u‖)`. -/
def unP : ℂ × ℝ → ℂ := fun z => (1 - z.2) • (z.1 / (‖z.1‖ : ℂ))

@[simp] lemma unP_apply (z : ℂ × ℝ) : unP z = (1 - z.2) • (z.1 / (‖z.1‖ : ℂ)) := rfl

/-- `u ↦ u / ‖u‖` is `C^∞` on `{u ≠ 0}`. -/
lemma contDiffOn_div_norm : ContDiffOn ℝ ⊤ (fun u : ℂ => u / (‖u‖ : ℂ)) {u : ℂ | u ≠ 0} := by
  have heq : (fun u : ℂ => u / (‖u‖ : ℂ)) = (fun u : ℂ => (‖u‖)⁻¹ • u) := by
    funext u
    rw [div_eq_inv_mul, Complex.real_smul, ← Complex.ofReal_inv]
  rw [heq]
  intro u hu
  have hnorm : ContDiffWithinAt ℝ ⊤ (fun w : ℂ => ‖w‖) {u : ℂ | u ≠ 0} u :=
    ContDiffWithinAt.norm ℝ contDiffWithinAt_id hu
  exact (hnorm.inv (by simpa using hu)).smul contDiffWithinAt_id

/-- `unP` is `C^∞` wherever `u ≠ 0`. -/
lemma contDiffOn_unP : ContDiffOn ℝ ⊤ unP {z : ℂ × ℝ | z.1 ≠ 0} := by
  have hinner : ∀ w : ℂ, w / (‖w‖ : ℂ) = (‖w‖)⁻¹ • w := by
    intro w
    rw [div_eq_inv_mul, Complex.real_smul, ← Complex.ofReal_inv]
  have hfun : unP = (fun w : ℂ × ℝ => (1 - w.2) • ((‖w.1‖)⁻¹ • w.1)) := by
    funext w
    simp only [unP, hinner]
  rw [hfun]
  intro z hz
  have hnorm : ContDiffWithinAt ℝ ⊤ (fun w : ℂ × ℝ => ‖w.1‖) {z : ℂ × ℝ | z.1 ≠ 0} z :=
    ContDiffWithinAt.norm ℝ contDiffWithinAt_id.fst hz
  have hsmul : ContDiffWithinAt ℝ ⊤ (fun w : ℂ × ℝ => (‖w.1‖)⁻¹ • w.1)
      {z : ℂ × ℝ | z.1 ≠ 0} z :=
    (hnorm.inv (by simpa using hz)).smul contDiffWithinAt_id.fst
  have h2 : ContDiffWithinAt ℝ ⊤ (fun w : ℂ × ℝ => 1 - w.2) {z : ℂ × ℝ | z.1 ≠ 0} z :=
    contDiffWithinAt_const.sub contDiffWithinAt_id.snd
  exact h2.smul hsmul

/-! ## The unfolding map -/

/-- The first projection `((x,u),σ) ↦ x`, as a continuous linear map. -/
def prX : (X × ℂ) × ℝ →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X ℂ).comp (ContinuousLinearMap.fst ℝ (X × ℂ) ℝ)

/-- The projection `((x,u),σ) ↦ (u,σ)`, as a continuous linear map. -/
def pr2 : (X × ℂ) × ℝ →L[ℝ] ℂ × ℝ :=
  ((ContinuousLinearMap.snd ℝ X ℂ).comp (ContinuousLinearMap.fst ℝ (X × ℂ) ℝ)).prod
    (ContinuousLinearMap.snd ℝ (X × ℂ) ℝ)

/-- The map `y ↦ (prX y, unP (pr2 y))`, which is `unfoldMap` rewritten. -/
def unfoldMap' : (X × ℂ) × ℝ → X × ℂ := fun y => (prX y, unP (pr2 y))

@[simp] lemma prX_apply (y : (X × ℂ) × ℝ) : prX (X := X) y = y.1.1 := rfl

@[simp] lemma pr2_apply (y : (X × ℂ) × ℝ) : pr2 (X := X) y = (y.1.2, y.2) := by
  simp [pr2]

@[simp] lemma unfoldMap'_apply (y : (X × ℂ) × ℝ) :
    unfoldMap' (X := X) y = (y.1.1, unP (y.1.2, y.2)) := by simp [unfoldMap']

lemma unfoldMap_eq' : unfoldMap (X := X) = unfoldMap' (X := X) := by
  funext y
  simp [unfoldMap, unfoldMap', unP]

/-- `unfoldMap` is `C^∞` wherever `y.1.2 ≠ 0`. -/
lemma contDiffOn_unfoldMap : ContDiffOn ℝ ⊤ (unfoldMap (X := X)) {y : (X × ℂ) × ℝ | y.1.2 ≠ 0} := by
  rw [unfoldMap_eq']
  intro y hy
  have hx : ContDiffWithinAt ℝ ⊤ (fun y : (X × ℂ) × ℝ => prX (X := X) y)
      {y : (X × ℂ) × ℝ | y.1.2 ≠ 0} y := (prX (X := X)).contDiff.contDiffWithinAt
  have hpr2cd : ContDiffWithinAt ℝ ⊤ (fun y : (X × ℂ) × ℝ => pr2 (X := X) y)
      {y : (X × ℂ) × ℝ | y.1.2 ≠ 0} y := (pr2 (X := X)).contDiff.contDiffWithinAt
  have hmem : pr2 (X := X) y ∈ {z : ℂ × ℝ | z.1 ≠ 0} := by simpa [pr2] using hy
  have hp2 : ContDiffWithinAt ℝ ⊤ (fun y => unP (pr2 (X := X) y))
      {y : (X × ℂ) × ℝ | y.1.2 ≠ 0} y :=
    (contDiffOn_unP.contDiffWithinAt hmem).comp y hpr2cd (fun w hw => by simpa [pr2] using hw)
  exact hx.prodMk hp2

/-! ## Bounds for the iterated derivatives of `unP` and of `unfoldMap` -/

/-- Bound of the iterated derivatives of `unP` on a compact subset of `{u ≠ 0}`. -/
lemma exists_unP_deriv_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hKV : K ⊆ {z : ℂ × ℝ | z.1 ≠ 0}) :
    ∃ B : ℕ → ℝ, ∀ i, ∀ z ∈ K, ‖iteratedFDeriv ℝ i unP z‖ ≤ B i := by
  have hV : IsOpen {z : ℂ × ℝ | z.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hcont : ∀ i, ContinuousOn (fun z : ℂ × ℝ => ‖iteratedFDeriv ℝ i unP z‖) K := fun i =>
    (ContinuousOn.continuousOn_iteratedFDeriv contDiffOn_unP hV (by simp)).norm.mono hKV
  choose B hB using fun i => hK.exists_bound_of_continuousOn (hcont i)
  exact ⟨B, fun i z hz => by simpa using hB i z hz⟩

/-- The iterated derivatives of `unfoldMap` are bounded on a region where `y.1.2` stays in a set
`W2` of vectors of norm `> 1/2` whose relevant points lie in the compact `K`. -/
lemma unfoldMap_deriv_bound {W2 : Set ℂ} {K : Set (ℂ × ℝ)}
    (hW2 : ∀ u ∈ W2, (1 : ℝ) / 2 < ‖u‖)
    (hmem : ∀ u ∈ W2, ∀ σ ∈ Set.Ioo 0 2, (u, σ) ∈ K) {B : ℕ → ℝ}
    (hB : ∀ i, ∀ z ∈ K, ‖iteratedFDeriv ℝ i unP z‖ ≤ B i) :
    ∀ i, 1 ≤ i → ∀ x : (X × ℂ) × ℝ, x.1.2 ∈ W2 → x.2 ∈ Set.Ioo 0 2 →
      ‖iteratedFDeriv ℝ i (unfoldMap (X := X)) x‖ ≤ 1 + B i := by
  intro i hi x hx2 hxσ
  rw [unfoldMap_eq']
  have hx2ne : x.1.2 ≠ 0 := by
    intro h
    have hlt := hW2 x.1.2 hx2
    rw [h, norm_zero] at hlt
    norm_num at hlt
  have hprXcd : ContDiffAt ℝ (i : WithTop ENat) (fun y : (X × ℂ) × ℝ => prX (X := X) y) x :=
    (prX (X := X)).contDiff.contDiffAt
  have hV : IsOpen {z : ℂ × ℝ | z.1 ≠ 0} := isOpen_ne.preimage continuous_fst
  have hmemx : pr2 (X := X) x ∈ {z : ℂ × ℝ | z.1 ≠ 0} := by simpa [pr2] using hx2ne
  have hunPcd : ContDiffAt ℝ (i : WithTop ENat)
      (fun y : (X × ℂ) × ℝ => unP (pr2 (X := X) y)) x :=
    ((contDiffOn_unP.contDiffAt (hV.mem_nhds hmemx)).of_le le_top).comp x
      (pr2 (X := X)).contDiff.contDiffAt
  have hprod := iteratedFDeriv_prodMk hprXcd hunPcd (le_refl (i : WithTop ENat))
  have heq : iteratedFDeriv ℝ i (unfoldMap' (X := X)) x
      = (iteratedFDeriv ℝ i (fun y : (X × ℂ) × ℝ => prX (X := X) y) x).prod
          (iteratedFDeriv ℝ i (fun y : (X × ℂ) × ℝ => unP (pr2 (X := X) y)) x) := by
    have hfun : unfoldMap' (X := X)
        = (fun y : (X × ℂ) × ℝ => (prX (X := X) y, unP (pr2 (X := X) y))) := rfl
    rw [hfun]
    exact hprod
  have h1 : ‖iteratedFDeriv ℝ i (fun y : (X × ℂ) × ℝ => prX (X := X) y) x‖ ≤ 1 := by
    refine (norm_iteratedFDeriv_coe_clm_le (prX (X := X)) hi x).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => ?_
    rw [prX_apply, Prod.norm_mk, Prod.norm_mk]
    calc ‖y.1.1‖ ≤ max ‖y.1.1‖ ‖y.1.2‖ := le_max_left _ _
      _ ≤ max (max ‖y.1.1‖ ‖y.1.2‖) |y.2| := le_max_left _ _
      _ = 1 * max (max ‖y.1.1‖ ‖y.1.2‖) |y.2| := (one_mul _).symm
  have h2 : ‖iteratedFDeriv ℝ i (fun y : (X × ℂ) × ℝ => unP (pr2 (X := X) y)) x‖ ≤ B i := by
    have hpre : IsOpen ((pr2 (X := X)) ⁻¹' {z : ℂ × ℝ | z.1 ≠ 0}) :=
      hV.preimage (pr2 (X := X)).continuous
    have hkey : iteratedFDeriv ℝ i (fun y : (X × ℂ) × ℝ => unP (pr2 (X := X) y)) x
        = (iteratedFDeriv ℝ i unP (pr2 (X := X) x)).compContinuousLinearMap
            (fun _ => pr2 (X := X)) := by
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hpre
        (f := fun y : (X × ℂ) × ℝ => unP (pr2 (X := X) y)) hx2ne,
        ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hV (f := unP)
          (by simpa [pr2] using hx2ne)]
      exact ContinuousLinearMap.iteratedFDerivWithin_comp_right (pr2 (X := X)) contDiffOn_unP
        hV.uniqueDiffOn hpre.uniqueDiffOn (x := x) hmemx (le_top)
    rw [hkey]
    refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
    have hle : ‖pr2 (X := X)‖ ≤ 1 := by
      rw [ContinuousLinearMap.opNorm_le_iff (by norm_num)]
      intro y
      rw [pr2_apply, Prod.norm_mk, Prod.norm_mk, one_mul]
      exact max_le (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    have hprod1 : (∏ _ : Fin i, ‖pr2 (X := X)‖) ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_one₀ (norm_nonneg _) hle
    calc ‖iteratedFDeriv ℝ i unP (pr2 (X := X) x)‖ * ∏ _ : Fin i, ‖pr2 (X := X)‖
        ≤ ‖iteratedFDeriv ℝ i unP (pr2 (X := X) x)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod1 (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ i unP (pr2 (X := X) x)‖ := mul_one _
      _ ≤ B i := hB i (pr2 (X := X) x) (hmem x.1.2 hx2 x.2 hxσ)
  rw [heq]
  exact (norm_prod_le_of_multilinear _ _).trans (add_le_add h1 h2)


/-! ## Smoothness and finite norm of `discUnfold` -/

lemma norm_div_norm_eq_one {u : ℂ} (hu : u ≠ 0) : ‖u / (‖u‖ : ℂ)‖ = 1 := by
  rw [norm_div]
  rw [show ‖((‖u‖ : ℝ) : ℂ)‖ = ‖u‖ from
    (Complex.norm_real _).trans (Real.norm_of_nonneg (norm_nonneg u))]
  exact div_self (norm_ne_zero_iff.mpr hu)

lemma mapsTo_unfoldMap {U : Set X} {x₀ : X} {r : ℝ} {u₀ : ℂ} (hu₀ : ‖u₀‖ = 1)
    (hsub : Metric.ball x₀ r ⊆ U) :
    Set.MapsTo (unfoldMap (X := X))
      ((Metric.ball x₀ r ×ˢ Metric.ball u₀ (1 / 2)) ×ˢ Set.Ioo 0 2)
      (U ×ˢ Metric.ball (0 : ℂ) 1) := by
  intro y hy
  obtain ⟨⟨hyx, hyu⟩, hy1, hy2⟩ := hy
  have hu0 : y.1.2 ≠ 0 := by
    intro h
    rw [h] at hyu
    simp only [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, hu₀] at hyu
    norm_num at hyu
  refine ⟨hsub hyx, ?_⟩
  show (1 - y.2) • (y.1.2 / (‖y.1.2‖ : ℂ)) ∈ Metric.ball (0 : ℂ) 1
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    norm_div_norm_eq_one hu0, mul_one, abs_lt]
  constructor <;> linarith [hy1, hy2]

theorem discUnfold_contDiffOn {k : ℕ} {U : Set X} (hU : IsOpen U) {g : X × ℂ → ℂ}
    (hg : ContDiffOn ℝ (k : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1)) :
    ContDiffOn ℝ (k : WithTop ENat) (discUnfold g)
      ((U ×ˢ {u : ℂ | 1/2 < ‖u‖}) ×ˢ Set.Ioo 0 2) := by
  have hsm : ContDiffOn ℝ ⊤ (unfoldMap (X := X)) ((U ×ˢ {u : ℂ | 1/2 < ‖u‖}) ×ˢ Set.Ioo 0 2) := by
    refine contDiffOn_unfoldMap.mono ?_
    rintro y ⟨⟨-, hmem⟩, -⟩
    exact norm_pos_iff.mp (by linarith [show (1 : ℝ)/2 < ‖y.1.2‖ from hmem])
  have hmap : Set.MapsTo (unfoldMap (X := X)) ((U ×ˢ {u : ℂ | 1/2 < ‖u‖}) ×ˢ Set.Ioo 0 2)
      (U ×ˢ Metric.ball (0 : ℂ) 1) := by
    intro y hy
    obtain ⟨⟨hyU, hyu⟩, hy1, hy2⟩ := hy
    have hu0 : y.1.2 ≠ 0 :=
      norm_pos_iff.mp (lt_trans (by norm_num) (show (1 : ℝ)/2 < ‖y.1.2‖ from hyu))
    refine ⟨hyU, ?_⟩
    show (1 - y.2) • (y.1.2 / (‖y.1.2‖ : ℂ)) ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      norm_div_norm_eq_one hu0, mul_one, abs_lt]
    constructor <;> linarith [hy1, hy2]
  rw [discUnfold_eq_comp g]
  exact hg.comp (hsm.of_le le_top) hmap


/-- The set of `(u,σ)` with `u ∈ closedBall u₀ (1/2)` (so `‖u‖ ≥ 1/2`) and `σ ∈ [0,2]`. -/
def Kset (u₀ : ℂ) : Set (ℂ × ℝ) := Metric.closedBall u₀ (1/2) ×ˢ Set.Icc (0:ℝ) 2

lemma isCompact_Kset (u₀ : ℂ) : IsCompact (Kset u₀) := by
  rw [Kset]
  exact (isCompact_closedBall u₀ (1/2)).prod isCompact_Icc

/-- A point of `ball u₀ (1/2)` with `‖u₀‖ = 1` has norm `> 1/2`. -/
lemma half_lt_norm_of_mem_ball {u₀ u : ℂ} (hu₀ : ‖u₀‖ = 1) (hu : u ∈ Metric.ball u₀ (1/2)) :
    (1:ℝ)/2 < ‖u‖ := by
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hu
  have h2 := norm_le_norm_sub_add u₀ u
  rw [hu₀] at h2
  linarith

lemma Kset_subset_ne_zero {u₀ : ℂ} (hu₀ : ‖u₀‖ = 1) : Kset u₀ ⊆ {z : ℂ × ℝ | z.1 ≠ 0} := by
  rintro z ⟨hz1, -⟩
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hz1
  have h2 := norm_le_norm_sub_add u₀ z.1
  rw [hu₀] at h2
  exact norm_pos_iff.mp (by linarith)

/-- **The unfolded function has finite `C^{k,β}` norm on a small product region.** -/
theorem discUnfold_holderNorm_ne_top {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {k : ℕ}
    {U : Set X} (hU : IsOpen U) {g : X × ℂ → ℂ}
    (hg : ContDiffOn ℝ (k : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1))
    (hfin : Work.CR.Flat.holderNorm k β g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤)
    {x₀ : X} {r : ℝ} (hr : 0 < r) (hsub : Metric.ball x₀ r ⊆ U)
    {u₀ : ℂ} (hu₀ : ‖u₀‖ = 1) :
    Work.CR.Flat.holderNorm k β (discUnfold g)
      ((Metric.ball x₀ r ×ˢ Metric.ball u₀ (1/2)) ×ˢ Set.Ioo 0 2) ≠ ⊤ := by
  classical
  obtain ⟨B, hB⟩ := exists_unP_deriv_bound (isCompact_Kset u₀) (Kset_subset_ne_zero hu₀)
  set D : ℕ → ℝ := fun m => 1 + |B m| with hDdef
  set E : ℕ → ℝ := fun m => D (m+1) + 2 * D m with hEdef
  set L : ℝ := D 1 with hLdef
  obtain ⟨C, _hCpos, hCmain⟩ :=
    holderNorm_comp_univ_contDiffOn (X := (X × ℂ) × ℝ) (Y := X × ℂ) β hβ0 L D E
  set s : Set ((X × ℂ) × ℝ) := (Metric.ball x₀ r ×ˢ Metric.ball u₀ (1/2)) ×ˢ Set.Ioo 0 2 with hsdef
  have hsopen : IsOpen s := (isOpen_ball.prod isOpen_ball).prod isOpen_Ioo
  have hssub : s ⊆ {y : (X × ℂ) × ℝ | y.1.2 ≠ 0} := by
    rintro y ⟨⟨-, hyu⟩, -⟩
    exact norm_pos_iff.mp (by linarith [half_lt_norm_of_mem_ball hu₀ hyu])
  have hne : ∀ z : (X × ℂ) × ℝ, z.1.2 ≠ 0 → {y : (X × ℂ) × ℝ | y.1.2 ≠ 0} ∈ 𝓝 z :=
    fun z hz => (isOpen_ne.preimage continuous_fst.snd).mem_nhds hz
  have hconv : Convex ℝ s := ((convex_ball x₀ r).prod (convex_ball u₀ (1/2))).prod (convex_Ioo 0 2)
  have hmemK : ∀ u ∈ Metric.ball u₀ (1/2), ∀ σ ∈ Set.Ioo 0 2, (u, σ) ∈ Kset u₀ := by
    intro u hu σ hσ
    exact ⟨Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hu)), ⟨hσ.1.le, hσ.2.le⟩⟩
  have hΦcd : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (unfoldMap (X := X)) s := fun m =>
    (contDiffOn_unfoldMap.of_le le_top).mono hssub
  have hmaps : Set.MapsTo (unfoldMap (X := X)) s (U ×ˢ Metric.ball (0 : ℂ) 1) :=
    mapsTo_unfoldMap hu₀ hsub
  have hDbound : ∀ i z, z ∈ Kset u₀ → ‖iteratedFDeriv ℝ i unP z‖ ≤ B i := hB
  have hDb : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ s,
      ‖iteratedFDerivWithin ℝ m (unfoldMap (X := X)) s x‖ ≤ D m := by
    intro m hm x hx
    rw [iteratedFDerivWithin_of_isOpen m hsopen hx]
    refine (unfoldMap_deriv_bound (B := B) (fun u hu => by
      linarith [half_lt_norm_of_mem_ball hu₀ hu]) hmemK hDbound m hm x hx.1.2 hx.2).trans ?_
    show 1 + B m ≤ D m
    rw [hDdef]
    simp only
    linarith [le_abs_self (B m)]
  have hLb : ∀ x ∈ s, ∀ y ∈ s, ‖unfoldMap (X := X) x - unfoldMap (X := X) y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := unfoldMap (X := X)) (C := D 1) (s := s) ?_ ?_ hconv hy hx
    · simpa only [hLdef] using this
    · intro z hz
      exact (contDiffOn_unfoldMap.contDiffAt (hne z (hssub hz))).differentiableAt (by simp)
    · intro z hz
      have h1 := hDb 1 le_rfl z hz
      rw [iteratedFDerivWithin_of_isOpen 1 hsopen hz] at h1
      rw [← fderivWithin_univ, ← norm_iteratedFDerivWithin_one (𝕜 := ℝ)
        (f := unfoldMap (X := X)) (x := z) (s := Set.univ) uniqueDiffWithinAt_univ,
        iteratedFDerivWithin_univ]
      exact h1
  have hEb : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ s, ∀ y ∈ s,
      ‖iteratedFDerivWithin ℝ m (unfoldMap (X := X)) s x
        - iteratedFDerivWithin ℝ m (unfoldMap (X := X)) s y‖ ≤ E m * ‖x - y‖ ^ β := by
    intro m hm x hx y hy
    rw [iteratedFDerivWithin_of_isOpen m hsopen hx, iteratedFDerivWithin_of_isOpen m hsopen hy]
    have hlip : ‖iteratedFDeriv ℝ m (unfoldMap (X := X)) x
        - iteratedFDeriv ℝ m (unfoldMap (X := X)) y‖ ≤ D (m+1) * ‖x - y‖ := by
      exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
        (f := fun z => iteratedFDeriv ℝ m (unfoldMap (X := X)) z) (C := D (m+1)) (s := s)
        (fun z hz => (contDiffOn_unfoldMap.contDiffAt (hne z (hssub hz))
          ).differentiableAt_iteratedFDeriv (by simp))
        (fun z hz => by
          rw [fderiv_iteratedFDeriv]
          change ‖(continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (m+1) => ((X × ℂ) × ℝ)) (X × ℂ))
                (iteratedFDeriv ℝ (m+1) (unfoldMap (X := X)) z)‖ ≤ D (m+1)
          rw [LinearIsometryEquiv.norm_map]
          have h := hDb (m+1) (by omega) z hz
          rwa [iteratedFDerivWithin_of_isOpen (m+1) hsopen hz] at h)
        hconv hy hx
    have hDm : (0:ℝ) ≤ D m := by show (0:ℝ) ≤ 1 + |B m|; positivity
    have hDm1 : (0:ℝ) ≤ D (m+1) := by show (0:ℝ) ≤ 1 + |B (m+1)|; positivity
    have hEm : (0:ℝ) ≤ E m := by show (0:ℝ) ≤ D (m+1) + 2 * D m; linarith
    have hDEm : D (m+1) ≤ E m := by show D (m+1) ≤ D (m+1) + 2 * D m; linarith
    have htwo : 2 * D m ≤ E m := by show 2 * D m ≤ D (m+1) + 2 * D m; linarith
    rcases le_total ‖x - y‖ 1 with h1 | h1
    · have hc : (0:ℝ) ≤ D (m+1) := by show (0:ℝ) ≤ 1 + |B (m+1)|; positivity
      have hle' : ‖x - y‖ ≤ ‖x - y‖ ^ β := by
        rcases eq_or_lt_of_le (norm_nonneg (x - y)) with h0 | h0
        · rw [← h0, Real.zero_rpow hβ0.ne']
        · calc ‖x - y‖ = ‖x - y‖ ^ (1:ℝ) := (Real.rpow_one _).symm
            _ ≤ ‖x - y‖ ^ β := Real.rpow_le_rpow_of_exponent_ge h0 h1 hβ1
      calc ‖iteratedFDeriv ℝ m (unfoldMap (X := X)) x
              - iteratedFDeriv ℝ m (unfoldMap (X := X)) y‖
          ≤ D (m+1) * ‖x - y‖ := hlip
        _ ≤ D (m+1) * ‖x - y‖ ^ β := mul_le_mul_of_nonneg_left hle' hc
        _ ≤ E m * ‖x - y‖ ^ β :=
            mul_le_mul_of_nonneg_right hDEm (Real.rpow_nonneg (norm_nonneg _) β)
    · have h2 : (1:ℝ) ≤ ‖x - y‖ ^ β := Real.one_le_rpow h1 hβ0.le
      have hupper : ‖iteratedFDeriv ℝ m (unfoldMap (X := X)) x
          - iteratedFDeriv ℝ m (unfoldMap (X := X)) y‖ ≤ 2 * D m := by
        refine (norm_sub_le _ _).trans ?_
        rw [← iteratedFDerivWithin_of_isOpen m hsopen hx, ← iteratedFDerivWithin_of_isOpen m hsopen hy]
        linarith [hDb m hm x hx, hDb m hm y hy]
      calc ‖iteratedFDeriv ℝ m (unfoldMap (X := X)) x
              - iteratedFDeriv ℝ m (unfoldMap (X := X)) y‖
          ≤ 2 * D m := hupper
        _ ≤ E m := htwo
        _ ≤ E m * ‖x - y‖ ^ β := le_mul_of_one_le_right hEm h2
  have hlt := (hCmain k (unfoldMap (X := X)) s (U ×ˢ Metric.ball (0 : ℂ) 1) g hΦcd hsopen
    (hU.prod isOpen_ball) hmaps hLb hDb hEb hg).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hfin))
  rw [← discUnfold_eq_comp g] at hlt
  exact ne_of_lt hlt

end Work.NN.DiscRadial
