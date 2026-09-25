/-
Localized ("region-restricted") infrastructure for the Seeley extension estimate
`Work.NN.Final.seeleyExt_region_holderNorm_le`.

This module contains the regions (`seHp`, `seUp`, `seSl`, `seLw`), and the chain rule for the
shear `p ↦ (p.1, c * p.2)` for functions that are only `C^i` on the (one-sided) closed half
space, in the `C^i` and `C^{i,α}` forms.
-/
import Mathlib
import Submission.Work.NN.Final.PolarDefs
import Submission.Work.NN.Seeley.seeleyEV_holderNorm_le
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.NN.Final

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The regions -/

/-- The `W`-restricted closed upper half space `W × [0,∞)`. -/
def seHp (W : Set E) : Set (E × ℝ) := W ×ˢ {t : ℝ | 0 ≤ t}

/-- The `W`-restricted open upper half space `W × (0,∞)`. -/
def seUp (W : Set E) : Set (E × ℝ) := W ×ˢ {t : ℝ | 0 < t}

/-- The `W`-restricted slab `W × (-δ,∞)`. -/
def seSl (W : Set E) (δ : ℝ) : Set (E × ℝ) := W ×ˢ {t : ℝ | -δ < t}

/-- The `W`-restricted open lower slab `W × (-δ,0)`. -/
def seLw (W : Set E) (δ : ℝ) : Set (E × ℝ) := W ×ˢ {t : ℝ | -δ < t ∧ t < 0}

@[simp] lemma mem_seHp {W : Set E} {p : E × ℝ} : p ∈ seHp W ↔ p.1 ∈ W ∧ 0 ≤ p.2 :=
  and_congr_right_iff.mpr fun _ => Iff.rfl

@[simp] lemma mem_seUp {W : Set E} {p : E × ℝ} : p ∈ seUp W ↔ p.1 ∈ W ∧ 0 < p.2 :=
  and_congr_right_iff.mpr fun _ => Iff.rfl

@[simp] lemma mem_seSl {W : Set E} {p : E × ℝ} {δ : ℝ} :
    p ∈ seSl W δ ↔ p.1 ∈ W ∧ -δ < p.2 := and_congr_right_iff.mpr fun _ => Iff.rfl

@[simp] lemma mem_seLw {W : Set E} {p : E × ℝ} {δ : ℝ} :
    p ∈ seLw W δ ↔ p.1 ∈ W ∧ -δ < p.2 ∧ p.2 < 0 :=
  and_congr_right_iff.mpr fun _ => and_congr_right_iff.mpr fun _ => Iff.rfl

lemma isOpen_seUp {W : Set E} (hW : IsOpen W) : IsOpen (seUp W) :=
  hW.prod isOpen_Ioi

lemma isOpen_seSl {W : Set E} (hW : IsOpen W) (δ : ℝ) : IsOpen (seSl W δ) :=
  hW.prod (isOpen_lt continuous_const continuous_id)

lemma isOpen_seLw {W : Set E} (hW : IsOpen W) (δ : ℝ) : IsOpen (seLw W δ) :=
  hW.prod ((isOpen_lt continuous_const continuous_id).inter
    (isOpen_lt continuous_id continuous_const))

lemma seUp_subset_seHp {W : Set E} : seUp W ⊆ seHp W := by
  intro p hp
  simp only [mem_seUp] at hp
  simp only [mem_seHp]
  exact ⟨hp.1, le_of_lt hp.2⟩

lemma seHp_subset_seSl {W : Set E} {δ : ℝ} (hδ : 0 < δ) : seHp W ⊆ seSl W δ := by
  intro p hp
  simp only [mem_seHp] at hp
  simp only [mem_seSl]
  exact ⟨hp.1, by linarith⟩

lemma seLw_subset_seSl {W : Set E} {δ : ℝ} : seLw W δ ⊆ seSl W δ := by
  intro p hp
  simp only [mem_seLw] at hp
  simp only [mem_seSl]
  exact ⟨hp.1, hp.2.1⟩

lemma seUp_subset {W W' : Set E} (h : W ⊆ W') : seUp W ⊆ seUp W' :=
  Set.prod_mono h Subset.rfl

lemma seHp_subset {W W' : Set E} (h : W ⊆ W') : seHp W ⊆ seHp W' :=
  Set.prod_mono h Subset.rfl

lemma seSl_subset {W W' : Set E} (h : W ⊆ W') (δ : ℝ) : seSl W δ ⊆ seSl W' δ :=
  Set.prod_mono h Subset.rfl

lemma seLw_subset {W W' : Set E} (h : W ⊆ W') (δ : ℝ) : seLw W δ ⊆ seLw W' δ :=
  Set.prod_mono h Subset.rfl

/-- The shear image of the lower slab with `0 < -c` lies in the open upper half space. -/
lemma shear_image_seLw_subset_seUp {W : Set E} {c δ : ℝ} (hc : 0 < -c) :
    (fun p : E × ℝ => (p.1, c * p.2)) '' seLw W δ ⊆ seUp W := by
  rintro q ⟨p, hp, rfl⟩
  simp only [mem_seLw] at hp
  simp only [mem_seUp]
  exact ⟨hp.1, by nlinarith [hp.2.2]⟩

/-- The shear map is injective for `c ≠ 0`. -/
lemma shear_inj {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (fun p : E × ℝ => (p.1, c * p.2)) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (mul_left_cancel₀ hc h.2)

/-- The image of an open set under the shear is open. -/
lemma isOpen_shear_image {c : ℝ} (hc : c ≠ 0) {Ω : Set (E × ℝ)} (hΩ : IsOpen Ω) :
    IsOpen ((fun p : E × ℝ => (p.1, c * p.2)) '' Ω) := by
  have h : (fun p : E × ℝ => (p.1, c * p.2)) '' Ω
      = (fun q : E × ℝ => (q.1, q.2 / c)) ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      show (p.1, c * p.2 / c) ∈ Ω
      have h2 : c * p.2 / c = p.2 := by field_simp
      rw [h2]
      exact hp
    · intro hy
      refine ⟨(y.1, y.2 / c), hy, ?_⟩
      show (y.1, c * (y.2 / c)) = y
      have h2 : c * (y.2 / c) = y.2 := by field_simp
      rw [h2]
  rw [h]
  exact hΩ.preimage (by fun_prop)

/-- The preimage of the shear image is the set itself. -/
lemma shear_preimage_image {c : ℝ} (hc : c ≠ 0) (Ω : Set (E × ℝ)) :
    (fun p : E × ℝ => (p.1, c * p.2)) ⁻¹' ((fun p : E × ℝ => (p.1, c * p.2)) '' Ω) = Ω := by
  refine Set.Subset.antisymm ?_ (fun x hx => ⟨x, hx, rfl⟩)
  rintro x ⟨y, hy, hxy⟩
  rw [← shear_inj hc hxy]
  exact hy

/-! ## The chain rule for the shear, for functions that are `C^i` on an open set -/

/-- Chain rule for the pullback under the shear `p ↦ (p.1, c * p.2)`, for functions that are
`C^i` on an open set `A` containing the image of `Ω`. -/
lemma iteratedFDeriv_comp_shear_of_contDiffOn {c : ℝ} (hc : c ≠ 0) {i : ℕ}
    {A Ω : Set (E × ℝ)} (hA : IsOpen A) (hΩ : IsOpen Ω)
    (hsub : (fun p : E × ℝ => (p.1, c * p.2)) '' Ω ⊆ A)
    {u : E × ℝ → ℂ} (hu : ContDiffOn ℝ (i : WithTop ENat) u A) {x : E × ℝ} (hx : x ∈ Ω) :
    iteratedFDeriv ℝ i (fun p : E × ℝ => u (p.1, c * p.2)) x
      = (iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)).compContinuousLinearMap
          (fun _ => seeleyLam (X := E) c) := by
  have hfun : ((seeleyLam (X := E) c) : E × ℝ → E × ℝ) = fun p : E × ℝ => (p.1, c * p.2) := by
    funext p; exact seeleyLam_apply c p
  have himg : IsOpen ((fun p : E × ℝ => (p.1, c * p.2)) '' Ω) := isOpen_shear_image hc hΩ
  have hpre : (fun p : E × ℝ => (p.1, c * p.2)) ⁻¹'
      ((fun p : E × ℝ => (p.1, c * p.2)) '' Ω) = Ω := shear_preimage_image hc Ω
  have hkey := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := seeleyLam (X := E) c) (s := (fun p : E × ℝ => (p.1, c * p.2)) '' Ω) (f := u)
    (hu.mono hsub) himg.uniqueDiffOn
    (by rw [hfun, hpre]; exact hΩ.uniqueDiffOn)
    (x := x) (by rw [hfun]; exact ⟨x, hx, rfl⟩) (i := i) le_rfl
  rw [hfun] at hkey
  rw [hpre] at hkey
  have hL : iteratedFDeriv ℝ i (fun p : E × ℝ => u (p.1, c * p.2)) x
      = iteratedFDerivWithin ℝ i (fun p : E × ℝ => u (p.1, c * p.2)) Ω x :=
    ((iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω)
      (f := fun p : E × ℝ => u (p.1, c * p.2)) i hΩ) hx).symm
  have hR : (iteratedFDerivWithin ℝ i u ((fun p : E × ℝ => (p.1, c * p.2)) '' Ω)
        ((fun p : E × ℝ => (p.1, c * p.2)) x)).compContinuousLinearMap
          (fun _ => seeleyLam (X := E) c)
      = (iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)).compContinuousLinearMap
          (fun _ => seeleyLam (X := E) c) := by
    rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (s := (fun p : E × ℝ => (p.1, c * p.2)) '' Ω) (f := u) i himg) ⟨x, hx, rfl⟩]
    simp only [seeleyLam_apply]
  rw [hL]
  change iteratedFDerivWithin ℝ i (u ∘ fun p : E × ℝ => (p.1, c * p.2)) Ω x = _
  rw [hkey, hR]

/-- Sup-norm bound for the pullback under the shear, for functions that are `C^i` on an open
set `A` containing the image of `Ω`. -/
lemma gDN_comp_shear_le {c : ℝ} (hc : 1 ≤ |c|) {i : ℕ} {A Ω : Set (E × ℝ)} (hA : IsOpen A)
    (hΩ : IsOpen Ω) (hsub : (fun p : E × ℝ => (p.1, c * p.2)) '' Ω ⊆ A)
    {u : E × ℝ → ℂ} (hu : ContDiffOn ℝ (i : WithTop ENat) u A) :
    gDN i (fun p : E × ℝ => u (p.1, c * p.2)) Ω ≤ ENNReal.ofReal (|c| ^ i) * gDN i u A := by
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have hmax : max 1 |c| = |c| := max_eq_right hc
  refine iSup₂_le fun x hx => ?_
  rw [iteratedFDeriv_comp_shear_of_contDiffOn hc0 hA hΩ hsub hu hx]
  calc ENNReal.ofReal ‖(iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)).compContinuousLinearMap
        (fun _ => seeleyLam (X := E) c)‖
      ≤ ENNReal.ofReal (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)‖ * |c| ^ i) :=
        ENNReal.ofReal_le_ofReal (by
          refine le_trans (norm_compContinuousLinearMap_const_le _ c) ?_
          rw [hmax])
    _ = ENNReal.ofReal ‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)‖ * ENNReal.ofReal (|c| ^ i) :=
        ENNReal.ofReal_mul (norm_nonneg _)
    _ = ENNReal.ofReal (|c| ^ i) *
        ENNReal.ofReal ‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)‖ := mul_comm _ _
    _ ≤ ENNReal.ofReal (|c| ^ i) * gDN i u A := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [seeleyLam_apply]
        exact le_gDN i (hsub ⟨x, hx, rfl⟩)

/-- Hölder-seminorm bound for the pullback under the shear, for functions that are `C^i` on an
open set `A` containing the image of `Ω`. -/
lemma gSN_comp_shear_le {c : ℝ} (hc : 1 ≤ |c|) {i : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {A Ω : Set (E × ℝ)} (hA : IsOpen A) (hΩ : IsOpen Ω)
    (hsub : (fun p : E × ℝ => (p.1, c * p.2)) '' Ω ⊆ A)
    {u : E × ℝ → ℂ} (hu : ContDiffOn ℝ (i : WithTop ENat) u A) :
    gSN i α (fun p : E × ℝ => u (p.1, c * p.2)) Ω
      ≤ ENNReal.ofReal ((|c| : ℝ) ^ (i + α)) * gSN i α u A := by
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have hcpos : 0 < |c| := lt_of_lt_of_le one_pos hc
  have hmax : max 1 |c| = |c| := max_eq_right hc
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [iteratedFDeriv_comp_shear_of_contDiffOn hc0 hA hΩ hsub hu hx,
    iteratedFDeriv_comp_shear_of_contDiffOn hc0 hA hΩ hsub hu hy]
  rw [compContinuousLinearMap_sub_const]
  by_cases hxy' : seeleyLam (X := E) c x = seeleyLam (X := E) c y
  · rw [hxy', sub_self]
    have hz : (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ).compContinuousLinearMap
        (fun _ => seeleyLam (X := E) c) = 0 := by
      ext m; simp
    rw [hz, norm_zero, zero_div, ENNReal.ofReal_zero]
    exact bot_le
  · have hnum : (0:ℝ) < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    have hden : (0:ℝ) < ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy')) _
    have hle : ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ≤ |c| * ‖x - y‖ := by
      calc ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖
          = ‖seeleyLam (X := E) c (x - y)‖ := by rw [map_sub]
        _ ≤ ‖seeleyLam (X := E) c‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max 1 |c| * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right (norm_seeleyLam_le c) (norm_nonneg _)
        _ = |c| * ‖x - y‖ := by rw [hmax]
    have hnorm := norm_compContinuousLinearMap_const_le
      (iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
        - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)) c
    rw [hmax] at hnorm
    have key : ‖(iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
            - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) c)‖ / ‖x - y‖ ^ α
        ≤ (|c| : ℝ) ^ (i + α)
          * (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖
            / ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α) := by
      have h1 : ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α
          ≤ (|c| : ℝ) ^ α * ‖x - y‖ ^ α := by
        rw [← Real.mul_rpow hcpos.le (norm_nonneg _)]
        exact Real.rpow_le_rpow (norm_nonneg _) hle hα
      have hkey : (1:ℝ) / ‖x - y‖ ^ α
          ≤ (|c| : ℝ) ^ α / ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α := by
        rw [div_le_iff₀ hnum, div_mul_eq_mul_div, le_div_iff₀ hden, one_mul]
        exact h1
      refine (div_le_div_of_nonneg_right hnorm hnum.le).trans ?_
      calc ‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖ * (|c| : ℝ) ^ i / ‖x - y‖ ^ α
          = (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖ * (|c| : ℝ) ^ i)
              * (1 / ‖x - y‖ ^ α) := by ring
        _ ≤ (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖ * (|c| : ℝ) ^ i)
              * ((|c| : ℝ) ^ α
                / ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (|c| : ℝ) ^ (i + α)
              * (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
                - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖
                / ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α) := by
            rw [Real.rpow_add hcpos, Real.rpow_natCast]
            ring
    calc ENNReal.ofReal (‖(iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
            - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) c)‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((|c| : ℝ) ^ (i + α)
            * (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖
              / ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α)) :=
          ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal ((|c| : ℝ) ^ (i + α))
            * ENNReal.ofReal (‖iteratedFDeriv ℝ i u (seeleyLam (X := E) c x)
              - iteratedFDeriv ℝ i u (seeleyLam (X := E) c y)‖
              / ‖seeleyLam (X := E) c x - seeleyLam (X := E) c y‖ ^ α) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg hcpos.le _)
      _ ≤ ENNReal.ofReal ((|c| : ℝ) ^ (i + α)) * gSN i α u A := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          rw [seeleyLam_apply, seeleyLam_apply]
          exact le_gSN i α (hsub ⟨x, hx, rfl⟩) (hsub ⟨y, hy, rfl⟩) hxy'


/-! ## The individual Seeley terms vanish far out on the lower slab -/

/-- If `b m * |x.2|` is at least `4` then the `m`-th Seeley term vanishes identically on a
neighbourhood of `x` (a point of the open lower half space). -/
lemma seeleyTerm_eventuallyEq_zero {a b : ℕ → ℝ} {g : E × ℝ → ℂ} {m : ℕ} {x : E × ℝ}
    (hb0 : 0 ≤ b m) (hx : x.2 < 0) (h : 4 ≤ b m * |x.2|) :
    seeleyTerm a b g m =ᶠ[𝓝 x] 0 := by
  have hneigh : {y : E × ℝ | y.2 < x.2 / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const) ?_
    change x.2 < x.2 / 2
    linarith
  filter_upwards [hneigh] with y hy
  have hyabs : |x.2| / 2 ≤ |y.2| := by
    rw [abs_of_neg hx, abs_of_neg (by linarith : y.2 < 0)]
    linarith
  have harg : 2 ≤ |-(b m) * y.2| := by
    rw [abs_neg_mul, abs_of_nonneg hb0]
    nlinarith [h]
  rw [seeleyTerm_apply, seeleyCut_eq_zero harg]
  simp

/-- On the open lower slab the Seeley extension agrees with a locally finite sum of the terms. -/
lemma seeleyExt_eventuallyEq_finsetSum {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {g : E × ℝ → ℂ} {x : E × ℝ}
    (hx : x.2 < 0) :
    ∃ N : ℕ, seeleyExt a b g =ᶠ[𝓝 x]
      (fun y => ∑ m ∈ Finset.range N, seeleyTerm a b g m y) := by
  obtain ⟨N, hN⟩ := exists_b_ge hbT (4 / |x.2|)
  have hxabs : 0 < |x.2| := abs_pos.mpr (ne_of_lt hx)
  have h1 : ∀ m ≥ N, 4 ≤ b m * |x.2| := by
    intro m hm
    have hle : 4 / |x.2| ≤ b m := hN m hm
    rw [div_le_iff₀ hxabs] at hle
    linarith
  refine ⟨N, ?_⟩
  have hneigh : {y : E × ℝ | y.2 < x.2 / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const) ?_
    change x.2 < x.2 / 2
    linarith
  have hfin : (fun y => ∑ m ∈ Finset.range N, seeleyTerm a b g m y)
      =ᶠ[𝓝 x] seeleySum a b g := by
    refine Filter.eventuallyEq_of_mem (s := {y : E × ℝ | y.2 < x.2 / 2}) hneigh
      fun y hy => ?_
    have hy' : y.2 < x.2 / 2 := hy
    have hyabs : |x.2| / 2 ≤ |y.2| := by
      rw [abs_of_neg hx, abs_of_neg (by linarith : y.2 < 0)]
      linarith
    rw [seeleySum]
    refine (tsum_eq_sum (s := Finset.range N) fun m hm => ?_).symm
    simp only [Finset.mem_range, not_lt] at hm
    have harg : 2 ≤ |-(b m) * y.2| := by
      rw [abs_neg_mul, abs_of_nonneg (by linarith [hb m] : (0 : ℝ) ≤ b m)]
      nlinarith [h1 m hm]
    rw [seeleyTerm_apply, seeleyCut_eq_zero harg]
    simp
  have h2 : seeleyExt a b g =ᶠ[𝓝 x] seeleySum a b g :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hx)
      (fun y hy => seeleyExt_of_neg a b g hy)
  exact h2.trans hfin.symm

/-- The Seeley extension is `C^i` on the open upper half space, where it agrees with `g`. -/
lemma contDiffOn_seUp_seeleyExt {a b : ℕ → ℝ} {W : Set E} {i : ℕ} {g : E × ℝ → ℂ}
    (hg : ContDiffOn ℝ (i : WithTop ENat) g (seUp W)) :
    ContDiffOn ℝ (i : WithTop ENat) (seeleyExt a b g) (seUp W) :=
  hg.congr fun p hp => seeleyExt_of_nonneg a b g (le_of_lt hp.2)

/-- The Seeley extension is `C^i` on the open lower slab, given that `g` is `C^i` on the open
upper half space. -/
lemma contDiffOn_seLw_seeleyExt {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {W : Set E} (hW : IsOpen W)
    {δ : ℝ} {i : ℕ} {g : E × ℝ → ℂ} (hg : ContDiffOn ℝ (i : WithTop ENat) g (seUp W)) :
    ContDiffOn ℝ (i : WithTop ENat) (seeleyExt a b g) (seLw W δ) := by
  have hOpen : IsOpen (seLw W δ) := isOpen_seLw hW δ
  refine hOpen.contDiffOn_iff.mpr fun x hx => ?_
  simp only [mem_seLw] at hx
  obtain ⟨N, hN⟩ := seeleyExt_eventuallyEq_finsetSum (a := a) (b := b) hb hbT (g := g) hx.2.2
  refine (ContDiffAt.sum (s := Finset.range N) fun m _ => ?_).congr_of_eventuallyEq hN
  have hbm : (0 : ℝ) < b m := by linarith [hb m]
  have hcmem : (seeleyLam (X := E) (-(b m))) x ∈ seUp W :=
    shear_image_seLw_subset_seUp (W := W) (δ := δ) (by linarith [hb m]) ⟨x, hx, rfl⟩
  have hgs : ContDiffAt ℝ (i : WithTop ENat) (fun q : E × ℝ => g (q.1, -(b m) * q.2)) x := by
    have hpre : (seeleyLam (X := E) (-(b m))) ⁻¹' (seUp W) ∈ 𝓝 x :=
      (isOpen_seUp hW).preimage (by fun_prop) |>.mem_nhds hcmem
    have h1 := (hg.comp_continuousLinearMap (seeleyLam (X := E) (-(b m)))).contDiffAt hpre
    have h2 : (fun q : E × ℝ => g (q.1, -(b m) * q.2))
        = (g ∘ (seeleyLam (X := E) (-(b m)))) := by
      funext q; simp [seeleyLam_apply]
    rwa [h2]
  have hcut : ContDiffAt ℝ (i : WithTop ENat)
      (fun q : E × ℝ => seeleyCut (-(b m) * q.2)) x := by
    have h2 : ContDiff ℝ ∞ (fun q : E × ℝ => -(b m) * q.2) := by fun_prop
    exact ((seeleyCut_contDiff.comp h2).of_le (by simp)).contDiffAt
  have hsmul : ContDiffAt ℝ (i : WithTop ENat)
      (fun q : E × ℝ => seeleyCut (-(b m) * q.2) • g (q.1, -(b m) * q.2)) x :=
    hcut.smul hgs
  have hfin : ContDiffAt ℝ (i : WithTop ENat)
      (fun q : E × ℝ => (a m) • (seeleyCut (-(b m) * q.2) • g (q.1, -(b m) * q.2))) x :=
    (contDiffAt_const (c := (a m))).smul hsmul
  refine hfin.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext q
  rw [seeleyTerm_apply]
  simp only [Complex.real_smul]

end Work.NN.Final
