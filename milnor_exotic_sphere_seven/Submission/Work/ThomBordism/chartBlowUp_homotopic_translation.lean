import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.Tubular.OnePointModel
import Submission.Work.ThomBordism.chartBlowUp_core
import Submission.Work.Tubular.blowCoeff_bounds

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The blow-up chart is homotopic to the translation, through maps vanishing only at the centre

This file proves `Work.ThomBordism.chartBlowUp_homotopic_translation`: near the point `E.e x` of the
tube, the ambient chart map `chartAffine E x` read through the radial blow-up
`Work.Tubular.normalBlowUp E ε` of the normal foot is homotopic to the plain translation
`y ↦ y - E.e x`, through maps whose only zero is the centre `E.e x`.

The homotopy is the *radial* one: on the small neighbourhood `N` of `E.e x` on which the normal foot
`p = C.inv y` has norm `< ε/2`, the two maps are

* `f₀ y = E.e p.1.1 + blowCoeff E ε p • p.1.2 - E.e x`,
* `f₁ y = E.e p.1.1 + p.1.2 - E.e x`  (since `y = tubeMap E p`),

and one interpolates the *coefficient* of the normal vector,
`H t y = E.e p.1.1 + c_t • p.1.2 - E.e x`, `c_t = (1-t) * blowCoeff E ε p + t`.  On `‖p‖ ≤ ε/2` one
has `1 ≤ blowCoeff E ε p ≤ 2` and hence `1 ≤ c_t ≤ 2`, so `c_t ≠ 0` and — the key geometric point —
`|c_t| * ‖p‖ ≤ ε`, i.e. the rescaled point still lies in the closed `ε`-disc bundle, where the tube
map is injective; this is what forces the vanishing locus of `H t ·` to be the single point `E.e x`.
-/

open scoped Topology unitInterval
open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.ThomBordism

noncomputable section

variable {k : ℕ} {V : Work.ThomBordism.Man8}

/-! ## The blow-up coefficient is continuous on the open disc bundle -/

/-- The blow-up coefficient `ε * (ε - ‖p‖)⁻¹` is continuous along any continuous family of points of
the open `ε`-disc bundle. -/
theorem continuous_blowCoeff_comp {X : Type*} [TopologicalSpace X]
    (E : EmbeddingData V (8 + k)) {ε : ℝ} {f : C(X, Work.Tubular.NormalTotal E)}
    (hf : ∀ z, Work.Tubular.normalNorm E (f z) < ε) :
    Continuous (fun z => Work.Tubular.blowCoeff E ε (f z)) := by
  have h1 : Continuous (fun z => ε - Work.Tubular.normalNorm E (f z)) :=
    continuous_const.sub ((Work.Tubular.continuous_normalNorm E).comp f.continuous)
  have h2 : Continuous (fun z => (ε - Work.Tubular.normalNorm E (f z))⁻¹) :=
    h1.inv₀ (fun z => by
      have hlt := hf z
      have h0 := Work.Tubular.normalNorm_nonneg E (f z)
      linarith)
  have h3 : (fun z => Work.Tubular.blowCoeff E ε (f z))
      = fun z => ε * (ε - Work.Tubular.normalNorm E (f z))⁻¹ := by
    funext z; rw [Work.Tubular.blowCoeff]
  rw [h3]
  exact h2.const_mul ε

/-! ## The constant radial rescale -/

/-- The tubular map of a constant radial rescale `p ↦ ⟨proj p, c • vec p⟩`. -/
theorem tubeMap_radialRescale (E : EmbeddingData V (8 + k)) (c : ℝ)
    (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.tubeMap E (radialRescale E (fun _ => c) p) = E.e p.1.1 + c • p.1.2 := by
  rw [Work.Tubular.tubeMap, radialRescale_coe]

/-- The ambient chart map of a constant radial rescale. -/
theorem chartAffine_radialRescale (E : EmbeddingData V (8 + k)) (x : V.pt) (c : ℝ)
    (p : Work.Tubular.NormalTotal E) :
    chartAffine E x (radialRescale E (fun _ => c) p)
      = Work.Tubular.tubeMap E (radialRescale E (fun _ => c) p) - E.e x := by
  rw [chartAffine_apply, Work.Tubular.tubeMap, radialRescale_coe]

/-- The blow-up is the constant radial rescale by the blow-up coefficient. -/
theorem radialRescale_blowCoeff (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (p : Work.Tubular.NormalTotal E) :
    radialRescale E (fun _ => Work.Tubular.blowCoeff E ε p) p
      = Work.Tubular.normalBlowUp E ε p := rfl

/-- The blow-up fixes the zero section: `0_x ↦ 0_x`. -/
theorem normalBlowUp_zeroSection (E : EmbeddingData V (8 + k)) (ε : ℝ) (x : V.pt) :
    Work.Tubular.normalBlowUp E ε (Work.Tubular.zeroSectionNormal E x)
      = Work.Tubular.zeroSectionNormal E x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rw [Work.Tubular.normalBlowUp_vec]
    simp

end

end Work.ThomBordism


namespace Work.ThomBordism

noncomputable section

variable {k : ℕ} {V : Work.ThomBordism.Man8}

/-- **The blow-up chart is homotopic to the translation, through maps vanishing only at the
centre.** -/
theorem chartBlowUp_homotopic_translation (k : ℕ) (V : Work.ThomBordism.Man8)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∃ N : Set (Work.Tubular.Euc (8 + k)), IsOpen N ∧ E.e x ∈ N ∧
      ∃ (f₀ f₁ : C(↥N, Work.Tubular.Euc (8 + k))),
        (∀ y, f₀ y = Work.ThomBordism.chartAffine E x
          (Work.Tubular.normalBlowUp E ε (C.inv (y : Work.Tubular.Euc (8 + k))))) ∧
        (∀ y, f₁ y = (y : Work.Tubular.Euc (8 + k)) - E.e x) ∧
        (∀ y : ↥N, f₀ y = 0 ↔ (y : Work.Tubular.Euc (8 + k)) = E.e x) ∧
        (∀ y : ↥N, f₁ y = 0 ↔ (y : Work.Tubular.Euc (8 + k)) = E.e x) ∧
        ∃ H : TopCat.Homotopy (TopCat.ofHom f₀) (TopCat.ofHom f₁),
          ∀ (t : unitInterval) (y : ↥N), H (t, y) = 0 →
            (y : Work.Tubular.Euc (8 + k)) = E.e x := by
  have hε : 0 < ε := C.eps_pos
  -- the neighbourhood of `E.e x`
  let N : Set (Work.Tubular.Euc (8 + k)) :=
    C.openTube ∩ C.inv ⁻¹' {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε / 2}
  have hNopen : IsOpen N := by
    show IsOpen (C.openTube ∩ C.inv ⁻¹'
      {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε / 2})
    exact C.continuousOn_openTube_inv.isOpen_inter_preimage C.openTube_isOpen
      (isOpen_lt (Work.Tubular.continuous_normalNorm E) continuous_const)
  have hxN : E.e x ∈ N := by
    show E.e x ∈ C.openTube ∩ C.inv ⁻¹'
      {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε / 2}
    refine ⟨C.mem_openTube x, ?_⟩
    show Work.Tubular.normalNorm E (C.inv (E.e x)) < ε / 2
    rw [inv_embed E C x]
    simp only [Work.Tubular.normalNorm, Work.Tubular.zeroSectionNormal_apply, norm_zero]
    linarith
  -- the two structure lemmas about points of `N`
  have hInvOn : ∀ y : ↥N, ((y : Work.Tubular.Euc (8 + k))) ∈ C.openTube := by
    intro y
    have h : (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube ∧ C.inv (y : Work.Tubular.Euc (8 + k))
        ∈ {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε / 2} := y.2
    exact h.1
  have hnorm_half : ∀ y : ↥N,
      Work.Tubular.normalNorm E (C.inv (y : Work.Tubular.Euc (8 + k))) ≤ ε / 2 := by
    intro y
    have h : (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube ∧ C.inv (y : Work.Tubular.Euc (8 + k))
        ∈ {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε / 2} := y.2
    exact le_of_lt h.2
  have hnorm_lt : ∀ y : ↥N,
      Work.Tubular.normalNorm E (C.inv (y : Work.Tubular.Euc (8 + k))) < ε :=
    fun y => lt_of_le_of_lt (hnorm_half y) (by linarith)
  -- continuity of the normal foot and of the blow-up
  have hInv_cont : Continuous (fun y : ↥N => C.inv (y : Work.Tubular.Euc (8 + k))) :=
    C.continuousOn_openTube_inv.comp_continuous continuous_subtype_val hInvOn
  have hblow_cont : Continuous (fun y : ↥N =>
      Work.Tubular.normalBlowUp E ε (C.inv (y : Work.Tubular.Euc (8 + k)))) := by
    have h1 : ContinuousOn (Work.Tubular.normalBlowUp E ε)
        {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p < ε} :=
      fun p hp => (Work.Tubular.continuousAt_normalBlowUp hp).continuousWithinAt
    exact h1.comp_continuous hInv_cont hnorm_lt
  have hcont_chartAffine : Continuous (chartAffine E x) :=
    ((E.smooth.continuous.comp (Work.Tubular.NormalTotal.continuous_proj E)).add
      (Work.Tubular.NormalTotal.continuous_vec E)).sub continuous_const
  -- the two maps
  let f₀ : C(↥N, Work.Tubular.Euc (8 + k)) :=
    ⟨fun y => chartAffine E x
        (Work.Tubular.normalBlowUp E ε (C.inv (y : Work.Tubular.Euc (8 + k)))),
      hcont_chartAffine.comp hblow_cont⟩
  let f₁ : C(↥N, Work.Tubular.Euc (8 + k)) :=
    ⟨fun y => (y : Work.Tubular.Euc (8 + k)) - E.e x,
      continuous_subtype_val.sub continuous_const⟩
  -- the homotopy, as a radial rescale with a time-dependent coefficient
  let g : C(unitInterval × ↥N, Work.Tubular.NormalTotal E) :=
    ⟨fun q => C.inv (q.2 : Work.Tubular.Euc (8 + k)),
      C.continuousOn_openTube_inv.comp_continuous
        (continuous_subtype_val.comp continuous_snd) (fun q => hInvOn q.2)⟩
  let Zc : unitInterval × ↥N → Work.Tubular.NormalTotal E :=
    fun q => radialRescale E
      (fun _ => (1 - (q.1 : ℝ)) * Work.Tubular.blowCoeff E ε (g q) + (q.1 : ℝ)) (g q)
  have hZc : Continuous Zc := by
    have hgv : Continuous (fun q : unitInterval × ↥N =>
        ((g q : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k))) :=
      continuous_subtype_val.comp g.continuous
    have htq : Continuous (fun q : unitInterval × ↥N => (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hlam : Continuous (fun q : unitInterval × ↥N => Work.Tubular.blowCoeff E ε (g q)) :=
      continuous_blowCoeff_comp E (fun q => by
        have h := hnorm_lt q.2
        exact h)
    have hcoef : Continuous (fun q : unitInterval × ↥N =>
        (1 - (q.1 : ℝ)) * Work.Tubular.blowCoeff E ε (g q) + (q.1 : ℝ)) :=
      ((continuous_const.sub htq).mul hlam).add htq
    refine Continuous.subtype_mk ?_ _
    exact Continuous.prodMk (continuous_fst.comp hgv)
      (hcoef.smul (continuous_snd.comp hgv))
  have hZc_apply : ∀ (t : unitInterval) (y : ↥N),
      Zc (t, y) = radialRescale E
        (fun _ => (1 - (t : ℝ)) * Work.Tubular.blowCoeff E ε
          (C.inv (y : Work.Tubular.Euc (8 + k))) + (t : ℝ))
        (C.inv (y : Work.Tubular.Euc (8 + k))) := fun t y => rfl
  let Hmap : C(unitInterval × ↥N, Work.Tubular.Euc (8 + k)) :=
    ⟨fun q => chartAffine E x (Zc q), hcont_chartAffine.comp hZc⟩
  have hH0 : ∀ y : ↥N, Hmap (0, y) = f₀ y := by
    intro y
    show chartAffine E x (Zc (0, y)) = chartAffine E x
      (Work.Tubular.normalBlowUp E ε (C.inv (y : Work.Tubular.Euc (8 + k))))
    have hZ0 : Zc (0, y) = Work.Tubular.normalBlowUp E ε
        (C.inv (y : Work.Tubular.Euc (8 + k))) := by
      rw [hZc_apply (0 : unitInterval) y]
      have hfun : (fun (_ : ℝ) => (1 - ((0 : unitInterval) : ℝ)) * Work.Tubular.blowCoeff E ε
            (C.inv (y : Work.Tubular.Euc (8 + k))) + ((0 : unitInterval) : ℝ))
          = fun (_ : ℝ) => Work.Tubular.blowCoeff E ε
            (C.inv (y : Work.Tubular.Euc (8 + k))) := by
        funext r; norm_num
      rw [hfun, radialRescale_blowCoeff]
    rw [hZ0]
  have hH1 : ∀ y : ↥N, Hmap (1, y) = f₁ y := by
    intro y
    show chartAffine E x (Zc (1, y)) = (y : Work.Tubular.Euc (8 + k)) - E.e x
    have hZ1 : Zc (1, y) = C.inv (y : Work.Tubular.Euc (8 + k)) := by
      rw [hZc_apply (1 : unitInterval) y]
      have hfun : (fun (_ : ℝ) => (1 - ((1 : unitInterval) : ℝ)) * Work.Tubular.blowCoeff E ε
            (C.inv (y : Work.Tubular.Euc (8 + k))) + ((1 : unitInterval) : ℝ))
          = fun (_ : ℝ) => (1 : ℝ) := by
        funext r; norm_num
      rw [hfun, radialRescale_one]
    rw [hZ1]
    exact chartAffine_inv E C x (C.openTube_subset_U (hInvOn y))
  have hf₀_zero : ∀ y : ↥N, f₀ y = 0 ↔ (y : Work.Tubular.Euc (8 + k)) = E.e x := by
    intro y
    constructor
    · intro hy
      have hy' : chartAffine E x (Work.Tubular.normalBlowUp E ε
          (C.inv (y : Work.Tubular.Euc (8 + k)))) = 0 := hy
      have htu : Work.Tubular.tubeMap E (radialRescale E
          (fun _ => Work.Tubular.blowCoeff E ε (C.inv (y : Work.Tubular.Euc (8 + k))))
          (C.inv (y : Work.Tubular.Euc (8 + k)))) = E.e x := by
        rw [← radialRescale_blowCoeff E ε, chartAffine_radialRescale E x] at hy'
        exact sub_eq_zero.mp hy'
      have hb := Work.Tubular.blowCoeff_bounds hε (hnorm_half y)
      have hle : |Work.Tubular.blowCoeff E ε (C.inv (y : Work.Tubular.Euc (8 + k)))| *
          Work.Tubular.normalNorm E (C.inv (y : Work.Tubular.Euc (8 + k))) ≤ ε := by
        rw [abs_of_nonneg (by linarith [hb.1])]
        have h0 := Work.Tubular.normalNorm_nonneg E (C.inv (y : Work.Tubular.Euc (8 + k)))
        nlinarith [hb.2, hnorm_half y]
      have hc0 : Work.Tubular.blowCoeff E ε (C.inv (y : Work.Tubular.Euc (8 + k))) ≠ 0 := by
        linarith [hb.1]
      rw [← C.inv_tubeMap_of_mem_openTube (hInvOn y)]
      exact chartBlowUp_core C hc0 htu hle
    · intro hy
      show chartAffine E x (Work.Tubular.normalBlowUp E ε
        (C.inv (y : Work.Tubular.Euc (8 + k)))) = 0
      rw [hy, inv_embed E C x, normalBlowUp_zeroSection, chartAffine_zeroSection]
  have hf₁_zero : ∀ y : ↥N, f₁ y = 0 ↔ (y : Work.Tubular.Euc (8 + k)) = E.e x := by
    intro y
    show (y : Work.Tubular.Euc (8 + k)) - E.e x = 0 ↔
      (y : Work.Tubular.Euc (8 + k)) = E.e x
    rw [sub_eq_zero]
  have hHker : ∀ (t : unitInterval) (y : ↥N), Hmap (t, y) = 0 →
      (y : Work.Tubular.Euc (8 + k)) = E.e x := by
    intro t y ht
    set c : ℝ := (1 - (t : ℝ)) * Work.Tubular.blowCoeff E ε
      (C.inv (y : Work.Tubular.Euc (8 + k))) + (t : ℝ) with hcdef
    have htmem : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨t.2.1, t.2.2⟩
    have hb := Work.Tubular.blowCoeff_bounds hε (hnorm_half y)
    have hcge : 1 ≤ c := by rw [hcdef]; nlinarith [hb.1, htmem.2]
    have hcle : c ≤ 2 := by rw [hcdef]; nlinarith [hb.2, htmem.1]
    have hcne : c ≠ 0 := by linarith
    have htu : Work.Tubular.tubeMap E (radialRescale E (fun _ => c)
        (C.inv (y : Work.Tubular.Euc (8 + k)))) = E.e x := by
      have htZ : chartAffine E x (Zc (t, y)) = 0 := ht
      rw [hZc_apply t y, ← hcdef] at htZ
      rw [chartAffine_radialRescale E x c (C.inv (y : Work.Tubular.Euc (8 + k)))] at htZ
      exact sub_eq_zero.mp htZ
    have hle : |c| * Work.Tubular.normalNorm E (C.inv (y : Work.Tubular.Euc (8 + k))) ≤ ε := by
      rw [abs_of_nonneg (by linarith)]
      have h0 := Work.Tubular.normalNorm_nonneg E (C.inv (y : Work.Tubular.Euc (8 + k)))
      nlinarith [hcle, hnorm_half y, h0]
    rw [← C.inv_tubeMap_of_mem_openTube (hInvOn y)]
    exact chartBlowUp_core C hcne htu hle
  refine ⟨N, hNopen, hxN, ?_⟩
  refine ⟨f₀, f₁, ?_, ?_, hf₀_zero, hf₁_zero, ?_⟩
  · intro y; rfl
  · intro y; rfl
  · refine ⟨⟨Hmap, hH0, hH1⟩, ?_⟩
    intro t y hzero
    exact hHker t y hzero

end

end Work.ThomBordism
