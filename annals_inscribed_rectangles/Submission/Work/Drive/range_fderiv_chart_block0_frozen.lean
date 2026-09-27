import Mathlib
import Submission.Work.Drive.encFamQ0
import Submission.Work.Drive.range_mfderiv_shear_eq
import Submission.Work.Drive.hrichCore
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.projTimesLine
import Submission.Work.Drive.range_fderiv_chart_planeBlock

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The range of the *frozen* block-`0` charted parameter derivative

`Work.Drive.encFamQ0₀` is block `0` of the corrected ends-clause family: the class-perturbed homotopy
evaluated at the sheared plane coordinates, at the **constant** level `c₀`.  When the class
perturbation is frozen (`p = 0`) the live parameter of the block is only the shear parameter
`q₀ ∈ 𝔼⁴`, and the map to differentiate is

`z ↦ chr p (H (s, shear z u), c₀)`

(`s` the frozen homotopy time, `u` the frozen plane point).  This file computes the range of its
derivative:

* the constant second component means that the level direction **vanishes** — unlike the plane blocks
  (`range_fderiv_chart_planeBlock`, where the twist of the level contributes the whole second factor
  and the answer is `liftAll`), here the image is `lift0 W`: the class reach `W` with *zero* level;
* the class reach of the shear-parametrised homotopy is the *same* as the class reach of the plane map
  `y ↦ H (s, y)` at the sheared point (`Work.Drive.range_mfderiv_shear_eq`), and the chart changes
  coordinates by `tangentCoordChange`.

So, with `W = tangentCoordChange · '' range (mfderiv (y ↦ H (s, y)) (shear q u))`,

`range (fderiv ℝ (z ↦ chr p (H (s, shear z u), c₀)) q) = lift0 W`,

which is exactly the shape of the reach `R₀` in `Work.Drive.hrichCore` (class directions only, zero
level).

The proof is the frozen analogue of `range_fderiv_chart_planeBlock`: the two new ingredients are
`map_psiLin_prod_bot` (`psiLin '' (W × {0}) = lift0 W`) and `range_fderiv_psiLin_prod_const` (the
range of the derivative of `z ↦ psiLin (f z, c)`), plus `contMDiff_slice`, which extracts the
smoothness of the frozen slice `y ↦ H (s, y)` from the joint smoothness of `H`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Work.Drive.projCharted Work.Drive.isManifold_projCharted
  Work.Drive.projTimesLineCharted Work.Drive.isManifold_projTimesLineCharted

/-! ## 1. The class directions with zero level -/

/-- **`psiLin` carries `W × {0}` onto `lift0 W`**: the class part lies in `W` and the level coordinate
vanishes.  The frozen counterpart of `map_psiLin_prod_top`. -/
theorem map_psiLin_prod_bot (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :
    Submodule.map (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4))
      (W.prod ⊥) = lift0 W := by
  ext z
  rw [Submodule.mem_map, mem_lift0]
  constructor
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨w, l⟩ := y
    rw [Submodule.mem_prod] at hy
    rw [← hzy]
    have hl : l = 0 := by simpa using hy.2
    exact ⟨by simpa [clsCLM_psiLin] using hy.1,
      by simpa [lvlCLM_psiLin] using hl⟩
  · rintro ⟨hz1, hz2⟩
    refine ⟨psiLin.symm z, ?_, psiLin.apply_symm_apply z⟩
    rw [Submodule.mem_prod]
    have hz2' : (psiLin.symm z).2 = 0 := by simpa [lvlCLM] using hz2
    exact ⟨by simpa [clsCLM] using hz1, by simpa using hz2'⟩

/-! ## 2. The range of the derivative of `z ↦ psiLin (f z, c)` -/

/-- **The range of the derivative of `psiLin` applied to a pair whose second component is
constant.**  The image is `lift0 (range (fderiv ℝ f x))`: the class reach, with *zero* level. -/
theorem range_fderiv_psiLin_prod_const
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 4)) (c : ℝ) (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => psiLin (f z, c)) x).range
      = lift0 (fderiv ℝ f x).range := by
  set L : EuclideanSpace ℝ (Fin 4) →L[ℝ] (EuclideanSpace ℝ (Fin 3) × ℝ) :=
    (fderiv ℝ f x).prod (0 : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ) with hLdef
  have hL : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) => (f z, c)) L x :=
    hf.hasFDerivAt.prodMk (hasFDerivAt_const c x)
  have hpsi : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) × ℝ => psiLin y)
      (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (f x, c) :=
    (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).hasFDerivAt
  have hF : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) => psiLin (f z, c))
      ((psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp L) x :=
    hpsi.comp x hL
  have hLrange : (L : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin 3) × ℝ)).range = (fderiv ℝ f x).range.prod ⊥ := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_prod.mpr ⟨LinearMap.mem_range.mpr ⟨z, rfl⟩, ?_⟩
      rw [Submodule.mem_bot]
      rfl
    · intro y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_prod.mp hy
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hy1
      have hy2' : y.2 = 0 := by simpa using hy2
      refine LinearMap.mem_range.mpr ⟨w, ?_⟩
      exact Prod.ext hw hy2'.symm
  rw [hF.fderiv]
  rw [show ((psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin 4)).comp L).range
      = Submodule.map (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin 4)) (L : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin 3) × ℝ)).range from
    LinearMap.range_comp _ _]
  rw [hLrange, map_psiLin_prod_bot]

/-! ## 3. The smoothness of the frozen slice -/

/-- The linear map `(y, t) ↦ (y 0, y 1, t) : 𝔼² × ℝ → 𝔼³`. -/
def embFrozen : EuclideanSpace ℝ (Fin 2) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ({ toFun := fun p => WithLp.toLp 2 ![p.1 0, p.1 1, p.2]
     map_add' := by intro a b; ext i; fin_cases i <;> simp
     map_smul' := by intro c a; ext i; fin_cases i <;> simp } :
    EuclideanSpace ℝ (Fin 2) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)).toContinuousLinearMap

@[simp] lemma embFrozen_apply (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    embFrozen (y, t) = WithLp.toLp 2 ![y 0, y 1, t] := rfl

@[simp] lemma embFrozen_apply_zero (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    embFrozen (y, t) 0 = y 0 := rfl

@[simp] lemma embFrozen_apply_one (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    embFrozen (y, t) 1 = y 1 := rfl

@[simp] lemma embFrozen_apply_two (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    embFrozen (y, t) 2 = t := rfl

/-- **The frozen slice of a jointly smooth `H` is smooth.**  The joint smoothness of `H` is given in
the "flattened" coordinates `x ↦ H (x 2, mk2 (x 0) (x 1))`; substituting `x = (y 0, y 1, s)` gives the
slice `y ↦ H (s, y)`. -/
theorem contMDiff_slice (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) (s : ℝ)
    (hH : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1)))) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y)) := by
  have hinl : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin 2) => (y, (0 : ℝ))) :=
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).contMDiff
  have htrans : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p + (0, s)) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_id.add contDiff_const
  have hpair : ContMDiff (𝓡 2) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin 2) => (y, s)) :=
    (htrans.comp hinl).congr (fun y => by simp)
  have hemb : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2) × ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) embFrozen :=
    embFrozen.contMDiff
  refine (hH.comp (hemb.comp hpair)).congr (fun y => ?_)
  simp only [Function.comp_apply, embFrozen_apply_zero, embFrozen_apply_one, embFrozen_apply_two]
  have hpt : mk2 (y 0) (y 1) = y := by ext i; fin_cases i <;> simp [mk2]
  rw [hpt]

/-! ## 4. The theorem -/

/-- **The range of the frozen block-`0` charted parameter derivative.**  With the level coordinate
frozen at `c₀` and only the shear parameter `z` live, the image of the derivative of
`z ↦ chr p (H (s, shear z u), c₀)` at `q` is the class reach of the plane map `y ↦ H (s, y)` at the
sheared point, changed by coordinates and lifted with **zero** level. -/
theorem range_fderiv_chart_block0_frozen
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (u : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 4))
    (s : ℝ) (c₀ : ℝ) (p : Projectivization ℝ (Eucl 3) × ℝ) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.projTimesLineCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ) :=
      Work.Drive.isManifold_projTimesLineCharted
    ContMDiff (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin 3))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) →
    Work.Drive.FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y)) →
    H (s, Work.Drive.shear q u) ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p.1).source →
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) => (Work.Drive.chr p)
        (H (s, Work.Drive.shear z u), c₀)) q).range =
      Work.Drive.lift0 (Submodule.map
        ((tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (H (s, Work.Drive.shear q u)) p.1 (H (s, Work.Drive.shear q u)))).toLinearMap
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y)) (Work.Drive.shear q u)).range) := by
  intro hH hfold hsrc
  -- the smoothness of the frozen slice
  have hslice : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y)) := contMDiff_slice H s hH
  obtain ⟨hfold0, hfold1⟩ :=
    (foldFlat_iff (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y))).mp hfold
  -- the shear is differentiable at `q`
  have hshearDiff : DifferentiableAt ℝ
      (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u) q := by
    have hfun' : (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u)
        = fun q' => spdPhiT u (ballClamp q') := by
      funext q'; exact (spdPhiT_ballClamp q' u).symm
    rw [hfun']
    exact (spdDifferentiableAt_PhiT u (ballClamp q)).comp q
      (spdHasFDerivAt_ballClamp q).differentiableAt
  have hL' : MDifferentiableAt (𝓡 4) (𝓡 2)
      (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u) q := hshearDiff.mdifferentiableAt
  have hAd : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y)) (shear q u) :=
    hslice.mdifferentiableAt (by simp)
  have hC0 : MDifferentiableAt (𝓡 4) (𝓡 3)
      ((fun y : EuclideanSpace ℝ (Fin 2) => H (s, y)) ∘
        (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' u)) q := hAd.comp q hL'
  have hC : MDifferentiableAt (𝓡 4) (𝓡 3)
      (fun q' : EuclideanSpace ℝ (Fin 4) => H (s, shear q' u)) q := by
    simpa [Function.comp_def] using hC0
  -- the chart rule for the class part
  have hF₁ : HasFDerivAt (fun q' : EuclideanSpace ℝ (Fin 4) =>
        chartAt (EuclideanSpace ℝ (Fin 3)) p.1 (H (s, shear q' u)))
      ((tangentCoordChange (𝓡 3) (H (s, shear q u)) p.1 (H (s, shear q u))).comp
        (mfderiv (𝓡 4) (𝓡 3) (fun q' : EuclideanSpace ℝ (Fin 4) => H (s, shear q' u)) q)) q :=
    hasFDerivAt_chartAt_comp (fun q' : EuclideanSpace ℝ (Fin 4) => H (s, shear q' u)) p.1 hC hsrc
  set f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) :=
    fun q' => chartAt (EuclideanSpace ℝ (Fin 3)) p.1 (H (s, shear q' u)) with hfdef
  have hf_diff : DifferentiableAt ℝ f q := by
    rw [hfdef]; exact hF₁.differentiableAt
  -- the chart of the transported product structure
  have hfun : (fun z : EuclideanSpace ℝ (Fin 4) => (chr p) (H (s, shear z u), c₀))
      = fun z => psiLin (f z, c₀) := by
    funext z
    rw [chr_projTimesLine_apply]
  have hfg := range_fderiv_psiLin_prod_const f q c₀ hf_diff
  -- the class part: chart change of the plane reach
  have hrw : (fderiv ℝ f q).range = Submodule.map
      ((tangentCoordChange (𝓡 3) (H (s, shear q u)) p.1 (H (s, shear q u)))).toLinearMap
      (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y))
        (shear q u)).range := by
    have hfd' : fderiv ℝ f q
        = (tangentCoordChange (𝓡 3) (H (s, shear q u)) p.1 (H (s, shear q u))).comp
            (mfderiv (𝓡 4) (𝓡 3) (fun q' : EuclideanSpace ℝ (Fin 4) => H (s, shear q' u)) q) := by
      rw [hfdef]; exact hF₁.fderiv
    rw [hfd']
    rw [show ((tangentCoordChange (𝓡 3) (H (s, shear q u)) p.1
            (H (s, shear q u))).comp
          (mfderiv (𝓡 4) (𝓡 3) (fun q' : EuclideanSpace ℝ (Fin 4) => H (s, shear q' u)) q)).range
        = Submodule.map ((tangentCoordChange (𝓡 3) (H (s, shear q u)) p.1
            (H (s, shear q u)))).toLinearMap
            (mfderiv (𝓡 4) (𝓡 3)
              (fun q' : EuclideanSpace ℝ (Fin 4) => H (s, shear q' u)) q).range from
      LinearMap.range_comp _ _]
    rw [range_mfderiv_shear_eq (fun y : EuclideanSpace ℝ (Fin 2) => H (s, y))
      hslice hfold0 hfold1 u q]
  rw [hfun, hfg, hrw]

end

end Work.Drive
