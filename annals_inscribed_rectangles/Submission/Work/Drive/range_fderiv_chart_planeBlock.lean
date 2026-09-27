import Mathlib
import Submission.Work.Drive.hrichCore
import Submission.Work.Drive.range_mfderiv_shear_eq
import Submission.Work.Drive.projTimesLine
import Submission.Work.Drive.shear_param_directions
import Submission.Work.Drive.deriv_thetaS_ne_zero_of_eq
import Submission.Work.Drive.fderiv_chartAt_chartedSpaceChangeModel
import Submission.Work.Drive.contDiff_shear_thetaS

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The range of the charted `planeBlock` parameter derivative

The encoded family of the ends clause (`EncodedGeneric`, `encFamQ0`) moves three chains by
*independent* parameter blocks.  This file computes, for the **plane block**, the image in the chart
of `ℝP³ × ℝ` of the parameter derivative

`z ↦ chr p (A (shear z.1 u), thetaS z.2 v)`  at `z = (q, r)`.

Here `A : 𝔼² → ℝP³` is the class map of the chain (the `C^∞` map, with its derivative annihilating
the two boundary directions of the parameter square), `shear` is the box shear, `thetaS` the twist
of the level interval, and `chr p` the chart of the transported product structure
`Work.Drive.projTimesLineCharted` at `p : ℝP³ × ℝ`.

**The statement.**  If `A (shear q u)` lies in the source of the projective chart at `p.1`, then

`range (fderiv ℝ (z ↦ chr p (A (shear z.1 u), thetaS z.2 v)) (q, r))`
`  = liftAll (map (tangentCoordChange … (A (shear q u)) p.1 …) (range (mfderiv A (shear q u))))`

i.e. the image is the *class* part `range (mfderiv A (shear q u))`, transported by the change of
coordinates `tangentCoordChange` of the projective chart and then lifted by `liftAll` to `ℝ⁴` with a
**free level coordinate** (the level direction is a full line: the hypothesis
`deriv (thetaS · v) r ≠ 0` says that the twist of the level is non-degenerate in its parameter, so
the `r`-direction contributes the whole second factor).  This is exactly the shape in which the
reaches `R₁, R₂` occur in the linear-algebraic closers
`Work.Drive.exists_coset_mem_lift`/`Work.Drive.surjective_pair_sub_of_coset` of `hrichCore.lean`.

**The proof** has three layers.

* *The chart.*  `chr p z = psiLin (chartAt 𝔼³ p.1 z.1, z.2)` — the transported product chart is the
  projective chart in the first factor and the identity in the second (`chr_projTimesLine_apply`).
* *The product.*  A map of the shape `z ↦ psiLin (f z.1, g z.2)` has derivative range
  `liftAll (range (fderiv ℝ f q))` as soon as `fderiv ℝ g r` is onto (`range_fderiv_psiLin_prod`,
  which uses `map_psiLin_prod_top`: `psiLin '' (W × ℝ) = liftAll W`).
* *The class part.*  `fderiv ℝ (q' ↦ chartAt 𝔼³ p.1 (A (shear q' u))) q` is the composite of
  `tangentCoordChange` with `mfderiv (A ∘ shear(·, u)) q` (`hasFDerivAt_chartAt_comp`), whose range
  is `range (mfderiv A (shear q u))` by `Work.Drive.range_mfderiv_shear_eq` (the shear does not
  change the range of the class derivative, by the boundary clamping of `A`).
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

/-- The product charted space `𝔼³ × ℝ` on `ℝP³ × ℝ`, made a local instance so that instance search
finds it (it cannot see through the `def` `ModelProd`). -/
local instance planeBlockProdCharted : ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ)
    (Projectivization ℝ (Eucl 3) × ℝ) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) ℝ ℝ

/-! ## 1. The chart of the transported product structure -/

/-- **The chart of `ℝP³ × ℝ` for the transported structure is
`psiLin ∘ (projective chart × identity)`.** -/
theorem chr_projTimesLine_apply (p z : Projectivization ℝ (Eucl 3) × ℝ) :
    chr p z = psiLin (chartAt (EuclideanSpace ℝ (Fin 3)) p.1 z.1, z.2) := by
  rw [show (chr p : Projectivization ℝ (Eucl 3) × ℝ → EuclideanSpace ℝ (Fin 4))
      = fun z => psiLin (chartAt (EuclideanSpace ℝ (Fin 3) × ℝ) p z) from
    chartAt_chartedSpaceChangeModel_apply (M := Projectivization ℝ (Eucl 3) × ℝ) psiLin p]
  rw [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
  simp

/-! ## 2. The lift `W × ℝ ↦ liftAll W` of the class coordinates -/

/-- **`liftAll W` is the image of `W × ℝ` under `psiLin`**: the linear isomorphism `psiLin` identifies
the splitting `ℝ⁴ ≅ 𝔼³ ⊕ ℝe₃` of `Work.Drive.clsCLM`/`Work.Drive.lvlCLM` with the product. -/
theorem map_psiLin_prod_top (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :
    Submodule.map (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4))
      (W.prod ⊤) = liftAll W := by
  ext z
  rw [Submodule.mem_map, mem_liftAll]
  constructor
  · rintro ⟨y, hy, hzy⟩
    rw [Submodule.mem_prod] at hy
    obtain ⟨w, l⟩ := y
    rw [← hzy]
    simpa [clsCLM_psiLin] using hy.1
  · intro hz
    refine ⟨psiLin.symm z, ?_, psiLin.apply_symm_apply z⟩
    rw [Submodule.mem_prod]
    exact ⟨hz, Submodule.mem_top⟩

/-! ## 3. The range of the derivative of `z ↦ psiLin (f z.1, g z.2)` -/

/-- **The range of the derivative of a map which is `psiLin` applied to a pair of functions of the
two variables separately.**  The second component only has to be *onto in the parameter*. -/
theorem range_fderiv_psiLin_prod
    (f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3)) (g : ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin 4)) (x₀ : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x₀)
    (hgr : (fderiv ℝ g x₀).range = ⊤) :
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) × ℝ => psiLin (f z.1, g z.2)) (x, x₀)).range
      = liftAll (fderiv ℝ f x).range := by
  set L : (EuclideanSpace ℝ (Fin 4) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 3) × ℝ) :=
    ((fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 4)) ℝ)).prod
      ((fderiv ℝ g x₀).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4)) ℝ))
    with hLdef
  have hL : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) × ℝ => (f z.1, g z.2)) L (x, x₀) :=
    (hf.hasFDerivAt.comp (x, x₀) hasFDerivAt_fst).prodMk
      (hg.hasFDerivAt.comp (x, x₀) hasFDerivAt_snd)
  have hpsi : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) × ℝ => psiLin y)
      (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (f x, g x₀) :=
    (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).hasFDerivAt
  have hF : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 4) × ℝ => psiLin (f z.1, g z.2))
      ((psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp L)
      (x, x₀) := hpsi.comp (x, x₀) hL
  have hLrange : L.range = (fderiv ℝ f x).range.prod ⊤ := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
      rw [Submodule.mem_prod]
      exact ⟨LinearMap.mem_range.mpr ⟨z.1, rfl⟩, Submodule.mem_top⟩
    · intro y hy
      rw [Submodule.mem_prod] at hy
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hy1
      have hy2' : y.2 ∈ (fderiv ℝ g x₀).range := by rw [hgr]; exact Submodule.mem_top
      obtain ⟨s, hs⟩ := LinearMap.mem_range.mp hy2'
      refine LinearMap.mem_range.mpr ⟨(w, s), ?_⟩
      have hval : (L : (EuclideanSpace ℝ (Fin 4) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3) × ℝ))
          (w, s) = ((fderiv ℝ f x) w, (fderiv ℝ g x₀) s) := rfl
      rw [hval]
      exact Prod.ext (by simpa using hw) (by simpa using hs)
  rw [hF.fderiv]
  rw [show ((psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin 4)).comp L).range
      = Submodule.map (psiLin : (EuclideanSpace ℝ (Fin 3) × ℝ) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin 4)) L.range from
    LinearMap.range_comp _ _]
  rw [hLrange, map_psiLin_prod_top]

/-! ## 4. The chain rule for the projective chart -/

/-- **The derivative of a chart followed by a smooth curve**, in terms of the manifold derivative and
the change of coordinates `tangentCoordChange`.  (The analogue of
`Work.Drive.fderiv_chart_comp` for a target charted on `𝔼³`.) -/
theorem hasFDerivAt_chartAt_comp {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) Ctop M]
    (C : EuclideanSpace ℝ (Fin 4) → M) (pp : M) {x : EuclideanSpace ℝ (Fin 4)}
    (hC : MDifferentiableAt (𝓡 4) (𝓡 3) C x)
    (hx : C x ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) pp).source) :
    HasFDerivAt (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) pp (C y))
      ((tangentCoordChange (𝓡 3) (C x) pp (C x)).comp (mfderiv (𝓡 4) (𝓡 3) C x)) x := by
  have hφ : MDifferentiableAt (𝓡 3) (𝓡 3) (chartAt (EuclideanSpace ℝ (Fin 3)) pp :
      M → EuclideanSpace ℝ (Fin 3)) (C x) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hx
  have hcomp : MDifferentiableAt (𝓡 4) (𝓡 3)
      (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) pp (C y)) x := hφ.comp x hC
  have hmf : mfderiv (𝓡 4) (𝓡 3) (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) pp (C y)) x
      = (tangentCoordChange (𝓡 3) (C x) pp (C x)).comp (mfderiv (𝓡 4) (𝓡 3) C x) := by
    have hmain := mfderiv_comp (g := (chartAt (EuclideanSpace ℝ (Fin 3)) pp)) (f := C) x hφ hC
    rw [mfderiv_chartAt_eq_tangentCoordChange hx] at hmain
    exact hmain
  have hd : DifferentiableAt ℝ (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) pp (C y)) x :=
    hcomp.differentiableAt
  have hfd : fderiv ℝ (fun y => chartAt (EuclideanSpace ℝ (Fin 3)) pp (C y)) x
      = (tangentCoordChange (𝓡 3) (C x) pp (C x)).comp (mfderiv (𝓡 4) (𝓡 3) C x) := by
    rw [← mfderiv_eq_fderiv, hmf]
  have h := hd.hasFDerivAt
  rw [hfd] at h
  exact h

/-! ## 5. The theorem -/

theorem range_fderiv_chart_planeBlock (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (u : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 4)) (r v : ℝ)
    (p : Projectivization ℝ (Eucl 3) × ℝ) :
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
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) A →
    (∀ y : EuclideanSpace ℝ (Fin 2), (y 0 = 0 ∨ y 0 = 1) →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A y
        (EuclideanSpace.single 0 1) = 0) →
    (∀ y : EuclideanSpace ℝ (Fin 2), (y 1 = 0 ∨ y 1 = 1) →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A y
        (EuclideanSpace.single 1 1) = 0) →
    deriv (fun r' : ℝ => Work.Drive.thetaS r' v) r ≠ 0 →
    A (Work.Drive.shear q u) ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) p.1).source →
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 4) × ℝ => (Work.Drive.chr p)
        (A (Work.Drive.shear z.1 u), Work.Drive.thetaS z.2 v)) (q, r)).range =
      Work.Drive.liftAll (Submodule.map
        ((tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (A (Work.Drive.shear q u)) p.1 (A (Work.Drive.shear q u)))).toLinearMap
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A
          (Work.Drive.shear q u)).range) := by
  intro hA hA0 hA1 hderiv hsrc
  -- the composite `A ∘ shear(·,u)` is differentiable at `q`, and so is the charted curve
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
  have hAd : MDifferentiableAt (𝓡 2) (𝓡 3) A (shear q u) := hA.mdifferentiableAt (by simp)
  have hC : MDifferentiableAt (𝓡 4) (𝓡 3)
      (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u)) q := hAd.comp q hL'
  have hF₁ : HasFDerivAt (fun q' : EuclideanSpace ℝ (Fin 4) =>
        chartAt (EuclideanSpace ℝ (Fin 3)) p.1 (A (shear q' u)))
      ((tangentCoordChange (𝓡 3) (A (shear q u)) p.1 (A (shear q u))).comp
        (mfderiv (𝓡 4) (𝓡 3) (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u)) q)) q :=
    hasFDerivAt_chartAt_comp (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u))
      p.1 hC hsrc
  -- the two components of the charted map
  set f : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) :=
    fun q' => chartAt (EuclideanSpace ℝ (Fin 3)) p.1 (A (shear q' u)) with hfdef
  set g : ℝ → ℝ := fun r' => thetaS r' v with hgdef
  have hf_diff : DifferentiableAt ℝ f q := by
    rw [hfdef]
    exact hF₁.differentiableAt
  have hgCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r' : ℝ => thetaS r' v) :=
    contDiff_shear_thetaS.2.comp (contDiff_id.prodMk contDiff_const)
  have hg_diff : DifferentiableAt ℝ g r := by
    rw [hgdef]
    exact hgCD.contDiffAt.differentiableAt (by simp)
  -- the level direction is a full line
  have hgr : (fderiv ℝ g r).range = ⊤ := by
    have hd : HasDerivAt g (deriv g r) r := hg_diff.hasDerivAt
    have hfd : fderiv ℝ g r = ContinuousLinearMap.toSpanSingleton ℝ (deriv g r) :=
      hd.hasFDerivAt.fderiv
    have hne : deriv g r ≠ 0 := by rw [hgdef]; exact hderiv
    rw [hfd, Submodule.eq_top_iff']
    intro y
    rw [LinearMap.mem_range]
    refine ⟨y / deriv g r, ?_⟩
    show (y / deriv g r) • deriv g r = y
    rw [smul_eq_mul, div_mul_cancel₀ _ hne]
  -- rewrite the charted map through the chart formula
  have hfun : (fun z : EuclideanSpace ℝ (Fin 4) × ℝ => chr p
        (A (shear z.1 u), thetaS z.2 v)) = fun z => psiLin (f z.1, g z.2) := by
    funext z
    rw [chr_projTimesLine_apply]
  have hfg := range_fderiv_psiLin_prod f g q r hf_diff hg_diff hgr
  -- the class part: the range of the charted class derivative
  have hrw : (fderiv ℝ f q).range = Submodule.map
      (tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (A (shear q u)) p.1 (A (shear q u))).toLinearMap
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) A (shear q u)).range := by
    have hfd' : fderiv ℝ f q
        = (tangentCoordChange (𝓡 3) (A (shear q u)) p.1 (A (shear q u))).comp
            (mfderiv (𝓡 4) (𝓡 3) (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u)) q) := by
      rw [hfdef]
      exact hF₁.fderiv
    rw [hfd']
    rw [show ((tangentCoordChange (𝓡 3) (A (shear q u)) p.1 (A (shear q u))).comp
          (mfderiv (𝓡 4) (𝓡 3) (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u)) q)).range
        = Submodule.map (tangentCoordChange (𝓡 3) (A (shear q u)) p.1
            (A (shear q u))).toLinearMap
            (mfderiv (𝓡 4) (𝓡 3)
              (fun q' : EuclideanSpace ℝ (Fin 4) => A (shear q' u)) q).range from
      LinearMap.range_comp _ _]
    rw [range_mfderiv_shear_eq A hA hA0 hA1 u q]
  rw [hfun, hfg, hrw]

end

end Work.Drive
