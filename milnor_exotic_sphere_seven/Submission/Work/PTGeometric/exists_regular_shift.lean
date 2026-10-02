import Mathlib
import Submission.Work.PTGeometric.FDerivInChart
import Submission.Work.PTGeometric.exists_regularValue_halfSpace
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.badSetEuclid

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Existence of a parameter `s` making the shifted level set regular

Given a smooth `ρ ≥ 0` on the closed half-space `ℝ^N₊`, smooth `ψ` and `χ` with `χ ≥ 0` strictly
positive on the positive half-line, and `c > 0`, `ε > 0`, there is a parameter `s ∈ (0, ε)` such
that every *interior* zero of `y ↦ ρ y - c * ψ (y 0) - s * χ (y 0)` is a regular point of that
function.

The proof is Sard's theorem in its parametric form.  On the open set `V = {0 < z 0}` of the model
space, put `G z = (halfSpaceExt ρ) z - c * ψ (z 0)` and `χₑ z = χ (z 0)`; then
`halfSpaceExt (ρ - cψ - sχ) = G - s χₑ` on `V`.  The Euclidean bad-set lemma
`volume_badSet_eq_zero_euclid_of_isOpen` applied to the pair `(e ∘ G, χₑ)` (where `e : ℝ ≃ₗᵢ ℝ¹` is
the standard linear isometry, needed because the bad-set lemma takes its parameters in `ℝ^k`) says
that the set of parameters `t ∈ ℝ¹` for which some interior `z` has `e (G z) = χₑ z • t` and is
critical for `y ↦ e (G y) - χₑ y • t` is Lebesgue-null.  Its preimage `N = e ⁻¹' T ⊆ ℝ` under `e`
is then null too; since `(0,ε)` has measure `ε > 0`, some `s ∈ (0,ε)` lies outside `N`, and that `s`
works: a critical *interior* zero `x` of the shifted function would be a witness for `e s ∈ T`
(namely `z = x.1`), since the manifold derivative of the shifted function at `x` is, by
`mfderiv_halfSpace_eq`, the Euclidean derivative of its extension to the model space, which is the
derivative of the critical perturbation `y ↦ e (G y) - χₑ y • e s` at `x.1`.
-/

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Set MeasureTheory Filter Function

noncomputable section

/-- The first coordinate of the half-space, as a `C^∞` function for the half-space model. -/
theorem coord_contMDiff {N : ℕ} [NeZero N] :
    ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞) (fun x : EuclideanHalfSpace N => x.1 0) := by
  have hI : ContMDiff (𝓡∂ N) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ((⊤:ℕ∞):WithTop ℕ∞) (𝓡∂ N) :=
    ModelWithCorners.contMDiff (𝓡∂ N) (n := ((⊤:ℕ∞):WithTop ℕ∞))
  have h2 : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun x : EuclideanHalfSpace N => (coordFun N) ((𝓡∂ N) x)) :=
    (coordFun N).contMDiff.comp hI
  simpa [Function.comp_def, coordFun_apply] using h2

/-- The shifted function `y ↦ ρ y - c • ψ (y 0) - s • χ (y 0)` is `C^∞`. -/
theorem shift_contMDiff {N : ℕ} [NeZero N] (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞) ρ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) ψ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) χ) (c s : ℝ) :
    ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) := by
  have h1 : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun y : EuclideanHalfSpace N => ψ (y.1 0)) :=
    hψ.contMDiff.comp coord_contMDiff
  have h2 : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun y : EuclideanHalfSpace N => χ (y.1 0)) :=
    hχ.contMDiff.comp coord_contMDiff
  have h3 : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun y : EuclideanHalfSpace N => c * ψ (y.1 0)) := by
    have h := (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,ℝ))
      (n := ((⊤:ℕ∞):WithTop ℕ∞)) (c : ℝ)).comp h1
    simpa [Function.comp_def, smul_eq_mul] using h
  have h4 : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞)
      (fun y : EuclideanHalfSpace N => s * χ (y.1 0)) := by
    have h := (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,ℝ))
      (n := ((⊤:ℕ∞):WithTop ℕ∞)) (s : ℝ)).comp h2
    simpa [Function.comp_def, smul_eq_mul] using h
  exact (hρ.sub h3).sub h4

/-- The first coordinate on the model space is `C^∞`. -/
theorem euclid_coord_contDiff {N : ℕ} [NeZero N] :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun z : EuclideanSpace ℝ (Fin N) => z 0) := by
  have h : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) => (coordFun N) z) :=
    (coordFun N).contDiff
  simpa [coordFun_apply] using h

/-- Smoothness on `{0 < z 0}` of the Euclidean representative `z ↦ e (halfSpaceExt ρ z - c ψ (z 0))`
of the lifted function, for a linear isometry `e : ℝ ≃ₗᵢ ℝ¹`. -/
theorem CInfOn_Gb {N : ℕ} [NeZero N] (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (𝓡∂ N) 𝓘(ℝ,ℝ) ((⊤:ℕ∞):WithTop ℕ∞) ρ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) ψ)
    (c : ℝ) (e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)) :
    Work.ThomBordism.Transversality.CInfOn
      (fun z : EuclideanSpace ℝ (Fin N) => e (halfSpaceExt ρ z - c * ψ (z 0)))
      {z | 0 < z 0} := by
  have hV : {z : EuclideanSpace ℝ (Fin N) | 0 < z 0} = interior (range (𝓡∂ N)) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace N]
  rw [hV]
  have h1 : ContDiffOn ℝ ((⊤:ℕ∞):WithTop ℕ∞) (halfSpaceExt ρ) (interior (range (𝓡∂ N))) :=
    contDiffOn_halfSpaceExt ρ hρ
  have h2 : ContDiffOn ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) => c * ψ (z 0)) (interior (range (𝓡∂ N))) :=
    (contDiff_const.mul (hψ.comp euclid_coord_contDiff)).contDiffOn
  have h3 : ContDiffOn ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) => halfSpaceExt ρ z - c * ψ (z 0))
      (interior (range (𝓡∂ N))) := h1.sub h2
  have h4 : ContDiffOn ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) => e (halfSpaceExt ρ z - c * ψ (z 0)))
      (interior (range (𝓡∂ N))) := by
    have h := (LinearIsometryEquiv.contDiff (n := ((⊤:ℕ∞):WithTop ℕ∞)) e).comp_contDiffOn h3
    simpa [Function.comp_def] using h
  exact h4

/-- Smoothness on `{0 < z 0}` of `z ↦ χ (z 0)`. -/
theorem CInfOn_Xb {N : ℕ} [NeZero N] (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) χ) :
    Work.ThomBordism.Transversality.CInfOn (fun z : EuclideanSpace ℝ (Fin N) => χ (z 0))
      {z | 0 < z 0} :=
  (hχ.comp euclid_coord_contDiff).contDiffOn

/-- **Existence of a shift making the level set regular.** -/
theorem exists_regular_shift {N : ℕ} [NeZero N]
    (ρ : EuclideanHalfSpace N → ℝ)
    (hρ : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχpos : ∀ t, 0 < t → 0 < χ t)
    (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ s ∈ Set.Ioo (0:ℝ) ε, ∀ x : EuclideanHalfSpace N,
      ρ x - c * ψ (x.1 0) - s * χ (x.1 0) = 0 → 0 < x.1 0 →
      mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
        (fun y => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) x ≠ 0 := by
  classical
  -- the standard linear isometry `ℝ ≃ ℝ¹`, and the open set of interior points
  set e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  set V : Set (EuclideanSpace ℝ (Fin N)) := {z | 0 < z 0} with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact isOpen_lt continuous_const (by fun_prop)
  have hGbSmooth : Work.ThomBordism.Transversality.CInfOn
      (fun z : EuclideanSpace ℝ (Fin N) => e (halfSpaceExt ρ z - c * ψ (z 0))) V := by
    rw [hVdef]
    exact CInfOn_Gb ρ hρ ψ hψ c e
  have hXbSmooth : Work.ThomBordism.Transversality.CInfOn
      (fun z : EuclideanSpace ℝ (Fin N) => χ (z 0)) V := by
    rw [hVdef]
    exact CInfOn_Xb χ hχ
  -- the null set of bad parameters
  set T : Set (EuclideanSpace ℝ (Fin 1)) := {t | ∃ z ∈ V,
      0 < χ (z 0) ∧ e (halfSpaceExt ρ z - c * ψ (z 0)) = χ (z 0) • t ∧
        ¬ Function.Surjective (fderiv ℝ
          (fun y : EuclideanSpace ℝ (Fin N) =>
            e (halfSpaceExt ρ y - c * ψ (y 0)) - χ (y 0) • t) z)} with hT
  have hTnull : volume T = 0 := by
    rw [hT]
    exact Work.ThomBordism.Transversality.TransversalApproximation.volume_badSet_eq_zero_euclid_of_isOpen
      (fun z : EuclideanSpace ℝ (Fin N) => e (halfSpaceExt ρ z - c * ψ (z 0)))
      (fun z : EuclideanSpace ℝ (Fin N) => χ (z 0)) V hVopen hGbSmooth hXbSmooth
      (fun z => hχ0 (z 0))
  have hnull : volume (e ⁻¹' T) = 0 := e.measurePreserving.preimage_null hTnull
  -- choose `s` avoiding the bad set
  obtain ⟨s, hsIoo, hsnot⟩ : ∃ s ∈ Set.Ioo (0:ℝ) ε, s ∉ e ⁻¹' T := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.Ioo (0:ℝ) ε ⊆ e ⁻¹' T := fun s hs => hcon s hs
    have h0 : volume (Set.Ioo (0:ℝ) ε) = 0 := measure_mono_null hsub hnull
    rw [Real.volume_Ioo, sub_zero] at h0
    have hpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨s, hsIoo, ?_⟩
  intro x hfx hx0 hzero
  -- the bridge from the manifold derivative to the Euclidean derivative
  have hFsm : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) :=
    shift_contMDiff ρ hρ ψ hψ χ hχ c s
  have hbridge := mfderiv_halfSpace_eq
    (ρ := fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) hFsm x
  rw [hzero] at hbridge
  have hmem : range (𝓡∂ N) ∈ 𝓝 ((𝓡∂ N) x) :=
    interior_range_mem_nhds (by simpa [model_apply_zero] using hx0)
  have hA : fderiv ℝ
      (halfSpaceExt (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)))
      ((𝓡∂ N) x) = 0 :=
    (fderivWithin_of_mem_nhds
      (f := halfSpaceExt (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)))
      (s := range (𝓡∂ N)) hmem).symm.trans hbridge.symm
  have hVx : (𝓡∂ N) x ∈ V := by
    rw [hVdef]
    simpa [model_apply_zero] using hx0
  have hcongr : halfSpaceExt (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0))
      =ᶠ[𝓝 ((𝓡∂ N) x)]
      (fun z : EuclideanSpace ℝ (Fin N) => (halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0)) := by
    filter_upwards [hVopen.mem_nhds hVx] with z hz
    rw [hVdef] at hz
    rw [halfSpaceExt_apply_of_le
          (fun y : EuclideanHalfSpace N => ρ y - c * ψ (y.1 0) - s * χ (y.1 0)) (le_of_lt hz),
        halfSpaceExt_apply_of_le ρ (le_of_lt hz)]
  have hB : fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin N) => (halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0))
      ((𝓡∂ N) x) = 0 := by
    rw [← hcongr.fderiv_eq]
    exact hA
  -- differentiability of the perturbation, and the chain rule with `e`
  have hpertCont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin N) => (halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0)) V := by
    rw [hVdef, ← interior_range_modelWithCornersEuclideanHalfSpace N]
    exact ((contDiffOn_halfSpaceExt ρ hρ).sub
      (contDiff_const.mul (hψ.comp euclid_coord_contDiff)).contDiffOn).sub
      (contDiff_const.mul (hχ.comp euclid_coord_contDiff)).contDiffOn
  have hdiff : DifferentiableAt ℝ
      (fun z : EuclideanSpace ℝ (Fin N) => (halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0))
      ((𝓡∂ N) x) :=
    (hpertCont.differentiableOn (by norm_num)).differentiableAt (hVopen.mem_nhds hVx)
  have hfun : (fun z : EuclideanSpace ℝ (Fin N) =>
        e (halfSpaceExt ρ z - c * ψ (z 0)) - χ (z 0) • e s)
      = fun z : EuclideanSpace ℝ (Fin N) =>
          e ((halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0)) := by
    funext z
    have h1 : e (s * χ (z 0)) = χ (z 0) • e s := by
      have h : e (χ (z 0) • s) = χ (z 0) • e s := map_smul e (χ (z 0)) s
      rw [smul_eq_mul, mul_comm] at h
      exact h
    simp only [map_sub, h1]
  have h3 : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) =>
      e (halfSpaceExt ρ z - c * ψ (z 0)) - χ (z 0) • e s) ((𝓡∂ N) x) = 0 := by
    rw [hfun]
    have hf : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) =>
          e ((fun z => (halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0)) z)) ((𝓡∂ N) x)
        = (e.toContinuousLinearEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
            (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) =>
              (halfSpaceExt ρ z - c * ψ (z 0)) - s * χ (z 0)) ((𝓡∂ N) x)) := by
      simpa [Function.comp_def] using
        ((ContinuousLinearMap.hasFDerivAt
            (e.toContinuousLinearEquiv : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))).comp
          ((𝓡∂ N) x) hdiff.hasFDerivAt).fderiv
    rw [hf, hB, ContinuousLinearMap.comp_zero]
  have hnsurj : ¬ Function.Surjective (fderiv ℝ
      (fun z : EuclideanSpace ℝ (Fin N) =>
        e (halfSpaceExt ρ z - c * ψ (z 0)) - χ (z 0) • e s) ((𝓡∂ N) x)) := by
    rw [h3]
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj (e 1)
    have h10 : (1:ℝ) = 0 := e.injective (by simpa using hv.symm)
    exact one_ne_zero h10
  -- the witness for the bad set
  have hwit : e s ∈ T := by
    rw [hT]
    refine ⟨x.1, ?_, ?_, ?_, ?_⟩
    · rw [hVdef]
      exact hx0
    · exact hχpos (x.1 0) hx0
    · have hρx : halfSpaceExt ρ x.1 = ρ x := by
        rw [halfSpaceExt_apply_of_le ρ x.2]
        rfl
      rw [hρx]
      have hval : ρ x - c * ψ (x.1 0) = s * χ (x.1 0) := by linarith [hfx]
      rw [hval]
      have h1 : e (s * χ (x.1 0)) = χ (x.1 0) • e s := by
        have h : e (χ (x.1 0) • s) = χ (x.1 0) • e s := map_smul e (χ (x.1 0)) s
        rw [smul_eq_mul, mul_comm] at h
        exact h
      exact h1
    · have hx1 : (𝓡∂ N) x = x.1 := modelWithCornersEuclideanHalfSpace_apply N
      simpa [hx1] using hnsurj
  exact hsnot hwit

end

end Work.PTGeometric
