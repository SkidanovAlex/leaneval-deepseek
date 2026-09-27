import Mathlib
import Submission.Work.Drive.ppParity.StripDefs
import Submission.Work.Drive.ppParity.ShiftDeriv
import Submission.Work.Drive.pairMeet2

/-!
# The richness of the intrinsic pair family on a general `4`-manifold

`Work.Drive.ppDiff` (`Submission/Work/Drive/ppParity/Defs.lean`) is the charted pair-difference map of
the transport's collapse count, built out of the two *intrinsically perturbed* plane chains
`ppShift Ξ w (unpackFst τ) E`, `ppShift Ξ w (unpackSnd τ) E'`
(`Submission/Work/Drive/ppParity/Shift.lean`).  The parametric-Sard engine of the `S3` lane consumes
exactly one analytic input at its pair-map zeros: the **surjectivity of the parameter-derivative**

> `τ ↦ ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x`

(`PieceDataStrip`'s `hsurj`, `Submission/Work/Drive/ppParity/StripDefs.lean`).

`Work.Drive.surjective_fderiv_ppDiff_shift` (`ppParity/Richness.lean`) proves this for `ChartPert Q 4 Ξ`
on the capping space `CappingSpace`.  This file proves the **general-manifold** form: `M` is an
arbitrary smooth `4`-manifold charted on `ℝ⁴`, and the two ingredients of `ChartPert` are used directly
— the joint smoothness `hΞsm` of `(t, e) ↦ Ξ t e`, and the pointwise surjectivity `hΞsurj` of
`t ↦ Ξ t e`.

## The mechanism (verbatim the `Richness.lean` argument)

`Ξ` is *intrinsic*: the parameter `τ` enters only through the two blocks `w (ftS x) • unpackFst τ`,
`w (ftS x) • unpackSnd τ` of `ℝ⁴`, and the two chart blocks of `ppDiff` are differentiated by the
**same** pair-difference criterion `Work.Drive.surjective_fderiv_pairDiff2_of_block`.  The derivative of
the first chart block in the parameter is

> `(shiftBlockCLM_gen Ξ e v p).comp (w (ftS x) • unpackFst)`,

where `v = w (ftS x) • unpackFst τ`, `e = E (ftS x) (ftU x)` and

> `shiftBlockCLM_gen Ξ e v p = tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e) ∘ mfderiv (Ξ (·) e) v`,

i.e. the chart bridge `fderiv_chart_comp_hasFDerivAt` (`ChartBridge.lean`) wrapped around the manifold
chain rule `mfderiv_gen_shift_clm_inner`.  Each factor is onto — `mfderiv (Ξ (·) e) v` by `hΞsurj`, and
the change of coordinates because it is injective between spaces of the same finite dimension
(`Work.Drive.tangentCoordChange_injective`) — so their composite is onto, and the scalar `w (ftS x)` is
harmless exactly when it does not vanish (`hwne`).  The two blocks `pairUp u₁ u₂` are then filled
independently.
-/

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

/-! ## The general-manifold block calculus of the intrinsic shift

These are the `ChartPert`-free copies of `Work.Drive.contMDiff_shift_clm`,
`mfderiv_shift_clm_inner`, `chart_comp_mfderiv_shift`, `hasFDerivAt_chart_clm`,
`surjective_shiftBlockCLM` and `exists_shiftBlockCLM_smul` of `ppParity/ShiftDeriv.lean`: the smoothness
of the joint map `(t, e) ↦ Ξ t e` (`hΞsm`) replaces the first two clauses of `ChartPert`, and the
pointwise surjectivity (`hΞsurj`) replaces the third. -/

/-- **The map `t ↦ Ξ (B t) e` is `C^∞`** for a continuous linear `B`. -/
theorem contMDiff_shift_clm_gen {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (e : M) (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    ContMDiff (𝓡 8) (𝓡 4) Ctop (fun t : EuclideanSpace ℝ (Fin 8) => Ξ (B t) e) := by
  have h1 : ContMDiff (𝓡 8) (𝓡 4) Ctop (fun t : EuclideanSpace ℝ (Fin 8) => B t) := B.contMDiff
  have h2 : ContMDiff (𝓡 8) (𝓡 4) Ctop (fun _ : EuclideanSpace ℝ (Fin 8) => e) := contMDiff_const
  exact hΞsm.comp (h1.prodMk h2)

/-- **The chain rule for the inner shift**: the derivative of the composed map
`t ↦ Ξ (B t) e` factors through the derivative of `Ξ (·) e` at the shifted point. -/
theorem mfderiv_gen_shift_clm_inner {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (e : M) (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) :
    mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) t
      = (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t)).comp B := by
  have hL : MDifferentiableAt (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t :=
    B.contMDiff.mdifferentiableAt Ctop_ne_zero
  have hG : MDifferentiableAt (𝓡 4) (𝓡 4)
      (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t) := by
    have hsm2 : ContMDiff (𝓡 4) (𝓡 4) Ctop (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) :=
      hΞsm.comp (contMDiff_id.prodMk contMDiff_const)
    exact hsm2.mdifferentiableAt Ctop_ne_zero
  have hcomp : mfderiv (𝓡 8) (𝓡 4)
      ((fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) ∘ (fun t' : EuclideanSpace ℝ (Fin 8) => B t')) t
      = (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t)).comp
          (mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t) :=
    mfderiv_comp (I := 𝓡 8) (I' := 𝓡 4) (I'' := 𝓡 4)
      (f := fun t' : EuclideanSpace ℝ (Fin 8) => B t')
      (g := fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) t hG hL
  have hfun : mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) t
      = mfderiv (𝓡 8) (𝓡 4)
          ((fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) ∘
            (fun t' : EuclideanSpace ℝ (Fin 8) => B t')) t := rfl
  rw [hfun, hcomp]
  ext u
  show (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t))
      ((mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => B t') t) u)
    = (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) (B t)) (B u)
  rw [mfderiv_clm_eq_self B t]
  rfl

/-- **The block map of the derivative** in the general-manifold setting: the chart change of
coordinates at `Ξ v e` composed with the derivative of `Ξ (·) e` at `v`. -/
noncomputable abbrev shiftBlockCLM_gen {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (e : M) (v : EuclideanSpace ℝ (Fin 4)) (p : M) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)).comp
    (mfderiv (𝓡 4) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' e) v)

/-- **The charted derivative of the shifted value factors through the block map.** -/
theorem chart_comp_mfderiv_gen_shift {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (e : M) (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) (p : M) (_hsrc : Ξ (B t) e ∈ (chr p).source) :
    (tangentCoordChange (𝓡 4) (Ξ (B t) e) p (Ξ (B t) e)).comp
        (mfderiv (𝓡 8) (𝓡 4) (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) t)
      = (shiftBlockCLM_gen Ξ e (B t) p).comp B := by
  rw [mfderiv_gen_shift_clm_inner (Ξ := Ξ) hΞsm e B t]
  rw [← ContinuousLinearMap.comp_assoc]

/-- **The derivative of the charted perturbed plane value in the parameter**, on a general
`4`-manifold. -/
theorem hasFDerivAt_chart_clm_gen {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (e : M) (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (t : EuclideanSpace ℝ (Fin 8)) (p : M) (hsrc : Ξ (B t) e ∈ (chr p).source) :
    HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin 8) => chr p (Ξ (B t') e))
      ((shiftBlockCLM_gen Ξ e (B t) p).comp B) t := by
  have hsm := contMDiff_shift_clm_gen (Ξ := Ξ) hΞsm e B
  have hmain := fderiv_chart_comp_hasFDerivAt
    (fun t' : EuclideanSpace ℝ (Fin 8) => Ξ (B t') e) hsm p hsrc
  rw [chart_comp_mfderiv_gen_shift (Ξ := Ξ) hΞsm e B t p hsrc] at hmain
  exact hmain

/-- **The block map of the derivative is onto** — from the pointwise surjectivity `hΞsurj` of
`mfderiv (Ξ (·) e)` and the invertibility of the change of coordinates. -/
theorem surjective_shiftBlockCLM_gen {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsurj : ∀ (t : EuclideanSpace ℝ (Fin 4)) (p : M),
      Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
        (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' p) t))
    (e : M) (v : EuclideanSpace ℝ (Fin 4)) (p : M) (hsrc : Ξ v e ∈ (chr p).source) :
    Function.Surjective (shiftBlockCLM_gen Ξ e v p) := by
  have hinj : Function.Injective (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)) := by
    refine Work.Drive.tangentCoordChange_injective (x := Ξ v e) (y := p) (z := Ξ v e) ⟨?_, ?_⟩
    · exact mem_extChartAt_source _
    · rw [extChartAt_source]; exact hsrc
  have hsurjT : Function.Surjective (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (tangentCoordChange (𝓡 4) (Ξ v e) p (Ξ v e)).toLinearMap) (by simp)).mp hinj
  exact hsurjT.comp (hΞsurj v e)

/-- **The scaled block map is onto**: for every `z` there is `u` with
`shiftBlockCLM_gen Ξ e v p (c • u) = z`, as soon as `c ≠ 0`. -/
theorem exists_shiftBlockCLM_gen_smul {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsurj : ∀ (t : EuclideanSpace ℝ (Fin 4)) (p : M),
      Function.Surjective (mfderiv (𝓡 4) (𝓡 4)
        (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' p) t))
    (e : M) (v : EuclideanSpace ℝ (Fin 4)) (p : M) (hsrc : Ξ v e ∈ (chr p).source)
    (c : ℝ) (hc : c ≠ 0) (a : EuclideanSpace ℝ (Fin 4)) :
    ∃ u : EuclideanSpace ℝ (Fin 4), (shiftBlockCLM_gen Ξ e v p) (c • u) = a := by
  obtain ⟨u₀, hu₀⟩ := surjective_shiftBlockCLM_gen (Ξ := Ξ) hΞsurj e v p hsrc a
  refine ⟨c⁻¹ • u₀, ?_⟩
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [smul_smul, hcc, one_smul]
  exact hu₀

/-! ## The richness theorem -/

theorem surjective_fderiv_ppDiff_shift_gen
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞsurj : ∀ (t : EuclideanSpace ℝ (Fin 4)) (p : M),
      Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' p) t))
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (w : ℝ → ℝ) (τ : EuclideanSpace ℝ (Fin 8)) (x : EuclideanSpace ℝ (Fin 9))
    (p p' : M)
    (hsrc : Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E
        (Work.Drive.ftS x) (Work.Drive.ftU x) ∈ (Work.Drive.chr p).source)
    (hsrc' : Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E'
        (Work.Drive.ftS x) (Work.Drive.ftU x) ∈ (Work.Drive.chr p').source)
    (hwne : w (Work.Drive.ftS x) ≠ 0) :
    Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) =>
      Work.Drive.ppDiff p p' (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ') E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ') E') V W x) τ) := by
  refine surjective_fderiv_pairDiff2_of_block 8
    (fun τ' (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) =>
      chr p (Ξ (w s • unpackFst τ') (E s u)))
    (fun τ' (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) =>
      chr p' (Ξ (w s • unpackSnd τ') (E' s u)))
    (fun _ (y : EuclideanSpace ℝ (Fin 3)) => chr p (V y))
    (fun _ (z : EuclideanSpace ℝ (Fin 3)) => chr p' (W z))
    τ x
    ((shiftBlockCLM_gen Ξ (E (ftS x) (ftU x)) (w (ftS x) • unpackFst τ) p).comp
      (w (ftS x) • unpackFst))
    ((shiftBlockCLM_gen Ξ (E' (ftS x) (ftU x)) (w (ftS x) • unpackSnd τ) p').comp
      (w (ftS x) • unpackSnd))
    0 0 ?_ ?_ (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) ?_
  · exact hasFDerivAt_chart_clm_gen (Ξ := Ξ) hΞsm (E (ftS x) (ftU x)) (w (ftS x) • unpackFst) τ p hsrc
  · exact hasFDerivAt_chart_clm_gen (Ξ := Ξ) hΞsm (E' (ftS x) (ftU x)) (w (ftS x) • unpackSnd) τ p' hsrc'
  · intro a b
    obtain ⟨u₁, hu₁⟩ := exists_shiftBlockCLM_gen_smul (Ξ := Ξ) hΞsurj (E (ftS x) (ftU x))
      (w (ftS x) • unpackFst τ) p hsrc (w (ftS x)) hwne a
    obtain ⟨u₂, hu₂⟩ := exists_shiftBlockCLM_gen_smul (Ξ := Ξ) hΞsurj (E' (ftS x) (ftU x))
      (w (ftS x) • unpackSnd τ) p' hsrc' (w (ftS x)) hwne b
    refine ⟨pairUp u₁ u₂, ?_, ?_, rfl, rfl⟩
    · show ((shiftBlockCLM_gen Ξ (E (ftS x) (ftU x)) (w (ftS x) • unpackFst τ) p).comp
        (w (ftS x) • unpackFst)) (pairUp u₁ u₂) = a
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, unpackFst_pairUp]
      exact hu₁
    · show ((shiftBlockCLM_gen Ξ (E' (ftS x) (ftU x)) (w (ftS x) • unpackSnd τ) p').comp
        (w (ftS x) • unpackSnd)) (pairUp u₁ u₂) = b
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, unpackSnd_pairUp]
      exact hu₂

end

end Work.Drive.ppParity
